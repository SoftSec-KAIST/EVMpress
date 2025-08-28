module Engine.SolveInfo

open B2R2.BinIR.SSA
open CPTypes
open TypeRecTypes
open Helper
open B2R2.BinIR
open B2R2
open System.Collections.Generic
open B2R2.Collections
open EVMpress.Type
open EVMpress.Utils

let mkTagVarPub pubAddr var = TagVarPublic (pubAddr, var)


type SolveInfo (perVarTags: Dictionary<TagVar, HashSet<Tag>>,
                varDisjointSet: DisjointSet<TagVar>,
                pubFuncInfos: Dictionary<Addr, PerFuncDataFlowInfo>) =
  /// perVarTags: 각 변수에 대한 태그들
  //let perVarTags = Dictionary<TagVar, HashSet<Tag>>()

  /// pubFuncInfos: 각 pub 함수에 대한 data-flow 정보
  //let pubFuncInfos = Dictionary<Addr, PubFuncInfo>()

  /// worklist
  let varQueue = UniqueQueue<TagVar>()

  /// src로부터 dst로의 dep이 등록됐는지 확인하기 위한 set. 최적화를 위해 사용됨.
  let depRegSet = HashSet<(TagVar * TagVar)>()
  let perVarAffectedVars = Dictionary<TagVar, HashSet<TagVar>>()
  let perVarTempTags = Dictionary<TagVar, HashSet<Tag>>()

  let perVarUntouchedTags = Dictionary<TagVar, HashSet<Tag>>()

  let getKExprFromTagVar tagVar =
    fnGetKExprFromTagVar pubFuncInfos tagVar

  let rec tryLoadTagVarFromMemoryAtConstant visited mem off =
    let memVar = TagVar.toVar mem
    match perVarTags.TryGetValue mem with
    | _ when (visited: Set<_>).Contains memVar -> None (* cycle detected *)
    | false, _ -> None
    | true, tags ->
      let visited = visited.Add memVar
      tags
      |> Seq.tryPick (function
        | TagRawMemStore (_inMem, addr, value) ->
          match getKExprFromTagVar addr
                |> KExpr.constantFolding
                |> KExpr.tryToBitVector with
          | None -> None
          | Some addrBv ->
            if not <| BitVector.isEqualTo addrBv off then None
            else Some value
        | _ -> None)
      |> function
        | Some v -> Some v
        | None ->
          (* follow its parent memory *)
          let pubAddr = getPubAddrFromTagVar mem
          let pubFuncInfo = pubFuncInfos[pubAddr]
          let memVar = TagVar.toVar mem
          match pubFuncInfo.CPState.SSAEdges.Defs.TryGetValue memVar with
          | false, _ -> None
          | true, stmt ->
            match stmt with
            | Def (_, e) ->
              match e with
              | Var parentMemVar ->
                tryLoadTagVarFromMemoryAtConstant visited (TagVarPublic (pubAddr, parentMemVar)) off
              | _ -> None (*FIXME*)
            | Phi (_, ids) ->
              (* phi인 경우 -> 하나만 선택 *)
              (*FIXME*)
              ids
              |> Seq.tryPick (fun id ->
                tryLoadTagVarFromMemoryAtConstant visited (TagVarPublic (pubAddr, { memVar with Identifier = id })) off)
            | ExternalCall (_, [ parentMemVar ], _) ->
              tryLoadTagVarFromMemoryAtConstant visited (TagVarPublic (pubAddr, parentMemVar)) off
            | _ -> None

  let rec expandToKExprMemo = Dictionary ()

  /// TODO: erase me
  and DepthLimit = 10

  and expandToKExpr tagVar =
    let kExpr = getKExprFromTagVar tagVar
    let pubAddr = getPubAddrFromTagVar tagVar
    expandToKExprAux pubAddr kExpr 0

  and expandToKExprAux pubAddr expr depth =
    let depth = depth + 1
    match KExpr.tryGetVar expr with
    | None -> expandToKExprAuxAux pubAddr expr depth
    | Some var ->
      let kExprKey = (pubAddr, var)
      if depth > DepthLimit then expr
      elif expandToKExprMemo.ContainsKey kExprKey then
        expandToKExprMemo[kExprKey]
      else
        let newExpr = expandToKExprAuxAux pubAddr expr depth
        expandToKExprMemo.Add (kExprKey, newExpr)
        newExpr

  and expandToKExprAuxAux pubAddr expr depth =
    match expr with
    (*
      SHA3
       : consider memory aliasing
    *)
    | KBinOp (recentVar, BinOpType.APP, KFuncName "keccak256", args) ->
      let [ inMem; off; len ] = KExpr.toList args
      let memTagVar = TagVarPublic (pubAddr, Option.get <| KExpr.tryGetVar inMem)
      let offBv = KExpr.tryToBitVector off
      let lenBv =
        match KExpr.constantFolding len with
        | KNum (_, bv) -> Some bv
        | _ -> None // failwith "TODO: invalid sha3 length"
      match offBv, lenBv with
      | Some offBv, Some lenBv ->
        (* offset이 0인 경우만 고려 *)
        if not <| offBv.IsZero then expr
        (* length: 0x20; might be array access *)
        elif BitVector.isEqualTo lenBv 0x20 then
          let firstValue = tryLoadTagVarFromMemoryAtConstant Set.empty memTagVar 0x00
          match firstValue with
          | Some firstValue ->
            let firstValueExpr = expandToKExpr firstValue
            let newArgs = KExpr.ofList [ firstValueExpr ]
            KBinOp (recentVar, BinOpType.APP, KFuncName "sha3", newArgs)
          | _ -> expr
        (* length: 0x40; might be mapping access *)
        elif BitVector.isEqualTo lenBv 0x40 then
          let firstValue = tryLoadTagVarFromMemoryAtConstant Set.empty memTagVar 0x00
          let secondValue = tryLoadTagVarFromMemoryAtConstant Set.empty memTagVar 0x20
          match firstValue, secondValue with
          | Some firstValue, Some secondValue ->
            let firstValueExpr = expandToKExpr firstValue
            let secondValueExpr = expandToKExpr secondValue
            let newArgs = KExpr.ofList [ firstValueExpr; secondValueExpr ]
            KBinOp (recentVar, BinOpType.APP, KFuncName "sha3", newArgs)
          | _ ->
#if TYPEDEBUG
            printfn "[-] cannot resolve into sha3: %A, %A" firstValue secondValue
#endif
            expr
        else expr
      | _ -> expr
    | KBinOp (recentVar, binOpType, kE1, kE2) ->
      let newKE1 = expandToKExprAux pubAddr kE1 depth
      let newKE2 = expandToKExprAux pubAddr kE2 depth
      KBinOp (recentVar, binOpType, newKE1, newKE2)
    | KCast (recentVar, castKind, kE) ->
      let newKE = expandToKExprAux pubAddr kE depth
      KCast (recentVar, castKind, newKE)
    | KUnOp (recentVar, unOpType, kE) ->
      let newKE = expandToKExprAux pubAddr kE depth
      KUnOp (recentVar, unOpType, newKE)
    | KRelOp (recentVar, relOpType, kE1, kE2) ->
      let newKE1 = expandToKExprAux pubAddr kE1 depth
      let newKE2 = expandToKExprAux pubAddr kE2 depth
      KRelOp (recentVar, relOpType, newKE1, newKE2)
    | KLoad (recentVar, memVar, addr) ->
      let newAddr = expandToKExprAux pubAddr addr depth
      KLoad (recentVar, memVar, newAddr)
    | KStore (recentVar, memVar, addr, value) ->
      let newAddr = expandToKExprAux pubAddr addr depth
      let newValue = expandToKExprAux pubAddr value depth
      KStore (recentVar, memVar, newAddr, newValue)
    | KExtract (recentVar, kE) ->
      let newKE = expandToKExprAux pubAddr kE depth
      KExtract (recentVar, newKE)
    | KIte (recentVar, kE1, kE2, kE3) ->
      let newKE1 = expandToKExprAux pubAddr kE1 depth
      let newKE2 = expandToKExprAux pubAddr kE2 depth
      let newKE3 = expandToKExprAux pubAddr kE3 depth
      KIte (recentVar, newKE1, newKE2, newKE3)
    | _ -> expr

  /// src depends on dst
  /// which means that dst affects src
  let fnRegisterDep srcVar dstVar =
    let regKey = (srcVar, dstVar)
    if not <| depRegSet.Add regKey then () (* ignore if already been added *)
    else
      if perVarAffectedVars.ContainsKey dstVar then
        let vars = perVarAffectedVars[dstVar]
        (vars: HashSet<_>).Add srcVar |> ignore
      else
        let vars = HashSet ()
        perVarAffectedVars.Add (dstVar, vars)
        perVarAffectedVars[dstVar] <- vars

  /// FIXME: if this is problematic, just revert it
  let pushUntouchedTag var tag =
    if perVarUntouchedTags.ContainsKey var then
      let tags = perVarUntouchedTags[var]
      (tags: HashSet<_>).Add tag |> ignore
    else
      let tags = HashSet ()
      tags.Add tag |> ignore
      perVarUntouchedTags[var] <- tags

  let fnRegisterTag var tag =
    match perVarTags.TryGetValue var with
    | true, tags when tags.Contains tag -> false (* already added tag *)
    | _ ->
      if perVarTempTags.ContainsKey var then
        let tags = perVarTempTags[var]
        (tags: HashSet<_>).Add tag |> ignore
      else
        let tags = HashSet ()
        tags.Add tag |> ignore
        perVarTempTags[var] <- tags
      pushUntouchedTag var tag
      true

  let fnPushVarToWorklist var =
    varQueue.Enqueue var
    match perVarAffectedVars.TryGetValue var with
    | false, _ -> ()
    | true, vars ->
      for affectedVar in vars do
        varQueue.Enqueue affectedVar

  /// TODO: implement this in the tag extraction phase.
  let fnParseTagToAddDeps srcVar tag =
    /// src depends on dsts
    let dstVars = Tag.getTagVars tag
    for dstVar in dstVars do fnRegisterDep srcVar dstVar

  /// Storage 주소를 나타내는 KExpr를 SymLoc으로 변환함.
  /// TODO: Calldata의 것과 합치기
  let rec convertToStorageSymLoc addr e =
    match e with
    | KNum (_, bv) -> SymLoc.Const bv
    | KBinOp (_, _, KFuncName "sload", args) ->
      let [ loc ]= KExpr.toList args
      SymLoc.SLoad <| convertToStorageSymLoc addr loc
    | KBinOp (_, _, KFuncName "sha3", args) ->
      let args = KExpr.toList args
      match args with
      | [ loc ] -> SymLoc.Hash [ convertToStorageSymLoc addr loc ]
      | [ _; loc ] -> SymLoc.Hash [ SymLoc.PlaceHolder; convertToStorageSymLoc addr loc ]
    | KBinOp (_, BinOpType.ADD, e1, e2) ->
      convertToStorageSymLoc addr e1 + convertToStorageSymLoc addr e2
    | KVar var -> (* must be phi var*)
      let funcInfo = fnGetFuncInfo pubFuncInfos addr
      match fnTryGetPhiLoopInfo funcInfo var with
      | None -> SymLoc.PlaceHolder
      | Some phiLoopInfo ->
        let i = phiLoopInfo.Initial
        let i = TagVarPublic (addr, i) |> expandToKExpr
        let d = phiLoopInfo.Delta
        let d = TagVarPublic (addr, d) |> expandToKExpr
        match i, d with
        (* loop *)
        (* some value + _ *)
        | someInitValue, KNum (_, bv) when bv.IsOne ->
          convertToStorageSymLoc addr someInitValue + SymLoc.PlaceHolder
        | _ -> SymLoc.PlaceHolder
    | _ -> SymLoc.PlaceHolder (*FIXME*)

  /// TagVar 별 Tag들.
  member __.PerVarTags with get()= perVarTags

  /// Pub 함수 주소 별 PubFuncInfo들.
  /// FIXME: currently it stores priv + pub
  member __.PubFuncInfos with get()= pubFuncInfos

  member __.Worklist with get()= varQueue

  member __.PerVarTempTags with get()= perVarTempTags

  member __.GetTagsFromTagVar tagVar =
    match perVarTags.TryGetValue tagVar with
    | false, _ -> seq{}
    | true, tags -> tags

  /// 새로운 TagVar를 추가한다.
  /// 전역 변수에 쓰일 수 있음.
  member __.AddNewTagVar tagVar =
    if __.PerVarTags.ContainsKey tagVar then ()
    else __.PerVarTags.Add (tagVar, HashSet ())

  member __.AddTagBase currVar tagVar tag addDeps =
    (* if the var is being used then lazily add the tag *)
    let isCurrentlyHandled = tagVar = currVar
    if isCurrentlyHandled then
      (* postpone adding the tag *)
      if fnRegisterTag tagVar tag then
        if addDeps then fnParseTagToAddDeps tagVar tag
        fnPushVarToWorklist tagVar
    else
      let okay =
        match perVarTags.TryGetValue tagVar with
        | false, _ ->
          let tags = HashSet ()
          tags.Add tag |> ignore
          perVarTags[tagVar] <- tags
          true
        | true, tags when tags.Contains tag ->
          false
        | true, tags ->
          tags.Add tag |> ignore
          true
      if okay then
        if addDeps then fnParseTagToAddDeps tagVar tag
        fnPushVarToWorklist tagVar

  member __.AddTag currVar tagVar tag =
    __.AddTagBase currVar tagVar tag true

  /// 오버헤드 줄이려고 deps는 굳이 안 업데이트한다
  /// 어차피 equality 때문에 계속 서로 전파할 거니까
  /// 이렇게 하면 solve에서 오버헤드 절반으로 줄어듦
  member __.AddEquality currVar var1 var2 =
    __.AddTagBase currVar var1 (TagEqualsTo var2) false
    __.AddTagBase currVar var2 (TagEqualsTo var1) false

  member __.PopUntouchedTags tagVar =
    match perVarUntouchedTags.TryGetValue tagVar with
    | false, _ -> []
    | true, tags ->
      let ret = tags |> Seq.toList
      tags.Clear ()
      ret

  member __.GetKExprFromTagVar tagVar =
    fnGetKExprFromTagVar pubFuncInfos tagVar

  member __.TryLoadTagVarFromMemoryAtConstant mem off =
    tryLoadTagVarFromMemoryAtConstant Set.empty mem off

  /// 태그 변수를 KExpr로 확장한다. 메모리 alias 고려해서 확장함. 따라서
  /// 이를 호출할 때는 이미 memory aliasing 관련한 정보가 모두 수집되어 있어야 함.
  member __.ExpandToKExpr tagVar =
    expandToKExpr tagVar

  member __.GetCPStateFromTagVar tagVar =
    fnGetCPStateFromTagVar pubFuncInfos tagVar

  member __.GetFuncInfoFromTagVar tagVar =
    fnGetPubAddrFromTagVar tagVar
    |> fnGetFuncInfo pubFuncInfos

  member __.ConvertToStorageSymLoc addr e =
    convertToStorageSymLoc addr e

  member __.InitWorklist () =
    for tagVar in perVarTags.Keys do
      varQueue.Enqueue tagVar
      match perVarTags.TryGetValue tagVar with
      | false, _ -> ()
      | true, tags ->
        for tag in tags do
          pushUntouchedTag tagVar tag

let tryGetRootMemVarFromFreePtrTagVar (solveInfo: SolveInfo) tv =
  let funcInfo = solveInfo.GetFuncInfoFromTagVar tv
  let pubAddr = getPubAddrFromTagVar tv
  let m = solveInfo.PubFuncInfos[pubAddr].RootMemMemo
  fnTryGetRootMemVarFromFreePtrVar m funcInfo (TagVar.toVar tv)

let getPossibleKExprsFromPhiKVar (solveInfo: SolveInfo) pubAddr kv =
  let v = KExpr.toVar kv
  let tagVar = TagVarPublic (pubAddr, v)
  let cpState = solveInfo.GetFuncInfoFromTagVar tagVar
  let ids = fnGetPhiIds cpState v
  fnExpandPhiVarsToKExprs cpState v ids
