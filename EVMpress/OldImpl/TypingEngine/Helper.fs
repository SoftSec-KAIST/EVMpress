[<AutoOpenAttribute>]
module Engine.Helper

open System.Collections.Generic
open B2R2
open B2R2.BinIR.SSA
open B2R2.MiddleEnd.DataFlow
open CPTypes
open TypeRecTypes
open B2R2.BinIR
open Epoche
open EVMpress.Type

module BitVector =
  let rt = 256<rt>
  let MaxUInt64 = BitVector.Cast (BitVector.MaxUInt64, rt)

  let ofArrBigEndian (arr: byte []) =
    let sz = arr.Length
    if sz > 8 then
      let arr = Seq.rev arr (*뒤집*)
      let arr = Seq.append arr [| 0uy |]
      let arr = Array.ofSeq arr (*TODO:overhead ㅠㅠ*)
      BitVector(bigint arr, sz * 8<rt>)
    else failwith "BitVector.ofArrBigEndian: array size must be greater than 8"

  let isFitIntoUInt64 (bv: BitVector) =
    if BitVector.Le(bv, MaxUInt64).IsTrue then true
    else false

  let tryToUInt64 bv =
    if not <| isFitIntoUInt64 bv then None
    else Some <| BitVector.ToUInt64 bv

  let isEqualTo (bv: BitVector) (v: bigint) =
    bv.BigValue = v

  let isEqualToUInt64 (bv: BitVector) v =
    match tryToUInt64 bv with
    | Some u -> u = v
    | None -> false

  /// 연속된 비트마스크
  let isBitmask (bv: BitVector) =
    (* check if this bv is a bitmask (e.g. 0xfff...ff) *)
    (* v & (v + 1) = 0 *)
    let n = bv.BigValue
    let n' = bigint.Add (n, 1)
    let n'' = n' &&& n
    n'' = 0I && n > 1

  /// ex) 0xff -> 8
  let getBitmaskBits (bv: BitVector) =
    let rec loop (bv: BitVector) i =
      if bv.IsZero then i
      else loop (BitVector.Shr(bv, (BitVector.One 256<rt>))) (i + 1)
    loop bv 0

  let isMultipleOfUInt64 (bv: BitVector) (i: uint64) =
    (BitVector.Modulo(bv, BitVector(i, 256<rt>))).IsZero

  /// we use a^b = a^[b/2] * a^(b - [b/2]) for b > 0 :)
  let Exp (bv1: BitVector, bv2: BitVector) =
    let rec f (a: BitVector) (b: BitVector) =
      if b.IsZero then BitVector.One a.Length
      elif b.IsOne then a
      else
        let halved = BitVector.Div(b, BitVector(2UL, 256<rt>))
        let rest = b - halved
        (f a (halved)) * (f a (rest))
    f bv1 bv2

  /// keccak256
  /// dyn array땜에
  let calculateKeccak256 (bv: BitVector) =
    let byArray = Array.create 32 0uy
    byArray[32-1] <- (bv.BigValue % 256I) |> uint8
    let hash = Keccak256.ComputeHash byArray
    let res = ofArrBigEndian hash
    res

  let one = BitVector.One rt

  /// 그냥 0될때까지 오른쪽으로 shift. e.g. 0b1000000 => 6+1=7 (0개수 + 1).
  /// 애초에 0이면 -1 반환.
  let getMSBOffset (bv: BitVector) =
    let rec loop bv i =
      if (bv:BitVector).IsZero then i
      else loop (BitVector.Shr(bv, one)) (i + 1)
    loop bv -1

  /// (1) 최상위비트가 (1<<256-1)이어야 하고 (2) 0xff...ff로 이루어져 있어야 함
  let isBytesNBitmask (bv: BitVector) =
    let msbOff = getMSBOffset bv
    if msbOff <> 255 then false
    else
      (*TODO: 귀찮*)
      true

  let WordBytes = 32

  let getBytesNBitmaskBytes (bv: BitVector) =
    let rec fn (bv:BitVector) i =
      if BitVector.And(bv, BitVector(1UL, rt)).IsZero |> not then(*처음으로 0이아니면->*)
        WordBytes - i
      elif bv.IsZero then (* 숫자 자체가 0이 되어 버렸다...? *)
        0
      else fn (BitVector.Div(bv, BitVector(0x100UL, rt))) (i + 1)
    fn bv 0

module Expr =
  let toVar = function
    | Var var -> var
    | _ -> failwith "Unexpected expression"

module KExpr =

  let toBitVector = function
    | KNum (_, bv) -> bv
    | _ -> failwith "Unexpected expression"

  let tryToBitVector = function
    | KNum (_, bv) -> Some bv
    | _ -> None

  let hasVar = (Option.isSome << KExpr.tryGetVar )

  let isFreePtr e =
    match e with
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let args = KExpr.toList args
      match args with
      | [ _; KNum (_, bv_0x40) ] when BitVector.isEqualTo bv_0x40 0x40 -> true
      | _ -> false
    | _ -> false

  /// 일단 더하기만 지원
  let rec constantFolding e =
    match e with
    | KBinOp (v, BinOpType.ADD, e1, e2) ->
      let e1' = constantFolding e1
      let e2' = constantFolding e2
      match e1', e2' with
      | KNum (_, n1), KNum (_, n2) -> KNum (v, n1 + n2)
      | _ -> e
    | KBinOp (v, BinOpType.DIV, e1, e2) ->
      let e1' = constantFolding e1
      let e2' = constantFolding e2
      match e1', e2' with
      | KNum (_, n1), KNum (_, n2) -> KNum (v, n1 / n2)
      | _ -> e
    | KBinOp (v, _, KFuncName "exp", args) ->
      let [ d; e ]= KExpr.toList args
      let e1' = constantFolding d
      let e2' = constantFolding e
      match e1', e2' with
      | KNum (_, n1), KNum (_, n2) -> KNum (v, BitVector.Exp (n1, n2))
      | _ -> e
    | _ -> e

  let collectAddOperands e =
    let rec loop e acc =
      match e with
      | KBinOp (_, BinOpType.ADD, e1, e2) -> loop e1 (loop e2 acc)
      | _ -> e :: acc
    loop e []

  let rec tryExtractMPtr e =
    match e with
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let [ _; loc ]= KExpr.toList args
      match loc with
      | KNum (_, bv) when BitVector.isEqualToUInt64 bv 0x40UL -> Some e
      | _ -> None
    | KBinOp (_, BinOpType.ADD, e1, e2) ->
      match tryExtractMPtr e1 with
      | Some e1 -> Some e1
      | None -> tryExtractMPtr e2
    | _ -> None

  let rec toString e =
    match e with
    | KNum (_, bv) -> sprintf "%A" bv
    | KBinOp (_, op, e1, e2) ->
      let opStr = BinOpType.toString op
      let e1Str = toString e1
      let e2Str = toString e2
      sprintf "(%s %s %s)" e1Str opStr e2Str
    | KUnOp (_, op, e) ->
      let opStr = UnOpType.toString op
      let eStr = toString e
      sprintf "(%s %s)" opStr eStr
    | KExtract (_, e) ->
      let eStr = toString e
      sprintf "(extract %s)" eStr
    | KCast (_, op, e) ->
      let opStr = CastKind.toString op
      let eStr = toString e
      sprintf "(%s %s)" opStr eStr
    | KFuncName name ->
      let nameStr = name
      sprintf "(%s)" nameStr
    | KVar var ->
      let varStr = var.ToString ()
      sprintf "(%s)" varStr
    | KRelOp (_, op, e1, e2) ->
      let opStr = RelOpType.toString op
      let e1Str = toString e1
      let e2Str = toString e2
      sprintf "(%s %s %s)" e1Str opStr e2Str
    | KNil -> "nil"
    | _ -> failwithf "Unexpected KExpr: %A" e

[<AutoOpen>]
module SSAHelper =
  /// This finds the root variable of a given variable.
  /// This is useful when we want to represent a variable in a unique way.
  /// Note that we do not follow phi variables.
  /// TODO: memoization
  let rec findRootVar (cpState: FakeCPState) var =
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> (* out-of-scope (e.g. parameter value *) var
    | true, stmt ->
      match stmt with
      (* expand the def's expression *)
      | Def (_, e) -> findRootVarAux cpState var e
      (* it is a phi variable, so we stop its tracking here! *)
      | Phi _ -> var
      | _ -> var

  and findRootVarAux cpState var e =
    match e with
    (* we have more to follow? *)
    | Var var -> findRootVar cpState var
    (* unless, stop here *)
    | _ -> var

  let isInsCallRelated name =
    match name with
    | "delegatecall"
    | "staticcall"
    | "callcode"
    | "call" -> true
    | _ -> false

/// TODO: 불필요한거 쳐내라
[<AutoOpen>]
module EngineLogicHelper =
  let fnGetFuncInfo m addr = (m: Dictionary<_, _>)[addr]
  let fnGetCPState m addr =
    let { CPState = cpState } = (m: Dictionary<_, _>)[addr]
    cpState
  let fnGetPubAddrFromTagVar tagVar =
     match tagVar with
     | TagVarPublic (pubAddr, _) -> pubAddr
     | _ -> Terminator.impossible ()
  let fnGetCPStateFromTagVar m tagVar =
     match tagVar with
     | TagVarPublic (pubAddr, _) -> fnGetCPState m pubAddr
     | _ -> failwith "cannot get CPState from non-public tag var"
  let fnGetKExprFromTagVar m tagVar =
    match tagVar with
    | TagVarPublic (pubAddr, var) ->
      let funcInfo = fnGetFuncInfo m pubAddr
      KExpr.ofExpr funcInfo None (Var var)
    | _ -> failwith "cannot get KExpr from non-public tag var"
  let getPubAddrFromTagVar tagVar =
    match tagVar with
    | TagVarPublic (pubAddr, _) -> pubAddr
    | _ -> failwith "cannot get pub addr from non-public tag var"
  let fnExpandPhiVarsToKExprs bundle var ids =
    ids
    |> Seq.map (fun id -> KExpr.ofExpr bundle None (Var { var with Identifier = id }))
    |> Seq.toList
  let fnGetPhiIds bundle var =
    let cpState = bundle.CPState
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> []
    | true, stmt ->
      match stmt with
      | Phi (_, ids) -> List.ofArray ids
      | _ -> []
  let fnIsPhiVar bundle var =
    let cpState = bundle.CPState
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> false
    | true, stmt ->
      match stmt with
      | Phi _ -> true
      | _ -> false
  let fnIsKExprFreePtr addrExpr =
    match addrExpr with
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let args = KExpr.toList args
      let [ inMemExpr; addrExpr ] = args
      match addrExpr with
      | KNum (_, bv) when BitVector.isEqualToUInt64 bv 0x40UL -> true
      | _ -> false
    | _ -> false
  let fnTryGetPhiLoopInfo bundle var =
    if fnIsPhiVar bundle var |> not then
      None
    else
      let exprs = fnExpandPhiVarsToKExprs bundle var <| fnGetPhiIds bundle var
      match exprs with
      (* x = phi(init, x + delta) *)
      | [ KBinOp (_, BinOpType.ADD, x, delta); init ]
      | [ KBinOp (_, BinOpType.ADD, delta, x); init ]
      | [ init; KBinOp (_, BinOpType.ADD, delta, x) ]
      | [ init; KBinOp (_, BinOpType.ADD, x, delta) ]
          when KExpr.tryGetVar x = Some var ->
        Some
        <| { Initial = Option.get <| KExpr.tryGetVar init
             Delta = Option.get <| KExpr.tryGetVar delta }
      | _ -> None
  let fnTryGetPhiArgKExprs funcInfo kExpr =
    let cpState = funcInfo.CPState
    let var = KExpr.tryGetVar kExpr
    match var with
    | None -> None
    | Some var ->
      match cpState.SSAEdges.Defs.TryGetValue var with
      | false, _ -> None
      | true, stmt ->
        match stmt with
        | Phi (_, ids) ->
          let exprs = fnExpandPhiVarsToKExprs funcInfo var ids
          Some exprs
        | _ -> None

  /// TODO: memoization
  /// this is used to find the representative mem var of a specific memory region.
  let rec fnFindDominatingFreeMemVar m funcInfo memVar =
    fnTryFindDominatingFreeMemVarAux m funcInfo Set.empty memVar
    |> Option.get
  and fnTryFindDominatingFreeMemVarAux m funcInfo s memVar =
    let cpState = funcInfo.CPState
    let key = memVar.Identifier
    match (m: Dictionary<_, _>).TryGetValue key with
    | true, v when v <> None -> v
    // | false, _ ->
    | _ ->
      let retVal =
        if Set.contains memVar.Identifier s then None
        else
          let s = Set.add memVar.Identifier s
          match (cpState: FakeCPState).SSAEdges.Defs.TryGetValue memVar with
          | false, _ -> Some { Kind = MemVar; Identifier = 0 }
          | true, stmt->
            match stmt with
            (* for phis, we should follow till the end *)
            | Phi (_, ids) ->
              let followedMemVars =
                ids
                |> Seq.map (fun id -> fnTryFindDominatingFreeMemVarAux m funcInfo s { memVar with Identifier = id })
                |> Seq.choose id
                |> Seq.distinct
              (*TODO: what if coming from different two pathes at a merging point *)
              (* sort by dominance relation, and pick the most dominated one *)
    #if DEBUG
              (*
              if Seq.length followedMemVars = 0 then
                let v = ssa.FindVertexByID vid
                ()
                assert false
              *)
              (*
              if Seq.length followedMemVars > 1 then
                let src = entryVertex
                let dst = ssa.FindVertexByID vid
                // let pathes = findPathes ssa src dst
                let a = ssa.FindVertexBy (fun v -> v.VData.PPoint.Address = 0x2645UL)
                let b = ssa.FindVertexBy (fun v -> v.VData.PPoint.Address = 0x219dUL)
                let domCtx = Dominator.initDominatorContext ssa entryVertex
                let doms1 = Dominator.doms domCtx a
                let doms2 = Dominator.doms domCtx b
                let domsShared = doms1 |> List.filter (fun dom1 -> List.exists (fun dom2 -> dom1 = dom2) doms2)
                // pathes |> Seq.iter (fun path -> printfn "%A" path)
                ()
                assert false
              *)
    #endif
              (*TODO: how to handle multiple incoming pointers?
                return multiple mem vars and consider all the cases? *)
              if Seq.length followedMemVars > 1 then
                Seq.tryHead followedMemVars
              else
                if Seq.isEmpty followedMemVars then
                  (*FIXME*)
                  Some { Kind = MemVar; Identifier = 0 }
                else
                  Seq.tryExactlyOne followedMemVars
            | Def (_, e) ->
              match e with
              (* currently we use Store expr only for stack stores, so ignore it here *)
              // | Store ...
              (*TODO: it is possible when a stack ptr is not a constant *)
              | _ -> failwith "TODO: invalid mem def expr"
            | ExternalCall (e, inVars, _) ->
              let [ inMemVar ] = inVars
              match e with
              | BinOp (BinOpType.APP, _, FuncName "mstore", ExprList args) ->
                let [ addr; value ] = args
                let kAddr = KExpr.ofExpr funcInfo None addr
                match kAddr with
                (* if the current mem was defined by a mapping { 0x40 |-> x },
                   then the current mem is the root (dominating) mem var *)
                | KNum (_, bv) when BitVector.isEqualToUInt64 bv 0x40UL -> Some memVar
                (* otw, just proceed to find the root *)
                | _ -> fnTryFindDominatingFreeMemVarAux m funcInfo s inMemVar
              | _ -> fnTryFindDominatingFreeMemVarAux m funcInfo s inMemVar
            | _ -> failwithf "TODO: invalid mem store stmt: %A" stmt
      m[key] <- retVal
      retVal
  /// currently we assume that the loc must be a free ptr
  let fnTryGetRootMemVarFromFreePtrVar m funcInfo loc =
    match KExpr.ofExpr funcInfo None (Var loc) with
    | e when fnIsKExprFreePtr e ->
      match e with
      | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
        let args = KExpr.toList args
        // let [ KVar inMem; _kLoc ] = args
        let [ inMemExpr; _kLoc ] = args
        let inMem = KExpr.toVar inMemExpr
        (* find its root until it meets store oper with { 0x40 |-> x } *)
        (* FIXME: inspection required *)
        // Some <| fnFindDominatingFreeMemVar inMem
        fnTryFindDominatingFreeMemVarAux m funcInfo Set.empty inMem
      | _ -> failwith "this must be an mload expression"
    | _ -> None (*TODO*)

  /// for testing
  let extractionSet = HashSet<(TagVar * Tag)> ()
  let registerExtraction tagVar tag =
    extractionSet.Add (tagVar, tag)
    |> ignore
  let isRegisteredExtraction tagVar tag =
    extractionSet.Contains (tagVar, tag)

module SymLoc =
  (*
  /// KExpr를 SymLoc으로 일반화. mem alias 처리돼이썽야함
  let rec ofKExpr e =
    match e with
    | KNum (_, bv) -> SymLoc.Const bv
    | KBinOp (_, _, KFuncName "sload", args) ->
      let [ loc ]= KExpr.toList args
      SymLoc.Storage <| ofKExpr loc
    | KBinOp (_, _, KFuncName "sha3", args) ->
      let args = KExpr.toList args
      match args with
      | [ loc ] -> SymLoc.Keccak256 [ ofKExpr loc ]
      | [ _; loc ] -> SymLoc.Keccak256 [ SymLoc.PlaceHolder; ofKExpr loc ]
    | _ -> SymLoc.PlaceHolder (*FIXME*)
  *)
  ()
