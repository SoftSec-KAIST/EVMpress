module Engine.Extract

open System.Collections.Generic

open B2R2
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.BinIR.SSA
open B2R2.MiddleEnd.DataFlow
open B2R2.BinIR
open B2R2.MiddleEnd.ControlFlowAnalysis

open TypeRecTypes
open CPTypes
open EVMpress.Type
open B2R2.MiddleEnd
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies
open EVMpress.Utils

let rec extractTagsFromPub (brew: BinaryBrew<EVMFuncUserContext, _>)
                           (privAddrs: Addr seq)
                           (funcInfo: PerFuncDataFlowInfo)
                           (privArgRetInfos: Dictionary<ProgramPoint, Dictionary<Addr, _>>)
                           (perVarTags: Dictionary<_, _>)
                           (varDisjointSet: DisjointSet<_>)=
  let privAddrSet = HashSet privAddrs
  let cpState = funcInfo.CPState
  let pubAddr = funcInfo.EntryPoint
  let ssa = funcInfo.SSACFG
  let entryVertex = ssa.SingleRoot
  let mkTagVar var = TagVarPublic (pubAddr, var)
  let fnAddTag var tag =
    if perVarTags.ContainsKey var then
      let prevTags = perVarTags[var]
      (prevTags: HashSet<_>).Add tag
    else
      let tags = HashSet [ tag ]
      perVarTags[var] <- tags
      true
  let fnAddTagPub var tag =
    let var = mkTagVar var
    if perVarTags.ContainsKey var then
      let prevTags = perVarTags[var]
      (prevTags: HashSet<_>).Add tag |> ignore
    else
      let tags = HashSet ()
      tags.Add tag |> ignore
      perVarTags[var] <- tags
#if TYPEDEBUG
      registerExtraction var tag
#endif

  /// Mem addr to variable
  let fnIsKExprFreePtr addrExpr =
    match addrExpr with
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let args = KExpr.toList args
      let [ inMemExpr; addrExpr ] = args
      match addrExpr with
      | KNum (_, bv) when BitVector.isEqualToUInt64 bv 0x40UL -> true
      | _ -> false
    | _ -> false
  /// TODO: memoization
  /// this is used to find the representative mem var of a specific memory region.
  let domFreeMemVarMemo = Dictionary ()
  let rec fnFindDominatingFreeMemVar memVar =
    fnFindDominatingFreeMemVarAux Set.empty memVar
    |> Option.get
  and fnFindDominatingFreeMemVarAux s memVar =
    let key = memVar.Identifier
    match domFreeMemVarMemo.TryGetValue key with
    | true, v when v <> None -> v
    | _ ->
      let retVal =
        if Set.contains memVar.Identifier s then None
        else
          let s = Set.add memVar.Identifier s
          match cpState.SSAEdges.Defs.TryGetValue memVar with
          | false, _ -> Some { Kind = MemVar; Identifier = 0 }
          | true, stmt->
            match stmt with
            (* for phis, we should follow till the end *)
            | Phi (_, ids) ->
              let followedMemVars =
                ids
                |> Seq.map (fun id -> fnFindDominatingFreeMemVarAux s { memVar with Identifier = id })
                |> Seq.choose id
                |> Seq.distinct
              (*TODO: what if coming from different two pathes at a merging point *)
              (* sort by dominance relation, and pick the most dominated one *)
  #if TYPEDEBUG
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
                | _ -> fnFindDominatingFreeMemVarAux s inMemVar
              | _ -> fnFindDominatingFreeMemVarAux s inMemVar
            | _ -> failwithf "TODO: invalid mem store stmt: %A" stmt
      domFreeMemVarMemo[key] <- retVal
      retVal
  /// currently we assume that the loc must be a free ptr
  let fnTryGetRootMemVarFromFreePtrVar loc =
    match KExpr.ofExpr funcInfo None (Var loc) with
    | e when fnIsKExprFreePtr e ->
      match e with
      | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
        let args = KExpr.toList args
        let [ KVar inMem; _kLoc ] = args
        (* find its root until it meets store oper with { 0x40 |-> x } *)
        (* FIXME: inspection required *)
        // Some <| fnFindDominatingFreeMemVar inMem
        fnFindDominatingFreeMemVarAux Set.empty inMem
      | _ -> failwith "this must be an mload expression"
    | _ -> None (*TODO*)
  let fnExpandPhiVarsToKExprs var ids =
    ids
    |> Seq.map (fun id -> KExpr.ofExpr funcInfo None (Var { var with Identifier = id }))
    |> Seq.toList
  let fnGetPhiIds var =
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> []
    | true, stmt ->
      match stmt with
      | Phi (_, ids) -> List.ofArray ids
      | _ -> []
  let fnIsPhiVar var =
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> false
    | true, stmt ->
      match stmt with
      | Phi _ -> true
      | _ -> false
  let fnTryGetPhiInfo var =
    assert (fnIsPhiVar var)
    let exprs = fnExpandPhiVarsToKExprs var <| fnGetPhiIds var
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
  let addNewTagVar tagVar =
    if perVarTags.ContainsKey tagVar then ()
    else perVarTags.Add (tagVar, HashSet ())
  let addEquality var1 var2 =
    fnAddTag var1 <| TagEqualsTo var2 |> ignore
    fnAddTag var2 <| TagEqualsTo var1 |> ignore

  /// 디버깅용
  let met = HashSet ()
  let checkpointPrint k =
    met.Add k

  (*
    1. collect tags
  *)
  (* we also resolve memory aliasing here *)
  (* 스택 터져서 tail-recursion으로 *)
  let rec dfs recentPrivAddrs visited vs =
    match vs with
    | [] -> ()
    | (v: IVertex<SSABasicBlock>) :: vs' when Set.contains v.ID visited ->
      dfs recentPrivAddrs visited vs'
    | v :: vs' ->
      let visited = Set.add v.ID visited
      let recentPrivAddrs =
        let currBBLAddr = v.VData.Internals.PPoint.Address
        if privAddrSet.Contains currBBLAddr then
          Set.add currBBLAddr recentPrivAddrs
        else
          recentPrivAddrs
      for pp, stmt in (v: IVertex<SSABasicBlock>).VData.Internals.Statements do
        (*
          priv arg/ret constraint
        *)
        match privArgRetInfos.TryGetValue pp with
        | true, perPrivAddrInfos ->
          (* TODO: this logic is somewhat confusing --- needs some explanation *)
          let recentPrivAddrs' =
            recentPrivAddrs
            |> Set.filter (fun addr -> perPrivAddrInfos.ContainsKey addr)
          for recentPrivAddr in recentPrivAddrs' do
            for info in perPrivAddrInfos[recentPrivAddr] do
              match info with
              | PrivArgInfo (_pp, privFuncAddr, off) ->
                let privTagVar = TagVarPrivate (privFuncAddr, off, true)
                match stmt with
                | Def (_, Var incomingVar) ->
                  let incomingTagVar = TagVarPublic (pubAddr, incomingVar)
                  fnAddTag incomingTagVar <| TagSubtypeOf privTagVar |> ignore
                  fnAddTag privTagVar <| TagSupertypeOf incomingTagVar |> ignore
    #if TYPEDEBUG
                  //printfn "add tag arg: %A" privTagVar
    #endif
                | _ ->
    #if TYPEDEBUG
                  fnCheckSPMismatch ()
    #endif
                  ()
                  (* FIXME: why happening? *)
                  //failwith "mismatch 1"
              | PrivRetInfo (_pp, privFuncAddr, off) ->
                let privTagVar = TagVarPrivate (privFuncAddr, off, false)
                match stmt with
                | Def (var, _) ->
                  let outgoingTagVar = TagVarPublic (pubAddr, var)
                  fnAddTag outgoingTagVar <| TagSubtypeOf privTagVar |> ignore
    #if TYPEDEBUG
                  //printfn "add tag ret: %A" privTagVar
    #endif
                  fnAddTag privTagVar <| TagSupertypeOf outgoingTagVar |> ignore
                | _ -> failwith "mismatch 2"
        | _ -> ()
        // printfn "pp: %A, stmt: %A" pp stmt
        match stmt with
        (* Stmt - phi
           we extract useful information, especially related to loops *)
        (* TODO: 이러면 gas 이런거 엄청 전파될듯*)
        (* TODO: bug 존재 *)
        | Phi ({ Kind = StackVar _ } as var, ids) ->
  #if TYPEDEBUG
          //printfn "phi var (0x%x) %A: %A" v.VData.PPoint.Address var exprs
  #endif
          (*
          let kExprs = fnExpandPhiVarsToKExprs var ids
          let tagVar = mkTagVar var
          kExprs
          |> Seq.iter (fun kExpr ->
            let phiOperVar = KExpr.toVar kExpr
            let phiOperTagVar = mkTagVar phiOperVar
            ()
          )
          *)
          (*
          for id in ids do
            let var' = { var with Identifier = id }
            let var' = findRootVar cpState var'
            let tagVar = mkTagVar var
            let tagVar' = mkTagVar var'
            addEquality tagVar tagVar'
          *)
          ()

        (* Stmt - phi
           we extract useful information, especially related to loops *)
        | Phi (var, ids) when var.Kind = MemVar -> // -288,12
          ()
(*
          let kExprs =
            ids
            |> Array.map (fun id ->
              KExpr.ofExpr funcInfo None (Var { var with Identifier = id }))
  #if TYPEDEBUG
          //printfn "+phi: %A" var
          //printfn "%A" kExprs
          //printfn "phi %A: %x %A" var pp.Address kExprs
  #endif
          for kExpr in kExprs do
            match kExpr with
            | KVar var when fnIsPhiVar var ->
              match cpState.SSAEdges.Defs.TryFind var with
              | None -> ()
              | Some (_, stmt) ->
                match stmt with
                | Phi (_, ids) ->
                  let kExprs2 = ids |> Array.map (fun id -> KExpr.ofExpr funcInfo None (Var { var with Identifier = id }))
                  // 0x20 + (-288, 12)
                  // [0x40] + 0x40
                  ()
                | _ -> failwith "impossible"
              ()
            | _ -> ()
          ()
*)
        (* ignore uninteresting data-flows *)
        | Def (var, _e) when KExpr.isUninterestingVar var -> ()
        (* single def *)
        | Def (var, e) when findRootVar cpState var = var ->
          (*
          solver.AddFact $"""
            Def("{getVarId pubAddr cpState var}", "{getExprId pubAddr cpState e}").
          """
          *)
  #if TYPEDEBUG
          //printfn "def: %x %A" pp.Address (IRHelper.symbolicExpand cpState e)
          //printfn "+def: %A" var
          let kExpr = KExpr.ofExpr funcInfo None e
          printfn "KExpr-Def (%x): %x - %A" pubAddr pp.Address kExpr
          printfn "Expr-Def (%x): %x - %A" pubAddr pp.Address (IRHelper.symbolicExpand cpState e|> fun e-> e|>Pp.expToString )
          ()
  #endif
          (* Check arith op *)
          match e with
          | BinOp (opType, _, e1, e2) when
               opType = BinOpType.ADD
            || opType = BinOpType.SUB
            //|| opType = BinOpType.MUL // ??? (e.g. sload(n) * 0x100)
            || opType = BinOpType.DIV // 이것도 마찬가지 storage
            || opType = BinOpType.MOD
            || opType = BinOpType.SHR
            || opType = BinOpType.SHL
            ->
            let kE1 = KExpr.ofExpr funcInfo None e1
            let kE2 = KExpr.ofExpr funcInfo None e2
            match KExpr.tryGetVar kE1 with
            | Some rootVar1 ->
              fnAddTagPub rootVar1 <| TagUsedInArithOp (opType, 1) |> ignore
            | _ -> ()
            match KExpr.tryGetVar kE2 with
            | Some rootVar2 ->
              fnAddTagPub rootVar2 <| TagUsedInArithOp (opType, 2) |> ignore
            | _ -> ()

            //findRootVar cpState (Option.get (KExpr.tryGetVar kE1))
            //let rootVar2 = findRootVar cpState (Option.get (KExpr.tryGetVar kE2))
            //if opType <> BinOpType.DIV then (* cf. sload(..) / 0x100... *)
            //fnAddTagPub rootVar1 <| TagUsedInArithOp (opType, 1) |> ignore
            //fnAddTagPub rootVar2 <| TagUsedInArithOp (opType, 2) |> ignore
            fnAddTagPub var  <| TagUsedInArithOp (opType, 0) |> ignore
  #if TYPEDEBUG
            //printfn "arith op: %A %A %A" opType kE1 kE2
  #endif
            ()
          | _ -> ()

          (* Check rel op *)
          match e with
          | Cast (_, _, RelOp (opType, _, e1, e2)) when
               opType = RelOpType.LT
            || opType = RelOpType.GT
            //|| opType = BinOpType.MUL
            //|| opType = BinOpType.DIV
            ->
            let kE1 = KExpr.ofExpr funcInfo None e1
            let kE2 = KExpr.ofExpr funcInfo None e2
            let rootVar1 = findRootVar cpState (Option.get (KExpr.tryGetVar kE1))
            let rootVar2 = findRootVar cpState (Option.get (KExpr.tryGetVar kE2))
            fnAddTagPub rootVar1 <| TagUsedAsRelOperand opType |> ignore
            fnAddTagPub rootVar2 <| TagUsedAsRelOperand opType |> ignore
  #if TYPEDEBUG
  #endif
            ()
          | _ -> ()

          (*
            그냥 쌩으로 KExpr 파싱
            근데 sym var 아님ㅎ
          *)
          match KExpr.ofExpr funcInfo None e with
          (*
            bytes
          *)
          | KBinOp
             (_, BinOpType.ADD,
              KNum (_, bv_0x1f),
              KBinOp
                (_, BinOpType.DIV,
                 KBinOp
                   (_, BinOpType.AND,
                    KBinOp
                      (_, BinOpType.SUB,
                       KBinOp
                         (_, BinOpType.MUL,
                          KNum (_, bv_0x100),
                          KCast
                            (_, CastKind.ZeroExt,
                             KRelOp
                               (None, RelOpType.EQ,
                                KBinOp
                                  (_, BinOpType.AND,
                                   KNum (_, bv_0x1),
                                   KBinOp
                                     (_, _,
                                      KFuncName "sload",
                                      KExprList
                                        (_,
                                         [ KNum (_, bv_slot) ]
                                         ))), KNum (None, bv_0x0)))),
                       KNum (_, bv_0x1_2)),
                    KBinOp
                      (_, BinOpType.APP, KFuncName "sload",
                       KExprList (_, [ KNum (_, bv_slot_2) ]))), KNum (_, bv_0x2)))
            when BitVector.isEqualToUInt64 bv_0x1f 0x1fUL
              && BitVector.isEqualToUInt64 bv_0x100 0x100UL
              && bv_0x0.IsZero
              && bv_0x1.IsOne
              && bv_0x1_2.IsOne
              && BitVector.isEqualTo bv_0x2 2
              && bv_slot = bv_slot_2
            ->
            let symLoc = SymLoc.Hash [ SymLoc.Const bv_slot ] + SymLoc.PlaceHolder
            let newTagVar = TagVarSym symLoc
            addNewTagVar newTagVar
            fnAddTag newTagVar <| TagHasType TyBytes |> ignore
          (*
            bytes length pattern

            TODO: 이값이 freemem의 첫번째에 할당된다면 => bytes의 힌트다
          *)
          | KBinOp
             (_, BinOpType.DIV,
              KBinOp
                (_, BinOpType.AND,
                 KBinOp
                   (_, BinOpType.APP, KFuncName "sload",
                    KExprList (_, [ KNum (_, bv_slot) ])),
                 KBinOp
                   (_, BinOpType.ADD,
                    KUnOp
                      (_, UnOpType.NOT,
                       KNum (_, bv_0x0_1)),
                    KBinOp
                      (_, BinOpType.MUL,
                       KNum (_, bv_0x100),
                       KCast
                         (_, CastKind.ZeroExt,
                          KRelOp
                            (None, RelOpType.EQ,
                             KBinOp
                               (_, BinOpType.AND,
                                KBinOp
                                  (_, BinOpType.APP, KFuncName "sload",
                                   KExprList
                                     (_, [ KNum (_, bv_slot_2) ])), KNum (_, bv_0x1)),
                             KNum (None, bv_0x0_3)))))),
              KNum (_, bv_0x2))
            when bv_0x0_1.IsZero
              && bv_0x0_3.IsZero
              && bv_0x1.IsOne
              && BitVector.isEqualTo bv_0x2 2
              && BitVector.isEqualToUInt64 bv_0x100 0x100UL
              && bv_slot = bv_slot_2
            ->
            let symLoc = SymLoc.Hash [ SymLoc.Const bv_slot ] + SymLoc.PlaceHolder
            (*TODO: symloc을 이렇게 잡는게 맞나? sload(sha3(n) + i) *)
            let newTagVar = TagVarSym symLoc
            addNewTagVar newTagVar
            fnAddTag newTagVar <| TagHasType TyBytes |> ignore
            (*
              bytes
            *)
          | KBinOp
             (_, BinOpType.ADD,
              KBinOp
                (_, BinOpType.DIV,
                 KBinOp
                   (_, BinOpType.AND,
                    KBinOp
                      (_, BinOpType.APP, KFuncName "sload",
                       KExprList
                         (_, [ KNum (_, bv_slot) ])),
                       KBinOp
                      (_, BinOpType.ADD,
                       KBinOp
                         (_, BinOpType.MUL,
                          KCast
                            (_, _,
                             KRelOp
                               (None, RelOpType.EQ,
                                KBinOp
                                  (_, BinOpType.AND,
                                   KBinOp
                                     (_, BinOpType.APP,
                                      KFuncName "sload",
                                      KExprList
                                        (_, [ KNum (_, bv_slot_2) ])),
                                   KNum (_, bv_0x1)),
                                KNum (None, bv_0x0))),
                          KNum (_, bv_0x100)),
                       KUnOp
                         (_, UnOpType.NOT,
                          KNum (_, bv_0x0_2)))),
                 KNum (_, bv_0x2)),
              KNum (_, bv_0x1f))
            when bv_0x0.IsZero
              && bv_0x0_2.IsZero
              && bv_0x1.IsOne
              && BitVector.isEqualToUInt64 bv_0x1f 0x1fUL
              && BitVector.isEqualToUInt64 bv_0x100 0x100UL
              && BitVector.isEqualTo bv_0x2 2
              && bv_slot = bv_slot_2
            ->
            //let symLoc = SymLoc.Storage (SymLoc.BinOp (BinOpType.ADD, SymLoc.Keccak256 [ SymLoc.Const bv_slot ], SymLoc.PlaceHolder))
            let symLoc = SymLoc.Hash [ SymLoc.Const bv_slot ] + SymLoc.PlaceHolder
            let newTagVar = TagVarSym symLoc
            addNewTagVar newTagVar
            fnAddTag newTagVar <| TagHasType TyBytes |> ignore
          | _ -> ()

          (*
            그냥 쌩으로 KExpr 파싱
            symbolic variable 도입
          *)
          match KExpr.ofExpr funcInfo None e with
          (*TODO: 나중에는 모두 cosntant folding해서 mask얻는 식으로 ㄱㄱ -> 논문에도 그렇게*)
          (*
            sload(n) / exp(0x100, k)
            => var(slot=n,offset=k)
          *)
          | KBinOp (_, BinOpType.DIV, KBinOp (_, BinOpType.APP, KFuncName "sload", sloadArgs),
                                      KBinOp (_, BinOpType.APP, KFuncName "exp", expArgs)) ->
            let sloadArgs = KExpr.toList sloadArgs
            let expArgs = KExpr.toList expArgs
            match sloadArgs, expArgs with
            | [ KNum (_, slotBv) ], [ KNum (_, bv_0x100); KNum (_, bv_off) ]
              when BitVector.isEqualToUInt64 bv_0x100 0x100UL ->
              let slot = slotBv
              let mask = BitVector.Exp (bv_0x100, bv_off)
              let absolute = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const slot), SymLoc.Const mask)
              let currTagVar = mkTagVar var
              addNewTagVar <| TagVarSym absolute
              addEquality currTagVar <| TagVarSym absolute
            | _ -> ()
          (*
            sload(n) / 0x100000...
            => var(slot=n,offset=k)
            위엣게 최적화된 버전 (exp가 constant folding)
          *)
          | KBinOp (_, BinOpType.DIV, KBinOp (_, BinOpType.APP, KFuncName "sload", sloadArgs),
                                      KNum (_, bv_0x100))
            when bv_0x100 - 1UL |> BitVector.isBitmask ->
            let sloadArgs = KExpr.toList sloadArgs
            match sloadArgs with
            | [ KNum (_, slotBv) ] ->
              let slot = slotBv
              let mask = bv_0x100
              let absolute = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const slot), SymLoc.Const mask)
              let currTagVar = mkTagVar var
              addNewTagVar <| TagVarSym absolute
              addEquality currTagVar <| TagVarSym absolute
            | _ -> ()
          (*
            sload(n) / (1 << 0xa8)
          *)
          | KBinOp
             (_, BinOpType.DIV,
              KBinOp
                (_, BinOpType.APP, KFuncName "sload",
                 KExprList (None, [ KNum (_, bv_slot) ])),
              KBinOp
                (_, BinOpType.SHL, KNum (_, bv_0x1),
                 KNum (_, bv_0xa8)))
            when bv_0x1.IsOne
              && BitVector.isMultipleOfUInt64 bv_0xa8 8UL ->
            let slot = bv_slot
            let mask = BitVector.Shl(bv_0x1, bv_0xa8)
            let absolute = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const slot), SymLoc.Const mask)
            let currTagVar = mkTagVar var
            addNewTagVar <| TagVarSym absolute
            addEquality currTagVar <| TagVarSym absolute
          | _ -> ()

          let ins = brew.Instructions.Find(pp.Address)
          let insName = ins.Disasm().Split(" ")[0]
          match e with
          (* Def - keccak256 *)
          (* 이 값과 비교했다면, bool이나 address 같은 타입일 수는 없다 *)
          | BinOp (BinOpType.APP, _, FuncName "keccak256", _) ->
            (*FIXME:편의상 요렇게*)
            fnAddTagPub var <| TagUsedInArithOp (BinOpType.APP, 0)
          (* Def - msg.sender => always address type *)
          | BinOp (BinOpType.APP, _, FuncName "msg.sender", _) ->
            let rootVar = findRootVar cpState var
            //fnAddTagPub <| TagAddress
            fnAddTagPub rootVar <| TagAddress
          (* Def - block.number => uint256 *)
          | BinOp (BinOpType.APP, _, FuncName "block.number", _)
          | BinOp (BinOpType.APP, _, FuncName "block.coinbase", _)
          | BinOp (BinOpType.APP, _, FuncName "block.basefee", _)
          | BinOp (BinOpType.APP, _, FuncName "block.timestamp", _)
          | BinOp (BinOpType.APP, _, FuncName "selfbalance", _)
          | BinOp (BinOpType.APP, _, FuncName "balancefee", _)
          | BinOp (BinOpType.APP, _, FuncName "block.difficulty", _)
          | BinOp (BinOpType.APP, _, FuncName "extcodehash", _) ->
            let rootVar = findRootVar cpState var
            fnAddTagPub rootVar <| TagHasType (TyUInt 256)
            fnAddTagPub rootVar <| TagUsedInArithOp (BinOpType.APP, 0) // 이걸 통해서, bool로 판단되는 것 등을 막을 수 있다
          (* address type *)
          | BinOp (BinOpType.APP, _, FuncName "tx.origin", _)
          | BinOp (BinOpType.APP, _, FuncName "create", _)
          | BinOp (BinOpType.APP, _, FuncName "create2", _) ->
            let rootVar = findRootVar cpState var
            //fnAddTagPub <| TagAddress
            fnAddTagPub rootVar <| TagAddress
          (* Def - LT *)
          | Cast (_, _,RelOp (RelOpType.LT, _, e1, e2)) ->
            let kE1 = KExpr.ofExpr funcInfo None e1
            let kE2 = KExpr.ofExpr funcInfo None e2
            let rootVar1 = findRootVar cpState (Option.get (KExpr.tryGetVar kE1))
            let rootVar2 = findRootVar cpState (Option.get (KExpr.tryGetVar kE2))
            let tag = TagLt <| mkTagVar rootVar2
            fnAddTagPub rootVar1 tag |> ignore
          (* Def - EQ *)
          | Cast (CastKind.ZeroExt, _, RelOp (RelOpType.EQ, _, _e, num_zero)) ->
            let kExpr = KExpr.ofExpr funcInfo None e
            match kExpr with
            (* Def - Cast-RelOp combo (iszero) *)
            (* Cast-Relop-EQ - Cast-Relop-EQ zero (double iszero) *)
            | KCast (_, CastKind.ZeroExt,
                     KRelOp (_, RelOpType.EQ,
                             KCast (_, CastKind.ZeroExt,
                                    KRelOp (_, RelOpType.EQ,
                                            some_value,
                                            KNum (_, bv_zero))),
                             KNum (_, bv_zero_2)))
                when bv_zero.IsZero && bv_zero_2.IsZero ->
              let tag = TagDoubleIsZero
              let someValueVar = Option.get (KExpr.tryGetVar some_value)
              if fnIsPhiVar someValueVar then (* 하나하나 ㄱㄱ*)
                let phiOperandVars = fnGetPhiIds someValueVar |> fnExpandPhiVarsToKExprs someValueVar
                for phiOperVar in phiOperandVars do(*이러면 KExpr거쳐서 자연히 rootvar*)
                  let var = Option.get (KExpr.tryGetVar phiOperVar)
                  fnAddTagPub var <| TagUsedAsHighLevJumpCond |> ignore
              let rootVar = findRootVar cpState someValueVar
              (* iszero(iszero(v)) => v: DoubleIsZero *)
              fnAddTagPub rootVar tag
              (* result: bool? *)
              (* TODO: too strong? *)
              fnAddTagPub var <| TagHasType TyBool
            (*
              EQ comparison
              같다/다르다
              => 같은 타입? 강한 가정?
            *)
            | KCast (_, _, KRelOp (_, RelOpType.EQ, kE1, kE2))
              when KExpr.hasVar kE1 && KExpr.hasVar kE2
              ->
              let rootVar1 = findRootVar cpState (Option.get (KExpr.tryGetVar kE1))
              let rootVar2 = findRootVar cpState (Option.get (KExpr.tryGetVar kE2))
              (* v1 = v2 and v2 = v1 --- 양방향 전파 *)
              let tagVar1 = mkTagVar rootVar1
              let tagVar2 = mkTagVar rootVar2
              addEquality tagVar1 tagVar2
            | _ -> ()
          | BinOp
              (BinOpType.AND, _, Var var,
               BinOp
                 (BinOpType.SHL, _, Num bv_1,
                  BinOp
                    (BinOpType.SUB, _,
                     BinOp
                       (BinOpType.MUL, _, BinOp (BinOpType.ADD, _, Var varCount, Num bv_1_2),
                        Num bv_0x8), Num bv_1_3)))
            when bv_1.IsOne
              && bv_1_2.IsOne
              && bv_0x8.BigValue = 0x8
              && bv_1_3.IsOne
              && insName = "signextend" ->
            let rootVar = findRootVar cpState var
            fnAddTagPub rootVar <| TagIsSigned |> ignore
          (* Def - AND *)
          | BinOp (BinOpType.AND, _, e1, e2) when e1.IsVar && e2.IsVar ->
            let fn e1 e2 kE1 kE2 =
              (* assuming that e2 has a variable;
                 cf) BYTE instruction *)
              match KExpr.tryGetVar kE2 with
              | None -> ()
              | Some e2Var ->
                match kE1 with
                (* bitmask: 0xff...ff *)
                | KNum (_, bv)
                    when BitVector.isBitmask bv && BitVector.getBitmaskBits bv % 8 = 0 ->
                  let varOper = e2Var |> findRootVar cpState
                  fnAddTagPub varOper <| TagAndWithBitmask bv |> ignore
                  fnAddTagPub varOper <| TagSupertypeOf (mkTagVar var) |> ignore
                  fnAddTagPub var <| TagSubtypeOf (mkTagVar varOper) |> ignore
                (* exp (2, a0) - 1 => 160bits *)
                | KBinOp (_, BinOpType.SUB,
                          KBinOp (_, BinOpType.APP, KFuncName "exp", KExprList (_, [ KNum (_, bv_0x2); KNum (_, bv_0xa0) ])),
                          KNum (_, bv_0x1))
                    when BitVector.isEqualToUInt64 bv_0x2 2UL
                      && BitVector.isEqualToUInt64 bv_0x1 1UL
                      && BitVector.Exp (bv_0x2, bv_0xa0) - bv_0x1 |> BitVector.isBitmask
                  ->
                  let v = e2Var |> findRootVar cpState
                  let bv = BitVector.Exp (bv_0x2, bv_0xa0) - bv_0x1
                  let tag = TagAndWithBitmask (bv)
                  fnAddTagPub v tag |> ignore
                  fnAddTagPub  v <| TagSupertypeOf (mkTagVar var) |> ignore
                  fnAddTagPub var <| TagSubtypeOf (mkTagVar v) |> ignore
                (* ((1 << 0xa0) - 1): 160bits *)
                | KBinOp (_, BinOpType.SUB, KBinOp (_, BinOpType.SHL, KNum (_, bv_0x1), KNum (_, bv_0xa0)),
                                            KNum (_, bv_0x1_2))
                    when BitVector.isEqualTo bv_0x1 0x1
                      && BitVector.isEqualTo bv_0x1_2 0x1
                      && (BitVector.Shl (bv_0x1, bv_0xa0) - bv_0x1_2) |> BitVector.isBitmask
                  ->
                  let v = e2Var |> findRootVar cpState
                  let bv = BitVector.Shl(bv_0x1, bv_0xa0) - bv_0x1_2
                  let tag = TagAndWithBitmask (bv)
                  (*
                  match kE2 with
                  | KBinOp (_, _, KFuncName "msg.data", KBinOp (_, _, KNum (_, bv_loc), _)) ->
                    let temp = TagVarSym <| SymLoc.Calldata (pubAddr, SymLoc.Const bv_loc)
                    fnAddTag temp <| TagAndWithBitmask (bv) |> ignore
                  | _ -> ()
                  *)
                  fnAddTagPub v tag |> ignore
                  fnAddTagPub  v <| TagSupertypeOf (mkTagVar var) |> ignore
                  fnAddTagPub var <| TagSubtypeOf (mkTagVar v) |> ignore
                (* ? *)
                | KNum (_, bv) ->
                  let v = e2Var |> findRootVar cpState
                  let tag = TagAndWithBitmask (bv)
                  fnAddTagPub v tag |> ignore
                | _ -> ()

              (* calldata and op hint *)
              (*
              match kE2 with
              | KBinOp (Some e2Var, BinOpType.APP, KFuncName "msg.data", KBinOp (_, _, kLoc, _)) ->
                match kE1 with
                (* bitmask: 0xff...ff *)
                | KNum (_, bv)
                  when BitVector.isBitmask bv
                    && BitVector.getBitmaskBits bv % 8 = 0 ->
                  let varOper = e2Var |> findRootVar cpState
                  fnAddTagPub varOper <| TagAnd bv |> ignore
                  fnAddTagPub varOper <| TagSupertypeOf (mkTagVar var) |> ignore
                  fnAddTagPub var <| TagSubtypeOf (mkTagVar varOper) |> ignore
                | _ -> ()
              | _ -> ()
              *)
            let kE1 = KExpr.ofExpr funcInfo None e1
            let kE2 = KExpr.ofExpr funcInfo None e2

            let var1 = Option.get (KExpr.tryGetVar kE1)
            let var2 = Option.get (KExpr.tryGetVar kE2)

            let rootVar1 = findRootVar cpState var1
            let rootVar2 = findRootVar cpState var2

            fnAddTagPub var <| TagAndOp (mkTagVar rootVar1, mkTagVar rootVar2) |> ignore

            (*
              storage variable 도입
              TODO: memory aliasing 아직 안됐을수도
            *)
            let kE = KExpr.ofExpr funcInfo None e
            match kE with
            (*
              sload(n) & ((1 << a0) - 1)
            *)
            | KBinOp
                (_, BinOpType.AND,
                 KBinOp
                   (_, BinOpType.SUB,
                    KBinOp
                      (_, BinOpType.SHL, KNum (_, bv_0x1),
                       KNum (_, bv_0xa0)),
                    KNum (_, bv_0x1_2)),
                 KBinOp
                   (_, BinOpType.APP, KFuncName "sload",
                    KExprList (_, [ KNum (_, bv_slot) ])))
                when BitVector.isEqualTo bv_0x1 0x1UL
                  && BitVector.isEqualTo bv_0xa0 0xa0UL
                  && BitVector.isEqualTo bv_0x1_2 0x1UL ->
              (*FIXME: bitmask 표시해주는게 나을지도? offset 0이더라도*)
              let symLoc = SymLoc.SLoad (SymLoc.Const bv_slot)
              let newTagVar = TagVarSym symLoc
              addNewTagVar newTagVar
              let currTagVar = mkTagVar var
              addEquality newTagVar currTagVar
            (*
              storage bytes/string length calculation pattern
              (sload(n) >> 1) & 0x7f
            *)
            | KBinOp
                (_, BinOpType.AND,
                 KBinOp
                   (_, BinOpType.SHR,
                    KBinOp
                      (_, BinOpType.APP, KFuncName "sload",
                       KExprList (_, [ KNum (_, bv_0xd) ])),
                    KNum (_, bv_0x1)),
                 KNum (_, bv_0x7f)) ->
              (* TODO:slot 자체가 pointer가 되어야? *)
              //let symLoc = SymLoc.Storage (SymLoc.Const bv_0xd)
              let symLoc = SymLoc.Hash [ SymLoc.Const bv_0xd ] + SymLoc.PlaceHolder
              let newTagVar = TagVarSym symLoc
              addNewTagVar newTagVar
              fnAddTag newTagVar <| TagHasType TyBytes |> ignore
            | _ -> ()

            fn e1 e2 kE1 kE2
            fn e2 e1 kE2 kE1
            //printfn "and: %x %A %A" pp.Address kE1 kE2
          (* Def- MLOAD *)
          | BinOp (BinOpType.APP, _, FuncName "mload", ExprList args) ->
            let [ mem; loc ] = args
            let memVar = Option.get <| KExpr.tryGetVar (KExpr.ofExpr funcInfo None mem)
            let kLoc = KExpr.ofExpr funcInfo None loc
            let locVar = Option.get <| KExpr.tryGetVar kLoc
            fnAddTagPub var <| TagMemoryLoad (mkTagVar memVar, mkTagVar locVar) |>ignore
            (* if this is a memory region, this is actually a memory *)
            match kLoc with
            | KNum (_, bv) when BitVector.isEqualTo bv 0x40UL ->
              // fnAddTagPub var <| TagHasType TyBytes |> ignore
              fnAddTagPub var <| TagIsFreeMemPtr |> ignore
              (* 나중에 타입이 결정되지 않았다면 bytes라고 가정한다 *)
            | _ -> ()
  #if TYPEDEBUG
            printfn "*mload loc: %A" kLoc
  #endif
            (*
            match kLoc with
            (* mload(freeptr)*)
            | _ when fnIsKExprFreePtr kLoc ->
              let rootMemVar = fnGetRootMemVarFromFreePtrVar locVar

              let tag = TagMemoryDeref (rootMemVar, locVar)
              fnAddTag var tag |> ignore
            (* mload(arr[])*)

            let tag = TagMemoryDeref (memVar, locVar)
            fnAddTag var tag |> ignore
            *)


          (* Def - SLOAD *)
          | BinOp (BinOpType.APP, _, FuncName "sload", ExprList args) ->
            let loc = List.head args
            let kLoc = KExpr.ofExpr funcInfo None loc
            ()
  #if TYPEDEBUG
            printfn "sload: %x %A" pp.Address (IRHelper.symbolicExpand cpState loc)
            printfn "sload: %x %A" pp.Address kLoc
  #endif
            let locVar = Option.get (KExpr.tryGetVar kLoc)
            fnAddTagPub var <| TagStorageLoad (mkTagVar locVar) |> ignore
          (* Def - SHA3 (KECCAK256) *)
          | BinOp (BinOpType.APP, _, FuncName "keccak256", ExprList args) ->
            let [ mem; loc; len ] = args
            let memTagVar = mkTagVar (Option.get <| KExpr.tryGetVar (KExpr.ofExpr funcInfo None mem))
            let locTagVar = mkTagVar (Option.get <| KExpr.tryGetVar (KExpr.ofExpr funcInfo None loc))
            let lenTagVar = mkTagVar (Option.get <| KExpr.tryGetVar (KExpr.ofExpr funcInfo None len))
            fnAddTagPub var <| TagHash (memTagVar, locTagVar, lenTagVar) |> ignore
          (* Def - CALL-related *)
          | BinOp (BinOpType.APP, _, FuncName fname, ExprList args)
              when isInsCallRelated fname ->
            let addrExpr = List.skip 1 args |> List.head (* 2nd: address *)
            let addrVar = Option.get (KExpr.tryGetVar (KExpr.ofExpr funcInfo None addrExpr))
            let tag = TagAddress
            fnAddTagPub addrVar tag |> ignore
            //printfn "call: %x %A" pp.Address (IRHelper.symbolicExpand cpState addrExpr)
            ()
          (* Def - CALLDATALOAD *)
          | BinOp (BinOpType.APP, _, FuncName "msg.data", ExprList args) ->
            let loc = List.head args
            let kLoc = KExpr.ofExpr funcInfo None loc
            let locVar = Option.get (KExpr.tryGetVar kLoc)
            (* TODO: is it necessary? *)
            fnAddTagPub locVar <| TagCalldataPtr |> ignore
            fnAddTagPub var <| TagCalldataLoad (mkTagVar locVar) |> ignore
  #if TYPEDEBUG
            printfn "calldataload: %x %A" pp.Address (IRHelper.symbolicExpand cpState loc)
            printfn "calldataload: %x %A" pp.Address kLoc
            if fnIsPhiVar locVar then
              let phiInfo = fnTryGetPhiInfo locVar
              match phiInfo with
              | Some { Initial = init; Delta = delta } ->
                let initValue = KExpr.ofExpr funcInfo None (Var init)
                let deltaValue = KExpr.ofExpr funcInfo None (Var delta)
                printfn "calldataload-phi: %x %A %A %A" pp.Address locVar initValue deltaValue
              | _ -> ()
  #endif
          | _ -> ()
          ()
        (*
          Stmt - external call
          : 여기에는 리턴값이 없는 external call들이 온다.
          ex) return, mstore, sstore, ...
        *)
        | ExternalCall (BinOp (BinOpType.APP, _, FuncName fnName, ExprList args), inVars, outVars) ->
  #if TYPEDEBUG
          let _ =
            let args = Expr.unrollAppArgs [] args
            // let args = args |> List.map (fun e -> IRHelper.symbolicExpand cpState e)
            let args = args |> List.map (fun e -> KExpr.ofExpr funcInfo None e)
            let inVars = inVars |> List.map (fun v -> IRHelper.symbolicExpand cpState (Var v))
            let outVar = outVars
            //printfn "extcall: %A |-> %s(%A, %A)" outVar fnName args inVars
            ()
  #endif
          match fnName with
          (* return *)
          | "return" ->
            let [ a1; a2 ] = args
            let [ inMemVar ] = inVars
            let loc = a1
            let len = a2
            let locVar = Option.get (KExpr.tryGetVar (KExpr.ofExpr funcInfo None loc))
            let lenVar = Option.get (KExpr.tryGetVar (KExpr.ofExpr funcInfo None len))

            let tag = TagReturn (mkTagVar inMemVar, mkTagVar locVar, mkTagVar lenVar)
            fnAddTagPub inMemVar tag |> ignore

            (*
            match KExpr.ofExpr funcInfo None data with
            | e when fnIsKExprFreePtr e ->
              let rootMemOfFreePtr = failwith "TODO"
              let
              ()
            | _ -> ()
            *)

  #if TYPEDEBUG
            //printfn "return: %x %A %A" pp.Address (IRHelper.symbolicExpand cpState a1) (IRHelper.symbolicExpand cpState a2)
  #endif
            ()
          (* calldatacopy -- before ABIEncoderV2 *)
          | "calldatacopy" ->
            let [ outMem ] = outVars
            let [ dst; src; len ] = args
  #if TYPEDEBUG
            printfn "ccopy: %x %A |-> %A (%A)"
              pp.Address
              (Pp.expToString <| IRHelper.symbolicExpand cpState dst)
              (Pp.expToString <| IRHelper.symbolicExpand cpState src)
              (Pp.expToString <| IRHelper.symbolicExpand cpState len)
  #endif
            let dstVar = Option.get (KExpr.tryGetVar (KExpr.ofExpr funcInfo None dst))
            let srcVar = Option.get (KExpr.tryGetVar (KExpr.ofExpr funcInfo None src))
            let lenVar = Option.get (KExpr.tryGetVar (KExpr.ofExpr funcInfo None len))
            let tag = TagCalldataCopy2 (mkTagVar dstVar, mkTagVar srcVar, mkTagVar lenVar)
            fnAddTagPub outMem tag |> ignore
            (*
            let fn ptrExpr dstVar srcVar lenVar =
              let rootMem =
                fnTryGetRootMemVarFromFreePtrVar (Option.get <| KExpr.tryGetVar ptrExpr)
                |> Option.get
                |> fnFindDominatingFreeMemVar
              let tag = TagCalldataCopy (mkTagVar rootMem, dstVar, srcVar, lenVar)
              fnAddTagPub outMem tag |> ignore
            match KExpr.ofExpr funcInfo None dst with
            (* [ basePtr ] |-> value *)
            | e when fnIsKExprFreePtr e ->
              let kSrc = KExpr.ofExpr funcInfo None src
              let kLen = KExpr.ofExpr funcInfo None len
              let dstVar = None
              let srcVar = Option.get <| KExpr.tryGetVar kSrc
              let lenVar = Option.get <| KExpr.tryGetVar kLen
              fn e (Option.map mkTagVar dstVar) (mkTagVar srcVar) (mkTagVar lenVar)
            (* [ basePtr + offset ] |-> value *)
            | KBinOp (_, BinOpType.ADD,
                      offset,
                      basePtr)
            | KBinOp (_, BinOpType.ADD,
                      basePtr,
                      offset)
                when fnIsKExprFreePtr basePtr ->
              let kSrc = KExpr.ofExpr funcInfo None src
              let kLen = KExpr.ofExpr funcInfo None len
              let dstVar = KExpr.tryGetVar offset
              let srcVar = Option.get <| KExpr.tryGetVar kSrc
              let lenVar = Option.get <| KExpr.tryGetVar kLen
              fn basePtr (Option.map mkTagVar dstVar) (mkTagVar srcVar) (mkTagVar lenVar)
            | _ -> ()
            *)
          (* sstore *)
          | "sstore" ->
            let inMem = List.head inVars
            let outMem = List.head outVars
            let [ addr; value ] = args
            let addrExpr = KExpr.ofExpr funcInfo None addr
            let valueExpr = KExpr.ofExpr funcInfo None value
            let addrVar = Option.get (KExpr.tryGetVar addrExpr)
            let valueVar = Option.get (KExpr.tryGetVar valueExpr)
            //fnAddTagPub outMem <| TagSStore (mkTagVar addrVar, mkTagVar valueVar) |> ignore
            fnAddTagPub outMem <| TagStorageStore (mkTagVar addrVar, mkTagVar valueVar)
          (*
            mstore8/mstore
            : aliasing 힌트들을 모은다
          *)
          | "mstore8"
          | "mstore" ->
            if fnName = "mstore8" then
              ()
            let [ addrExpr; valueExpr ] = args
            let inMem = List.head inVars
            let outMem = List.head outVars
  #if TYPEDEBUG
            if pp.Address = 0xd0bUL then ()
            printfn "mstore: %x %A |-> %A" pp.Address (Pp.expToString <| IRHelper.symbolicExpand cpState addrExpr) (Pp.expToString <| IRHelper.symbolicExpand cpState valueExpr)
  #endif
            let inMemTagVar = TagVarPublic (pubAddr, inMem)
            let addrTagVar = TagVarPublic (pubAddr, Expr.toVar addrExpr)
            let valueTagVar = TagVarPublic (pubAddr, Expr.toVar valueExpr)
            let tag = TagRawMemStore (inMemTagVar, addrTagVar, valueTagVar)
            fnAddTagPub outMem <| tag
          | _ -> ()
        | Jmp jmp ->
          match jmp with
          | InterCJmp (Extract (Var var, _, _), tbr, fbr) ->
            let rootVar = findRootVar cpState var
            let kE = KExpr.ofExpr funcInfo None (Var rootVar)
  #if TYPEDEBUG
            printfn "[+] Cond jmp: %A" kE
            printfn "[+] Cond jmp: %A" (IRHelper.symbolicExpand cpState (Var rootVar) |> Pp.expToString)
  #endif
            match kE with
            (*
              ((sload(n) & 0x1) = (someVar < 0x20)) = 0
              might be due to optim..
              not ((A && B) or (!A && !B))
              => (A || B) and (A || B) => A || B...!!!!
              wow?
              => bytes to memory 패턴
            *)
            | KCast
                (_, _,
                 KRelOp
                   (_, RelOpType.EQ,
                    KCast
                      (_, _,
                       KRelOp
                         (_, RelOpType.EQ,
                          KBinOp
                            (_, BinOpType.AND,
                             KBinOp
                               (_, BinOpType.APP, KFuncName "sload",
                                KExprList
                                  (_, [ KNum (_, bv_slot) ])),
                             KNum (_, bv_0x1)),
                          KCast
                            (_, _,
                             KRelOp
                               (_, RelOpType.LT, (KVar _ as somePhiVar),
                                KNum (_, bv_0x20))))),
                    KNum (_, bv_0x0)))
              when BitVector.isEqualToUInt64 bv_0x1 1UL
                && BitVector.isEqualToUInt64 bv_0x20 0x20UL
                && bv_0x0.IsZero
                && fnIsPhiVar (KExpr.toVar somePhiVar) ->
              let symLocPos = (* sha3(n) + _ *)
                  SymLoc.Hash [ SymLoc.Const bv_slot ] + SymLoc.PlaceHolder
              let newTagVar = TagVarSym symLocPos
              addNewTagVar newTagVar
              (* bytes로 쓰였다는 tag 추가 *)
              fnAddTag newTagVar <| TagHasType TyBytes |> ignore
            (*
              이것도 bytes 변환 패턴
            *)
            | KBinOp
                (_, BinOpType.SUB,
                 KBinOp
                   (_, BinOpType.AND,
                    KBinOp
                      (_, BinOpType.APP, KFuncName "sload",
                       KExprList (None, [ KNum (_, bv_slot) ])),
                    KNum (_, bv_0x1)),
                 KCast
                   (_, _,
                    KRelOp
                      (_, RelOpType.LT, (KVar _ as somePhiVar),
                       KNum (_, bv_0x20))))
              when BitVector.isEqualToUInt64 bv_0x1 1UL
                && BitVector.isEqualToUInt64 bv_0x20 0x20UL
                && fnIsPhiVar (KExpr.toVar somePhiVar) ->
              (* 아 goto 마렵다*)
              let symLocPos = (* sha3(n) + _ *) SymLoc.Hash [ SymLoc.Const bv_slot ] + SymLoc.PlaceHolder
              let newTagVar = TagVarSym symLocPos
              addNewTagVar newTagVar
              (* bytes로 쓰였다는 tag 추가 *)
              fnAddTag newTagVar <| TagHasType TyBytes |> ignore
            (*
              condjmp(iszero(var),...)
              높은 확률로 bool이다
            *)
            | KCast (_, _, KRelOp (_, RelOpType.EQ, someKExpr, KNum (_, bv_0)))
            | KCast (_, _, KRelOp (_, RelOpType.EQ, KNum (_, bv_0), someKExpr))
                when BitVector.isEqualTo bv_0 0UL ->
              let someVar = Option.get (KExpr.tryGetVar someKExpr)
              fnAddTagPub someVar <| TagUsedAsHighLevJumpCond |> ignore
              (*
                condjmp(iszero(iszero(var)),...)
              *)
              match someKExpr with
              | _ when fnIsPhiVar someVar ->
                let phiOperandVars = fnGetPhiIds someVar |> fnExpandPhiVarsToKExprs someVar
                for phiOperVar in phiOperandVars do
                  match phiOperVar with
                  | KCast (_, _, KRelOp (_, RelOpType.EQ, someKExpr2, KNum (_, bv_0_2)))
                  | KCast (_, _, KRelOp (_, RelOpType.EQ, KNum (_, bv_0_2), someKExpr2))
                      when BitVector.isEqualTo bv_0_2 0UL ->
                    let someVar2 = Option.get (KExpr.tryGetVar someKExpr2)
                    fnAddTagPub someVar2 <| TagUsedAsHighLevJumpCond |> ignore
                  | _ -> ()
              | KCast (_, _, KRelOp (_, RelOpType.EQ, someKExpr2, KNum (_, bv_0_2)))
              | KCast (_, _, KRelOp (_, RelOpType.EQ, KNum (_, bv_0_2), someKExpr2))
                  when BitVector.isEqualTo bv_0_2 0UL ->
                let someVar2 = Option.get (KExpr.tryGetVar someKExpr2)
                fnAddTagPub someVar2 <| TagUsedAsHighLevJumpCond |> ignore
              | _ -> ()
            (*
              condjmp(var,...)
              높은 확률로 bool이다
            *)
            | someKExpr ->
              let someVar = KExpr.toVar someKExpr
              if fnIsPhiVar someVar then (* 하나하나 ㄱㄱ*)
                let phiOperandVars = fnGetPhiIds someVar |> fnExpandPhiVarsToKExprs someVar
                for phiOperVar in phiOperandVars do(*이러면 KExpr거쳐서 자연히 rootvar*)
                  let var = Option.get (KExpr.tryGetVar phiOperVar)
                  fnAddTagPub var <| TagUsedAsHighLevJumpCond |> ignore
              let someVar = Option.get (KExpr.tryGetVar someKExpr)
              fnAddTagPub someVar <| TagUsedAsHighLevJumpCond |> ignore
            | _ -> ()
          | _ when jmp.IsInterCJmp ->
            ()
          | _ ->
            ()
          ()
        | _ -> ()
      (* go to next step *)
      (*
      for succ in DiGraph.GetSuccs (ssa, v) do
        dfs recentPrivAddr visited succ
      *)
      let succs = ssa.GetSuccs v |> Array.toList
      let vs' = List.append vs' succs
      dfs recentPrivAddrs visited vs'
  dfs Set.empty Set.empty [ entryVertex ]

