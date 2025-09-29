module Engine.Solve

open System.Collections.Generic

open B2R2
open B2R2.BinIR
open B2R2.BinIR.SSA

open TypeRecTypes
open CPTypes
open SolveInfo
open EVMpress.Type

let rt =256<rt>

let private handleMemorySymLoc solveInfo currTagVar tags =
  match currTagVar with
  | TagVarSym (SymLoc.FreeMemPtr (pubAddr, rootMid) as symLocPtr) ->
    (*
      handle constant-sized bytes
    *)
    let symLocPtr_0x20 = symLocPtr + SymLoc.Const (BitVector(0x20UL, rt))
    let symLocVal = SymLoc.MLoad (pubAddr, symLocPtr)
    for tag in (solveInfo: SolveInfo).GetTagsFromTagVar <| TagVarSym symLocVal do
      match tag with
      | TagEqualsTo dstVar ->
        let dstVarExpr = (solveInfo: SolveInfo).GetKExprFromTagVar dstVar
        match dstVarExpr with
        (* 1. constant n *)
        | KNum (_, bv_n) ->
          let tagVarVal_0x20 = TagVarSym <| SymLoc.MLoad (pubAddr, symLocPtr_0x20)
          for tag in solveInfo.GetTagsFromTagVar tagVarVal_0x20 do
            match tag with
            | TagEqualsTo dstVar_0x20 ->
              (* 2. the value has (256 - n * 8) bitvector *)
              (* then -> bytes *)
              (*TODO: consider optim*)
              match solveInfo.GetKExprFromTagVar dstVar_0x20 with
              | KBinOp (_, BinOpType.SHL, KNum (_, bv_value), KNum (_, bv_bits))
                when bv_bits + bv_n * 8UL = BitVector(0x100UL, rt) ->
                let tagVarPtr = TagVarSym <| symLocPtr
                solveInfo.AddTag currTagVar tagVarPtr <| TagHasType TyBytes
                ()
              | _ -> ()
            | _ -> ()
        (* 1. M[0] |-> cload(...) => T[] *)
        (* TODO: check the actual ... *)
        | KBinOp (_, _, KFuncName "msg.data", _) ->
          let tagVarVal_0x20 = TagVarSym <| SymLoc.MLoad (pubAddr, symLocPtr_0x20)
          for tag in solveInfo.GetTagsFromTagVar tagVarVal_0x20 do
            match tag with
            | TagEqualsTo dstVar_0x20 ->
              (* 2. the value has (256 - n * 8) bitvector *)
              (* then -> bytes *)
              (*TODO: consider optim*)
              match solveInfo.GetKExprFromTagVar dstVar_0x20 with
              | _ -> ()
            | _ -> ()
          ()
        | _ -> ()
      | _ -> ()
      ()

    (*
    match symLocLoc with
    | SymLoc.FreeMemPtr (_, memId) ->
      ()
    | SymLoc.BinOp (BinOpType.ADD, SymLoc.FreeMemPtr (_, memId), symLocOff) ->
      ()
    | _ -> ()
    *)
  | _ -> ()

let solveConstraints (solveInfo: SolveInfo) =
  (*
    2. solve hints ---
    add new tags into the tag (constraint) set
  *)
  /// tags waiting for being added into the perVarTags.
  /// this is for preventing invalid access
  solveInfo.InitWorklist ()
  //solveInfo.PerVarTags.Keys |> Seq.iter (fun var -> varQueue.Enqueue var)

  while not <| solveInfo.Worklist.IsEmpty do
    let currVar = solveInfo.Worklist.Dequeue ()
    // let tags = solveInfo.PerVarTags[currVar]
    let untouchedTags = solveInfo.PopUntouchedTags currVar
(*
    match currVar with
    | TagVarPublic (_, { Kind = StackVar (_, -352L); Identifier = 4 }) ->
      printfn "."
    | _ -> ()

*)

    if currVar |> (function | TagVarSym (SymLoc.FreeMemPtr _) -> true | _ -> false) then
      let tags = solveInfo.GetTagsFromTagVar currVar
      handleMemorySymLoc solveInfo currVar tags

    for untouchedTag in untouchedTags do
      (*
        directly propagate its tag into the target variable
      *)
      (* e.g. x: address and x = y -> y: address
         this is useful when we resolve memory aliasing *)
      match untouchedTag with
      | TagEqualsTo dstVar ->
        match dstVar with
        | TagVarSym (SymLoc.CLoad _) ->
          ()
        | _ -> ()
        untouchedTags
        |> Seq.filter (fun tag ->
          match tag with
          | TagEqualsTo _ -> false
          | _ -> true)
        |> Seq.iter (fun tag -> solveInfo.AddTag currVar dstVar tag)
      | _ -> ()

      (*
        propagate tags into its sub-expressions
      *)
      (*
      match tag with
      (* calldata ptr property *)
      | TagCalldataPtr
      (* array prorperty *)
      | TagArray _ ->
        let kExpr = solveInfo.GetKExprFromTagVar currVar
        let pubAddr = getPubAddrFromTagVar currVar
        match kExpr with
        (*
        | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x4),
                                    KBinOp (_, BinOpType.APP, KFuncName "msg.data", args))
            when isBVEqualTo bv_0x4 0x4 ->
          let args = KExpr.unrollAppArgs args
          let loc = List.head args
          match loc with
          | KNum (_, bv) ->
            ()
          | KBinOp (_, BinOpType.ADD, KNum _, KNum _) ->
            ()
          | _ -> ()
          let var1 = Option.get (KExpr.tryGetVar kE1)
          let var2 = Option.get (KExpr.tryGetVar kE2)
          fnAddTag var1 tag
          fnAddTag var2 tag
        *)
        (*
        | KBinOp (_, BinOpType.ADD, kE1, kE2) ->
          let var1 = Option.get (KExpr.tryGetVar kE1)
          let var2 = Option.get (KExpr.tryGetVar kE2)
          fnAddTag (mkTagVar pubAddr var1) tag
          fnAddTag (mkTagVar pubAddr var2) tag
        *)
        | KBinOp (_, BinOpType.ADD, kE1, kE2) ->
          let fnIsCLoad kE =
            match kE with
            | KBinOp (_, BinOpType.APP, KFuncName "msg.data", _) -> true
            | _ -> false
          let var1 = Option.get (KExpr.tryGetVar kE1)
          let var2 = Option.get (KExpr.tryGetVar kE2)
          if fnIsCLoad kE1 then
            solveInfo.AddTag currVar (mkTagVarPub pubAddr var1) tag
          elif fnIsCLoad kE2 then
            solveInfo.AddTag currVar (mkTagVarPub pubAddr var2) tag
        | _ -> ()
      | _ -> ()
      *)

      SolveMemory.handleMemoryTags solveInfo currVar untouchedTag
      SolveStorage.handleStorageTags solveInfo currVar untouchedTag
      SolveCalldata.handleCalldataTags solveInfo currVar untouchedTag

      (*
        memory aliasing rules --- load
        from mload to store operations (e.g. mstore, calldatacopy)
      *)
      (*
      match tag with
      | TagMemoryDeref (memVar, locVar) ->
        /// collect tags on the given memory region
        /// TODO: too inefficient
        let cpState = fnGetCPStateFromTagVar memVar
        let pubAddr = fnGetPubAddrFromTagVar memVar
        let fnCollectTagsOnFreeMem memPtrVar =
          let lowerBoundMem = Option.get <| fnTryGetRootMemVarFromFreePtrVar perPubFuncDataFlows[pubAddr].RootMemMemo cpState memPtrVar
          let workingMemVars = UniqueQueue ()
          let visited = HashSet ()
          let collectedTags = HashSet () (*TODO: use queue to preserve the visiting order*)
          workingMemVars.Enqueue <| TagVar.toVar memVar
          while not workingMemVars.IsEmpty do
            let currMemVar = workingMemVars.Dequeue ()
            visited.Add currMemVar.Identifier |> ignore
            (* parse tags *)
            match perVarTags.TryGetValue <| TagVarPublic (pubAddr, currMemVar) with
            | false, _ -> ()
            | true, tags -> tags |> Seq.iter (fun tag -> collectedTags.Add (currMemVar, tag) |> ignore)
            (* proceed *)
            if currMemVar = lowerBoundMem then ()
            else
              match cpState.SSAEdges.Defs.TryFind currMemVar with
              | None -> () (* TODO: is this possible? *)
              | Some (_, stmt) ->
                match stmt with
                | Phi (_, ids) ->
                  ids
                  |> Seq.map (fun id -> { currMemVar with Identifier = id })
                  |> Seq.filter (fun memVar -> not <| visited.Contains memVar.Identifier)
                  |> Seq.iter workingMemVars.Enqueue
                | ExternalCall (e, inVars, outVars) ->
                  let [ inMemVar ] = inVars
                  if not <| visited.Contains inMemVar.Identifier then
                    workingMemVars.Enqueue inMemVar
                | Def (_, e) -> () (* this cannot happen; Def-Store is only defined by stack store ops *)
                | _ -> failwith "TODO: invalid stmt"
          collectedTags
        let rec fnExtractConstantFromOffsetExpr offsetExpr =
          match offsetExpr with
          | KNum (_, bv) -> Some bv
          (* offset + (0x20 * i) *)
          | KBinOp (_, BinOpType.ADD, KNum (_, bv),
                                      KBinOp (_, BinOpType.MUL, a, b)) ->
            Some bv
          | _ -> None
        let fn memPtr offsetLoadBv =
          let memPtrVar = Option.get <| KExpr.tryGetVar memPtr
          let history = fnCollectTagsOnFreeMem memPtrVar
          let freeRootMem = Option.get <| fnTryGetRootMemVarFromFreePtrVar perPubFuncDataFlows[pubAddr].RootMemMemo cpState memPtrVar
          (* aliasing *)
          for currMem, tag in history do
            match tag with
            | TagCalldataCopy (freeRootMem', Some (TagVarPublic (_, offsetStoreVar)), locVar, lenVar)
                when TagVar.toVar freeRootMem' = freeRootMem ->
              (* check if load and store operations are on the same offset *)
              let offsetStoreExpr = KExpr.ofExpr funcInfo None (Var offsetStoreVar)
              let offsetStoreBv = fnExtractConstantFromOffsetExpr offsetStoreExpr
              match offsetStoreBv with
              | Some bv when bv = offsetLoadBv ->
                fnAddEquality currVar currVar (TagVarPublic (pubAddr, currMem)) (* we use mem since there is no explicit stack var for ccopy*)
              | _ -> ()
            | TagFreeMemStore (freeRootMem', Some (TagVarPublic (_, offsetStoreVar)), valueVar)
                when TagVar.toVar freeRootMem' = freeRootMem ->
              (* check if load and store operations are on the same offset *)
              let offsetStoreExpr = KExpr.ofExpr funcInfo None (Var offsetStoreVar)
              let offsetStoreBv = fnExtractConstantFromOffsetExpr offsetStoreExpr
              match offsetStoreBv with
              | Some bv when bv = offsetLoadBv ->
                fnAddEquality currVar currVar valueVar
              | _ -> ()
            | TagFreeMemStoreWithPhi (freeRootMem', Some (TagVarPublic (_, offsetStoreVar)), deltaVar, valueVar)
                when TagVar.toVar freeRootMem' = freeRootMem ->
              (* check if load and store operations are on the same offset *)
              let offsetStoreExpr = KExpr.ofExpr funcInfo None (Var offsetStoreVar)
              let offsetStoreBv = fnExtractConstantFromOffsetExpr offsetStoreExpr
              match offsetStoreBv with
              | Some bv when bv = offsetLoadBv ->
                fnAddEquality currVar currVar valueVar
              | _ -> ()
            | _ -> ()
        match fnGetKExprFromTagVar locVar with
        (* load(ptr)*)
        (* TODO: merge with fn *)
        | memPtr
            when fnIsKExprFreePtr memPtr ->
          let history = fnCollectTagsOnFreeMem <| TagVar.toVar locVar
          let freeRootMem = Option.get <| fnTryGetRootMemVarFromFreePtrVar perPubFuncDataFlows[pubAddr].RootMemMemo cpState (TagVar.toVar locVar)
          (* aliasing *)
          for currMem, tag in history do
            match tag with
            (* valueVar = var *)
            | TagFreeMemStore (freeRootMem', offsetVar, valueVar)
                when TagVar.toVar freeRootMem' = freeRootMem
                  && offsetVar = None ->
              fnAddEquality currVar currVar valueVar
            | _ -> ()
        (* load((0x20 + ptr) + phi) *)
        | KBinOp (_, BinOpType.ADD, KBinOp (_, BinOpType.ADD, KNum (_, bv_off), memPtr), phiVar)
            when fnIsKExprFreePtr memPtr
              && fnIsPhiVar cpState <| Option.get (KExpr.tryGetVar phiVar) ->
          let phiVar = Option.get <| KExpr.tryGetVar phiVar
          match fnTryGetPhiInfo cpState phiVar with
          | Some phiInfo ->
            let initBv =
              KExpr.ofExpr funcInfo None (Var phiInfo.Initial)
              |> function
                | KNum (_, bv) -> bv
            let startPos = BitVector.Add (bv_off, initBv)
            fn memPtr startPos
          | None -> ()
        (* load(ptr + offset)*)
        | KBinOp (_, BinOpType.ADD, memPtr, offsetLoad)
        | KBinOp (_, BinOpType.ADD, offsetLoad, memPtr)
            when fnIsKExprFreePtr memPtr ->
          let memPtrVar = Option.get <| KExpr.tryGetVar memPtr
          match fnExtractConstantFromOffsetExpr offsetLoad with
          | Some offsetLoadBv -> fn memPtr offsetLoadBv
          | _ -> () (* TODO: offset is not a constant *)
        (* etc. *)
        | e ->
          ()
      | _ -> ()
      *)

      (* mem store *)
      (*
      match tag with
      | TagFreeMemStore (rootMem, Some offVar, valueVar) ->
        let valueKExpr = solveInfo.GetKExprFromTagVar valueVar
        (*
          constant string pattern:
          p + 0    |-> len (bytes)
          p + off  |-> (constant << bits) where len * 8 + bits = 257
        *)
        match valueKExpr with
        | KBinOp (_, BinOpType.SHL, KNum (Some constVar, bv), KNum (_, bv_bits)) ->
          let rec fnGetBitVectorBytes bv =
            let bv = BitVector.Shr (bv, BitVector.OfUInt64 0x8UL 256<rt>)
            if BitVector.IsZero bv then 0
            else 1 + fnGetBitVectorBytes bv
          (* add one for null terminator*)
          let constBytes = fnGetBitVectorBytes bv |> uint64 |> (+) 1UL
          let shiftedBits = BitVector.ToUInt64 bv_bits
          if constBytes * 8UL + shiftedBits = 257UL then
            (* TODO: is it consistent to add a tag to its root mem? *)
            solveInfo.AddTag currVar rootMem <| TagString
            ()
          else ()
        | _ -> ()
      | _ -> ()
      *)

      (*
        calldata arg copy types -- structural (under v1)
      *)
      (*
      match tag with
      | TagCalldataCopy (freePtrRootMem, dstVar, srcVar, lenVar)->
        let srcExpr = solveInfo.GetKExprFromTagVar srcVar
        let pubAddr = fnGetPubAddrFromTagVar srcVar
        match srcExpr with
        (* 1-d dyn array
          copy(dst, loc + 0x20, len) *)
        | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20_1), srcBaseLoc)
        | KBinOp (_, BinOpType.ADD, srcBaseLoc, KNum (_, bv_0x20_1))
            when BitVector.isEqualTo bv_0x20_1 0x20 ->
          (* note that ccopy does not have a stack var;
             so we use the memory as a deref variable *)
          let srcBaseLocVar = Option.get <| KExpr.tryGetVar srcBaseLoc
          solveInfo.AddTag currVar (TagVarPublic (pubAddr, srcBaseLocVar)) <| TagArray (currVar, 0)
        | _ -> ()
        ()
      | _ -> ()
      *)

      (*
        calldata arg deref types -- structural
      *)
      (*
      match tag with
      | TagCalldataLoad locVar ->
        let kLoc = solveInfo.GetKExprFromTagVar locVar
        let cpState = solveInfo.GetCPStateFromTagVar locVar
        let pubAddr = fnGetPubAddrFromTagVar locVar
        match kLoc with
        (* phi var -> possibly array *)
        | KVar locVar when fnIsPhiVar cpState locVar ->
          let phiInfo = fnTryGetPhiLoopInfo cpState locVar
          match phiInfo with
          | None -> ()
          | Some phiInfo ->
            let initial = KExpr.ofExpr funcInfo None <| Var phiInfo.Initial
            let delta = KExpr.ofExpr funcInfo None <| Var phiInfo.Delta
#if TYPEDEBUG
            printfn "%A %A" initial delta
#endif
            match initial, delta with
            (* [memory] 1-dim dyn array
               init = cptr + 0x20;
               delta = 0x20 *)
            (* previous version *)
            (*
            | KBinOp (_, BinOpType.ADD, baseCPtr, KNum (_, bv_0x20_1)),
              KNum (_, bv_0x20_2)
            | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20_1), baseCPtr),
              KNum (_, bv_0x20_2)
                when isBV0x20 bv_0x20_1
                  && isBV0x20 bv_0x20_2 ->
            *)
            | KBinOp (_, BinOpType.ADD, baseCPtr, KNum (_, bv)),
              KNum (_, bv_0x20_2)
            | KBinOp (_, BinOpType.ADD, KNum (_, bv), baseCPtr),
              KNum (_, bv_0x20_2)
                when BitVector.isEqualTo bv_0x20_2 0x20 ->
              let baseCPtrVar = Option.get <| KExpr.tryGetVar baseCPtr
              solveInfo.AddTag currVar (TagVarPublic (pubAddr, baseCPtrVar))
              <| TagArray (currVar, 0)
            | _ -> ()
        (* [calldata] 1-dim array *)
        | KBinOp (_, BinOpType.ADD, KBinOp (_, BinOpType.MUL, KNum (_, bv_0x20_1), idx),
                                    KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20_2), baseAddr))
            when BitVector.isEqualTo bv_0x20_1 0x20
              && BitVector.isEqualTo bv_0x20_2 0x20 ->
          match KExpr.tryGetVar idx with
          | Some idxVar ->
            match solveInfo.PerVarTags.TryGetValue (TagVarPublic (pubAddr, idxVar)) with
            | false, _ -> ()
            | true, idxTags ->
              match idxTags |> Seq.tryFind (fun tag -> match tag with TagLt _ -> true | _ -> false) with
              | Some (TagLt ubVar) ->
                match solveInfo.PerVarTags.TryGetValue ubVar with
                | false, _ -> ()
                | true, ubTags ->
                  if ubTags |> Seq.exists (fun tag -> match tag with TagCalldataLoad _ -> true | _ -> false) then
                    (* dynamic array *)
                    let baseAddrVar = Option.get (KExpr.tryGetVar baseAddr)
                    solveInfo.AddTag currVar (TagVarPublic (pubAddr, baseAddrVar)) (TagArray (currVar, 0))
                  else
                    () (* TODO*)
              | _ -> ()
          | _ -> ()
          ()
        | _ -> ()
        ()
      (* TODO: other tags *)
      | _ -> ()

      match tag with
      | TagAddress ->

        ()
      | _ -> ()
      ()
      *)
    (* handle temp tags *)
    match solveInfo.PerVarTempTags.TryGetValue currVar with
    | false, _ -> ()
    | true, tags ->
      match solveInfo.PerVarTags.TryGetValue currVar with
      | false, _ ->
        let tags' = HashSet ()
        tags'.UnionWith tags
        solveInfo.PerVarTags[currVar] <- tags'
      | true, tags' ->
        tags'.UnionWith tags
      solveInfo.PerVarTempTags[currVar].Clear ()

    match solveInfo.PerVarTags.TryGetValue currVar with
    | false, _ -> ()
    | true, tags ->
      /// TODO: just separate tags for equality
      for tag in tags do
        match tag with
        (* if equal to exists *)
        | TagEqualsTo dstVar when dstVar <> currVar ->
          (* then prop *)
          for tag' in tags do
            if tag'.IsTagEqualsTo |> not then
              (*FIXME: is it safe? *)
              solveInfo.AddTagBase currVar dstVar tag' false
        | _ -> ()

