module Engine.SolveCalldata

open Types
open B2R2.BinIR.SSA
open CPTypes
open TypeRecTypes
open Helper
open B2R2.BinIR
open B2R2
open SolveInfo
open EVMpress.Type

[<AutoOpen>]
module private SolveCalldataHelper =
  let rec private convertToCallSymLoc pubAddr kExpr =
    match kExpr with
    | KNum (_, bv_loc) -> SymLoc.Const bv_loc
    | KBinOp (_, _, KFuncName "msg.data", args) ->
      let [ innerLoc ] = KExpr.toList args
      match KExpr.constantFolding innerLoc with
      | KNum (_, bv_offset) ->
        SymLoc.CLoad (pubAddr, SymLoc.Const bv_offset)
      | _ -> SymLoc.PlaceHolder
    (*
    | KBinOp (_, BinOpType.ADD, KNum (_, bv_x), KNum (_, bv_y)) ->
    *)
    (*
    | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x4), KBinOp (_, _, KFuncName "msg.data", args))
    | KBinOp (_, BinOpType.ADD, KBinOp (_, _, KFuncName "msg.data", args), KNum (_, bv_0x4))
      when BitVector.isEqualTo bv_0x4 0x4 ->
      let [ innerLoc ] = KExpr.toList args
      match KExpr.constantFolding innerLoc with
      | KNum (_, bv_offset) ->
        SymLoc.Const bv_0x4 + SymLoc.CLoad (pubAddr, SymLoc.Calldata (pubAddr, bv_offset))
      | _ -> SymLoc.PlaceHolder
    *)
    | KBinOp (_, BinOpType.ADD, x, y) ->
      convertToCallSymLoc pubAddr x + convertToCallSymLoc pubAddr y
    | _ -> SymLoc.PlaceHolder

  let handleTagCalldataLoad (solveInfo: SolveInfo) currTagVar locTagVar =
    let kExpr = solveInfo.GetKExprFromTagVar locTagVar
    let pubAddr = getPubAddrFromTagVar locTagVar
    (* TODO: 어느 정도 pattern 일반화되면, storage에서처럼 SymLoc으로 변환하는 함수 도입 *)
    match kExpr with
    (*
      phi
    *)
    | KVar _ ->
      // let exprs = getPossibleKExprsFromPhiKVar solveInfo pubAddr kExpr
      let funcInfo = solveInfo.GetFuncInfoFromTagVar locTagVar
      let var = kExpr |> KExpr.toVar
      match fnTryGetPhiLoopInfo funcInfo var with
      | Some phiLoopInfo ->
        let initialTagVar = TagVarPublic (pubAddr, phiLoopInfo.Initial)
        let initialKExpr = solveInfo.GetKExprFromTagVar initialTagVar
        let deltaTagVar = TagVarPublic (pubAddr, phiLoopInfo.Delta)
        let deltaKExpr = solveInfo.GetKExprFromTagVar deltaTagVar
        match initialKExpr, deltaKExpr with
        (*
        (*
          initial = ???
          delta = 0x20
        *)
        | _, KNum (_, bv_0x20)
          when BitVector.isEqualTo bv_0x20 0x20
          ->
          let symLocBaseLoc = convertToCallSymLoc pubAddr baseLoc
          let symLocLoc_0x20 = convertToCallSymLoc pubAddr initialKExpr
          let symLocVal = SymLoc.CLoad (pubAddr, symLocLoc_0x20)
          let tagVarVal = TagVarSym symLocVal
          let tagVarBaseLoc = TagVarSym symLocBaseLoc
          let tagVarLoc_0x20 = TagVarSym symLocLoc_0x20
          solveInfo.AddNewTagVar tagVarVal
          solveInfo.AddNewTagVar tagVarBaseLoc
          solveInfo.AddEquality currTagVar currTagVar tagVarVal
          solveInfo.AddTag currTagVar tagVarBaseLoc <| TagHasType (TyArray (TyTop, 0))
          ()
        *)
        (*
          cptr + 0x20,
          0x20
          => 1d dyn array, element access
        *)
        | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20), baseLoc),
          KNum (_, bv_0x20_2)
        | KBinOp (_, BinOpType.ADD, baseLoc, KNum (_, bv_0x20)),
          KNum (_, bv_0x20_2)
          when BitVector.isEqualTo bv_0x20 0x20
            && BitVector.isEqualTo bv_0x20_2 0x20 ->
          (*
          let symLocBaseLoc = convertToCallSymLoc pubAddr baseLoc
          let symLocLoc_0x20 = convertToCallSymLoc pubAddr initialKExpr
          let symLocVal = SymLoc.CLoad (pubAddr, symLocLoc_0x20)
          let tagVarVal = TagVarSym symLocVal
          let tagVarBaseLoc = TagVarSym symLocBaseLoc
          let tagVarLoc_0x20 = TagVarSym symLocLoc_0x20
          solveInfo.AddNewTagVar tagVarVal
          solveInfo.AddNewTagVar tagVarBaseLoc
          solveInfo.AddEquality currTagVar currTagVar tagVarVal
          solveInfo.AddTag currTagVar tagVarBaseLoc <| TagHasType (TyArray (TyTop, 0))
          *)
          let baseLocSymLoc = convertToCallSymLoc pubAddr baseLoc
          let baseLocSymLocTagVar = TagVarSym baseLocSymLoc
          solveInfo.AddTag currTagVar baseLocSymLocTagVar <| TagArray (currTagVar, 0)
          //solveInfo.AddTag currTagVar tagVarLoc_0x20 <| TagPtrBelongsTo tagVarBaseLoc
          //solveInfo.AddTag currTagVar tagVarBaseLoc <| TagHasPtr tagVarLoc_0x20
        | _ -> ()
      | _ -> ()
    (*
      (0x20 * i) + (cptr + 0x20)
      => 1d dyn array (calldata)
    *)
    | KBinOp (_, BinOpType.ADD,
              KBinOp (_, BinOpType.MUL, KNum (_, bv_0x20), someIndexExpr),
              KBinOp (_, BinOpType.ADD, someCPtrExpr, KNum (_, bv_0x20_2)))
    | KBinOp (_, BinOpType.ADD,
              KBinOp (_, BinOpType.MUL, someIndexExpr, KNum (_, bv_0x20)),
              KBinOp (_, BinOpType.ADD, someCPtrExpr, KNum (_, bv_0x20_2)))
    | KBinOp (_, BinOpType.ADD,
              KBinOp (_, BinOpType.MUL, KNum (_, bv_0x20), someIndexExpr),
              KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20_2), someCPtrExpr))
    | KBinOp (_, BinOpType.ADD,
              KBinOp (_, BinOpType.MUL, someIndexExpr, KNum (_, bv_0x20)),
              KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20_2), someCPtrExpr))
      when BitVector.isEqualTo bv_0x20 0x20
        && BitVector.isEqualTo bv_0x20_2 0x20
      ->
      match someCPtrExpr with
      | KBinOp (_, BinOpType.ADD, KNum (_, bv_globalLoc), KBinOp (_, _, KFuncName "msg.data", args))
      | KBinOp (_, BinOpType.ADD, KBinOp (_, _, KFuncName "msg.data", args), KNum (_, bv_globalLoc))
        when BitVector.isEqualTo bv_globalLoc 0x4 ->
        let [innerLoc]= KExpr.toList args
        match KExpr.constantFolding innerLoc with
        | KNum (_, bv_offset) ->
          let symLocLoc = SymLoc.Const bv_offset
          let symLocLocTagVar = TagVarSym symLocLoc
          let symLocVal = SymLoc.CLoad (pubAddr, symLocLoc)
          let symLocValTagVar = TagVarSym symLocVal
          solveInfo.AddNewTagVar symLocLocTagVar
          solveInfo.AddNewTagVar symLocValTagVar
          solveInfo.AddTag currTagVar symLocLocTagVar <| TagHasType (TyArray (TyTop, 0))
          solveInfo.AddEquality currTagVar currTagVar symLocValTagVar
        | _ -> ()
      | _ -> ()
    (*
      cl(const)
      => global prim
    *)
    | KNum (_, bv_const) ->
      (* loc *)
      let symLoc = SymLoc.Const bv_const
      let symLocTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar symLocTagVar
      solveInfo.AddEquality currTagVar locTagVar symLocTagVar
      (* val *)
      let symLoc = SymLoc.Const bv_const
      let symLocTagVar = TagVarSym (SymLoc.CLoad (pubAddr, symLoc))
      solveInfo.AddNewTagVar symLocTagVar
      solveInfo.AddEquality currTagVar currTagVar symLocTagVar
    | _ ->
      match KExpr.constantFolding kExpr with
      | KNum (_, bv_const) ->
        (* loc *)
        let symLoc = SymLoc.Const bv_const
        let symLocTagVar = TagVarSym symLoc
        solveInfo.AddNewTagVar symLocTagVar
        solveInfo.AddEquality currTagVar locTagVar symLocTagVar
        (* val *)
        let symLoc = SymLoc.Const bv_const
        let symLocTagVar = TagVarSym (SymLoc.CLoad (pubAddr, symLoc))
        solveInfo.AddNewTagVar symLocTagVar
        solveInfo.AddEquality currTagVar currTagVar symLocTagVar
      | _ -> ()

  let handleTagCalldataCopy2 (solveInfo: SolveInfo) currTagVar dstTagVar srcTagVar lenTagVar =
    let dstKExpr = solveInfo.GetKExprFromTagVar dstTagVar
    let srcKExpr = solveInfo.GetKExprFromTagVar srcTagVar
    let lenKExpr = solveInfo.GetKExprFromTagVar lenTagVar
    let pubAddr = getPubAddrFromTagVar dstTagVar

    let fnFixMe () =
      match srcKExpr with
      (*
        배열 초기화 패턴!
         memory 관련
        => either bytes or array
      *)
      | KBinOp (_, _, KFuncName "msg.data.size", _) ->
        match dstKExpr with
        | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20), someFreePtr)
        | KBinOp (_, BinOpType.ADD, someFreePtr, KNum (_, bv_0x20))
          when KExpr.isFreePtr someFreePtr
            && BitVector.isEqualTo bv_0x20 0x20 ->
          let var = someFreePtr |> KExpr.toVar
          let tv = TagVarPublic (pubAddr, var)
          let rootMem = tryGetRootMemVarFromFreePtrTagVar solveInfo tv
          match rootMem with
          | None -> ()
          | Some rootMem ->
            let id = rootMem.Identifier
            let symLocLoc = SymLoc.FreeMemPtr (pubAddr, id)
            let tagVarLoc = TagVarSym symLocLoc
            let cpState = solveInfo.GetCPStateFromTagVar srcTagVar
            solveInfo.AddNewTagVar tagVarLoc
            (*
            let possibleLens = fnTryGetPhiArgKExprs cpState lenKExpr
            let isBytes =
              let phiLoopInfo = fnTryGetPhiLoopInfo cpState var
              match possibleLens with
              | None -> false
              | Some lens ->
            *)
            solveInfo.AddTag currTagVar tagVarLoc <| TagHasType (TyArray (TyTop, 0))

        | _ -> ()
      | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20), someCPtr)
      | KBinOp (_, BinOpType.ADD, someCPtr, KNum (_, bv_0x20))
        when BitVector.isEqualTo bv_0x20 0x20
        ->
        match lenKExpr with
        (*
          len = cl(...)
          => bytes (바이트 그대로 복사)
        *)
        | KBinOp (_, _, KFuncName "msg.data", _) ->
          (* 여기서 someCPtr 파싱; TODO: 일반화 *)
          match someCPtr with
          (*
            0x4 + cl(0x4)
            => global (most-upper layer var)
          *)
          | KBinOp (_, BinOpType.ADD, KNum (_, bv_globalBase), KBinOp (_, _, KFuncName "msg.data", args))
          | KBinOp (_, BinOpType.ADD, KBinOp (_, _, KFuncName "msg.data", args), KNum (_, bv_globalBase))
            when BitVector.isEqualTo bv_globalBase 0x4
            ->
            let [ kInnerLoc ] = KExpr.toList args
            match KExpr.constantFolding kInnerLoc with
            | KNum (_, bv_loc) ->
              (* TODO: 이렇게 하면 헷갈린다. 상수더라도 calldata, storage 구분가능하게 해야함 *)
              (* 그러나 애매한 부분이 있어서 Const 사용하는 것으로 rollback한다*)
              (* bytes 타입은 상수에게 주어져야지, calldata로 감싼 것에는 주어지면 안됨 *)
              let symLoc = SymLoc.Const bv_loc
              let symLoc = convertToCallSymLoc pubAddr someCPtr
              let symLocTagVar = TagVarSym symLoc
              solveInfo.AddNewTagVar symLocTagVar
              solveInfo.AddTag currTagVar symLocTagVar <| TagHasType TyBytes
              //let symLocVal = SymLoc.Calldata (pubAddr, symLocLoc)
              //let symLocValTagVar = TagVarSym symLocVal
              //solveInfo.AddNewTagVar symLocValTagVar
              //solveInfo.AddEquality currTagVar currTagVar symLocValTagVar
            | _ -> ()
          | _ -> ()
        (*
          len = 0x20 * cl(...)
          => 1-dim array
        *)
        | KBinOp (_, _,
                  KNum (_, bv_0x20),
                  KBinOp (_, _, KFuncName "msg.data", args))
          when BitVector.isEqualTo bv_0x20 0x20 ->
          (* TODO: merge with similar logics *)
          match someCPtr with
          (*
          | KBinOp (_, BinOpType.ADD, KNum (_, bv_globalBase), KBinOp (_, _, KFuncName "msg.data", args))
          | KBinOp (_, BinOpType.ADD, KBinOp (_, _, KFuncName "msg.data", args), KNum (_, bv_globalBase))
            when BitVector.isEqualTo bv_globalBase 0x4
            ->
            let [ kInnerLoc ] = KExpr.toList args
            match KExpr.constantFolding kInnerLoc with
            | KNum (_, bv_loc) ->
              (* loc *)
              let symLoc = convertToCallSymLoc pubAddr  //SymLoc.Calldata (pubAddr, bv_loc)
              let symLocTagVar = TagVarSym symLoc
              let locTagVar = kInnerLoc |> KExpr.toVar |> fun v -> TagVarPublic (pubAddr, v)
              solveInfo.AddNewTagVar symLocTagVar
              solveInfo.AddEquality currTagVar locTagVar symLocTagVar
              (* val: cload(cload(cloc) + _) => we omit the length field for convinience *)
              let symLocTagVar = TagVarSym <| SymLoc.CLoad (pubAddr, SymLoc.CLoad (pubAddr, symLoc))
              solveInfo.AddNewTagVar symLocTagVar
              solveInfo.AddEquality currTagVar currTagVar symLocTagVar
            | _ -> ()
          | _ -> ()
          *)
          | _ ->
            (* loc *)
            let symLoc = convertToCallSymLoc pubAddr someCPtr //SymLoc.Calldata (pubAddr, bv_loc)
            let symLocTagVar = TagVarSym symLoc
            let locTagVar = someCPtr |> KExpr.toVar |> fun v -> TagVarPublic (pubAddr, v)
            solveInfo.AddNewTagVar symLocTagVar
            solveInfo.AddNewTagVar locTagVar
            solveInfo.AddEquality currTagVar locTagVar symLocTagVar
            (* val *)
            let symLocSrc = convertToCallSymLoc pubAddr srcKExpr
            let symLocVal = SymLoc.CLoad (pubAddr, symLocSrc)
            let tagVarVal = TagVarSym symLocVal
            solveInfo.AddNewTagVar tagVarVal
            solveInfo.AddEquality currTagVar currTagVar symLocTagVar
        | _ -> ()
      | _ -> ()

    match dstKExpr with
    (*
      dst = mptr + 0x20
    *)
    | KBinOp (_, BinOpType.ADD,
              freeMemPtr,
              KNum (_, bv_0x20))
    | KBinOp (_, BinOpType.ADD,
              KNum (_, bv_0x20),
              freeMemPtr)
      when KExpr.isFreePtr freeMemPtr
        && BitVector.isEqualTo bv_0x20 0x20 ->
      fnFixMe ()
      match srcKExpr with
      | KBinOp (_, BinOpType.ADD,
                KNum (_, bv_0x20),
                calldataBaseLoc)
        when BitVector.isEqualTo bv_0x20 0x20
        ->
        (* TODO: "type이 같다"를 새로 추가? *)
        let calldataBaseLocSymLoc = convertToCallSymLoc pubAddr calldataBaseLoc
        let calldataBaseLocSymLocTagVar = TagVarSym calldataBaseLocSymLoc
        let freeMemPtrVar = freeMemPtr |> KExpr.toVar
        let freeMemPtrTagVar = TagVarPublic (pubAddr, freeMemPtrVar)
        match tryGetRootMemVarFromFreePtrTagVar solveInfo freeMemPtrTagVar with
        | None -> ()
        | Some rootFreeMemVar ->
          let rootFreeMemId = rootFreeMemVar.Identifier
          let freeMemPtrSymLoc = SymLoc.FreeMemPtr (pubAddr, rootFreeMemId)
          let freeMemPtrSymLocTagVar = TagVarSym freeMemPtrSymLoc
          solveInfo.AddEquality currTagVar freeMemPtrSymLocTagVar calldataBaseLocSymLocTagVar
      | _ -> ()
    (*
      ccopy(mptr + 0x40, 0x20 + cptr, *cptr)
      ccopy(_, 0x20 + cptr, *cptr)
      => cptr => bytes
      이때, cptr = base + *cptr' (e.g. 0x4 + cl(0x4))
    *)
    //| KBinOp (_, BinOpType.ADD, KBinOp (_, _, KFuncName "mload", args), KNum (_, bv_0x20))
    //  when BitVector.isEqualTo bv_0x20 0x20 ->
    | _ ->
      fnFixMe ()
      (*
      let dstTagVar = TagVarPublic (pubAddr, TagVar.toVar dstTagVar)
      match tryGetRootMemVarFromFreePtrTagVar solveInfo dstTagVar with
      | None -> ()
      | Some rootFreeMemVar ->
        ()
      *)
    | _ -> ()

let handleCalldataTags (solveInfo: SolveInfo) currTagVar tag =
  match tag with
  | TagCalldataLoad locTagVar ->
    handleTagCalldataLoad solveInfo currTagVar locTagVar
  | TagCalldataCopy2 (dstTagVar, srcTagVar, lenTagVar) ->
    handleTagCalldataCopy2 solveInfo currTagVar dstTagVar srcTagVar lenTagVar
  | TagAndOp (tagVar1, tagVar2) ->
    ()
  | _ -> ()
