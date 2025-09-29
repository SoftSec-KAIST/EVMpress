module Engine.SolveMemory

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
module private SolveMemoryHelper =

  let handleMemoryLoad (solveInfo: SolveInfo) currTagVar inMemTagVar addrTagVar =
    let addrKExpr = solveInfo.GetKExprFromTagVar addrTagVar
    let pubAddr = getPubAddrFromTagVar addrTagVar
    match addrKExpr with
    (*
      (0x20 * i) + (0x20 + mptr)
      =>
      T[]
    *)
    | KBinOp (_, BinOpType.ADD,
              KBinOp (_, BinOpType.MUL, KNum (_, bv_0x20), KVar _),
              KBinOp (_, BinOpType.ADD, KNum (_, bv_0x20_2), freeMemPtr))
      when KExpr.isFreePtr freeMemPtr
        && BitVector.isEqualTo bv_0x20 0x20 && BitVector.isEqualTo bv_0x20_2 0x20
      ->
      let freeMemPtrVar = freeMemPtr |> KExpr.toVar
      let freeMemPtrTagVar = TagVarPublic (pubAddr, freeMemPtrVar)
      match tryGetRootMemVarFromFreePtrTagVar solveInfo freeMemPtrTagVar with
      | None -> ()
      | Some rootFreeMemVar ->
        let rootFreeMemId = rootFreeMemVar.Identifier
        let freeMemPtrSymLoc = SymLoc.FreeMemPtr (pubAddr, rootFreeMemId)
        let freeMemPtrSymLocTagVar = TagVarSym freeMemPtrSymLoc
        (* t(mptr) <: T[] *)
        //let tyArray = TyArray (TyTop, 0)
        //solveInfo.AddTag currTagVar freeMemPtrSymLocTagVar <| TagHasType tyArray
        (* elem = x *)
        let elemSymLoc = SymLoc.MLoad (pubAddr, freeMemPtrSymLoc + SymLoc.Const bv_0x20)
        let elemSymLocTagVar = TagVarSym elemSymLoc
        solveInfo.AddEquality currTagVar currTagVar elemSymLocTagVar
        solveInfo.AddTag currTagVar freeMemPtrSymLocTagVar <| TagArray (elemSymLocTagVar, 0)
        // solveInfo.AddTag currTagVar freeMemPtrSymLocTagVar <| TagHasElemAs elemSymLocTagVar
    | _ -> ()

  let handleTagRawMemStore (solveInfo: SolveInfo) currTagVar inMemTagVar addrTagVar valueTagVar =
    let addrKExpr = solveInfo.GetKExprFromTagVar addrTagVar
    let pubAddr = getPubAddrFromTagVar addrTagVar
    match KExpr.tryExtractMPtr addrKExpr with
    | Some baseMPtr ->
      for termKExpr in KExpr.collectAddOperands addrKExpr do
        let termTagVar = TagVarPublic (pubAddr, termKExpr |> KExpr.toVar)
        solveInfo.AddTag currTagVar termTagVar TagUsedAsMemStoreOffset
      let properAddrTagVar = baseMPtr |> KExpr.toVar |> fun v -> TagVarPublic (pubAddr, v)
      match tryGetRootMemVarFromFreePtrTagVar solveInfo properAddrTagVar with
      | None -> ()
      | Some rootFreeMemVar ->
        let rootFreeMemId = rootFreeMemVar.Identifier
#if TYPEDEBUG
        let valueKExpr = solveInfo.GetKExprFromTagVar valueTagVar
        printfn "%A" valueKExpr
        if rootFreeMemVar.Identifier = 5 then
          ()
#endif
        let symLocLoc = SymLoc.FreeMemPtr (pubAddr, rootFreeMemId)
        let symLocVal = SymLoc.MLoad (pubAddr, symLocLoc) (*TODO: overwriting *)
        let symLocLocTagVar = TagVarSym symLocLoc
        let symLocValTagVar = TagVarSym symLocVal
        let valVar = TagVar.toVar valueTagVar
        let valTagVar = TagVarPublic (pubAddr, valVar)
        solveInfo.AddNewTagVar valTagVar
        solveInfo.AddEquality currTagVar symLocValTagVar valTagVar
        let rootFreeMemTagVar = TagVarPublic (pubAddr, rootFreeMemVar)
        //solveInfo.AddTag currTagVar symLocLocTagVar <| TagHasMemStore (rootFreeMemTagVar, addrTagVar, valueTagVar)
        solveInfo.AddTag currTagVar currTagVar <| TagHasFreeMemStore (rootFreeMemTagVar, addrTagVar, valueTagVar)
    | None -> ()(*TODO*)

    match addrKExpr with
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let kFreePtr = addrKExpr
      let tagVar = kFreePtr |> KExpr.toVar |> fun v -> TagVarPublic (pubAddr, v)
      match tryGetRootMemVarFromFreePtrTagVar solveInfo tagVar with
      | None -> ()
      | Some rootFreeMemVar ->
        let rootFreeMemId = rootFreeMemVar.Identifier
        let symLocFreePtr = SymLoc.FreeMemPtr (pubAddr, rootFreeMemId)
        let symLocLoc = symLocFreePtr
        let tagVarVal = TagVarSym (SymLoc.MLoad (pubAddr, symLocLoc))
        let tagVarLoc = TagVarSym symLocLoc
        let tagVarBaseLoc = TagVarSym symLocFreePtr
        let varAddr = KExpr.toVar addrKExpr
        let tagVarAddr = TagVarPublic (pubAddr, varAddr)
        solveInfo.AddNewTagVar tagVarVal
        solveInfo.AddNewTagVar tagVarBaseLoc
        solveInfo.AddNewTagVar tagVarLoc
        solveInfo.AddEquality currTagVar tagVarAddr tagVarLoc(*TODO: necessary?*)
        solveInfo.AddEquality currTagVar tagVarVal valueTagVar
        solveInfo.AddTag currTagVar tagVarBaseLoc <| TagHasPtr (tagVarLoc)
        solveInfo.AddTag currTagVar tagVarLoc <| TagPtrBelongsTo (tagVarBaseLoc)
    | KBinOp (_, BinOpType.ADD,
              ((KBinOp (_, BinOpType.APP, KFuncName "mload", args)) as kFreePtr),
              KNum (_, bv_const)) ->
      let tagVar = kFreePtr |> KExpr.toVar |> fun v -> TagVarPublic (pubAddr, v)
      match tryGetRootMemVarFromFreePtrTagVar solveInfo tagVar with
      | None -> ()
      | Some rootFreeMemVar ->
        let rootFreeMemId = rootFreeMemVar.Identifier
        let symLocFreePtr = SymLoc.FreeMemPtr (pubAddr, rootFreeMemId)
        let constOff = bv_const
        let symLocOff = SymLoc.Const (constOff)
        let symLocBaseLoc = symLocFreePtr
        let symLocLoc = symLocBaseLoc + symLocOff
        let tagVarVal = TagVarSym (SymLoc.MLoad (pubAddr, symLocLoc))
        let tagVarLoc = TagVarSym symLocLoc
        let tagVarBaseLoc = TagVarSym symLocBaseLoc
        let varAddr = KExpr.toVar addrKExpr
        let tagVarAddr = TagVarPublic (pubAddr, varAddr)
        solveInfo.AddNewTagVar tagVarVal
        solveInfo.AddNewTagVar tagVarBaseLoc
        solveInfo.AddNewTagVar tagVarLoc
        solveInfo.AddEquality currTagVar tagVarAddr tagVarLoc(*TODO: necessary?*)
        solveInfo.AddEquality currTagVar tagVarVal valueTagVar
        solveInfo.AddTag currTagVar tagVarBaseLoc <| TagHasPtr (tagVarLoc)
        solveInfo.AddTag currTagVar tagVarLoc <| TagPtrBelongsTo (tagVarBaseLoc)
    (* mptr + phi *)
    | KBinOp (_, BinOpType.ADD,
              ((KBinOp (_, BinOpType.APP, KFuncName "mload", args)) as kFreePtr),
              KVar _) ->
      ()
    (* phi *)
    | KVar _ ->
      ()
    | _ -> ()


    (* check if addr is an allocated free mem pointer *)
    (*
    match addrKExpr with
    (*
      mptr |-> v
      mptr + c |-> v
      => free mem store
    *)
    | KBinOp (_, BinOpType.ADD,
              KBinOp (_, BinOpType.APP, KFuncName "mload", args),
              _)
    | KBinOp (_, BinOpType.ADD,
              _,
              KBinOp (_, BinOpType.APP, KFuncName "mload", args))
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let [ kMem; kAddr ]= KExpr.toList args
      match kAddr with
      | KNum (_, bv_0x40) when BitVector.isEqualTo bv_0x40 0x40 ->
        (* FIXME: clean up T_T*)
        match addrKExpr with
        | KBinOp (_, BinOpType.ADD,
                    ((KBinOp (_, BinOpType.APP, KFuncName "mload", args)) as e),
                    offKExpr)
        | KBinOp (_, BinOpType.ADD,
                    offKExpr,
                    ((KBinOp (_, BinOpType.APP, KFuncName "mload", args)) as e))
          ->
          let offTagVar = TagVarPublic (pubAddr, offKExpr |> KExpr.toVar)
          solveInfo.AddNewTagVar offTagVar
          solveInfo.AddTag currTagVar offTagVar <| TagUsedAsMemStoreOffset
        | KBinOp (_, BinOpType.APP, KFuncName "mload", args) -> ()
        let properAddrKExpr =
          match addrKExpr with
          | KBinOp (_, BinOpType.ADD,
                      ((KBinOp (_, BinOpType.APP, KFuncName "mload", args)) as e),
                      _)
          | KBinOp (_, BinOpType.ADD,
                      _,
                      ((KBinOp (_, BinOpType.APP, KFuncName "mload", args)) as e))
            -> e
          | KBinOp (_, BinOpType.APP, KFuncName "mload", args) -> addrKExpr
        let properAddrTagVar = properAddrKExpr |> KExpr.toVar |> fun v -> TagVarPublic (pubAddr, v)
        match tryGetRootMemVarFromFreePtrTagVar solveInfo properAddrTagVar with
        | None -> ()
        | Some rootFreeMemVar ->
          let rootFreeMemId = rootFreeMemVar.Identifier
#if TYPEDEBUG
          let valueKExpr = solveInfo.GetKExprFromTagVar valueTagVar
          printfn "%A" valueKExpr
          if rootFreeMemVar.Identifier = 5 then
            ()
#endif
          let symLocLoc = SymLoc.FreeMemPtr (pubAddr, rootFreeMemId)
          let symLocVal = SymLoc.Memory (pubAddr, symLocLoc) (*TODO: overwriting *)
          let symLocLocTagVar = TagVarSym symLocLoc
          let symLocValTagVar = TagVarSym symLocVal
          let valVar = TagVar.toVar valueTagVar
          let valTagVar = TagVarPublic (pubAddr, valVar)
          solveInfo.AddNewTagVar valTagVar
          solveInfo.AddEquality currTagVar symLocValTagVar valTagVar
          let rootFreeMemTagVar = TagVarPublic (pubAddr, rootFreeMemVar)
          //solveInfo.AddTag currTagVar symLocLocTagVar <| TagHasMemStore (rootFreeMemTagVar, addrTagVar, valueTagVar)
          solveInfo.AddTag currTagVar currTagVar <| TagHasFreeMemStore (rootFreeMemTagVar, addrTagVar, valueTagVar)
      | _ -> ()
    | otherKExpr ->
      ()
    *)


let handleMemoryTags (solveInfo: SolveInfo) currTagVar tag =
  match tag with
  | TagRawMemStore (inMemTagVar, addrTagVar, valueTagVar) ->
    handleTagRawMemStore solveInfo currTagVar inMemTagVar addrTagVar valueTagVar
  | TagMemoryLoad (inMemTagVar, addrTagVar) ->
    handleMemoryLoad solveInfo currTagVar inMemTagVar addrTagVar
  | _ -> ()
