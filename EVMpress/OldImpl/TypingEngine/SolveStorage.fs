module Engine.SolveStorage

open B2R2.BinIR.SSA
open CPTypes
open TypeRecTypes
open Helper
open B2R2.BinIR
open B2R2
open SolveInfo

open EVMpress.Type

let rec private convertToSymLoc kExpr =
  match kExpr with
  | KNum (_, bv) -> SymLoc.Const bv
  | KBinOp (_, BinOpType.APP, KFuncName "sha3", args) ->
    let args = KExpr.toList args
    let args = List.map convertToSymLoc args
    SymLoc.Hash args
  | KBinOp (_, BinOpType.ADD, kExpr1, kExpr2) ->
    let kExpr1 = convertToSymLoc kExpr1
    let kExpr2 = convertToSymLoc kExpr2
    SymLoc.BinOp (BinOpType.ADD, kExpr1, kExpr2)
  | _ -> SymLoc.PlaceHolder

///TODO: 이미 쓰인 tag-rule 조합에 대해서는 다시 처리하지 않도록?
let handleStorageTags (solveInfo: SolveInfo) currTagVar tag =
  match tag with
  (*
    Keccak256
     : (1) mapping
       (2) array
  *)
  /// FIXME: 이거 처음에 작성한 rule인데.. 다른 rule들이 이거 subsume할 거 같은디?
  /// FIXME: 이런 룰들은 굳이 tag가 아니더라도 extract하고 나서 "한번 돌면서" 해도 될듯
  | TagHash (inMem, off, len) ->
    (* mapping 패턴: (key) | (slot) *)
    (* slot: 상수 or 변수 *)
    (* 먼저 0x0에서부터 쓰는지 확인 *)
    match solveInfo.GetKExprFromTagVar off with
    | KNum (_, offBv) ->
      let kLen = solveInfo.GetKExprFromTagVar len
      let lenBv =
        match kLen with
        | KNum (_, bv) -> Some bv
        (* FIXME: 0x0077c5372f41275f67f8106c4970bf6c773767c6
           why does this occur? *)
        | KBinOp (_, BinOpType.ADD, KNum (_, bv), KNum (_, bv2)) -> Some <| bv + bv2
        | _ -> None//failwith "TODO: invalid sha3 length"
      (* off = 0x0, len = 0x40 *)
      match lenBv with
      | None -> ()
      | Some lenBv ->
        if not <| offBv.IsZero then ()
        (* length: 0x20; might be array access *)
        elif BitVector.isEqualTo lenBv 0x20 then ()
        (* length: 0x40; might be mapping access *)
        elif BitVector.isEqualTo lenBv 0x40 then
          let firstValue = solveInfo.TryLoadTagVarFromMemoryAtConstant inMem 0x00
          let secondValue = solveInfo.TryLoadTagVarFromMemoryAtConstant inMem 0x20
          match firstValue, secondValue with
          | Some keyTagVar, Some slotTagVar ->
            (* slot이 상수인 경우 *)
            match KExpr.tryToBitVector <| solveInfo.GetKExprFromTagVar slotTagVar with
            | None ->
              (* FIXME: maybe phi*)
#if TYPEDEBUG
              printfn "FIXME: non-constant slot number"
#endif
              ()
            | Some slotBv ->
              (* 새로운 symbolic TagVar 추가 *)
              let symLoc = SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const slotBv ]
              let newTagVar = TagVarSym symLoc
              solveInfo.AddNewTagVar newTagVar
              (* 서로 연결 *)
              solveInfo.AddEquality currTagVar currTagVar newTagVar
          | _ -> ()
        (*TODO*)
        else ()
    | _ -> () (*TODO: variant start offset?*)
  (*
    SLOAD
     : SL(c) ->
       등등
  *)
  | TagStorageLoad locTagVar ->
    //// 여기서 바로 expand하면서 꼴을 본다
    //// 꼴이 적절하다면 symbolic variable 도입
    let kLoc = solveInfo.ExpandToKExpr locTagVar
#if TYPEDEBUG
    if true then //checkpointPrint tag then
      printfn "[+] SLoad: %A" kLoc
      (*
      let var = KExpr.toVar kLoc
      let cpState = fnGetCPStateFromTagVar locTagVar
      if fnIsPhiVar cpState var then
        let phiInfo = fnTryGetPhiLoopInfo cpState var
        match phiInfo with
        | None -> ()
        | Some phiInfo ->
          let initTagVar = mkTagVarPub (fnGetPubAddrFromTagVar locTagVar) phiInfo.Initial
          let initKExpr = initTagVar |> solveInfo.ExpandToKExpr
          let incTagVar = mkTagVarPub (fnGetPubAddrFromTagVar locTagVar) phiInfo.Delta
          let incKExpr = incTagVar |> solveInfo.ExpandToKExpr
          ()
      *)
#endif
    let cpState = solveInfo.GetCPStateFromTagVar locTagVar
    let funcInfo = solveInfo.GetFuncInfoFromTagVar locTagVar
    (* sload의 인자를 살펴봄 *)
    match kLoc with
    (*
      sload (sha(slot) + phi)
      global 배열 가능성
    *)
    | KBinOp
        (_, BinOpType.ADD,
         KBinOp
           (_, BinOpType.APP, KFuncName "sha3",
            KExprList (_, [ KNum (_, bv_slot) ])),
         (KVar var as phiKVar))
      when fnIsPhiVar funcInfo var
      ->
      let phiInfo = fnTryGetPhiLoopInfo funcInfo var
      match phiInfo with
      | None -> () (*FIXME:??*)
      | Some phiInfo ->
        let initTagVar = mkTagVarPub (getPubAddrFromTagVar locTagVar) phiInfo.Initial
        let incTagVar = mkTagVarPub (getPubAddrFromTagVar locTagVar) phiInfo.Delta
        let initKExpr = initTagVar |> solveInfo.ExpandToKExpr
        let incKExpr = incTagVar |> solveInfo.ExpandToKExpr
        match initKExpr, incKExpr with
        (*
          initial = sha3(slot)
          increment = 1
          this is either an array or bytes(string)
          =>
          sym loc 형태: storage (sha3(loc) + _)
        *)
        | KBinOp (_, BinOpType.APP, KFuncName "sha3", KExprList (_, [ KNum (_, bv_slot) ])),
          KNum (_, bv_inc) ->
          (* TODO: check bv_inc *)
          let symLocPos = SymLoc.Hash [ SymLoc.Const bv_slot ] + SymLoc.PlaceHolder
          let symLoc = SymLoc.SLoad symLocPos
          let newTagVar = TagVarSym symLoc
          solveInfo.AddNewTagVar newTagVar
          (* 루프에서 읽은 값이라는 사실 저장 *)
          solveInfo.AddTag currTagVar newTagVar <| TagReadValueInLoop
          (* value eq 일단 추가*)
          solveInfo.AddEquality currTagVar currTagVar newTagVar
        | _ -> ()
      ()
    (*
      loc 전체가 phi var
    *)
    | _ when fnIsPhiVar funcInfo (KExpr.toVar kLoc) ->
      let var = KExpr.toVar kLoc
      let phiInfo = fnTryGetPhiLoopInfo funcInfo var
      match phiInfo with
      | None -> () (*FIXME:??*)
      | Some phiInfo ->
        let initTagVar = mkTagVarPub (getPubAddrFromTagVar locTagVar) phiInfo.Initial
        let incTagVar = mkTagVarPub (getPubAddrFromTagVar locTagVar) phiInfo.Delta
        let initKExpr = initTagVar |> solveInfo.ExpandToKExpr
        let incKExpr = incTagVar |> solveInfo.ExpandToKExpr
        match initKExpr, incKExpr with
        (*
          initial = sha3(slot)
          increment = 1
          this is either an array or bytes(string)
          =>
          sym loc 형태: storage (sha3(loc) + _)
        *)
        | KBinOp (_, BinOpType.APP, KFuncName "sha3", KExprList (_, [ KNum (_,bv_slot) ])),
          KNum (_, bv_inc) ->
          (*TODO:check bv_inc*)
          let symLocPos =
            SymLoc.Hash [ SymLoc.Const bv_slot ]
            + SymLoc.PlaceHolder
          let symLoc = SymLoc.SLoad symLocPos
          let newTagVar = TagVarSym symLoc
          solveInfo.AddNewTagVar newTagVar
          (* 루프에서 읽은 값이라는 사실 저장 *)
          solveInfo.AddTag currTagVar newTagVar <| TagReadValueInLoop
          (* value eq 일단 추가*)
          solveInfo.AddEquality currTagVar currTagVar newTagVar
        | _ -> ()
        ()
    (* 그냥 uint256 -> 모든 변수가 최소한 이 타입을 갖는다 *)
    | KNum (_, bv_slot) ->
      let symLoc = SymLoc.SLoad (SymLoc.Const bv_slot)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      solveInfo.AddEquality currTagVar currTagVar newTagVar
    (*
      (idx / perSlot) + sha3(slot)
      : compaction 있는 array access
    *)
    | KBinOp
        (_, BinOpType.ADD,
         KBinOp
           (_, BinOpType.DIV, KNum (_, bv_idx), KNum (_, bv_perSlotFields)),
         KBinOp
           (_, BinOpType.APP, KFuncName "sha3",
            KExprList (_, [ KNum (_, bv_slot) ]))) ->
      (* uint128이면 -> slot당 2개씩 들어가므로 -> bv_perSlotFields = 2 *)
      (* 단일 타입의 배열일 수도 있고, struct의 배열일 수도 있다? struct의 경우에는 이렇게 안함 *)
      (* FIXME: 순서만 살짝 해쉬값이 먼저 오도록 바꿨다 -> side-effect는 없는가? *)
      (* FIXME: perSLot으로 나누는 부분도 생략함 -> side-effect?*)
      let symLoc =
        SymLoc.SLoad <| SymLoc.BinOp (BinOpType.ADD, SymLoc.Hash [ SymLoc.Const bv_slot ], SymLoc.PlaceHolder)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* link *)
      solveInfo.AddEquality currTagVar currTagVar newTagVar
    (*
      sha3(...) + idx
      dynamic array, or struct
    *)
    | KBinOp (_, BinOpType.ADD, KBinOp (_, BinOpType.APP, KFuncName "sha3", args), kIdx) ->
      let symLoc = convertToSymLoc kLoc
      match symLoc with
      // hash(key; loc) + idx
      // struct or array
      | SymLoc.BinOp (BinOpType.ADD, SymLoc.Hash [ key; loc ], SymLoc.Const _) ->
        let tagVarVal = TagVarSym <| SymLoc.SLoad symLoc
        solveInfo.AddNewTagVar tagVarVal
        solveInfo.AddEquality currTagVar currTagVar tagVarVal
        //printfn "."
      | _ -> ()
      (*
      let args = KExpr.toList args
      match args with
      (*
        global dynamic array
        이때, element가 primitive인지 struct인지 아직 모름
        만약 (1) idx가 연산없이 단순 i이고 (2) 하나의 sym 안에 여러 타입이 섞여있으면, struct로 간주
      *)
      | [ KNum (_, bvSlot) ] ->
        let symLoc = SymLoc.SLoad <| SymLoc.BinOp (BinOpType.ADD, SymLoc.Keccak256 [ SymLoc.Const bvSlot ], SymLoc.PlaceHolder)
        let newTagVar = TagVarSym symLoc
        solveInfo.AddNewTagVar newTagVar
        (* link *)
        solveInfo.AddEquality currTagVar currTagVar newTagVar
      | _ -> ()
      *)
    (* sha3는 keccak256의 resolved된 형태임 *)
    | KBinOp (_, BinOpType.APP, KFuncName "sha3", args) ->
      let args = KExpr.toList args
      match args with
      (*
        매핑 패턴 with 상수 slot
        sha3(key | slot)
      *)
      | [ kKey; kSlot ] when kSlot.IsKNum ->
        let slotBv = KExpr.toBitVector kSlot
        (* 새로운 symoblic variable 만들어서 *)
        let symLocLoc = SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const slotBv ]
        let symLocVal = SymLoc.SLoad symLocLoc
        //let tagVarLoc = TagVarSym symLocLoc
        //solveInfo.AddNewTagVar tagVarLoc (*TODO: 이거랑 실제 저 kLoc이랑 equality? *)
        (* key 관점 *)
        (* value 관점 *)
        let newTagVar = TagVarSym symLocVal
        solveInfo.AddNewTagVar newTagVar
        solveInfo.AddEquality currTagVar currTagVar newTagVar
        (* key 관점 *)
        let keyVar = KExpr.toVar kKey
        let pubAddr = getPubAddrFromTagVar locTagVar
        let keyTagVar = mkTagVarPub pubAddr keyVar
        solveInfo.AddTag currTagVar newTagVar <| TagHasKey keyTagVar
      (*
        mapping (k1 => mapping (k2 => v)) pattern
        sha3(key2 | sha3(key1 | slot))
      *)
      (* TODO: generalize for arbitrarily nested ones *)
      | [ kKey; KBinOp (Some firstSHA3Var, BinOpType.APP, KFuncName "sha3", args') ] ->
        let args' = KExpr.toList args'
        match args' with
        | [ kKey'; kSlot ] when kSlot.IsKNum ->
          let slotBv = KExpr.toBitVector kSlot
          (* hard-coded *)
          (* 1. first key *)
          let symLoc = SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const slotBv ]
          let newTagVar = TagVarSym symLoc
          solveInfo.AddNewTagVar newTagVar
          let firstSHA3TagVar = mkTagVarPub (getPubAddrFromTagVar locTagVar) firstSHA3Var
          solveInfo.AddEquality currTagVar firstSHA3TagVar newTagVar
          solveInfo.AddTag currTagVar newTagVar <| TagHasKey (mkTagVarPub (getPubAddrFromTagVar locTagVar) (KExpr.toVar kKey'))
          (* 2. second key *)
          let secondBaseSymLoc = SymLoc.Hash [ SymLoc.PlaceHolder; symLoc ]
          let secondBaseTagVar = TagVarSym secondBaseSymLoc
          solveInfo.AddTag currTagVar secondBaseTagVar <| TagHasKey (mkTagVarPub (getPubAddrFromTagVar locTagVar) (KExpr.toVar kKey))
          let symLoc = SymLoc.SLoad secondBaseSymLoc
          let newTagVar = TagVarSym symLoc
          solveInfo.AddNewTagVar newTagVar
          solveInfo.AddEquality currTagVar currTagVar newTagVar
        | _ -> ()
      (* TODO *)
      | _ -> ()
    | _ -> ()
  (*
    SSTORE
  *)
  | TagStorageStore (off, value) ->
    let kOff = solveInfo.ExpandToKExpr off
    let kValue = solveInfo.ExpandToKExpr value
#if TYPEDEBUG
    if true then // checkpointPrint tag then
      let offStr = KExpr.toString kOff
      let valueStr = KExpr.toString kValue
      printfn "[+] SStore: %A |-> %A" kOff kValue
      printfn "[+] SStore: %s |-> %s" offStr valueStr
#endif
    match kOff with
    | KNum (_, bvSlot) ->
      let symLoc = SymLoc.SLoad (SymLoc.Const bvSlot)
      let newTagVar = TagVarSym symLoc
      let valueVar = KExpr.toVar kValue
      let valueTagVar = mkTagVarPub (getPubAddrFromTagVar value) valueVar
      solveInfo.AddNewTagVar newTagVar
      solveInfo.AddEquality currTagVar newTagVar valueTagVar
    | KBinOp (_, BinOpType.APP, KFuncName "sha3", args) ->
      let args = KExpr.toList args
      match args with
      (* global mapping pattern *)
      | [ kKey; kSlot ] when kSlot.IsKNum ->
        (* add sym tag var *)
        let slotBv = KExpr.toBitVector kSlot
        let symLoc = SymLoc.SLoad <| SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const slotBv ]
        let newTagVar = TagVarSym symLoc
        solveInfo.AddNewTagVar newTagVar
        (* link value *)
        let srcValueVar = KExpr.toVar kValue
        let srcValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) srcValueVar
        solveInfo.AddEquality currTagVar newTagVar srcValueTagVar
        (* link key *)
        let keyVar = KExpr.toVar kKey
        let pubAddr = getPubAddrFromTagVar off
        let keyTagVar = mkTagVarPub pubAddr keyVar
        solveInfo.AddTag currTagVar newTagVar <| TagHasKey keyTagVar
      | _ -> ()
    (*
      dyn array using pre-computed sha3
    *)
    | KBinOp
       (_, BinOpType.ADD,
        KNum
          (_, bv_sha3),
        KBinOp
          (_, BinOpType.APP, KFuncName "sload",
           KExprList (_, [ KNum (_, bv_slot) ])))
      when BitVector.calculateKeccak256 bv_slot = bv_sha3 ->
      (*FIXME: 패턴 호환성위해 임의로 바꿈*)
      (* shape*)
      let symLocBase = SymLoc.BinOp (BinOpType.ADD, SymLoc.Hash [ SymLoc.Const bv_slot ], SymLoc.PlaceHolder)
      let newTagVar = TagVarSym symLocBase
      solveInfo.AddNewTagVar newTagVar
      let ty = TyArray (TyTop, 0) (*FIXME: length: 0 -> constant*)
      solveInfo.AddTag currTagVar newTagVar <| TagHasType ty
      (* elem*)
      let elemTagVar = TagVarSym (SymLoc.SLoad symLocBase)
      solveInfo.AddNewTagVar elemTagVar
      match kValue with
      (*
        elem: string
      *)
      |  KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.ADD, lengthExpr1, lengthExpr2),
         KBinOp
           (_, BinOpType.AND,
            KBinOp
              (_, BinOpType.APP, KFuncName "msg.data",
               KExprList
                 (_,
                  [KBinOp
                    (_, BinOpType.ADD,
                     KNum (_, bv_0x20),
                     KBinOp
                       (_, BinOpType.ADD,
                        KNum (_, bv_0x4),
                        KBinOp
                          (_, _, KFuncName "msg.data",
                           KExprList
                             (_, [ bv_0x4_2 ]))    ))])    ),
            KUnOp
              (_, UnOpType.NOT,
               KNum (_, bv_0xff))))
        when lengthExpr1 = lengthExpr2 ->
        solveInfo.AddTag currTagVar elemTagVar <| TagHasType TyBytes
      | _ ->
        ()
      let symLoc = SymLoc.SLoad symLocBase
      let newTagVar = TagVarSym symLoc
      let valueVar = KExpr.toVar kValue
      let valueTagVar = mkTagVarPub (getPubAddrFromTagVar value) valueVar
      solveInfo.AddNewTagVar newTagVar
      solveInfo.AddEquality currTagVar valueTagVar newTagVar
    (*
      likely mapping-struct store pattern
      someMap[key].field = value
    *)
    | KBinOp
        (_, BinOpType.ADD,
         KBinOp
           (_, BinOpType.APP, KFuncName "sha3",
            KExprList
              (_,
               [ keyKExpr;
                 KNum (_, bv_slot) ])),
         KNum (_, bv_fieldOffset)) ->
#if TYPEDEBUG
      printfn "[+] mapping-struct field: %A %A" bv_slot bv_fieldOffset
#endif
      let symLoc = SymLoc.SLoad (SymLoc.BinOp (BinOpType.ADD, SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ], SymLoc.Const bv_fieldOffset))
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      let valueVar = KExpr.toVar kValue
      let valueTagVar = mkTagVarPub (getPubAddrFromTagVar value) valueVar
      solveInfo.AddEquality currTagVar valueTagVar newTagVar
      (*TODO: key? *)
      (*
      let keyVar = KExpr.toVar keyKExpr
      let keyTagVar = mkTagVarPub (fnGetPubAddrFromTagVar off) keyVar
      solveInfo.AddTag currTagVar <| TagHasKey keyTagVar
      *)
    | _ -> ()
    (*
      value pattern
    *)
    match kValue with
    (*

      mapping(k => struct{})) store 패턴
      compaction 된 경우
    *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.AND,
            KUnOp
              (_, UnOpType.NOT,
               KBinOp
                 (_, BinOpType.MUL,
                  KNum
                    (_,
                     bv_0xffffffffffffffffffffffffffffffffffffffff),
                  KBinOp
                    (_, BinOpType.APP, KFuncName "exp",
                     KExprList
                       (None, [ KNum (_, bv_0x100);
                                KNum (_, bv_0x0) ])))),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList
                 (None,
                  [ KBinOp
                      (_, BinOpType.ADD,
                       KNum (_, bv_structFieldOff),
                       KBinOp
                         (_, BinOpType.APP, KFuncName "sha3",
                          KExprList
                            (None, [ someFirstKey;
                                     KNum (_, bv_slot) ]))) ]))),
         KBinOp
           (_, BinOpType.MUL,
            someValue,
            KBinOp
              (_, _, KFuncName "exp",
               KExprList
                 (_, [ KNum (_, bv_0x100_2); KNum (_, bv_0x0_2) ]  )))) ->
      (* sload(sha3(_, slot) + fieldOff) & 0xfff...ff *)
      let symLocBase =
        SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ]
      let symLocBaseTagVar = TagVarSym symLocBase
      solveInfo.AddNewTagVar symLocBaseTagVar
      let firstKeyVar = KExpr.toVar someFirstKey
      let firstKeyTagVar = mkTagVarPub (getPubAddrFromTagVar off) firstKeyVar
      let tagHasKey = TagHasKey firstKeyTagVar
      solveInfo.AddTag currTagVar symLocBaseTagVar tagHasKey
      let symLoc =
        SymLoc.BinOp (
          BinOpType.AND,
          SymLoc.SLoad <| symLocBase + SymLoc.Const bv_structFieldOff,
          SymLoc.Const <| BitVector.Exp (bv_0x100_2, bv_0x0_2)
        )
      let symLocTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar symLocTagVar
      let valueVar = KExpr.toVar someValue
      let valueTagVar = mkTagVarPub (getPubAddrFromTagVar value) valueVar
      solveInfo.AddEquality currTagVar symLocTagVar valueTagVar
    (*
      or (
        (1 << 0xa8) * someValue,
        sload(n) & (not (ff << 0xa8))
      )
      =>
      compaction
    *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.MUL,
            KBinOp
              (_, BinOpType.SHL, KNum (_, bv_0x1),
               KNum (_, bv_0xa8)),
            someValue),
         KBinOp
           (_, BinOpType.AND,
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (_, [ KNum (_, bv_slot) ]))    ,
            KUnOp
              (_, UnOpType.NOT,
               KBinOp
                 (_, BinOpType.SHL,
                  KNum (_, bv_0xff),
                  KNum (_, bv_0xa8_1)))))
      when bv_0x1.IsOne
        && BitVector.isBitmask bv_0xff
        && bv_0xa8 = bv_0xa8_1
      ->
      let absoluteMask = bv_0xff * BitVector.Shl(bv_0x1, bv_0xa8)
      let symLoc =
        SymLoc.BinOp (
          BinOpType.AND,
          SymLoc.SLoad (SymLoc.Const bv_slot),
          SymLoc.Const absoluteMask
        )
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* value *)
      let someValueVar = KExpr.toVar someValue
      let someValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) someValueVar
      solveInfo.AddEquality currTagVar newTagVar someValueTagVar
    (*
      최적화 이빠이 된 경우
      or (
        and (0xffff.....000, sload(c)),
        and (0x0000.....fff, some_value)
      )
    *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.AND,
            KNum (_, bv_otherBitmask),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (_, [ KNum (_, bv_slot) ]))),
         KBinOp
           (_, BinOpType.AND,
            KNum (_, bv_lenBitmask),
            someValue))
      when bv_lenBitmask |> BitVector.isBitmask
        && BitVector.Not bv_otherBitmask = bv_lenBitmask
      ->
      let symLoc = SymLoc.SLoad (SymLoc.Const bv_slot)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* value *)
      let someValueVar = KExpr.toVar someValue
      let someValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) someValueVar
      solveInfo.AddEquality currTagVar newTagVar someValueTagVar
    (*
      or(
        and (
          not (0xff * (0x100^0)),
          sload(sha3(k, slot)
        ),
        mul (
          v,
          exp(0x100, 0x0)
        )
      )
      =>
      mapping(k => v) + compaction
    *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.AND,
            KUnOp
              (_, UnOpType.NOT,
               KBinOp
                 (_, BinOpType.MUL,
                  KNum (_, bv_0xff),
                  KBinOp
                    (_, BinOpType.APP, KFuncName "exp",
                     KExprList
                       (_, [ KNum (_, bv_0x100); KNum (_, bv_0x0) ]))   )),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList
                 (_,
                  [ KBinOp
                      (_, BinOpType.APP, KFuncName "sha3",
                       KExprList
                         (_,
                          [ someKey; KNum (_, bv_slot) ]))
                  ]))    ),
         KBinOp
           (_, BinOpType.MUL,
            someValue,
            KBinOp
              (_, BinOpType.APP, KFuncName "exp",
               KExprList
                 (_, [ KNum (_, bv_0x100_1);
                       KNum (_, bv_0x0_1) ]))   )) ->
      let absoluteMask = bv_0xff * BitVector.Exp (bv_0x100, bv_0x0)
      let symLoc =
        SymLoc.BinOp (BinOpType.AND,
          SymLoc.SLoad (SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ]),
          SymLoc.Const absoluteMask
        )
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* key *)
      (*skip*)
      (* value *)
      let someValueVar = KExpr.toVar someValue
      let someValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) someValueVar
      solveInfo.AddEquality currTagVar newTagVar someValueTagVar
    (*
      global w/ compaction
    *)
    | KBinOp
        (_, OR,
         KBinOp
           (_, AND,
            KUnOp
              (_, NOT,
               KBinOp
                 (_, MUL,
                  KNum (_, bv_0xff),
                  KBinOp
                    (_, APP, KFuncName "exp",
                     KExprList
                       (_, [ KNum (_, bv_0x100); KNum (_, bv_0x14) ])  ))),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (None, [ KNum (_, bv_slot) ]))),
         KBinOp
           (_, BinOpType.MUL,
            someValue,
            KBinOp
              (_, BinOpType.APP, KFuncName "exp",
               KExprList (_, [ KNum (_, bv_0x100_2); KNum (_, bv_0x14_2) ])) ))
      when BitVector.isBitmask bv_0xff
        && BitVector.isEqualTo bv_0x100 0x100
        && BitVector.isEqualTo bv_0x100_2 0x100
        && bv_0x14 = bv_0x14_2 (* determines offset*) ->
      let absoluteMask = bv_0xff * BitVector.Exp (bv_0x100, bv_0x14)
      let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const bv_slot), SymLoc.Const absoluteMask)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* value *)
      let someValueVar = KExpr.toVar someValue
      let someValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) someValueVar
      solveInfo.AddEquality currTagVar newTagVar someValueTagVar
    (*
      bool
    *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.MUL,
            KNum (_, bv_0x10000), KCast
              (_, CastKind.ZeroExt,
               KRelOp
                 (_, RelOpType.EQ,
                  KCast
                    (_, CastKind.ZeroExt,
                     KRelOp
                       (_, RelOpType.EQ,
                        (* 0과 비교 *)
                        some_value, KNum (_, bv_0x0))), KNum (_, bv_0x0_2)))),
         KBinOp
           (_, BinOpType.AND,
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (_, [ KNum (_, bv_slot) ])),
            KUnOp
              (_, UnOpType.NOT,
               KNum (_, bv_0xff0000))))
        when bv_0x0.IsZero && bv_0x0_2.IsZero ->
      (*TODO: check bv_0x10000*)
      let symLoc = SymLoc.BinOp (BinOpType.AND,
                                 SymLoc.SLoad (SymLoc.Const bv_slot),
                                 SymLoc.Const bv_0xff0000)
      (* sload(slot) & 0xff0000 *)
      let newTagVar = TagVarSym symLoc
      let someValueVar = KExpr.toVar some_value
      let someValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) someValueVar
      solveInfo.AddNewTagVar newTagVar
      solveInfo.AddEquality currTagVar newTagVar someValueTagVar
      solveInfo.AddTag currTagVar newTagVar <| TagHasType TyBool
    (* global value w/ compaction *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.MUL,
            KNum (_, bv_0x100000000),
            KBinOp
              (_, BinOpType.AND,
               srcValue,
               KNum (_, bv_0xffffffff))),
         KBinOp
           (_, BinOpType.AND,
            KUnOp
              (_, UnOpType.NOT,
               KNum (_, bv_0xffffffff00000000)),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (None, [ KNum (_, bv_slot) ]))))
        when BitVector.isBitmask bv_0xffffffff
          && bv_0xffffffff * bv_0x100000000 = bv_0xffffffff00000000 ->
      // bv_0x100000000 (* offset hint *)
      // bv_0xffffffff (* mask hint *)
      (* symoblic 변수 도입 *)
      (* stor (bv_slot) & bv_ 0xfff.... *)
      (* 헷갈리니 잘 볼 것*)
      let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const bv_slot), SymLoc.Const bv_0xffffffff00000000)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* src 값과, 심볼릭 변수의 동등성 추가 *)
      let srcValueVar = KExpr.toVar srcValue
      let srcValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) srcValueVar
      solveInfo.AddEquality currTagVar newTagVar srcValueTagVar
    (*
      (not(bitmsk) & sload(sha3(k, slot))) or someValue
      mapping(k => v) + compaction
    *)
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.AND,
            KUnOp
              (_, UnOpType.NOT,
               KNum (_, bv_0xff)),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList
                 (_,
                  [ KBinOp
                      (_, BinOpType.APP, KFuncName "sha3",
                       KExprList
                         (_,
                          [ someKeyKExpr;
                            KNum (_, bv_slot) ] ))
                  ]))         ),
         someValueKExpr)
      when BitVector.isBitmask bv_0xff ->
      (* register sym loc*)
      let symLoc =
        SymLoc.BinOp (BinOpType.AND,
          SymLoc.SLoad (SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ]),
          SymLoc.Const bv_0xff)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      (* key *)
      let keyVar = KExpr.toVar someKeyKExpr
      let keyTagVar = mkTagVarPub (getPubAddrFromTagVar value) keyVar
      (*TODO: how about key?*)
      (* value *)
      let valueVar = KExpr.toVar someValueKExpr
      let valueTagVar = mkTagVarPub (getPubAddrFromTagVar value) valueVar
      solveInfo.AddEquality currTagVar newTagVar valueTagVar
    | KBinOp
        (_, BinOpType.OR,
         KBinOp
           (_, BinOpType.AND,
            KUnOp
              (_, UnOpType.NOT,
               KBinOp
                 (_, BinOpType.SUB,
                  KBinOp
                    (_, BinOpType.SHL,
                     KNum (_, bv_0x1),
                     KNum (_, bv_0xa0)),
                  KNum (_, bv_0x1_2))),
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList
                 (_,
                  [ KBinOp
                      (_, BinOpType.ADD,
                       KNum
                         (_,
                          bv_0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563),
                       KBinOp
                         (_, _, KFuncName "sload",
                          KExprList
                            (_, [ KNum (_, bv_slot) ]))     )
                  ]))     ),
         someValue)
      when bv_0x1.IsOne
        && bv_0x1_2.IsOne
        && BitVector.isMultipleOfUInt64 bv_0xa0 8UL
        && BitVector.calculateKeccak256 bv_slot = bv_0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563
      ->
      (*compaction때문에 힘들구먼*)
      (*ptr*)
      let symLocPtr = SymLoc.BinOp (BinOpType.ADD, SymLoc.Hash [ SymLoc.Const bv_slot ], SymLoc.PlaceHolder)
      let newTagVar = TagVarSym symLocPtr
      solveInfo.AddNewTagVar newTagVar
      solveInfo.AddTag currTagVar newTagVar <| TagHasType (TyArray (TyTop, 0)) (*크기: unknown,그래서 0으로 set*)
      (*element*)
      let absoluteMask = BitVector.Shl(bv_0x1, bv_0xa0) - bv_0x1_2
      let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad symLocPtr, SymLoc.Const absoluteMask)
      let newTagVar = TagVarSym symLoc
      solveInfo.AddNewTagVar newTagVar
      let someValueVar = KExpr.toVar someValue
      let someValueTagVar = mkTagVarPub (getPubAddrFromTagVar value) someValueVar
      solveInfo.AddEquality currTagVar newTagVar someValueTagVar
    | _ -> ()
  (*
    HasKey
  *)
  (* mapping에서, key 값 간의 동등성 전파 -- 어차피 value끼리는 이미 잘 전파됨
     t1 = m and m = t2 => t1.key = t2.key *)
  (* 만약, 어떤 mapping 형태의 sym var와 관계가 있다면 *)
  (* TODO: 방향성 고려? *)
  | TagHasKey keyTagVar ->
    (* 다른 애들과의 동등성 추가 *)
    (* TODO: maybe dangerous*)
    for tag in solveInfo.GetTagsFromTagVar currTagVar do
      match tag with
      | TagHasKey keyTagVar' when keyTagVar <> keyTagVar' ->
        solveInfo.AddEquality currTagVar keyTagVar keyTagVar'
      | _ -> ()
  (*
    AND 연산
    memory aliasing 고려해서 여기서 처리
    (SymVar & 0xffff...)
    compaction
  *)
  | TagAndOp (tagVar1, tagVar2) ->
    let fn tagVar1 tagVar2=
      let kExpr1 = solveInfo.ExpandToKExpr tagVar1
      let kExpr2 = solveInfo.ExpandToKExpr tagVar2

      let fnTryGetBitmaskBitsFromKExpr kExpr =
        match kExpr with
        | KNum (_, bv) when BitVector.isBitmask bv ->
          BitVector.getBitmaskBits bv
          |> Some
        (* 1 <<a0 -1*)
        | KBinOp (_, BinOpType.SUB, KBinOp (_, BinOpType.SHL, KNum (_, bv_0x1), KNum (_, bv_a0)), KNum (_, bv_1))
          when bv_1.IsOne
            && bv_0x1.IsOne
            && BitVector.isMultipleOfUInt64 bv_a0 8UL ->
          BitVector.Shl(bv_0x1, bv_a0) - bv_1
          |> BitVector.getBitmaskBits
          |> Some
        | _ -> None

      (*
        패턴 보기
      *)
      match kExpr1, kExpr2 with
      (*
        global compaction
        (sload(n) / (1 << a0)) & 0xff
        =>
        slot,off,mask(len)까지 모두 알려주는 케이스
      *)
      | KNum (_, bv_0xff),
         KBinOp
           (_, BinOpType.DIV,
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (_, [ KNum (_, bv_slot) ])),
            KBinOp
              (_, BinOpType.SHL, KNum (_, bv_0x1),
               KNum (_, bv_0xa0)))
       | KBinOp
           (_, BinOpType.DIV,
            KBinOp
              (_, BinOpType.APP, KFuncName "sload",
               KExprList (_, [ KNum (_, bv_slot) ])),
            KBinOp
              (_, BinOpType.SHL, KNum (_, bv_0x1),
               KNum (_, bv_0xa0))),
         KNum (_, bv_0xff)
        (*
        when BitVector.isEqualTo bv_0xff 0xff
          && BitVector.isEqualTo bv_0x1 1
          && BitVector.isEqualTo bv_0xa0 0xa0 ->
        *)
        when BitVector.isBitmask bv_0xff
          && bv_0x1.IsOne
          && BitVector.isMultipleOfUInt64 bv_0xa0 8UL ->
        //let absoluteBitmask = bv_0xff * (bv_0x1.Shl bv_0xa0)
        (*FIXME: 일부러 length는 mask에서 생략!! length를 모를때와의 호환성을 위해!*)
        (*일부러 bits=1로 만든다*)
        (*대신, 바로 아래서 크기에 대한 constraint 생성 *)
        (*TODO:이렇게할거면, AND라고 표현하지 말고, 뭐 다른 표현으로? e.g. StorageWithOffset=... 나중에 ㅠ*)
        let absoluteBitmask = BitVector.Shl(bv_0x1, bv_0xa0)
        let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const bv_slot), SymLoc.Const absoluteBitmask)
        let newTagVar = TagVarSym symLoc
        solveInfo.AddNewTagVar newTagVar
        solveInfo.AddEquality currTagVar currTagVar newTagVar
        (* value length constraint *)
        solveInfo.AddTag currTagVar newTagVar <| TagHasType (TyUInt <| BitVector.getBitmaskBits bv_0xff)
      (*
        (sload(...) / 0x1000....) & 0xff
        uint8 or bool
      *)
      | KBinOp
          (_, BinOpType.DIV,
          KBinOp
            (_, BinOpType.APP, KFuncName "sload",
             KExprList
               (None, [ KNum (_, bv_slot) ])),
          KNum
            (_,
             bv_0x10000000000000000000000000000000000000000)),
        KNum (_, bv_0xff)
        when BitVector.isEqualTo bv_0xff 0xff
          && (bv_0x10000000000000000000000000000000000000000 - 1UL) |> BitVector.isBitmask ->
        let absoluteBitmask = bv_0x10000000000000000000000000000000000000000 * bv_0xff
        let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const bv_slot), SymLoc.Const absoluteBitmask)
        let newTagVar = TagVarSym symLoc
        solveInfo.AddNewTagVar newTagVar
        solveInfo.AddEquality currTagVar currTagVar newTagVar
      (*
        (sload(...) / 0x1000....) & 0xff
        위엣거 일반화
        TODO: 이런 식으로 다 일반화하면 됨 ofKExpr써서 나중에 공개하기전에 ㄱㄱ
      *)
      | KBinOp
          (_, BinOpType.DIV,
          KBinOp
            (_, BinOpType.APP, KFuncName "sload",
             KExprList
               (None, [ someLocKExpr ])),
          someDivisor),
        KNum (_, bv_0xff)
        when BitVector.isBitmask bv_0xff
          && KExpr.constantFolding someDivisor
             |> (fun e -> match e with | KNum (_, bv) -> bv.IsOne || bv - 1UL |> BitVector.isBitmask | _ -> false)
        ->
        match tagVar1 with
        | TagVarPublic (pubAddr, _)
          when solveInfo.ConvertToStorageSymLoc pubAddr someLocKExpr <> SymLoc.PlaceHolder
          ->
          (* 여기서, someLocKExpr으로부터 sym loc을 파싱해와야함 *)
          let innerSymLoc = solveInfo.ConvertToStorageSymLoc pubAddr someLocKExpr
          let posBitmask = KExpr.constantFolding someDivisor |> KExpr.toBitVector
          let symLoc = SymLoc.SLoad innerSymLoc &&& SymLoc.Const posBitmask
          let newTagVar = TagVarSym symLoc
          solveInfo.AddNewTagVar newTagVar
          solveInfo.AddTag currTagVar newTagVar <| TagHasType (TyUInt <| BitVector.getBitmaskBits bv_0xff)
          solveInfo.AddEquality currTagVar currTagVar newTagVar
        | _ -> ()
      (*
        (sload(sha3(_, slot)) -----------) & 0xffff...
        => offset=0,len=...
      *)
      (*
        (sload(sha3(_, slot)) / 0x1000...) & ((1 << 0xa0) - 1)
        => offset=...,len=...
      *)
      (*
        (sload(sha3(_, slot)) / (1 << c0)) & 0xff
        => offset=...,len=...
      *)
      | KBinOp (_, BinOpType.APP, KFuncName "sload",
                KExprList (_, [ KBinOp (_, BinOpType.APP, KFuncName "sha3", args) ])),
        lengthBitmask
        ->
        // offset = 0
        //let absoluteBitmask = BitVector.Zero 256<rt>
        let args = KExpr.toList args
        match args with
        | [ _; KNum (_, bv_slot)] ->
          let symLoc = SymLoc.SLoad (SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ])
          let newTagVar = TagVarSym symLoc
          solveInfo.AddNewTagVar newTagVar
          solveInfo.AddEquality currTagVar currTagVar newTagVar
          let bits = fnTryGetBitmaskBitsFromKExpr lengthBitmask
          match bits with
          | Some bits ->
            solveInfo.AddTag currTagVar newTagVar <| TagHasType (TyUInt bits)
          | _ -> ()
        | _ -> ()
      | KBinOp (
          _,
          BinOpType.DIV,
          KBinOp (_, BinOpType.APP, KFuncName "sload",
                  KExprList (_, [ KBinOp (_, BinOpType.APP, KFuncName "sha3", args) ])),
          divisor
        ),
        lengthBitmask
        ->
        let args = KExpr.toList args
        match args with
        | [ _; KNum (_, bv_slot)] ->
          // divisor parsing
          match divisor with
          | KNum (_, bv_divisor) ->
            let absoluteBitmask = bv_divisor
            let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ]), SymLoc.Const absoluteBitmask)
            let newTagVar = TagVarSym symLoc
            solveInfo.AddNewTagVar newTagVar
            solveInfo.AddEquality currTagVar currTagVar newTagVar
            let bits = fnTryGetBitmaskBitsFromKExpr lengthBitmask
            match bits with
            | Some bits ->
              solveInfo.AddTag currTagVar newTagVar <| TagHasType (TyUInt bits)
            | _ -> ()
          | KBinOp (_, BinOpType.SHL, KNum (_, bv_1), KNum (_, bv_c0)) ->
            let absoluteBitmask = BitVector.Shl(bv_1, bv_c0)
            let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Hash [ SymLoc.PlaceHolder; SymLoc.Const bv_slot ]), SymLoc.Const absoluteBitmask)
            let newTagVar = TagVarSym symLoc
            solveInfo.AddNewTagVar newTagVar
            solveInfo.AddEquality currTagVar currTagVar newTagVar
            let bits = fnTryGetBitmaskBitsFromKExpr lengthBitmask
            match bits with
            | Some bits ->
              solveInfo.AddTag currTagVar newTagVar <| TagHasType (TyUInt bits)
            | _ -> ()
          | _ -> ()
        | _ -> ()
      (*
        msg.data(off) & 0xffffffff00000.......00
        bytesN 패턴
      *)
      | KBinOp (_, BinOpType.APP, KFuncName "msg.data", args),
        KNum (_, bv)
        when BitVector.isBytesNBitmask bv ->
        (*TODO:introduce symvar*)
        //let pubAddr = fnGetPubAddrFromTagVar currTagVar
        //let symLoc = SymLoc.BinOp (BinOpType.AND, SymLoc.Calldata (pubAddr, SymLoc.Const bv))
        let n = BitVector.getBytesNBitmaskBytes bv
        let tagHasType = TagHasType (TyBytesN n)
        solveInfo.AddTag currTagVar currTagVar tagHasType |> ignore
      | _ -> ()

      (* sybolic 변수 갖는지 체크 *)
      let tryGetSymLoc tagVar =
        match solveInfo.PerVarTags.TryGetValue tagVar with
        | false, _ -> None
        | true, tags ->
          tags |> Seq.tryPick (function
            | TagEqualsTo ( TagVarSym symLoc )-> Some symLoc
            | _ -> None)
      let symLoc1 = tryGetSymLoc tagVar1
      match symLoc1, kExpr2 with
      (*
        sload(...) & 0xffff...
      *)
      | Some (SymLoc.SLoad _ as symLoc1),
        KNum (_, bv_bitmask)
          when BitVector.isBitmask bv_bitmask ->
        let newSymLoc = SymLoc.BinOp (BinOpType.AND, symLoc1, SymLoc.Const bv_bitmask)
        let newTagVar = TagVarSym newSymLoc
        solveInfo.AddNewTagVar newTagVar
        solveInfo.AddEquality currTagVar currTagVar newTagVar
      | _ -> ()
    fn tagVar1 tagVar2
    fn tagVar2 tagVar1
  (*
  (*
    storage 변수 도입
    ex) (sload(0) & (1 << a0) - 1) => (slot=0, off=0)
  *)
  | TagAndOp (tag1, tag2) ->

    solveInfo.AddTag currTagVar tag1 tag
    solveInfo.AddTag currTagVar tag2 tag
  *)
  | _ -> ()

