module TypeRecTypes

open B2R2
open B2R2.BinIR
open B2R2.BinIR.SSA
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.DataFlow
open System.Collections.Generic
open System.Text.Json
open System.Text.Json.Serialization
open Prelude
open Microsoft.FSharp.Core.LanguagePrimitives

type Type =
  | TyTop
  | TyUInt of bits: int
  | TyInt of bits: int
  | TyAddr
  | TyArray of elemType: Type * length: int
  | TyBool
  | TyBytes
  | TyBytesN of n: int
  | TyMapping of keyType: Type * valueType: Type
  /// offset to the field
  | TyStruct of Map<int, Type>
  | TyBot

with
  override this.ToString () =
    match this with
    | TyTop -> "uint256"
    | TyUInt bits -> sprintf "uint%d" bits
    | TyAddr -> "address"
    | TyArray (elemType, length) ->
      let elemTy = elemType.ToString ()
      let len = if length = 0 then "" else length.ToString ()
      $"{elemTy}[{len}]"
    | TyBool -> "bool"
    | TyBytes -> "bytes"
    | TyMapping (keyType, valueType) ->
      let keyTy = keyType.ToString ()
      let valueTy = valueType.ToString ()
      $"mapping ({keyTy} => {valueTy})"
    | TyStruct fields ->
      let s =
        fields
        (*FIXME: 오프셋 표현해서 출력하는게 더 나을지도*)
        // |> Seq.map (fun (KeyValue (k, v)) -> $"{k.ToString ()}: {v.ToString ()}")
        |> Seq.sortBy (fun (KeyValue (k, v)) -> k)
        |> Seq.map (fun (KeyValue (k, v)) -> v.ToString ())
        |> String.concat ", "
      $"({s})"
    | TyBytesN n -> $"bytes{n}"
    | TyInt b -> $"int{b}"
    | TyBot -> "nil"

/// Symbolic locations
/// ex) sha3(x | slot) (이때, x는 placeholder)
//[<RequireQualifiedAccess; CustomEquality; NoComparison>]
[<RequireQualifiedAccess>]
type SymLoc =
  /// 상수.
  | Const of BitVector
  /// 아무런 값이 올 수 있는 placeholder.
  | PlaceHolder
  /// Binary 연산.
  | BinOp of BinOpType * SymLoc * SymLoc
  /// Hash 연산.
  | Hash of args: SymLoc list
  /// Storage 영역 읽기
  | SLoad of slot: SymLoc
  /// Memory 영역 읽기
  | MLoad of pubAddr: Addr * addr: SymLoc
  /// Calldata 영역 읽기
  | CLoad of pubAddr: Addr * addr: SymLoc
  /// Storage 상수
  //| Storage of pubAddr: Addr * loc: BitVector
  /// Calldata 상수
  //| Calldata of pubAddr: Addr * loc: BitVector
  /// Free memory를 가리키는 포인터. id는 root memory의 id로, 같은 region이라면
  /// 같은 id를 가지므로 aliasing을 표현할 수 있다.
  | FreeMemPtr of pubAddr: Addr * id: int
with
  static member (+) (v: SymLoc, a) =
    BinOp (BinOpType.ADD, v, a)
  static member (-) (v: SymLoc, a) =
    BinOp (BinOpType.SUB, v, a)
  static member (&&&) (v: SymLoc, a) =
    BinOp (BinOpType.AND, v, a)
  static member (/) (v: SymLoc, a) =
    BinOp (BinOpType.DIV, v, a)
  static member (*) (v: SymLoc, a) =
    BinOp (BinOpType.MUL, v, a)
  static member (!) (v: SymLoc) =
    SLoad v
  static member OfInt (n: int) =
    Const (BitVector(n, 256<rt>))
(*
  override __.Equals rhs =
    match rhs with
    | :? E as rhs ->
      match __, rhs with
      | Num (n1), Num (n2) -> n1 = n2
      | Var (t1, r1, _, _), Var (t2, r2, _, _) -> t1 = t2 && r1 = r2
      | Nil, Nil -> true
      | PCVar (t1, _), PCVar (t2, _) -> t1 = t2
      | TempVar (t1, n1), TempVar (t2, n2) -> t1 = t2 && n1 = n2
      | UnOp (t1, e1, _), UnOp (t2, e2, _) -> t1 = t2 && PhysicalEquality e1 e2
      | Name (s1), Name (s2) -> s1 = s2
      | FuncName (n1), FuncName (n2) -> n1 = n2
      | BinOp (o1, t1, lhs1, rhs1, _), BinOp (o2, t2, lhs2, rhs2, _) ->
        o1 = o2 && t1 = t2 &&
          PhysicalEquality lhs1 lhs2 && PhysicalEquality rhs1 rhs2
      | RelOp (o1, lhs1, rhs1, _), RelOp (o2, lhs2, rhs2, _) ->
        o1 = o2 && PhysicalEquality lhs1 lhs2 && PhysicalEquality rhs1 rhs2
      | Load (n1, t1, e1, _), Load (n2, t2, e2, _) ->
        n1 = n2 && t1 = t2 && PhysicalEquality e1 e2
      | Ite (c1, t1, f1, _), Ite (c2, t2, f2, _) ->
        PhysicalEquality c1 c2 &&
          PhysicalEquality t1 t2 && PhysicalEquality f1 f2
      | Cast (k1, t1, e1, _), Cast (k2, t2, e2, _) ->
        k1 = k2 && t1 = t2 && PhysicalEquality e1 e2
      | Extract (e1, t1, p1, _), Extract (e2, t2, p2, _) ->
        PhysicalEquality e1 e2 && t1 = t2 && p1 = p2
      | Undefined (t1, s1), Undefined (t2, s2) -> t1 = t2 && s1 = s2
      | _ -> false
    | _ -> false

  static member inline HashVar (rt: RegType) (rid: RegisterID) =
    19 * (19 * int rt + int rid) + 1

  static member inline HashPCVar (rt: RegType) =
    19 * int rt + 2

  static member inline HashTempVar (rt: RegType) n =
    19 * (19 * int rt + n) + 3

  static member inline HashUnOp (op: UnOpType) e =
    19 * (19 * int op + e.HashKey) + 4

  static member inline HashName ((s, n): Symbol) =
    19 * (19 * s.GetHashCode () + n) + 5

  static member inline HashFuncName (s: string) =
    (19 * s.GetHashCode ()) + 6

  static member inline HashBinOp (op: BinOpType) (rt: RegType) e1 e2 =
    19 * (19 * (19 * (19 * int op + int rt) + e1.HashKey) + e2.HashKey) + 7

  static member inline HashRelOp (op: RelOpType) e1 e2 =
    19 * (19 * (19 * int op + e1.HashKey) + e2.HashKey) + 8

  static member inline HashLoad (endian: Endian) (rt: RegType) e =
    19 * (19 * (19 * int endian + int rt) + e.HashKey) + 9

  static member inline HashIte cond t f =
    19 * (19 * (19 * cond.HashKey + t.HashKey) + f.HashKey) + 10

  static member inline HashCast (kind: CastKind) (rt: RegType) e =
    19 * (19 * (19 * int kind + int rt) + e.HashKey) + 11

  static member inline HashExtract e (rt: RegType) pos =
    19 * (19 * (19 * e.HashKey + int rt) + pos) + 12

  static member inline HashUndef (rt: RegType) (s: string) =
    19 * (19 * int rt + s.GetHashCode ()) + 13

  override __.GetHashCode () =
    match __ with
    | Num n -> n.GetHashCode ()
    | Var (rt, rid, _, _) -> E.HashVar rt rid
    | Nil -> 0
    | PCVar (rt, _) -> E.HashPCVar rt
    | TempVar (rt, n) -> E.HashTempVar rt n
    | UnOp (op, e, _) -> E.HashUnOp op e
    | Name (s) -> E.HashName s
    | FuncName (s) -> E.HashFuncName s
    | BinOp (op, rt, e1, e2, _) -> E.HashBinOp op rt e1 e2
    | RelOp (op, e1, e2, _) -> E.HashRelOp op e1 e2
    | Load (endian, rt, e, _) -> E.HashLoad endian rt e
    | Ite (cond, t, f, _) -> E.HashIte cond t f
    | Cast (k, rt, e, _) -> E.HashCast k rt e
    | Extract (e, rt, pos, _) -> E.HashExtract e rt pos
    | Undefined (rt, s) -> E.HashUndef rt s
*)

  (*
  override __.Equals rhs =
    match rhs with
    | :? SymLoc as rhs ->
      match __, rhs with
      | Const bv1, Const bv2 -> bv1 = bv2
      | PlaceHolder, PlaceHolder -> true
      | BinOp (op1, a1, b1), BinOp (op2, a2, b2) ->
        if op1 <> op2
          || a1.GetHashCode () <> a2.GetHashCode ()
          || b1.GetHashCode () <> b2.GetHashCode () then false
        else a1 = a2 && b1 = b2
      (* TODO: use hash comparison first *)
      | Keccak256 args1, Keccak256 args2 ->
        args1 = args2
      | Storage slot1, Storage slot2 -> slot1 = slot2
      | Memory (pubAddr1, addr1), Memory (pubAddr2, addr2) ->
        pubAddr1 = pubAddr2 && addr1 = addr2
      | Calldata (pubAddr1, addr1), Calldata (pubAddr2, addr2) ->
        pubAddr1 = pubAddr2 && addr1 = addr2
      | FreeMemPtr (pubAddr1, id1), FreeMemPtr (pubAddr2, id2) ->
        pubAddr1 = pubAddr2 && id1 = id2
      | _ -> false
    | _ -> false

  static member inline HashConst bv =
    19 * bv.GetHashCode () + 1

  static member inline HashPlaceHolder () =
    19 * 0 + 2

  static member inline HashBinOp op a b =
    19 * (19 * int op + a.GetHashCode ()) + b.GetHashCode () + 3

  static member inline HashKeccak256 args =
    args
    |> List.fold (fun acc a -> 19 * acc + a.GetHashCode ()) 0
    |> (+) 4

  static member inline HashStorage slot =
    19 * slot.GetHashCode () + 5

  static member inline HashMemory pubAddr addr =
    19 * (19 * pubAddr.GetHashCode () + addr.GetHashCode ()) + 6

  static member inline HashCalldata pubAddr addr =
    19 * (19 * pubAddr.GetHashCode () + addr.GetHashCode ()) + 7

  static member inline HashFreeMemPtr pubAddr id =
    19 * (19 * pubAddr.GetHashCode () + id) + 8

  /// TODO: not use 19 => ...
  override __.GetHashCode () =
    match __ with
    | Const bv -> SymLoc.HashConst bv
    | PlaceHolder -> SymLoc.HashPlaceHolder ()
    | BinOp (op, a, b) -> SymLoc.HashBinOp op a b
    | Keccak256 args -> SymLoc.HashKeccak256 args
    | Storage slot -> SymLoc.HashStorage slot
    | Memory (pubAddr, addr) -> SymLoc.HashMemory pubAddr addr
    | Calldata (pubAddr, addr) -> SymLoc.HashCalldata pubAddr addr
    | FreeMemPtr (pubAddr, id) -> SymLoc.HashFreeMemPtr pubAddr id
  *)

/// Constraint 세상에서 사용되는 변수.
type TagVar =
  /// a variable in a specific public function.
  | TagVarPublic of pubAddr: Addr * var: Variable
  /// private function param or ret value.
  /// note that they are all stack variables (word-wise).
  | TagVarPrivate of privAddr: Addr * nth: int64 * isArg: bool
  /// For representing symoblic locations
  // TODO: 여기서 비교하는 overhead 줄이려면, SymLoc을 어떤 유일한 정수로 매핑하는 맵을 하나 만들어야할듯
  | TagVarSym of SymLoc

type PrivArgRetInfo =
  | PrivArgInfo of ProgramPoint: ProgramPoint * FunctionAddress: Addr * Offset: int64
  | PrivRetInfo of ProgramPoint: ProgramPoint * FunctionAddress: Addr * Offset: int64

/// We consider (merge) all of the three regions: calldata, storage, and memory.
/// TODO: classify tags by their kinds (e.g. behavior, memory, etc.)
type Tag =
  (*
    type-related tags
  *)
  /// propagates its type to the dst (used for forward prop)
  | TagSupertypeOf of variable: TagVar
  /// fetch type hints from the dst (used for type inference)
  | TagSubtypeOf of variable: TagVar

  (*
    operational tags
  *)
  /// propagate its all tags into the dst
  | TagEqualsTo of dst: TagVar

  (*
    behavior hints from step 1
  *)
  /// used as an AND operand
  | TagAndWithBitmask of operand: BitVector
  /// used as a LT operand
  | TagLt of upperBound: TagVar
  /// used as an address type (e.g. call parameter)
  | TagAddress
  /// used as a calldata ptr
  | TagCalldataPtr
  | TagStoragePtr
  /// when returning values from a public function
  | TagReturn of inMem: TagVar * location: TagVar * length: TagVar
  /// raw mem store.
  /// memory aliasing에 쓰임.
  | TagRawMemStore of inMem: TagVar * addr: TagVar * value: TagVar
  /// mem store; off is None if it is stored to the start of the memory
  | TagFreeMemStore of freePtrRootMem: TagVar * off: TagVar option * value: TagVar
  /// mem store with loop
  | TagFreeMemStoreWithPhi of freePtrRootMem: TagVar * off: TagVar option * delta: TagVar * value: TagVar
  | TagCalldataCopy of freePtrRootMem: TagVar * dst: TagVar option * src: TagVar * len: TagVar
  | TagSStore of keyAddr: TagVar * value: TagVar
  /// used as an offset (no pointer)
  /// e.g. offset in [ ptr + offset ]
  | TagUsedAsOffset
  /// used as a pointer
  /// e.g. ptr + 0xcafebeef
  | TagUsedAsPointer
  ///
  | TagDoubleIsZero
  /// TODO: separate tags (e.g. TagMStore8 with some value...)
  | TagStoredAsString
  | TagIsSigned

  (*
    memory
  *)
  /// this is a variable that was dereferenced from...
  | TagMemoryLoad of mem: TagVar * addr: TagVar
  | TagIsFreeMemPtr
  | TagString

  (*
    calldata
  *)
  (* inferred structures *)
  | TagArray of elemVar: TagVar * length: int

  (*

    new tags
    FIXME: 위에 tag들은 이제 대부분 안 씀

  *)

  /// 어떤 해쉬 연산의 결과이다.
  | TagHash of memVar: TagVar * off: TagVar * len: TagVar
  /// SLOAD 명령어의 결과.
  | TagStorageLoad of location: TagVar
  /// SSTORE 명령어.
  | TagStorageStore of off: TagVar * value: TagVar

  /// Free memory SymLoc인 경우에만 가질 수 있는 태그.
  /// 이를 통해, 해당 free memory가 어떤 값들을 갖는지 알 수 있다.
  | TagHasFreeMemStore of rootFreeMemVar: TagVar * addr: TagVar * value: TagVar

  /// 어디에 속할 때 (e.g. p = p + 0x20이면, p + 0x20은 p에 속함)
  | TagPtrBelongsTo of freePtrTagVar: TagVar
  /// 가질 때
  | TagHasPtr of ptrTagVar: TagVar

  /// StorageLoad와 사촌관계
  | TagCalldataLoad of location: TagVar
  | TagCalldataCopy2 of dst: TagVar* src: TagVar * len: TagVar

  /// 어떤 심볼릭한 storage 변수가 key를 가질 때 사용한다.
  /// e.g. mapping (k => v) m;에서, TagHasKey(m, k)
  | TagHasKey of var: TagVar

  /// 어떤 타입 힌트가 분명할 때 씀.
  /// TODO: TagAddress 등 삭제.
  | TagHasType of ty: Type

  /// 배열 원소 타입
  //| TagHasElemAs of elemVar: TagVar

  /// 어떤 and op의 결과인지.
  | TagAndOp of arg1: TagVar * arg2: TagVar

  /// 이거 conditional jump condition으로 쓰이면 추가됨.
  | TagUsedAsHighLevJumpCond

  /// 사칙연산에 쓰였는지. 이거 없어야 bool로 introduce함.
  /// 사칙연산 operand로 쓰였든, 그 결과이든
  | TagUsedInArithOp of op: BinOpType * nth: int

  | TagUsedAsRelOperand of op: RelOpType

  /// mstore 따위에 의해 offset으로 쓰였다면 -> 높은 확률로 primitive 아님 (그냥 offset).
  | TagUsedAsMemStoreOffset

  /// 루프에서 deref될 때 추가함.
  /// array이거나 bytes임.
  | TagReadValueInLoop


type PhiLoopInfo = {
  Initial: Variable
  Delta: Variable
}

(*
type Constraint =
  /// lhs |-> rhs
  | ConsAssign of lhs: Term * rhs: Term

and Term =
  | TermTy of Type
  | TermFV of Variable
  | TermUnion of Term list
  | TermMeet of Term list
*)


/// Used as a final representation of a function type
type PerFuncType = {
  //[<JsonConverter(typeof(HexStringConverter))>]
  Addr: Addr
  /// for storage
  Offset: Addr
  Kind: string //
  Params: string list
  Returns: string list
}

module Tag =
  let getTagVars = function
    | TagStorageLoad loc -> [ loc ]
    | TagCalldataLoad loc -> [ loc ]
    | TagMemoryLoad (mem, addr) -> [ mem; addr ]
    | TagSupertypeOf var -> [ var ]
    | TagSubtypeOf var -> [ var ]
    | TagEqualsTo dst -> [ dst ]
    | TagAndWithBitmask _ -> []
    | TagLt upperBound -> [ upperBound ]
    | TagAddress -> []
    | TagCalldataPtr -> []
    | TagStoragePtr -> []
    | TagReturn (inMem, location, len) -> [ inMem; location; len ]
    | TagRawMemStore (inMem, addr, value) -> [ inMem; addr; value ]
    | TagFreeMemStore (freePtrRootMem, off, value) ->
      (Option.toList off) @ [ freePtrRootMem; value ]
    | TagFreeMemStoreWithPhi (freePtrRootMem, off, delta, value) ->
      (Option.toList off) @ [ freePtrRootMem; delta; value ]
    | TagCalldataCopy (freePtrRootMem, dst, src, len) ->
      (Option.toList dst) @ [ freePtrRootMem; src; len ]
    | TagSStore (keyAddr, value) -> [ keyAddr; value ]
    | TagUsedAsOffset -> []
    | TagUsedAsPointer -> []
    | TagDoubleIsZero -> []
    | TagStoredAsString -> []
    | TagArray (elemVar, _) -> [ elemVar ]
    | TagString -> []
    | TagHash (memVar, off, len) -> [ memVar; off; len ]
    | TagHasKey var -> [ var ]
    | TagStorageStore (off, value) -> [ off; value ]
    | TagHasType _ -> []
    | TagAndOp (arg1, arg2) -> [ arg1; arg2 ]
    | TagUsedAsHighLevJumpCond -> []
    | TagUsedInArithOp _ -> []
    | TagReadValueInLoop -> []
    | TagUsedAsRelOperand _ -> []
    | TagHasFreeMemStore (inMem, addr, value) -> [ inMem; addr; value ]
    | TagUsedAsMemStoreOffset -> []
    | TagPtrBelongsTo freePtrTagVar -> [ freePtrTagVar ]
    | TagHasPtr ptrTagVar -> [ ptrTagVar ]
    | TagCalldataCopy2 (dst, src, len) -> [ dst; src; len ]
    | TagIsFreeMemPtr -> []
    | TagIsSigned -> []

module Type =
  let rec meet t1 t2 =
    match t1, t2 with
    | _ when t1 = t2 -> t1
    (* top인 타입이 들어왔는데 0이 아닌 다른 게 있었다면 -> 모두 고려 *)
    (*
    | TyTop, TyStruct fields
    | TyStruct fields, TyTop when fields.Count = 1 && fields.ContainsKey 0
      ->
      fields[0]
    *)
    (* 만약 필드가 0에 하나인 게 들어오면 -> 그냥 primitive지 뭐*)
    | TyTop, TyStruct fields
    | TyStruct fields, TyTop when fields.Count = 1 && fields.ContainsKey 0
      ->
      fields[0]
    | TyTop, _ -> t2
    | _, TyTop -> t1
    | TyAddr, TyUInt 160
    | TyUInt 160, TyAddr -> TyAddr
    (*
      bytes & array => bytes
      이건 우리 design 내에서의 이야기
    *)
    | TyBytes, TyArray _
    | TyArray _, TyBytes -> TyBytes
    (*
      array & array
    *)
    | TyArray (elemType1, len1), TyArray (elemType2, len2) ->
      let elemType = meet elemType1 elemType2
      let len =
        match len1, len2 with
        | 0, l | l, 0 -> l (* 0보다는 다른 길이가 더 구체적이다*)
        | _ -> min len1 len2 (* 아니라면 더 작은걸루 ㄱㄱㄱ*)
      TyArray (elemType, len)
    (*
      uint8 * bool = bool
      => mapping에서 1바이트 차지하기 때문에 필요
    *)
    | TyUInt 8, TyBool
    | TyBool, TyUInt 8 -> TyBool
    (* struct와 struct 간 연산 *)
    | TyStruct fields1, TyStruct fields2 ->
      (* fields1 = base *)
      let fields =
        fields2.Keys
        |> Seq.fold (fun (acc: Map<_,_>) k ->
          let v2 = fields2[k]
          if acc.ContainsKey k then
            let v1 = acc[k]
            let v = meet v1 v2
            acc.Add (k, v)
          else
            acc.Add (k, v2)) fields1
      TyStruct fields
    (* struct와 단일 타입간 연산*)
    (* 이경우, struct의 offset이 0 하나이라면, struct를 단일 타입으로 바꾼다*)
    | TyStruct fields, t
    | t, TyStruct fields ->
      if fields.ContainsKey 0 && fields.Count = 1 then
        (* shrink*)
        let v = fields[0]
        meet v t
      else
        (* add t into fields *)
        let newFields =
          if fields.ContainsKey 0 then
            fields.Add (0, meet fields[0] t)
          else
            fields.Add (0, t)
        TyStruct newFields
    (*
      mapping끼리의 연산
      => key와 value를 각각 meet
    *)
    | TyMapping (k1, v1), TyMapping (k2, v2) ->
      TyMapping (meet k1 k2, meet v1 v2)
    | TyUInt b1, TyInt b2 ->
      TyInt <| min b1 b2
    | TyInt b1, TyUInt b2 ->
      TyInt <| min b1 b2
    | TyInt b1, TyInt b2 ->
      TyInt <| min b1 b2
    (*TODO: report the type conflicts not only for result but also for easy debugging *)
    | _ -> t1 (* TODO: we conservatively keep the previous abstract value since we dunno how to transfer the value *)

  let join t1 t2 =
    match t1, t2 with
    | _ when t1 = t2 -> t1
    (* bot + x = x *)
    | TyBot, _ -> t2
    | _, TyBot -> t1
    (* top + x = top *)
    | TyTop, _ -> TyTop
    | _, TyTop -> TyTop
    //| TyUInt 256, _ -> TyUInt 256
    //| _, TyUInt 256 -> TyUInt 256
    (* ... *)
    | _ -> t1 (* TODO *)

module TagVar =
  let toVar = function
    | TagVarPublic (_, var) -> var
    | _ -> failwith "cannot convert to a variable"

