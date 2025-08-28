module Types (* type-recovery related *)

open B2R2
open CPTypes

(*
[<RequireQualifiedAccess>]
/// kind of value-set
/// e.g.
/// A = P(Calldata, 0x4+0x20, 0)
/// B = P(A, 0x20, [ T(V, 0x20) ])
/// where V has a constraint of LT(V, N) and N is the upper bound of the array
type Pointer =
  | Ptr of basePtr: Pointer * offset: int * terms: EExpr list
  (* represent which region it refers to *)
  | Calldata (* 1 *)
  | Storage (* 2 *)
  | Memory (* 3 *)
*)

