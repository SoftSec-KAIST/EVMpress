module Loop

(*
open CP
open CPTypes

open B2R2.BinIR.SSA
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.BinIR

type LoopVarInfo = {
  /// the inter var of itself
  InterVar: InterVar
  /// its initial value
  IValue: EExpr
  /// delta
  Delta: EExpr
}

let tryGetLoopVarInfo (cp: CP) iv =
  let vid, inSP, var = iv
  let ee = CPHelper.expandExprToEExpr cp vid (Some iv) (Var var)
  match ee with
  | ELoad (memInterVar, ENum (addr, _), _unused) ->
    let vid', inSP', memVar' = memInterVar
    let m = cp.EvalExpr vid' (Var memVar')
    let m = M.ofV m
    let addr = SPAddr.ofBitVector addr
    match m.TryGetValue addr with
    | false, _ -> failwith "TODO: mem slot is empty"
    | true, slot ->
      let _, rds = slot
      (* here we assume that there is two rds: one for initial value and another
         for value inc/dec *)
      let rds = Set.toArray rds
      if rds.Length <> 2 then None (* FIXME: this may be dangerous*)
      else
        let firstIV = rds[0]
        let secondIV = rds[1]
        let fn iv =
          let vid, inSP, var = iv
          let ee = CPHelper.expandExprToEExpr cp vid (Some iv) (Var var)
          ee
        let ee1 = fn firstIV (* intial value (constant) *)
        let ee2 = fn secondIV (* addition of a delta and variable *)
        match ee1, ee2 with
        | initialValue, EBinOp (BinOpType.ADD, addValue, ELoad _, _)
        | initialValue, EBinOp (BinOpType.ADD, ELoad _, addValue, _) ->
          { InterVar = iv
            IValue = initialValue
            Delta = addValue }
          |> Some
        | _ -> None
  | _ -> None
*)
