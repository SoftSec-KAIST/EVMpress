module CPTypes

open System.Collections.Generic
open B2R2.BinIR.SSA
open B2R2.BinIR
open B2R2
open Prelude
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.DataFlow

open EVMpress.Type

/// TODO: Rename to `Bundle`.
(*
type PubFuncInfo = {
  Addr: Addr
  SSA: IDiGraph<SSABasicBlock, CFGEdgeKind>
  Root: IVertex<SSABasicBlock>
  CPState: SSASparseDataFlow.State<ConstantDomain.Lattice>
  KExprMemo: Dictionary<Variable, KExpr>
  RootMemMemo: Dictionary<int, Variable option>
}
*)

module KExpr =
  let isUninterestingVar v =
    match v with
    | { Kind = RegVar (_, _, name) }
        when name = "SP"
          || name = "PC"
          || name = "GAS" -> true
    | _ -> false

  let tryGetVar e =
    match e with
    | KVar v -> Some v
    | KNum (v, _) -> v
    | KLoad (v, _, _) -> v
    | KStore (v, _, _, _) -> v
    | KCast (v, _, _) -> v
    | KRelOp (v, _, _, _) -> v
    | KBinOp (v, _, _, _) -> v
    | KUnOp (v, _, _) -> v
    | KExtract (v, _) -> v
    | KIte (v, _, _, _) -> v
    | KExprList (v, _) -> v
    | KFuncName _ -> None
    | KNil -> None

  let toVar e = tryGetVar e |> Option.get

  (* tail-recursive *)
  let ofList l = KExprList (None, l)

  let rec toList (args: KExpr) =
    match args with
    | KExprList (_, args) -> args
    | _ -> failwith "invalid app arg format"

  /// Convert Expr to KExpr.
  let rec ofExpr (bundle: PerFuncDataFlowInfo) recentVar e =
    match e with
    | Var var ->
      match bundle.KExprMemo.TryGetValue var with
      | false, _ ->
        let kexpr = ofExprAux bundle recentVar e
        bundle.KExprMemo[var] <- kexpr
        kexpr
      | true, kexpr -> kexpr
    | _ -> ofExprAux bundle recentVar e

  and private ofExprAux (bundle: PerFuncDataFlowInfo) recentVar e =
    match e with
    | Num n -> KNum (recentVar, n)
    | Var v when isUninterestingVar v -> KVar v
    | Var v ->
      match bundle.CPState.SSAEdges.Defs.TryGetValue v with
      | true, Def (_, e) -> ofExpr bundle (Some v) e
      | true, Phi (_, ids) ->
        bundle.KExprMemo[v] <- KVar v (* to prevent inf loops *)
        let givenId = v.Identifier
        let ids = Array.distinct ids |> Array.filter (fun id -> id <> givenId)
        let exprs =
          ids |> Array.map (fun id ->
            let v = { v with Identifier = id }
            ofExpr bundle None (Var v))
        (*
        // FIXME: inf loop T_T 0x00000000ede6d8d217c60f93191c060747324bca
        let exprs' =
          exprs
          |> Array.filter (fun e -> tryGetVar e <> Some v)
          |> Array.distinct
        *)
        let exprs' =
          exprs
          |> Array.filter (fun e -> tryGetVar e <> Some v)
        (* redundant phi:
           e.g. x = phi(x; y)
           we can translate this into just y *)
        if exprs.Length <> exprs'.Length && exprs'.Length >= 1 && Array.forall (fun x -> x = exprs'[0]) exprs' (*exprs'.Length = 1*) then
          let exprToReturn = Array.head exprs'
          //cpState.KExprs[(recentVar, e)] <- exprToReturn
          exprToReturn
        else
          KVar v (* leave a phi as it is *)
      | _ -> KVar v
    | ExprList exprs ->
      let exprs = List.map (ofExpr bundle None) exprs
      KExprList (recentVar, exprs)
    | Load (v, rt, e) ->
      let e = ofExpr bundle None e
      KLoad (recentVar, v, e)
    | Store (v, rt, e1, e2) ->
      let e1 = ofExpr bundle None e1
      let e2 = ofExpr bundle None e2
      KStore (recentVar, v, e1, e2)
    | Cast (castKind, rt, e) ->
      let e = ofExpr bundle None e
      KCast (recentVar, castKind, e)
    | RelOp (relOpType, rt, e1, e2) ->
      let e1 = ofExpr bundle None e1
      let e2 = ofExpr bundle None e2
      KRelOp (recentVar, relOpType, e1, e2)
    | BinOp (binOpType, rt, e1, e2) ->
      let e1 = ofExpr bundle None e1
      let e2 = ofExpr bundle None e2
      KBinOp (recentVar, binOpType, e1, e2)
    | UnOp (unOpType, rt, e) ->
      let e = ofExpr bundle None e
      KUnOp (recentVar, unOpType, e)
    | Extract (e, rt, pos) ->
      let e = ofExpr bundle None e
      KExtract (recentVar, e)
    | Ite (e1, rt, e2, e3) ->
      let e1 = ofExpr bundle None e1
      let e2 = ofExpr bundle None e2
      let e3 = ofExpr bundle None e3
      KIte (recentVar, e1, e2, e3)
    | FuncName name -> KFuncName name
    | Undefined (_, name) -> KUndefined (recentVar, name)

