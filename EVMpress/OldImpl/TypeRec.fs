module TypeRec

open B2R2
open B2R2.BinIR
open B2R2.BinIR.SSA
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.BinGraph
open System.Collections.Generic
open CPTypes
open TypeRecTypes
open System.Threading.Tasks

open Prelude
open Prelude.Global
open Types
open Engine
open B2R2.MiddleEnd.DataFlow
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies
open SolveInfo
open B2R2.Collections
open B2R2.MiddleEnd
open EVMpress.Type
open EVMpress.Utils

let filterAddr = None

[<AutoOpen>]
module private HelperFunctions =
  let rec unrollAppArgs (args: BinIR.SSA.Expr) =
    match args with
    | SSA.ExprList args -> args
    | _ -> failwith "invalid app arg format"

  let isExprFreePtrSlot e =
    match e with
    | Num bv when bv.BigValue = 0x40 -> true
    | _ -> false

  let isBVEqualTo bv (n: bigint) =
    (bv: BitVector).BigValue = n

  let isBV0x20 (bv: BitVector) =
    bv.BigValue = 0x20

  let fnGetCPState m addr =
    let { CPState = cpState } = (m: Dictionary<_, _>)[addr]
    cpState
  let fnGetBundleFromTagVar (m: Dictionary<_, _>) tagVar =
     match tagVar with
     | TagVarPublic (pubAddr, _) -> m[pubAddr]
     | _ -> failwith "cannot get CPState from non-public tag var"
  let fnGetCPStateFromTagVar m tagVar =
     match tagVar with
     | TagVarPublic (pubAddr, _) -> fnGetCPState m pubAddr
     | _ -> failwith "cannot get CPState from non-public tag var"
  let fnGetKExprFromTagVar m tagVar =
    match tagVar with
    | TagVarPublic (pubAddr, var) ->
      let bundle = m[pubAddr]
      KExpr.ofExpr bundle None (Var var)
    | _ -> failwith "cannot get KExpr from non-public tag var"
  let fnGetPubAddrFromTagVar tagVar =
    match tagVar with
    | TagVarPublic (pubAddr, _) -> pubAddr
    | _ -> failwith "cannot get pub addr from non-public tag var"
  let fnExpandPhiVarsToKExprs funcInfo var ids =
    ids
    |> Seq.map (fun id -> KExpr.ofExpr funcInfo None (Var { var with Identifier = id }))
    |> Seq.toList
  let fnGetPhiIds (cpState: SSASparseDataFlow.State<_>) var =
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> []
    | true, stmt ->
      match stmt with
      | Phi (_, ids) -> List.ofArray ids
      | _ -> []
  let fnIsPhiVar (cpState: SSASparseDataFlow.State<_>) var =
    match cpState.SSAEdges.Defs.TryGetValue var with
    | false, _ -> false
    | true, stmt ->
      match stmt with
      | Phi _ -> true
      | _ -> false
  /// Mem addr to variable
  let fnIsKExprFreePtr addrExpr =
    match addrExpr with
    | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
      let args = KExpr.toList args
      let [ inMemExpr; addrExpr ] = args
      match addrExpr with
      | KNum (_, bv) when isBVEqualTo bv 0x40UL -> true
      | _ -> false
    | _ -> false
  /// TODO: memoization
  /// this is used to find the representative mem var of a specific memory region.
  let rec fnFindDominatingFreeMemVar bundle memVar =
    fnTryFindDominatingFreeMemVarAux bundle Set.empty memVar
    |> Option.get
  and fnTryFindDominatingFreeMemVarAux bundle s memVar =
    let key = (memVar: SSA.Variable).Identifier
    let m = (bundle: PerFuncDataFlowInfo).RootMemMemo
    let cpState = bundle.CPState
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
                |> Seq.map (fun id -> fnTryFindDominatingFreeMemVarAux bundle s { memVar with Identifier = id })
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
              | BinOp (BinOpType.APP, _, FuncName "mstore", args) ->
                let args = unrollAppArgs args
                let [ addr; value ] = args
                let kAddr = KExpr.ofExpr bundle None addr
                match kAddr with
                (* if the current mem was defined by a mapping { 0x40 |-> x },
                   then the current mem is the root (dominating) mem var *)
                | KNum (_, bv) when isBVEqualTo bv 0x40UL -> Some memVar
                (* otw, just proceed to find the root *)
                | _ -> fnTryFindDominatingFreeMemVarAux bundle s inMemVar
              | _ -> fnTryFindDominatingFreeMemVarAux bundle s inMemVar
            | _ -> failwithf "TODO: invalid mem store stmt: %A" stmt
      m[key] <- retVal
      retVal
  /// currently we assume that the loc must be a free ptr
  let fnTryGetRootMemVarFromFreePtrVar bundle loc =
    match KExpr.ofExpr bundle None (Var loc) with
    | e when fnIsKExprFreePtr e ->
      match e with
      | KBinOp (_, BinOpType.APP, KFuncName "mload", args) ->
        let args = KExpr.toList args
        let [ KVar inMem; _kLoc ] = args
        (* find its root until it meets store oper with { 0x40 |-> x } *)
        (* FIXME: inspection required *)
        // Some <| fnFindDominatingFreeMemVar inMem
        fnTryFindDominatingFreeMemVarAux bundle Set.empty inMem
      | _ -> failwith "this must be an mload expression"
    | _ -> None (*TODO*)

(*
  [Predicates]

  // Stmt
  Stmt_Info(stmt, pubAddr, vid, index)
  Stmt_Kind(stmt, "def" | ...)
  Stmt_Param(stmt, nth, expr)

  // Expr
  ? Expr_Info(expr)
  Expr_Kind(expr, "const", "add" | "gt" | "calldataload" | ...)
  Expr_Param(expr, nth, expr)

  // for memory read
  Mem_Load(memVar, addr, const)

*)

(*
let DefaultRules = """
  %%%
  %%% Stmt
  %%%
  Stmt_HasExpr(stmt, expr) :-
    Stmt_Kind(stmt, "def"),
    Stmt_Param(stmt, 1, expr).

  %%%
  %%% Expr
  %%%
  % const
  % ex) Expr_EvaluateToConst("expr_41", "0x1")
  Expr_EvaluateToConst(expr, pubAddr, vid, const) :-
    Stmt_Info(stmt, pubAddr, vid, _idx),
    Stmt_HasExpr(stmt, expr),
    Expr_Kind(expr, "const"),
    Expr_Param(expr, 0, const).

  % transitivity
  Expr_EvaluateToConst(expr, pubAddr, vid, const) :-
    Stmt_Info(stmt, pubAddr, vid, _idx),
    Stmt_HasExpr(stmt, expr),
    Expr_Kind(expr, "var"),
    Expr_Param(expr, 0, var),
    Var_EvaluateToConst(var, pubAddr, vid, const).

  % load from memory
  Expr_EvaluateToConst(expr, pubAddr, vid, const) :-
    Expr_Kind(expr, "load"),
    Expr_Param(expr, 0, memVar),
    Expr_Param(expr, 1, addr),
    Mem_LoadToVar(pubAddr, vid, memVar, addr, vid', var),
    Var_EvaluateToConst(var, pubAddr, vid', const).

  %%%
  %%% Var
  %%%
  Var_EvaluateToConst(var, pubAddr, vid, const) :-
    Stmt_Info(stmt, pubAddr, vid, _idx),
    Stmt_Kind(stmt, "def"),
    Stmt_Param(stmt, 0, var),
    Stmt_Param(stmt, 1, expr),
    Expr_EvaluateToConst(expr, pubAddr, vid, const).

  %%%
  %%% Calldata
  %%%
  Calldata_ConstLoc(const) :-
    Expr_Kind(expr, "calldataload"),
    Expr_Param(expr, 0, locExpr),
    Stmt_HasExpr(stmt, locExpr),
    Stmt_Info(stmt, pubAddr, vid, _idx),
    Expr_EvaluateToConst(locExpr, pubAddr, vid, const).
"""
*)

(*
let DefaultRules = """
  %%%
  %%% -
  %%%

  %IsSame(var1, var2) :- IsSame(var2, var1).
  %IsSame(var, var') :- IsSame(var, m), IsSame(m, var').
  %IsSame(var, var') :- Def(var, e), Var(e, var').

  %BinOp(e, kind, e1', e2) :- BinOp(e, kind, e1, e2), Var(e1, var1), IsSame(var1, var1'), Var(e1', var1').
  %BinOp(e, kind, e1, e2') :- BinOp(e, kind, e1, e2), Var(e2, var2), IsSame(var2, var2'), Var(e2', var2').

  CPtr(var) :- Var(e, var), BinOp(_, "app", fname, args), FuncName(fname, "msg.data"), BinOp(args, "::", e, _).

"""
*)

let DefaultRules = "" // System.IO.File.ReadAllText "DefaultRules.dl"

[<AutoOpen>]
module private TypeRec =
  let varToString blkAddr (var: BinIR.SSA.Variable) =
    let kind =
      match var.Kind with
      | BinIR.SSA.RegVar (_, _, regName) -> regName
      | BinIR.SSA.PCVar _ -> "PC"
      | BinIR.SSA.MemVar -> "MEM"
      | BinIR.SSA.TempVar _ -> "TMP"
      | _ -> failwith "TODO"
    let id = var.Identifier
    $"{blkAddr}_{kind}_{id}".Replace (" ", "")

  (*
  let rec exprToString (cp: CP.CP) vid blkAddr (e: BinIR.SSA.Expr) =
    match e with
    | BinIR.SSA.Num bv -> bv.ValToString ()
    | BinIR.SSA.Var ({ Kind = BinIR.SSA.TempVar _ } as var) ->
      varToString blkAddr var
      (*
      // let rds = cp.FindReachingDefs vid var
      let spToState = cp.States.GetByFirstKey vid
      let sps = spToState.Keys
      let sp = sps |> Seq.head (* FIXME: introduce phi here? *)
      let interVar = vid, sp, var
      let stmt = cp.InterVarToDefStmt[interVar]
      // let ee = CPHelper.expandEExpr cp vid e
      match stmt with
      | BinIR.SSA.Def (_, e) -> exprToString cp vid blkAddr e
      | _ -> failwith "TODO"
      *)
    | BinIR.SSA.Var var -> varToString blkAddr var
    | BinIR.SSA.Load (var, _, addr) ->
      match cp.EvalExpr vid addr with
      | CPTypes.V.Number bv ->
        let addrStr = bv.ValToString ()
        $"MEM[{addrStr}]"
      | _ -> (* unresolvable *)
        let addrStr = exprToString cp vid blkAddr addr
        $"MEM[{addrStr}]"
    | BinIR.SSA.BinOp (BinIR.BinOpType.APP, _, BinIR.SSA.FuncName fnName, args) ->
      match fnName with
      (*
      | "msg.value"
      | "msg.data.size"
      | "msg.sender"
      | "selfbalance"
      | "extcodehash"
      | "extcodesize" -> fnName
      | "msg.data" -> (* CALLDATALOAD *)
        let args = unrollAppArgs [] args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"calldataload({argStr})"
      | "sload" -> (* SLOAD *)
        let args = unrollAppArgs [] args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"sload({argStr})"
      | "calldatacopy" -> (* CALLDATACOPY *)
        let args = unrollAppArgs [] args
        (* TODO: handle arg strings in the constant prop engine *)
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"calldatacopy({argStr})"
      | "delegatecall" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"delegatecall({argStr})"
      | "staticcall" ->
        let args = unrollAppArgs [] args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"staticcall({argStr})"
      | "returndatasize" ->
        let args = unrollAppArgs [] args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"returndatasize({argStr})"
      | "returndatacopy" ->
        let args = unrollAppArgs [] args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"returndatacopy({argStr})"
      | "codecopy" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"codecopy({argStr})"
      | "exp" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"exp({argStr})"
      | "keccak256" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"keccak256({argStr})"
      | "sstore" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"sstore({argStr})"
      | name when name.StartsWith "log" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"{name}({argStr})"
      | "call" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"call({argStr})"
      | "revert" ->
        let args = unrollAppArgs [] args
        // let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        let argStr = "UNRESOLVED"
        $"revert({argStr})"
      | "return" ->
        let args = unrollAppArgs [] args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"return({argStr})"
      | _ when args = BinIR.SSA.Nil -> fnName
      *)
      | name ->
        let args = unrollAppArgs args
        let argStr = args |> List.map (exprToString cp vid blkAddr) |> String.concat ", "
        $"{name}({argStr})"
      //| _ -> failwith "TODO"
    | BinIR.SSA.BinOp (op, _rt, e1, e2) ->
      let e1Str = exprToString cp vid blkAddr e1
      let e2Str = exprToString cp vid blkAddr e2
      let op = BinIR.BinOpType.toString op
      $"{e1Str} {op} {e2Str}"
    | BinIR.SSA.Cast (_, _, e) -> exprToString cp vid blkAddr e
    | BinIR.SSA.RelOp (op, _, e1, e2) ->
      let e1Str = exprToString cp vid blkAddr e1
      let e2Str = exprToString cp vid blkAddr e2
      let op = BinIR.RelOpType.toString op
      $"{e1Str} {op} {e2Str}"
    | BinIR.SSA.UnOp (op, _, e) ->
      let eStr = exprToString cp vid blkAddr e
      let op = BinIR.UnOpType.toString op
      $"{op} {eStr}"
    | BinIR.SSA.Extract (e, _, _) ->
      exprToString cp vid blkAddr e
    | _ -> failwith "TODO"

  let isNotInterestingVarDef var =
    match (var: BinIR.SSA.Variable).Kind with
    | BinIR.SSA.RegVar (_, _, regName) -> regName = "PC" (*|| regName = "SP"*)
    // | BinIR.SSA.TempVar _ -> true
    | _ -> false

  let stmtToString fn blkAddr vid stmt lastIns =
    let cp = (fn: Func).CP
    match stmt with
    (* Filter out meaningless definitions *)
    | Def (var, _) when isNotInterestingVarDef var -> ""
    (* Store *)
    | Def (var, Store (prevVar, _, addr, value)) ->
      match addr with
      // | BinIR.SSA.Var { Kind = BinIR.SSA.TempVar _ } -> ""
      (* stack *)
      // | BinIR.SSA.Var { Kind = BinIR.SSA.RegVar (_, _, "SP") } ->
      | _ ->
        // let addrStr = exprToString blkAddr addr
        let addrStr =
          match (fn: Func).CP.EvalExpr vid addr with
          | CPTypes.V.Number bv -> bv.ValToString ()
          | _ -> exprToString cp vid blkAddr value
        let valueStr = exprToString cp vid blkAddr value
        $"MEM[{addrStr}] := {valueStr}"
      (* memory *)
      (*
      | _ ->
        let addrStr = exprToString cp vid blkAddr addr
        let valueStr = exprToString cp vid blkAddr value
        $"MEM[{addrStr}] := {valueStr}"
      *)
    (* Def *)
    | Def (var, e) ->
      let varNameStr = varToString blkAddr var
      let expStr = exprToString cp vid blkAddr e
      $"{varNameStr} := {expStr}"
    (*
    | BinIR.SSA.Jmp (BinIR.SSA.InterJmp _) ->
      if List.isEmpty succAddrs then ""
      else
        (* must have only one successor *)
        let succAddr = List.exactlyOne succAddrs
        if ftAddr = succAddr then ""
        else $"goto LABEL_{succAddr:x}"
    *)
    | Jmp _ -> ""
    | SideEffect _ ->
      let tokens = (lastIns: FrontEnd.BinLifter.Instruction).Decompose false
      let insName = tokens[0].AsmWordValue
      $"{insName}()"
    | ExternalCall (e, inVars, _outVars) ->
      let eStr = exprToString cp vid blkAddr e
      let argStrs = inVars |> List.map (fun var -> varToString blkAddr var) |> String.concat ", "
      $"extc {eStr}({argStrs})"
    | _ -> failwith "TODO"

#if ! TYPEDEBUG
  let mutable tempWriter: System.IO.StreamWriter = null
#else
  let mutable tempWriter: System.IO.StreamWriter = null
#endif

  let printf fmt =
#if TYPEDEBUG
    let fn (s: string) =
      tempWriter.Write s
    Printf.kprintf fn fmt
#else
    Printf.kprintf ignore fmt
#endif

  let print = printfn

  let inline printfn fmt =
#if TYPEDEBUG
    //let fn (s: string) = tempWriter.WriteLine s
    let fn (s: string) = printfn "%s" s
    //let fn = ignore
#else
    let fn = ignore
    //let fn (s: string) = tempWriter.WriteLine s
#endif
    let fn (s: string) = printfn "%s" s
    Printf.kprintf fn fmt

  /// this is not for pretty printing but for TYPEDEBUGging.
  let printVertices (cfgRec: CFGRecoverer) fnAddr =
    let funcMap = cfgRec.FuncMap
    let fn = funcMap[fnAddr]
    let vertices =
      fn.IRCFG.GetVertices ()
      |> Seq.filter (fun v -> not <| v.VData.IsFakeBlock ())
      |> Seq.sortBy (fun v -> v.VData.PPoint.Address)
    printfn $"function fun_{fnAddr:x}:"
    vertices |> Seq.iter (fun v ->
      let vid = v.GetID ()
      let ssaBlk = fn.VidToSSABlk vid
      let blkAddr = ssaBlk.PPoint.Address
      let lastIns = ssaBlk.InsInfos |> Array.last |> fun info -> info.Instruction
      printfn "LABEL_%x:" ssaBlk.PPoint.Address (* TODO: remove this when no distant jump comes in *)
      for (_pp, stmt) in ssaBlk.SSAStmtInfos do
        let s = stmtToString fn blkAddr vid stmt lastIns
        if s <> "" then printfn "\t%s" s
      (*..*)
      let ftAddr = ssaBlk.Range.Max + 1UL
      let succs = DiGraph.GetSuccs (fn.IRCFG, v)
      if List.isEmpty succs then ()
      elif List.length succs = 1 then
        let succ = List.exactlyOne succs
        if succ.VData.IsFakeBlock () then
          printfn $"\tcall fun_{succ.VData.PPoint.Address:x}"
        elif succ.VData.PPoint.Address = ftAddr then ()
        else printfn "\tgoto LABEL_%x" succ.VData.PPoint.Address
      else (* cond branch *)
        let succAddrs =
          succs
          |> List.map (fun v -> v.VData.PPoint.Address)
          |> List.rev
          |> Array.ofList
        let lastStmt = ssaBlk.SSAStmtInfos |> Array.last |> fun (_, stmt) -> stmt
        match lastStmt with
        | Jmp (InterCJmp (cond, tAddr, fAddr))->
          let condStr = exprToString fn.CP vid blkAddr cond
          let getHexStr bv =
            (bv: BitVector).ValToString ()
            |> fun s -> s.Replace ("0x", "")
          let tAddrStr =
            match fn.CP.EvalExpr vid tAddr with
            | CPTypes.V.Number bv -> "LABEL_" + getHexStr bv
            | _ -> exprToString fn.CP vid blkAddr tAddr
          let fAddrStr =
            match fn.CP.EvalExpr vid fAddr with
            | CPTypes.V.Number bv -> "LABEL_" + getHexStr bv
            | _ -> exprToString fn.CP vid blkAddr fAddr
          printfn $"\tif ({condStr})"
          printfn $"\t\tgoto {tAddrStr:x}"
          printfn $"\telse"
          printfn $"\t\tgoto {fAddrStr:x}"
          (*
          let succ = succs[1]
          if succ.VData.IsFakeBlock () then
            printfn $"\t\tcall fun_{succ.VData.PPoint.Address:x}"
          elif succ.VData.PPoint.Address = ftAddr then ()
          else printfn "\t\tgoto LABEL_%x" succ.VData.PPoint.Address
          *)
        | _ -> failwith "TODO"
    )
    printfn ""

  let printAll (cfgRec: CFGRecoverer) =
    let funcMap = cfgRec.FuncMap
    funcMap.Keys |> Seq.iter (fun fnAddr -> printVertices cfgRec fnAddr)

  /// To draw a graph on a single (super) CFG, which is generated during type
  /// recovery.
  let printVerticesOnGraph (g: DiGraph<IRBasicBlock, _>) (cp: CP) (perVertexSSABlk: Dictionary<_, _>) =
    let roots = DiGraph.GetUnreachables g
    let vertices =
      Traversal.foldTopologically g roots (fun acc v -> v :: acc) [] |> List.rev
    vertices |> Seq.iter (fun v ->
      let vid = v.GetID ()
      let ssaBlk = perVertexSSABlk[vid]
      let blkAddr = (ssaBlk: SSABasicBlock).PPoint.Address
      let lastIns = ssaBlk.InsInfos |> Array.last |> fun info -> info.Instruction
      if DiGraph.GetPreds (g, v) |> (Seq.isEmpty >> not) then
        printfn "LABEL_%x:" ssaBlk.PPoint.Address
      for (_pp, stmt) in ssaBlk.SSAStmtInfos do
        let stmtStr =
          match stmt with
          | Def ({ Kind = TempVar _ }, e) -> ""
          | Def ({ Kind = RegVar (_, _, "SP") }, e) -> ""
          | Def (memVar, Store (inMemVar, _, addr, value)) ->
            match cp.EvalExpr vid addr with
            | CPTypes.V.Number bv
                when BitVector.Ge (bv, BitVector.OfInt64 CP.StackPointerLB rt)
                     |> BitVector.IsTrue ->
              let valueEExpr = CPHelper.expandExprToEExpr cp vid None value
              let valueStr = EExpr.toString valueEExpr
              let s = $"MEM[{bv.ValToString ()}] := {valueStr}"
              s
            | CPTypes.V.Number bv
                when bv = BitVector.OfUInt64 0x40UL rt -> (* free ptr *)
              let valueEExpr = CPHelper.expandExprToEExpr cp vid None value
              let valueStr = EExpr.toString valueEExpr
              let s = $"FREE := {valueStr}"
              s
            | _ ->
              let addrEExpr = CPHelper.expandExprToEExpr cp vid None addr
              let valueEExpr = CPHelper.expandExprToEExpr cp vid None value
              let addrStr = EExpr.toString addrEExpr
              let valueStr = EExpr.toString valueEExpr
              let s = $"MEM[{addrStr}] := {valueStr}"
              s
          | Def (var, e) ->
            let eExpr = CPHelper.expandExprToEExpr cp vid None e
            let eStr = EExpr.toString eExpr
            let varStr = "VAR_TEMP_FIXME"
            let s = $"{varStr} := {eStr}"
            s
          | _ -> ""
        if stmtStr = "" then ()
        else
          printfn "\t%s" stmtStr
      (*..*)
      let ftAddr = ssaBlk.Range.Max + 1UL
      let succs = DiGraph.GetSuccs (g, v)
      if List.isEmpty succs then ()
      elif List.length succs = 1 then
        let succ = List.exactlyOne succs
        if ftAddr = 0x2c8UL then ()
        if succ.VData.PPoint.Address = ftAddr then ()
        else printfn "\tgoto LABEL_%x" succ.VData.PPoint.Address
      else (* cond branch *)
        (*
        let succAddrs =
          succs
          |> List.map (fun v -> v.VData.PPoint.Address)
          |> List.rev
          |> Array.ofList
        *)
        let lastStmt = ssaBlk.SSAStmtInfos |> Array.last |> fun (_, stmt) -> stmt
        match lastStmt with
        | Jmp (InterCJmp (cond, tAddr, fAddr))->
          let condEExpr = CPHelper.expandExprToEExpr cp vid None cond
          let tAddrEExpr = CPHelper.expandExprToEExpr cp vid None tAddr
          let fAddrEExpr = CPHelper.expandExprToEExpr cp vid None fAddr
          let condStr = EExpr.toString condEExpr
          let tAddrStr = EExpr.toString tAddrEExpr
          let fAddrStr = EExpr.toString fAddrEExpr
          let getHexStr bv =
            (bv: BitVector).ValToString ()
            |> fun s -> s.Replace ("0x", "")
          let tAddrStr =
            match cp.EvalExpr vid tAddr with
            | CPTypes.V.Number bv -> "LABEL_" + getHexStr bv
            | _ -> EExpr.toString tAddrEExpr
          let fAddrStr =
            match cp.EvalExpr vid fAddr with
            | CPTypes.V.Number bv -> "LABEL_" + getHexStr bv
            | _ -> EExpr.toString fAddrEExpr
          printfn $"\tif ({condStr})"
          printfn $"\t\tgoto {tAddrStr}"
          (*
          printfn $"\telse"
          printfn $"\t\tgoto {fAddrStr}"
          *)
        | _ -> failwith "TODO"
    )
    printfn ""

*)

(*
let getReturnValueIdx ssa =
  (ssa: SSACFG).IterVertex (fun v ->
    v.VData.SSAStmtInfos
    |> Seq.map (fun (_, stmt) -> stmt)
    |> Seq.iter (fun stmt ->
      match stmt with
      | Def (_, Store _) -> ()
      | Def (_, e) ->
        match e with
        | Var { Kind = StackVar (_, off); Identifier = 0 } ->

          ()
        | _ -> ()
      | _ -> ()))
*)

(*
let getFuncArgCnt (ctx: CFGBuildingContext<EVMFuncUserContext, _>) =
  let ir = ctx.CFG
  let cp = ctx.UserContext.CP
  let argMap = Dictionary ()
  ir.IterVertex (fun v ->
    let vid = v.GetID ()
    let ssaBlk = fn.VidToSSABlk vid
    ssaBlk.SSAStmtInfos
    |> Seq.map (fun (_, stmt) -> stmt)
    |> Seq.iter (fun stmt ->
      match stmt with
      | Def (_, Store _) -> ()
      | Def (_, e) ->
        let ee = CPHelper.expandExprToEExpr cp vid None e
        match ee with
        | ELoad (_, ENum (n, _), _) ->
          if n.Le InitialStackPointer |> BitVector.IsTrue then
            let n = BitVector.ToInt64 n
            let delta = n - InitialStackPointerAddr
            let nth = delta / 32L
            argMap[nth] <- ()
          else ()
        | _ -> ()
      | _ -> ()
      ())
    ())
  let readCnt = argMap.Count
  if fn.ReturnProperty = ReturnProperty.NoRet then readCnt
  else readCnt - 1 (* decrease one for a return address *)
*)

(*
[<RequireQualifiedAccess>]
type Term =
  | Const of BitVector
  | Var of pubAddr: Addr * vid: VertexID * var: Variable
  // | StackVar of pubAddr: Addr * vid: VertexID * pp: ProgramPoint * offset: int
  | BinOp of BinOpType * Term * Term
  | Load of pubAddr: Addr * vid: VertexID * memVar: Term * addr: Term
  | Store of pubAddr: Addr * vid: VertexID * memVar: Term * addr: Term * value: Term

type Solver () =
  let facts = List ()

  (*
  let addFact (name: string) (terms: Term list) isNegated =
    Datalog.Expr.create name terms isNegated
    |> facts.Add
  *)
  let addFact (fact: string) =
    facts.Add fact

  member __.RemoveAllFacts () =
    facts.Clear ()

  member __.AddFact fact = addFact fact

  member __.Solve () =
    let dl =
      { Datalog.edb = Map.empty
        Datalog.factsBeingRetracted = Map.empty
        Datalog.incomingFacts = Map.empty
        Datalog.rules = [] }
    __.AddFact DefaultRules
    let dl =
      facts
      |> Seq.collect Datalog.LexParser.parseText
      |> Seq.fold (fun dl stmt -> fst <| Datalog.Datalog.executeStmt dl stmt) dl

    for fact in facts do
      printfn "%s" fact

    // exit 0

    (*
    let test =
      Datalog.LexParser.parseText """Var_EvaluateToConst(var, pubAddr, vid, const)?"""
    let test = List.head test
    let res = Datalog.Datalog.executeStmt dl test
    *)
    dl
*)

type TypeRecoverer (brew: BinaryBrew<EVMFuncUserContext, DummyContext>,
                    pubBodyAddresses: Addr list) =
  let hdl = brew.BinHandle
  let dataFlowManager = DataFlowManager(hdl)
  let superCFGManager = SuperCFGManager(brew, dataFlowManager, pubBodyAddresses)

  let exprToId = Dictionary ()
  let idToExpr = Dictionary ()

  let varToId = Dictionary ()
  let idToVar = Dictionary ()

  let isUninterestingVar (var: Variable) =
    match var.Kind with
    | PCVar _ -> true
    | RegVar (_, _, regName) ->
      regName = "SP"
      || regName = "GAS"
    | _ -> false

  (*
  let getStmtId pubAddr vid stmtIndex =
    let stmtId = $"stmt_0x{pubAddr:x}_{vid}_{stmtIndex}"
    match stmtIds.TryGetValue stmtId with
    | true, _ -> stmtId
    | false, _ ->
      solver.AddFact $"""Stmt_Info("{stmtId}", "0x{pubAddr:x}", {vid}, {stmtIndex})."""
      stmtId
  *)

  let getVarId fnAddr cpState var =
    let var = findRootVar cpState var
    let varKey = fnAddr, var
    match varToId.TryGetValue varKey with
    | true, id -> id
    | false, _ ->
      let varStr = Variable.ToString var
      let id = $"var_{fnAddr:x}_{varStr}"
      varToId[varKey] <- id
      idToVar[id] <- var
      id

  (*
  let rec addFactExpr fnAddr cpState exprId e =
    match e with
    | Num bv ->
      solver.AddFact $"""Num("{exprId}", "{bv.ValToString ()}")."""
    | Var var ->
      let varId = getVarId fnAddr cpState var
      solver.AddFact $"""Var("{exprId}", "{varId}")."""
    | Store (memVar, _, addr, value) ->
      let memVarId = getVarId fnAddr cpState memVar
      let addrId = getExprId fnAddr cpState addr
      let valueId = getExprId fnAddr cpState value
      solver.AddFact $"""Store("{exprId}", "{memVarId}", "{addrId}", "{valueId}")."""
    | Load (memVar, _, addr) ->
      let memVarId = getVarId fnAddr cpState memVar
      let addrId = getExprId fnAddr cpState addr
      solver.AddFact $"""Load("{exprId}", "{memVarId}", "{addrId}")."""
    | BinOp (op, _, e1, e2) ->
      let e1Id = getExprId fnAddr cpState e1
      let e2Id = getExprId fnAddr cpState e2
      let op = BinOpType.toString op
      solver.AddFact $"""BinOp("{exprId}", "{op}", "{e1Id}", "{e2Id}")."""
    | RelOp (op, _, e1, e2) ->
      let e1Id = getExprId fnAddr cpState e1
      let e2Id = getExprId fnAddr cpState e2
      let op = RelOpType.toString op
      solver.AddFact $"""RelOp("{exprId}", "{op}", "{e1Id}", "{e2Id}")."""
    | FuncName fnName ->
      solver.AddFact $"""FuncName("{exprId}", "{fnName}")."""
    | _ ->
      printfn "TODO: %A" e

  and getExprId (fnAddr: Addr) cpState e =
    let exprKey = fnAddr, e
    match exprToId.TryGetValue exprKey with
    | true, id -> id
    | false, _ ->
      let count = exprToId.Count
      let id = $"expr_{fnAddr:x}_{count}"
      exprToId[exprKey] <- id
      idToExpr[id] <- e
      addFactExpr fnAddr cpState id e
      id
  *)

  (*
  let rec fnAddFactStmt vid stmtId e =
    match e with
    | Var var ->
      let varId = getVarId pubAddr vid var
      // let defs = cp.FindReachingDefs vid var
      let facts =
        [ $"""Stmt_Kind({stmtId}, "var")."""
          $"""Stmt_Param({stmtId}, 0, {varId}).""" ]
      facts
    | Num bv ->
      let facts =
        [ $"""Stmt_Kind({stmtId}, "bv")."""
          $"""Stmt_Param({stmtId}, 0, "{bv.ToString ()}").""" ]
      facts
    | Load (memVar, _, addr) ->
      let facts =
        [ $"""Stmt_Kind({stmtId}, "load")."""
          $"""Stmt_Param({stmtId}, 0, "{memVar.ToString ()}")."""
          $"""Stmt_Param({stmtId}, 1, "{addr}").""" ]
      facts
    | Store (memVar, _, addr, value) ->
      let addrId = getExprId addr
      let valueId = getExprId value
      let facts =
        [ $"""Stmt_Kind({stmtId}, "store")."""
          $"""Stmt_Param({stmtId}, 0, "{memVar.ToString ()}")."""
          $"""Stmt_Param({stmtId}, 1, "{addr.ToString ()}")."""
          $"""Stmt_Param({stmtId}, 2, "{value.ToString ()}").""" ]
      facts
    | _ -> failwith "TODO"
  *)

  let getOffsetFromBigIntBitmask bi =
    let rec fn bi off =
      if (bigint.Remainder (bi, 256)) <> 0 then off
      else
        let bi = bi >>> 8
        fn bi (off + 1)
    fn bi 0

  let inferTypes  (solveInfo: SolveInfo)
                  privArgRetInfos
                  finalFuncTypes =
    let calldataRegions = Dictionary ()
    let returnMemoryRegions = Dictionary ()
    let storageRegions = Dictionary ()
    let fnFindRootVarFromTagVar tv =
      match tv with
      | TagVarPublic (pubAddr, v) ->
        let cpState = solveInfo.PubFuncInfos[pubAddr].CPState
        (*FIXME: this logic is inconsistent through the entire code.
          we may not want to care of the notion of root var itself *)
        let foundRootVar = findRootVar cpState v
        TagVarPublic (pubAddr, foundRootVar)
      | _ -> tv
    let gatherEqualTagVars (tv: TagVar) =
      let rec fn tv acc =
        let acc = (acc: ImmSet<_>).Add tv
        match solveInfo.PerVarTags.TryGetValue tv with
        | false, _ -> acc
        | true, tags ->
          tags
          |> Seq.filter (fun t ->
            match t with
            | TagEqualsTo tv -> true
            | _ -> false)
          |> Seq.fold (fun acc t ->
            match t with
            | TagEqualsTo tv when not <| acc.Contains tv -> fn tv acc
            | _ -> acc) acc
      fn tv ImmSet.Empty
#if !TYPEDEBUG
    let typeMemo = Dictionary ()
#else
    let typeMemo = Vis.perTagVarTypes
#endif
    let containsUsedAsArithOperand tags skipDiv =
      tags |> Seq.exists (fun t ->
        match t with
        | TagUsedInArithOp (BinOpType.DIV, 1) when skipDiv -> false (*skip*)
        | TagUsedInArithOp _ -> true
        | _ -> false)
    let containsUsedAsRelOperand tags =
      tags |> Seq.exists (fun t ->
        match t with
        | TagUsedAsRelOperand _ -> true
        | _ -> false)
    let containsUsedAsHighLevJumpCond tags =
      tags |> Seq.exists (fun t ->
        match t with
        | TagUsedAsHighLevJumpCond  -> true
        | _ -> false)
    let containsIsFreeMemPtr tags =
      tags |> Seq.exists (fun t ->
        match t with
        | TagIsFreeMemPtr -> true
        | _ -> false)
    let rec fnGetTypeFromTags tags =
      fnGetTypeFromTagsAux ImmDict.Empty tags

    /// jidoc
    and fnGetTypeFromTagsAux visited tags =
      let mutable ty = TyTop
      for (tag: Tag) in tags do
        match tag with
        | TagIsSigned -> ty <- Type.meet ty <| TyInt 256
        | TagSubtypeOf v -> ty <- Type.meet ty <| fnGetTypeFromTagVarAux visited v
        | TagAddress -> ty <- Type.meet ty <| TyAddr
        | TagAndWithBitmask bv when BitVector.isBitmask bv && BitVector.getBitmaskBits bv % 8 = 0 ->
          ty <- Type.meet ty <| TyUInt (BitVector.getBitmaskBits bv)
        | TagArray (v, len) -> (*recursive tracking*)
          ty <- Type.meet ty <| TyArray (fnGetTypeFromTagVarAux visited v, len)
        (* cases using specific patterns *)
        | TagDoubleIsZero
          when not <| containsUsedAsArithOperand tags true
            && not <| containsUsedAsRelOperand tags ->
          ty <- Type.meet ty <| TyBool
        | TagUsedAsHighLevJumpCond
          when not <| containsUsedAsArithOperand tags true
            && not <| containsUsedAsRelOperand tags ->
          ty <- Type.meet ty <| TyBool
        | TagStoredAsString -> ty <- Type.meet ty <| TyBytes
        | TagHasType t -> ty <- Type.meet ty t
        | _ -> ()
      let ty = fnPostprocessType ty tags
      ty
    (*TODO: be careful to this rule*)
    and fnPostprocessType ty tags =
      if ty = TyTop && containsIsFreeMemPtr tags then TyBytes
      else if containsUsedAsArithOperand tags true || containsUsedAsRelOperand tags then ty
      else
        match ty with
        | TyUInt 160 -> TyAddr
        | TyUInt 8 when containsUsedAsHighLevJumpCond tags -> TyBool
        | _ -> ty
    and fnGetTypeFromTagVar var =
      let rootVar = fnFindRootVarFromTagVar var
      fnGetTypeFromTagVarAux ImmDict.Empty rootVar
    and fnGetTypeFromTagVarAux (visited: ImmDict<_, _>) var =
      if typeMemo.ContainsKey var then typeMemo[var]
      //if visited.ContainsKey var then visited[var] (* FIXME *)
      else
        let visited = visited.Add (var, TyTop) (* prevent inf loop *)
        typeMemo[var] <- TyTop (* prevent inf loop *)
#if TYPEDEBUG
        match var with
        | TagVarPublic (pubAddr, v) ->
          ()
        | _ -> ()
#endif
        let var = fnFindRootVarFromTagVar var
        match solveInfo.PerVarTags.TryGetValue var with
        | false, _ -> TyTop
        | true, tags ->
          let ty = fnGetTypeFromTagsAux visited tags
          typeMemo[var] <- ty
          ty
    let fnHasTag var tag =
      match solveInfo.PerVarTags.TryGetValue var with
      | false, _ -> false
      | true, tags -> tags |> Seq.exists (fun t -> t = tag)
    let fnGetCPStateFromTagVar tv =
      fnGetCPStateFromTagVar solveInfo.PubFuncInfos tv
    let fnGetBundleFromTagVar tv =
      let pubAddr = fnGetPubAddrFromTagVar tv
      solveInfo.PubFuncInfos[pubAddr]
    let fnTryGetRootMemVarFromFreePtrTagVar tv =
      let pubAddr = fnGetPubAddrFromTagVar tv
      let bundle = solveInfo.PubFuncInfos[pubAddr]
      fnTryGetRootMemVarFromFreePtrVar bundle (TagVar.toVar tv)
    // let fnGetKExprFromTagVar = fnGetKExprFromTagVar solveInfo.PubFuncInfos
    let fnGetCalldataRegion pubAddr =
      match calldataRegions.TryGetValue pubAddr with
      | false, _ ->
        let m = Dictionary ()
        calldataRegions[pubAddr] <- m
        m
      | true, m -> m
    let fnGetCalldataReturnRegion pubAddr =
      match returnMemoryRegions.TryGetValue pubAddr with
      | false, _ ->
        let m = Dictionary ()
        returnMemoryRegions[pubAddr] <- m
        m
      | true, m -> m
    let perPrivFunc = Dictionary ()
    let findKeyTagVar tags =
      tags
      |> Seq.pick (fun tag ->
        match tag with
        | TagHasKey v -> Some v
        | _ -> None)
    let tryFindKeyTagVarFromTagVar tv =
      match solveInfo.PerVarTags.TryGetValue tv with
      | false, _ ->
        (*FIXME: why? *)
        //failwith "found no key tag var"
        None
      | true, tags -> Some <| findKeyTagVar tags
    let symHandledSet = HashSet ()
    let updateStorageRegion slot (mask: BitVector) ty =
      let off =
        (*FIXME: should not have zero bitmask *)
        if mask.IsZero then 0UL
        else getOffsetFromBigIntBitmask mask.BigValue |> uint64
      let k = slot, off
      match storageRegions.TryGetValue k with
      | true, _ when ty = TyTop || ty = TyUInt 256 -> () (*ignore if the new type is just a top*)
      | _ ->
        let prev = storageRegions.TryGetValue k |> function true, t -> t | _ -> TyTop
        (* TODO: we need to use join here actually (e.g. struct) *)
        let next = Type.meet prev ty
        let rec fnPostProcess ty =
          match ty with
          | TyUInt 7 -> TyBytes(*FIXME: 0xee972ad3b8ac062de2e4d5e6ea4a37e36c849a11*)
          | TyMapping (k, v) ->
            let k = fnPostProcess k
            let v = fnPostProcess v
            TyMapping (k, v)
          | TyArray (v, len) ->
            let v = fnPostProcess v
            TyArray (v, len)
          | TyStruct m when m.Count = 1 ->
            let valTy = m.Values |> Seq.exactlyOne
            let valTy = fnPostProcess valTy
            valTy
          | _ -> ty
        let next = fnPostProcess next
        storageRegions[k] <- next
        //storageRegions[k] <- Type.join prev ty
#if TYPEDEBUG
        printfn "[+] updated into: %A" <| storageRegions[k].ToString ()
#endif
    let rec getTypeFromCallSymLoc symLoc =
      match symLoc with
      | SymLoc.BinOp (BinOpType.ADD, symLocAdjust, SymLoc.CLoad (pubAddr, p)) ->
        let ty = fnGetTypeFromTagVar (TagVarSym symLoc)
        match ty with
        | TyArray (elemTy, 0) ->
          let symLocElem = SymLoc.CLoad (pubAddr, symLoc + SymLoc.Const (BitVector(0x20, 256<rt>)))
          let elemTy' = fnGetTypeFromTagVar (TagVarSym symLocElem)
          let elemTyMerged =
            if elemTy' = TyTop then elemTy (*FIXME: how to merge them? *)
            else elemTy'
          (*TODO: meet or join?*)
          TyArray (elemTyMerged, 0)
        | TyArray (elemTy, len) ->
          let symLocElem = SymLoc.CLoad (pubAddr, symLoc)
          let elemTy' = fnGetTypeFromTagVar (TagVarSym symLocElem)
          TyArray (elemTy', len)
        | TyBytes -> TyBytes
        | _ -> TyBot
      | SymLoc.CLoad (pubAddr, SymLoc.Const bv_loc) ->
        (* check if it is used as ptr *)
        let symLocAdjust = SymLoc.Const (BitVector(0x4, 256<rt>))
        let symLocPtr = symLocAdjust + symLoc
        match getTypeFromCallSymLoc symLocPtr with
        | TyBot -> fnGetTypeFromTagVar <| TagVarSym symLoc
        | ty -> ty
      | _ -> TyBot
    // jidoc
    let handleSymbolicVarCalldata (var: TagVar) tags =
      let zeroBv = BitVector(0L, rt)
      match var with
      | TagVarSym symLoc ->
        match symLoc with
        (*
          cload(const)
          : global primitve type
        *)
        | SymLoc.CLoad (pubAddr, SymLoc.Const bv_loc) ->
          let tagVarVal = symLoc
          let ty = getTypeFromCallSymLoc tagVarVal
          let region = fnGetCalldataRegion pubAddr
          let locBigint = bv_loc.BigValue
          region[locBigint] <- ty
          (*
          let valueTy = fnGetTypeFromTags tags
          let valueTy =
            match valueTy with
            | TyArray (elemTy, len) ->
              let symLocVal = SymLoc.CLoad (pubAddr, symLoc)
              let elemTy' = fnGetTypeFromTagVar (TagVarSym symLocVal)
              let elemTy = Type.meet elemTy elemTy'
              TyArray (elemTy, len)
            | _ -> valueTy
          let region = fnGetCalldataRegion pubAddr
          let locBigint = bv_loc.BigValue ()
          region[locBigint] <- valueTy
          *)
        | _ -> ()
      | _ -> ()
    /// 심볼
    /// jidoc
    let handleSymbolicVarStorage (var: TagVar) tags =
      if not var.IsTagVarSym then ()
      else
#if TYPEDEBUG
        printfn "Symbolic var: %A -> %A" var ((fnGetTypeFromTags tags).ToString ())
#endif
        let zeroBv = BitVector(0L, rt)
        match var with
        (*

        *)
        (*
          mapping(k => struct{})
        *)
        | TagVarSym (SymLoc.BinOp (
            BinOpType.AND,
            SymLoc.SLoad (SymLoc.BinOp (BinOpType.ADD, (SymLoc.Hash [ _; SymLoc.Const bv_loc ] as mapSymLoc), SymLoc.Const bv_structFieldOff)),
            SymLoc.Const bv_posMask)) ->
          let mapTagVar = TagVarSym mapSymLoc
          let keyTagVar = tryFindKeyTagVarFromTagVar mapTagVar
          let keyTy =
            match keyTagVar with
            | Some keyTagVar -> fnGetTypeFromTagVar keyTagVar
            | None -> TyTop
          (* map + 0, pos=0   addr*)
          (* map + 1, pos=0   addr*)
          (* map + 1, pos=20  uint32*)
          (* => mapping(k, (v1,v2,v3))*)
          (*
            e.g.
            0 |-> { 0 |-> ty1 }
            1 |-> { 0 |-> ty2 }
            1 |-> { 20 |-> ty3 }
            => 1 |-> { 0 |-> ty2; 20 |-> ty3 }
          *)
          let fieldOffInt = BitVector.ToInt32 bv_structFieldOff
          let posMaskInt = BitVector.getMSBOffset bv_posMask
          let valueTy = fnGetTypeFromTags tags
          let ty = TyStruct <| Map [ fieldOffInt, TyStruct <| Map [ posMaskInt, valueTy ] ]
          let finalTy = TyMapping (keyTy, ty)
          updateStorageRegion bv_loc zeroBv finalTy
        (*
          global storage variable
        *)
        | TagVarSym symLoc ->
          match symLoc with
          | _ when symHandledSet.Contains var -> ()
          (*
            sload(sha(loc) + _)
            T[] array;
            bytes;
            global dyn array or string/bytes!
          *)
          | SymLoc.SLoad (SymLoc.BinOp (BinOpType.ADD, SymLoc.Hash [ SymLoc.Const slotBv ], SymLoc.PlaceHolder) as baseLoc) ->
            let baseTy = fnGetTypeFromTagVar (TagVarSym baseLoc)
            let elemTy = fnGetTypeFromTags tags
            (*
            let ty =
              match baseTy with
              | TyArray (prevElemTy, len) ->
                TyArray (Type.meet prevElemTy elemTy, len)
              | _ -> baseTy
            *)
            let ty =
              match baseTy with
              | TyArray (prevElemTy, len) ->
                TyArray (Type.meet prevElemTy elemTy, len)
              | TyBytes -> TyBytes
              | _ -> TyArray (elemTy, 0)
            updateStorageRegion slotBv zeroBv ty
          (*
            T[] array;
            bytes;
            global dyn array
            sload(sha(loc) + _) & mask
          *)
          | SymLoc.BinOp (
              BinOpType.AND,
              SymLoc.SLoad (
                SymLoc.BinOp (
                  BinOpType.ADD,
                  SymLoc.Hash [ SymLoc.Const slotBv ],
                  SymLoc.PlaceHolder) as baseLoc
                ),
              SymLoc.Const maskBv)
            ->
            let baseTy = fnGetTypeFromTagVar (TagVarSym baseLoc)
            let elemTy = fnGetTypeFromTags tags
            let off = getOffsetFromBigIntBitmask maskBv.BigValue
            let elemTy = TyStruct <| Map.empty.Add (off, elemTy)
            let ty =
              match baseTy with
              | TyArray (prevElemTy, len) ->
                TyArray (Type.meet prevElemTy elemTy, len)
              | TyBytes -> TyBytes
              | _ -> TyArray (elemTy, 0)
            updateStorageRegion slotBv zeroBv ty
          (*
            sload(loc) & mask
            global compaction
            consider off
          *)
          | SymLoc.BinOp (BinOpType.AND, SymLoc.SLoad (SymLoc.Const slotBv), SymLoc.Const maskBv) ->
            let ty = fnGetTypeFromTags tags
            updateStorageRegion slotBv maskBv ty
          (*
            sload (loc + const)
            struct value
            e.g. the value type in mapping(uint => (string, string))
          *)
          | SymLoc.SLoad (SymLoc.BinOp (BinOpType.ADD, innerLoc, SymLoc.Const bv_fieldOffset)) ->
            let fieldOffset = bv_fieldOffset |> BitVector.ToInt32
            let tyValue = fnGetTypeFromTags tags
            let tyStruct = TyStruct <| Map.ofList [ (fieldOffset, tyValue) ]
            match innerLoc with
            | SymLoc.Hash [ _; SymLoc.Const slotBv ] ->
              let tagVarInnerLoc = TagVarSym <| SymLoc.SLoad innerLoc
              let keyTagVar = tryFindKeyTagVarFromTagVar tagVarInnerLoc
              let keyTy =
                match keyTagVar with
                | Some keyTagVar ->
                  fnGetTypeFromTagVar keyTagVar
                | _ -> TyTop
              let ty = TyMapping (keyTy, tyStruct)
              updateStorageRegion slotBv zeroBv ty
            | _ -> ()
          (*
            mapping (k1 => mapping (k2 => v))
          *)
          | SymLoc.SLoad (SymLoc.Hash [ _; SymLoc.Hash [ _; SymLoc.Const slotBv ] as innerSymLoc ] as outerSymLoc) ->
            let innerTagVarSym = TagVarSym innerSymLoc
            let innerTags = solveInfo.PerVarTags[innerTagVarSym]
            let innerKeyTy = fnGetTypeFromTagVar <| findKeyTagVar innerTags
            (* second key *)
            let outerTagVarSym = TagVarSym outerSymLoc
            let outerTags = solveInfo.PerVarTags[outerTagVarSym]
            let keyTy = fnGetTypeFromTagVar <| findKeyTagVar outerTags
            let valueTagVar = var
            let valueTy = fnGetTypeFromTagVar valueTagVar
            //storageRegions[slotAndOff] <- TyMapping (keyTy, TyMapping (innerKeyTy, valueTy))
            updateStorageRegion slotBv zeroBv <| TyMapping (innerKeyTy, TyMapping (keyTy, valueTy))
          (*
          *)
          | SymLoc.BinOp (
              BinOpType.AND,
              SymLoc.SLoad (SymLoc.Hash [ _; SymLoc.Hash [ _; SymLoc.Const slotBv ] as innerSymLoc ] as outerSymLoc),
              SymLoc.Const bvMask
            ) ->
            let innerTagVarSym = TagVarSym innerSymLoc
            let innerTags = solveInfo.PerVarTags[innerTagVarSym]
            let innerKeyTy = fnGetTypeFromTagVar <| findKeyTagVar innerTags
            (* second key *)
            let outerTagVarSym = TagVarSym outerSymLoc
            let outerTags = solveInfo.PerVarTags[outerTagVarSym]
            let keyTy = fnGetTypeFromTagVar <| findKeyTagVar outerTags
            let valueTagVar = var
            let valueTy = fnGetTypeFromTagVar valueTagVar
            //storageRegions[slotAndOff] <- TyMapping (keyTy, TyMapping (innerKeyTy, valueTy))
            updateStorageRegion slotBv zeroBv <| TyMapping (innerKeyTy, TyMapping (keyTy, valueTy))
          (*
            mapping (k => v)
          *)
          | SymLoc.SLoad (SymLoc.Hash [ _; SymLoc.Const slotBv ]) ->
            (* find key tag var *)
            let keyTagVar = findKeyTagVar tags
            let valueTagVar = var
            (* infer types *)
            let keyTy = fnGetTypeFromTagVar keyTagVar
            let valueTy = fnGetTypeFromTagVar valueTagVar
            let valueTy = TyStruct <| Map.ofList [ (0, valueTy) ]
            //storageRegions[slotAndOff] <- TyMapping (keyTy, valueTy)
            updateStorageRegion slotBv zeroBv <| TyMapping (keyTy, valueTy)
          (*
            sload (loc)
          *)
          | SymLoc.SLoad (innerLoc) ->
            match innerLoc with
            | SymLoc.Const slotBv ->
              let ty = fnGetTypeFromTags tags
              let ty = TyStruct <| Map.ofList [ (0, ty) ]
              updateStorageRegion slotBv zeroBv ty
            | _ -> ()
          | SymLoc.BinOp (BinOpType.AND, (SymLoc.SLoad (SymLoc.Hash [ _; SymLoc.Const slotBv ]) as parentSymLoc), SymLoc.Const maskBv) ->
            (* get parent tag var *)
            let parentTagVar = TagVarSym parentSymLoc
            let parentTags = solveInfo.PerVarTags[parentTagVar]
            (* find key tag var *)
            let keyTagVar = findKeyTagVar parentTags
            let valueTagVar = var
            (* infer types *)
            let keyTy = fnGetTypeFromTagVar keyTagVar
            let valueTy = fnGetTypeFromTagVar valueTagVar
            symHandledSet.Add parentTagVar |> ignore
            //storageRegions[slotAndOff] <- TyMapping (keyTy, valueTy)
            let off = getOffsetFromBigIntBitmask maskBv.BigValue
            let tyStruct = TyStruct <| Map.empty.Add (off, valueTy)
            let finalTy = TyMapping (keyTy, tyStruct)
            //updateStorageRegion slotBv zeroBv <| TyMapping (keyTy, valueTy)
            updateStorageRegion slotBv zeroBv <| finalTy
          | _ -> ()
        | _ -> ()
    (*TODO: optimization: grouping when adding tags *)
    for (KeyValue (var, tags)) in solveInfo.PerVarTags do
      handleSymbolicVarCalldata var tags
      handleSymbolicVarStorage var tags
      (* handle priv param/return types *)
      match var with
      | TagVarPrivate (privAddr, nth, isParam) ->
        (* TODO: calculate supertype relations in the solver, not here *)
        let mutable ty = TyBot
        for tag in tags do
          match tag with
          | TagSupertypeOf v ->
            let currTy = fnGetTypeFromTagVar v
            ty <- Type.join ty currTy
          | _ -> ()
        if not <| perPrivFunc.ContainsKey privAddr then perPrivFunc[privAddr] <- List ()
        let info = (isParam, nth, ty)
        perPrivFunc[privAddr].Add info
#if TYPEDEBUG
        printfn "priv %x %b: %A -> %A" privAddr isParam nth ty
#endif
      | _ -> ()

      /// we use a simple worklist algorithm to get all the related tags to a given free mem region
      let backwardSliceToGatherFreeMemStoreTags pubAddr currId upperBoundId =
        let workingMemVars = UniqueQueue ()
        let visited = HashSet ()
        let mutable collectedTags = []
        workingMemVars.Enqueue <| { Kind = MemVar; Identifier = currId }
        while not workingMemVars.IsEmpty do
          let currMemVar = workingMemVars.Dequeue ()
          if not <| visited.Add currMemVar then ()
          else
            let currTagVar = TagVarPublic (pubAddr, currMemVar)
            match solveInfo.PerVarTags.TryGetValue currTagVar with
            | false, _ -> ()
            | true, tags ->
              for tag in tags do
                match tag with
                | TagHasFreeMemStore (rootFreeMemVar, _, _)
                  when rootFreeMemVar
                       |> TagVar.toVar
                       |> (fun v -> v.Identifier = upperBoundId) ->
                  collectedTags <- tag::collectedTags
                | _ -> ()
            (* track the data-flow *)
            let cpState = solveInfo.GetCPStateFromTagVar currTagVar
            match cpState.SSAEdges.Defs.TryGetValue currMemVar with
            | false, _ -> ()
            | true, stmt->
              match stmt with
              | ExternalCall (BinOp _, inVars, outVars) ->
                let [inMemVar] = inVars
                workingMemVars.Enqueue inMemVar
              | _ -> () (*FIXME*)
        collectedTags |> List.rev

      let isTagVarUsedAsOffset tv =
        match solveInfo.PerVarTags.TryGetValue tv with
        | false, _ -> false
        | true, tags ->
          tags |> Seq.exists (fun t ->
            match t with
            | TagUsedAsMemStoreOffset -> true
            | _ -> false)
      let isKExprUsedAsOffsetForReturn kExpr =
        match kExpr with
        | KBinOp (_, BinOpType.SUB, KBinOp (_, BinOpType.ADD, offsetKExpr, freePtr1), freePtr2)
          when fnIsKExprFreePtr freePtr1 && freePtr1 = freePtr2 -> true
        | _ -> false

      for tag in tags do
        match tag with
        (* pub func - ret *)
        (* jidoc *)
        | TagReturn (memVar, locVar, lenVar) ->
          let lenKExpr = solveInfo.ExpandToKExpr lenVar
          let maybeLen =
            match lenKExpr with
            | KBinOp (_, BinOpType.SUB,
                      KBinOp (_, BinOpType.ADD, KNum (_, bv_len), freePtr1),
                      freePtr2)
              (* TODO: 둘이 같은지 확인해야 하는데, root로 확인해야함 *)
              when KExpr.isFreePtr freePtr1 && KExpr.isFreePtr freePtr2
              ->
              Some bv_len
            | _ -> None
          let pubAddr = fnGetPubAddrFromTagVar memVar
          match fnTryGetRootMemVarFromFreePtrTagVar locVar with
          | None -> () (*TODO*)
          | Some rootFreeMemVar ->
            (* 단순히 root mem에 기록해서는 안 됨 => 그러면 false-negative store *)
            (*TODO:revert*)
            let upperBoundId = rootFreeMemVar.Identifier
            let currID = memVar |> TagVar.toVar |> fun v -> v.Identifier
            let collectedTags = backwardSliceToGatherFreeMemStoreTags pubAddr currID upperBoundId
            for memTag in collectedTags do
              match memTag with
              | TagHasFreeMemStore (_, addrTagVar, valueTagVar) ->
#if TYPEDEBUG
                printfn "mem store addr and value"
                let otherKExpr = solveInfo.ExpandToKExpr addrTagVar
                printfn "%A" otherKExpr
                let valueKExpr = solveInfo.ExpandToKExpr valueTagVar
                printfn "%A" valueKExpr
                match valueKExpr with
                | KBinOp (_, BinOpType.APP, KFuncName "mload", v) ->
                  let [_;v] = KExpr.toList v
                  let var = KExpr.toVar v
                  let cpState = fnGetCPStateFromTagVar addrTagVar
                  let exprs = fnTryGetPhiArgKExprs cpState v
                  ()
                | _ -> ()
#endif
                match solveInfo.ExpandToKExpr addrTagVar with
                (*
                  free ptr alone
                  => offset = 0x0
                *)
                | KBinOp (_, BinOpType.APP, KFuncName "mload", _) ->
                  let kValue = solveInfo.ExpandToKExpr valueTagVar
                  let valueTagVar = KExpr.toVar kValue |> fun v -> TagVarPublic (pubAddr, v)
                  if isTagVarUsedAsOffset valueTagVar
                     || isKExprUsedAsOffsetForReturn kValue
                    (*|| isTagVarLengthField valueTagVar*) then ()
                  else
                    let ty = fnGetTypeFromTagVar valueTagVar
                    let region = fnGetCalldataReturnRegion pubAddr
                    let valueKExpr = solveInfo.ExpandToKExpr valueTagVar
                    let isValueNotInteresting =
                      match valueKExpr with
                      | KNum (_, v) when BitVector.Modulo(v, BitVector(0x20UL, 256<rt>)).IsZero -> true
                      | _ -> false
                    (* old writes -> ignore *)
                    if region.ContainsKey 0 then ()
                    else if isValueNotInteresting then ()
                    else region[0] <- ty
                (*
                  free ptr + const offset
                *)
                | KBinOp (_, BinOpType.ADD,
                          KNum (_, bv_off),
                          KBinOp (_, BinOpType.APP, KFuncName "mload", _))
                | KBinOp (_, BinOpType.ADD,
                          KBinOp (_, BinOpType.APP, KFuncName "mload", _),
                          KNum (_, bv_off))
                  when BitVector.isMultipleOfUInt64 bv_off 0x20UL
                       && (maybeLen.IsNone
                           || (maybeLen.IsSome
                               && BitVector.Lt(maybeLen.Value, bv_off).IsTrue))
                  ->
                  (* 0x289ba1701c2f088cf0faf8b3705246331cb8a839:
                     (root) free mem can be shared in different areas *)
                  let valueKExpr = solveInfo.ExpandToKExpr valueTagVar
#if TYPEDEBUG
                  match valueKExpr with
                  | KBinOp (_, _, KFuncName "mload", args) ->
                    let [mem;loc]= KExpr.toList args
                    let var = KExpr.toVar loc
                    let cpState = fnGetCPStateFromTagVar valueTagVar
                    let ids = fnGetPhiIds cpState var
                    let exprs = fnTryGetPhiArgKExprs cpState loc
                    ()
                  | _ -> ()
#endif
                  let fnResolveAliasToGetTagVars valueKExpr =
                    match valueKExpr with
                    | KBinOp (_, _, KFuncName "mload", KExprList (_, [ kInMem; kAddr ]))
                      when not kAddr.IsKNum
                      ->
                      let rec fnHandleAddr acc visited kAddr =
                        match kAddr with
                        | KVar var when Set.contains var visited ->
                          acc
                        | KVar var ->
                          let visited = Set.add var visited
                          // let cpState = fnGetCPStateFromTagVar valueTagVar
                          let bundle = solveInfo.PubFuncInfos[pubAddr]
                          let exprs = fnTryGetPhiArgKExprs bundle kAddr
                          match exprs with
                          | None -> []
                          | Some exprs ->
                            exprs
                            |> Seq.fold (fun acc kExpr -> fnHandleAddr acc visited kExpr) acc
                        (* mload(mload(0x40) + n) *)
                        | KBinOp (_, BinOpType.APP, KFuncName "mload", _)
                        | KBinOp (_, BinOpType.ADD, _, KBinOp (_, BinOpType.APP, KFuncName "mload", _))
                        | KBinOp (_, BinOpType.ADD, KBinOp (_, BinOpType.APP, KFuncName "mload", _), _)
                          ->
                          let mptrExprAndOff =
                            match KExpr.constantFolding kAddr with
                            | KBinOp (_, BinOpType.ADD, mptrExpr, KNum (_, bv_off))
                            | KBinOp (_, BinOpType.ADD, KNum (_, bv_off), mptrExpr) ->
                              Some <| (mptrExpr, bv_off.BigValue)
                            | KBinOp (_, BinOpType.APP, KFuncName "mload", _) ->
                              Some <| (kAddr, 0I)
                            | _ -> None
                              //failwithf "unexpected case w/ %A" kAddr
                          match mptrExprAndOff with
                          | None -> [] (*FIXME*)
                          | Some (mptrExpr, off) ->
                            let tagVar = TagVarPublic (pubAddr, mptrExpr |> KExpr.toVar)
                            match fnTryGetRootMemVarFromFreePtrTagVar tagVar with
                            | None ->  [](*FIXME*)
                            | Some rootFreeMemVar ->
                              let upperBoundId = rootFreeMemVar.Identifier
                              let currId = kInMem |> KExpr.toVar |> fun v -> v.Identifier
                              let relatedMemTags = backwardSliceToGatherFreeMemStoreTags pubAddr currId upperBoundId
                              relatedMemTags
                              |> Seq.tryPick (fun memTag ->
                                match memTag with
                                | TagHasFreeMemStore (_, addrTagVar, valueTagVar) ->
                                  match solveInfo.ExpandToKExpr addrTagVar |> KExpr.constantFolding with
                                  | KBinOp (_, BinOpType.APP, KFuncName "mload", _)
                                    when off = 0I ->
                                    Some valueTagVar
                                  (*상수 ->찾음*)
                                  | KBinOp (_, BinOpType.ADD,
                                              KNum (_, bv_off),
                                              KBinOp (_, BinOpType.APP, KFuncName "mload", _))
                                  | KBinOp (_, BinOpType.ADD,
                                              KBinOp (_, BinOpType.APP, KFuncName "mload", _),
                                              KNum (_, bv_off))
                                    when bv_off.BigValue = off ->
                                    Some valueTagVar
                                  | _ -> None
                                | _ -> None)
                              |> function
                                | None -> []
                                | Some foundRecentValueTagVar ->
                                  [foundRecentValueTagVar]
                        | _ -> []
                      fnHandleAddr [] Set.empty kAddr
                    | _ -> []
                  let foundValueTagVars =
                    fnResolveAliasToGetTagVars valueKExpr
                  (* now, aliasing is resolved *)

                  let foundValueTagVars = valueTagVar :: foundValueTagVars

                  for foundValueTagVar in foundValueTagVars do
                    (* bytes 같은 copy 타입 추론 *)
                    match foundValueTagVar with
                    | valueTagVar ->
                      let tags = solveInfo.GetTagsFromTagVar valueTagVar
                      for tag in tags do
                        match tag with
                        | TagEqualsTo dstVar ->
                          match dstVar with
                          (* 길이 읽기 *)
                          | TagVarSym (SymLoc.MLoad (_, (SymLoc.FreeMemPtr _ as symLocPtr))) ->
                            let tagVarPtr = TagVarSym symLocPtr
                            let ty = fnGetTypeFromTagVar tagVarPtr
                            let region = fnGetCalldataReturnRegion pubAddr
                            let off = BitVector.ToInt32 bv_off
                            // FIXME: why happening?
                            // 0x0abfb15ca7fce092a30ae8ea445a61db3e08c4e1
                            //if off % 0x20 = 0 then ()
                            if off = 0 && ty = TyBytes then ()
                            else if ty = TyTop then () (*FIXME: name in 0xee972ad3b8ac062de2e4d5e6ea4a37e36c849a11*)
                            else if (match maybeLen with None -> false | Some bv_len -> BitVector.Ge(bv_off,  bv_len).IsTrue) then
                              () (* ignore since it is oob write *)
                            else
                              region[off] <- ty
                          | _ -> ()
                        | _ -> ()

                    let e= solveInfo.ExpandToKExpr foundValueTagVar
                    match e with
                    (*
                      (mptr + const) - mptr
                      => highly likely to be a pointer in the return region
                      => so we can ignore
                    *)
                    | KBinOp (_, BinOpType.SUB,
                                KBinOp (_, BinOpType.ADD, mptr, KNum (_, bv_off)),
                                mptr_2)
                    | KBinOp (_, BinOpType.SUB,
                                KBinOp (_, BinOpType.ADD, KNum (_, bv_off), mptr),
                                mptr_2)
                      when mptr = mptr_2 ->
                      (*
                      let ty = fnGetTypeFromTagVar valueTagVar
                      let region = fnGetCalldataReturnRegion pubAddr
                      let off = BitVector.ToInt32 bv_off
                      if region.ContainsKey off then ()
                      else region[off] <- ty
                      *)
                      ()
                    (*
                      => phi
                    *)
                    | KVar _ ->
                      let kExprs = getPossibleKExprsFromPhiKVar solveInfo pubAddr e
                      let fnIsBytesPattern kExpr =
                        match kExpr with
                        (* (sload(...) /  2) & 0x7f *)
                        | KBinOp (_, BinOpType.AND,
                                    KBinOp (_, BinOpType.DIV,
                                            KBinOp (_, _, KFuncName "sload", _),
                                            KNum (_, bv_2)),
                                    KNum (_, bv_0x7f))
                          when BitVector.isEqualTo bv_2 2UL && BitVector.isEqualTo bv_0x7f 0x7fUL -> true
                        (* (sload(...) >> 1) & 0x7f *)
                        | KBinOp (_, BinOpType.AND,
                                    KBinOp (_, BinOpType.SHR,
                                            KBinOp (_, _, KFuncName "sload", _),
                                            KNum (_, bv_1)),
                                    KNum (_, bv_0x7f))
                          when BitVector.isEqualTo bv_1 1UL && BitVector.isEqualTo bv_0x7f 0x7fUL -> true
                        | _ -> false
                      let hasBytesPattern = kExprs |> Seq.exists fnIsBytesPattern
                      if not hasBytesPattern then
                        let ty = fnGetTypeFromTagVar valueTagVar
                        let region = fnGetCalldataReturnRegion pubAddr
                        let off = BitVector.ToInt32 bv_off
                        if region.ContainsKey off then ()
                        else region[off] <- ty
                      else
                        let region = fnGetCalldataReturnRegion pubAddr
                        let off = BitVector.ToInt32 bv_off
                        region[off] <- TyBytes

                    (*
                      ...
                      => bytes
                    *)
                    | KBinOp (_, BinOpType.DIV,
                              KBinOp (_, BinOpType.AND,
                                      (KBinOp (_, _, KFuncName "sload", sloadArgs) as sloadKExpr),
                                      _), (* => (not x) + y *)
                              KNum (_, bv_0x2))
                    | KBinOp (_, BinOpType.DIV,
                              KBinOp (_, BinOpType.AND,
                                      _,
                                      (KBinOp (_, _, KFuncName "sload", sloadArgs) as sloadKExpr)),
                                      (* => (not x) + y *)
                              KNum (_, bv_0x2))
                      when BitVector.isEqualTo bv_0x2 0x2 ->
                      ()
                      let [kSloadBaseAddrExpr]= sloadArgs |> KExpr.toList
                      let sloadBaseAddrSymLoc = solveInfo.ConvertToStorageSymLoc pubAddr kSloadBaseAddrExpr
                      let sloadBytesSymLoc = (SymLoc.Hash ([sloadBaseAddrSymLoc]) + SymLoc.PlaceHolder)
                      let sloadBytesTagVar = TagVarSym sloadBytesSymLoc
                      let ty = fnGetTypeFromTagVar sloadBytesTagVar
                      if ty = TyBytes then
                        let region = fnGetCalldataReturnRegion pubAddr
                        let off = BitVector.ToInt32 bv_off
                        region[off] <- TyBytes
                      else
                        let ty = fnGetTypeFromTagVar valueTagVar
                        let region = fnGetCalldataReturnRegion pubAddr
                        let off = BitVector.ToInt32 bv_off
                        if region.ContainsKey off then ()
                        else region[off] <- ty
                    (*
                      mptr + 0x20 |-> (sload(c) / 0x100) * 0x100
                      (mptr + alpha) + 0x0 |-> (sload(c) / 0x100) * 0x100
                      and c: bytes
                      => mptr + alpha: bytes
                    *)
                    (*TODO: nested structures *)
                    | KBinOp (_, BinOpType.MUL,
                                 KBinOp (_, BinOpType.DIV,
                                           (KBinOp (_, BinOpType.APP, KFuncName "sload", _) as kSload),
                                           KNum (_, bv_div)),
                                 KNum (_, bv_mul))
                      when BitVector.isEqualTo bv_div 0x100UL
                        && BitVector.isEqualTo bv_mul 0x100UL
                      ->
                      let sloadSymLoc = solveInfo.ConvertToStorageSymLoc pubAddr kSload
                      let ty = fnGetTypeFromTagVar <| TagVarSym sloadSymLoc
                      // TODO; FIXME: implement this
                      ()
                    (*
                      normal cases
                    *)
                    | valueKExpr ->
                      let ty = fnGetTypeFromTagVar valueTagVar
                      let region = fnGetCalldataReturnRegion pubAddr
                      let off = BitVector.ToInt32 bv_off
                      //region[off] <- if region.ContainsKey off then Type.meet region[off] ty else ty
                      if false&& off % 0x20 = 0 then
                        () // TODO: check if |use| = 1 and defined in the return codes
                      elif region.ContainsKey off then ()
                      elif (match maybeLen with None -> false | Some bv_len -> BitVector.Ge(bv_off,  bv_len).IsTrue) then
                        () (* ignore since it is oob write *)
                      else region[off] <- ty
                    ()
                | otherKExpr ->
  #if TYPEDEBUG
                    (*
                    printfn "unsupported mem store addr"
                    printfn "%A" otherKExpr
                    let valueKExpr = solveInfo.ExpandToKExpr valueTagVar
                    printfn "%A" valueKExpr
                    *)
  #endif
                    ()
              | _ -> ()
          ()
          let region = fnGetCalldataReturnRegion pubAddr
          if region.Count = 0 then (*fill the region; this can happen due to skipping of constants that were judged as pointer values *)
            let mutable i = 0
            match maybeLen with
            | None -> ()
            | Some returnRegionLen ->
              let returnRegionLen = BitVector.ToInt32 returnRegionLen
              while i < returnRegionLen do
                region[i] <- TyTop
                i <- i + 0x20
          (*
          match fnTryGetRootMemVarFromFreePtrTagVar locVar with
          (* this is the current memory region's lower bound in our mem exploration *)
          | Some rootMemVar ->
            let returnMemoryRegion = Dictionary ()
            let lowerBoundMemVar = rootMemVar
            let workingMemVars = UniqueQueue ()
            let visited = HashSet ()
            let cpState = fnGetCPStateFromTagVar memVar
            let pubAddr = fnGetPubAddrFromTagVar memVar
            workingMemVars.Enqueue memVar
            while not workingMemVars.IsEmpty do
              let currMemVar = TagVar.toVar <| workingMemVars.Dequeue ()
              visited.Add currMemVar.Identifier |> ignore
              (* parse tags *)
              match solveInfo.PerVarTags.TryGetValue (TagVarPublic (pubAddr, currMemVar)) with
              | false, _ -> ()
              | true, currMemTags ->
                for memTag in currMemTags do
                  match memTag with
                  | TagRawMemStore (inMemTagVar, addrTagVar, valueTagVar) ->
                    ()
                  (* [ ptr + off ] |-> x *)
                  (*
                  | TagFreeMemStore (freePtrRootMem, off, valueVar)
                      when TagVar.toVar freePtrRootMem = rootMemVar ->
                    let off =
                      match off with
                      | None -> (0: bigint)
                      | Some offVar ->
                        match fnGetKExprFromTagVar offVar with
                        | KNum (_, bv) -> bv.BigValue ()
                        | _ -> failwith "TODO: unsupported off expr"
                    let value = fnGetKExprFromTagVar valueVar // -224, 22
                    match value with
                    | _ when off % 32I <> 0 -> ()
                    (*
                    (* ptr + off |-> ptr' - ptr
                       : pointing to somewhere inside the same region pattern.
                       in this case, ptr' can be assumed as a semi-ptr *)
                    | KBinOp (_, BinOpType.SUB, kE1,
                                                kE2)
                        when fnIsKExprFreePtr kE2
                          && rootMemVar = Option.get (fnTryGetRootMemVarFromFreePtrVar <| Option.get (KExpr.tryGetVar kE2)) ->
                      ()
                    *)
                    (*
                    | KBinOp (_, BinOpType.SUB, KBinOp (_, BinOpType.ADD, kOff, kPtr1),
                                                kPtr2)
                        when KExpr.tryGetVar kPtr1 = KExpr.tryGetVar kPtr2 ->
                      ()
                    *)
                    (* if the value was used as an offset, then ignore since this is kinda pointer *)
                    | _ when fnHasTag valueVar TagUsedAsOffset -> ()
                    (* we assume that this is an primitive *)
                    | _ ->
                      let elemTy = fnGetTypeFromTagVar valueVar
                      (* the older (closer to the root mem) stores are ignored *)
                      if returnMemoryRegion.ContainsKey off then ()
                      else
                        returnMemoryRegion[off] <- elemTy
                  *)
                  (* phi *)
                  | TagFreeMemStoreWithPhi (freePtrRootMem, off, delta, valueVar)
                      when TagVar.toVar freePtrRootMem = rootMemVar ->
                    let off =
                      match off with
                      | None -> (0: bigint)
                      | Some offVar ->
                        match fnGetKExprFromTagVar offVar with
                        | KNum (_, bv) -> bv.BigValue ()
                        | _ -> failwith "TODO: unsupported off expr"
                    let value = fnGetKExprFromTagVar valueVar
                    match value with
                    | _ when off % 32I <> 0 -> ()
                    | _ ->
                      let elemTy = fnGetTypeFromTagVar valueVar
                      if returnMemoryRegion.ContainsKey off then ()
                      else
                        returnMemoryRegion[off] <- elemTy
                  | _ -> ()
              (* proceed to its parent mem *)
              if currMemVar = lowerBoundMemVar then ()
              else
                match cpState.SSAEdges.Defs.TryFind currMemVar with
                | None -> () (* TODO: is this possible? *)
                | Some (_, stmt) ->
                  match stmt with
                  | Phi (_, ids) ->
                    ids
                    |> Seq.map (fun id -> { currMemVar with Identifier = id })
                    |> Seq.filter (fun memVar -> not <| visited.Contains memVar.Identifier)
                    |> Seq.map (fun memVar -> TagVarPublic (pubAddr, memVar))
                    |> Seq.iter workingMemVars.Enqueue
                  | ExternalCall (e, inVars, outVars) ->
                    let [ inMemVar ] = inVars
                    if not <| visited.Contains inMemVar.Identifier then
                      workingMemVars.Enqueue (TagVarPublic (pubAddr, inMemVar))
                  | Def (_, e) -> () (* this cannot happen; Def-Store is only defined by stack store ops *)
                  | _ -> failwith "TODO: invalid stmt"
            (* from now on, no need to traverse the memories since we only have
               a single root memory
               TODO: is it safe? are there any different root memories? *)
            (* TODO: merge different regions in the same function since there can be multiple return spots in a single function*)
            returnMemoryRegions[pubAddr] <- returnMemoryRegion
            ()
          | _ ->
            (*TODO: is this possible?*)
            ()
          *)
        | _ -> ()

        (*
        match tag with
        | TagCalldataPtr ->
          match tags |> Seq.tryFind (fun tag -> match tag with TagArray _ -> true | _ -> false) with
          | Some (TagArray (elemVar, len)) ->
            let elemTy = fnGetTypeFromTagVar elemVar
            let locExpr = fnGetKExprFromTagVar var
            match locExpr with
            (*
            | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x4),
                                        KBinOp (_, BinOpType.APP, KFuncName "msg.data", args))
                when isBVEqualTo bv_0x4 0x4 ->
            *)
            | KBinOp (_, BinOpType.APP, KFuncName "msg.data", args) ->
              let args = KExpr.toList args
              let locInside = List.head args
              let pubAddr = fnGetPubAddrFromTagVar var
              let calldataRegion = fnGetCalldataRegion pubAddr
              match locInside with
              | KNum (_, bv) ->
                let addr = bv
                let addr = addr.BigValue ()
                calldataRegion[addr] <- TyArray (elemTy, len)
              (*TODO:or just simplify it to get a single constant *)
              | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x4), KNum (_, bv_offset))
              | KBinOp (_, BinOpType.ADD, KNum (_, bv_offset), KNum (_, bv_0x4))
                  when isBVEqualTo bv_0x4 0x4 ->
                let addr = BitVector.Add (bv_0x4, bv_offset)
                let addr = addr.BigValue ()
                calldataRegion[addr] <- TyArray (elemTy, len)
              | _ ->
                (*TODO*)
                ()
            | _ -> ()
            ()
          | _ -> ()
          ()
        | _ -> ()

        match tag with
        | TagCalldataLoad locVar ->
          (* check if this is a structural type *)
          if tags |> Seq.exists (fun tag -> match tag with TagCalldataPtr -> true | _ -> false) then
            ()
          elif not var.IsTagVarPublic then () (*FIXME*)
          else
            let pubAddr = fnGetPubAddrFromTagVar var
            let calldataRegion = fnGetCalldataRegion pubAddr
            match fnGetKExprFromTagVar locVar with
            (* [ loc ] *)
            | KNum (_, bv) ->
              let addr = bv
              let addr = addr.BigValue ()
              calldataRegion[addr] <- fnGetTypeFromTags tags
            (* [ 0x4 + off ] *)
            | KBinOp (_, BinOpType.ADD, KNum (_, bv_0x4), KNum (_, bv_offset))
            | KBinOp (_, BinOpType.ADD, KNum (_, bv_offset), KNum (_, bv_0x4))
                when isBVEqualTo bv_0x4 0x4UL ->
              let addr = BitVector.Add (bv_0x4, bv_offset)
              let addr = addr.BigValue ()
              calldataRegion[addr] <- fnGetTypeFromTags tags
            | _ -> ()
        | _ -> ()
        *)

    (*
      finalize type inference
    *)
    (* 1. pub func *)
    for pubAddr in solveInfo.PubFuncInfos.Keys do
      let calldataRegion = fnGetCalldataRegion pubAddr
      (* pub arg *)
      let args =
        calldataRegion
        |> Seq.sortBy (fun (KeyValue (addr, _)) -> addr)
        |> Seq.map (fun (KeyValue (_addr, ty)) -> ty.ToString ())
        |> Seq.toList
      (* pub ret *)
      let rets =
        match returnMemoryRegions.TryGetValue pubAddr with
        | false, _ -> []
        | true, returnMemoryRegion ->
          returnMemoryRegion
          |> Seq.sortBy (fun (KeyValue (off, _)) -> off)
          |> Seq.filter (fun (KeyValue (addr, _)) -> addr % 0x20 = 0)
          |> Seq.map (fun (KeyValue (_off, ty)) -> ty.ToString ())
          |> Seq.toList
      let info =
        { Addr = pubAddr
          Offset = 0UL
          Kind = "pub"
          Params = args
          Returns = rets }
      (finalFuncTypes: List<_>).Add info
    (* 2. priv func *)
    for (KeyValue (privAddr, infos)) in perPrivFunc do
      let args = List ()
      let rets = List ()
      (* 0, 32, 64,...에서 0: stack top *)
      for info in infos |> Seq.sortBy (fun (_, nth, _) -> nth) do
        let isParam, _nth, ty = info
        if isParam then args.Add <| ty.ToString ()
        else rets.Add <| ty.ToString ()
      let info =
        { Addr = privAddr
          Offset = 0UL
          Kind = "priv"
          Params = args |> Seq.toList
          Returns = rets |> Seq.toList }
      finalFuncTypes.Add info
    (* 3. stor *)
    for (KeyValue ((slot, off), ty)) in
      storageRegions
      |> Seq.filter (fun (KeyValue ((slot, bitmask), ty)) -> BitVector.isFitIntoUInt64 slot) do
      let info =
        { Addr = BitVector.ToUInt64 slot (* slot *)
          Offset = off (* off *)
          Kind = "stor"
          Params = [ ty.ToString () ]
          Returns = [] }
      finalFuncTypes.Add info

#if !TYPEDEBUG
    let showResult =
      false
#else
    let showResult =
      true
#endif

    if showResult then
      (* note that there can be duplication since this is a list! *)
      finalFuncTypes
      |> Seq.sortBy (fun info -> info.Addr, info.Offset)
      |> Seq.iter (fun info ->
        let addr = info.Addr
        let offset = info.Offset
        let kind = info.Kind
        let args = info.Params
        let rets = info.Returns
        if kind = "stor" then
          printfn "stor %d (%d): %A" addr offset args[0]
        else
          printfn "func %x (%s): %A -> %A" addr kind args rets)
      storageRegions
      |> Seq.sortBy (fun (KeyValue ((slot, off), _)) -> (slot.BigValue, off))
      |> Seq.iter (fun (KeyValue ((slot, off), ty)) ->
        printfn "slot %A (%A): %A" slot off <| ty.ToString ())
      (*
      solveInfo.PerVarTags.Keys
      |> Seq.iter (fun var ->
        fnGetTypeFromVar var|>ignore)
      *)

  let collectArgRetInfosFromPrivFunc (bld: ICFGBuildable<EVMFuncUserContext, _>)
                                     (m: Dictionary<_, _>) =
    let addr = bld.EntryPoint
    let noRetStatus = bld.Context.NonReturningStatus
    let isRet = noRetStatus.IsNotNoRet
    let returnOff =
      match noRetStatus with
      (* Opposite direction of the stack *)
      | NotNoRet -> - int bld.Context.UserContext.ReturnTargetStackOff
      | _ -> -0xdeadbeef
    let returnValueOff =
      match noRetStatus with
      | NotNoRet -> - int bld.Context.UserContext.StackPointerDiff.Value
      | _ -> -0xdeadbeef
    let reads = Dictionary ()
    let stores = Dictionary ()
    (* dfs *)
    let worklist = Stack ()
    let super = superCFGManager.GetSuperCFG addr
    dataFlowManager.RegisterCFG addr super
    let dfInfo = dataFlowManager.GetDataFlowInfo addr
    let ssa = dfInfo.SSACFG
    let root = ssa.SingleRoot
    let visited = HashSet ()
    worklist.Push root
    while worklist.Count > 0 do
      let v = worklist.Pop ()
      visited.Add v |> ignore
      let ssaStmts = v.VData.Internals.Statements
      let revSSAStmts = Array.rev ssaStmts
      for pp, stmt in revSSAStmts do
        match stmt with
        (* read *)
        | Def (_var, Var { Kind = StackVar (_, off); Identifier = 0 }) ->
          reads[off] <- pp, addr, off
        (* write *)
        | Def ({ Kind = StackVar (_, off); Identifier = _varId }, _e) ->
          stores[off] <- pp, addr, off
        | _ -> ()
      let succs = ssa.GetSuccs v
      for succ in succs do
        if not <| visited.Contains succ then
          worklist.Push succ
    (*
      args
    *)
    let addInfo pp info =
      let m'=
        match m.TryGetValue pp with
        | false, _ ->
          let lst = Dictionary ()
          m[pp] <- lst
          lst
        | true, lst -> lst
      let lst =
        match m'.TryGetValue addr with
        | false, _ ->
          let lst = List ()
          m'[addr] <- lst
          lst
        | true, lst -> lst
      lst.Add info
    reads
    |> Seq.filter (fun (KeyValue (off, (_, _, _off))) -> off <> returnOff)
    |> Seq.iter (fun (KeyValue (off, (pp, addr, _off))) ->
      addInfo pp (PrivArgInfo (pp, addr, off)))
    (*
      rets when exist
    *)
    if isRet then
      let finalOff = returnValueOff
      stores
      |> Seq.filter (fun (KeyValue (off, (_, _, _))) ->
        (* lastOff <= off <= jumpOff *)
        (* opposite direction *)
        off <= finalOff && off >= returnOff)
      |> Seq.iter (fun (KeyValue (off, (pp, addr, _))) ->
        addInfo pp (PrivRetInfo (pp, addr, off)))

  let collectArgRetInfosFromPrivFuncs privAddrs =
    /// pp to info
    let m = Dictionary ()
    for privAddr in privAddrs do
      let bld = brew.Builders[privAddr]
      // let isRet = fn.ReturnProperty <> ReturnProperty.NoRet
      let usrCtx = bld.Context.UserContext
      if usrCtx.IsSharedRegion || usrCtx.IsPublicFunction then ()
      else
        collectArgRetInfosFromPrivFunc bld m
        //collectArgRetInfosFromPrivFuncWithIRCFG privAddr isRet fn m
    m

  let collectTagsFromPublicFunctions privArgRetInfos
                                     (perVarTags: Dictionary<_, _>)
                                     (perPubFuncDataFlows: Dictionary<_, _>)
                                     (varDisjointSet: DisjointSet<_>)
                                     privAddrs
                                     pubAddrs =
    let useParallel = false
    let mutable extractTime = 0L
    if useParallel then
      (*
      let fnCalcSSA pubAddr =
        let entryPointV = DiGraph.FindVertexBy (rootGraph, fun v -> v.VData.PPoint.Address = pubAddr)
        let g = cutGraphFrom rootGraph entryPointV
        let ssa, root = SSAFactory.translateToSSACFG cfgRec.BinHandle g pubAddr
        let scp = SparseConstantPropagation (cfgRec.BinHandle, ssa)
        let cpState = scp.Compute root
        pubAddr, ssa, root, cpState
      let fn pubAddr ssa root cpState =
  #if TYPEDEBUG
        if pubAddr = 0x153UL then
          printfn "."
          ()
  #endif
        Extract.extractTagsFromPub cfgRec.BinHandle cfgRec privArgRetInfos ssa pubAddr cpState perVarTags
        let ret =
          { Addr = pubAddr
            SSA = ssa
            Root = root
            CPState = cpState
            RootMemMemo = Dictionary () }
        perPubFuncDataFlows[pubAddr] <- ret
      let sw = System.Diagnostics.Stopwatch.StartNew ()

      let subTasksCalcSSA =
        pubAddrs
        |> Seq.map (fun pubAddr -> Task.Factory.StartNew (fun _ -> fnCalcSSA pubAddr))
      Task.WhenAll subTasksCalcSSA |> fun t -> t.Wait ()

      for task in subTasksCalcSSA do
        let pubAddr, ssa, root, cpState = task.Result
        fn pubAddr ssa root cpState

      sw.Stop ()
      print "[+] worker threads done in collecting tags: %d ms" sw.ElapsedMilliseconds
      (*
      let fnGetSSA pubAddr =
        let entryPointV = DiGraph.FindVertexBy (rootGraph, fun v -> v.VData.PPoint.Address = pubAddr)
        let g = cutGraphFrom rootGraph entryPointV
        let ssa, root = SSAFactory.translateToSSACFG cfgRec.BinHandle g pubAddr
        let scp = SparseConstantPropagation (cfgRec.BinHandle, ssa)
        let cpState = scp.Compute root
        pubAddr, ssa, root, cpState
      let ssaTasks = pubAddrs |> Seq.map (fun pubAddr -> Task.Factory.StartNew (fun _ -> fnGetSSA pubAddr))
      let mainTask = Task.WhenAll ssaTasks
      mainTask.Wait ()
      for task in ssaTasks do
        let pubAddr, ssa, root, cpState = task.Result
        extractTagsFromPub cfgRec.BinHandle privArgRetInfos ssa pubAddr cpState solveInfo.PerVarTags
        let pubFuncDataFlow =
          { Addr = pubAddr
            SSA = ssa
            Root = root
            CPState = cpState
            RootMemMemo = Dictionary () }
        perPubFuncDataFlows[pubAddr] <- pubFuncDataFlow
      *)
      *)
      Terminator.impossible ()
    else
      (* previous single-threaded version*)
      pubAddrs
      (* for testing *)
  #if TYPEDEBUG
      |> Seq.filter (fun pubAddr -> match filterAddr with | None -> true | Some filterAddr -> pubAddr = filterAddr)//pubAddr = 0x3f5UL)//pubAddr = 0x5cbUL)
  #endif
      |> Seq.iter (fun pubAddr ->
        let sw = System.Diagnostics.Stopwatch.StartNew ()
        let super = superCFGManager.GetSuperCFG pubAddr
        dataFlowManager.RegisterCFG pubAddr super
        let funcInfo = dataFlowManager.GetDataFlowInfo pubAddr
        Extract.extractTagsFromPub brew privAddrs funcInfo privArgRetInfos
                                   perVarTags varDisjointSet
        extractTime <- extractTime + sw.ElapsedMilliseconds
        perPubFuncDataFlows[pubAddr] <- funcInfo
        ())
#if DEBUG
    printfn "[+] extract tags from public functions: %d ms" extractTime
#endif

  let extractConstraints () =
    (*
    let fnOnStmt stmt =
      match stmt with
      |
      | _ -> ()
    ()
    *)
    failwith "TODO"

  /// Main function of type recovery
  let run priv pub fallbackAddr =
    let privAddrs, pubAddrs = priv, pub
    let funcTypes = List ()
#if DEBUG
    printfn "[+] collect priv arg and ret infos..."
    let sw = System.Diagnostics.Stopwatch.StartNew ()
#endif
    let privArgRetInfos = collectArgRetInfosFromPrivFuncs privAddrs
#if DEBUG
    printfn "[+] collect priv arg and ret infos done: %d ms" sw.ElapsedMilliseconds
#endif
    let perPubFuncDataFlows = Dictionary ()
    let perVarTags = Dictionary ()
    (* TODO *)
    (*
    let pubAddrs = (* add fallback addr to the pub func addr list only for
                      extracting hints *)
      match fallbackAddr with
      | None -> pubAddrs
      | Some fallbackAddr ->
        Seq.append pubAddrs [ fallbackAddr ]
    *)
    // 1. collect tags from public functions
    (* TODO: collect tags in parallel!!! *)
    let sw = System.Diagnostics.Stopwatch.StartNew ()
    let pubAddrs = pubAddrs
      (*
      if Seq.isEmpty pubAddrs then
        Seq.append pubAddrs [ 0x0UL ] (* 0x05b98e50bf2e6a2ed42ca5e9913175ef778a93ed *)
      else
        pubAddrs
      *)
    let varDisjointSet = DisjointSet ()
#if DEBUG
    printfn "[+] collect tags from public functions..."
#endif
    collectTagsFromPublicFunctions privArgRetInfos perVarTags
                                   perPubFuncDataFlows varDisjointSet privAddrs
                                   pubAddrs
    sw.Stop ()
#if DEBUG
    printfn "[+] collect tags done: %d ms" sw.ElapsedMilliseconds
#endif
    // 2. solve
#if DEBUG
    printfn "[+] collect tags from public functions..."
#endif
    let sw = System.Diagnostics.Stopwatch.StartNew ()
    let solveInfo = SolveInfo (perVarTags, varDisjointSet, perPubFuncDataFlows)
    Solve.solveConstraints solveInfo
    sw.Stop ()
#if DEBUG
    printfn "[+] solve done: %d ms" sw.ElapsedMilliseconds
#endif
    // 3. infer high-level types
    let sw = System.Diagnostics.Stopwatch.StartNew ()
    inferTypes solveInfo privArgRetInfos funcTypes
    sw.Stop ()
#if DEBUG
    printfn "[+] infer done: %d ms" sw.ElapsedMilliseconds
#endif
    // Finalize
    // FIXME
    match fallbackAddr with
    | None ->
      funcTypes
      |> Seq.toList
    | Some fallbackAddr ->
      funcTypes
      |> Seq.filter (fun funcType -> funcType.Addr <> fallbackAddr)
      |> Seq.toList

  member __.Run priv pub fallbackAddr =
    run priv pub fallbackAddr

