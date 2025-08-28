namespace EVMpress.Type

open System
open System.Collections.Generic
open System.Collections.Concurrent
open System.Threading.Tasks.Dataflow
open B2R2
open B2R2.FrontEnd
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.SSA
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies
open B2R2.MiddleEnd.DataFlow
open B2R2.BinIR
open B2R2.BinIR.SSA
open B2R2.MiddleEnd.ControlFlowAnalysis

/// TODO: Just use SSAEdges directly.
type FakeCPState = {
  SSAEdges: SSAEdges
}

[<AutoOpen>]
module private DataFlowManagerLogics =
  let addInOutMemVars inVars outVars =
    let inVar = { Kind = MemVar; Identifier = -1 }
    let outVar = { Kind = MemVar; Identifier = -1 }
    inVar :: inVars, outVar :: outVars

type DataFlowManager (hdl: BinHandle) =
  let usesMulticore = false

  let cache = Dictionary ()

  let stream = BufferBlock ()

  let evmStmtProcessor =
    { new IStmtPostProcessor with
        member _.WordSize with get () = WordSize.Bit256
        member _.PostProcess stmt =
          match stmt with
          | Def (outMemVar, Store (inMemVar, rt1, addr,
                                   BinOp (BinOpType.APP, rt2, FuncName fname,
                                          ExprList args)))
            when fname = "mload"
              || fname = "keccak256" ->
            let dstExpr =
              let inMemVar = { Kind = MemVar; Identifier = -1 }
              let inMem = Var inMemVar
              (* We add an incoming memory flow for these stmts. Note that
                 the current lifting logic does not support having incoming
                 memory flows for returning APP expressions. *)
              let newArgs = inMem :: args
              let argsWithInMem = ExprList newArgs
              BinOp (BinOpType.APP, rt2, FuncName fname, argsWithInMem)
            Def (outMemVar, Store (inMemVar, rt1, addr, dstExpr))
          (* add an incoming memory flow for external call stmts *)
          | ExternalCall ((BinOp (BinOpType.APP, _, FuncName fname, _)) as e,
                          _, _)
            when fname = "calldatacopy"
              || fname = "mstore"
              || fname = "mstore8"
              || fname = "return"
              || fname = "sstore" ->
            let inVars, outVars = addInOutMemVars [] []
            ExternalCall (e, inVars, outVars)
          | stmt -> stmt }

  let ssaFactory = SSALifterFactory.Create (hdl, evmStmtProcessor)

  let fn g ep =
    let ssa = ssaFactory.Lift g
    // let cp = SSAConstantPropagation hdl
    // let cpState = (cp :> IDataFlowComputable<_, _, _, _>).Compute ssa
    let ssaEdges = SSAEdges(ssa)
    let cpState = { SSAEdges = ssaEdges }
    let info =
      { EntryPoint = ep
        OriginalCFG = g
        CPState = cpState
        SSACFG = ssa
        KExprMemo = Dictionary ()
        RootMemMemo = Dictionary () }
    cache[ep] <- info
    // printfn "Data flow info for %x registered." ep

  /// We compute data-flow information while expanding other CFGs into inter-
  /// procedural CFGs.
  let makeWorker () = task {
    while true do
      let! (ep, g) = stream.ReceiveAsync ()
      fn g ep
    }

  let workerNums =
    Environment.ProcessorCount / 2
    |> max 1

  let _workers =
    if not usesMulticore then Array.empty
    else Array.init workerNums (fun _ -> makeWorker ())

  /// Compute a SSA graph of the given CFG, and its data-flow information.
  member _.RegisterCFG addr g =
    assert (not <| cache.ContainsKey addr)
    if usesMulticore then
      stream.Post (addr, g) |> ignore
    else
      fn g addr

  member this.GetDataFlowInfo addr =
#if DEBUG
    // printfn "[+] Waiting for %x" addr
#endif
    if not <| cache.ContainsKey addr then
      failwith ""
      // fn g addr
      this.GetDataFlowInfo addr
      // cache[addr]
      // this.GetDataFlowInfo addr (* Busy-waiting *)
    else
      cache[addr]

  member this.GetDataFlowInfo(g, addr) =
#if DEBUG
    // printfn "[+] Waiting for %x" addr
#endif
    if not <| cache.ContainsKey addr then
      fn g addr
      cache[addr]
      // this.GetDataFlowInfo addr (* Busy-waiting *)
    else
      cache[addr]

/// TODO: Comment.
and PerFuncDataFlowInfo = {
  EntryPoint: Addr
  OriginalCFG: IDiGraph<LowUIRBasicBlock, CFGEdgeKind>
  SSACFG: IDiGraph<SSABasicBlock, CFGEdgeKind>
  // CP: SSAConstantPropagation
  // CPState: SSASparseDataFlow.State<ConstantDomain.Lattice>
  CPState: FakeCPState
  KExprMemo: Dictionary<SSA.Variable, KExpr>
  /// TODO: Comment.
  RootMemMemo: Dictionary<int, SSA.Variable option>
}

/// TODO: Move this into a proper place.
and KExpr =
  | KVar of SSA.Variable
  | KNum of SSA.Variable option * BitVector
  | KBinOp of SSA.Variable option * BinOpType * KExpr * KExpr
  | KRelOp of SSA.Variable option * RelOpType * KExpr * KExpr
  | KUnOp of SSA.Variable option * UnOpType * KExpr
  | KCast of SSA.Variable option * CastKind * KExpr
  | KLoad of SSA.Variable option * memVar: SSA.Variable * addr: KExpr
  | KStore of SSA.Variable option * memVar: SSA.Variable * addr: KExpr * value: KExpr
  | KExtract of SSA.Variable option * KExpr
  | KIte of SSA.Variable option * KExpr * KExpr * KExpr
  | KFuncName of string
  | KExprList of SSA.Variable option * KExpr list
  | KUndefined of SSA.Variable option * string
  | KNil
