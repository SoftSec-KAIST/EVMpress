namespace EVMpress.Type

open System.Collections.Generic
open B2R2
open B2R2.BinIR
open B2R2.FrontEnd
open B2R2.FrontEnd.EVM
open B2R2.MiddleEnd
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies
open B2R2.MiddleEnd.DataFlow
open B2R2.MiddleEnd.DataFlow.LowUIRSensitiveDataFlow
open B2R2.MiddleEnd.SSA
open B2R2.BinIR.SSA

[<AutoOpen>]
module private SuperCFGManagerLogics =
  type AbnormalVertexType =
    | AbnormalReturning
    | AbnormalAbstract

  let makeStopBBL (lunit: LiftingUnit) (parser: EVMParser) =
    let ins = parser.Parse(EVM.STOP, 0, 1ul, 0xdeadbeefUL, 0xdeadbeefUL)
    let stmts = lunit.LiftInstruction (ins = ins, optimize = true)
    let liftedIns =
      { Original = ins
        Stmts = stmts
        BBLAddr = 0xdeadbeefUL }
    let liftedInss = [| liftedIns |]
    let pp = ProgramPoint.GetFake ()
    let data = LowUIRBasicBlock.CreateRegular (liftedInss, pp)
    data

  /// Filters out exits that have improper stack unwinding. Note that the given
  /// super CFG is different from its original CFG, as it has been modified.
  let handleImproperExits (ctx: CFGBuildingContext<EVMFuncUserContext, _>)
                          (super: IDiGraph<_, _>) =
    ()

  let copyGraphTo (src: IDiGraph<_, _>) (dst: IDiGraph<_, _>) =
    let vertices = src.Vertices
    let mapping = Dictionary ()
    let root = src.SingleRoot
    let exits = src.Exits
    for v in vertices do
      let vInDst, _ = dst.AddVertex(v.VData)
      mapping[v] <- vInDst
    let rootInDst = mapping[root]
    let exitsInDst = exits |> Array.map (fun e -> mapping[e])
    let edges = src.Edges
    for e in edges do
      let srcInDst = mapping[e.First]
      let dstInDst = mapping[e.Second]
      dst.AddEdge(srcInDst, dstInDst, e.Label) |> ignore
    rootInDst, exitsInDst

  /// Collects return nodes from the given exit vertices of a super CFG.
  /// Note that they are not abstract vertices, as they are in a super CFG.
  let collectReturnNodes (exits: IVertex<LowUIRBasicBlock>[]) =
    assert (exits |> Array.forall (fun v -> not v.VData.Internals.IsAbstract))
    exits
    |> Array.filter (fun v ->
      let lastIns = v.VData.Internals.LastInstruction
      if lastIns.IsExit then false (* Filter out transaction terminators. *)
      elif lastIns.IsBranch then true
      else Terminator.impossible ())

  let hasNoAbsVertex (g: IDiGraph<LowUIRBasicBlock, _>) =
    g.Vertices
    |> Array.forall (fun v -> not v.VData.Internals.IsAbstract)

type SuperCFGManager (brew: BinaryBrew<EVMFuncUserContext, DummyContext>,
                      dfm: DataFlowManager,
                      exclusions: Addr list) =
  let hdl = brew.BinHandle
  let lunit = hdl.NewLiftingUnit ()
  let parser = EVMParser(ISA Architecture.EVM)
  let builders = brew.Builders
  let exclusions = Set.ofList exclusions
  let candidates =
    builders.Values
    |> Array.filter (fun b -> not <| Set.contains b.EntryPoint exclusions)
  let superCFGCache = Dictionary ()

  let selectivelyTransplant (ctx: CFGBuildingContext<EVMFuncUserContext, _>)
                            (super: IDiGraph<LowUIRBasicBlock, _>)
                            (abnormals: (IVertex<_> * AbnormalVertexType) seq) =
    let abnormalMap = Map.ofSeq abnormals
    let g = ctx.CFG
    let usrCtx = ctx.UserContext
    let cp = usrCtx.CP
    let state = cp.State
    let root = g.SingleRoot
    let worklist = Stack [ root ]
    let visited = HashSet ()
    let superVertices = Dictionary ()
    let superVirtualVertices = Dictionary ()
    let getVertexInSuper (v: IVertex<LowUIRBasicBlock>) stackOffset =
      let key = v, stackOffset
      match superVertices.TryGetValue key with
      | true, vInSuper -> vInSuper
      | false, _ ->
        let data =
          match abnormalMap.TryFind v with
          | Some AbnormalAbstract -> makeStopBBL lunit parser
          | _ -> v.VData
        let vInSuper, _ = super.AddVertex(data)
        superVertices[key] <- vInSuper
        vInSuper
    let getVirtualTerminatorVertexInSuper v stackOffset =
      let key = v, stackOffset
      match superVirtualVertices.TryGetValue key with
      | true, virtualVInSuper -> virtualVInSuper
      | false, _ ->
        let data = makeStopBBL lunit parser
        let virtualVInSuper, _ = super.AddVertex(data)
        superVirtualVertices[key] <- virtualVInSuper
        virtualVInSuper
    while worklist.Count > 0 do
      let v = worklist.Pop()
      visited.Add v |> ignore
      let exeCtxs = state.PerVertexPossibleExeCtxs[v]
      let perStackOffsetExeCtxs =
        exeCtxs
        |> Seq.groupBy (fun exeCtx -> exeCtx.StackOffset)
        |> Seq.toList
      let doesBranch =
        if v.VData.Internals.IsAbstract then
          v.VData.Internals.AbstractContent.ReturningStatus = NotNoRet
        else
          v.VData.Internals.LastInstruction.IsBranch
      for stackOffset, _exeCtxs in perStackOffsetExeCtxs do
        let succEdges = g.GetSuccEdges v
        match abnormalMap.TryFind v with
        | _ when Array.isEmpty succEdges && doesBranch -> (* Return node. *)
          let returnStackOffset =
            match usrCtx.StackPointerDiff with
            | None -> 0UL
            | Some diff -> diff
          let stackPointerDelta = usrCtx.GetStackPointerDelta(state, v)
          let lastStackOffset = stackOffset + stackPointerDelta
          let vInSuper = getVertexInSuper v stackOffset
          if int returnStackOffset = lastStackOffset then ()
          else
            let virtualVInSuper = getVirtualTerminatorVertexInSuper v stackOffset
            super.AddEdge(vInSuper, virtualVInSuper, CFGEdgeKind.UnknownEdge)
            |> ignore
        | Some AbnormalReturning when false -> (* FIXME *)
          assert Array.isEmpty succEdges
          (* Connect this to a virtual node that contains a terminator only. *)
          let vInSuper = getVertexInSuper v stackOffset
          let virtualVInSuper = getVirtualTerminatorVertexInSuper v stackOffset
          super.AddEdge(vInSuper, virtualVInSuper, CFGEdgeKind.UnknownEdge)
          |> ignore
        | _ ->
          let stackOffsetDelta = usrCtx.GetStackPointerDelta(state, v)
          let succStackOffset = stackOffset + stackOffsetDelta
          let possibleSuccEdges =
            succEdges
            |> Array.filter (fun e ->
              let succ = e.Second
              match state.PerVertexPossibleExeCtxs.TryGetValue succ with
              | true, exeCtxs ->
                exeCtxs
                |> Seq.exists (fun tag -> tag.StackOffset = succStackOffset)
              (* TODO: More safe way? *)
              | false, _ -> false)
          let vInSuper = getVertexInSuper v stackOffset
          if Array.isEmpty possibleSuccEdges
             && not <| Array.isEmpty succEdges then
            (* 0x000000000000631c681c13c8285ed5a3bc5a754a:
               20ca -> [1ff0] -> 2020; back edge not executed due to explosion
               prevention. *)
            let vInSuper = getVertexInSuper v stackOffset
            let virtualVInSuper = getVirtualTerminatorVertexInSuper v stackOffset
            super.AddEdge(vInSuper, virtualVInSuper, CFGEdgeKind.UnknownEdge)
            |> ignore
          else
          for e in possibleSuccEdges do
            let succ = e.Second
            let edgeKind = e.Label
            let succInSuper = getVertexInSuper succ succStackOffset
            super.AddEdge(vInSuper, succInSuper, edgeKind) |> ignore
            if not <| visited.Contains succ then
              worklist.Push succ

  let collectAbnormalVertices (ctx: CFGBuildingContext<EVMFuncUserContext, _>) =
    let abnormalExits = List ()
    let entryPoint = ctx.FunctionAddress
    let stackPointerDiff = ctx.UserContext.StackPointerDiff
    let state = ctx.UserContext.CP.State
    let g = ctx.CFG
    let returns =
      g.Exits
      |> Array.filter (fun v ->
        if not v.VData.Internals.IsAbstract then
          let lastIns = v.VData.Internals.LastInstruction
          if lastIns.IsExit then false
          else true
        else
          let calleeAddr = v.VData.Internals.PPoint.Address
          let calleeBuilder = builders[calleeAddr]
          let calleeCtx = calleeBuilder.Context
          match v.VData.Internals.AbstractContent.ReturningStatus with
          | NotNoRet -> true
          | NoRet when calleeCtx.NonReturningStatus = NotNoRet -> (* Changed *)
            if v.VData.Internals.PPoint.Address = entryPoint then
              abnormalExits.Add (v, AbnormalAbstract)
              false
            else
              Terminator.impossible ()
          | NoRet -> false
          | _ -> Terminator.impossible ())
    for returnVertex in returns do
      if not <| state.PerVertexPossibleExeCtxs.ContainsKey returnVertex then
        abnormalExits.Add (returnVertex, AbnormalReturning)
      else
        for exeCtx in state.PerVertexPossibleExeCtxs[returnVertex] do
          let stackInfo = state.PerVertexStackPointerInfos[returnVertex, exeCtx]
          let _, outStackPointer = stackInfo
          match outStackPointer with
          | StackPointerDomain.ConstSP vertexOutSP ->
            let outSP = BitVector.ToUInt64 vertexOutSP
            let vertexStackOffset = outSP - Constants.InitialStackPointer
            match stackPointerDiff with
            | None -> (* It is a no-ret func, but some abnormal nodes exist. *)
              abnormalExits.Add (returnVertex, AbnormalReturning)
            | Some diff ->
              if vertexStackOffset <> diff then
  #if DEBUG
                printfn "[-] Stack pointer: %A <> %A" vertexStackOffset diff
  #endif
                abnormalExits.Add (returnVertex, AbnormalReturning)
          | _ -> Terminator.impossible ()
    abnormalExits


  let rec traverse (visited: HashSet<_>) (super: IDiGraph<_, _>) vs =
    match vs with
    | [] -> ()
    | v :: vs ->
      let succs = super.GetSuccs v
      let vs = succs |> Array.fold (fun acc succ ->
        if visited.Add succ then succ :: acc
        else acc) vs
      traverse visited super vs

  /// Removes unreachable vertices from the root node. Unreachable vertices can
  /// be caused by removal of nodes due to mutual recursive calls.
  let rec removeUnreachables (super: IDiGraph<LowUIRBasicBlock, _>) =
    let visited = HashSet ()
    let root = super.SingleRoot
    visited.Add root |> ignore
    traverse visited super [ root ]
    for v in super.Vertices do
      if not <| visited.Contains v then
        super.RemoveVertex v |> ignore

  /// Computes the super CFG for the given builder. We take a strategy of
  /// minimizing the number of contexts by merging similar contexts and
  /// removing unnecessary contexts.
  /// TODO: Check stack pointer inconsistency.
  let rec computeSuperCFG visited
                          (ctx: CFGBuildingContext<EVMFuncUserContext, _>) =
    let visited = Set.add ctx.FunctionAddress visited
#if DEBUG
    printfn "%x" ctx.FunctionAddress
    if ctx.FunctionAddress = 0x5e45UL then ()
#endif
    let super = LowUIRCFG Imperative
    let usrCtx = ctx.UserContext
    let cp = usrCtx.CP
    (cp :> IDataFlowComputable<_, _, _, _>).Compute ctx.CFG |> ignore
    let abnormals = collectAbnormalVertices ctx
    selectivelyTransplant ctx super abnormals
    handleImproperExits ctx super
    expandCallNodes ctx super visited
    removeUnreachables super
    super

  and expandCallNodes ctx (super: IDiGraph<LowUIRBasicBlock, _>) visited =
    let vertices = super.Vertices
    let absVertices =
      vertices |> Array.filter (fun v -> v.VData.Internals.IsAbstract)
    for absV in absVertices do
      let calleeAddr = absV.VData.Internals.AbstractContent.EntryPoint
      assert (calleeAddr <> ctx.FunctionAddress)
      let predsOfAbsV = super.GetPreds absV
      let succsOfAbsV = super.GetSuccs absV
      let calleeBuilder = builders[calleeAddr]
      if Set.contains calleeAddr visited then
        super.RemoveVertex absV |> ignore
        let bbl = makeStopBBL lunit parser
        let newVertex, _ = super.AddVertex(bbl)
        for pred in predsOfAbsV do
          super.AddEdge(pred, newVertex, CFGEdgeKind.UnknownEdge) |> ignore
      else
        let superCallee = getSuperCFG visited calleeBuilder
        (* 1. Collect information before removing the abstract vertex. *)
        (* 2. Remove it *)
        super.RemoveVertex absV |> ignore
        (* 3. Add the callee's vertices and edges. *)
        let calleeEntryNode, calleeExitNodes = copyGraphTo superCallee super
        (* 4. Connect edges -- from (callee) exits to successors *)
        let calleeExitNodes = collectReturnNodes calleeExitNodes
        let calleeCtx = calleeBuilder.Context
        let calleeUsrCtx = calleeCtx.UserContext
        if Option.isNone calleeUsrCtx.StackPointerDiff then () (* No return. *)
        elif Array.isEmpty succsOfAbsV then () (* Optimized code. *)
        else
          assert (calleeCtx.NonReturningStatus.IsNotNoRet)
          let succ = succsOfAbsV |> Array.exactlyOne
          if calleeExitNodes.Length = 0 then
            (* It was originally a returning function, but for some reason (e.g.
               vertex filtering due to recursive call) it became a non-returning
               function, so we do not connect to the successor. *)
            ()
          else
          for calleeExitNode in calleeExitNodes do
            super.AddEdge(calleeExitNode, succ, CFGEdgeKind.RetEdge) |> ignore
        (* 5. Connect edges -- from predecessors to (callee) entry node *)
        for pred in predsOfAbsV do
          super.AddEdge(pred, calleeEntryNode, CFGEdgeKind.CallEdge) |> ignore
    assert hasNoAbsVertex super

  and getSuperCFG visited b =
    let addr = (b: ICFGBuildable<_, _>).EntryPoint
    match superCFGCache.TryGetValue addr with
    | true, g -> g
    | false, _ ->
      let g = computeSuperCFG visited b.Context
      if addr <> 0UL then
        dfm.RegisterCFG addr g
      superCFGCache[addr] <- g
      g

  let analyze () =
    for builder in candidates do
      getSuperCFG Set.empty builder |> ignore

  do analyze ()

  member _.X = ()

  member _.GetSuperCFG addr =
    match superCFGCache.TryGetValue addr with
    | true, g -> g
    | false, _ -> failwith ""

