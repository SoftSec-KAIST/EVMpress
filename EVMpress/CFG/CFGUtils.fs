[<AutoOpen>]
module EVMpress.CFG.CFGUtils

open System
open System.Collections.Generic
open B2R2
open B2R2.BinIR
open B2R2.FrontEnd
open B2R2.FrontEnd.BinLifter
open B2R2.MiddleEnd
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.DataFlow
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowGraph

/// Given a path to a bytecode file, this function parses the bytecode
let parseBytecode strategy (path: string) =
  let isa = ISA Architecture.EVM
  let hdl = BinHandle (path, isa)
  let strategies = [| strategy |]
  let brew = EVMBinaryBrew (hdl, strategies)
  brew

let private getCoveredRanges (builders: ICFGBuildable<_, _>[]) =
  let ranges = SortedList ()
  builders
  |> Array.iter (fun bld ->
    let ctx = bld.Context
    let g = ctx.CFG
    g.IterVertex (fun v ->
      if v.VData.Internals.IsAbstract then ()
      else
        let vData = v.VData.Internals
        let s, e = vData.Range.Min, vData.Range.Max
        let pair = (s, e)
        (* Handle when the same key exists (e.g. due to split of a block) *)
        if ranges.ContainsKey s then
          let (_prevS, prevE)= ranges[s]
          if prevE >= e then ()
          else ranges[s] <- pair
        else ranges.Add (s, pair)))
  let mutable i = 0
  while i < ranges.Count - 2 do
    let (s1, e1), (s2, e2) =
      ranges.GetValueAtIndex i, ranges.GetValueAtIndex (i + 1)
    if s2 <= e1 + 1UL then
      ranges.RemoveAt i
      ranges.RemoveAt i
      let newRange = (s1, max e1 e2)
      ranges.Add (s1, newRange)
      i <- 0
    else
      i <- i + 1
  ranges

let private getUncoveredRanges (hdl: BinHandle) builders =
  let ranges = getCoveredRanges builders
  let uncoveredRanges = SortedList ()
  let bytecodeLength = hdl.File.RawBytes.Length |> uint64
  (* calculate uncovered ranges *)
  let mutable i = 0
  while i < ranges.Count - 2 do
    let (s1, e1), (s2, e2) =
      ranges.GetValueAtIndex i, ranges.GetValueAtIndex (i + 1)
    if e1 + 1UL <> s2 then
      let s = e1 + 1UL
      let e = s2 - 1UL
      let range = s, e
      uncoveredRanges.Add (s, range)
    i <- i + 1
  match ranges.Values |> Seq.tryLast with
  | Some (_, e) when e <> bytecodeLength - 1UL ->
    let s = e + 1UL
    let e = bytecodeLength - 1UL
    let range = s, e
    uncoveredRanges.Add (s, range)
  | _ -> ()
  uncoveredRanges

let private OpcodeJUMPDEST = 0x5buy (* JUMPDEST opcode *)

/// Finds the least upper bound key in a sorted list for a given key.
/// Returns None if no such key exists.
let private findLeastUpperBoundKey key (sortedList: SortedList<_, _>) =
  let mutable low = 0
  let mutable high = sortedList.Count - 1
  let mutable ret = None
  while low <= high do
    let mid = (low + high) / 2
    let midKey = sortedList.Keys[mid]
    if midKey < key then
      low <- mid + 1
    else
      ret <- Some midKey
      high <- mid - 1
  ret

let isUnlikelyValidEntryPoint (inss: IInstruction list) =
  let inss = inss |> List.toArray
  (* JUMPDEST; JUMPDEST *)
  if inss.Length >= 2 && inss[0].IsNop && inss[1].IsNop then true
  (* JUMPDEST; JUMP *)
  elif inss.Length >= 2 && inss[0].IsNop && inss[1].IsBranch then true
  (* JUMPDEST; STOP *)
  elif inss.Length >= 2 && inss[0].IsNop && inss[1].IsExit then true
  else false

let tryParseSingleBBL (bblFactory: BBLFactory) addr =
  bblFactory.PeekBBL addr

let getCallbackOnPostProcessing () =
  let mutable currMinAddr = 0UL
  let rec callbackOnPostProcessing (builders: ICFGBuildable<_, _>[]) =
    (* TODO: Optimize. *)
    let anyBuilder = builders |> Array.head
    let anyContext = anyBuilder.Context
    let hdl = anyContext.BinHandle
    let bblFactory = anyContext.BBLFactory
    let ranges = getUncoveredRanges hdl builders
    match findLeastUpperBoundKey currMinAddr ranges with
    | None -> [||]
    | Some minAddr ->
      let b = hdl.File.RawBytes[int minAddr]
      if b <> OpcodeJUMPDEST then [||] (* maybe end of code? *)
      else
        (* Parse a single BBL, and decide if it is a valid entry point of a
           function. *)
        match tryParseSingleBBL bblFactory minAddr with
        | Error _e -> [||]
        | Ok bbl when isUnlikelyValidEntryPoint bbl -> (* Skip this BBL. *)
          let lastIns = bbl |> List.last
          let nextAddr = lastIns.Address + uint64 lastIns.Length
          currMinAddr <- nextAddr
          callbackOnPostProcessing builders
        | Ok _bbl ->
          let nextAddr = minAddr + 1UL
          currMinAddr <- nextAddr
          [| minAddr |]
  callbackOnPostProcessing

let hasVertexInstruction (v: IVertex<LowUIRBasicBlock>) insName =
  let disasms = v.VData.Internals.Disassemblies
  disasms |> Array.exists (fun d -> d = insName)

let hasVertexCallvalueCheck v =
  hasVertexInstruction v "callvalue"

let predictGeneration (publicBuilders: ICFGBuildable<_, _>[]) =
  publicBuilders
  |> Array.exists (fun publicBuilder ->
    let context = publicBuilder.Context
    let entryNodeAddr = context.FunctionAddress
    let entryNodePP = ProgramPoint (entryNodeAddr, 0)
    let entryNode = context.Vertices[entryNodePP]
    let targets =
      if entryNode.VData.Internals.Disassemblies.Length = 3 &&
         entryNode.VData.Internals.Disassemblies[0] = "jumpdest" &&
         entryNode.VData.Internals.Disassemblies[1].StartsWith "push" &&
         entryNode.VData.Internals.Disassemblies[2] = "jump" then (* via-IR *)
        let succs = context.CFG.GetSuccs entryNode
        Array.append succs [| entryNode |]
      else
        [| entryNode |]
    targets |> Array.exists hasVertexCallvalueCheck)

let rec findAnyCallPath g root =
  let dfp = Dominance.CytronDominanceFrontier ()
  let dom = Dominance.LengauerTarjanDominance.create g dfp
  let exits =
    let exitNodes = g.Exits
    if Array.isEmpty exitNodes then [||]
    else
      exitNodes
      |> Array.filter (fun (v: IVertex<LowUIRBasicBlock>) ->
        v.VData.Internals.Disassemblies
        |> Array.tryLast
        |> function
          | None -> false
          | Some d -> d = "stop" || d = "return")
  if Array.isEmpty exits then []
  else
    exits
    |> Array.map (fun exit ->
        let mutable path = []
        let mutable v = exit
        while v <> root && v <> null do
          if v.VData.Internals.IsAbstract then
            path <- v :: path
          v <- dom.ImmediateDominator v
        path)
    |> Array.sortByDescending (fun p -> p.Length)
    |> Array.head

let pruneUnreachableNodes (g: IDiGraph<LowUIRBasicBlock, _>) =
  let reachable = HashSet ()
  let root = g.SingleRoot
  let rec dfs vs =
    match vs with
    | [] -> ()
    | v :: vs ->
      reachable.Add v |> ignore
      let succs = g.GetSuccs v
      let succsToVisit =
        succs
        |> Seq.filter (fun s -> not <| reachable.Contains s)
        |> Seq.toList
      dfs <| vs @ succsToVisit
  dfs [ root ]
  for v in g.Vertices do
    if not <| reachable.Contains v then
      g.RemoveVertex v |> ignore

///
let collectPublicFunctionBodies (brew: BinaryBrew<EVMFuncUserContext, _>) =
  for bld in brew.Builders.Values do
    let g = bld.Context.CFG
    pruneUnreachableNodes g
  let bodyAddrs = HashSet ()
  let builders = brew.Builders.Values
  let mainBuilder =
    builders |> Array.find (fun b -> b.Context.FunctionAddress = 0x0UL)
  let publicBuilders =
    builders |> Array.filter (fun b -> b.Context.UserContext.IsPublicFunction)
  if Array.length publicBuilders = 0 then ()
  else
    let isNewGen =
      predictGeneration <| Array.append publicBuilders [| mainBuilder |]
    for publicBuilder in publicBuilders do
      let context = publicBuilder.Context
      let g = context.CFG
      let entryPP = ProgramPoint (context.FunctionAddress, 0)
      let entryVertex = context.Vertices[entryPP]
      let callPath = findAnyCallPath g entryVertex
      match callPath with
      | [] ->
        g.Exits
        |> Array.filter (fun v ->
          v.VData.Internals.IsAbstract && v.VData.Internals.AbstractContent.ReturningStatus.IsNoRet)
        |> Array.iter (fun v -> bodyAddrs.Add(v.VData.Internals.PPoint.Address) |> ignore)
      | callNodes when not isNewGen ->
        let callNode = callNodes[0]
        let addr = callNode.VData.Internals.PPoint.Address
        bodyAddrs.Add addr |> ignore
      | callNodes ->
        let callNode = callNodes[0]
        let callerNode = g.GetPreds callNode |> Array.head
        let hasArgPreparer = hasVertexInstruction callerNode "calldatasize"
        let callNode =
          if not hasArgPreparer then
            callNodes[0]
          elif callNodes.Length = 1 then
            (* only body exists: 0x0601ec5350b48fe2c3f421ea42915d16df108d27 *)
            callNodes[0]
          elif callNodes.Length < 2 then (* Oops. *)
            null
          else
            callNodes[1]
        if isNull callNode then ()
        else
          let addr = callNode.VData.Internals.PPoint.Address
          bodyAddrs.Add addr |> ignore
  bodyAddrs

///
let buildSuperCFG = ()
