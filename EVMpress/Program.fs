module EVMpress.Program

open System
open System.IO
open EVMpress.CFG
open EVMpress.Common
open EVMpress.Common.Timer
open B2R2.MiddleEnd.ControlFlowAnalysis
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies

let usesGapCompletion = true
Console.SetOut (new StreamWriter (Console.OpenStandardOutput (), AutoFlush = false))

let getFuncKindFromContext (ctx: CFGBuildingContext<EVMFuncUserContext, _>) =
  if ctx.UserContext.IsPublicFunction then
    Public
  elif ctx.UserContext.IsSharedRegion then
    Shared
  else
    Private

let extractAddrFromPath (path: string) = Path.GetFileNameWithoutExtension path

let isSilent = true

[<EntryPoint>]
let main argv =
#if DEBUG
  let addr = "0x2361f3344ce44a090bacf2dc5830d606fdf24ca6" (* yul *)
  let addr = "0x5283fc3a1aac4dac6b9581d3ab65f4ee2f3de7dc" (* yul *)
  // let addr = "0x000000000000d0151e748d25b766e77efe2a6c83"(* non-yul *)
  let hexDir = @"D:/db/hex-to_20231231/"
  let inputPath = hexDir + addr + ".hex"
  let outputPath = "temp.json"
#else
  let args = argv
  let inputPath = args[0]
  let outputPath = args[1]
#endif
  let results = Results.Empty
  let callbackOnPostProcessing = getCallbackOnPostProcessing ()
  let strategy = EVMCFGRecovery(callbackOnPostProcessing)
  let brew, timeForBrew =
    calcTime (fun _ ->
      inputPath
      |> parseBytecode strategy
      // |> analyzeRecursion strategy
      )
  (*
  let brew, timeForGap =
    calcTime (fun _ ->
      brew
      |> if usesGapCompletion then applyGapCompletion strategy
         else fun brew -> brew)
  *)
  let timeForGap = 0L
  results.Addr <- extractAddrFromPath inputPath
  results.TimeForCFG <- timeForBrew
  results.TimeForGap <- timeForGap
  (* 1. Write the result of function detection. *)
  let pubFuncBodies = collectPublicFunctionBodies brew
#if DEBUG
  for addr in pubFuncBodies |> Seq.sort do
    Console.WriteLine $"Public function body: {addr:X8}"
#endif
  for builder in brew.Builders.Values do
    let ctx = builder.Context
    let addr = ctx.FunctionAddress
    if pubFuncBodies.Contains addr || addr = 0x0UL then ()
    else
      let kind = getFuncKindFromContext ctx
      if kind = Shared then () (* Shared regions are not functions. *)
      else results.AddFunc addr kind
#if DEBUG
  for x in results.Funcs do
    Console.WriteLine $"{x.Key:X8}\t{x.Value}"
#endif
  (* 2. Write the result of type recovery. *)
  let pubBodyAddrs = pubFuncBodies |> Seq.toList
  let privAddrs = System.Collections.Generic.List ()
  let pubAddrs = System.Collections.Generic.List ()
  for KeyValue (addr, kind) in results.Funcs do
    match kind with
    | "pub" -> pubAddrs.Add (uint64 <| int addr)
    | "priv" -> privAddrs.Add (uint64 <| int addr)
    | _ -> ()
  let testResult, timeForInfer = calcTime (fun _ ->
    let testTypeRec = TypeRec.TypeRecoverer (brew, pubBodyAddrs)
    let testResult = testTypeRec.Run privAddrs pubAddrs None
    testResult)
  results.Types <- testResult
  results.TimeForType <- timeForInfer
  (* 3. Save to a file. *)
  results.Save outputPath
  if not isSilent then Console.Out.Flush ()
  0

