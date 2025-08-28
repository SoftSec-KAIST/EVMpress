module EVMpress.Common.Timer

let calcTime<'Ret> (fn: unit -> 'Ret) =
  let sw = System.Diagnostics.Stopwatch.StartNew ()
  let result = fn ()
  sw.Stop ()
#if DEBUG
  printfn "[*] Elapsed time: %A" sw.Elapsed
#endif
  result, sw.ElapsedMilliseconds

