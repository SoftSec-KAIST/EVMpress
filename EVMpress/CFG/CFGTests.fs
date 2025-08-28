module EVMpress.CFG.CFGTests

open B2R2.MiddleEnd

let testBrew (brew: EVMBinaryBrew) =
  let builders = brew.Builders
  for bld in builders.Values do
    let ctx = bld.Context
    let userCtx = ctx.UserContext
    let addr = ctx.FunctionAddress
    let isSharedRegion = userCtx.IsSharedRegion
    let isPublicFunction = userCtx.IsPublicFunction
    let prefix =
      match isPublicFunction with
      | true -> "publ_"
      | false ->
        match isSharedRegion with
        | true -> "shar_"
        | false -> "priv_"
    let funcName = prefix + addr.ToString("x")
    printfn "Function: %s" funcName
    // printfn "Function at %x: isSharedRegion=%b, isPublicFunction=%b" addr isSharedRegion isPublicFunction

