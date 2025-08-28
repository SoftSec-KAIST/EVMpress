namespace EVMpress.Type

open B2R2
open System.Collections.Generic
open B2R2.MiddleEnd
open B2R2.MiddleEnd.ControlFlowAnalysis.Strategies

[<AutoOpen>]
module private InferrerLogics =

  ()

type Inferrer (brew: BinaryBrew<EVMFuncUserContext, DummyContext>,
               pubBodyAddresses: Addr list) =
  let hdl = brew.BinHandle
  let dataFlowManager = DataFlowManager(hdl)
  let superCFGManager = SuperCFGManager(brew, dataFlowManager, pubBodyAddresses)
  let _ = ()

  member _.Types with get () = failwith "TODO"
