namespace EVMpress.Common

open System.IO
open System.Collections.Generic
open Newtonsoft.Json
open B2R2
open TypeRecTypes

type Results = {
  mutable Addr: string

  /// Addr to func kind.
  /// e.g. "0x3ab" -> "pub" | "priv" | "shared"
  Funcs: Dictionary<string, string>

  mutable TimeForCFG: int64

  mutable TimeForGap: int64

  mutable TimeForType: int64

  mutable Types: PerFuncType list
}
with
  static member Empty =
    { Addr = ""
      Funcs = Dictionary<string, string> ()
      Types = []
      TimeForCFG = 0
      TimeForGap = 0
      TimeForType = 0 }

  member this.AddFunc (addr: Addr) kind =
    let addr = $"0x{addr:x}"
    let kind =
      match kind with
      | Public -> "pub"
      | Private -> "priv"
      | Shared -> "shared"
    this.Funcs[addr] <- kind

  member this.Save outputPath =
    let json = JsonConvert.SerializeObject (this, Formatting.Indented)
    File.WriteAllText (outputPath, json)

and FuncKind =
  | Public
  | Private
  | Shared
