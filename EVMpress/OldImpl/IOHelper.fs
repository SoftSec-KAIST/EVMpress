module IOHelper

open System

let convertHexStrToByteArray (hex: string) =
  let hex = hex.Trim ()
  let hex = if hex.StartsWith ("0x") then hex.Substring (2) else hex
  let hexLen = hex.Length
  assert (hexLen % 2 = 0)
  let byteCount = hex.Length / 2
  [0 .. byteCount - 1] // inclusive range
  |> Seq.map (fun i ->
    let byteStr = hex.Substring(i * 2, 2)
    let byte = Convert.ToByte(byteStr, 16)
    byte)
  |> Seq.toArray
