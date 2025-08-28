module DualDictionary

open System.Collections.Generic

type DualDictionary<'K1, 'K2, 'V
                      when 'K1 : equality and
                           'K2 : equality> () =
  let dict = Dictionary<'K1, Dictionary<'K2, 'V>> ()

  member __.FirstKeys = dict.Keys

  member __.Item with get(k1, k2) = __.Get k1 k2 and
                      set(k1, k2) value = __.Add k1 k2 value

  member __.GetByFirstKey firstKey =
    match dict.TryGetValue firstKey with
    | true, innerDict -> innerDict
    | false, _ -> failwith "Key not found"

  member __.TryGetByFirstKey firstKey =
    match dict.TryGetValue firstKey with
    | true, innerDict -> Some innerDict
    | false, _ -> None

  member __.Get (key1: 'K1) (key2: 'K2) =
    match dict.TryGetValue key1 with
    | true, innerDict -> innerDict[key2]
    | false, _ -> failwith "Key not found"

  /// This method will overwrite the value if the key already exists.
  member __.Add (key1: 'K1) (key2: 'K2) (value: 'V) =
    match dict.TryGetValue key1 with
    | true, innerDict ->
      if innerDict.ContainsKey key2 then innerDict.Remove key2 |> ignore
      innerDict.Add (key2, value)
    | false, _ ->
      let innerDict = Dictionary<'K2, 'V> ()
      innerDict.Add (key2, value)
      dict.Add (key1, innerDict)

  member __.TryGetValue (key1: 'K1) (key2: 'K2) =
    match dict.TryGetValue key1 with
    | true, innerDict -> innerDict.TryGetValue key2
    | false, _ -> false, Unchecked.defaultof<'V>

  member __.ContainsKey (key1: 'K1) (key2: 'K2) =
    match dict.TryGetValue key1 with
    | true, innerDict -> innerDict.ContainsKey key2
    | false, _ -> false

  member __.RemoveByFirstKey (key1: 'K1) =
    match dict.TryGetValue key1 with
    | true, _innerDict -> dict.Remove key1 |> ignore
    | false, _ -> ()

  member __.Clear () = dict.Clear ()

  member __.HasFirstKey (key1: 'K1) = dict.ContainsKey key1

