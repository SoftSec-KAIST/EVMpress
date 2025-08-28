/// TODO: Can be moved to B2R2.Collections
namespace EVMpress.Utils

open System.Collections.Generic

type DisjointSet<'T when 'T: equality> () =
    let parent = Dictionary<'T, 'T> ()
    let rank = Dictionary<'T, int> ()

    let rec find x =
      match parent.TryGetValue x with
      | true, p when p <> x ->
        let root = find p
        parent[x] <- root // Path compression.
        root
      | true, p -> p
      | _ -> (* Newly add one. *)
        parent[x] <- x
        rank[x] <- 0
        x

    let union x y =
      let rootX = find x
      let rootY = find y
      if rootX <> rootY then
        let rankX = rank[rootX]
        let rankY = rank[rootY]
        if rankX < rankY then
          parent[rootX] <- rootY
        elif rankX > rankY then
          parent[rootY] <- rootX
        else
          parent[rootY] <- rootX
          rank[rootX] <- rankX + 1

    member _.Union(x: 'T, y: 'T) =
      union x y

    member _.Find(x: 'T) =
      find x
