module Prelude

open System.Collections.Immutable
open B2R2
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.ControlFlowGraph
open B2R2.FrontEnd.BinLifter
open B2R2.BinIR.SSA

/// Graph with IRBasicBlock as node and CFGEdgeKind as edge.
type IRGraph = IDiGraph<LowUIRBasicBlock, CFGEdgeKind>
/// Immutable dict.
type ImmDict<'A, 'B> = ImmutableDictionary<'A, 'B>
/// Immutable set.
type ImmSet<'A> = ImmutableHashSet<'A>

module Global =
  let rt = 256<rt>
