import FreeFermionGraphs.ObstructionSearchTerminalComponentOccurrence

/-!
# Lemma 14(iv): terminal path component provenance

In the remaining two-incoming branch of Lemma 14(iv), the common stopping path
is the component denoted `P` in the manuscript.  Relative to either incoming
search, it is the `bd` component, namely the component in the source pairing
family whose original-hole side is `C_b`.

The terminal path is stored once per target, while an obstruction arc proves
that the target has the opposite pairing label to its source.  It is therefore
most faithful to record the path in the `bd` family indexed by the opposite of
the target pairing and derive its membership in the incoming source family.

This module records only that literal stopping-path provenance.  It does not
assume original-hole membership of the path's `C_b` vertices, exact four-colour
membership, terminal-hole persistence, clonehood, or degree three.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Literal component-family provenance of the terminal path selected by an
initialized obstruction search.

The path is indexed by the target, so its family is expressed using the
opposite of the target's pairing.  Under an incoming arc this is definitionally
the pairing family of the source only after applying the already derived
obstruction-pairing theorem. -/
structure InitializationTerminalPathComponentData
    (T : I.InitializationTerminalCoreData) : Prop where
  terminalPath_mem_opposite_bd :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        Set.range (T.terminalPath target).vertex ∈
          (families ((I.pairing target).opposite)).bdPaths

namespace InitializationTerminalPathComponentData

variable {T : I.InitializationTerminalCoreData}

/-- For an actual incoming arc, the terminal path is a `bd` component of the
source's fixed-pairing family. -/
theorem terminalPath_mem_source_bd
    (P : I.InitializationTerminalPathComponentData T)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Set.range (T.terminalPath target).vertex ∈
      (families (I.pairing source)).bdPaths := by
  have hpair :
      (I.pairing target).opposite = I.pairing source := by
    have hopposite :=
      congrArg PairingType.opposite
        (T.obstructionOpposite hclaw incoming)
    simpa using hopposite
  simpa [hpair] using P.terminalPath_mem_opposite_bd incoming

/-- The manuscript inclusion `P ∩ C_b ⊆ C_j^(m)` no longer needs terminal
component membership as a per-vertex premise once the literal terminal-path
provenance is supplied.

Original-hole membership and exact four-colour membership remain explicit:
those are the two terminal-colouring facts still to be extracted from the
initialized stopping construction. -/
theorem terminalCb_mem_manuscriptFinalHole_of_componentData
    (P : I.InitializationTerminalPathComponentData T)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos : 0 < (T.executionTrace.execution source).blockCount)
    {x : V}
    (hxPath : x ∈ Set.range (T.terminalPath target).vertex)
    (hxCb : x ∈ (families (I.pairing source)).Cb)
    (hxExact : ExactlyOneOfFour x
      (families (I.pairing source)).Ca
      (families (I.pairing source)).Cb
      (families (I.pairing source)).Cc
      (families (I.pairing source)).Cd)
    (hxOriginal : x ∈ Set.range T.executionTrace.originalHole.vertex) :
    x ∈ Set.range
      (T.executionTrace.execution source).manuscriptFinalHole.vertex := by
  exact T.terminalCb_mem_manuscriptFinalHole incoming hpos
    (P.terminalPath_mem_source_bd hclaw incoming)
    hxPath hxCb hxExact hxOriginal

end InitializationTerminalPathComponentData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
