import FreeFermionGraphs.ObstructionSearchTerminalComponentOccurrence

/-!
# Lemma 14(iv): terminal path component provenance

In the remaining two-incoming branch of Lemma 14(iv), the common stopping path
is the component denoted `P` in the manuscript.  Relative to either incoming
search, it is the `bd` component in the source pairing family.

The terminal path is stored once per target, while an obstruction arc proves
that the target has the opposite pairing label to its source.  It is therefore
most faithful to record the path in the `bd` family indexed by the opposite of
the target pairing and derive its membership in the incoming source family.

This component provenance does not by itself prove
`P ∩ C_b ⊆ C_j^(m)`.  A vertex in `C_b ∩ C'_c` may also occur on an executed
`ac` path, as allowed by Corollary 9.  The remaining manuscript obligation is
to use the introduced/removed orientation of Definition 19 to show that a
missing `C_b` vertex would have been removed by a `bd` block.
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
opposite of the target's pairing.  Under an incoming arc, the already derived
obstruction-pairing theorem identifies this with the source family. -/
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

end InitializationTerminalPathComponentData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
