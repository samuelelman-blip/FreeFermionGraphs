import FreeFermionGraphs.ObstructionSearchTerminalSameClone

/-!
# Lemma 14(iv): the distinct-clone terminal case

The second terminal case in the manuscript begins with distinct clone centres
for the common obstruction target.  Its neighborhood propagation ends with
four explicitly identified vertices forming a claw.  This module isolates
that final graph-theoretic contradiction and combines it with the common-clone
case.

The resulting pairwise theorem assumes the final neighbourhood facts produced
by the corresponding branch of the obstruction-search analysis.  In
particular, the three leaf nonedges of the eventual claw are derived from the
manuscript's two statements that one terminal vertex has no additional
neighbours in the original hole and that the alternative clone has precisely
its two displayed neighbours there.  It does not assume that the target is an
endpoint.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The final local configuration in the distinct-clone branch of
Lemma 14(iv).  In the manuscript these vertices are the center `u'` and the
three leaves `j_{p-2}`, `w'`, and `v''` (with the exact adornments determined
by the two incoming searches). -/
structure DistinctCloneInteriorGeometry (G : SimpleGraph V) where
  center : V
  previous : V
  originalNeighbor : V
  otherClone : V
  adj_previous : G.Adj center previous
  adj_originalNeighbor : G.Adj center originalNeighbor
  adj_otherClone : G.Adj center otherClone
  previous_ne_originalNeighbor : previous ≠ originalNeighbor
  previous_ne_otherClone : previous ≠ otherClone
  originalNeighbor_ne_otherClone : originalNeighbor ≠ otherClone
  previous_not_adj_originalNeighbor : ¬G.Adj previous originalNeighbor
  previous_not_adj_otherClone : ¬G.Adj previous otherClone
  originalNeighbor_not_adj_otherClone : ¬G.Adj originalNeighbor otherClone

namespace DistinctCloneInteriorGeometry

/-- The terminal distinct-clone configuration contradicts claw-freeness. -/
theorem false_of_clawFree
    (X : DistinctCloneInteriorGeometry G)
    (hclaw : G.IsClawFree) : False := by
  rcases hclaw X.adj_previous X.adj_originalNeighbor X.adj_otherClone
      X.previous_ne_originalNeighbor X.previous_ne_otherClone
      X.originalNeighbor_ne_otherClone with
    hpreviousOriginal | hpreviousClone | horiginalClone
  · exact X.previous_not_adj_originalNeighbor hpreviousOriginal
  · exact X.previous_not_adj_otherClone hpreviousClone
  · exact X.originalNeighbor_not_adj_otherClone horiginalClone

end DistinctCloneInteriorGeometry

/-- The final neighbourhood information obtained at the end of the
distinct-clone propagation in Lemma 14(iv).

In the manuscript, `center`, `previous`, `propagatedNeighbor`, and
`otherClone` are respectively `u'`, `j_{p-2}`, `w'` (printed as `w''` in the
last displayed claw), and `v''`.  The vertices `b0` and `b1` are the two
original-hole neighbours of `v''`.

Unlike `DistinctCloneInteriorGeometry`, this structure does not contain any
of the three nonedges required by a claw.  They follow from the two exact
original-hole neighbourhood bounds in the final paragraph of the paper. -/
structure DistinctCloneFinalNeighborhood (G : SimpleGraph V) where
  originalHole : IndexedInducedHole G
  center : V
  previous : V
  propagatedNeighbor : V
  otherClone : V
  b0 : V
  b1 : V
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  adj_otherClone : G.Adj center otherClone
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  previous_ne_otherClone : previous ≠ otherClone
  propagatedNeighbor_ne_otherClone : propagatedNeighbor ≠ otherClone
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range originalHole.vertex
  otherClone_mem_originalHole :
    otherClone ∈ Set.range originalHole.vertex
  propagatedNeighbor_ne_b0 : propagatedNeighbor ≠ b0
  propagatedNeighbor_ne_b1 : propagatedNeighbor ≠ b1
  otherClone_ne_b0 : otherClone ≠ b0
  otherClone_ne_b1 : otherClone ≠ b1
  previous_originalHole_neighbors :
    ∀ ⦃x : V⦄,
      x ∈ Set.range originalHole.vertex →
      G.Adj previous x →
        x = b0 ∨ x = b1
  otherClone_originalHole_neighbors :
    ∀ ⦃x : V⦄,
      x ∈ Set.range originalHole.vertex →
      G.Adj otherClone x →
        x = b0 ∨ x = b1

namespace DistinctCloneFinalNeighborhood

/-- The propagated original-hole neighbour is not adjacent to the preceding
terminal vertex, because that vertex has no original-hole neighbours beyond
`b0` and `b1`. -/
theorem previous_not_adj_propagatedNeighbor
    (X : DistinctCloneFinalNeighborhood G) :
    ¬G.Adj X.previous X.propagatedNeighbor := by
  intro h
  rcases X.previous_originalHole_neighbors
      X.propagatedNeighbor_mem_originalHole h with h0 | h1
  · exact X.propagatedNeighbor_ne_b0 h0
  · exact X.propagatedNeighbor_ne_b1 h1

/-- The preceding terminal vertex is not adjacent to the alternative clone
for the same reason. -/
theorem previous_not_adj_otherClone
    (X : DistinctCloneFinalNeighborhood G) :
    ¬G.Adj X.previous X.otherClone := by
  intro h
  rcases X.previous_originalHole_neighbors
      X.otherClone_mem_originalHole h with h0 | h1
  · exact X.otherClone_ne_b0 h0
  · exact X.otherClone_ne_b1 h1

/-- The propagated neighbour is not adjacent to the alternative clone,
whose only neighbours in the original hole are `b0` and `b1`. -/
theorem propagatedNeighbor_not_adj_otherClone
    (X : DistinctCloneFinalNeighborhood G) :
    ¬G.Adj X.propagatedNeighbor X.otherClone := by
  intro h
  rcases X.otherClone_originalHole_neighbors
      X.propagatedNeighbor_mem_originalHole h.symm with h0 | h1
  · exact X.propagatedNeighbor_ne_b0 h0
  · exact X.propagatedNeighbor_ne_b1 h1

/-- The paper's final neighbourhood bounds construct the explicit local claw
geometry; none of its leaf nonedges is supplied separately. -/
def toInteriorGeometry
    (X : DistinctCloneFinalNeighborhood G) :
    DistinctCloneInteriorGeometry G where
  center := X.center
  previous := X.previous
  originalNeighbor := X.propagatedNeighbor
  otherClone := X.otherClone
  adj_previous := X.adj_previous
  adj_originalNeighbor := X.adj_propagatedNeighbor
  adj_otherClone := X.adj_otherClone
  previous_ne_originalNeighbor := X.previous_ne_propagatedNeighbor
  previous_ne_otherClone := X.previous_ne_otherClone
  originalNeighbor_ne_otherClone := X.propagatedNeighbor_ne_otherClone
  previous_not_adj_originalNeighbor :=
    X.previous_not_adj_propagatedNeighbor
  previous_not_adj_otherClone := X.previous_not_adj_otherClone
  originalNeighbor_not_adj_otherClone :=
    X.propagatedNeighbor_not_adj_otherClone

/-- The final distinct-clone neighbourhood contradicts claw-freeness. -/
theorem false_of_clawFree
    (X : DistinctCloneFinalNeighborhood G)
    (hclaw : G.IsClawFree) : False :=
  X.toInteriorGeometry.false_of_clawFree hclaw

end DistinctCloneFinalNeighborhood

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- The two local alternatives obtained by the manuscript's comparison of
the clone centres in the terminal holes. -/
inductive TwoIncomingInteriorGeometry
    (T : I.InitializationTerminalCoreData)
    (target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometry T target
  | distinctClone :
      Nonempty (DistinctCloneFinalNeighborhood G) →
      TwoIncomingInteriorGeometry T target

/-- Pairwise terminal analysis from the concrete `OS` trace.  The field is
only requested under the negation of both endpoint alternatives, and it
returns one of the two explicit claw configurations. -/
structure TwoIncomingTerminalClawAnalysis
    (T : I.InitializationTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        TwoIncomingInteriorGeometry T target

namespace InitializationTerminalCoreData

/-- Both clone-centre alternatives contradict claw-freeness, so a common
target of two distinct incoming searches is one of their current terminal
endpoints. -/
theorem target_is_current_endpoint_of_twoIncoming_of_clawAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target) :
    ((T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V) ∨
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)) := by
  have hslots :
      T.currentSlot source target ≠ T.currentSlot source' target := by
    intro hslot
    exact hne (T.currentSlot_source_injective hclaw h h' hslot)
  by_cases hsource :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V)
  · exact Or.inl hsource
  by_cases hsource' :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)
  · exact Or.inr hsource'
  rcases A.interiorGeometry hne h h' hsource hsource' with
      hsame | hdistinct
  · obtain ⟨X⟩ := hsame
    have hgeometry : Nonempty
        ((T.terminalPath target).SameCloneInteriorGeometry
          (target : V)) := by
      cases hslot : T.currentSlot source target <;>
          cases hslot' : T.currentSlot source' target
      · exact (hslots (hslot.trans hslot'.symm)).elim
      · exact X.toInteriorGeometry
          (by simpa [hslot] using hsource)
          (by simpa [hslot'] using hsource')
      · exact X.toInteriorGeometry
          (by simpa [hslot'] using hsource')
          (by simpa [hslot] using hsource)
      · exact (hslots (hslot.trans hslot'.symm)).elim
    obtain ⟨Y⟩ := hgeometry
    exact (Y.false_of_clawFree hclaw).elim
  · obtain ⟨X⟩ := hdistinct
    exact (X.false_of_clawFree hclaw).elim

/-- Promote the terminal core to the complete certificate after proving the
two concrete interior-claw alternatives. -/
def toInitializationTerminalData_of_clawAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree) :
    I.InitializationTerminalData where
  toInitializationTerminalCoreData := T
  target_is_current_endpoint_of_twoIncoming := by
    intro source source' target hne h h'
    exact T.target_is_current_endpoint_of_twoIncoming_of_clawAnalysis
      A hclaw hne h h'

/-- Lemma 14 from the terminal core and the two explicit interior-claw
branches.  In particular, this theorem has no endpoint-alternative premise. -/
theorem lemma14_of_terminalClawAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree) :
    (∀ source : I.Node,
      (I.output source).run = none ∨
        ∃ F : FullDefinition19Deformation
            (families (I.pairing source)) Cprime,
          (I.output source).run = some F) ∧
    I.graph.IsBipartiteByPairing I.pairing ∧
    (∀ ⦃source source' : I.Node⦄,
      source ≠ source' →
      I.pairing source = I.pairing source' →
        Disjoint (I.output source).paths
          (I.output source').paths) ∧
    ((∀ target : I.Node, I.graph.AtMostTwoIncoming target) ∧
      ∀ ⦃source source' target : I.Node⦄,
        source ≠ source' →
        I.graph.Arc source target →
        I.graph.Arc source' target →
          ((I.dependentSet source = {(target : V)} ∧
              I.dependentSet source' ≠ {(target : V)}) ∨
            (I.dependentSet source ≠ {(target : V)} ∧
              I.dependentSet source' = {(target : V)}))) := by
  exact InitializationTerminalData.lemma14_of_initializationTerminalData
    (T.toInitializationTerminalData_of_clawAnalysis A hclaw) hclaw

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
