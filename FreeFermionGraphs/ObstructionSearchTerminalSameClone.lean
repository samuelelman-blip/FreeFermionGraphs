import FreeFermionGraphs.ObstructionSearchTerminal

/-!
# Lemma 14(iv): the common-clone terminal case

When two obstruction searches approach the same terminal path from its two
ends, assume their obstruction target is not one of those ends.  In the first
case of the manuscript proof, the target has the same clone centre in the two
terminal holes.  The preceding target-side vertex, the target, and the
following target-side vertex are pairwise nonadjacent vertices of the induced
path, while all three are adjacent to the common clone centre.  They therefore
induce a claw.

This module records exactly that local indexed-path geometry and proves the
contradiction.  It does not assume that the target is an endpoint.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The local geometry of the same-clone interior case in Lemma 14(iv).

The three displayed path vertices are the manuscript's
`j_{p-2}`, `j_{p-1}`, and `j_p`.  Consecutive displayed vertices are two
indices apart in the alternating induced path. -/
structure SameCloneInteriorGeometry
    (P : IndexedInducedPath G) (target : V) where
  previousIndex : Fin P.card
  targetIndex : Fin P.card
  nextIndex : Fin P.card
  previous_gap : previousIndex.val + 2 = targetIndex.val
  next_gap : targetIndex.val + 2 = nextIndex.val
  target_eq : P.vertex targetIndex = target
  cloneCenter : V
  clone_adj_previous : G.Adj cloneCenter (P.vertex previousIndex)
  clone_adj_target : G.Adj cloneCenter (P.vertex targetIndex)
  clone_adj_next : G.Adj cloneCenter (P.vertex nextIndex)

namespace SameCloneInteriorGeometry

/-- Two vertices whose indices differ by two on an induced path are
nonadjacent. -/
theorem previous_not_adj_target
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target) :
    ¬G.Adj (P.vertex X.previousIndex) (P.vertex X.targetIndex) := by
  have hgap := X.previous_gap
  intro h
  rcases (P.adj_iff X.previousIndex X.targetIndex).1 h with hstep | hstep
  · omega
  · omega

/-- The target-side vertex and its next same-side path vertex are
nonadjacent. -/
theorem target_not_adj_next
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target) :
    ¬G.Adj (P.vertex X.targetIndex) (P.vertex X.nextIndex) := by
  have hgap := X.next_gap
  intro h
  rcases (P.adj_iff X.targetIndex X.nextIndex).1 h with hstep | hstep
  · omega
  · omega

/-- The two flanking same-side vertices are four indices apart and hence
nonadjacent. -/
theorem previous_not_adj_next
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target) :
    ¬G.Adj (P.vertex X.previousIndex) (P.vertex X.nextIndex) := by
  have hpreviousGap := X.previous_gap
  have hnextGap := X.next_gap
  intro h
  rcases (P.adj_iff X.previousIndex X.nextIndex).1 h with hstep | hstep
  · omega
  · omega

/-- The preceding and target vertices are distinct. -/
theorem previous_ne_target
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target) :
    P.vertex X.previousIndex ≠ P.vertex X.targetIndex := by
  have hgap := X.previous_gap
  intro h
  have hindex := P.injective h
  have hval := congrArg Fin.val hindex
  omega

/-- The preceding and following vertices are distinct. -/
theorem previous_ne_next
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target) :
    P.vertex X.previousIndex ≠ P.vertex X.nextIndex := by
  have hpreviousGap := X.previous_gap
  have hnextGap := X.next_gap
  intro h
  have hindex := P.injective h
  have hval := congrArg Fin.val hindex
  omega

/-- The target and following vertices are distinct. -/
theorem target_ne_next
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target) :
    P.vertex X.targetIndex ≠ P.vertex X.nextIndex := by
  have hgap := X.next_gap
  intro h
  have hindex := P.injective h
  have hval := congrArg Fin.val hindex
  omega

/-- The common-clone interior configuration is impossible in a claw-free
graph. -/
theorem false_of_clawFree
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneInteriorGeometry target)
    (hclaw : G.IsClawFree) : False := by
  rcases hclaw X.clone_adj_previous X.clone_adj_target X.clone_adj_next
      X.previous_ne_target X.previous_ne_next X.target_ne_next with
    hpreviousTarget | hpreviousNext | htargetNext
  · exact X.previous_not_adj_target hpreviousTarget
  · exact X.previous_not_adj_next hpreviousNext
  · exact X.target_not_adj_next htargetNext

end SameCloneInteriorGeometry

/-- If every non-endpoint occurrence of `target` produces the manuscript's
same-clone interior geometry, then `target` must be one of the two selected
endpoints. -/
theorem target_eq_selectedEndpoint_of_sameClone
    (P : IndexedInducedPath G) (target : V)
    (firstSlot lastSlot : ObstructionSlot)
    (hinterior :
      P.obstructionEndpoint firstSlot ≠ target →
      P.obstructionEndpoint lastSlot ≠ target →
        Nonempty (P.SameCloneInteriorGeometry target))
    (hclaw : G.IsClawFree) :
    P.obstructionEndpoint firstSlot = target ∨
      P.obstructionEndpoint lastSlot = target := by
  by_cases hfirst : P.obstructionEndpoint firstSlot = target
  · exact Or.inl hfirst
  by_cases hlast : P.obstructionEndpoint lastSlot = target
  · exact Or.inr hlast
  obtain ⟨X⟩ := hinterior hfirst hlast
  exact (X.false_of_clawFree hclaw).elim

end IndexedInducedPath

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- The concrete same-clone branch for every pair of distinct searches
entering one target.  Its field is local indexed-path geometry, not the
desired endpoint conclusion. -/
structure SameCloneTerminalAnalysis
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
        Nonempty
          ((T.terminalPath target).SameCloneInteriorGeometry
            (target : V))

namespace InitializationTerminalCoreData

/-- The common-clone local claw theorem yields the exact two-incoming
endpoint alternative required by Lemma 14(iv). -/
theorem target_is_current_endpoint_of_twoIncoming_of_sameClone
    (T : I.InitializationTerminalCoreData)
    (S : SameCloneTerminalAnalysis T)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target) :
    ((T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V) ∨
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)) := by
  exact
    (T.terminalPath target).target_eq_selectedEndpoint_of_sameClone
      (target : V)
      (T.currentSlot source target)
      (T.currentSlot source' target)
      (S.interiorGeometry hne h h') hclaw

/-- In the all-common-clone special case, the core obstruction-search data
can be promoted to the complete terminal certificate without assuming the
endpoint alternative. -/
def toInitializationTerminalData_of_sameClone
    (T : I.InitializationTerminalCoreData)
    (S : SameCloneTerminalAnalysis T)
    (hclaw : G.IsClawFree) :
    I.InitializationTerminalData where
  toInitializationTerminalCoreData := T
  target_is_current_endpoint_of_twoIncoming := by
    intro source source' target hne h h'
    exact T.target_is_current_endpoint_of_twoIncoming_of_sameClone
      S hclaw hne h h'

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
