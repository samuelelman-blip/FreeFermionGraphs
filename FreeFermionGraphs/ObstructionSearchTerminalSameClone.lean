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

/-- Paper-faithful data for the equal-clone-centre branch of Lemma 14(iv).

The obstruction target lies on the same alternating side as both endpoints,
so its path index is even and the path has odd cardinality.  The common clone
centre is adjacent to the target and to the two same-side vertices two path
steps away.  The two flanking indices and their separation are derived below;
they are not certificate fields. -/
structure SameCloneTerminalNeighborhood
    (P : IndexedInducedPath G) (target : V) where
  targetIndex : Fin P.card
  target_eq : P.vertex targetIndex = target
  targetIndex_even : Even targetIndex.val
  pathCard_odd : Odd P.card
  cloneCenter : V
  clone_adj_target : G.Adj cloneCenter (P.vertex targetIndex)
  clone_adj_previous :
    ∀ previousIndex : Fin P.card,
      previousIndex.val + 2 = targetIndex.val →
        G.Adj cloneCenter (P.vertex previousIndex)
  clone_adj_next :
    ∀ nextIndex : Fin P.card,
      targetIndex.val + 2 = nextIndex.val →
        G.Adj cloneCenter (P.vertex nextIndex)

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

namespace SameCloneTerminalNeighborhood

/-- A target distinct from both endpoints has a strictly interior path
index. -/
theorem targetIndex_bounds
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneTerminalNeighborhood target)
    (hfirst : P.obstructionEndpoint .first ≠ target)
    (hlast : P.obstructionEndpoint .last ≠ target) :
    0 < X.targetIndex.val ∧ X.targetIndex.val + 1 < P.card := by
  constructor
  · by_contra hpositive
    have hzero : X.targetIndex.val = 0 := by omega
    have hindex :
        P.obstructionEndpointIndex .first = X.targetIndex := by
      apply Fin.ext
      simp [obstructionEndpointIndex, hzero]
    apply hfirst
    rw [obstructionEndpoint, hindex, X.target_eq]
  · by_contra hupper
    have hlastIndex : X.targetIndex.val = P.card - 1 := by
      have hisLt := X.targetIndex.isLt
      omega
    have hindex :
        P.obstructionEndpointIndex .last = X.targetIndex := by
      apply Fin.ext
      simp [obstructionEndpointIndex, hlastIndex]
    apply hlast
    rw [obstructionEndpoint, hindex, X.target_eq]

/-- Alternating-side parity turns strict interiority into the two flanking
same-side indices used in the manuscript's induced claw. -/
theorem exists_twoStepFlanks
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneTerminalNeighborhood target)
    (hfirst : P.obstructionEndpoint .first ≠ target)
    (hlast : P.obstructionEndpoint .last ≠ target) :
    ∃ previousIndex nextIndex : Fin P.card,
      previousIndex.val + 2 = X.targetIndex.val ∧
        X.targetIndex.val + 2 = nextIndex.val := by
  obtain ⟨hpositive, hupper⟩ := X.targetIndex_bounds hfirst hlast
  obtain ⟨a, ha⟩ := X.targetIndex_even
  obtain ⟨b, hb⟩ := X.pathCard_odd
  have hprevious : X.targetIndex.val - 2 < P.card := by omega
  have hnext : X.targetIndex.val + 2 < P.card := by omega
  let previousIndex : Fin P.card :=
    ⟨X.targetIndex.val - 2, hprevious⟩
  let nextIndex : Fin P.card :=
    ⟨X.targetIndex.val + 2, hnext⟩
  refine ⟨previousIndex, nextIndex, ?_, ?_⟩
  · dsimp [previousIndex]
    omega
  · rfl

/-- The equal-clone terminal neighborhood constructs the local claw
geometry once the target is assumed not to be either path endpoint. -/
theorem toInteriorGeometry
    {P : IndexedInducedPath G} {target : V}
    (X : P.SameCloneTerminalNeighborhood target)
    (hfirst : P.obstructionEndpoint .first ≠ target)
    (hlast : P.obstructionEndpoint .last ≠ target) :
    Nonempty (P.SameCloneInteriorGeometry target) := by
  obtain ⟨previousIndex, nextIndex, hprevious, hnext⟩ :=
    X.exists_twoStepFlanks hfirst hlast
  exact ⟨
    { previousIndex := previousIndex
      targetIndex := X.targetIndex
      nextIndex := nextIndex
      previous_gap := hprevious
      next_gap := hnext
      target_eq := X.target_eq
      cloneCenter := X.cloneCenter
      clone_adj_previous := X.clone_adj_previous previousIndex hprevious
      clone_adj_target := X.clone_adj_target
      clone_adj_next := X.clone_adj_next nextIndex hnext }⟩

end SameCloneTerminalNeighborhood

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
entering one target.  Its field is the alternating terminal neighborhood,
not the already assembled claw or the desired endpoint conclusion. -/
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
          ((T.terminalPath target).SameCloneTerminalNeighborhood
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
  have hslots :
      T.currentSlot source target ≠ T.currentSlot source' target := by
    intro hslot
    exact hne (T.currentSlot_source_injective hclaw h h' hslot)
  exact
    (T.terminalPath target).target_eq_selectedEndpoint_of_sameClone
      (target : V)
      (T.currentSlot source target)
      (T.currentSlot source' target)
      (by
        intro hfirst hlast
        obtain ⟨X⟩ := S.interiorGeometry hne h h' hfirst hlast
        cases hsource : T.currentSlot source target <;>
            cases hsource' : T.currentSlot source' target
        · exact (hslots (hsource.trans hsource'.symm)).elim
        · exact X.toInteriorGeometry
            (by simpa [hsource] using hfirst)
            (by simpa [hsource'] using hlast)
        · exact X.toInteriorGeometry
            (by simpa [hsource'] using hlast)
            (by simpa [hsource] using hfirst)
        · exact (hslots (hsource.trans hsource'.symm)).elim)
      hclaw

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
