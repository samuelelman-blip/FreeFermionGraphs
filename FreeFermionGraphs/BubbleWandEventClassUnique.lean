import FreeFermionGraphs.EqE1CanonicalTargetCount

/-!
# Uniqueness of the deformation class behind one Boolean bubble-wand arc

Two retained events with the same source and target have hoop carriers that
share the whole post-handle path and differ only in their bubble vertex.  This
module proves that, in a claw-free graph, those two carriers differ by one
literal Definition 10 deformation.  Hence the quotient class selected for a
Boolean Eq. (E1) arc is independent of the retained event.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- Reverse the two color roles while preserving the cyclic orientation.
Every old `b i` becomes the new `a i`; the matching new `b i` is the old
`a (prev i)`. -/
def swapColors {k : Nat} (C : EvenHoleLabeling G k) :
    EvenHoleLabeling G k where
  two_le := C.two_le
  a := C.b
  b := fun i => C.a (C.prev i)
  next := C.next
  prev := C.prev
  next_ne := C.next_ne
  next_next_ne := C.next_next_ne
  next_prev := C.next_prev
  prev_next := C.prev_next
  a_injective := C.b_injective
  b_injective := by
    intro i j hij
    have hprev : C.prev i = C.prev j := C.a_injective hij
    calc
      i = C.next (C.prev i) := (C.next_prev i).symm
      _ = C.next (C.prev j) := congrArg C.next hprev
      _ = j := C.next_prev j
  color_disjoint := by
    intro i j
    exact (C.color_disjoint (C.prev j) i).symm
  adj_aa := C.adj_bb
  adj_bb := by
    intro i j
    exact C.adj_aa (C.prev i) (C.prev j)
  adj_ab_iff := by
    intro i j
    constructor
    · intro hij
      rcases (C.adj_ab_iff (C.prev j) i).1 hij.symm with hprev | hj
      · right
        calc
          j = C.next (C.prev j) := (C.next_prev j).symm
          _ = C.next i := congrArg C.next hprev.symm
      · left
        exact (C.next_prev j).symm.trans hj.symm
    · intro hij
      rcases hij with hji | hj
      · subst j
        exact (C.adj_a_prev_b i).symm
      · have hprev : C.prev j = i := by
          rw [hj, C.prev_next]
        rw [hprev]
        exact (C.adj_a_b i).symm

@[simp]
theorem swapColors_a {k : Nat} (C : EvenHoleLabeling G k)
    (i : Fin k) : C.swapColors.a i = C.b i :=
  rfl

/-- Swapping the alternating color names leaves the concrete hole carrier
unchanged. -/
@[simp]
theorem swapColors_carrier {k : Nat} (C : EvenHoleLabeling G k) :
    C.swapColors.carrier = C.carrier := by
  ext v
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact C.b_mem_carrier i
    · exact C.a_mem_carrier (C.prev i)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · right
      refine ⟨C.next i, ?_⟩
      change C.a (C.prev (C.next i)) = C.a i
      rw [C.prev_next]
    · left
      exact ⟨i, rfl⟩

/-- Exact neighbors of a `b`-vertex inside an alternating even-hole
carrier. -/
theorem adj_b_iff_of_mem {k : Nat} (C : EvenHoleLabeling G k)
    {i : Fin k} {v : V} (hv : v ∈ C.carrier) :
    G.Adj (C.b i) v ↔
      v = C.a i ∨ v = C.a (C.prev i) := by
  rcases hv with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · constructor
    · intro h
      rcases (C.adj_ab_iff j i).1 h.symm with hij | hij
      · exact Or.inl (congrArg C.a hij.symm)
      · right
        apply congrArg C.a
        calc
          j = C.prev (C.next j) := (C.prev_next j).symm
          _ = C.prev i := congrArg C.prev hij.symm
    · rintro (h | h)
      · exact ((C.adj_ab_iff j i).2
          (Or.inl (C.a_injective h).symm)).symm
      · apply ((C.adj_ab_iff j i).2 ?_).symm
        right
        have hj : j = C.prev i := C.a_injective h
        exact calc
          i = C.next (C.prev i) := (C.next_prev i).symm
          _ = C.next j := congrArg C.next hj.symm
  · constructor
    · exact fun h => (C.adj_bb i j h).elim
    · rintro (h | h)
      · exact (C.color_disjoint i j h.symm).elim
      · exact (C.color_disjoint (C.prev i) j h.symm).elim

/-- Every vertex of an alternating even hole has two distinct carrier
neighbors, and these are all of its carrier neighbors. -/
theorem exact_two_neighbors_of_mem {k : Nat}
    (C : EvenHoleLabeling G k) {x : V} (hx : x ∈ C.carrier) :
    ∃ u v : V,
      u ≠ v ∧ u ∈ C.carrier ∧ v ∈ C.carrier ∧
        ∀ z : V, z ∈ C.carrier →
          (G.Adj x z ↔ z = u ∨ z = v) := by
  rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨C.b i, C.b (C.next i), ?_,
      C.b_mem_carrier i, C.b_mem_carrier (C.next i), ?_⟩
    · intro h
      exact C.next_ne i (C.b_injective h).symm
    · intro z hz
      exact C.adj_a_iff_of_mem hz
  · refine ⟨C.a i, C.a (C.prev i), ?_,
      C.a_mem_carrier i, C.a_mem_carrier (C.prev i), ?_⟩
    · intro h
      exact C.prev_ne i (C.a_injective h).symm
    · intro z hz
      exact C.adj_b_iff_of_mem hz

/-- If a second alternating hole is obtained set-theoretically by replacing
one `a`-vertex, claw-freeness forces the replacement vertex to be a literal
clone at that index. -/
theorem cloneAt_of_shared_deletion {k l : Nat}
    (C : EvenHoleLabeling G k) (D : EvenHoleLabeling G l)
    (s : V) (i : Fin k) (hclaw : G.IsClawFree)
    (hsOutside : s ∉ C.carrier)
    (hcarrier : D.carrier = C.deformedCarrier s i) :
    C.CloneAt s i := by
  let left := C.b i
  let right := C.b (C.next i)
  have hleft_ne_right : left ≠ right := by
    intro h
    exact C.next_ne i (C.b_injective h).symm
  have hsD : s ∈ D.carrier := by
    rw [hcarrier]
    exact C.clone_mem_deformedCarrier s i
  have hleftD : left ∈ D.carrier := by
    rw [hcarrier]
    exact C.b_mem_deformedCarrier s i
  have hrightD : right ∈ D.carrier := by
    rw [hcarrier]
    exact C.b_next_mem_deformedCarrier s i
  have hsLeft : G.Adj s left := by
    by_contra hnot
    obtain ⟨u, v, huv, huD, hvD, hneighbors⟩ :=
      D.exact_two_neighbors_of_mem hleftD
    have huAdj : G.Adj left u :=
      (hneighbors u huD).2 (Or.inl rfl)
    have hvAdj : G.Adj left v :=
      (hneighbors v hvD).2 (Or.inr rfl)
    have huRest : u ∈ C.carrier \ {C.a i} := by
      rw [hcarrier] at huD
      rcases Set.mem_insert_iff.1 huD with hus | huRest
      · exact (hnot (hus ▸ huAdj).symm).elim
      · exact huRest
    have hvRest : v ∈ C.carrier \ {C.a i} := by
      rw [hcarrier] at hvD
      rcases Set.mem_insert_iff.1 hvD with hvs | hvRest
      · exact (hnot (hvs ▸ hvAdj).symm).elim
      · exact hvRest
    have huEq : u = C.a (C.prev i) := by
      rcases (C.adj_b_iff_of_mem huRest.1).1
          ((hneighbors u (by rw [hcarrier]; exact Or.inr huRest)).2
            (Or.inl rfl)) with hu | hu
      · exact (huRest.2 (by simpa using hu)).elim
      · exact hu
    have hvEq : v = C.a (C.prev i) := by
      rcases (C.adj_b_iff_of_mem hvRest.1).1
          ((hneighbors v (by rw [hcarrier]; exact Or.inr hvRest)).2
            (Or.inr rfl)) with hv | hv
      · exact (hvRest.2 (by simpa using hv)).elim
      · exact hv
    exact huv (huEq.trans hvEq.symm)
  have hsRight : G.Adj s right := by
    by_contra hnot
    obtain ⟨u, v, huv, huD, hvD, hneighbors⟩ :=
      D.exact_two_neighbors_of_mem hrightD
    have huAdj : G.Adj right u :=
      (hneighbors u huD).2 (Or.inl rfl)
    have hvAdj : G.Adj right v :=
      (hneighbors v hvD).2 (Or.inr rfl)
    have huRest : u ∈ C.carrier \ {C.a i} := by
      rw [hcarrier] at huD
      rcases Set.mem_insert_iff.1 huD with hus | huRest
      · exact (hnot (hus ▸ huAdj).symm).elim
      · exact huRest
    have hvRest : v ∈ C.carrier \ {C.a i} := by
      rw [hcarrier] at hvD
      rcases Set.mem_insert_iff.1 hvD with hvs | hvRest
      · exact (hnot (hvs ▸ hvAdj).symm).elim
      · exact hvRest
    have huEq : u = C.a (C.next i) := by
      rcases (C.adj_b_iff_of_mem huRest.1).1
          ((hneighbors u (by rw [hcarrier]; exact Or.inr huRest)).2
            (Or.inl rfl)) with hu | hu
      · exact hu
      · have huai : u = C.a i := by
          calc
            u = C.a (C.prev (C.next i)) := hu
            _ = C.a i := congrArg C.a (C.prev_next i)
        exact (huRest.2 (by simpa using huai)).elim
    have hvEq : v = C.a (C.next i) := by
      rcases (C.adj_b_iff_of_mem hvRest.1).1
          ((hneighbors v (by rw [hcarrier]; exact Or.inr hvRest)).2
            (Or.inr rfl)) with hv | hv
      · exact hv
      · have hvai : v = C.a i := by
          calc
            v = C.a (C.prev (C.next i)) := hv
            _ = C.a i := congrArg C.a (C.prev_next i)
        exact (hvRest.2 (by simpa using hvai)).elim
    exact huv (huEq.trans hvEq.symm)
  obtain ⟨u, v, huv, huD, hvD, hsExact⟩ :=
    D.exact_two_neighbors_of_mem hsD
  have hleftPair := (hsExact left hleftD).1 hsLeft
  have hrightPair := (hsExact right hrightD).1 hsRight
  have hsCarrierExact : ∀ z : V, z ∈ D.carrier →
      (G.Adj s z ↔ z = left ∨ z = right) := by
    intro z hz
    rcases hleftPair with hlu | hlv <;>
      rcases hrightPair with hru | hrv
    · exact (hleft_ne_right (hlu.trans hru.symm)).elim
    · simpa [← hlu, ← hrv] using hsExact z hz
    · simpa [← hlv, ← hru, or_comm] using hsExact z hz
    · exact (hleft_ne_right (hlv.trans hrv.symm)).elim
  have hprevD : C.a (C.prev i) ∈ D.carrier := by
    rw [hcarrier]
    right
    refine ⟨C.a_mem_carrier (C.prev i), ?_⟩
    simpa only [Set.mem_singleton_iff] using C.a_ne_prev i
  have hsPrev : ¬G.Adj s (C.a (C.prev i)) := by
    intro h
    rcases (hsCarrierExact _ hprevD).1 h with hleft | hright
    · exact C.color_disjoint (C.prev i) i hleft
    · exact C.color_disjoint (C.prev i) (C.next i) hright
  have hsOriginal : G.Adj s (C.a i) := by
    rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
        hsLeft (C.adj_a_b i).symm (C.adj_a_prev_b i).symm
        (fun h => hsOutside (h ▸ C.a_mem_carrier i))
        (fun h => hsOutside (h ▸ C.a_mem_carrier (C.prev i)))
        (C.a_ne_prev i).symm (C.adj_aa i (C.prev i)) with h | h
    · exact h
    · exact (hsPrev h).elim
  refine
    { outside := hsOutside
      adj_iff := ?_ }
  intro z hz
  constructor
  · intro hsz
    by_cases hzi : z = C.a i
    · exact Or.inl hzi
    · right
      have hzD : z ∈ D.carrier := by
        rw [hcarrier]
        exact Or.inr ⟨hz, by simpa using hzi⟩
      exact (C.adj_a_iff_of_mem hz).2
        ((hsCarrierExact z hzD).1 hsz)
  · rintro (rfl | hiz)
    · exact hsOriginal
    · rcases (C.adj_a_iff_of_mem hz).1 hiz with rfl | rfl
      · exact hsLeft
      · exact hsRight

end EvenHoleLabeling

/-- In a claw-free graph, all retained events represented by one Boolean
bubble-wand arc determine the same even-hole deformation class. -/
theorem bubbleWandEventClassUnique_of_isClawFree
    {K : Set V} (hclaw : G.IsClawFree) :
    BubbleWandEventClassUnique G K := by
  intro P Q bubble bubble' E E'
  by_cases hbb : bubble = bubble'
  · subst bubble'
    rfl
  have hbP : bubble ∉ P.originalCarrier := by
    intro hb
    rw [E.source] at hb
    rcases hb with ⟨q, hq⟩
    apply E.wand.outside
    exact ⟨q, hq.trans E.bubble.symm⟩
  have hbP' : bubble' ∉ P.originalCarrier := by
    intro hb
    rw [E'.source] at hb
    rcases hb with ⟨q, hq⟩
    apply E'.wand.outside
    exact ⟨q, hq.trans E'.bubble.symm⟩
  have hbmem : bubble ∈ E.labeling.carrier := by
    rw [E.labelCarrier_eq_canonical]
    exact Or.inr rfl
  rcases hbmem with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hbOutside : bubble' ∉ E.labeling.carrier := by
      rw [E.labelCarrier_eq_canonical]
      simp [bubbleWandArcHoopCarrier, hbP', Ne.symm hbb]
    have hcarrier : E'.labeling.carrier =
        E.labeling.deformedCarrier bubble' i := by
      rw [E'.labelCarrier_eq_canonical]
      unfold EvenHoleLabeling.deformedCarrier
      rw [E.labelCarrier_eq_canonical]
      ext v
      simp [bubbleWandArcHoopCarrier, hi, hbP,
        Set.mem_insert_iff]
      constructor
      · rintro (h | h)
        · exact Set.mem_insert_iff.2 (Or.inl h)
        · exact Set.mem_insert_iff.2 (Or.inr h)
      · intro h
        exact Set.mem_insert_iff.1 h
    have hclone := E.labeling.cloneAt_of_shared_deletion
      E'.labeling bubble' i hclaw hbOutside hcarrier
    apply evenHoleDeformationClassOf_eq_of_step
    exact ⟨E.halfLength, E.labeling, bubble', i, hclone,
      Or.inl ⟨E.labelCarrier_eq_canonical.symm,
        E'.labelCarrier_eq_canonical.symm.trans hcarrier⟩⟩
  · let C := E.labeling.swapColors
    have hi' : C.a i = bubble := by
      exact hi
    have hbOutside : bubble' ∉ C.carrier := by
      rw [EvenHoleLabeling.swapColors_carrier,
        E.labelCarrier_eq_canonical]
      simp [bubbleWandArcHoopCarrier, hbP', Ne.symm hbb]
    have hcarrier : E'.labeling.carrier =
        C.deformedCarrier bubble' i := by
      rw [E'.labelCarrier_eq_canonical]
      unfold EvenHoleLabeling.deformedCarrier
      rw [show C.carrier = E.labeling.carrier by simp [C]]
      rw [E.labelCarrier_eq_canonical]
      ext v
      simp [bubbleWandArcHoopCarrier, hi', hbP,
        Set.mem_insert_iff]
      constructor
      · rintro (h | h)
        · exact Set.mem_insert_iff.2 (Or.inl h)
        · exact Set.mem_insert_iff.2 (Or.inr h)
      · intro h
        exact Set.mem_insert_iff.1 h
    have hclone := C.cloneAt_of_shared_deletion
      E'.labeling bubble' i hclaw hbOutside hcarrier
    apply evenHoleDeformationClassOf_eq_of_step
    exact ⟨E.halfLength, C, bubble', i, hclone,
      Or.inl ⟨by
          rw [EvenHoleLabeling.swapColors_carrier,
            E.labelCarrier_eq_canonical],
        E'.labelCarrier_eq_canonical.symm.trans hcarrier⟩⟩

namespace EqE1ClassWeightData

/-- Event-class uniqueness is automatic in the paper's claw-free setting,
so the finite target-count invariant is the sole remaining local graph input
for the canonical Eq. (E1) weights. -/
theorem canonical_toEqE1WeightData_isDeformationCompatible_of_targetCount
    {K : Set V} {R : Type*} [Fintype V] [Field R]
    (hclaw : G.IsClawFree)
    (hcount : CanonicalBubbleWandTargetCountInvariant G K)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R) :
    (canonicalEqE1ClassWeightData G K R coupling
      generalizedCycleEigenvalue).toEqE1WeightData.IsDeformationCompatible :=
  canonical_toEqE1WeightData_isDeformationCompatible
    hclaw (bubbleWandEventClassUnique_of_isClawFree hclaw)
      hcount coupling generalizedCycleEigenvalue

end EqE1ClassWeightData

/-- Canonical local Eq. (E1) prefix-entry invariance with the event-choice
ambiguity discharged from claw-freeness. -/
theorem RootedInducedPath.canonical_eqE1_deformedPrefix_weight_of_targetCount
    {K : Set V} {R : Type*} [Fintype V] [Field R]
    (hK : G.IsClique K) (hclaw : G.IsClawFree)
    (hcount : CanonicalBubbleWandTargetCountInvariant G K)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R)
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val) :
    let W := (canonicalEqE1ClassWeightData G K R coupling
      generalizedCycleEigenvalue).toEqE1WeightData
    eqE1WeightedAdjacency G K W
        (P.initialSegment r) (P.initialSegment s) =
      eqE1WeightedAdjacency G K W
        (P.deformedPrefix h r) (P.deformedPrefix h s) := by
  exact RootedInducedPath.canonical_eqE1_deformedPrefix_weight
    hK hclaw (bubbleWandEventClassUnique_of_isClawFree hclaw)
      hcount coupling generalizedCycleEigenvalue P h hj r s hir his

end SimpleGraph
