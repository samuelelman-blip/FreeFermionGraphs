import FreeFermionGraphs.Lemma11BOutsideOrdinaryPredecessor

/-!
# Lemma 11(b): a common C_b neighbor in the ordinary outside branch

The preceding theorem isolates the last ordinary obstruction: the other
prime-hole neighbor at the preceding introduced vertex may also neighbor
the preceding removed vertex.  Even in this case, claw-freeness forces that
prime neighbor to meet one of the two persistent b-vertices.  The current
dependent vertex meets both, so the two vertices already lie in the same
fixed-pairing component through a named C_b witness.

Thus the remaining ordinary task is purely the two-step Definition 20
attachment; component connectivity is discharged here.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The ordinary prime-hole candidate always shares a C_b-neighbor with
the current dependent vertex.  It is either already Definition 20
dependent one step earlier, or it is adjacent to that step's removed
vertex, the remaining two-step obstruction. -/
theorem ordinary_prime_neighbor_with_commonB_or_previousDefinition20
    {k kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierOverlapColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    ∃ u' w : V,
      u' ∈ Cprime ∧
      u' ∈ O.Cd ∧
      G.Adj u' (D.deformation.step ⟨t, ht⟩).introduced ∧
      u' ≠ u ∧
      ¬G.Adj u' u ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w ∧
      ((u' =
          (D.deformation.step ⟨t, ht⟩).before.vertex
            (D.deformation.step ⟨t, ht⟩).removedIndex ∨
        G.Adj u'
          ((D.deformation.step ⟨t, ht⟩).before.vertex
            (D.deformation.step ⟨t, ht⟩).removedIndex)) ∨
        D.Definition20DependentAt t u') := by
  obtain ⟨u', hu'Prime, hu'Cd, hu'Introduced,
      hu'NeU, hu'NotU, hcandidate⟩ :=
    D.ordinary_prime_neighbor_or_previousDefinition20CommonNeighbor
      M A P L hclaw hcolors horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  rcases hcandidate with hu'Removed |
      ⟨w, hu'Definition20, hwCb, hu'w, huw⟩
  · let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
    let C : EvenHoleLabeling G k := A.labeling previous
    let r : Fin k := A.removedAIndex previous
    have huBoth :
        G.Adj u (C.b r) ∧
          G.Adj u (C.b (C.next r)) := by
      simpa [C, r, previous] using
        D.adj_two_persistent_b_of_adj_previous_introduced
          M A L hclaw hcolors horder hopposite
          hu huOutside hnotAnti ht hts huPreviousIntroduced
    have hbBefore :
        C.b r ∈
          Set.range (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.b_mem_carrier r
    have hbNextBefore :
        C.b (C.next r) ∈
          Set.range (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.b_mem_carrier (C.next r)
    have hremovedB :
        G.Adj
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex)
          (C.b r) := by
      rw [A.removed_eq previous]
      exact C.adj_a_b r
    have hremovedBNext :
        G.Adj
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex)
          (C.b (C.next r)) := by
      rw [A.removed_eq previous]
      exact C.adj_a_b_next r
    have hbCb : C.b r ∈ O.Cb := by
      rcases (M.stepGeometry previous).before_subset hbBefore with
        hbCa | hbCb
      · exact ((M.stepGeometry previous).ca_independent
          (M.stepGeometry previous).removed_ca hbCa hremovedB).elim
      · exact hbCb
    have hbNextCb : C.b (C.next r) ∈ O.Cb := by
      rcases (M.stepGeometry previous).before_subset hbNextBefore with
        hbNextCa | hbNextCb
      · exact ((M.stepGeometry previous).ca_independent
          (M.stepGeometry previous).removed_ca hbNextCa
          hremovedBNext).elim
      · exact hbNextCb
    rcases hu'Removed with hu'EqRemoved | hu'Removed
    · have hu'B : G.Adj u' (C.b r) := by
        rw [hu'EqRemoved]
        exact hremovedB
      exact
        ⟨u', C.b r, hu'Prime, hu'Cd, hu'Introduced,
          hu'NeU, hu'NotU, hbCb, hu'B, huBoth.1,
          Or.inl (Or.inl hu'EqRemoved)⟩
    have hu'NotCb : u' ∉ O.Cb :=
      (hcolors.not_mem_cb_cc_of_mem_cd hu'Prime hu'Cd).1
    have hu'NeB : u' ≠ C.b r := by
      intro heq
      apply hu'NotCb
      rw [heq]
      exact hbCb
    have hu'NeBNext : u' ≠ C.b (C.next r) := by
      intro heq
      apply hu'NotCb
      rw [heq]
      exact hbNextCb
    have hbNeBNext : C.b r ≠ C.b (C.next r) :=
      (C.b_ne_next r).symm
    have hu'Introduced' :
        G.Adj u' (D.deformation.step previous).introduced := by
      simpa [previous] using hu'Introduced
    rcases hclaw hu'Introduced'.symm
        (A.cloneAt previous).adj_b
        (A.cloneAt previous).adj_b_next
        hu'NeB hu'NeBNext hbNeBNext with
      hu'B | hu'BNext | hbBNext
    · exact
        ⟨u', C.b r, hu'Prime, hu'Cd, hu'Introduced,
          hu'NeU, hu'NotU, hbCb, hu'B, huBoth.1,
          Or.inl (Or.inr hu'Removed)⟩
    · exact
        ⟨u', C.b (C.next r), hu'Prime, hu'Cd,
          hu'Introduced, hu'NeU, hu'NotU, hbNextCb,
          hu'BNext, huBoth.2, Or.inl (Or.inr hu'Removed)⟩
    · exact (C.adj_bb r (C.next r) hbBNext).elim
  · exact
      ⟨u', w, hu'Prime, hu'Cd, hu'Introduced,
        hu'NeU, hu'NotU, hwCb, hu'w, huw,
        Or.inr hu'Definition20⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
