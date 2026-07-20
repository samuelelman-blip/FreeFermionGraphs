import FreeFermionGraphs.Corollaries45
import FreeFermionGraphs.Lemma11BOrdinaryPersistentNeighbors
import FreeFermionGraphs.Lemma11BPrimeHoleInPathDescent

/-!
# Lemma 11(b): the ordinary outside predecessor

In the ordinary outside-path branch, a commuting dependent vertex is
adjacent to the preceding introduced vertex.  The prime hole supplies its
other neighbor at that vertex.  If that neighbor misses the preceding
removed vertex, Corollary 4 and the two persistent active-hole b-neighbors
give the one-step Definition 20 predecessor and its common C_b witness.

The only unresolved alternative is now explicit: the extra prime-hole
neighbor may itself be adjacent to the preceding removed vertex.  This is
the paper's remaining two-step obstruction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- In the ordinary outside branch, the extra prime-hole neighbor either
meets the preceding removed vertex (the remaining two-step obstruction) or
already gives a Definition 20 predecessor one step earlier, sharing a
C_b-neighbor with the current dependent vertex. -/
theorem ordinary_prime_neighbor_or_previousDefinition20CommonNeighbor
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
    ∃ u' : V,
      u' ∈ Cprime ∧
      u' ∈ O.Cd ∧
      G.Adj u' (D.deformation.step ⟨t, ht⟩).introduced ∧
      u' ≠ u ∧
      ¬G.Adj u' u ∧
      ((u' =
          (D.deformation.step ⟨t, ht⟩).before.vertex
            (D.deformation.step ⟨t, ht⟩).removedIndex ∨
        G.Adj u'
          ((D.deformation.step ⟨t, ht⟩).before.vertex
            (D.deformation.step ⟨t, ht⟩).removedIndex)) ∨
        ∃ w : V,
          D.Definition20DependentAt t u' ∧
          w ∈ O.Cb ∧
          G.Adj u' w ∧
          G.Adj u w) := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have huCurrent :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huPrime : u ∈ Cprime :=
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huCurrent).1
  obtain ⟨u', hu'Prime, hu'Introduced, hu'NeU, hu'NotU⟩ :=
    P.exists_other_prime_neighbor
      previous huPrime (by
        simpa [previous] using huPreviousIntroduced)
  have hu'Cd : u' ∈ O.Cd := by
    rcases (M.stepGeometry previous).prime_subset hu'Prime with
      hu'Cc | hu'Cd
    · exact ((M.stepGeometry previous).base.cc_independent
        hu'Cc (M.stepGeometry previous).base.introduced_cc
        hu'Introduced).elim
    · exact hu'Cd
  refine ⟨u', hu'Prime, hu'Cd, ?_, hu'NeU, hu'NotU, ?_⟩
  · simpa [previous] using hu'Introduced
  by_cases hu'EqRemoved :
      u' =
        (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex
  · exact Or.inl (Or.inl (by simpa [previous] using hu'EqRemoved))
  by_cases hu'Removed :
      G.Adj u'
        ((D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex)
  · exact Or.inl (Or.inr (by simpa [previous] using hu'Removed))
  · apply Or.inr
    have hu'NeRemoved :
        u' ≠
          (D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex := by
      exact hu'EqRemoved
    have hu'Step :
        u' ∈ (D.deformation.step previous).dependentSet := by
      exact
        (ConcreteDeformationStep.mem_dependentSet
          (D.deformation.step previous)).2
          ⟨hu'Prime, hu'Introduced, hu'NeRemoved, hu'Removed⟩
    have hu'Definition20 :
        D.Definition20DependentAt t u' := by
      refine ⟨ht, hu'Prime, ?_, ?_, ?_⟩
      · simpa [previous] using hu'Introduced
      · simpa [previous] using hu'NeRemoved
      · simpa [previous] using hu'Removed
    let C : EvenHoleLabeling G k := A.labeling previous
    let r : Fin k := A.removedAIndex previous
    have hu'Outside :
        u' ∉ Set.insert (D.deformation.step previous).introduced
          C.carrier := by
      simpa [C, A.carrier_eq previous] using
        M.outsideHole previous hu'Step
    obtain ⟨earlier, hearlier, _huEarlierOriginal,
        _huNotEarlierClone⟩ :=
      D.earlier_original_adj_and_clone_not_adj_of_adj_previous_introduced
        M L hclaw horder hopposite
        hu huOutside hnotAnti ht hts huPreviousIntroduced
    have hep : earlier.val + 1 = previous.val := by
      simpa [previous] using hearlier
    have hpc : previous.val + 1 = current.val := by
      dsimp [previous, current]
      omega
    have hk : 2 < k :=
      D.two_lt_halfLength_of_three_consecutive_steps
        A L hep hpc
    have huBoth :
        G.Adj u (C.b r) ∧
          G.Adj u (C.b (C.next r)) := by
      simpa [C, r, previous] using
        D.adj_two_persistent_b_of_adj_previous_introduced
          M A L hclaw hcolors horder hopposite
          hu huOutside hnotAnti ht hts huPreviousIntroduced
    have hu'NotOriginal :
        ¬G.Adj u' (C.a r) := by
      simpa [C, r, A.removed_eq previous] using hu'Removed
    have hu'B :=
      (A.cloneAt previous).corollary4
        hclaw hk hu'Outside
        (Or.inl ⟨hu'Introduced, hu'NotOriginal⟩)
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
    rcases hu'B with ⟨hu'B, _hu'NotBNext⟩ |
        ⟨_hu'NotB, hu'BNext⟩
    · exact
        ⟨C.b r, hu'Definition20, hbCb, hu'B, huBoth.1⟩
    · exact
        ⟨C.b (C.next r), hu'Definition20, hbNextCb,
          hu'BNext, huBoth.2⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
