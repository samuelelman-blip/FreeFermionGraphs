import FreeFermionGraphs.Lemma11BInPathFinalDegree

/-!
# Lemma 11(b): outside-path neighbor count

A dependent vertex is adjacent to the vertex introduced at its deformation
step, and Definition 19 places that introduced vertex on the common active
path. Hence its active-path neighbor set is nonempty.

If the dependent vertex commutes with the active path, parity together with
the induced-path classification of Lemma 7 leaves only two or four path
neighbors. This is the first reduction in the remaining outside-path branch
of Lemma 11(b).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A dependent vertex's active-path neighbor set is nonempty: it contains
the path index of the vertex introduced at its own step. -/
theorem one_le_path_neighbor_count_of_mem_dependentAt
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    1 ≤ (D.path.neighborIndexSet u).ncard := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [i] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huIntroduced :
      G.Adj u (D.deformation.step i).introduced :=
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step i)).1 huStep).2.1
  have hindex :
      L.introducedPathIndex i ∈
        D.path.neighborIndexSet u := by
    change G.Adj u
      (D.path.vertex (L.introducedPathIndex i))
    rw [L.introduced_eq i]
    exact huIntroduced
  have hsubset :
      ({L.introducedPathIndex i} :
        Set (Fin D.path.card)) ⊆
        D.path.neighborIndexSet u := by
    intro q hq
    simpa using hq ▸ hindex
  calc
    1 = ({L.introducedPathIndex i} :
        Set (Fin D.path.card)).ncard := by simp
    _ ≤ (D.path.neighborIndexSet u).ncard :=
      Set.ncard_le_ncard hsubset

/-- In the outside-path commuting branch, Lemma 7 and parity force exactly
two or four active-path neighbors. -/
theorem outside_path_neighbor_count_eq_two_or_four
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    (D.path.neighborIndexSet u).ncard = 2 ∨
      (D.path.neighborIndexSet u).ncard = 4 := by
  have hcomm : D.path.CommutesWith u := by
    rcases D.path.commutesWith_or_anticommutesWith u with
      hcomm | hanti
    · exact hcomm
    · exact (hnotAnti hanti).elim
  have hpositive :
      1 ≤ (D.path.neighborIndexSet u).ncard :=
    D.one_le_path_neighbor_count_of_mem_dependentAt L hu
  rcases
      D.path.commutesWith_count_eq_zero_or_two_or_four
        hclaw huOutside hcomm with
    hzero | htwo | hfour
  · omega
  · exact Or.inl htwo
  · exact Or.inr hfour

/-- Therefore the outside-path commuting branch contains two explicitly
distinct active-path neighbors. -/
theorem exists_two_distinct_path_neighbors_of_outside_commuting
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    ∃ p q : Fin D.path.card,
      p ≠ q ∧
      G.Adj u (D.path.vertex p) ∧
      G.Adj u (D.path.vertex q) := by
  rcases D.outside_path_neighbor_count_eq_two_or_four
      L hclaw hu huOutside hnotAnti with htwo | hfour
  · obtain ⟨p, q, hpq, hset⟩ :=
      Set.ncard_eq_two.mp htwo
    refine ⟨p, q, hpq, ?_, ?_⟩
    · change p ∈ D.path.neighborIndexSet u
      rw [hset]
      simp
    · change q ∈ D.path.neighborIndexSet u
      rw [hset]
      simp
  · obtain ⟨p, q, r, t, hpq, hpr, hpt,
      hqr, hqt, hrt, hset⟩ :=
      Set.ncard_eq_four.mp hfour
    refine ⟨p, q, hpq, ?_, ?_⟩
    · change p ∈ D.path.neighborIndexSet u
      rw [hset]
      simp
    · change q ∈ D.path.neighborIndexSet u
      rw [hset]
      simp

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
