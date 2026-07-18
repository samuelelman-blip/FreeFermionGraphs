import FreeFermionGraphs.Lemma11BBase

/-!
# Lemma 11(b): the four-neighbor commuting case

Lemma 7 restricts a commuting external vertex to zero, two, or four
neighbors on an induced path.  Consequently, once the local geometry in
Lemma 11(b) supplies a lower bound of three neighbors, the count is exactly
four.  This module also packages that reduction as the degree-four rule
needed by `Lemma11BLocalData`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- A commuting external vertex with at least three path neighbors has
exactly four path neighbors. -/
theorem commutesWith_count_eq_four_of_three_le
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree)
    {u : V}
    (huOutside : u ∉ Set.range P.vertex)
    (hcomm : P.CommutesWith u)
    (hthree : 3 ≤ (P.neighborIndexSet u).ncard) :
    (P.neighborIndexSet u).ncard = 4 := by
  rcases P.commutesWith_count_eq_zero_or_two_or_four
      hclaw huOutside hcomm with hzero | htwo | hfour
  · omega
  · omega
  · exact hfour

/-- The same reduction stated from non-anticommutation, matching the
hypothesis used in Lemma 11(b). -/
theorem count_eq_four_of_not_anticommutesWith_of_three_le
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree)
    {u : V}
    (huOutside : u ∉ Set.range P.vertex)
    (hnotAnti : ¬P.AnticommutesWith u)
    (hthree : 3 ≤ (P.neighborIndexSet u).ncard) :
    (P.neighborIndexSet u).ncard = 4 := by
  have hcomm : P.CommutesWith u := by
    rcases P.commutesWith_or_anticommutesWith u with hcomm | hanti
    · exact hcomm
    · exact (hnotAnti hanti).elim
  exact P.commutesWith_count_eq_four_of_three_le
    hclaw huOutside hcomm hthree

/-- Convert the path-count reduction into the degree-four local rule used
by the abstract Lemma 11(b) assembly.  The remaining neighborhood analysis
supplies `hthree` and identifies its degree with this path count through
`hdegreeCount`. -/
theorem lemma11b_degree_four_rule_of_path_count
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree)
    (U : Nat → Set V) (degree : Nat → V → Nat)
    (houtside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → u ∉ Set.range P.vertex)
    (hthree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ¬P.AnticommutesWith u →
        3 ≤ (P.neighborIndexSet u).ncard)
    (hdegreeCount : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s →
        degree s u = (P.neighborIndexSet u).ncard) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ¬P.AnticommutesWith u →
        degree s u = 4 := by
  intro s u hu hnotAnti
  calc
    degree s u = (P.neighborIndexSet u).ncard :=
      hdegreeCount hu
    _ = 4 :=
      P.count_eq_four_of_not_anticommutesWith_of_three_le
        hclaw (houtside hu) hnotAnti (hthree hu hnotAnti)

end IndexedInducedPath

end SimpleGraph
