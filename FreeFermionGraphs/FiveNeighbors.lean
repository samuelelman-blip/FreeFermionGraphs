import FreeFermionGraphs.FourNeighbors

/-!
# Five or more external neighbors of induced paths and holes

This module proves the core cardinality-five and upper-bound step in
Lemma 7.  Five distinct external neighbors induce a five-cycle, while six
distinct external neighbors are impossible.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Between one and two of three possible incident edges are present. -/
def OneOrTwoOfThree (x y z : Prop) : Prop :=
  ExactlyOneOfThree x y z ∨ ExactlyTwoOfThree x y z

/-- Exactly two of four possible incident edges are present. -/
def ExactlyTwoOfFour (w x y z : Prop) : Prop :=
  (w ∧ x ∧ ¬y ∧ ¬z) ∨
    (w ∧ ¬x ∧ y ∧ ¬z) ∨
    (w ∧ ¬x ∧ ¬y ∧ z) ∨
    (¬w ∧ x ∧ y ∧ ¬z) ∨
    (¬w ∧ x ∧ ¬y ∧ z) ∨
    (¬w ∧ ¬x ∧ y ∧ z)

/-- The indicator sum of four propositions satisfying `ExactlyTwoOfFour`
is two. -/
theorem exactlyTwoOfFour_indicator_eq_two
    {w x y z : Prop}
    [Decidable w] [Decidable x] [Decidable y] [Decidable z]
    (h : ExactlyTwoOfFour w x y z) :
    (if w then 1 else 0) + (if x then 1 else 0) +
      (if y then 1 else 0) + (if z then 1 else 0) = 2 := by
  rcases h with ⟨hw, hx, hy, hz⟩ | ⟨hw, hx, hy, hz⟩ |
    ⟨hw, hx, hy, hz⟩ | ⟨hw, hx, hy, hz⟩ |
    ⟨hw, hx, hy, hz⟩ | ⟨hw, hx, hy, hz⟩
  · simp [hw, hx, hy, hz]
  · simp [hw, hx, hy, hz]
  · simp [hw, hx, hy, hz]
  · simp [hw, hx, hy, hz]
  · simp [hw, hx, hy, hz]
  · simp [hw, hx, hy, hz]

/-- The ten possible edges on `p`, `q`, `r`, `s`, and `t` give every
vertex degree two.  This is precisely the five-cycle case. -/
def FiveNeighborCycleCase
    (pq pr ps pt qr qs qt rs rt st : Prop) : Prop :=
  ExactlyTwoOfFour pq pr ps pt ∧
    ExactlyTwoOfFour pq qr qs qt ∧
    ExactlyTwoOfFour pr qr rs rt ∧
    ExactlyTwoOfFour ps qs rs st ∧
    ExactlyTwoOfFour pt qt rt st

/-- Every vertex in one of the four-neighbor shapes has degree one or two. -/
theorem FourNeighborDegreeShape.degree_bounds
    {pq pr ps qr qs rs : Prop}
    (h : FourNeighborDegreeShape pq pr ps qr qs rs) :
    OneOrTwoOfThree pq pr ps ∧
      OneOrTwoOfThree pq qr qs ∧
      OneOrTwoOfThree pr qr rs ∧
      OneOrTwoOfThree ps qs rs := by
  simp only [FourNeighborDegreeShape, FourNeighborTwoEdgesCase,
    FourNeighborPathCase, FourNeighborCycleCase] at h
  unfold OneOrTwoOfThree
  tauto

/-- If every three-element restriction of four propositions contains one or
two true propositions, then exactly two of the four are true. -/
theorem exactlyTwoOfFour_of_triple_bounds
    {w x y z : Prop}
    (hwxy : OneOrTwoOfThree w x y)
    (hwxz : OneOrTwoOfThree w x z)
    (hwyz : OneOrTwoOfThree w y z)
    (hxyz : OneOrTwoOfThree x y z) :
    ExactlyTwoOfFour w x y z := by
  classical
  have hwxy' :
      (if w then 1 else 0) + (if x then 1 else 0) +
          (if y then 1 else 0) = 1 ∨
        (if w then 1 else 0) + (if x then 1 else 0) +
          (if y then 1 else 0) = 2 := by
    rcases hwxy with hwxy | hwxy
    · exact Or.inl (exactlyOneOfThree_indicator_eq_one hwxy)
    · exact Or.inr (exactlyTwoOfThree_indicator_eq_two hwxy)
  have hwxz' :
      (if w then 1 else 0) + (if x then 1 else 0) +
          (if z then 1 else 0) = 1 ∨
        (if w then 1 else 0) + (if x then 1 else 0) +
          (if z then 1 else 0) = 2 := by
    rcases hwxz with hwxz | hwxz
    · exact Or.inl (exactlyOneOfThree_indicator_eq_one hwxz)
    · exact Or.inr (exactlyTwoOfThree_indicator_eq_two hwxz)
  have hwyz' :
      (if w then 1 else 0) + (if y then 1 else 0) +
          (if z then 1 else 0) = 1 ∨
        (if w then 1 else 0) + (if y then 1 else 0) +
          (if z then 1 else 0) = 2 := by
    rcases hwyz with hwyz | hwyz
    · exact Or.inl (exactlyOneOfThree_indicator_eq_one hwyz)
    · exact Or.inr (exactlyTwoOfThree_indicator_eq_two hwyz)
  have hxyz' :
      (if x then 1 else 0) + (if y then 1 else 0) +
          (if z then 1 else 0) = 1 ∨
        (if x then 1 else 0) + (if y then 1 else 0) +
          (if z then 1 else 0) = 2 := by
    rcases hxyz with hxyz | hxyz
    · exact Or.inl (exactlyOneOfThree_indicator_eq_one hxyz)
    · exact Or.inr (exactlyTwoOfThree_indicator_eq_two hxyz)
  have hsum :
      (if w then 1 else 0) + (if x then 1 else 0) +
        (if y then 1 else 0) + (if z then 1 else 0) = 2 := by
    omega
  by_cases hw : w <;>
    by_cases hx : x <;>
    by_cases hy : y <;>
    by_cases hz : z <;>
    simp_all [ExactlyTwoOfFour]

/-- If all five four-vertex restrictions have one of the degree shapes from
the cardinality-four classification, the five-vertex graph is a cycle. -/
theorem fiveNeighborCycleCase_of_four_shapes
    {pq pr ps pt qr qs qt rs rt st : Prop}
    (hpqrs : FourNeighborDegreeShape pq pr ps qr qs rs)
    (hpqrt : FourNeighborDegreeShape pq pr pt qr qt rt)
    (hpqst : FourNeighborDegreeShape pq ps pt qs qt st)
    (hprst : FourNeighborDegreeShape pr ps pt rs rt st)
    (hqrst : FourNeighborDegreeShape qr qs qt rs rt st) :
    FiveNeighborCycleCase pq pr ps pt qr qs qt rs rt st := by
  obtain ⟨hp_qrs, hq_prs, hr_pqs, hs_pqr⟩ := hpqrs.degree_bounds
  obtain ⟨hp_qrt, hq_prt, hr_pqt, ht_pqr⟩ := hpqrt.degree_bounds
  obtain ⟨hp_qst, hq_pst, hs_pqt, ht_pqs⟩ := hpqst.degree_bounds
  obtain ⟨hp_rst, hr_pst, hs_prt, ht_prs⟩ := hprst.degree_bounds
  obtain ⟨hq_rst, hr_qst, hs_qrt, ht_qrs⟩ := hqrst.degree_bounds
  exact ⟨
    exactlyTwoOfFour_of_triple_bounds hp_qrs hp_qrt hp_qst hp_rst,
    exactlyTwoOfFour_of_triple_bounds hq_prs hq_prt hq_pst hq_rst,
    exactlyTwoOfFour_of_triple_bounds hr_pqs hr_pqt hr_pst hr_qst,
    exactlyTwoOfFour_of_triple_bounds hs_pqr hs_pqt hs_prt hs_qrt,
    exactlyTwoOfFour_of_triple_bounds ht_pqr ht_pqs ht_prs ht_qrs⟩

/-- Cardinality-five path case of Lemma 7: five distinct external neighbors
of an indexed induced path induce a five-cycle. -/
theorem IndexedInducedPath.five_external_neighbors_induce_cycle
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {p q r s t : Fin P.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpt : p ≠ t)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqt : q ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hjp : G.Adj j (P.vertex p)) (hjq : G.Adj j (P.vertex q))
    (hjr : G.Adj j (P.vertex r)) (hjs : G.Adj j (P.vertex s))
    (hjt : G.Adj j (P.vertex t)) :
    FiveNeighborCycleCase
      (G.Adj (P.vertex p) (P.vertex q))
      (G.Adj (P.vertex p) (P.vertex r))
      (G.Adj (P.vertex p) (P.vertex s))
      (G.Adj (P.vertex p) (P.vertex t))
      (G.Adj (P.vertex q) (P.vertex r))
      (G.Adj (P.vertex q) (P.vertex s))
      (G.Adj (P.vertex q) (P.vertex t))
      (G.Adj (P.vertex r) (P.vertex s))
      (G.Adj (P.vertex r) (P.vertex t))
      (G.Adj (P.vertex s) (P.vertex t)) := by
  apply fiveNeighborCycleCase_of_four_shapes
  · exact P.four_external_neighbors_degree_shape hclaw hjP
      hpq hpr hps hqr hqs hrs hjp hjq hjr hjs
  · exact P.four_external_neighbors_degree_shape hclaw hjP
      hpq hpr hpt hqr hqt hrt hjp hjq hjr hjt
  · exact P.four_external_neighbors_degree_shape hclaw hjP
      hpq hps hpt hqs hqt hst hjp hjq hjs hjt
  · exact P.four_external_neighbors_degree_shape hclaw hjP
      hpr hps hpt hrs hrt hst hjp hjr hjs hjt
  · exact P.four_external_neighbors_degree_shape hclaw hjP
      hqr hqs hqt hrs hrt hst hjq hjr hjs hjt

/-- Cardinality-five hole case of Lemma 7: five distinct external neighbors
of an indexed induced hole induce a five-cycle. -/
theorem IndexedInducedHole.five_external_neighbors_induce_cycle
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) {p q r s t : Fin C.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpt : p ≠ t)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqt : q ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hjp : G.Adj j (C.vertex p)) (hjq : G.Adj j (C.vertex q))
    (hjr : G.Adj j (C.vertex r)) (hjs : G.Adj j (C.vertex s))
    (hjt : G.Adj j (C.vertex t)) :
    FiveNeighborCycleCase
      (G.Adj (C.vertex p) (C.vertex q))
      (G.Adj (C.vertex p) (C.vertex r))
      (G.Adj (C.vertex p) (C.vertex s))
      (G.Adj (C.vertex p) (C.vertex t))
      (G.Adj (C.vertex q) (C.vertex r))
      (G.Adj (C.vertex q) (C.vertex s))
      (G.Adj (C.vertex q) (C.vertex t))
      (G.Adj (C.vertex r) (C.vertex s))
      (G.Adj (C.vertex r) (C.vertex t))
      (G.Adj (C.vertex s) (C.vertex t)) := by
  apply fiveNeighborCycleCase_of_four_shapes
  · exact C.four_external_neighbors_degree_shape hclaw hjC
      hpq hpr hps hqr hqs hrs hjp hjq hjr hjs
  · exact C.four_external_neighbors_degree_shape hclaw hjC
      hpq hpr hpt hqr hqt hrt hjp hjq hjr hjt
  · exact C.four_external_neighbors_degree_shape hclaw hjC
      hpq hps hpt hqs hqt hst hjp hjq hjs hjt
  · exact C.four_external_neighbors_degree_shape hclaw hjC
      hpr hps hpt hrs hrt hst hjp hjr hjs hjt
  · exact C.four_external_neighbors_degree_shape hclaw hjC
      hqr hqs hqt hrs hrt hst hjq hjr hjs hjt

/-- Five Boolean edge variables cannot have exactly two true variables in
each of their five four-element restrictions. -/
theorem five_exact_two_restrictions_impossible
    {a b c d e : Prop}
    (habcd : ExactlyTwoOfFour a b c d)
    (habce : ExactlyTwoOfFour a b c e)
    (habde : ExactlyTwoOfFour a b d e)
    (hacde : ExactlyTwoOfFour a c d e)
    (hbcde : ExactlyTwoOfFour b c d e) : False := by
  classical
  have habcd' := exactlyTwoOfFour_indicator_eq_two habcd
  have habce' := exactlyTwoOfFour_indicator_eq_two habce
  have habde' := exactlyTwoOfFour_indicator_eq_two habde
  have hacde' := exactlyTwoOfFour_indicator_eq_two hacde
  have hbcde' := exactlyTwoOfFour_indicator_eq_two hbcde
  omega

/-- Six distinct external neighbors of an indexed induced path are
impossible.  This is the upper-bound part of Lemma 7 for paths. -/
theorem IndexedInducedPath.not_six_external_neighbors
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {p q r s t u : Fin P.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hpt : p ≠ t) (hpu : p ≠ u)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u)
    (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hjp : G.Adj j (P.vertex p)) (hjq : G.Adj j (P.vertex q))
    (hjr : G.Adj j (P.vertex r)) (hjs : G.Adj j (P.vertex s))
    (hjt : G.Adj j (P.vertex t)) (hju : G.Adj j (P.vertex u)) : False := by
  have hpqrst := P.five_external_neighbors_induce_cycle hclaw hjP
    hpq hpr hps hpt hqr hqs hqt hrs hrt hst hjp hjq hjr hjs hjt
  have hpqrsu := P.five_external_neighbors_induce_cycle hclaw hjP
    hpq hpr hps hpu hqr hqs hqu hrs hru hsu hjp hjq hjr hjs hju
  have hpqrtu := P.five_external_neighbors_induce_cycle hclaw hjP
    hpq hpr hpt hpu hqr hqt hqu hrt hru htu hjp hjq hjr hjt hju
  have hpqstu := P.five_external_neighbors_induce_cycle hclaw hjP
    hpq hps hpt hpu hqs hqt hqu hst hsu htu hjp hjq hjs hjt hju
  have hprstu := P.five_external_neighbors_induce_cycle hclaw hjP
    hpr hps hpt hpu hrs hrt hru hst hsu htu hjp hjr hjs hjt hju
  exact five_exact_two_restrictions_impossible
    hpqrst.1 hpqrsu.1 hpqrtu.1 hpqstu.1 hprstu.1

/-- Six distinct external neighbors of an indexed induced hole are
impossible.  This is the upper-bound part of Lemma 7 for holes. -/
theorem IndexedInducedHole.not_six_external_neighbors
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) {p q r s t u : Fin C.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hpt : p ≠ t) (hpu : p ≠ u)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u)
    (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hjp : G.Adj j (C.vertex p)) (hjq : G.Adj j (C.vertex q))
    (hjr : G.Adj j (C.vertex r)) (hjs : G.Adj j (C.vertex s))
    (hjt : G.Adj j (C.vertex t)) (hju : G.Adj j (C.vertex u)) : False := by
  have hpqrst := C.five_external_neighbors_induce_cycle hclaw hjC
    hpq hpr hps hpt hqr hqs hqt hrs hrt hst hjp hjq hjr hjs hjt
  have hpqrsu := C.five_external_neighbors_induce_cycle hclaw hjC
    hpq hpr hps hpu hqr hqs hqu hrs hru hsu hjp hjq hjr hjs hju
  have hpqrtu := C.five_external_neighbors_induce_cycle hclaw hjC
    hpq hpr hpt hpu hqr hqt hqu hrt hru htu hjp hjq hjr hjt hju
  have hpqstu := C.five_external_neighbors_induce_cycle hclaw hjC
    hpq hps hpt hpu hqs hqt hqu hst hsu htu hjp hjq hjs hjt hju
  have hprstu := C.five_external_neighbors_induce_cycle hclaw hjC
    hpr hps hpt hpu hrs hrt hru hst hsu htu hjp hjr hjs hjt hju
  exact five_exact_two_restrictions_impossible
    hpqrst.1 hpqrsu.1 hpqrtu.1 hpqstu.1 hprstu.1

end SimpleGraph
