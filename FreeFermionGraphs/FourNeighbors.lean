import FreeFermionGraphs.ThreeNeighborEndpoint

/-!
# Four external neighbors of induced paths and holes

The cardinality-four cases in Lemma 7.  Four external neighbors induce
either two disjoint edges, a path on four vertices, or a four-cycle.

We express the three cases through the degrees in the graph induced by the
four selected vertices.  Since that graph is simple, the degree patterns
`(1, 1, 1, 1)`, `(1, 1, 2, 2)`, and `(2, 2, 2, 2)` are precisely the three
configurations above.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Exactly one of three possible incident edges is present. -/
def ExactlyOneOfThree (x y z : Prop) : Prop :=
  (x ∧ ¬y ∧ ¬z) ∨ (¬x ∧ y ∧ ¬z) ∨ (¬x ∧ ¬y ∧ z)

/-- Exactly two of three possible incident edges are present. -/
def ExactlyTwoOfThree (x y z : Prop) : Prop :=
  (x ∧ y ∧ ¬z) ∨ (x ∧ ¬y ∧ z) ∨ (¬x ∧ y ∧ z)

/-- The four vertices all have degree one, so they induce two disjoint edges. -/
def FourNeighborTwoEdgesCase
    (pq pr ps qr qs rs : Prop) : Prop :=
  ExactlyOneOfThree pq pr ps ∧
    ExactlyOneOfThree pq qr qs ∧
    ExactlyOneOfThree pr qr rs ∧
    ExactlyOneOfThree ps qs rs

/-- Two vertices have degree one and two have degree two, so they induce a
path on four vertices.  The six disjuncts choose the two endpoints. -/
def FourNeighborPathCase
    (pq pr ps qr qs rs : Prop) : Prop :=
  (ExactlyOneOfThree pq pr ps ∧ ExactlyOneOfThree pq qr qs ∧
      ExactlyTwoOfThree pr qr rs ∧ ExactlyTwoOfThree ps qs rs) ∨
    (ExactlyOneOfThree pq pr ps ∧ ExactlyOneOfThree pr qr rs ∧
      ExactlyTwoOfThree pq qr qs ∧ ExactlyTwoOfThree ps qs rs) ∨
    (ExactlyOneOfThree pq pr ps ∧ ExactlyOneOfThree ps qs rs ∧
      ExactlyTwoOfThree pq qr qs ∧ ExactlyTwoOfThree pr qr rs) ∨
    (ExactlyOneOfThree pq qr qs ∧ ExactlyOneOfThree pr qr rs ∧
      ExactlyTwoOfThree pq pr ps ∧ ExactlyTwoOfThree ps qs rs) ∨
    (ExactlyOneOfThree pq qr qs ∧ ExactlyOneOfThree ps qs rs ∧
      ExactlyTwoOfThree pq pr ps ∧ ExactlyTwoOfThree pr qr rs) ∨
    (ExactlyOneOfThree pr qr rs ∧ ExactlyOneOfThree ps qs rs ∧
      ExactlyTwoOfThree pq pr ps ∧ ExactlyTwoOfThree pq qr qs)

/-- The four vertices all have degree two, so they induce a four-cycle. -/
def FourNeighborCycleCase
    (pq pr ps qr qs rs : Prop) : Prop :=
  ExactlyTwoOfThree pq pr ps ∧
    ExactlyTwoOfThree pq qr qs ∧
    ExactlyTwoOfThree pr qr rs ∧
    ExactlyTwoOfThree ps qs rs

/-- The three possible degree shapes for four external neighbors.  The six
arguments are the possible edges `pq`, `pr`, `ps`, `qr`, `qs`, and `rs`. -/
def FourNeighborDegreeShape
    (pq pr ps qr qs rs : Prop) : Prop :=
  FourNeighborTwoEdgesCase pq pr ps qr qs rs ∨
    FourNeighborPathCase pq pr ps qr qs rs ∨
    FourNeighborCycleCase pq pr ps qr qs rs

/-- A nonempty proper subset of three propositions contains exactly one or
exactly two propositions. -/
theorem exactlyOneOrTwoOfThree_of_bounds
    {x y z : Prop} (hpos : x ∨ y ∨ z) (hlt : ¬(x ∧ y ∧ z)) :
    ExactlyOneOfThree x y z ∨ ExactlyTwoOfThree x y z := by
  by_cases hx : x
  · by_cases hy : y
    · have hnz : ¬z := by
        intro hz
        exact hlt ⟨hx, hy, hz⟩
      refine Or.inr ?_
      exact Or.inl ⟨hx, hy, hnz⟩
    · by_cases hz : z
      · refine Or.inr ?_
        exact Or.inr (Or.inl ⟨hx, hy, hz⟩)
      · refine Or.inl ?_
        exact Or.inl ⟨hx, hy, hz⟩
  · by_cases hy : y
    · by_cases hz : z
      · refine Or.inr ?_
        exact Or.inr (Or.inr ⟨hx, hy, hz⟩)
      · refine Or.inl ?_
        exact Or.inr (Or.inl ⟨hx, hy, hz⟩)
    · have hz : z := by
        rcases hpos with hx' | hy' | hz
        · exact (hx hx').elim
        · exact (hy hy').elim
        · exact hz
      refine Or.inl ?_
      exact Or.inr (Or.inr ⟨hx, hy, hz⟩)

/-- The indicator sum of three propositions satisfying `ExactlyOneOfThree`
is one. -/
theorem exactlyOneOfThree_indicator_eq_one
    {x y z : Prop} [Decidable x] [Decidable y] [Decidable z]
    (h : ExactlyOneOfThree x y z) :
    (if x then 1 else 0) + (if y then 1 else 0) +
      (if z then 1 else 0) = 1 := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · simp [hx, hy, hz]
  · simp [hx, hy, hz]
  · simp [hx, hy, hz]

/-- The indicator sum of three propositions satisfying `ExactlyTwoOfThree`
is two. -/
theorem exactlyTwoOfThree_indicator_eq_two
    {x y z : Prop} [Decidable x] [Decidable y] [Decidable z]
    (h : ExactlyTwoOfThree x y z) :
    (if x then 1 else 0) + (if y then 1 else 0) +
      (if z then 1 else 0) = 2 := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · simp [hx, hy, hz]
  · simp [hx, hy, hz]
  · simp [hx, hy, hz]

/-- If every vertex in a four-vertex graph has degree at least one and at
most two, its degree pattern is one of the three cases above. -/
theorem fourNeighborDegreeShape_of_bounds
    {pq pr ps qr qs rs : Prop}
    (hp_pos : pq ∨ pr ∨ ps) (hq_pos : pq ∨ qr ∨ qs)
    (hr_pos : pr ∨ qr ∨ rs) (hs_pos : ps ∨ qs ∨ rs)
    (hp_lt_three : ¬(pq ∧ pr ∧ ps))
    (hq_lt_three : ¬(pq ∧ qr ∧ qs))
    (hr_lt_three : ¬(pr ∧ qr ∧ rs))
    (hs_lt_three : ¬(ps ∧ qs ∧ rs)) :
    FourNeighborDegreeShape pq pr ps qr qs rs := by
  classical
  have hp := exactlyOneOrTwoOfThree_of_bounds hp_pos hp_lt_three
  have hq := exactlyOneOrTwoOfThree_of_bounds hq_pos hq_lt_three
  have hr := exactlyOneOrTwoOfThree_of_bounds hr_pos hr_lt_three
  have hs := exactlyOneOrTwoOfThree_of_bounds hs_pos hs_lt_three
  rcases hp with hp1 | hp2 <;>
    rcases hq with hq1 | hq2 <;>
    rcases hr with hr1 | hr2 <;>
    rcases hs with hs1 | hs2
  · unfold FourNeighborDegreeShape FourNeighborTwoEdgesCase
    exact Or.inl ⟨hp1, hq1, hr1, hs1⟩
  · exfalso
    have hpw := exactlyOneOfThree_indicator_eq_one hp1
    have hqw := exactlyOneOfThree_indicator_eq_one hq1
    have hrw := exactlyOneOfThree_indicator_eq_one hr1
    have hsw := exactlyTwoOfThree_indicator_eq_two hs2
    omega
  · exfalso
    have hpw := exactlyOneOfThree_indicator_eq_one hp1
    have hqw := exactlyOneOfThree_indicator_eq_one hq1
    have hrw := exactlyTwoOfThree_indicator_eq_two hr2
    have hsw := exactlyOneOfThree_indicator_eq_one hs1
    omega
  · unfold FourNeighborDegreeShape FourNeighborPathCase
    exact Or.inr (Or.inl (Or.inl ⟨hp1, hq1, hr2, hs2⟩))
  · exfalso
    have hpw := exactlyOneOfThree_indicator_eq_one hp1
    have hqw := exactlyTwoOfThree_indicator_eq_two hq2
    have hrw := exactlyOneOfThree_indicator_eq_one hr1
    have hsw := exactlyOneOfThree_indicator_eq_one hs1
    omega
  · unfold FourNeighborDegreeShape FourNeighborPathCase
    exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hp1, hr1, hq2, hs2⟩)))
  · unfold FourNeighborDegreeShape FourNeighborPathCase
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl
      ⟨hp1, hs1, hq2, hr2⟩))))
  · exfalso
    have hpw := exactlyOneOfThree_indicator_eq_one hp1
    have hqw := exactlyTwoOfThree_indicator_eq_two hq2
    have hrw := exactlyTwoOfThree_indicator_eq_two hr2
    have hsw := exactlyTwoOfThree_indicator_eq_two hs2
    omega
  · exfalso
    have hpw := exactlyTwoOfThree_indicator_eq_two hp2
    have hqw := exactlyOneOfThree_indicator_eq_one hq1
    have hrw := exactlyOneOfThree_indicator_eq_one hr1
    have hsw := exactlyOneOfThree_indicator_eq_one hs1
    omega
  · unfold FourNeighborDegreeShape FourNeighborPathCase
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hq1, hr1, hp2, hs2⟩)))))
  · unfold FourNeighborDegreeShape FourNeighborPathCase
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hq1, hs1, hp2, hr2⟩))))))
  · exfalso
    have hpw := exactlyTwoOfThree_indicator_eq_two hp2
    have hqw := exactlyOneOfThree_indicator_eq_one hq1
    have hrw := exactlyTwoOfThree_indicator_eq_two hr2
    have hsw := exactlyTwoOfThree_indicator_eq_two hs2
    omega
  · unfold FourNeighborDegreeShape FourNeighborPathCase
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hr1, hs1, hp2, hq2⟩))))))
  · exfalso
    have hpw := exactlyTwoOfThree_indicator_eq_two hp2
    have hqw := exactlyTwoOfThree_indicator_eq_two hq2
    have hrw := exactlyOneOfThree_indicator_eq_one hr1
    have hsw := exactlyTwoOfThree_indicator_eq_two hs2
    omega
  · exfalso
    have hpw := exactlyTwoOfThree_indicator_eq_two hp2
    have hqw := exactlyTwoOfThree_indicator_eq_two hq2
    have hrw := exactlyTwoOfThree_indicator_eq_two hr2
    have hsw := exactlyOneOfThree_indicator_eq_one hs1
    omega
  · unfold FourNeighborDegreeShape FourNeighborCycleCase
    exact Or.inr (Or.inr ⟨hp2, hq2, hr2, hs2⟩)

/-- Among four distinct neighbors of one vertex in a claw-free graph, a
selected vertex cannot be isolated if the other three do not form a triangle. -/
theorem IsClawFree.four_neighbors_no_isolated
    (hclaw : G.IsClawFree) {j a b c d : V}
    (hja : G.Adj j a) (hjb : G.Adj j b)
    (hjc : G.Adj j c) (hjd : G.Adj j d)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hnot_triangle :
      ¬(G.Adj b c ∧ G.Adj c d ∧ G.Adj b d)) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj a d := by
  by_cases hab : G.Adj a b
  · exact Or.inl hab
  by_cases hac : G.Adj a c
  · exact Or.inr (Or.inl hac)
  by_cases had : G.Adj a d
  · exact Or.inr (Or.inr had)
  have hbc : G.Adj b c := by
    rcases hclaw hja hjb hjc hab_ne hac_ne hbc_ne with hab' | hac' | hbc'
    · exact (hab hab').elim
    · exact (hac hac').elim
    · exact hbc'
  have hcd : G.Adj c d := by
    rcases hclaw hja hjc hjd hac_ne had_ne hcd_ne with hac' | had' | hcd'
    · exact (hac hac').elim
    · exact (had had').elim
    · exact hcd'
  have hbd : G.Adj b d := by
    rcases hclaw hja hjb hjd hab_ne had_ne hbd_ne with hab' | had' | hbd'
    · exact (hab hab').elim
    · exact (had had').elim
    · exact hbd'
  exact (hnot_triangle ⟨hbc, hcd, hbd⟩).elim

/-- If `b`, `c`, and `d` are distinct neighbors of `j`, claw-freeness and
triangle-freeness prevent a fourth vertex `a` from being adjacent to all
three of them. -/
theorem IsClawFree.four_neighbors_not_degree_three
    (hclaw : G.IsClawFree) {j a b c d : V}
    (hjb : G.Adj j b) (hjc : G.Adj j c) (hjd : G.Adj j d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hnot_triangle_abc :
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c))
    (hnot_triangle_abd :
      ¬(G.Adj a b ∧ G.Adj b d ∧ G.Adj a d))
    (hnot_triangle_acd :
      ¬(G.Adj a c ∧ G.Adj c d ∧ G.Adj a d)) :
    ¬(G.Adj a b ∧ G.Adj a c ∧ G.Adj a d) := by
  rintro ⟨hab, hac, had⟩
  rcases hclaw hjb hjc hjd hbc_ne hbd_ne hcd_ne with hbc | hbd | hcd
  · exact hnot_triangle_abc ⟨hab, hbc, hac⟩
  · exact hnot_triangle_abd ⟨hab, hbd, had⟩
  · exact hnot_triangle_acd ⟨hac, hcd, had⟩

/-- Cardinality-four path case of Lemma 7: four distinct external neighbors
induce two disjoint edges, a path on four vertices, or a four-cycle. -/
theorem IndexedInducedPath.four_external_neighbors_degree_shape
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (_hjP : j ∉ Set.range P.vertex) {p q r s : Fin P.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hjp : G.Adj j (P.vertex p)) (hjq : G.Adj j (P.vertex q))
    (hjr : G.Adj j (P.vertex r)) (hjs : G.Adj j (P.vertex s)) :
    FourNeighborDegreeShape
      (G.Adj (P.vertex p) (P.vertex q))
      (G.Adj (P.vertex p) (P.vertex r))
      (G.Adj (P.vertex p) (P.vertex s))
      (G.Adj (P.vertex q) (P.vertex r))
      (G.Adj (P.vertex q) (P.vertex s))
      (G.Adj (P.vertex r) (P.vertex s)) := by
  have hpqv : P.vertex p ≠ P.vertex q := fun h => hpq (P.injective h)
  have hprv : P.vertex p ≠ P.vertex r := fun h => hpr (P.injective h)
  have hpsv : P.vertex p ≠ P.vertex s := fun h => hps (P.injective h)
  have hqrv : P.vertex q ≠ P.vertex r := fun h => hqr (P.injective h)
  have hqsv : P.vertex q ≠ P.vertex s := fun h => hqs (P.injective h)
  have hrsv : P.vertex r ≠ P.vertex s := fun h => hrs (P.injective h)
  have hp_pos := hclaw.four_neighbors_no_isolated
    hjp hjq hjr hjs hpqv hprv hpsv hqrv hqsv hrsv
    (P.not_triangle q r s)
  have hq_pos_raw := hclaw.four_neighbors_no_isolated
    hjq hjp hjr hjs hpqv.symm hqrv hqsv hprv hpsv hrsv
    (P.not_triangle p r s)
  have hr_pos_raw := hclaw.four_neighbors_no_isolated
    hjr hjp hjq hjs hprv.symm hqrv.symm hrsv hpqv hpsv hqsv
    (P.not_triangle p q s)
  have hs_pos_raw := hclaw.four_neighbors_no_isolated
    hjs hjp hjq hjr hpsv.symm hqsv.symm hrsv.symm hpqv hprv hqrv
    (P.not_triangle p q r)
  have hq_pos :
      G.Adj (P.vertex p) (P.vertex q) ∨
        G.Adj (P.vertex q) (P.vertex r) ∨
        G.Adj (P.vertex q) (P.vertex s) := by
    rcases hq_pos_raw with hqp | hqr' | hqs'
    · exact Or.inl hqp.symm
    · exact Or.inr (Or.inl hqr')
    · exact Or.inr (Or.inr hqs')
  have hr_pos :
      G.Adj (P.vertex p) (P.vertex r) ∨
        G.Adj (P.vertex q) (P.vertex r) ∨
        G.Adj (P.vertex r) (P.vertex s) := by
    rcases hr_pos_raw with hrp | hrq | hrs'
    · exact Or.inl hrp.symm
    · exact Or.inr (Or.inl hrq.symm)
    · exact Or.inr (Or.inr hrs')
  have hs_pos :
      G.Adj (P.vertex p) (P.vertex s) ∨
        G.Adj (P.vertex q) (P.vertex s) ∨
        G.Adj (P.vertex r) (P.vertex s) := by
    rcases hs_pos_raw with hsp | hsq | hsr
    · exact Or.inl hsp.symm
    · exact Or.inr (Or.inl hsq.symm)
    · exact Or.inr (Or.inr hsr.symm)
  have hp_lt_three := hclaw.four_neighbors_not_degree_three
    hjq hjr hjs hqrv hqsv hrsv
    (P.not_triangle p q r) (P.not_triangle p q s)
    (P.not_triangle p r s)
  have hq_lt_three_raw := hclaw.four_neighbors_not_degree_three
    hjp hjr hjs hprv hpsv hrsv
    (P.not_triangle q p r) (P.not_triangle q p s)
    (P.not_triangle q r s)
  have hr_lt_three_raw := hclaw.four_neighbors_not_degree_three
    hjp hjq hjs hpqv hpsv hqsv
    (P.not_triangle r p q) (P.not_triangle r p s)
    (P.not_triangle r q s)
  have hs_lt_three_raw := hclaw.four_neighbors_not_degree_three
    hjp hjq hjr hpqv hprv hqrv
    (P.not_triangle s p q) (P.not_triangle s p r)
    (P.not_triangle s q r)
  have hq_lt_three :
      ¬(G.Adj (P.vertex p) (P.vertex q) ∧
        G.Adj (P.vertex q) (P.vertex r) ∧
        G.Adj (P.vertex q) (P.vertex s)) := by
    rintro ⟨hpq', hqr', hqs'⟩
    exact hq_lt_three_raw ⟨hpq'.symm, hqr', hqs'⟩
  have hr_lt_three :
      ¬(G.Adj (P.vertex p) (P.vertex r) ∧
        G.Adj (P.vertex q) (P.vertex r) ∧
        G.Adj (P.vertex r) (P.vertex s)) := by
    rintro ⟨hpr', hqr', hrs'⟩
    exact hr_lt_three_raw ⟨hpr'.symm, hqr'.symm, hrs'⟩
  have hs_lt_three :
      ¬(G.Adj (P.vertex p) (P.vertex s) ∧
        G.Adj (P.vertex q) (P.vertex s) ∧
        G.Adj (P.vertex r) (P.vertex s)) := by
    rintro ⟨hps', hqs', hrs'⟩
    exact hs_lt_three_raw ⟨hps'.symm, hqs'.symm, hrs'.symm⟩
  exact fourNeighborDegreeShape_of_bounds hp_pos hq_pos hr_pos hs_pos
    hp_lt_three hq_lt_three hr_lt_three hs_lt_three

/-- Cardinality-four hole case of Lemma 7: four distinct external neighbors
induce two disjoint edges, a path on four vertices, or a four-cycle. -/
theorem IndexedInducedHole.four_external_neighbors_degree_shape
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (_hjC : j ∉ Set.range C.vertex) {p q r s : Fin C.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hjp : G.Adj j (C.vertex p)) (hjq : G.Adj j (C.vertex q))
    (hjr : G.Adj j (C.vertex r)) (hjs : G.Adj j (C.vertex s)) :
    FourNeighborDegreeShape
      (G.Adj (C.vertex p) (C.vertex q))
      (G.Adj (C.vertex p) (C.vertex r))
      (G.Adj (C.vertex p) (C.vertex s))
      (G.Adj (C.vertex q) (C.vertex r))
      (G.Adj (C.vertex q) (C.vertex s))
      (G.Adj (C.vertex r) (C.vertex s)) := by
  have hpqv : C.vertex p ≠ C.vertex q := fun h => hpq (C.injective h)
  have hprv : C.vertex p ≠ C.vertex r := fun h => hpr (C.injective h)
  have hpsv : C.vertex p ≠ C.vertex s := fun h => hps (C.injective h)
  have hqrv : C.vertex q ≠ C.vertex r := fun h => hqr (C.injective h)
  have hqsv : C.vertex q ≠ C.vertex s := fun h => hqs (C.injective h)
  have hrsv : C.vertex r ≠ C.vertex s := fun h => hrs (C.injective h)
  have hp_pos := hclaw.four_neighbors_no_isolated
    hjp hjq hjr hjs hpqv hprv hpsv hqrv hqsv hrsv
    (C.not_triangle q r s)
  have hq_pos_raw := hclaw.four_neighbors_no_isolated
    hjq hjp hjr hjs hpqv.symm hqrv hqsv hprv hpsv hrsv
    (C.not_triangle p r s)
  have hr_pos_raw := hclaw.four_neighbors_no_isolated
    hjr hjp hjq hjs hprv.symm hqrv.symm hrsv hpqv hpsv hqsv
    (C.not_triangle p q s)
  have hs_pos_raw := hclaw.four_neighbors_no_isolated
    hjs hjp hjq hjr hpsv.symm hqsv.symm hrsv.symm hpqv hprv hqrv
    (C.not_triangle p q r)
  have hq_pos :
      G.Adj (C.vertex p) (C.vertex q) ∨
        G.Adj (C.vertex q) (C.vertex r) ∨
        G.Adj (C.vertex q) (C.vertex s) := by
    rcases hq_pos_raw with hqp | hqr' | hqs'
    · exact Or.inl hqp.symm
    · exact Or.inr (Or.inl hqr')
    · exact Or.inr (Or.inr hqs')
  have hr_pos :
      G.Adj (C.vertex p) (C.vertex r) ∨
        G.Adj (C.vertex q) (C.vertex r) ∨
        G.Adj (C.vertex r) (C.vertex s) := by
    rcases hr_pos_raw with hrp | hrq | hrs'
    · exact Or.inl hrp.symm
    · exact Or.inr (Or.inl hrq.symm)
    · exact Or.inr (Or.inr hrs')
  have hs_pos :
      G.Adj (C.vertex p) (C.vertex s) ∨
        G.Adj (C.vertex q) (C.vertex s) ∨
        G.Adj (C.vertex r) (C.vertex s) := by
    rcases hs_pos_raw with hsp | hsq | hsr
    · exact Or.inl hsp.symm
    · exact Or.inr (Or.inl hsq.symm)
    · exact Or.inr (Or.inr hsr.symm)
  have hp_lt_three := hclaw.four_neighbors_not_degree_three
    hjq hjr hjs hqrv hqsv hrsv
    (C.not_triangle p q r) (C.not_triangle p q s)
    (C.not_triangle p r s)
  have hq_lt_three_raw := hclaw.four_neighbors_not_degree_three
    hjp hjr hjs hprv hpsv hrsv
    (C.not_triangle q p r) (C.not_triangle q p s)
    (C.not_triangle q r s)
  have hr_lt_three_raw := hclaw.four_neighbors_not_degree_three
    hjp hjq hjs hpqv hpsv hqsv
    (C.not_triangle r p q) (C.not_triangle r p s)
    (C.not_triangle r q s)
  have hs_lt_three_raw := hclaw.four_neighbors_not_degree_three
    hjp hjq hjr hpqv hprv hqrv
    (C.not_triangle s p q) (C.not_triangle s p r)
    (C.not_triangle s q r)
  have hq_lt_three :
      ¬(G.Adj (C.vertex p) (C.vertex q) ∧
        G.Adj (C.vertex q) (C.vertex r) ∧
        G.Adj (C.vertex q) (C.vertex s)) := by
    rintro ⟨hpq', hqr', hqs'⟩
    exact hq_lt_three_raw ⟨hpq'.symm, hqr', hqs'⟩
  have hr_lt_three :
      ¬(G.Adj (C.vertex p) (C.vertex r) ∧
        G.Adj (C.vertex q) (C.vertex r) ∧
        G.Adj (C.vertex r) (C.vertex s)) := by
    rintro ⟨hpr', hqr', hrs'⟩
    exact hr_lt_three_raw ⟨hpr'.symm, hqr'.symm, hrs'⟩
  have hs_lt_three :
      ¬(G.Adj (C.vertex p) (C.vertex s) ∧
        G.Adj (C.vertex q) (C.vertex s) ∧
        G.Adj (C.vertex r) (C.vertex s)) := by
    rintro ⟨hps', hqs', hrs'⟩
    exact hs_lt_three_raw ⟨hps'.symm, hqs'.symm, hrs'.symm⟩
  exact fourNeighborDegreeShape_of_bounds hp_pos hq_pos hr_pos hs_pos
    hp_lt_three hq_lt_three hr_lt_three hs_lt_three

end SimpleGraph
