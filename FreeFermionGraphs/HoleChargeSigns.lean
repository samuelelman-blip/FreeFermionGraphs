import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.PathCommutation
import FreeFermionGraphs.Lemma7

/-!
# The sign of `h_C h_S` and the clone structure of the anticommuting vertices

This module formalises the passage in the proof of Theorem 1(ii) of the manuscript
(arXiv 2305.15625 v1, proof of `theorem:conservedcharges` (ii), L906-908) that

> Assume `h_C` and `h_S` anticommute.  There is at least one (and an odd number in
> general) vertex `s_0` in `S` such that `h_{s_0}` and `h_C` anticommute, as shown in
> Section [Neighboring Relations], ...,

together with the Section-2 remark (Lemma 2, L653, table case (b.i), and the remark
below Corollary 2) that, for an even hole `C` in a claw-free graph, a vertex `s` outside
`C` whose term anticommutes with `h_C` is a clone of exactly one vertex of `C`.

## Contents

* `SimpleGraph.anticommutingVertices G C S`: the vertices `s ∈ S` whose term anticommutes
  with the product over `C`, i.e. with `|Γ_C(s)|` odd (`SimpleGraph.AnticommutesWithSet`).
* `PauliFrustrationRepresentation.labelingOperator_mul_independentProduct`: for an
  alternating labelling `L` (carrier `C`, classes `C_a`, `C_b`) and an independent `S`,
  `h_C h_S = (-1)^{|A(C,S)|} h_S h_C`.  The proof applies the sign calculus of
  `FreeFermionGraphs.PauliSetSigns` to the two colour classes and reduces the total cross
  count `c(C_a, S) + c(C_b, S) = Σ_{s ∈ S} |Γ_C(s)|` modulo two.  Neither claw-freeness
  nor a full cyclic order is needed here.
* `EvenHoleLabeling.not_anticommutesWithSet_of_mem_carrier`: a vertex of `C` has exactly two
  neighbours in `C`, hence commutes with `h_C`.
* `EvenHoleLabeling.cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet`: for a labelling
  with full cyclic order in a claw-free graph, a vertex `s` with `|Γ_C(s)|` odd lies outside
  `C` and is a clone of some `a_i` (`s ≺_C a_i`) or of some `b_i`; the latter is a clone for
  the colour-swapped labelling `swapColors`.  The proof presents the carrier as an
  `IndexedInducedHole` of even length (`isEvenHoleCarrier_of_hasFullCyclicOrder`) and applies
  `IndexedInducedHole.lemma7`: an odd count must be `3` (the cases `0, 2, 4` are even, `5`
  needs a hole of length `5`), the three neighbours form an induced path `x-y-z` of the hole,
  and the middle vertex `y` is `a_i` or `b_i`.

v1 numbering: the repository's Lemma 7 is v1 Lemma 2 (L653).
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The vertices `s` of `S` whose term `h_s` anticommutes with the product `h_C` over the
vertex set `C`, i.e. those with an odd number `|Γ_C(s)|` of neighbours in `C`
(v1 proof of Theorem 1(ii), L906-907: "the vertices `s_0` in `S` such that `h_{s_0}` and
`h_C` anticommute").  Noncomputable so that no decidability instance is carried as data. -/
noncomputable def anticommutingVertices (G : SimpleGraph V) (C : Set V)
    (S : Finset V) : Finset V := by
  classical exact S.filter fun s => G.AnticommutesWithSet s C

theorem mem_anticommutingVertices {C : Set V} {S : Finset V} {s : V} :
    s ∈ G.anticommutingVertices C S ↔ s ∈ S ∧ G.AnticommutesWithSet s C := by
  classical
  unfold anticommutingVertices
  simp only [Finset.mem_filter]

/-! ### Parity bookkeeping -/

/-- The sum of a natural-valued function over a finset is congruent modulo two to the
number of arguments where it takes an odd value. -/
theorem sum_mod_two_eq_card_filter_odd [DecidableEq V] (S : Finset V) (f : V → ℕ) :
    (∑ s ∈ S, f s) % 2 = (S.filter fun s => f s % 2 = 1).card % 2 := by
  rw [Finset.sum_nat_mod, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : f s % 2 = 0 ∨ f s % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases h with h | h <;> simp [h]

namespace EvenHoleLabeling

/-- The two colour classes of a labelling, as finsets. -/
theorem coe_image_a_union_image_b [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) :
    ((Finset.univ.image L.a ∪ Finset.univ.image L.b : Finset V) : Set V) = L.carrier := by
  simp [carrier]

theorem disjoint_image_a_image_b [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) :
    Disjoint (Finset.univ.image L.a) (Finset.univ.image L.b) := by
  rw [Finset.disjoint_left]
  intro v hva hvb
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hva hvb
  obtain ⟨i, rfl⟩ := hva
  obtain ⟨j, hj⟩ := hvb
  exact L.color_disjoint i j hj.symm

/-- For a vertex `s`, the number of neighbours in the whole carrier is the sum of the numbers
of neighbours in the two colour classes. -/
theorem adjacencyCount_carrier_eq [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (L : G.EvenHoleLabeling k) (s : V) :
    G.adjacencyCount s L.carrier =
      ((Finset.univ.image L.a).filter (G.Adj s)).card +
        ((Finset.univ.image L.b).filter (G.Adj s)).card := by
  have hset : G.adjacentIn s L.carrier =
      (((Finset.univ.image L.a ∪ Finset.univ.image L.b).filter (G.Adj s) : Finset V) :
        Set V) := by
    ext v
    rw [Finset.coe_filter, ← L.coe_image_a_union_image_b]
    simp [adjacentIn]
  unfold adjacencyCount
  rw [hset, Set.ncard_coe_finset, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter L.disjoint_image_a_image_b)]

/-- The total cross count of the two colour classes with `S` is `Σ_{s ∈ S} |Γ_C(s)|`. -/
theorem crossCount_image_a_add_crossCount_image_b [DecidableEq V] {k : ℕ}
    (L : G.EvenHoleLabeling k) (S : Finset V) :
    G.crossCount (Finset.univ.image L.a) S + G.crossCount (Finset.univ.image L.b) S =
      ∑ s ∈ S, G.adjacencyCount s L.carrier := by
  classical
  rw [crossCount_comm, crossCount_comm (Finset.univ.image L.b),
    crossCount_eq_sum_card_filter, crossCount_eq_sum_card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => (L.adjacencyCount_carrier_eq s).symm

end EvenHoleLabeling

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- **Sign of `h_C h_S`** (v1 proof of Theorem 1(ii), L906-908).  For an alternating
labelling `L` with carrier `C` and an independent finset `S`,
`h_C h_S = (-1)^{|A(C,S)|} h_S h_C`, where `A(C,S)` is the set of vertices of `S` with an odd
number of neighbours in `C`.  No claw-freeness and no full cyclic order is needed.  In
particular `h_C` and `h_S` anticommute iff `|A(C,S)|` is odd. -/
theorem labelingOperator_mul_independentProduct [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    {k : ℕ} (L : G.EvenHoleLabeling k) {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    H.labelingOperator L * H.independentProduct S =
      (-1 : A) ^ (G.anticommutingVertices L.carrier S).card *
        (H.independentProduct S * H.labelingOperator L) := by
  classical
  set Pa := H.independentProduct (Finset.univ.image L.a) with hPa
  set Pb := H.independentProduct (Finset.univ.image L.b) with hPb
  set hS' := H.independentProduct S with hhS
  have ha : Pa * hS' = (-1 : A) ^ G.crossCount (Finset.univ.image L.a) S * (hS' * Pa) :=
    H.independentProduct_mul_independentProduct L.isIndepSet_image_a hS
  have hb : Pb * hS' = (-1 : A) ^ G.crossCount (Finset.univ.image L.b) S * (hS' * Pb) :=
    H.independentProduct_mul_independentProduct L.isIndepSet_image_b hS
  have hexp : (-1 : A) ^ G.crossCount (Finset.univ.image L.a) S *
        (-1 : A) ^ G.crossCount (Finset.univ.image L.b) S =
      (-1 : A) ^ (G.anticommutingVertices L.carrier S).card := by
    rw [← pow_add, L.crossCount_image_a_add_crossCount_image_b,
      neg_one_pow_eq_pow_mod_two (R := A) (n := ∑ s ∈ S, G.adjacencyCount s L.carrier),
      neg_one_pow_eq_pow_mod_two (R := A)
        (n := (G.anticommutingVertices L.carrier S).card)]
    congr 1
    rw [sum_mod_two_eq_card_filter_odd]
    have h : G.anticommutingVertices L.carrier S =
        S.filter (fun s => G.adjacencyCount s L.carrier % 2 = 1) := by
      ext s
      rw [mem_anticommutingVertices, Finset.mem_filter]
      rfl
    rw [h]
  calc H.labelingOperator L * hS' = Pa * (Pb * hS') := by
        unfold labelingOperator; rw [mul_assoc]
    _ = Pa * ((-1 : A) ^ G.crossCount (Finset.univ.image L.b) S * (hS' * Pb)) := by rw [hb]
    _ = (-1 : A) ^ G.crossCount (Finset.univ.image L.b) S * (Pa * hS') * Pb := by
        rw [(neg_one_pow_commute (G.crossCount (Finset.univ.image L.b) S) Pa).symm.left_comm]
        simp only [mul_assoc]
    _ = (-1 : A) ^ G.crossCount (Finset.univ.image L.b) S *
          ((-1 : A) ^ G.crossCount (Finset.univ.image L.a) S * (hS' * Pa)) * Pb := by
        rw [ha]
    _ = ((-1 : A) ^ G.crossCount (Finset.univ.image L.a) S *
          (-1 : A) ^ G.crossCount (Finset.univ.image L.b) S) * (hS' * (Pa * Pb)) := by
        rw [(neg_one_pow_commute (G.crossCount (Finset.univ.image L.a) S)
          ((-1 : A) ^ G.crossCount (Finset.univ.image L.b) S)).eq]
        simp only [mul_assoc]
    _ = (-1 : A) ^ (G.anticommutingVertices L.carrier S).card *
          (hS' * H.labelingOperator L) := by
        rw [hexp]; rfl

end PauliFrustrationRepresentation

namespace EvenHoleLabeling

/-! ### Neighbourhoods inside the carrier of a labelling -/

/-- The vertices of the carrier adjacent to `a i` are `b i` and `b (next i)`. -/
theorem adj_a_iff_of_mem_carrier {k : ℕ} (L : G.EvenHoleLabeling k) (i : Fin k) {v : V}
    (hv : v ∈ L.carrier) : G.Adj (L.a i) v ↔ v = L.b i ∨ v = L.b (L.next i) := by
  rcases hv with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · refine ⟨fun h => (L.adj_aa i j h).elim, ?_⟩
    rintro (h | h)
    · exact (L.color_disjoint j i h).elim
    · exact (L.color_disjoint j _ h).elim
  · rw [L.adj_ab_iff, L.b_injective.eq_iff, L.b_injective.eq_iff]

/-- A vertex `a i` has exactly the two neighbours `b i`, `b (next i)` in the carrier. -/
theorem adjacencyCount_a {k : ℕ} (L : G.EvenHoleLabeling k) (i : Fin k) :
    G.adjacencyCount (L.a i) L.carrier = 2 := by
  have hset : G.adjacentIn (L.a i) L.carrier = {L.b i, L.b (L.next i)} := by
    ext v
    simp only [adjacentIn, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, hadj⟩
      exact (L.adj_a_iff_of_mem_carrier i hv).1 hadj
    · intro hv
      have hv' : v ∈ L.carrier := by
        rcases hv with rfl | rfl
        · exact L.b_mem_carrier i
        · exact L.b_mem_carrier _
      exact ⟨hv', (L.adj_a_iff_of_mem_carrier i hv').2 hv⟩
  unfold adjacencyCount
  rw [hset, Set.ncard_pair]
  intro h
  exact L.next_ne i (L.b_injective h).symm

/-- A vertex of the carrier of a labelling has exactly two neighbours in the carrier, so its
term commutes with the product over the carrier (v1 L313: in an even hole every vertex has two
neighbours on the hole).  Both colour classes are covered: `a i` directly, `b i` through the
colour-swapped labelling. -/
theorem adjacencyCount_eq_two_of_mem_carrier {k : ℕ} (L : G.EvenHoleLabeling k) {v : V}
    (hv : v ∈ L.carrier) : G.adjacencyCount v L.carrier = 2 := by
  rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact L.adjacencyCount_a i
  · have h := L.swapColors.adjacencyCount_a i
    rwa [swapColors_a, swapColors_carrier] at h

/-- No vertex of the carrier of a labelling anticommutes with the carrier
(a vertex of `C` has exactly two neighbours in `C`). -/
theorem not_anticommutesWithSet_of_mem_carrier {k : ℕ} (L : G.EvenHoleLabeling k) {v : V}
    (hv : v ∈ L.carrier) : ¬G.AnticommutesWithSet v L.carrier := by
  unfold AnticommutesWithSet
  rw [L.adjacencyCount_eq_two_of_mem_carrier hv]
  omega

/-! ### Clone structure -/

/-- A vertex outside the carrier whose neighbours in the carrier are exactly `b i`, `a i`,
`b (next i)` is a clone of `a i`. -/
theorem cloneAt_of_adj_iff {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} (i : Fin k)
    (hs : s ∉ L.carrier)
    (hN : ∀ v ∈ L.carrier, G.Adj s v ↔ v = L.b i ∨ v = L.a i ∨ v = L.b (L.next i)) :
    L.CloneAt s i := by
  refine ⟨hs, fun v hv => ?_⟩
  rw [hN v hv, L.adj_a_iff_of_mem_carrier i hv]
  tauto

/-- If the neighbours of `s` in the carrier are `x, y, z` where `y = a i` and `x, z` are
distinct neighbours of `y`, then `s` is a clone of `a i`. -/
theorem cloneAt_of_neighbors_middle_a {k : ℕ} (L : G.EvenHoleLabeling k) {s x y z : V}
    (i : Fin k) (hy : y = L.a i) (hs : s ∉ L.carrier) (hx : x ∈ L.carrier)
    (hz : z ∈ L.carrier) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : x ≠ z)
    (hN : ∀ v ∈ L.carrier, G.Adj s v ↔ v = x ∨ v = y ∨ v = z) :
    L.CloneAt s i := by
  subst hy
  have hx' := (L.adj_a_iff_of_mem_carrier i hx).1 hxy.symm
  have hz' := (L.adj_a_iff_of_mem_carrier i hz).1 hyz
  refine L.cloneAt_of_adj_iff i hs fun v hv => ?_
  rw [hN v hv]
  rcases hx' with rfl | rfl <;> rcases hz' with rfl | rfl
  · exact (hxz rfl).elim
  · tauto
  · tauto
  · exact (hxz rfl).elim

/-- If the neighbours of `s` in the carrier are three vertices `x, y, z` with `x - y - z` a path
(`x ≠ z`), then `s` is a clone of some `a i`, or of some `b i`, the latter being a clone of
`swapColors.a i = b i` for the colour-swapped labelling. -/
theorem cloneAt_or_swapColors_cloneAt_of_neighbors {k : ℕ} (L : G.EvenHoleLabeling k)
    {s x y z : V} (hs : s ∉ L.carrier) (hx : x ∈ L.carrier) (hy : y ∈ L.carrier)
    (hz : z ∈ L.carrier) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : x ≠ z)
    (hN : ∀ v ∈ L.carrier, G.Adj s v ↔ v = x ∨ v = y ∨ v = z) :
    (∃ i, L.CloneAt s i) ∨ ∃ i, L.swapColors.CloneAt s i := by
  rcases hy with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl ⟨i, L.cloneAt_of_neighbors_middle_a i hi.symm hs hx hz hxy hyz hxz hN⟩
  · refine Or.inr ⟨i, L.swapColors.cloneAt_of_neighbors_middle_a i hi.symm ?_ ?_ ?_ hxy hyz hxz ?_⟩
    · rwa [swapColors_carrier]
    · rwa [swapColors_carrier]
    · rwa [swapColors_carrier]
    · rwa [swapColors_carrier]

/-- A vertex is a clone of at most one `a i`: `s ≺_C a_i` and `s ≺_C a_j` force `i = j`. -/
theorem CloneAt.index_unique {k : ℕ} {L : G.EvenHoleLabeling k} {s : V} {i j : Fin k}
    (hi : L.CloneAt s i) (hj : L.CloneAt s j) : i = j := by
  have h := (hj.adj_iff (L.a i) (L.a_mem_carrier i)).1 hi.adj_original
  rcases h with h | h
  · exact L.a_injective h
  · exact (L.adj_aa j i h).elim

/-- A vertex cannot be a clone of some `a i` and also of some `b j` (that is, a clone for the
colour-swapped labelling): the first kind has exactly one neighbour `a i` among the `a`-vertices
of the carrier, the second kind has the two neighbours `a j`, `a (prev j)`. -/
theorem CloneAt.not_swapColors_cloneAt {k : ℕ} {L : G.EvenHoleLabeling k} {s : V} {i j : Fin k}
    (hi : L.CloneAt s i) (hj : L.swapColors.CloneAt s j) : False := by
  have hadj : ∀ v ∈ L.carrier, G.Adj (L.b j) v → G.Adj s v := by
    intro v hv hbv
    have hv' : v ∈ L.swapColors.carrier := by rwa [swapColors_carrier]
    exact (hj.adj_iff v hv').2 (Or.inr hbv)
  have hatom : ∀ m : Fin k, G.Adj (L.b j) (L.a m) → m = i := by
    intro m hm
    have hs := hadj _ (L.a_mem_carrier m) hm
    rcases (hi.adj_iff (L.a m) (L.a_mem_carrier m)).1 hs with h | h
    · exact L.a_injective h
    · exact (L.adj_aa i m h).elim
  have h1 : j = i := hatom j (L.adj_a_b j).symm
  have h2 : L.prev j = i := hatom (L.prev j) (L.adj_a_prev_b j).symm
  exact L.prev_ne j (h2.trans h1.symm)

/-- **Clone structure of the anticommuting vertices** (v1 L653, Lemma 2 table case (b.i), and
the remark below Corollary 2 that `h_j` anticommutes with `h_C` for an even hole only in case
(b.i); v1 proof of Theorem 1(ii), L907).

Let `L` be a labelling with full cyclic order (so its carrier `C` is an even hole) in a
claw-free graph.  A vertex `s` that anticommutes with `h_C`, i.e. with `|Γ_C(s)|` odd, lies
outside `C` and is a clone of exactly one vertex of `C`: `s ≺_C a_i` for some `i`, or
`s ≺_C b_i`, which is a clone for the colour-swapped labelling `L.swapColors`
(`swapColors.a i = b i`, same carrier).

Proof: present `C` as an `IndexedInducedHole` of even length
(`isEvenHoleCarrier_of_hasFullCyclicOrder`) and apply `IndexedInducedHole.lemma7`.  The cases
with `0, 2, 4` neighbours have an even count, and `5` neighbours force a hole of length `5`.
So the count is `3` and the three neighbours form an induced path `x-y-z` of the hole, with
`y` one of `a_i`, `b_i`. -/
theorem cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet {k : ℕ} (L : G.EvenHoleLabeling k)
    (hL : L.HasFullCyclicOrder) (hclaw : G.IsClawFree) {s : V}
    (hanti : G.AnticommutesWithSet s L.carrier) :
    s ∉ L.carrier ∧ ((∃ i, L.CloneAt s i) ∨ ∃ i, L.swapColors.CloneAt s i) := by
  have hs : s ∉ L.carrier := fun hsC => L.not_anticommutesWithSet_of_mem_carrier hsC hanti
  refine ⟨hs, ?_⟩
  obtain ⟨C, hCeven, hCrange⟩ := L.isEvenHoleCarrier_of_hasFullCyclicOrder hL
  have hsC : s ∉ Set.range C.vertex := by rw [hCrange]; exact hs
  -- the number of neighbours of `s` in the carrier is that in the hole
  have hcount : G.adjacencyCount s L.carrier = (C.neighborIndexSet s).ncard := by
    have himg : C.vertex '' C.neighborIndexSet s = G.adjacentIn s L.carrier := by
      ext v
      simp only [Set.mem_image, IndexedInducedHole.mem_neighborIndexSet, adjacentIn,
        Set.mem_setOf_eq, ← hCrange, Set.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, rfl⟩, hi⟩
      · rintro ⟨⟨i, rfl⟩, hi⟩
        exact ⟨i, hi, rfl⟩
    unfold adjacencyCount
    rw [← himg, Set.ncard_image_of_injective _ C.injective]
  have hanti' : (C.neighborIndexSet s).ncard % 2 = 1 := by
    rw [← hcount]; exact hanti
  rcases C.lemma7 hclaw hsC with h0 | ⟨h2, _⟩ | ⟨h3, htriple⟩ | ⟨h4, _⟩ | ⟨h5, hcard5⟩
  · omega
  · omega
  · obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Set.ncard_eq_three.mp h3
    have hmem : ∀ k : Fin C.card, G.Adj s (C.vertex k) ↔ k = p ∨ k = q ∨ k = r := by
      intro k
      have := Set.ext_iff.mp hset k
      simpa using this
    have hp : G.Adj s (C.vertex p) := (hmem p).2 (Or.inl rfl)
    have hq : G.Adj s (C.vertex q) := (hmem q).2 (Or.inr (Or.inl rfl))
    have hr : G.Adj s (C.vertex r) := (hmem r).2 (Or.inr (Or.inr rfl))
    have hN : ∀ v ∈ L.carrier,
        G.Adj s v ↔ v = C.vertex p ∨ v = C.vertex q ∨ v = C.vertex r := by
      intro v hv
      rw [← hCrange] at hv
      obtain ⟨i, rfl⟩ := hv
      rw [hmem i, C.injective.eq_iff, C.injective.eq_iff, C.injective.eq_iff]
    have hmemC : ∀ k : Fin C.card, C.vertex k ∈ L.carrier := fun k => by
      rw [← hCrange]; exact ⟨k, rfl⟩
    rcases htriple p q r hpq hpr hqr hp hq hr (fun k hk => (hmem k).1 hk) with
      ⟨hxy, hyz, _, hxz⟩ | ⟨hxy, hyz, _, hxz⟩ | ⟨hxy, hyz, _, hxz⟩
    · -- middle vertex `p`, ends `q`, `r`
      exact L.cloneAt_or_swapColors_cloneAt_of_neighbors hs (hmemC q) (hmemC p) (hmemC r)
        hxy hyz hxz (fun v hv => (hN v hv).trans (by tauto))
    · -- middle vertex `q`, ends `p`, `r`
      exact L.cloneAt_or_swapColors_cloneAt_of_neighbors hs (hmemC p) (hmemC q) (hmemC r)
        hxy hyz hxz (hN)
    · -- middle vertex `r`, ends `p`, `q`
      exact L.cloneAt_or_swapColors_cloneAt_of_neighbors hs (hmemC p) (hmemC r) (hmemC q)
        hxy hyz hxz (fun v hv => (hN v hv).trans (by tauto))
  · omega
  · -- five neighbours would force a hole of length five, but the hole has even length
    rw [hcard5] at hCeven
    exact absurd hCeven (by decide)

/-- **Exactly one clone** (the "exactly one vertex of `C`" of the package statement).  Under the
hypotheses of `cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet`, an anticommuting vertex
`s` lies outside `C` and is the clone of exactly one vertex of `C`: either of a unique `a_i`
(and of no `b_j`), or of a unique `b_j` (a clone for `swapColors`, and of no `a_i`). -/
theorem exists_unique_clone_of_anticommutesWithSet {k : ℕ} (L : G.EvenHoleLabeling k)
    (hL : L.HasFullCyclicOrder) (hclaw : G.IsClawFree) {s : V}
    (hanti : G.AnticommutesWithSet s L.carrier) :
    s ∉ L.carrier ∧
      (((∃! i, L.CloneAt s i) ∧ ¬∃ j, L.swapColors.CloneAt s j) ∨
        ((∃! j, L.swapColors.CloneAt s j) ∧ ¬∃ i, L.CloneAt s i)) := by
  obtain ⟨hs, hclone⟩ :=
    L.cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet hL hclaw hanti
  refine ⟨hs, ?_⟩
  rcases hclone with ⟨i, hi⟩ | ⟨j, hj⟩
  · refine Or.inl ⟨⟨i, hi, fun i' hi' => hi'.index_unique hi⟩, ?_⟩
    rintro ⟨j, hj⟩
    exact hi.not_swapColors_cloneAt hj
  · refine Or.inr ⟨⟨j, hj, fun j' hj' => hj'.index_unique hj⟩, ?_⟩
    rintro ⟨i, hi⟩
    exact hi.not_swapColors_cloneAt hj

end EvenHoleLabeling

end SimpleGraph
