import FreeFermionGraphs.T3HoleClassRun
import FreeFermionGraphs.T3PairingIndex
import FreeFermionGraphs.HoleChargeSigns

/-!
# The claw-free count formula `Ψ = |crossed W| - |matched W|`

This module computes the pairing index `Ψ(s, s')` of `FreeFermionGraphs.T3PairingIndex` for two
hole-class states `s = (A, B)`, `s' = (A', B')` (colouring classes of even holes `C = A ∪ B` and
`C' = A' ∪ B'`) of a claw-free graph.  It is the combinatorial heart of the selection rule for
the palindromic deformation in the synthesised proof of Theorem 1(iii) of the manuscript
(arXiv 2305.15625 v1, label `theorem:conservedcharges`).

The manuscript works with the set
`W = {j ∈ C' ∖ C | [h_j, h_C] = -1}` (Definition 20, `definition:anticommutingdependentsubsets`,
L996-1013; "`|W|` is odd", L1013) of the vertices of `C'` whose term anticommutes with `h_C`, and
it prescribes the *source set* of the obstruction graph (Definition 21,
`definition:obstructiongraphcoloringclasses`, L1017) as the larger of the two *pairing types* of
the vertices of `W`.  The pairing type of `j ∈ W` is read off the clone structure of the vertex
`j` in `C` (v1 Lemma 2, `lemma:vertexcyclerelations`, L654 with the Table at L630-650, case
(b.i): `j` is a clone of exactly one vertex `k` of `C`, `j ≺_C k`): `j` is *matched* if the
colour class of `j` in `C'` is the colour class of its clone `k` in `C`, and *crossed* otherwise.

## Definitions

* `SimpleGraph.matchedW G s s'`: the vertices `w ∈ s'.i ∖ C` that are clones in `C` of a vertex
  of `s.i` (`i = 1, 2`).
* `SimpleGraph.crossedW G s s'`: the same with a vertex of the other class `s.(3 - i)`.

## Main results

* `SimpleGraph.anticommutingVertices_eq_matchedW_union_crossedW`: for a claw-free graph and
  hole-class states, `anticommutingVertices C C' = matchedW s s' ∪ crossedW s s'`, a disjoint
  union.  (`W` of v1 Definition 20 is `matchedW ∪ crossedW`; the set `W'` of vertices of `C`
  anticommuting with `h_{C'}` is `matchedW s' s ∪ crossedW s' s`.)
* `SimpleGraph.pairingIndex_eq_card_sub_card`:
  `Ψ(s, s') = |crossedW s s'| - |matchedW s s'|`.  So `Ψ(s, s') < 0` iff there are more matched
  than crossed vertices; in the pairing used by the synthesised proof `matchedW` then plays the
  role of v1's source set and `crossedW` that of its obstruction set (the correspondence with
  the pairing types of v1's obstruction search is not formalised here, only the count).
* `SimpleGraph.matchedW_union_crossedW_subset`: `W ⊆ (s.1 ⊕ s'.1) ∪ (s.2 ⊕ s'.2)`.
* `SimpleGraph.matchedW_swap_swap`, `SimpleGraph.crossedW_swap_swap`: exchanging the two classes
  of both states leaves the matched and the crossed set unchanged.

## Proof of the count formula

`Ψ = Σ_y χ_{s'}(y) g(y)` with `g(y) = Σ_x χ_s(x) (A + 2 I)_{x y} = |N(y) ∩ s.1| - |N(y) ∩ s.2|
+ 2 χ_s(y)` (`sum_classSign_mul`).  Three cases:

* `y ∈ C`: the two neighbours of `y` on the hole have the colour opposite to `y`, so `g(y) = 0`
  (`imbalance_of_mem`).
* `y ∉ C`, anticommuting with `h_C` (an odd number of neighbours in `C`): `y ≺_C k` is a clone
  of a vertex `k` of `C` (`IsHoleClasses.exists_isCloneIn_of_anticommutesWithSet`, from the
  clone structure `EvenHoleLabeling.cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet`), so
  `N_C(y) = {k} ∪ N_C(k)` and `g(y) = -χ_s(k)` (`IsHoleClasses.clone_counts_fst`,
  `IsHoleClasses.clone_counts_snd`).
* `y ∉ C`, commuting with `h_C` (an even number of neighbours): the even cases of v1 Lemma 2
  (no neighbour, two adjacent neighbours, four neighbours forming two edges, a path `P4` or a
  4-hole) are colour balanced, so `g(y) = 0`.  The formalisation shows this directly: both
  `|N(y) ∩ s.1|` and `|N(y) ∩ s.2|` are at most `2` by claw-freeness
  (`SimpleGraph.card_filter_adj_le_two`), and one of them vanishes iff the other does by v1
  Corollary 1 (`corollary:vertexcycleneighboring`, L672;
  `IsHoleClasses.exists_adj_snd_of_adj_fst`), so an even sum forces equality
  (`IsHoleClasses.card_filter_fst_eq_snd_of_not_anticommutesWithSet`).

Then `χ_{s'}(y) g(y)` is `-1` for matched `y` and `+1` for crossed `y`, and `0` otherwise.

Claw-freeness enters only through the clone structure of the anticommuting vertices and the
even-count case; the formula holds for every pair of hole-class states of a claw-free graph, with
no further relation between the two holes.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The *matched* vertices `W_match(s, s')` of a pair of hole-class states (package T3-10; v1
Definition 20, L996-1013, with the pairing type read off v1 Lemma 2, L654): the vertices
`w ∈ s'.i ∖ C` (`C = s.1 ∪ s.2`, `i = 1, 2`) that are clones in `C` of a vertex of the *same*
class `s.i`.  For claw-free `G` and hole-class states, `matchedW s s' ∪ crossedW s s'` is the set
of vertices of `C'` whose term anticommutes with `h_C`
(`anticommutingVertices_eq_matchedW_union_crossedW`).  The definition is noncomputable so that
the statements do not carry a choice of decidability instance for the clone predicate. -/
noncomputable def matchedW (G : SimpleGraph V) [DecidableEq V] (s s' : Finset V × Finset V) :
    Finset V := by
  classical
  exact ((s'.1 \ (s.1 ∪ s.2)).filter fun w => ∃ k ∈ s.1, G.IsCloneIn ↑(s.1 ∪ s.2) w k) ∪
    ((s'.2 \ (s.1 ∪ s.2)).filter fun w => ∃ k ∈ s.2, G.IsCloneIn ↑(s.1 ∪ s.2) w k)

/-- The *crossed* vertices `W_cross(s, s')` of a pair of hole-class states: the vertices
`w ∈ s'.i ∖ C` that are clones in `C` of a vertex of the *other* class `s.(3 - i)`.  See
`matchedW`. -/
noncomputable def crossedW (G : SimpleGraph V) [DecidableEq V] (s s' : Finset V × Finset V) :
    Finset V := by
  classical
  exact ((s'.1 \ (s.1 ∪ s.2)).filter fun w => ∃ k ∈ s.2, G.IsCloneIn ↑(s.1 ∪ s.2) w k) ∪
    ((s'.2 \ (s.1 ∪ s.2)).filter fun w => ∃ k ∈ s.1, G.IsCloneIn ↑(s.1 ∪ s.2) w k)

section MatchedCrossed

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- Membership in `matchedW`, unfolded. -/
theorem mem_matchedW {w : V} :
    w ∈ G.matchedW s s' ↔
      (w ∈ s'.1 ∧ w ∉ s.1 ∪ s.2 ∧ ∃ k ∈ s.1, G.IsCloneIn ↑(s.1 ∪ s.2) w k) ∨
      (w ∈ s'.2 ∧ w ∉ s.1 ∪ s.2 ∧ ∃ k ∈ s.2, G.IsCloneIn ↑(s.1 ∪ s.2) w k) := by
  classical
  unfold matchedW
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, and_assoc]

/-- Membership in `crossedW`, unfolded. -/
theorem mem_crossedW {w : V} :
    w ∈ G.crossedW s s' ↔
      (w ∈ s'.1 ∧ w ∉ s.1 ∪ s.2 ∧ ∃ k ∈ s.2, G.IsCloneIn ↑(s.1 ∪ s.2) w k) ∨
      (w ∈ s'.2 ∧ w ∉ s.1 ∪ s.2 ∧ ∃ k ∈ s.1, G.IsCloneIn ↑(s.1 ∪ s.2) w k) := by
  classical
  unfold crossedW
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, and_assoc]

/-- Exchanging the two classes of both states leaves the matched set unchanged: a clone of a
vertex of `s.i` that lies in `s'.i` is a clone of a vertex of `s.swap.(3-i)` lying in
`s'.swap.(3-i)`. -/
theorem matchedW_swap_swap : G.matchedW s.swap s'.swap = G.matchedW s s' := by
  ext w
  rw [mem_matchedW, mem_matchedW]
  simp only [Prod.fst_swap, Prod.snd_swap, Finset.union_comm s.2 s.1]
  exact or_comm

/-- Exchanging the two classes of both states leaves the crossed set unchanged. -/
theorem crossedW_swap_swap : G.crossedW s.swap s'.swap = G.crossedW s s' := by
  ext w
  rw [mem_crossedW, mem_crossedW]
  simp only [Prod.fst_swap, Prod.snd_swap, Finset.union_comm s.2 s.1]
  exact or_comm

/-- The matched vertices lie in the symmetric differences of the classes: a matched vertex of
`s'.1` (resp. `s'.2`) lies outside the carrier of `s`, hence outside `s.1` (resp. `s.2`). -/
theorem matchedW_subset_symmDiff :
    G.matchedW s s' ⊆ symmDiff s.1 s'.1 ∪ symmDiff s.2 s'.2 := by
  intro w hw
  rw [mem_matchedW] at hw
  simp only [Finset.mem_union, Finset.mem_symmDiff]
  rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · left; right
    exact ⟨h1, fun h => h2 (Finset.mem_union_left _ h)⟩
  · right; right
    exact ⟨h1, fun h => h2 (Finset.mem_union_right _ h)⟩

/-- The crossed vertices lie in the symmetric differences of the classes: a crossed vertex of
`s'.1` (resp. `s'.2`) lies outside the carrier of `s`, hence outside `s.1` (resp. `s.2`). -/
theorem crossedW_subset_symmDiff :
    G.crossedW s s' ⊆ symmDiff s.1 s'.1 ∪ symmDiff s.2 s'.2 := by
  intro w hw
  rw [mem_crossedW] at hw
  simp only [Finset.mem_union, Finset.mem_symmDiff]
  rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · left; right
    exact ⟨h1, fun h => h2 (Finset.mem_union_left _ h)⟩
  · right; right
    exact ⟨h1, fun h => h2 (Finset.mem_union_right _ h)⟩

/-- The matched vertices lie in `C' ∖ C`. -/
theorem matchedW_subset_sdiff : G.matchedW s s' ⊆ (s'.1 ∪ s'.2) \ (s.1 ∪ s.2) := by
  intro w hw
  rw [mem_matchedW] at hw
  rw [Finset.mem_sdiff]
  rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨Finset.mem_union_left _ h1, h2⟩
  · exact ⟨Finset.mem_union_right _ h1, h2⟩

/-- The crossed vertices lie in `C' ∖ C`. -/
theorem crossedW_subset_sdiff : G.crossedW s s' ⊆ (s'.1 ∪ s'.2) \ (s.1 ∪ s.2) := by
  intro w hw
  rw [mem_crossedW] at hw
  rw [Finset.mem_sdiff]
  rcases hw with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨Finset.mem_union_left _ h1, h2⟩
  · exact ⟨Finset.mem_union_right _ h1, h2⟩

end MatchedCrossed

/-! ### Counting neighbours in the two colour classes -/

section Counting

variable [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The number of neighbours of `v` in a finset, as a `Set`-level `adjacencyCount`. -/
theorem adjacencyCount_coe_finset (v : V) (X : Finset V) :
    G.adjacencyCount v (X : Set V) = (X.filter (G.Adj v)).card := by
  have hset : G.adjacentIn v (X : Set V) = ((X.filter (G.Adj v) : Finset V) : Set V) := by
    ext w
    simp [adjacentIn]
  unfold adjacencyCount
  rw [hset, Set.ncard_coe_finset]

/-- A vertex of an independent set has no neighbour in it. -/
private theorem filter_adj_eq_empty_of_isIndepSet {A : Finset V} (hA : G.IsIndepSet (↑A : Set V)) {v : V}
    (hv : v ∈ A) : A.filter (G.Adj v) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x hx hadj
  by_cases hxv : v = x
  · subst hxv
    exact G.loopless.irrefl _ hadj
  · exact hA hv hx hxv hadj

/-- Clone of a vertex of the class `A`: the clone has exactly one neighbour in `A` (the clone
target) and as many neighbours in `B` as the target has (`2`). -/
theorem card_filter_adj_of_isCloneIn {A B : Finset V} (hA : G.IsIndepSet (↑A : Set V)) (hAB : Disjoint A B)
    (h2 : ∀ v ∈ A, (B.filter (G.Adj v)).card = 2) {y k : V}
    (hy : G.IsCloneIn (↑(A ∪ B) : Set V) y k) (hk : k ∈ A) :
    (A.filter (G.Adj y)).card = 1 ∧ (B.filter (G.Adj y)).card = 2 := by
  obtain ⟨-, -, hadj⟩ := hy
  constructor
  · have hfil : A.filter (G.Adj y) = {k} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hvA, hyv⟩
        rcases (hadj v (by simp [hvA])).1 hyv with h | hkv
        · exact h
        · by_cases hvk : k = v
          · exact hvk.symm
          · exact absurd hkv (hA hk hvA hvk)
      · rintro rfl
        exact ⟨hk, (hadj v (by simp [hk])).2 (Or.inl rfl)⟩
    rw [hfil]
    rfl
  · have hfil : B.filter (G.Adj y) = B.filter (G.Adj k) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hvB, hyv⟩
        refine ⟨hvB, ?_⟩
        rcases (hadj v (by simp [hvB])).1 hyv with h | hkv
        · exact absurd (h ▸ hk) (Finset.disjoint_right.mp hAB hvB)
        · exact hkv
      · rintro ⟨hvB, hkv⟩
        exact ⟨hvB, (hadj v (by simp [hvB])).2 (Or.inr hkv)⟩
    rw [hfil]
    exact h2 k hk

end Counting

/-! ### Neighbour counts for hole-class states -/

section HoleCounting

variable [DecidableEq V] [DecidableRel G.Adj] {s s' : Finset V × Finset V}

/-- A vertex of the carrier of a hole-class state has two neighbours on the hole, so the numbers
of its neighbours in the two colour classes add up to `2` (v1 L313: in an even hole every vertex
has two neighbours on the hole). -/
theorem IsHoleClasses.card_filter_adj_fst_add_snd (hs : G.IsHoleClasses s) {v : V}
    (hv : v ∈ s.1 ∪ s.2) :
    (s.1.filter (G.Adj v)).card + (s.2.filter (G.Adj v)).card = 2 := by
  have hdisj := hs.disjoint
  obtain ⟨n, L, -, h1, h2⟩ := hs
  have hcar : L.carrier = ↑(s.1 ∪ s.2) := by
    rw [← h1, ← h2]
    exact L.coe_image_a_union_image_b.symm
  have hvC : v ∈ L.carrier := by
    rw [hcar]
    exact Finset.mem_coe.mpr hv
  have h := L.adjacencyCount_eq_two_of_mem_carrier hvC
  rw [hcar, adjacencyCount_coe_finset, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)] at h
  exact h

/-- The number of neighbours of `y` in the carrier of a hole-class state is the sum of the
numbers in the two colour classes. -/
theorem IsHoleClasses.adjacencyCount_eq (hs : G.IsHoleClasses s) (y : V) :
    G.adjacencyCount y (↑(s.1 ∪ s.2) : Set V) =
      (s.1.filter (G.Adj y)).card + (s.2.filter (G.Adj y)).card := by
  rw [adjacencyCount_coe_finset, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hs.disjoint)]

/-- A vertex of the first class has two neighbours in the second class. -/
theorem IsHoleClasses.card_filter_snd_of_mem_fst (hs : G.IsHoleClasses s) {v : V}
    (hv : v ∈ s.1) : (s.2.filter (G.Adj v)).card = 2 := by
  have h := hs.card_filter_adj_fst_add_snd (Finset.mem_union_left _ hv)
  rw [filter_adj_eq_empty_of_isIndepSet hs.isIndepSet_fst hv, Finset.card_empty] at h
  omega

/-- A vertex of the second class has two neighbours in the first class. -/
theorem IsHoleClasses.card_filter_fst_of_mem_snd (hs : G.IsHoleClasses s) {v : V}
    (hv : v ∈ s.2) : (s.1.filter (G.Adj v)).card = 2 := by
  have h := hs.card_filter_adj_fst_add_snd (Finset.mem_union_right _ hv)
  rw [filter_adj_eq_empty_of_isIndepSet hs.isIndepSet_snd hv, Finset.card_empty] at h
  omega

/-- A clone of a vertex of the first class has one neighbour in the first class and two in the
second. -/
theorem IsHoleClasses.clone_counts_fst (hs : G.IsHoleClasses s) {y k : V}
    (hy : G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) (hk : k ∈ s.1) :
    (s.1.filter (G.Adj y)).card = 1 ∧ (s.2.filter (G.Adj y)).card = 2 :=
  card_filter_adj_of_isCloneIn hs.isIndepSet_fst hs.disjoint (fun _ hv => hs.card_filter_snd_of_mem_fst hv) hy hk

/-- A clone of a vertex of the second class has two neighbours in the first class and one in the
second. -/
theorem IsHoleClasses.clone_counts_snd (hs : G.IsHoleClasses s) {y k : V}
    (hy : G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) (hk : k ∈ s.2) :
    (s.2.filter (G.Adj y)).card = 1 ∧ (s.1.filter (G.Adj y)).card = 2 := by
  rw [Finset.union_comm] at hy
  exact card_filter_adj_of_isCloneIn hs.isIndepSet_snd hs.disjoint.symm
    (fun _ hv => hs.card_filter_fst_of_mem_snd hv) hy hk

/-- A clone of a vertex of the carrier of a hole-class state has an odd number (`3`) of
neighbours in the carrier, i.e. its term anticommutes with the hole operator. -/
theorem IsHoleClasses.anticommutesWithSet_of_isCloneIn (hs : G.IsHoleClasses s) {y k : V}
    (hy : G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) : G.AnticommutesWithSet y ↑(s.1 ∪ s.2) := by
  have hk : k ∈ s.1 ∪ s.2 := Finset.mem_coe.mp hy.2.1
  unfold AnticommutesWithSet
  rw [hs.adjacencyCount_eq]
  rcases Finset.mem_union.mp hk with hk | hk
  · have := hs.clone_counts_fst hy hk
    omega
  · have := hs.clone_counts_snd hy hk
    omega

omit [DecidableRel G.Adj] in
/-- (v1 Lemma 2 / `lemma:vertexcyclerelations`, Table case (b.i)) In a claw-free graph, a
vertex whose term anticommutes with the hole operator of a hole-class state is a clone in the
carrier of some vertex of it. -/
theorem IsHoleClasses.exists_isCloneIn_of_anticommutesWithSet (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) {y : V} (hy : G.AnticommutesWithSet y ↑(s.1 ∪ s.2)) :
    ∃ k, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k := by
  obtain ⟨n, L, hL, h1, h2⟩ := hs
  have hcar : L.carrier = ↑(s.1 ∪ s.2) := by
    rw [← h1, ← h2]
    exact L.coe_image_a_union_image_b.symm
  rw [← hcar] at hy ⊢
  obtain ⟨-, ⟨i, hi⟩ | ⟨i, hi⟩⟩ :=
    L.cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet hL hclaw hy
  · exact ⟨L.a i, hi.outside, L.a_mem_carrier i, hi.adj_iff⟩
  · have hc : L.swapColors.carrier = L.carrier := EvenHoleLabeling.swapColors_carrier L
    refine ⟨L.swapColors.a i, ?_, ?_, ?_⟩
    · rw [← hc]
      exact hi.outside
    · rw [← hc]
      exact L.swapColors.a_mem_carrier i
    · intro v hv
      rw [← hc] at hv
      exact hi.adj_iff v hv

omit [DecidableRel G.Adj] in
/-- (v1 Corollary 1, `corollary:vertexcycleneighboring`, L672: "if `j` is a neighbour to `k` in an even hole `C`, then `j` is also
neighbouring to a neighbour of `k` in `C`") for a vertex outside the carrier of a hole-class state:
a neighbour in the first class forces a neighbour in the second class. -/
theorem IsHoleClasses.exists_adj_snd_of_adj_fst (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    {y v : V} (hy : y ∉ s.1 ∪ s.2) (hv : v ∈ s.1) (hyv : G.Adj y v) :
    ∃ w ∈ s.2, G.Adj y w := by
  obtain ⟨n, L, -, h1, h2⟩ := hs
  rw [← h1] at hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  rw [← h1, ← h2] at hy
  have hyb : ∀ j, y ≠ L.b j := fun j h =>
    hy (Finset.mem_union_right _ (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hbmem : ∀ j, L.b j ∈ s.2 := fun j => by
    rw [← h2]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors hyv (L.adj_a_b i) (L.adj_a_b_next i)
      (hyb i) (hyb _) (L.b_ne_next i).symm (L.adj_bb i _) with h | h
  · exact ⟨L.b i, hbmem i, h⟩
  · exact ⟨L.b (L.next i), hbmem _, h⟩

omit [DecidableRel G.Adj] in
/-- The same with the two classes exchanged: a neighbour in the second class forces a neighbour
in the first class. -/
theorem IsHoleClasses.exists_adj_fst_of_adj_snd (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    {y v : V} (hy : y ∉ s.1 ∪ s.2) (hv : v ∈ s.2) (hyv : G.Adj y v) :
    ∃ w ∈ s.1, G.Adj y w := by
  obtain ⟨n, L, -, h1, h2⟩ := hs
  rw [← h2] at hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  rw [← h1, ← h2] at hy
  have hya : ∀ j, y ≠ L.a j := fun j h =>
    hy (Finset.mem_union_left _ (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hamem : ∀ j, L.a j ∈ s.1 := fun j => by
    rw [← h1]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors hyv (L.adj_a_b i).symm
      (L.adj_a_prev_b i).symm (hya i) (hya _) (L.a_ne_prev i).symm (L.adj_aa i _) with h | h
  · exact ⟨L.a i, hamem i, h⟩
  · exact ⟨L.a (L.prev i), hamem _, h⟩

/-- A vertex outside the hole whose term commutes with the hole operator has as many neighbours
in the first class as in the second.  The proof is the "even count" case of v1 Lemma 2: both
numbers are at most `2` (claw-freeness), and one vanishes iff the other does (Corollary 1). -/
theorem IsHoleClasses.card_filter_fst_eq_snd_of_not_anticommutesWithSet (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) {y : V} (hy : y ∉ s.1 ∪ s.2)
    (hna : ¬G.AnticommutesWithSet y ↑(s.1 ∪ s.2)) :
    (s.1.filter (G.Adj y)).card = (s.2.filter (G.Adj y)).card := by
  have hP := card_filter_adj_le_two hclaw hs.isIndepSet_fst y
  have hQ := card_filter_adj_le_two hclaw hs.isIndepSet_snd y
  have h12 : (s.1.filter (G.Adj y)).card ≠ 0 → (s.2.filter (G.Adj y)).card ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    rw [Finset.mem_filter] at hv
    obtain ⟨w, hw, hyw⟩ := hs.exists_adj_snd_of_adj_fst hclaw hy hv.1 hv.2
    exact Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hyw⟩⟩)
  have h21 : (s.2.filter (G.Adj y)).card ≠ 0 → (s.1.filter (G.Adj y)).card ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    rw [Finset.mem_filter] at hv
    obtain ⟨w, hw, hyw⟩ := hs.exists_adj_fst_of_adj_snd hclaw hy hv.1 hv.2
    exact Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hyw⟩⟩)
  have hpar : ¬((s.1.filter (G.Adj y)).card + (s.2.filter (G.Adj y)).card) % 2 = 1 := by
    unfold AnticommutesWithSet at hna
    rwa [hs.adjacencyCount_eq] at hna
  omega

/-- The imbalance `|N(y) ∩ s.1| - |N(y) ∩ s.2|` of the neighbours of `y` between the two colour
classes of `s`.  For a vertex outside a hole of a claw-free graph it is `-1`, `0` or `1`
(`imbalance_cases`), and `-1` (`1`) exactly when `y` is a clone of a vertex of the first (second)
class (`exists_isCloneIn_fst_iff`, `exists_isCloneIn_snd_iff`). -/
private def imbalance (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V × Finset V) (y : V) : ℤ :=
  ((s.1.filter (G.Adj y)).card : ℤ) - (s.2.filter (G.Adj y)).card

private theorem imbalance_of_isCloneIn_fst (hs : G.IsHoleClasses s) {y k : V}
    (hy : G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) (hk : k ∈ s.1) : imbalance G s y = -1 := by
  have h := hs.clone_counts_fst hy hk
  unfold imbalance
  omega

private theorem imbalance_of_isCloneIn_snd (hs : G.IsHoleClasses s) {y k : V}
    (hy : G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) (hk : k ∈ s.2) : imbalance G s y = 1 := by
  have h := hs.clone_counts_snd hy hk
  unfold imbalance
  omega

private theorem imbalance_of_not_exists_isCloneIn (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    {y : V} (hy : y ∉ s.1 ∪ s.2) (hno : ¬∃ k, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) :
    imbalance G s y = 0 := by
  have hna : ¬G.AnticommutesWithSet y ↑(s.1 ∪ s.2) := fun h =>
    hno (hs.exists_isCloneIn_of_anticommutesWithSet hclaw h)
  have h := hs.card_filter_fst_eq_snd_of_not_anticommutesWithSet hclaw hy hna
  unfold imbalance
  omega

/-- For `y` in the carrier the imbalance is `-2 χ_s(y)`: a vertex of the first class has two
neighbours in the second class, and conversely. -/
private theorem imbalance_of_mem (hs : G.IsHoleClasses s) {y : V} (hy : y ∈ s.1 ∪ s.2) :
    imbalance G s y + 2 * classSign s y = 0 := by
  unfold imbalance
  rcases Finset.mem_union.mp hy with h1 | h2
  · have hP := filter_adj_eq_empty_of_isIndepSet hs.isIndepSet_fst h1
    have hQ := hs.card_filter_snd_of_mem_fst h1
    rw [classSign_of_mem_fst h1, hP, Finset.card_empty, hQ]
    norm_num
  · have h1 : y ∉ s.1 := fun h => Finset.disjoint_left.mp hs.disjoint h h2
    have hQ := filter_adj_eq_empty_of_isIndepSet hs.isIndepSet_snd h2
    have hP := hs.card_filter_fst_of_mem_snd h2
    rw [classSign_of_mem_snd h1 h2, hQ, Finset.card_empty, hP]
    norm_num

/-- Outside the carrier the imbalance is determined by the clone structure. -/
private theorem exists_isCloneIn_fst_iff (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) {y : V}
    (hy : y ∉ s.1 ∪ s.2) :
    (∃ k ∈ s.1, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) ↔ imbalance G s y = -1 := by
  constructor
  · rintro ⟨k, hk, hcl⟩
    exact imbalance_of_isCloneIn_fst hs hcl hk
  · intro h
    by_cases hex : ∃ k, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k
    · obtain ⟨k, hcl⟩ := hex
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hcl.2.1) with hk | hk
      · exact ⟨k, hk, hcl⟩
      · have := imbalance_of_isCloneIn_snd hs hcl hk
        omega
    · have := imbalance_of_not_exists_isCloneIn hclaw hs hy hex
      omega

private theorem exists_isCloneIn_snd_iff (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) {y : V}
    (hy : y ∉ s.1 ∪ s.2) :
    (∃ k ∈ s.2, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k) ↔ imbalance G s y = 1 := by
  constructor
  · rintro ⟨k, hk, hcl⟩
    exact imbalance_of_isCloneIn_snd hs hcl hk
  · intro h
    by_cases hex : ∃ k, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k
    · obtain ⟨k, hcl⟩ := hex
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hcl.2.1) with hk | hk
      · have := imbalance_of_isCloneIn_fst hs hcl hk
        omega
      · exact ⟨k, hk, hcl⟩
    · have := imbalance_of_not_exists_isCloneIn hclaw hs hy hex
      omega

/-- Outside the carrier the imbalance is `-1`, `0` or `1`. -/
private theorem imbalance_cases (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) {y : V}
    (hy : y ∉ s.1 ∪ s.2) : imbalance G s y = -1 ∨ imbalance G s y = 0 ∨ imbalance G s y = 1 := by
  by_cases hex : ∃ k, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) y k
  · obtain ⟨k, hcl⟩ := hex
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hcl.2.1) with hk | hk
    · exact Or.inl (imbalance_of_isCloneIn_fst hs hcl hk)
    · exact Or.inr (Or.inr (imbalance_of_isCloneIn_snd hs hcl hk))
  · exact Or.inr (Or.inl (imbalance_of_not_exists_isCloneIn hclaw hs hy hex))

/-- Membership in `matchedW` in terms of the imbalance. -/
private theorem mem_matchedW_iff (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) {w : V} :
    w ∈ G.matchedW s s' ↔
      w ∉ s.1 ∪ s.2 ∧
        ((w ∈ s'.1 ∧ imbalance G s w = -1) ∨ (w ∈ s'.2 ∧ imbalance G s w = 1)) := by
  rw [mem_matchedW]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h2, Or.inl ⟨h1, (exists_isCloneIn_fst_iff hclaw hs h2).1 h3⟩⟩
    · exact ⟨h2, Or.inr ⟨h1, (exists_isCloneIn_snd_iff hclaw hs h2).1 h3⟩⟩
  · rintro ⟨h2, ⟨h1, h3⟩ | ⟨h1, h3⟩⟩
    · exact Or.inl ⟨h1, h2, (exists_isCloneIn_fst_iff hclaw hs h2).2 h3⟩
    · exact Or.inr ⟨h1, h2, (exists_isCloneIn_snd_iff hclaw hs h2).2 h3⟩

/-- Membership in `crossedW` in terms of the imbalance. -/
private theorem mem_crossedW_iff (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) {w : V} :
    w ∈ G.crossedW s s' ↔
      w ∉ s.1 ∪ s.2 ∧
        ((w ∈ s'.1 ∧ imbalance G s w = 1) ∨ (w ∈ s'.2 ∧ imbalance G s w = -1)) := by
  rw [mem_crossedW]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h2, Or.inl ⟨h1, (exists_isCloneIn_snd_iff hclaw hs h2).1 h3⟩⟩
    · exact ⟨h2, Or.inr ⟨h1, (exists_isCloneIn_fst_iff hclaw hs h2).1 h3⟩⟩
  · rintro ⟨h2, ⟨h1, h3⟩ | ⟨h1, h3⟩⟩
    · exact Or.inl ⟨h1, h2, (exists_isCloneIn_snd_iff hclaw hs h2).2 h3⟩
    · exact Or.inr ⟨h1, h2, (exists_isCloneIn_fst_iff hclaw hs h2).2 h3⟩

/-- The column sum `Σ_x χ_s(x) (A + 2 I)_{x y}` of the pairing index is the imbalance of `y`
plus `2 χ_s(y)`. -/
private theorem sum_classSign_mul [Fintype V] (hs : Disjoint s.1 s.2) (y : V) :
    ∑ x, classSign s x * ((if G.Adj x y then (1 : ℤ) else 0) + (if x = y then 2 else 0)) =
      imbalance G s y + 2 * classSign s y := by
  have hpt : ∀ x, classSign s x * (if G.Adj x y then (1 : ℤ) else 0) =
      (if x ∈ s.1.filter (G.Adj y) then (1 : ℤ) else 0) -
        (if x ∈ s.2.filter (G.Adj y) then (1 : ℤ) else 0) := by
    intro x
    have h3' : G.Adj y x ↔ G.Adj x y := G.adj_comm y x
    by_cases h1 : x ∈ s.1
    · have h2 : x ∉ s.2 := Finset.disjoint_left.mp hs h1
      rw [classSign_of_mem_fst h1]
      by_cases h3 : G.Adj x y <;> simp [Finset.mem_filter, h1, h2, h3, h3']
    · by_cases h2 : x ∈ s.2
      · rw [classSign_of_mem_snd h1 h2]
        by_cases h3 : G.Adj x y <;> simp [Finset.mem_filter, h1, h2, h3, h3']
      · rw [classSign_of_not_mem h1 h2]
        simp [Finset.mem_filter, h1, h2]
  have hA : ∑ x, classSign s x * (if G.Adj x y then (1 : ℤ) else 0) = imbalance G s y := by
    have hcard : ∀ F : Finset V, ∑ x, (if x ∈ F then (1 : ℤ) else 0) = F.card := by
      intro F
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      simp
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_sub_distrib, hcard, hcard]
    rfl
  have hI : ∑ x, classSign s x * (if x = y then (2 : ℤ) else 0) = 2 * classSign s y := by
    simp [mul_comm]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hA, hI]

end HoleCounting

/-! ### The main results -/

section Main

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **The anticommuting vertices are the matched and crossed `W`** (v1 Lemma 2
`lemma:vertexcyclerelations`, L654, Table case (b.i), and the set `W` of Definition 20
`definition:anticommutingdependentsubsets`, L996).  For a claw-free graph and hole-class states
`s`, `s'` with carriers `C`, `C'`, the vertices of `C'` whose term anticommutes with `h_C` form
the disjoint union of `matchedW s s'` and `crossedW s s'`: each such vertex lies outside `C` and
is a clone of exactly one vertex of `C` (`IsHoleClasses.exists_isCloneIn_of_anticommutesWithSet`
and `IsHoleClasses.anticommutesWithSet_of_isCloneIn`), and it is matched or crossed according
to whether the colour class of the clone agrees with that of the vertex in `C'`. -/
theorem anticommutingVertices_eq_matchedW_union_crossedW (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') :
    G.anticommutingVertices (↑(s.1 ∪ s.2) : Set V) (s'.1 ∪ s'.2) =
        G.matchedW s s' ∪ G.crossedW s s' ∧
      Disjoint (G.matchedW s s') (G.crossedW s s') := by
  classical
  constructor
  · ext w
    rw [mem_anticommutingVertices, Finset.mem_union (s := G.matchedW s s') (t := G.crossedW s s'),
      mem_matchedW_iff hclaw hs, mem_crossedW_iff hclaw hs]
    constructor
    · rintro ⟨hw', hanti⟩
      obtain ⟨k, hk⟩ := hs.exists_isCloneIn_of_anticommutesWithSet hclaw hanti
      have hwC : w ∉ s.1 ∪ s.2 := fun h => hk.1 (Finset.mem_coe.mpr h)
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hk.2.1) with hk1 | hk2
      · have hi := imbalance_of_isCloneIn_fst hs hk hk1
        rcases Finset.mem_union.mp hw' with h1 | h2
        · exact Or.inl ⟨hwC, Or.inl ⟨h1, hi⟩⟩
        · exact Or.inr ⟨hwC, Or.inr ⟨h2, hi⟩⟩
      · have hi := imbalance_of_isCloneIn_snd hs hk hk2
        rcases Finset.mem_union.mp hw' with h1 | h2
        · exact Or.inr ⟨hwC, Or.inl ⟨h1, hi⟩⟩
        · exact Or.inl ⟨hwC, Or.inr ⟨h2, hi⟩⟩
    · rintro (⟨hwC, ⟨h1, hi⟩ | ⟨h2, hi⟩⟩ | ⟨hwC, ⟨h1, hi⟩ | ⟨h2, hi⟩⟩)
      · obtain ⟨k, -, hk⟩ := (exists_isCloneIn_fst_iff hclaw hs hwC).2 hi
        exact ⟨Finset.mem_union_left _ h1, hs.anticommutesWithSet_of_isCloneIn hk⟩
      · obtain ⟨k, -, hk⟩ := (exists_isCloneIn_snd_iff hclaw hs hwC).2 hi
        exact ⟨Finset.mem_union_right _ h2, hs.anticommutesWithSet_of_isCloneIn hk⟩
      · obtain ⟨k, -, hk⟩ := (exists_isCloneIn_snd_iff hclaw hs hwC).2 hi
        exact ⟨Finset.mem_union_left _ h1, hs.anticommutesWithSet_of_isCloneIn hk⟩
      · obtain ⟨k, -, hk⟩ := (exists_isCloneIn_fst_iff hclaw hs hwC).2 hi
        exact ⟨Finset.mem_union_right _ h2, hs.anticommutesWithSet_of_isCloneIn hk⟩
  · rw [Finset.disjoint_left]
    intro w hm hc
    rw [mem_matchedW_iff hclaw hs] at hm
    rw [mem_crossedW_iff hclaw hs] at hc
    have hd : ∀ {x : V}, x ∈ s'.1 → x ∈ s'.2 → False := fun h1 h2 =>
      Finset.disjoint_left.mp hs'.disjoint h1 h2
    obtain ⟨-, hm⟩ := hm
    obtain ⟨-, hc⟩ := hc
    rcases hm with ⟨h1, hi⟩ | ⟨h2, hi⟩ <;> rcases hc with ⟨h1', hi'⟩ | ⟨h2', hi'⟩
    · omega
    · exact hd h1 h2'
    · exact hd h1' h2
    · omega

/-- **The pairing index counts crossed minus matched `W`** (package T3-10; v1 Lemma 2,
`lemma:vertexcyclerelations`, L654 with Table L630-650; `W` and `|W|` odd L996-1013;
Definition 21 `definition:obstructiongraphcoloringclasses`, L1017).

For a claw-free graph and hole-class states `s`, `s'`,
`Ψ(s, s') = |crossedW s s'| - |matchedW s s'|`.  Proof: `Ψ = Σ_y χ_{s'}(y) g(y)` with
`g(y) = Σ_x χ_s(x) (A + 2 I)_{x y}`.  For `y ∈ C` the two neighbours of `y` on the hole have
the opposite colour, so `g(y) = 0`; for `y ∉ C` one has `g(y) = |N(y) ∩ s.1| - |N(y) ∩ s.2|`,
which is `-χ_s(k)` if `y` is a clone of `k` (the neighbours are `k` and the two neighbours of
`k` on the hole) and `0` otherwise (the even cases of v1 Lemma 2 are colour balanced).  Summing
`χ_{s'}(y) g(y)` over the matched (`-1`) and crossed (`+1`) vertices gives the formula. -/
theorem pairingIndex_eq_card_sub_card [Fintype V] (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') :
    G.pairingIndex s s' = ((G.crossedW s s').card : ℤ) - (G.matchedW s s').card := by
  classical
  have hpt : ∀ y : V, ∑ x, classSign s x * classSign s' y *
        ((if G.Adj x y then (1 : ℤ) else 0) + (if x = y then 2 else 0)) =
      (if y ∈ G.crossedW s s' then (1 : ℤ) else 0) -
        (if y ∈ G.matchedW s s' then (1 : ℤ) else 0) := by
    intro y
    have hfac : ∑ x, classSign s x * classSign s' y *
          ((if G.Adj x y then (1 : ℤ) else 0) + (if x = y then 2 else 0)) =
        classSign s' y * ∑ x, classSign s x *
          ((if G.Adj x y then (1 : ℤ) else 0) + (if x = y then 2 else 0)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hfac, sum_classSign_mul hs.disjoint y]
    by_cases hyC : y ∈ s.1 ∪ s.2
    · rw [imbalance_of_mem hs hyC, mul_zero]
      have hm : y ∉ G.matchedW s s' := fun h => ((mem_matchedW_iff hclaw hs).1 h).1 hyC
      have hc : y ∉ G.crossedW s s' := fun h => ((mem_crossedW_iff hclaw hs).1 h).1 hyC
      simp [hm, hc]
    · rw [classSign_of_not_mem (fun h => hyC (Finset.mem_union_left _ h))
        (fun h => hyC (Finset.mem_union_right _ h)), mul_zero, add_zero]
      have hm : y ∈ G.matchedW s s' ↔
          (y ∈ s'.1 ∧ imbalance G s y = -1) ∨ (y ∈ s'.2 ∧ imbalance G s y = 1) := by
        rw [mem_matchedW_iff hclaw hs]
        simp [hyC]
      have hc : y ∈ G.crossedW s s' ↔
          (y ∈ s'.1 ∧ imbalance G s y = 1) ∨ (y ∈ s'.2 ∧ imbalance G s y = -1) := by
        rw [mem_crossedW_iff hclaw hs]
        simp [hyC]
      by_cases h1 : y ∈ s'.1
      · have h2 : y ∉ s'.2 := Finset.disjoint_left.mp hs'.disjoint h1
        rw [classSign_of_mem_fst h1]
        rcases imbalance_cases hclaw hs hyC with hi | hi | hi <;> simp [hm, hc, h1, h2, hi]
      · by_cases h2 : y ∈ s'.2
        · rw [classSign_of_mem_snd h1 h2]
          rcases imbalance_cases hclaw hs hyC with hi | hi | hi <;> simp [hm, hc, h1, h2, hi]
        · rw [classSign_of_not_mem h1 h2]
          simp [hm, hc, h1, h2]
  rw [pairingIndex_eq_sum_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_sub_distrib]
  have hcard : ∀ F : Finset V, ∑ y, (if y ∈ F then (1 : ℤ) else 0) = F.card := by
    intro F
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp
  rw [hcard, hcard]

/-- **`W ⊆ (s.1 ⊕ s'.1) ∪ (s.2 ⊕ s'.2)`** (v1 L996ff: the vertices of `W` lie in `C' ∖ C`).  The
hole hypotheses are not needed (see `matchedW_subset_symmDiff`, `crossedW_subset_symmDiff`);
they are kept to match the package signature. -/
theorem matchedW_union_crossedW_subset (_hs : G.IsHoleClasses s) (_hs' : G.IsHoleClasses s') :
    G.matchedW s s' ∪ G.crossedW s s' ⊆ symmDiff s.1 s'.1 ∪ symmDiff s.2 s'.2 :=
  Finset.union_subset matchedW_subset_symmDiff crossedW_subset_symmDiff

/-- `|W| = |matchedW| + |crossedW|` (v1 L996-1013: `W` is the set of vertices of `C'` anticommuting
with `h_C`).  Together with `pairingIndex_eq_card_sub_card` this gives
`Ψ ≡ |W| (mod 2)`. -/
theorem card_anticommutingVertices_eq_card_matchedW_add_card_crossedW (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') :
    (G.anticommutingVertices (↑(s.1 ∪ s.2) : Set V) (s'.1 ∪ s'.2)).card =
      (G.matchedW s s').card + (G.crossedW s s').card := by
  obtain ⟨h, hd⟩ := anticommutingVertices_eq_matchedW_union_crossedW hclaw hs hs'
  rw [h, Finset.card_union_of_disjoint hd]

end Main

end SimpleGraph
