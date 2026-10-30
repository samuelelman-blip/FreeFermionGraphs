import FreeFermionGraphs.T3ComponentTether
import FreeFermionGraphs.T3FixedPairingSymm
import Mathlib.Tactic.Linarith

/-!
# A good candidate block exists when `Ψ < 0`

This module is the counting step of the synthesised proof of Theorem 1(iii) of arXiv 2305.15625 v1
(label `theorem:conservedcharges`), package T3-20.  It replaces the obstruction-graph pigeonhole
and rerouting of v1 (L1150-1172: "there must be at least one vertex `j''` in the obstruction set
of `D^{(i)}` with at least two incoming arcs", i.e. the source set is strictly larger than the
obstruction set) by a pure counting argument over the components of the two side graphs.

## Setting

`G` is claw-free and `s = (C_a, C_b)`, `s' = (C'_c, C'_d)` are hole-class states
(`SimpleGraph.IsHoleClasses`).  The vertices of `C'` anticommuting with `h_C` are the disjoint union
of `matchedW s s'` (v1's *source set*, when `Ψ(s, s') < 0`) and `crossedW s s'` (v1's
*obstruction set*), and `Ψ(s, s') = |crossedW s s'| - |matchedW s s'|`
(`pairingIndex_eq_card_sub_card`).  A *side block* of `(s, s')` is an odd block of the side graph
`G[C_a ⊕ C'_c]` or `G[C_b ⊕ C'_d]` (`SideBlock`).  For a side component `K` write

* `m = |K ∩ matchedW s s'|`, `x = |K ∩ crossedW s s'|`,
* `m' = |K ∩ matchedW s' s|`, `x' = |K ∩ crossedW s' s|`.

## Main definitions and results

* `SimpleGraph.SideBlock.GoodSource B` (the "good source" of the work package): `B` runs forward
  from `s`, has `(m, x) = (1, 0)`, and `(m', x') ∈ {(0, 0), (1, 1)}`.
* `SimpleGraph.exists_goodCandidate` (package T3-20): if `Ψ(s, s') < 0`, then
  (i) some side block `B` runs forward from `s` and backward from `s'` and has `(m, x) = (1, 0)`
  (the key `(1, 0, 1, 0)`), or (ii) some side block of `(s, s')` is a good source, or (iii) some
  side block of `(s', s)` is a good source (the mirror image).
* `SimpleGraph.HasGoodCandidate G s s'`: the conclusion of `exists_goodCandidate` as a proposition;
  `HasGoodCandidate.swap` transports it to `(s.swap, s'.swap)`.
* `SimpleGraph.hasGoodCandidate_of_component`: the local step, a side component with
  `(m - x) + (m' - x') > 0` yields a good candidate.
* `SimpleGraph.card_inter_eq_sum_components`: the partition of a finset by the components of
  `G[X]` (with `componentFinset_subset`, `mem_componentFinset_self`, `componentFinset_eq_of_mem`),
  and `SimpleGraph.mem_exactly_one_side_of_mem_W`: every vertex of `W` (and of `W'`) lies in exactly
  one of the two side graphs.

The statement has no counterpart in v1: v1 finds the starting vertex of its search by the
pigeonhole argument of L1150-1172 on the obstruction graph, which this counting argument replaces.

## Proof

Every vertex of `W = matchedW s s' ∪ crossedW s s'` and of `W' = matchedW s' s ∪ crossedW s' s`
lies in exactly one of the two side graphs (`W` avoids `C`, so a vertex of `C'_c ∖ C` is in
`C_a ⊕ C'_c` and not in `C_b ⊕ C'_d`, and symmetrically; likewise for `W'` with the roles of the
holes exchanged; `mem_exactly_one_side_of_mem_W`).  Partitioning by side component
(`card_inter_eq_sum_components`, the fibrewise cardinality formula
`Finset.card_eq_sum_card_fiberwise`) gives
`Σ_K ((m - x) + (m' - x')) = (|matchedW s s'| - |crossedW s s'|) +`
`(|matchedW s' s| - |crossedW s' s|) = -Ψ(s, s') - Ψ(s', s) = -2 Ψ(s, s') > 0`
(`pairingIndex_eq_card_sub_card`, `pairingIndex_comm`), so some side component `K` has
`(m - x) + (m' - x') > 0`.  On that component the tether lemma (`component_matched_le_crossed`,
package T3-19) for `(s, s')` and for `(s', s)` leaves three cases (`hasGoodCandidate_of_component`):
* `m > x` and `m' > x'`: the block of `(s, s')` and the block of `(s', s)` with the support `K` are
  reverses of each other (`OddBlock.eq_of_support_eq`), so the block runs forward from `s` and
  backward from `s'`: case (i);
* only `m > x`: the reverse of the block is a block of `(s', s)` with the support `K`, so `m' ≤ 1`
  by `OddBlock.card_matchedW_le_one`, and positivity forces `m' = x'`: case (ii);
* only `m' > x'`: symmetrically, case (iii).

A component of the second side graph is a component of the first side graph of
`(s.swap, s'.swap)`, which reduces the second side to the first (`HasGoodCandidate.swap`).

Claw-freeness enters only through the tether lemma and the count formula for `Ψ`.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Components of an induced subgraph as finsets -/

section Components

variable [Fintype V] {X : Finset V}

/-- The component of a vertex lies in the vertex set of the induced subgraph. -/
theorem componentFinset_subset (v : V) : G.componentFinset X v ⊆ X := by
  intro w hw
  obtain ⟨_, hw', _⟩ := mem_componentFinset.1 hw
  exact Finset.mem_coe.1 hw'

/-- A vertex of `X` lies in its own component. -/
theorem mem_componentFinset_self {v : V} (hv : v ∈ X) : v ∈ G.componentFinset X v :=
  mem_componentFinset.2 ⟨Finset.mem_coe.2 hv, Finset.mem_coe.2 hv, SimpleGraph.Reachable.refl _⟩

/-- Two vertices of the same component have the same component. -/
theorem componentFinset_eq_of_mem {v w : V} (hw : w ∈ G.componentFinset X v) :
    G.componentFinset X w = G.componentFinset X v := by
  obtain ⟨hv', hw', hr⟩ := mem_componentFinset.1 hw
  ext u
  rw [mem_componentFinset, mem_componentFinset]
  constructor
  · rintro ⟨_, hu, hr'⟩
    exact ⟨hv', hu, hr.trans hr'⟩
  · rintro ⟨_, hu, hr'⟩
    exact ⟨hw', hu, hr.symm.trans hr'⟩

/-- **Partition by component.**  For a finset `S` and a finset `T` of components of `G[X]` which
contains the component of every vertex of `S ∩ X`, the number of vertices of `S` in `X` is the sum
over `T` of the numbers of vertices of `S` in each component (the fibrewise cardinality formula
`Finset.card_eq_sum_card_fiberwise` for the map `v ↦ componentFinset X v`). -/
theorem card_inter_eq_sum_components [DecidableEq V] (X S : Finset V) (T : Finset (Finset V))
    (hT : ∀ u ∈ S ∩ X, G.componentFinset X u ∈ T)
    (hTX : ∀ K ∈ T, ∃ w ∈ X, G.componentFinset X w = K) :
    (S ∩ X).card = ∑ K ∈ T, (S ∩ K).card := by
  rw [Finset.card_eq_sum_card_fiberwise hT]
  refine Finset.sum_congr rfl fun K hK => ?_
  obtain ⟨w, hwX, rfl⟩ := hTX K hK
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨huS, huX⟩, hcomp⟩
    exact ⟨huS, hcomp ▸ mem_componentFinset_self huX⟩
  · rintro ⟨huS, hu⟩
    exact ⟨⟨huS, componentFinset_subset w hu⟩, componentFinset_eq_of_mem hu⟩

end Components

/-! ### The sides of the vertices of `W` -/

section Sides

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- A vertex of `matchedW s s' ∪ crossedW s s'` lies in the second hole `C'` and outside the first
hole `C`. -/
theorem mem_snd_carrier_of_mem_W {w : V} (hw : w ∈ G.matchedW s s' ∪ G.crossedW s s') :
    w ∈ s'.1 ∪ s'.2 ∧ w ∉ s.1 ∪ s.2 := by
  rcases Finset.mem_union.1 hw with h | h
  · rw [mem_matchedW] at h
    rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨Finset.mem_union_left _ h1, h2⟩
    · exact ⟨Finset.mem_union_right _ h1, h2⟩
  · rw [mem_crossedW] at h
    rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨Finset.mem_union_left _ h1, h2⟩
    · exact ⟨Finset.mem_union_right _ h1, h2⟩

/-- **Every vertex of `W` lies in exactly one side graph.**  A vertex `w` of
`matchedW s s' ∪ crossedW s s'` lies in `s.1 ⊕ s'.1` or in `s.2 ⊕ s'.2`, but not in both: it is in
`C'` and not in `C`, so it is in the symmetric difference of the colour classes it belongs to in
`C'`, and in no other. -/
theorem mem_exactly_one_side_of_mem_W (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {w : V}
    (hw : w ∈ G.matchedW s s' ∪ G.crossedW s s') :
    (w ∈ symmDiff s.1 s'.1 ∨ w ∈ symmDiff s.2 s'.2) ∧
      ¬(w ∈ symmDiff s.1 s'.1 ∧ w ∈ symmDiff s.2 s'.2) := by
  refine ⟨Finset.mem_union.1 (matchedW_union_crossedW_subset hs hs' hw), ?_⟩
  obtain ⟨h1, h2⟩ := mem_snd_carrier_of_mem_W hw
  rintro ⟨hd1, hd2⟩
  rw [Finset.mem_union, not_or] at h2
  rw [Finset.mem_union] at h1
  rw [Finset.mem_symmDiff] at hd1 hd2
  have hdis := hs'.disjoint
  rcases h1 with h1 | h1
  · rcases hd2 with ⟨a, -⟩ | ⟨a, -⟩
    · exact h2.2 a
    · exact Finset.disjoint_left.1 hdis h1 a
  · rcases hd1 with ⟨a, -⟩ | ⟨a, -⟩
    · exact h2.1 a
    · exact Finset.disjoint_right.1 hdis h1 a

/-- A finset lying in the union of two finsets, and meeting their intersection nowhere, is the
disjoint union of its two traces. -/
theorem card_eq_card_inter_add_of_exactly_one_mem (S D₁ D₂ : Finset V)
    (hsub : ∀ w ∈ S, w ∈ D₁ ∨ w ∈ D₂)
    (hdis : ∀ w ∈ S, ¬(w ∈ D₁ ∧ w ∈ D₂)) : S.card = (S ∩ D₁).card + (S ∩ D₂).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hw
      rcases hsub w hw with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, h⟩
    · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
  · rw [Finset.disjoint_left]
    intro w h1 h2
    exact hdis w (Finset.mem_inter.1 h1).1 ⟨(Finset.mem_inter.1 h1).2, (Finset.mem_inter.1 h2).2⟩

end Sides

/-! ### Good sources and good candidates -/

namespace SideBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- A side block `B` of `(s, s')` is a **good source** (package T3-20): it runs forward from `s`
(`RunsFrom`), it contains exactly one vertex of `matchedW s s'` and none of `crossedW s s'`
(the key `(m, x) = (1, 0)`), and its content of `W' = matchedW s' s ∪ crossedW s' s` is balanced,
`(m', x') ∈ {(0, 0), (1, 1)}`.  Its matched vertex is the vertex of the source set which
initialises the block (the initialising vertex of the search of v1, L1150-1172). -/
def GoodSource (B : G.SideBlock s s') : Prop :=
  B.RunsFrom ∧ (B.support ∩ G.matchedW s s').card = 1 ∧ (B.support ∩ G.crossedW s s').card = 0 ∧
    (((B.support ∩ G.matchedW s' s).card = 0 ∧ (B.support ∩ G.crossedW s' s).card = 0) ∨
      ((B.support ∩ G.matchedW s' s).card = 1 ∧ (B.support ∩ G.crossedW s' s).card = 1))

/-- Exchanging the two sides of a good source gives a good source of the swapped states. -/
theorem GoodSource.swap {B : G.SideBlock s s'} (h : B.GoodSource) : B.swap.GoodSource := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [RunsFrom, word_swap, exists_classRun_swap_iff]
    exact h1
  · rw [support_swap, matchedW_swap_swap]
    exact h2
  · rw [support_swap, crossedW_swap_swap]
    exact h3
  · rw [support_swap, matchedW_swap_swap, crossedW_swap_swap]
    exact h4

end SideBlock

/-- The conclusion of the good-candidate theorem `exists_goodCandidate` for the pair `(s, s')`:
(i) a side block running forward from `s` and backward from `s'` with `(m, x) = (1, 0)`, or (ii) a
good source among the side blocks of `(s, s')`, or (iii) a good source among the side blocks of
`(s', s)`. -/
def HasGoodCandidate (G : SimpleGraph V) [DecidableEq V] (s s' : Finset V × Finset V) : Prop :=
  (∃ B : G.SideBlock s s', B.RunsFrom ∧ B.RunsBack ∧ (B.support ∩ G.matchedW s s').card = 1 ∧
      (B.support ∩ G.crossedW s s').card = 0) ∨
    (∃ B : G.SideBlock s s', B.GoodSource) ∨ (∃ B : G.SideBlock s' s, B.GoodSource)

/-- A good candidate for `(s, s')` gives one for the swapped states `(s.swap, s'.swap)` (exchange
the two sides of every block). -/
theorem HasGoodCandidate.swap [DecidableEq V] {s s' : Finset V × Finset V}
    (h : G.HasGoodCandidate s s') : G.HasGoodCandidate s.swap s'.swap := by
  rcases h with ⟨B, h1, h2, h3, h4⟩ | ⟨B, hB⟩ | ⟨B, hB⟩
  · refine Or.inl ⟨B.swap, ?_, ?_, ?_, ?_⟩
    · rw [SideBlock.RunsFrom, SideBlock.word_swap, exists_classRun_swap_iff]
      exact h1
    · rw [SideBlock.RunsBack, SideBlock.word_swap, exists_classRun_swap_iff]
      exact h2
    · rw [SideBlock.support_swap, matchedW_swap_swap]
      exact h3
    · rw [SideBlock.support_swap, crossedW_swap_swap]
      exact h4
  · exact Or.inr (Or.inl ⟨B.swap, hB.swap⟩)
  · exact Or.inr (Or.inr ⟨B.swap, hB.swap⟩)

/-! ### A positive side component gives a good candidate -/

section Local

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

/-- **A positive side component gives a good candidate** (package T3-20, the local step).  Let `K`
be the component of `v` in the first side graph `G[s.1 ⊕ s'.1]`, and suppose that
`(m - x) + (m' - x') > 0`, where `m = |K ∩ matchedW s s'|`, `x = |K ∩ crossedW s s'|`,
`m' = |K ∩ matchedW s' s|` and `x' = |K ∩ crossedW s' s|`.  Then `s`, `s'` have a good candidate.

By the tether lemma (`component_matched_le_crossed`, package T3-19) for `(s, s')` and for
`(s', s)`, `m > x` forces `K` to be the support of a block `Q` of `(s, s')` running from `s` with
`(m, x) = (1, 0)`, and `m' > x'` forces `K` to be the support of a block `Q'` of `(s', s)` running
from `s'` with `(m', x') = (1, 0)`.  If both hold, `Q'` is the reverse of `Q` (a block is determined
by its support), so `Q` runs forward from `s` and backward from `s'`: case (i).  If only `m > x`,
the reverse of `Q` is a block of `(s', s)` with the support `K`, so `m' ≤ 1` by
`OddBlock.card_matchedW_le_one`; positivity forces `m' = x'`, so `(m', x') ∈ {(0,0), (1,1)}` and
`Q` is a good source: case (ii).  If only `m' > x'`, symmetrically, `Q'` is a good source of
`(s', s)`: case (iii). -/
theorem hasGoodCandidate_of_component (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') {v : V} {K : Finset V}
    (hv : v ∈ symmDiff s.1 s'.1) (hK : K = G.componentFinset (symmDiff s.1 s'.1) v)
    (hpos : (K ∩ G.crossedW s s').card + (K ∩ G.crossedW s' s).card <
      (K ∩ G.matchedW s s').card + (K ∩ G.matchedW s' s).card) :
    G.HasGoodCandidate s s' := by
  have hv' : v ∈ symmDiff s'.1 s.1 := by rwa [symmDiff_comm]
  have h1 := component_matched_le_crossed hclaw hs hs' hv
  have h2 := component_matched_le_crossed hclaw hs' hs hv'
  rw [symmDiff_comm s'.1 s.1, ← hK] at h2
  rw [← hK] at h1
  rcases h1 with h1 | ⟨Q, hQK, hQrun, hQm, hQx⟩ <;>
    rcases h2 with h2 | ⟨Q', hQ'K, hQ'run, hQ'm, hQ'x⟩
  · omega
  · -- only `m' > x'`: case (iii)
    have hmle := OddBlock.card_matchedW_le_one hclaw hs hs' Q'.reverse
    rw [OddBlock.reverse_support, hQ'K] at hmle
    rw [hQ'K] at hQ'm hQ'x
    refine Or.inr (Or.inr ⟨Sum.inl Q', hQ'run, ?_, ?_, ?_⟩)
    · rw [SideBlock.support_inl, hQ'K]
      exact hQ'm
    · rw [SideBlock.support_inl, hQ'K]
      exact hQ'x
    · rw [SideBlock.support_inl, hQ'K]
      omega
  · -- only `m > x`: case (ii)
    have hmle := OddBlock.card_matchedW_le_one hclaw hs' hs Q.reverse
    rw [OddBlock.reverse_support, hQK] at hmle
    rw [hQK] at hQm hQx
    refine Or.inr (Or.inl ⟨Sum.inl Q, hQrun, ?_, ?_, ?_⟩)
    · rw [SideBlock.support_inl, hQK]
      exact hQm
    · rw [SideBlock.support_inl, hQK]
      exact hQx
    · rw [SideBlock.support_inl, hQK]
      omega
  · -- both: case (i)
    have hrev : Q.reverse = Q' :=
      OddBlock.eq_of_support_eq _ _ (by rw [OddBlock.reverse_support, hQK, hQ'K])
    refine Or.inl ⟨Sum.inl Q, hQrun, ?_, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hQ'run
      refine ⟨t, ?_⟩
      rw [← hrev, OddBlock.reverse_word] at ht
      exact ht
    · rw [SideBlock.support_inl, hQK] at *
      exact hQm
    · rw [SideBlock.support_inl, hQK] at *
      exact hQx

end Local

/-! ### The good candidate theorem -/

section Main

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

/-- **A good candidate block exists when `Ψ < 0`** (package T3-20; replaces the obstruction-graph
pigeonhole and rerouting of arXiv 2305.15625 v1, L1150-1172, where the source set is strictly
larger than the obstruction set).

Let `G` be claw-free and `s`, `s'` hole-class states with `Ψ(s, s') < 0`.  Write
`B ∩ W = B.support ∩ matchedW s s'` and `B ∩ X = B.support ∩ crossedW s s'` for a side block `B`.
Then one of the following holds:
* (i) some side block `B` of `(s, s')` runs forward from `s` and backward from `s'` and has
  `|B ∩ matchedW s s'| = 1`, `|B ∩ crossedW s s'| = 0` (the key `(1, 0, 1, 0)`);
* (ii) some side block of `(s, s')` is a good source (`SideBlock.GoodSource`);
* (iii) some side block of `(s', s)` is a good source (the mirror image).

The proof partitions `W ∪ W'` by side component and sums the signed counts of the four sets over
the components: the total is `-Ψ(s, s') - Ψ(s', s) = -2 Ψ(s, s') > 0`
(`pairingIndex_eq_card_sub_card`, `pairingIndex_comm`), so some component has a positive
contribution, and `hasGoodCandidate_of_component` turns it into a block.  A component of the
second side graph is treated through `(s.swap, s'.swap)` (`HasGoodCandidate.swap`). -/
theorem exists_goodCandidate (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hneg : G.pairingIndex s s' < 0) :
    (∃ B : G.SideBlock s s', B.RunsFrom ∧ B.RunsBack ∧ (B.support ∩ G.matchedW s s').card = 1 ∧
        (B.support ∩ G.crossedW s s').card = 0) ∨
      (∃ B : G.SideBlock s s', B.GoodSource) ∨ (∃ B : G.SideBlock s' s, B.GoodSource) := by
  show G.HasGoodCandidate s s'
  -- the sets involved
  set M := G.matchedW s s' with hM
  set Xc := G.crossedW s s' with hXc
  set M' := G.matchedW s' s with hM'
  set X' := G.crossedW s' s with hX'
  set D₁ : Finset V := symmDiff s.1 s'.1 with hD₁
  set D₂ : Finset V := symmDiff s.2 s'.2 with hD₂
  set U : Finset V := (M ∪ Xc) ∪ (M' ∪ X') with hU
  set T₁ : Finset (Finset V) := (U ∩ D₁).image (G.componentFinset D₁) with hT₁
  set T₂ : Finset (Finset V) := (U ∩ D₂).image (G.componentFinset D₂) with hT₂
  -- sidedness of the vertices of `W` and of `W'`
  have hside : ∀ w ∈ M ∪ Xc, (w ∈ D₁ ∨ w ∈ D₂) ∧ ¬(w ∈ D₁ ∧ w ∈ D₂) := fun w hw =>
    mem_exactly_one_side_of_mem_W hs hs' hw
  have hside' : ∀ w ∈ M' ∪ X', (w ∈ D₁ ∨ w ∈ D₂) ∧ ¬(w ∈ D₁ ∧ w ∈ D₂) := fun w hw => by
    have := mem_exactly_one_side_of_mem_W hs' hs hw
    rwa [symmDiff_comm s'.1 s.1, symmDiff_comm s'.2 s.2] at this
  -- partition of a subset of `U` by side components
  have key : ∀ S : Finset V, S ⊆ U → (∀ w ∈ S, (w ∈ D₁ ∨ w ∈ D₂) ∧ ¬(w ∈ D₁ ∧ w ∈ D₂)) →
      (S.card : ℤ) = ∑ K ∈ T₁, ((S ∩ K).card : ℤ) + ∑ K ∈ T₂, ((S ∩ K).card : ℤ) := by
    intro S hSU hSside
    have h0 := card_eq_card_inter_add_of_exactly_one_mem S D₁ D₂ (fun w hw => (hSside w hw).1)
      (fun w hw => (hSside w hw).2)
    have h1 := card_inter_eq_sum_components (G := G) D₁ S T₁
      (fun u hu => Finset.mem_image.2 ⟨u, Finset.mem_inter.2
        ⟨hSU (Finset.mem_inter.1 hu).1, (Finset.mem_inter.1 hu).2⟩, rfl⟩)
      (fun K hK => by
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hK
        exact ⟨w, (Finset.mem_inter.1 hw).2, rfl⟩)
    have h2 := card_inter_eq_sum_components (G := G) D₂ S T₂
      (fun u hu => Finset.mem_image.2 ⟨u, Finset.mem_inter.2
        ⟨hSU (Finset.mem_inter.1 hu).1, (Finset.mem_inter.1 hu).2⟩, rfl⟩)
      (fun K hK => by
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hK
        exact ⟨w, (Finset.mem_inter.1 hw).2, rfl⟩)
    rw [h0, h1, h2]
    push_cast
    rfl
  have kM := key M (fun w hw => by
      simp only [hU, Finset.mem_union]; exact Or.inl (Or.inl hw))
    (fun w hw => hside w (Finset.mem_union_left _ hw))
  have kXc := key Xc (fun w hw => by
      simp only [hU, Finset.mem_union]; exact Or.inl (Or.inr hw))
    (fun w hw => hside w (Finset.mem_union_right _ hw))
  have kM' := key M' (fun w hw => by
      simp only [hU, Finset.mem_union]; exact Or.inr (Or.inl hw))
    (fun w hw => hside' w (Finset.mem_union_left _ hw))
  have kX' := key X' (fun w hw => by
      simp only [hU, Finset.mem_union]; exact Or.inr (Or.inr hw))
    (fun w hw => hside' w (Finset.mem_union_right _ hw))
  -- the total contribution is `-2 Ψ > 0`
  have hΨ := pairingIndex_eq_card_sub_card hclaw hs hs'
  have hΨ' := pairingIndex_eq_card_sub_card hclaw hs' hs
  have hcomm : G.pairingIndex s s' = G.pairingIndex s' s := pairingIndex_comm
  set q : Finset V → ℤ := fun K =>
    ((M ∩ K).card : ℤ) - (Xc ∩ K).card + (M' ∩ K).card - (X' ∩ K).card with hq
  have hsum : ∑ K ∈ T₁, q K + ∑ K ∈ T₂, q K =
      (M.card : ℤ) - Xc.card + M'.card - X'.card := by
    simp only [hq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linarith
  have hpos : 0 < ∑ K ∈ T₁, q K + ∑ K ∈ T₂, q K := by
    rw [hsum]
    linarith
  have hex : (∃ K ∈ T₁, 0 < q K) ∨ (∃ K ∈ T₂, 0 < q K) := by
    by_contra hcon
    have h1 : ∑ K ∈ T₁, q K ≤ 0 :=
      Finset.sum_nonpos fun K hK => not_lt.1 fun h => hcon (Or.inl ⟨K, hK, h⟩)
    have h2 : ∑ K ∈ T₂, q K ≤ 0 :=
      Finset.sum_nonpos fun K hK => not_lt.1 fun h => hcon (Or.inr ⟨K, hK, h⟩)
    linarith
  rcases hex with ⟨K, hK, hKq⟩ | ⟨K, hK, hKq⟩
  · -- a component of the first side graph
    obtain ⟨w, hw, hwK⟩ := Finset.mem_image.1 hK
    have hK' : (K ∩ Xc).card + (K ∩ X').card < (K ∩ M).card + (K ∩ M').card := by
      simp only [hq] at hKq
      simp only [Finset.inter_comm K]
      omega
    exact hasGoodCandidate_of_component hclaw hs hs' (Finset.mem_inter.1 hw).2 hwK.symm hK'
  · -- a component of the second side graph: pass to `(s.swap, s'.swap)`
    obtain ⟨w, hw, hwK⟩ := Finset.mem_image.1 hK
    have hK' : (K ∩ Xc).card + (K ∩ X').card < (K ∩ M).card + (K ∩ M').card := by
      simp only [hq] at hKq
      simp only [Finset.inter_comm K]
      omega
    have hK'' : (K ∩ G.crossedW s.swap s'.swap).card + (K ∩ G.crossedW s'.swap s.swap).card <
        (K ∩ G.matchedW s.swap s'.swap).card + (K ∩ G.matchedW s'.swap s.swap).card := by
      rw [crossedW_swap_swap, crossedW_swap_swap, matchedW_swap_swap, matchedW_swap_swap]
      exact hK'
    have hcand := hasGoodCandidate_of_component hclaw hs.swap hs'.swap
      (v := w) (K := K) (Finset.mem_inter.1 hw).2 hwK.symm hK''
    have := hcand.swap
    rwa [Prod.swap_swap, Prod.swap_swap] at this

end Main

end SimpleGraph
