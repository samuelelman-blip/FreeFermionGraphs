import FreeFermionGraphs.T3BlockPathBridge
import FreeFermionGraphs.T3PairingIndexCount

/-!
# The component tether lemma: matched versus crossed `W` on a side component

This module is the componentwise form of the tether pairing in the proof of Theorem 1 (ii)
(arXiv 2305.15625 v1, L906-911: "each such vertex initializes a deformation path, but may be
tethered.  If every such initializing vertex is tethered, then they can be uniquely paired, which
contradicts the assumption that `h_S` and `h_C` anticommute.  Thus, there is at least one
untethered path") and of the tethering discussion of v1 L762-766 (Fig. `deformationsequence`).  It
replaces the history-dependent "pending vertex" analysis of the obstruction search of v1 by a
statement about a single component of a side graph.

Let `s = (A, B)` and `s' = (A', B')` be hole-class states (the colouring classes of two even holes
`C = A ∪ B` and `C' = A' ∪ B'`) of a claw-free graph, and let `K` be a component of `G[A ⊕ A']`
(the *side graph* of the first colour class).  The vertices of `C'` whose term anticommutes with
`h_C` are the disjoint union of the *matched* vertices (clones in `C` of a vertex of the same
colour class, `SimpleGraph.matchedW`) and the *crossed* vertices (clones of a vertex of the other
class, `SimpleGraph.crossedW`); see `anticommutingVertices_eq_matchedW_union_crossedW`.  A vertex
of `K` can be neither in `B'` (since `K ⊆ A ⊕ A'`) nor in `A` (since `W ∩ C = ∅`), so the matched
vertices of `K` are the clones of an `A`-vertex lying in `A'`, and the crossed vertices of `K` are
the clones of a `B`-vertex lying in `A'`.

## Main definitions and results

* `SimpleGraph.componentFinset G X v`: the component of `v` in `G[X]`, as a `Finset`
  (`mem_componentFinset`).
* `SimpleGraph.component_matched_le_crossed` (v1 L906-911): with `m = |K ∩ matchedW s s'|` and
  `x = |K ∩ crossedW s s'|`, either `m ≤ x`, or `K` is the support of an `OddBlock Q` of
  `(s.1, s'.1)` which runs from `s` and has `(m, x) = (1, 0)`.
* `SimpleGraph.OddBlock.card_matchedW_le_one` (v1 L764, the block `P` has a single initialising
  vertex `s_0`): an `OddBlock` of `(s.1, s'.1)` contains at most one matched vertex.  Together
  with the previous result this gives `m ≤ 1` on every component with `m > x`.
* `SimpleGraph.OddBlock.eq_first_of_mem_matchedW`: more precisely, the matched vertex of a
  block, if any, is its first vertex.
* Path-level facts used in the proofs:
  `EvenHoleLabeling.SetDeformationPath.support_inter_matchedW` (`P.support ∩ matchedW s s' =
  {s_0}`), `support_inter_crossedW` (`P.support ∩ crossedW s s' = ∅`), `tether_mem_crossedW` (the
  tether of a deformation path is a crossed vertex), `tether_mem_of_first_mem` (it lies in the
  same component as `s_0`).

The same statements hold for the second colour classes by `matchedW_swap_swap`,
`crossedW_swap_swap` (apply the results to `s.swap`, `s'.swap`), and for the primed counts
`m' = |K ∩ matchedW s' s|`, `x' = |K ∩ crossedW s' s|` by applying them to `(s', s)`.

## Proof of `component_matched_le_crossed`

Fix a full-cyclic labelling `L` of `C` with `{a_i} = A`.  A matched vertex `w ∈ K` is a clone of
some `a_i`, so `CloneAt.exists_setDeformationPath` gives a maximal deformation path `P` of `L`
along `A'` initialised by `s_0 = w`.

* If some such `P` is *untethered*, its support is a component of `G[A' ⊕ A]` containing `w`, hence
  equals `K`.  The bridge `OddBlock.exists_of_untethered` (work package T3-18) turns it into a
  forward-running `OddBlock` with support `K`.  The vertices `a_{i_j}` lie in `C`, so they are not
  in `W`; `s_0` is matched (it is a clone of `a_{i_0}`), and `s_j` for `j ≥ 1` is not in `W`:
  it has the two `B`-neighbours of `a_{i_j}` and the two `A`-neighbours `a_{i_{j-1}}`,
  `a_{i_j}`, whereas a clone of an `A`-vertex has one `A`-neighbour and a clone of a `B`-vertex
  has one `B`-neighbour.  So `(m, x) = (1, 0)`.
* If every such `P` is *tethered*, each matched `w ∈ K` is paired with a tether `t = τ(w)`.  The
  last replaced vertex `a_{i_{ℓ-1}}` lies in `K` (the path is connected through `S ⊕ C_a`), and
  `t ∈ A' ∖ A` is adjacent to it, so `t ∈ K` by closedness of the component.  The tether is a
  clone of a `b`-vertex, i.e. `t` is crossed.  The map `τ` is injective because tethering is a
  symmetric relation with unique partners (`TetherPair.symm`, `TetherPair.unique`).  Hence
  `m ≤ x`.

## Hypotheses

Claw-freeness is used through `exists_setDeformationPath`, `exists_of_untethered` and the tether
involution.  `OddBlock.card_matchedW_le_one` does not use claw-freeness (the hypothesis `_hclaw`
is kept so that the statement has the shape recorded in the work package); it uses only the clone
counts of hole-class states.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### The component of a vertex as a finset -/

/-- The component of `v` in the subgraph `G[X]` induced by the finset `X`, as a finset
(`SimpleGraph.inducedComponentSet`, the vertices of `X` reachable from `v` inside `G[X]`; empty if
`v ∉ X`).  For `X = s.1 ⊕ s'.1` this is the component `K` of the side graph used in the tether
lemma `component_matched_le_crossed`. -/
noncomputable def componentFinset (G : SimpleGraph V) [Fintype V] (X : Finset V) (v : V) :
    Finset V := by
  classical exact Finset.univ.filter (· ∈ G.inducedComponentSet ↑X v)

/-- Membership in `componentFinset`, unfolded. -/
theorem mem_componentFinset [Fintype V] {X : Finset V} {v w : V} :
    w ∈ G.componentFinset X v ↔ w ∈ G.inducedComponentSet (↑X : Set V) v := by
  classical
  unfold componentFinset
  simp

/-! ### Clone data of a labelling at the carrier level -/

namespace EvenHoleLabeling

variable {k : ℕ}

/-- A labelled clone `L.CloneAt j i` is a carrier-level clone `j ≺_{C} a_i` of the carrier of
`L` (v1 Definition 10, L682). -/
theorem CloneAt.isCloneIn_carrier {L : G.EvenHoleLabeling k} {j : V} {i : Fin k}
    (h : L.CloneAt j i) : G.IsCloneIn L.carrier j (L.a i) :=
  ⟨h.outside, L.a_mem_carrier i, h.adj_iff⟩

/-- The carrier of a labelling whose colour classes are those of a hole-class state `s` is the
carrier `s.1 ∪ s.2` of the state. -/
theorem carrier_eq_coe_union_of_image [DecidableEq V] {L : G.EvenHoleLabeling k}
    {s : Finset V × Finset V} (ha : Finset.univ.image L.a = s.1)
    (hb : Finset.univ.image L.b = s.2) : L.carrier = ↑(s.1 ∪ s.2) := by
  rw [← ha, ← hb]
  exact L.coe_image_a_union_image_b.symm

end EvenHoleLabeling

/-! ### Matched vertices inside a side graph -/

section Matched

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- A matched vertex lying in the symmetric difference `s.1 ⊕ s'.1` is a vertex of `s'.1` outside
the carrier of `s` which is a clone of a vertex of `s.1`: the second kind of matched vertex
(`w ∈ s'.2`) is neither in `s.1` (it lies outside `C`) nor in `s'.1` (the classes of `s'` are
disjoint). -/
theorem mem_matchedW_of_mem_symmDiff (hs' : G.IsHoleClasses s') {w : V}
    (hw : w ∈ G.matchedW s s') (hsd : w ∈ symmDiff s.1 s'.1) :
    w ∈ s'.1 ∧ w ∉ s.1 ∪ s.2 ∧ ∃ k ∈ s.1, G.IsCloneIn (↑(s.1 ∪ s.2) : Set V) w k := by
  rw [mem_matchedW] at hw
  rcases hw with h | ⟨h1, h2, -⟩
  · exact h
  · exfalso
    rw [Finset.mem_symmDiff] at hsd
    rcases hsd with ⟨h3, -⟩ | ⟨h3, -⟩
    · exact h2 (Finset.mem_union_left _ h3)
    · exact Finset.disjoint_left.1 hs'.disjoint h3 h1

end Matched

/-! ### Deformation paths and the sets `matchedW`, `crossedW` -/

namespace EvenHoleLabeling

namespace SetDeformationPath

variable [DecidableEq V] {k : ℕ} {L : G.EvenHoleLabeling k} {s s' : Finset V × Finset V}

/-- The vertex `s_j` of a deformation path has the two `B`-neighbours of `a_{i_j}`
(`adj_s_iff_adj_a_b`), so exactly two neighbours in the second colour class. -/
theorem card_filter_snd_adj_s [DecidableRel G.Adj] (hs : G.IsHoleClasses s)
    (ha : Finset.univ.image L.a = s.1) (hb : Finset.univ.image L.b = s.2) {S : Finset V}
    (P : L.SetDeformationPath S) (j : Fin P.len) : (s.2.filter (G.Adj (P.s j))).card = 2 := by
  have h : s.2.filter (G.Adj (P.s j)) = s.2.filter (G.Adj (L.a (P.idx j))) := by
    apply Finset.filter_congr
    intro y hy
    rw [← hb] at hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact P.adj_s_iff_adj_a_b j q
  rw [h]
  exact hs.card_filter_snd_of_mem_fst (ha ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))

/-- For `j ≥ 1` the vertex `s_j` has at least two neighbours in the first colour class, namely
`a_{i_{j-1}}` and `a_{i_j}`. -/
theorem one_lt_card_filter_fst_adj_s [DecidableRel G.Adj] (ha : Finset.univ.image L.a = s.1)
    {S : Finset V} (P : L.SetDeformationPath S) {j : Fin P.len} (hj : j ≠ P.first) :
    1 < (s.1.filter (G.Adj (P.s j))).card := by
  have hj0 : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (Fin.ext h) hj
    · exact h
  have hj1 : j.val - 1 < P.len := by have := j.isLt; omega
  have hne : L.a (P.idx ⟨j.val - 1, hj1⟩) ≠ L.a (P.idx j) := fun e => by
    have := congrArg Fin.val (P.idx_injective (L.a_injective e))
    simp only at this
    omega
  have hmem : ∀ q, L.a q ∈ s.1 := fun q => ha ▸ Finset.mem_image_of_mem _ (Finset.mem_univ q)
  refine Finset.one_lt_card.2 ⟨L.a (P.idx ⟨j.val - 1, hj1⟩), ?_, L.a (P.idx j), ?_, hne⟩
  · exact Finset.mem_filter.2 ⟨hmem _, P.link ⟨j.val - 1, hj1⟩ j (by simp only; omega)⟩
  · exact Finset.mem_filter.2 ⟨hmem _, P.adj_a_idx j⟩

/-- The initialising vertex `s_0` of a deformation path along `s'.1` is a matched vertex: it lies
in `s'.1`, outside `C`, and is a clone of `a_{i_0} ∈ s.1`. -/
theorem s_first_mem_matchedW (ha : Finset.univ.image L.a = s.1)
    (hb : Finset.univ.image L.b = s.2) (P : L.SetDeformationPath s'.1) :
    P.s P.first ∈ G.matchedW s s' := by
  rw [mem_matchedW]
  left
  have hcar := carrier_eq_coe_union_of_image ha hb
  refine ⟨P.s_mem _, fun h => P.cloneAt_first_step.outside ?_, L.a (P.idx P.first), ?_, ?_⟩
  · rw [hcar]
    exact Finset.mem_coe.2 h
  · rw [← ha]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · rw [← hcar]
    exact P.cloneAt_first_step.isCloneIn_carrier

/-- For `j ≠ 0` the vertex `s_j` of a deformation path is not matched: a matched vertex has one
neighbour in `s.1`, whereas `s_j` is adjacent to `a_{i_{j-1}}` and `a_{i_j}`. -/
theorem s_not_mem_matchedW_of_ne_first (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (ha : Finset.univ.image L.a = s.1) (P : L.SetDeformationPath s'.1) {j : Fin P.len}
    (hj : j ≠ P.first) : P.s j ∉ G.matchedW s s' := by
  classical
  intro hm
  rw [mem_matchedW] at hm
  rcases hm with ⟨-, -, k, hk, hcl⟩ | ⟨h1, -, -⟩
  · have h1 := (hs.clone_counts_fst hcl hk).1
    have h2 := P.one_lt_card_filter_fst_adj_s ha hj
    omega
  · exact Finset.disjoint_left.1 hs'.disjoint (P.s_mem j) h1

/-- No vertex `s_j` of a deformation path is crossed: a crossed vertex of `s'.1` has one neighbour
in `s.2`, whereas `s_j` has the two `B`-neighbours of `a_{i_j}`. -/
theorem s_not_mem_crossedW (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (ha : Finset.univ.image L.a = s.1) (hb : Finset.univ.image L.b = s.2)
    (P : L.SetDeformationPath s'.1) (j : Fin P.len) : P.s j ∉ G.crossedW s s' := by
  classical
  intro hm
  rw [mem_crossedW] at hm
  rcases hm with ⟨-, -, k, hk, hcl⟩ | ⟨h1, -, -⟩
  · have h1 := (hs.clone_counts_snd hcl hk).1
    have h2 := P.card_filter_snd_adj_s hs ha hb j
    omega
  · exact Finset.disjoint_left.1 hs'.disjoint (P.s_mem j) h1

/-- The matched vertices on the support of a deformation path: only the initialising vertex
`s_0` (the `a_{i_j}` lie in `C`, and `s_j`, `j ≥ 1`, is not in `W`). -/
theorem support_inter_matchedW (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (ha : Finset.univ.image L.a = s.1) (hb : Finset.univ.image L.b = s.2)
    (P : L.SetDeformationPath s'.1) : P.support ∩ G.matchedW s s' = {P.s P.first} := by
  ext v
  rw [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hm⟩
    rcases P.mem_support_iff.1 hv with ⟨j, rfl | rfl⟩
    · by_contra hne
      exact P.s_not_mem_matchedW_of_ne_first hs hs' ha (j := j) (fun e => hne (by rw [e])) hm
    · exfalso
      have h := (Finset.mem_sdiff.1 (matchedW_subset_sdiff hm)).2
      exact h (Finset.mem_union_left _ (ha ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  · rintro rfl
    exact ⟨P.s_mem_support _, P.s_first_mem_matchedW ha hb⟩

/-- No vertex on the support of a deformation path is crossed. -/
theorem support_inter_crossedW (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (ha : Finset.univ.image L.a = s.1) (hb : Finset.univ.image L.b = s.2)
    (P : L.SetDeformationPath s'.1) : P.support ∩ G.crossedW s s' = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro v hv
  obtain ⟨hv, hc⟩ := Finset.mem_inter.1 hv
  rcases P.mem_support_iff.1 hv with ⟨j, rfl | rfl⟩
  · exact P.s_not_mem_crossedW hs hs' ha hb j hc
  · have h := (Finset.mem_sdiff.1 (crossedW_subset_sdiff hc)).2
    exact h (Finset.mem_union_left _ (ha ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)))

/-! #### The component of the initialising vertex -/

/-- The support of a deformation path lies in any component `K` of `G[S ⊕ C_a]` that contains the
initialising vertex `s_0`: the path `s_0 - a_{i_0} - s_1 - ⋯` is connected inside `S ⊕ C_a`
(v1 L764). -/
theorem coe_support_subset_of_first_mem {S : Finset V} (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) {K : Set V}
    (hK : G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.a)) K)
    (h0 : P.s P.first ∈ K) : (↑P.support : Set V) ⊆ K := by
  have hsU : ∀ j : Fin P.len, P.s j ∈ (↑(symmDiff S (Finset.univ.image L.a)) : Set V) := fun j =>
    Finset.mem_coe.2 (Finset.mem_symmDiff.2 (Or.inl ⟨P.s_mem j, P.s_not_mem_image_a hS j⟩))
  have haU : ∀ j : Fin P.len,
      L.a (P.idx j) ∈ (↑(symmDiff S (Finset.univ.image L.a)) : Set V) := fun j =>
    Finset.mem_coe.2 (Finset.mem_symmDiff.2
      (Or.inr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), P.a_idx_not_mem hS j⟩))
  have key : ∀ (m : ℕ) (hm : m < P.len), P.s ⟨m, hm⟩ ∈ K := by
    intro m
    induction m with
    | zero => intro hm; exact h0
    | succ m ih =>
        intro hm
        have hm' : m < P.len := by omega
        have haK : L.a (P.idx ⟨m, hm'⟩) ∈ K :=
          hK.2.2 (ih hm') (haU ⟨m, hm'⟩) (P.adj_a_idx ⟨m, hm'⟩)
        exact hK.2.2 haK (hsU ⟨m + 1, hm⟩) (P.link ⟨m, hm'⟩ ⟨m + 1, hm⟩ rfl).symm
  intro v hv
  rcases P.mem_support_iff.1 (Finset.mem_coe.1 hv) with ⟨j, rfl | rfl⟩
  · exact key j.val j.isLt
  · exact hK.2.2 (key j.val j.isLt) (haU j) (P.adj_a_idx j)

/-- **The tether lies in the component of the initialising vertex** (v1 L762-763): the tether `t`
is adjacent to the last replaced vertex `a_{i_{ℓ-1}}`, which lies in the component `K` of
`G[S ⊕ C_a]` containing `s_0`, and `t ∈ S ∖ C_a`, so `t ∈ K` by closedness of the component. -/
theorem tether_mem_of_first_mem {S : Finset V} (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) {K : Set V}
    (hK : G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.a)) K)
    (h0 : P.s P.first ∈ K) {t : V} (ht : P.TetheredTo t) : t ∈ K := by
  obtain ⟨htS, -, hadj, -⟩ := ht
  have haK : L.a (P.idx P.last) ∈ K :=
    P.coe_support_subset_of_first_mem hS hK h0 (Finset.mem_coe.2 (P.a_idx_mem_support _))
  have htA : t ∉ Finset.univ.image L.a := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro q hq
    exact L.adj_aa q (P.idx P.last) (hq ▸ hadj)
  exact hK.2.2 haK (Finset.mem_coe.2 (Finset.mem_symmDiff.2 (Or.inl ⟨htS, htA⟩))) hadj.symm

/-- **The tether of a deformation path is a crossed vertex** (v1 L763): the tether `t ∈ S ∖ C` is
a clone of a `b`-vertex of `C` (a clone for the colour swap), lies in `s'.1`, so it is a crossed
vertex. -/
theorem tether_mem_crossedW (ha : Finset.univ.image L.a = s.1)
    (hb : Finset.univ.image L.b = s.2) (P : L.SetDeformationPath s'.1) {t : V}
    (ht : P.TetheredTo t) : t ∈ G.crossedW s s' := by
  obtain ⟨htS, -, -, r, hr⟩ := ht
  have hcar := carrier_eq_coe_union_of_image ha hb
  rw [mem_crossedW]
  left
  refine ⟨htS, fun h => hr.outside ?_, L.swapColors.a r, ?_, ?_⟩
  · rw [swapColors_carrier, hcar]
    exact Finset.mem_coe.2 h
  · rw [swapColors_a, ← hb]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · have h := hr.isCloneIn_carrier
    rwa [swapColors_carrier, hcar] at h

end SetDeformationPath

end EvenHoleLabeling

/-! ### The component tether lemma -/

section Main

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **The component tether lemma, part (i)** (v1 L906-911, L762-766; work package T3-19).

Let `G` be claw-free, `s`, `s'` hole-class states and `K` the component of `v ∈ s.1 ⊕ s'.1` in
`G[s.1 ⊕ s'.1]` (`componentFinset`).  With `m = |K ∩ matchedW s s'|` and
`x = |K ∩ crossedW s s'|`, either `m ≤ x`, or `K` is the support of an `OddBlock Q` of
`(s.1, s'.1)` which runs from `s` (`OddBlock.RunsFrom`) and has `(m, x) = (1, 0)`.

In the second case a matched vertex of `K` initialises an *untethered* deformation path
(v1 L764), which the bridge `OddBlock.exists_of_untethered` turns into a forward-running block;
otherwise every matched vertex of `K` is tethered (v1 L762-763) to a crossed vertex of `K`, and
tethering is an injective map from the matched to the crossed vertices of `K`
(`EvenHoleLabeling.TetherPair.symm`, `EvenHoleLabeling.TetherPair.unique`).

The same holds for the second colour classes via `matchedW_swap_swap`, `crossedW_swap_swap`
(apply it to `s.swap`, `s'.swap`), and for the primed counts `m' = |K ∩ matchedW s' s|`,
`x' = |K ∩ crossedW s' s|` by applying it to `(s', s)`. -/
theorem component_matched_le_crossed [Fintype V] (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {v : V}
    (hv : v ∈ symmDiff s.1 s'.1) :
    (G.componentFinset (symmDiff s.1 s'.1) v ∩ G.matchedW s s').card ≤
        (G.componentFinset (symmDiff s.1 s'.1) v ∩ G.crossedW s s').card ∨
      ∃ Q : G.OddBlock s.1 s'.1, Q.support = G.componentFinset (symmDiff s.1 s'.1) v ∧
        Q.RunsFrom s ∧ (Q.support ∩ G.matchedW s s').card = 1 ∧
        (Q.support ∩ G.crossedW s s').card = 0 := by
  obtain ⟨n, L, hL, ha, hb⟩ := id hs
  have hS : G.IsIndepSet (↑s'.1 : Set V) := hs'.isIndepSet_fst
  have hX : symmDiff s.1 s'.1 = symmDiff s'.1 (Finset.univ.image L.a) := by
    rw [ha]
    exact symmDiff_comm _ _
  obtain ⟨K, hKdef⟩ : ∃ K : Set V, K = G.inducedComponentSet (↑(symmDiff s.1 s'.1) : Set V) v :=
    ⟨_, rfl⟩
  have hmemK : ∀ w, w ∈ G.componentFinset (symmDiff s.1 s'.1) v ↔ w ∈ K := fun w => by
    rw [mem_componentFinset, hKdef]
  have hKcomp : G.IsInducedComponent ↑(symmDiff s.1 s'.1) K := by
    rw [hKdef]
    exact isInducedComponent_inducedComponentSet (Finset.mem_coe.2 hv)
  have hKcomp' : G.IsInducedComponent ↑(symmDiff s'.1 (Finset.univ.image L.a)) K := by
    rw [← hX]
    exact hKcomp
  by_cases hA : ∃ w ∈ G.componentFinset (symmDiff s.1 s'.1) v ∩ G.matchedW s s',
      ∃ P : L.SetDeformationPath s'.1, P.s P.first = w ∧ P.Untethered
  · -- some matched vertex of `K` initialises an untethered path: `K` is a forward-running block
    right
    obtain ⟨w, hw, P, hP0, hPU⟩ := hA
    have hwK : w ∈ K := (hmemK w).1 (Finset.mem_inter.1 hw).1
    have hwP : w ∈ (↑P.support : Set V) := by
      rw [← hP0]
      exact Finset.mem_coe.2 (P.s_mem_support _)
    have hset : (↑P.support : Set V) = K :=
      eq_of_isInducedComponent_of_mem hPU hKcomp' hwP hwK
    have hsupp : P.support = G.componentFinset (symmDiff s.1 s'.1) v := by
      ext x
      rw [hmemK, ← hset]
      exact Finset.mem_coe
    obtain ⟨Q, hQs, -, hQr⟩ := OddBlock.exists_of_untethered hclaw hs hs' hL ha hb P hPU
    refine ⟨Q, hQs.trans hsupp, hQr, ?_, ?_⟩
    · rw [hQs, P.support_inter_matchedW hs hs' ha hb, Finset.card_singleton]
    · rw [hQs, P.support_inter_crossedW hs hs' ha hb, Finset.card_empty]
  · -- every matched vertex of `K` is tethered, to a crossed vertex of `K`
    left
    push Not at hA
    have hex : ∀ w, w ∈ G.componentFinset (symmDiff s.1 s'.1) v ∩ G.matchedW s s' →
        ∃ t, EvenHoleLabeling.TetherPair L s'.1 w t ∧
          t ∈ G.componentFinset (symmDiff s.1 s'.1) v ∩ G.crossedW s s' := by
      intro w hw
      obtain ⟨hwc, hwm⟩ := Finset.mem_inter.1 hw
      have hwK : w ∈ K := (hmemK w).1 hwc
      have hwX : w ∈ symmDiff s.1 s'.1 := Finset.mem_coe.1 (hKcomp.1 hwK)
      obtain ⟨hw1, -, k, hk, hcl⟩ := mem_matchedW_of_mem_symmDiff hs' hwm hwX
      obtain ⟨i, rfl⟩ : ∃ i, L.a i = k := by
        rw [← ha] at hk
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hk
        exact ⟨i, hi⟩
      have hcl' : L.CloneAt w i := L.cloneAt_of_isCloneIn (by rw [ha, hb]; exact hcl)
      obtain ⟨P, hP0, -, hP, -⟩ := EvenHoleLabeling.CloneAt.exists_setDeformationPath hclaw hL hS
        hw1 hcl'
      rcases hP with hU | ⟨t, ht⟩
      · exact (hA w hw P hP0 hU).elim
      · refine ⟨t, Or.inl ⟨P, hP0, ht⟩, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
        · refine (hmemK t).2 (P.tether_mem_of_first_mem hS hKcomp' ?_ ht)
          rw [hP0]
          exact hwK
        · exact P.tether_mem_crossedW ha hb ht
    haveI : Nonempty V := ⟨v⟩
    choose! τ hτ using hex
    refine Finset.card_le_card_of_injOn τ (fun w hw => (hτ w hw).2) ?_
    intro w₁ hw₁ w₂ hw₂ heq
    have h1 := (hτ w₁ hw₁).1
    have h2 := (hτ w₂ hw₂).1
    rw [← heq] at h2
    exact EvenHoleLabeling.TetherPair.unique hclaw hL hS
      (EvenHoleLabeling.TetherPair.symm hclaw hS h1).2.2
      (EvenHoleLabeling.TetherPair.symm hclaw hS h2).2.2

end Main

/-! ### Odd blocks contain at most one matched vertex -/

namespace OddBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **A matched vertex of an odd block is its first vertex** (v1 L764: the block
`s_0 - a_{i_0} - s_1 - ⋯` has the single initialising vertex `s_0`, a clone of one `a`-vertex).

A matched vertex `w` of an `OddBlock Q` of `(s.1, s'.1)` lies in `s'.1 ∖ C` and has exactly one
neighbour in `s.1` (it is a clone of a vertex of `s.1`).  It sits at an even position `2c` of the
path, whose neighbours at the odd positions `2c ± 1` lie in `s.1 ∖ s'.1`.  If `c ≥ 1` there are
two such neighbours, a contradiction; so `c = 0` and `w = Q.first`. -/
theorem eq_first_of_mem_matchedW (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (Q : G.OddBlock s.1 s'.1) {w : V} (hwQ : w ∈ Q.support) (hwM : w ∈ G.matchedW s s') :
    w = Q.first := by
  classical
  obtain ⟨hw1, hwC, k, hk, hcl⟩ :=
    mem_matchedW_of_mem_symmDiff hs' hwM (Q.support_subset_symmDiff hwQ)
  have hcount := (hs.clone_counts_fst hcl hk).1
  obtain ⟨i, rfl⟩ := OddBlock.mem_support.1 hwQ
  obtain ⟨r, hr⟩ := Q.even_card
  have hi := i.isLt
  rcases Nat.even_or_odd' i.val with ⟨c, hc | hc⟩
  · -- even position `2c`
    by_cases hc0 : c = 0
    · exact congrArg Q.path.vertex (Fin.ext (by simp [hc, hc0]))
    · exfalso
      have h1 : i.val - 1 < Q.path.card := by omega
      have h2 : i.val + 1 < Q.path.card := by omega
      have hodd1 : Odd (⟨i.val - 1, h1⟩ : Fin Q.path.card).val :=
        ⟨c - 1, by simp only; omega⟩
      have hodd2 : Odd (⟨i.val + 1, h2⟩ : Fin Q.path.card).val := ⟨c, by simp only; omega⟩
      have hmem1 : Q.path.vertex ⟨i.val - 1, h1⟩ ∈ s.1 := (Finset.mem_sdiff.1 (Q.mem_X _ hodd1)).1
      have hmem2 : Q.path.vertex ⟨i.val + 1, h2⟩ ∈ s.1 := (Finset.mem_sdiff.1 (Q.mem_X _ hodd2)).1
      have hadj1 : G.Adj (Q.path.vertex i) (Q.path.vertex ⟨i.val - 1, h1⟩) :=
        (Q.path.adj_iff _ _).2 (Or.inr (by simp only; omega))
      have hadj2 : G.Adj (Q.path.vertex i) (Q.path.vertex ⟨i.val + 1, h2⟩) :=
        (Q.path.adj_iff _ _).2 (Or.inl rfl)
      have hne : Q.path.vertex ⟨i.val - 1, h1⟩ ≠ Q.path.vertex ⟨i.val + 1, h2⟩ := fun e => by
        have := congrArg Fin.val (Q.path.injective e)
        simp only at this
        omega
      have hlt : 1 < (s.1.filter (G.Adj (Q.path.vertex i))).card :=
        Finset.one_lt_card.2 ⟨_, Finset.mem_filter.2 ⟨hmem1, hadj1⟩, _,
          Finset.mem_filter.2 ⟨hmem2, hadj2⟩, hne⟩
      omega
  · -- odd position: the vertex lies in `s.1`, contradicting `w ∉ C`
    exfalso
    have hodd : Odd i.val := ⟨c, hc⟩
    exact hwC (Finset.mem_union_left _ (Finset.mem_sdiff.1 (Q.mem_X i hodd)).1)

/-- **An odd block contains at most one matched vertex** (v1 L764; Theorem 1 (ii) tether
pairing, work package T3-19 (ii)).  Let `Q` be an `OddBlock` of `(s.1, s'.1)` for hole-class
states `s`, `s'`.  Then `|Q ∩ matchedW s s'| ≤ 1`: the matched vertex, if any, is the first
vertex `Q.first` (`eq_first_of_mem_matchedW`).

Claw-freeness is not needed (the hypothesis `_hclaw` records the shape of the work-package
statement): only the clone counts of a hole-class state enter. -/
theorem card_matchedW_le_one (_hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) :
    (Q.support ∩ G.matchedW s s').card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  obtain ⟨haQ, haM⟩ := Finset.mem_inter.1 ha
  obtain ⟨hbQ, hbM⟩ := Finset.mem_inter.1 hb
  exact (eq_first_of_mem_matchedW hs hs' Q haQ haM).trans
    (eq_first_of_mem_matchedW hs hs' Q hbQ hbM).symm

end OddBlock

end SimpleGraph
