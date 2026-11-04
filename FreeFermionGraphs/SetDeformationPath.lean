import FreeFermionGraphs.SymmDiffComponentToggle
import FreeFermionGraphs.Corollaries45
import FreeFermionGraphs.EvenHoleLabelingDeform
import FreeFermionGraphs.EvenHoleFullCyclicOrder
import FreeFermionGraphs.BubbleWandEventClassUnique

/-!
# Deformation of a labelled even hole along an independent set

This module formalises the informal paragraph of the manuscript (arXiv 2305.15625 v1,
Section "Neighboring Relations", L753-766 and Fig. `deformationsequence`), which is the
combinatorial core of the proof of Theorem 1 (ii) (v1 L904-927): the *deformation along a
path* of a labelled even hole `C` by an independent set `S`.

Let `L` be an alternating labelling of an even hole `C` (`|C| = 2k`, colour classes
`C_a = {a_i}`, `C_b = {b_i}`), let `S` be an independent finset of a claw-free graph and let
`s₀ ∈ S` be a clone of some `a_{i₀}` (`s₀ ≺_C a_{i₀}`).

* `SimpleGraph.EvenHoleLabeling.DeformsAlong` is the sequence of single-vertex deformations
  `C ⟶ C^{(0)} ⟶ C^{(1)} ⟶ ⋯` by the vertices `s₀, s₁, …` (v1 L762: "we call this sequential
  deformation by vertices in `P ∩ S` a deformation along the path `P`"), and
  `DeformsAlongAt` is the same notion with the replaced index `i_j` recorded at each step.
* `SetDeformationPath` is the datum `(s_j, i_j)_{j<ℓ}` of a deformation along an independent
  set: distinct `s_j ∈ S`, distinct indices `i_j`, each `s_j ≺_{C^{(j-1)}} a_{i_j}`, and
  `s_{j+1} ~ a_{i_j}` (v1 L762: "`s_{j+1}` is not neighboring to `s_j` but is neighboring to
  its clone `a_j ∈ C^{(j-1)}`").
* `SetDeformationPath.Untethered` says that `P = {s_j} ∪ {a_{i_j}}` is a whole connected
  component of `G[S ⊕ C_a]` (an induced path with `2ℓ - 1` edges, "untethered" in v1 L764);
  `SetDeformationPath.TetheredTo t` says that some `t ∈ S ∖ {s_j}` is adjacent to the last
  replaced vertex `a_{i_{ℓ-1}}` and is a clone of a `b`-vertex of `C` (three neighbours in
  `C`; v1 L763: "a vertex `s_ℓ` with only three neighbors in `C`, and we cannot deform by
  `s_ℓ` if it is present", i.e. `s₀` is *tethered* to `s_ℓ`).

The main results are

* `CloneAt.exists_setDeformationPath`: existence of the run starting from `s₀`, with the
  untethered/tethered dichotomy, the two alternatives being mutually exclusive;
* `SetDeformationPath.pairs_eq_of_start` and `SetDeformationPath.eq_of_start`: uniqueness of
  the run (its pairs `(s_j, i_j)`, hence its length and its support) given the initialising
  vertex `s₀`;
* `SetDeformationPath.len_le`: the bound `ℓ ≤ k` of v1 L765;
* `SetDeformationPath.adj_s_a_iff`, `crossCount_support`, `odd_crossCount_support`: the
  path `s₀ - a_{i₀} - s₁ - ⋯ - a_{i_{ℓ-1}}` is induced and has `2ℓ - 1` edges, so (when it is
  untethered) it is an odd component of `G[S ⊕ C_a]` in the sense of
  `card_and_tokenSlideReachable_symmDiff` (v1 L764).

Auxiliary facts on runs that are used downstream are also provided: the final labelling keeps
the `b`-vertices and `next` (`DeformsAlongAt.b_eq`, `next_eq`), has `s_j` at index `i_j`
(`SetDeformationPath.final_a_idx`) and the original `a`-vertices at all other indices
(`final_a_of_forall_ne`).

The step from `s_j` to `s_{j+1}` is Lemma 3 of v1 (repo `CloneAt.lemma8`): in its cases
(ii) and (iv) the neighbour `t ∈ S` of `a_{i_j}` is itself a clone in the deformed hole and
the run continues, while in the cases (i) and (iii) `t` has exactly three neighbours in `C`
and is a clone of a `b`-vertex (a clone for `L.swapColors`): the tether.

## Deviations from the informal text of the manuscript

* In `SetDeformationPath` the replaced indices `i_j` are recorded in the run itself
  (`DeformsAlongAt`), whereas a run `DeformsAlong S L (List.ofFn s) final` hides them
  existentially.  With hidden indices the field `idx` is not tied to the run, and the
  uniqueness statement is false (we did not formalise the counterexample): take `ℓ = 1` and
  `S = {s₀, t}` with `s₀ ≺_C a_{i₀}` untethered, `t` a clone of `b_r` for some `r` with
  `r, r - 1 ≠ i₀`, and `s₀`, `t` nonadjacent; then `(s := s₀, idx := r)` satisfies every field
  of the structure with the same hidden run, and is tethered to `t`, but its support
  `{s₀, a_r}` differs from the true support `{s₀, a_{i₀}}`.  The index-forgetting version of
  the run is recovered in `SetDeformationPath.run_forget`.
* v1 L762 calls `P` "the path component of `G[S ⊕ C_a]` with endpoint `s₀`".  In the
  tethered case the component of `G[S ⊕ C_a]` continues past `a_{i_{ℓ-1}}` through the tether
  vertex `t`, so the deformation path is the whole component only in the untethered case;
  this is why `Untethered` is a statement about the component and `TetheredTo` is not.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Connectivity helpers -/

/-- A single vertex induces a connected subgraph. -/
theorem connected_induce_singleton_set (v : V) : (G.induce ({v} : Set V)).Connected := by
  rw [connected_induce_iff_closed]
  refine ⟨⟨v, rfl⟩, fun A hAQ hA _ => ?_⟩
  obtain ⟨a, ha⟩ := hA
  refine Set.Subset.antisymm hAQ fun w hw => ?_
  have h1 : a = v := hAQ ha
  have h2 : w = v := hw
  rw [h2, ← h1]
  exact ha

/-- Adding a vertex adjacent to an existing vertex keeps an induced subgraph connected. -/
theorem connected_induce_insert_of_adj {Q : Set V} {x y : V} (hQ : (G.induce Q).Connected)
    (hx : x ∈ Q) (hxy : G.Adj x y) : (G.induce (insert y Q)).Connected := by
  rw [connected_induce_iff_closed] at hQ ⊢
  refine ⟨⟨y, Set.mem_insert _ _⟩, fun A hAQ hA hcl => ?_⟩
  by_cases hAQ' : (A ∩ Q).Nonempty
  · have hEq : A ∩ Q = Q :=
      hQ.2 (A ∩ Q) Set.inter_subset_right hAQ'
        (fun z w hz hw hzw => ⟨hcl hz.1 (Set.mem_insert_of_mem _ hw) hzw, hw⟩)
    have hxA : x ∈ A := by
      have : x ∈ A ∩ Q := hEq.symm ▸ hx
      exact this.1
    have hyA : y ∈ A := hcl hxA (Set.mem_insert _ _) hxy
    refine Set.Subset.antisymm hAQ (Set.insert_subset hyA fun q hq => ?_)
    have : q ∈ A ∩ Q := hEq.symm ▸ hq
    exact this.1
  · exfalso
    obtain ⟨a, ha⟩ := hA
    rcases Set.mem_insert_iff.1 (hAQ ha) with rfl | haQ
    · exact hAQ' ⟨x, hcl ha (Set.mem_insert_of_mem _ hx) hxy.symm, hx⟩
    · exact hAQ' ⟨a, ha, haQ⟩

namespace EvenHoleLabeling

/-! ### Runs of single-vertex deformations -/

/-- `L.DeformsAlong S ss L'`: the alternating labelling `L` is deformed successively by the
vertices `ss = [s₀, s₁, …]` of `S` (each one a clone of some `a`-vertex of the current hole),
ending at `L'`.  This is the sequence `C ⟶ C^{(0)} ⟶ C^{(1)} ⟶ ⋯` of v1 L760-762. -/
inductive DeformsAlong (S : Set V) {k : ℕ} :
    G.EvenHoleLabeling k → List V → G.EvenHoleLabeling k → Prop
  | nil (L : G.EvenHoleLabeling k) : DeformsAlong S L [] L
  | cons {L L' : G.EvenHoleLabeling k} {s : V} {i : Fin k} {rest : List V}
      (hs : s ∈ S) (h : L.CloneAt s i) :
      DeformsAlong S (L.deform h) rest L' → DeformsAlong S L (s :: rest) L'

/-- `L.DeformsAlongAt S ps L'`: as `DeformsAlong`, but the list `ps = [(s₀, i₀), (s₁, i₁), …]`
also records the index `i_j` of the `a`-vertex replaced by `s_j` at each step. -/
inductive DeformsAlongAt (S : Set V) {k : ℕ} :
    G.EvenHoleLabeling k → List (V × Fin k) → G.EvenHoleLabeling k → Prop
  | nil (L : G.EvenHoleLabeling k) : DeformsAlongAt S L [] L
  | cons {L L' : G.EvenHoleLabeling k} {s : V} {i : Fin k} {rest : List (V × Fin k)}
      (hs : s ∈ S) (h : L.CloneAt s i) :
      DeformsAlongAt S (L.deform h) rest L' → DeformsAlongAt S L ((s, i) :: rest) L'

/-- Forgetting the indices of a `DeformsAlongAt` run gives a `DeformsAlong` run. -/
theorem DeformsAlongAt.toDeformsAlong {S : Set V} {k : ℕ} {L L' : G.EvenHoleLabeling k}
    {ps : List (V × Fin k)} (hrun : L.DeformsAlongAt S ps L') :
    L.DeformsAlong S (ps.map Prod.fst) L' := by
  induction hrun with
  | nil L => exact .nil L
  | cons hs h _ ih => exact .cons hs h ih

/-! ### Local facts about clones and independent sets -/

section Local

variable {k : ℕ} {L : G.EvenHoleLabeling k} {s : V} {i : Fin k}

/-- A clone `s ≺_C a_i` is adjacent to exactly one `a`-vertex, namely `a_i`. -/
theorem CloneAt.adj_a_iff_index (h : L.CloneAt s i) (j : Fin k) : G.Adj s (L.a j) ↔ j = i := by
  constructor
  · intro hs
    rcases (h.adj_iff (L.a j) (L.a_mem_carrier j)).1 hs with heq | hai
    · exact L.a_injective heq
    · exact (L.adj_aa i j hai).elim
  · rintro rfl
    exact h.adj_original

/-- The index `i` in `s ≺_C a_i` is determined by `s`. -/
theorem CloneAt.index_eq_of_clone {i' : Fin k} (h : L.CloneAt s i) (h' : L.CloneAt s i') :
    i = i' :=
  ((h.adj_a_iff_index i').1 h'.adj_original).symm

/-- A clone is different from every `a`-vertex. -/
theorem CloneAt.ne_a_vertex (h : L.CloneAt s i) (q : Fin k) : s ≠ L.a q :=
  fun hq => h.outside (hq ▸ L.a_mem_carrier q)

/-- A clone is different from every `b`-vertex. -/
theorem CloneAt.ne_b_vertex (h : L.CloneAt s i) (q : Fin k) : s ≠ L.b q :=
  fun hq => h.outside (hq ▸ L.b_mem_carrier q)

/-- If a clone lies in an independent set `S`, then the vertex it clones does not. -/
theorem CloneAt.a_not_mem_indep {S : Set V} (hS : G.IsIndepSet S) (h : L.CloneAt s i)
    (hs : s ∈ S) : L.a i ∉ S :=
  fun ha => hS hs ha (h.ne_a_vertex i) h.adj_original

/-- Claw-freeness: a vertex has at most two neighbours in an independent set.  If `v` is
adjacent to `x`, `y`, `z` in `S` and `x ≠ y`, `x ≠ z`, then `y = z`. -/
theorem eq_of_three_nbrs_of_indep {S : Set V} (hclaw : G.IsClawFree) (hS : G.IsIndepSet S)
    {v x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z) (hxy : x ≠ y) (hxz : x ≠ z) :
    y = z := by
  by_contra hyz
  rcases hclaw hvx hvy hvz hxy hxz hyz with h | h | h
  · exact hS hx hy hxy h
  · exact hS hx hz hxz h
  · exact hS hy hz hyz h

/-- A clone is not among the `a`-vertices. -/
theorem CloneAt.not_mem_image_a_finset [DecidableEq V] (h : L.CloneAt s i) :
    s ∉ Finset.univ.image L.a := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro q hq
  exact h.ne_a_vertex q hq.symm

end Local

/-! ### Invariants of runs -/

section Runs

variable {S : Set V} {k : ℕ} {L L' : G.EvenHoleLabeling k} {ps : List (V × Fin k)}

/-- Every vertex used in a run lies in `S`. -/
theorem DeformsAlongAt.mem_S (hrun : L.DeformsAlongAt S ps L') : ∀ p ∈ ps, p.1 ∈ S := by
  induction hrun with
  | nil L => simp
  | cons hs h _ ih =>
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hs
      · exact ih p hp

/-- Each vertex used in a run is a clone, at the stated index, of some intermediate labelling
with the same `b`-vertices as `L`. -/
theorem DeformsAlongAt.exists_clone (hrun : L.DeformsAlongAt S ps L') :
    ∀ p ∈ ps, ∃ M : G.EvenHoleLabeling k, M.CloneAt p.1 p.2 ∧ ∀ q, M.b q = L.b q := by
  induction hrun with
  | nil L => simp
  | @cons L L' s i rest hs h _ ih =>
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨L, h, fun q => rfl⟩
      · obtain ⟨M, hM, hMb⟩ := ih p hp
        exact ⟨M, hM, fun q => (hMb q).trans (L.deform_b h q)⟩

/-- If the replaced indices are distinct, each vertex of the run is adjacent to the `a`-vertex
of the *original* labelling that it replaces. -/
theorem DeformsAlongAt.adj_orig (hrun : L.DeformsAlongAt S ps L')
    (hnd : (ps.map Prod.snd).Nodup) : ∀ p ∈ ps, G.Adj p.1 (L.a p.2) := by
  induction hrun with
  | nil L => simp
  | @cons L L' s i rest hs h _ ih =>
      intro p hp
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h.adj_original
      · have hne : p.2 ≠ i := fun hpi => hnd.1 (List.mem_map.2 ⟨p, hp, hpi⟩)
        have := ih hnd.2 p hp
        rwa [L.deform_a_away h hne] at this

/-- Vertices of `S` among the `a`-vertices are never touched by a run: they are neither
replaced (their indices are not among the `i_j`) nor re-used as some `s_j`, and they are
still present at the end of the run. -/
theorem DeformsAlongAt.avoid (hS : G.IsIndepSet S) (hrun : L.DeformsAlongAt S ps L') :
    ∀ q, L.a q ∈ S →
      q ∉ ps.map Prod.snd ∧ L.a q ∉ ps.map Prod.fst ∧ L'.a q = L.a q := by
  induction hrun with
  | nil L => simp
  | @cons L L' s i rest hs h _ ih =>
      intro q hq
      have hqi : q ≠ i := by
        rintro rfl
        exact h.a_not_mem_indep hS hs hq
      have hq' : (L.deform h).a q ∈ S := by rwa [L.deform_a_away h hqi]
      obtain ⟨h1, h2, h3⟩ := ih q hq'
      rw [L.deform_a_away h hqi] at h2 h3
      refine ⟨?_, ?_, h3⟩
      · simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨hqi, h1⟩
      · simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨(h.ne_a_vertex q).symm, h2⟩

/-- A run does not change the `b`-vertices. -/
theorem DeformsAlongAt.b_eq (hrun : L.DeformsAlongAt S ps L') : ∀ q, L'.b q = L.b q := by
  induction hrun with
  | nil L => intro q; rfl
  | @cons L L' s i rest hs h _ ih => intro q; exact (ih q).trans (L.deform_b h q)

/-- A run does not change the cyclic successor map. -/
theorem DeformsAlongAt.next_eq (hrun : L.DeformsAlongAt S ps L') : ∀ q, L'.next q = L.next q := by
  induction hrun with
  | nil L => intro q; rfl
  | @cons L L' s i rest hs h _ ih => intro q; exact (ih q).trans (L.deform_next h q)

/-- The `a`-vertices at indices that are not replaced are unchanged by a run. -/
theorem DeformsAlongAt.a_eq_of_not_mem (hrun : L.DeformsAlongAt S ps L') :
    ∀ q, q ∉ ps.map Prod.snd → L'.a q = L.a q := by
  induction hrun with
  | nil L => intro q _; rfl
  | @cons L L' s i rest hs h _ ih =>
      intro q hq
      simp only [List.map_cons, List.mem_cons, not_or] at hq
      rw [ih q hq.2, L.deform_a_away h hq.1]

/-- If the replaced indices are distinct, the `a`-vertex at index `i_j` of the final labelling
is the clone `s_j`. -/
theorem DeformsAlongAt.a_eq_of_mem (hrun : L.DeformsAlongAt S ps L')
    (hnd : (ps.map Prod.snd).Nodup) : ∀ p ∈ ps, L'.a p.2 = p.1 := by
  induction hrun with
  | nil L => simp
  | @cons L L' s i rest hs h hr ih =>
      intro p hp
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [hr.a_eq_of_not_mem i hnd.1, L.deform_a_at h]
      · exact ih hnd.2 p hp

/-- If the replaced indices are distinct, a clone `s_j` of a run is not adjacent to the
original `a`-vertices `a_{i_m}` with `m > j` (they are still present when `s_j` is added, and
a clone has exactly one `a`-neighbour). -/
theorem DeformsAlongAt.pairwise_not_adj (hrun : L.DeformsAlongAt S ps L')
    (hnd : (ps.map Prod.snd).Nodup) :
    ps.Pairwise (fun p q => ¬G.Adj p.1 (L.a q.2)) := by
  induction hrun with
  | nil L => exact List.Pairwise.nil
  | @cons L L' s i rest hs h hr ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      have hne : ∀ q ∈ rest, q.2 ≠ i := fun q hq e => hnd.1 (List.mem_map.2 ⟨q, hq, e⟩)
      refine List.pairwise_cons.2 ⟨?_, ?_⟩
      · intro q hq hadj
        exact hne q hq ((h.adj_a_iff_index q.2).1 hadj)
      · refine List.Pairwise.imp_of_mem ?_ (ih hnd.2)
        intro p q hp hq hpq hadj
        apply hpq
        rwa [L.deform_a_away h (hne q hq)]

end Runs

/-! ### Deformation paths along an independent set -/

/-- A deformation of the labelled even hole `L` along the independent set `S`
(v1 L760-762): `ℓ = len` distinct vertices `s₀, …, s_{ℓ-1} ∈ S`, distinct indices
`i₀, …, i_{ℓ-1}`, and a run `C ⟶ C^{(0)} ⟶ ⋯ ⟶ C^{(ℓ-1)} = final` in which `s_j` is a clone of
`a_{i_j}` in the current hole (`s_j ≺_{C^{(j-1)}} a_{i_j}`), such that `s_{j+1}` is adjacent to
the replaced vertex `a_{i_j}` (the field `link`; `L.a (idx j)` is the vertex of the *original*
hole, which is the one replaced at step `j` because the indices are distinct).

The structure records only the sequential data; whether the run is *maximal* is expressed
by `Untethered` / `TetheredTo`. -/
structure SetDeformationPath {k : ℕ} (L : G.EvenHoleLabeling k) (S : Finset V) where
  /-- The number `ℓ` of vertex-clone pairs. -/
  len : ℕ
  len_pos : 0 < len
  /-- The deforming vertices `s_j`. -/
  s : Fin len → V
  /-- The replaced indices `i_j`, so that `s_j` replaces `a_{i_j}`. -/
  idx : Fin len → Fin k
  s_mem : ∀ j, s j ∈ S
  s_injective : Function.Injective s
  idx_injective : Function.Injective idx
  /-- The hole obtained at the end of the run. -/
  final : G.EvenHoleLabeling k
  run : L.DeformsAlongAt (↑S) (List.ofFn fun j => (s j, idx j)) final
  link : ∀ j j' : Fin len, j.val + 1 = j'.val → G.Adj (s j') (L.a (idx j))

namespace SetDeformationPath

section Basic

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The index `0`, i.e. the initialising vertex `s₀`. -/
def first (P : L.SetDeformationPath S) : Fin P.len := ⟨0, P.len_pos⟩

/-- The index `ℓ - 1`, i.e. the last vertex-clone pair. -/
def last (P : L.SetDeformationPath S) : Fin P.len :=
  ⟨P.len - 1, by have := P.len_pos; omega⟩

theorem first_eq (P : L.SetDeformationPath S) : P.first = ⟨0, P.len_pos⟩ := rfl

theorem last_eq (P : L.SetDeformationPath S) :
    P.last = ⟨P.len - 1, by have := P.len_pos; omega⟩ := rfl

/-- The vertex set `P = {s_j} ∪ {a_{i_j}}` of the deformation path
`s₀ - a_{i₀} - s₁ - ⋯ - s_{ℓ-1} - a_{i_{ℓ-1}}` (v1 L764). -/
def support [DecidableEq V] (P : L.SetDeformationPath S) : Finset V :=
  Finset.univ.image P.s ∪ Finset.univ.image (fun j => L.a (P.idx j))

/-- *Untethered*: the deformation path is a whole connected component of `G[S ⊕ C_a]`
(v1 L764: "if `s₀` is untethered with respect to `C`, i.e. `s_ℓ` is not present, then the path
`P` has odd length `2ℓ - 1`", an odd component in the sense of
`SimpleGraph.IsInducedComponent`). -/
def Untethered [DecidableEq V] (P : L.SetDeformationPath S) : Prop :=
  G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.a)) ↑P.support

/-- *Tethered to `t`*: the last replaced vertex `a_{i_{ℓ-1}}` has a further neighbour
`t ∈ S ∖ {s_j}`, and `t` has exactly three neighbours in `C`, namely it is a clone of some
`b`-vertex (a clone for the colour-swapped labelling); v1 L763 ("`s₀` and `s_ℓ` are tethered
with respect to `C`").  The tether `t` is the vertex `s_ℓ` of v1; it is a neighbour of
`a_{i_{ℓ-1}}` and of one further `a`-vertex of `C`. -/
def TetheredTo (P : L.SetDeformationPath S) (t : V) : Prop :=
  t ∈ S ∧ t ∉ Set.range P.s ∧ G.Adj t (L.a (P.idx P.last)) ∧
    ∃ r, L.swapColors.CloneAt t r

theorem mem_support_iff [DecidableEq V] (P : L.SetDeformationPath S) {v : V} :
    v ∈ P.support ↔ ∃ j, P.s j = v ∨ L.a (P.idx j) = v := by
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨j, Or.inl hj⟩
    · exact ⟨j, Or.inr hj⟩
  · rintro ⟨j, hj | hj⟩
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr ⟨j, hj⟩

theorem s_mem_support [DecidableEq V] (P : L.SetDeformationPath S) (j : Fin P.len) :
    P.s j ∈ P.support :=
  P.mem_support_iff.2 ⟨j, Or.inl rfl⟩

theorem a_idx_mem_support [DecidableEq V] (P : L.SetDeformationPath S) (j : Fin P.len) :
    L.a (P.idx j) ∈ P.support :=
  P.mem_support_iff.2 ⟨j, Or.inr rfl⟩

/-- The run of a deformation path, forgetting the replaced indices. -/
theorem run_forget (P : L.SetDeformationPath S) :
    L.DeformsAlong (↑S) (List.ofFn P.s) P.final := by
  have := P.run.toDeformsAlong
  simpa [List.map_ofFn, Function.comp_def] using this

/-- The number of vertex-clone pairs is at most `k` (v1 L765: "for `|C| = 2k`, we have
`ℓ ≤ k`"), because the replaced indices are distinct. -/
theorem len_le (P : L.SetDeformationPath S) : P.len ≤ k := by
  simpa using Fintype.card_le_of_injective P.idx P.idx_injective

theorem nodup_fst (P : L.SetDeformationPath S) :
    ((List.ofFn fun j => (P.s j, P.idx j)).map Prod.fst).Nodup := by
  simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.2 P.s_injective

theorem nodup_snd (P : L.SetDeformationPath S) :
    ((List.ofFn fun j => (P.s j, P.idx j)).map Prod.snd).Nodup := by
  simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.2 P.idx_injective

/-- Each `s_j` is adjacent to the `a`-vertex `a_{i_j}` of the original hole. -/
theorem adj_a_idx (P : L.SetDeformationPath S) (j : Fin P.len) :
    G.Adj (P.s j) (L.a (P.idx j)) :=
  P.run.adj_orig P.nodup_snd (P.s j, P.idx j) (List.mem_ofFn.2 ⟨j, rfl⟩)

/-- The vertices of a deformation path are clones of the intermediate holes, with the same
`b`-vertices as `L`. -/
theorem exists_clone (P : L.SetDeformationPath S) (j : Fin P.len) :
    ∃ M : G.EvenHoleLabeling k, M.CloneAt (P.s j) (P.idx j) ∧ ∀ q, M.b q = L.b q :=
  P.run.exists_clone (P.s j, P.idx j) (List.mem_ofFn.2 ⟨j, rfl⟩)

/-- An `a`-vertex of `L` that lies in `S` is not replaced along a deformation path. -/
theorem idx_ne_of_a_mem (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S)
    {q : Fin k} (hq : L.a q ∈ S) (j : Fin P.len) : P.idx j ≠ q := by
  intro hj
  exact (P.run.avoid hS q hq).1
    (List.mem_map.2 ⟨(P.s j, P.idx j), List.mem_ofFn.2 ⟨j, rfl⟩, hj⟩)

/-- An `a`-vertex of `L` that lies in `S` is not one of the deforming vertices. -/
theorem s_ne_of_a_mem (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S)
    {q : Fin k} (hq : L.a q ∈ S) (j : Fin P.len) : P.s j ≠ L.a q := by
  intro hj
  exact (P.run.avoid hS q hq).2.1
    (List.mem_map.2 ⟨(P.s j, P.idx j), List.mem_ofFn.2 ⟨j, rfl⟩, hj⟩)

/-- Untethered and tethered runs are mutually exclusive: a neighbour `t ∈ S` of the last
replaced vertex that is not on the path contradicts maximality of the component. -/
theorem not_untethered_of_ext [DecidableEq V] (P : L.SetDeformationPath S) {t : V}
    (ht : t ∈ S) (htP : t ∉ Set.range P.s) (hadj : G.Adj t (L.a (P.idx P.last))) :
    ¬P.Untethered := by
  intro hU
  have htA : t ∉ Finset.univ.image L.a := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro q hq
    exact L.adj_aa q (P.idx P.last) (hq ▸ hadj)
  have htU : t ∈ (↑(symmDiff S (Finset.univ.image L.a)) : Set V) := by
    simp only [Finset.mem_coe, Finset.mem_symmDiff]
    exact Or.inl ⟨ht, htA⟩
  have hmem := hU.2.2 (Finset.mem_coe.2 (P.a_idx_mem_support P.last)) htU hadj.symm
  rcases P.mem_support_iff.1 (Finset.mem_coe.1 hmem) with ⟨j, hj | hj⟩
  · exact htP ⟨j, hj⟩
  · exact htA (Finset.mem_image.2 ⟨P.idx j, Finset.mem_univ _, hj⟩)

theorem not_untethered_of_tetheredTo [DecidableEq V] (P : L.SetDeformationPath S) {t : V}
    (ht : P.TetheredTo t) : ¬P.Untethered :=
  P.not_untethered_of_ext ht.1 ht.2.1 ht.2.2.1

end Basic

end SetDeformationPath

namespace SetDeformationPath

section Construction

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The one-step deformation path `s ≺_C a_i`. -/
def single {s : V} {i : Fin k} (hs : s ∈ S) (h : L.CloneAt s i) : L.SetDeformationPath S where
  len := 1
  len_pos := Nat.one_pos
  s := fun _ => s
  idx := fun _ => i
  s_mem := fun _ => hs
  s_injective := fun a b _ => Subsingleton.elim a b
  idx_injective := fun a b _ => Subsingleton.elim a b
  final := L.deform h
  run := by
    simpa [List.ofFn_succ] using
      DeformsAlongAt.cons (S := (↑S : Set V)) (Finset.mem_coe.2 hs) h (DeformsAlongAt.nil _)
  link := fun j j' hjj' => by
    have := j'.isLt
    omega

theorem mem_support_single [DecidableEq V] {s : V} {i : Fin k} (hs : s ∈ S)
    (h : L.CloneAt s i) {v : V} :
    v ∈ (single hs h).support ↔ v = s ∨ v = L.a i := by
  rw [mem_support_iff]
  simp only [single, exists_const]
  exact or_congr eq_comm eq_comm

/-- If the initialising vertex `s₀` has no further `S`-neighbour at `a_{i₀}`, the one-step
path is untethered: `{s₀, a_{i₀}}` is a whole component of `G[S ⊕ C_a]`. -/
theorem single_untethered [DecidableEq V] (hS : G.IsIndepSet (S : Set V)) {s : V} {i : Fin k}
    (hs : s ∈ S) (h : L.CloneAt s i)
    (hno : ∀ t ∈ S, t ≠ s → ¬G.Adj t (L.a i)) : (single hs h).Untethered := by
  have hsupp : (↑(single hs h).support : Set V) = {s, L.a i} := by
    ext v
    rw [Finset.mem_coe, mem_support_single]
    simp
  have hai : L.a i ∉ S := h.a_not_mem_indep hS (Finset.mem_coe.2 hs)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [hsupp] at hv
    simp only [Finset.mem_coe, Finset.mem_symmDiff]
    rcases hv with rfl | rfl
    · exact Or.inl ⟨hs, h.not_mem_image_a_finset⟩
    · exact Or.inr ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hai⟩
  · rw [hsupp]
    exact connected_induce_insert_of_adj (connected_induce_singleton_set (L.a i))
      (Set.mem_singleton _) h.adj_original.symm
  · intro x y hx hy hxy
    rw [hsupp] at hx ⊢
    simp only [Finset.mem_coe, Finset.mem_symmDiff] at hy
    rcases hx with rfl | rfl
    · rcases hy with ⟨hyS, _⟩ | ⟨hyA, _⟩
      · exact (hS (Finset.mem_coe.2 hs) (Finset.mem_coe.2 hyS) hxy.ne hxy).elim
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyA
        have := (h.adj_a_iff_index q).1 hxy
        subst this
        exact Or.inr rfl
    · rcases hy with ⟨hyS, _⟩ | ⟨hyA, _⟩
      · by_cases hys : y = s
        · exact Or.inl hys
        · exact (hno y hyS hys hxy.symm).elim
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyA
        exact (L.adj_aa i q hxy).elim

/-- The one-step path is tethered to any vertex `t ∈ S ∖ {s₀}` adjacent to `a_{i₀}` that is a
clone of a `b`-vertex. -/
theorem single_tetheredTo [DecidableEq V] {s : V} {i : Fin k} (hs : s ∈ S) (h : L.CloneAt s i)
    {t : V} (ht : t ∈ S) (hts : t ≠ s) (hadj : G.Adj t (L.a i))
    (hr : ∃ r, L.swapColors.CloneAt t r) : (single hs h).TetheredTo t := by
  refine ⟨ht, ?_, hadj, hr⟩
  rintro ⟨j, hj⟩
  exact hts hj.symm

/-! #### Prepending a step to a deformation path -/

/-- The replaced indices of a path from the deformed hole `L.deform h` avoid `i`. -/
theorem tail_idx_ne (hS : G.IsIndepSet (S : Set V)) {s : V} {i : Fin k} (hs : s ∈ S)
    (h : L.CloneAt s i) (P : (L.deform h).SetDeformationPath S) (j : Fin P.len) :
    P.idx j ≠ i :=
  P.idx_ne_of_a_mem hS (by rw [L.deform_a_at h]; exact hs) j

/-- The deforming vertices of a path from the deformed hole `L.deform h` differ from `s`. -/
theorem tail_s_ne (hS : G.IsIndepSet (S : Set V)) {s : V} {i : Fin k} (hs : s ∈ S)
    (h : L.CloneAt s i) (P : (L.deform h).SetDeformationPath S) (j : Fin P.len) :
    P.s j ≠ s := by
  have := P.s_ne_of_a_mem hS (q := i) (by rw [L.deform_a_at h]; exact hs) j
  rwa [L.deform_a_at h] at this

/-- Replacing `s` by `s ≺_C a_i` in front of a deformation path of the deformed hole
`L.deform h` gives a deformation path of `L`, provided the first vertex of the tail path is
adjacent to the replaced vertex `a_i` (the `link` condition). -/
def prepend (hS : G.IsIndepSet (S : Set V)) {s : V} {i : Fin k} (hs : s ∈ S)
    (h : L.CloneAt s i) (P : (L.deform h).SetDeformationPath S)
    (hlink : G.Adj (P.s P.first) (L.a i)) : L.SetDeformationPath S where
  len := P.len + 1
  len_pos := Nat.succ_pos _
  s := (Fin.cons s P.s : Fin (P.len + 1) → V)
  idx := (Fin.cons i P.idx : Fin (P.len + 1) → Fin k)
  s_mem := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hs
    · simpa using P.s_mem j
  s_injective := Fin.cons_injective_iff.2
    ⟨by rintro ⟨j, hj⟩; exact tail_s_ne hS hs h P j hj, P.s_injective⟩
  idx_injective := Fin.cons_injective_iff.2
    ⟨by rintro ⟨j, hj⟩; exact tail_idx_ne hS hs h P j hj, P.idx_injective⟩
  final := P.final
  run := by
    have e : (List.ofFn fun j : Fin (P.len + 1) =>
        ((Fin.cons s P.s : Fin (P.len + 1) → V) j,
          (Fin.cons i P.idx : Fin (P.len + 1) → Fin k) j)) =
        (s, i) :: List.ofFn fun j => (P.s j, P.idx j) := by
      simp [List.ofFn_succ]
    rw [e]
    exact DeformsAlongAt.cons (Finset.mem_coe.2 hs) h P.run
  link := by
    intro j j' hjj'
    obtain ⟨j'', rfl⟩ : ∃ j'' : Fin P.len, j' = j''.succ :=
      ⟨⟨j'.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    cases j using Fin.cases with
    | zero =>
        have hj'' : j'' = P.first := Fin.ext (by simp [first] at hjj' ⊢; omega)
        subst hj''
        simpa using hlink
    | succ j0 =>
        have hlt : j0.val + 1 = j''.val := by simp at hjj'; omega
        have := P.link j0 j'' hlt
        rw [L.deform_a_away h (tail_idx_ne hS hs h P j0)] at this
        simpa using this

section PrependLemmas

variable (hS : G.IsIndepSet (S : Set V)) {s : V} {i : Fin k} (hs : s ∈ S) (h : L.CloneAt s i)
  (P : (L.deform h).SetDeformationPath S) (hlink : G.Adj (P.s P.first) (L.a i))

include hS hs in
theorem prepend_first_s : (prepend hS hs h P hlink).s (prepend hS hs h P hlink).first = s := rfl

include hS hs in
theorem prepend_first_idx :
    (prepend hS hs h P hlink).idx (prepend hS hs h P hlink).first = i := rfl

include hS hs in
theorem prepend_last :
    (prepend hS hs h P hlink).last = P.last.succ := by
  apply Fin.ext
  have := P.len_pos
  show P.len + 1 - 1 = P.len - 1 + 1
  omega

include hS hs in
theorem mem_support_prepend [DecidableEq V] {v : V} :
    v ∈ (prepend hS hs h P hlink).support ↔ v = s ∨ v = L.a i ∨ v ∈ P.support := by
  rw [mem_support_iff, mem_support_iff]
  change (∃ j : Fin (P.len + 1), (Fin.cons s P.s : Fin (P.len + 1) → V) j = v ∨
      L.a ((Fin.cons i P.idx : Fin (P.len + 1) → Fin k) j) = v) ↔ _
  rw [Fin.exists_fin_succ]
  have e : ∀ j, L.a (P.idx j) = (L.deform h).a (P.idx j) :=
    fun j => (L.deform_a_away h (tail_idx_ne hS hs h P j)).symm
  simp only [Fin.cons_zero, Fin.cons_succ, e]
  constructor
  · rintro ((hv | hv) | ⟨j, hj⟩)
    · exact Or.inl hv.symm
    · exact Or.inr (Or.inl hv.symm)
    · exact Or.inr (Or.inr ⟨j, hj⟩)
  · rintro (hv | hv | ⟨j, hj⟩)
    · exact Or.inl (Or.inl hv.symm)
    · exact Or.inl (Or.inr hv.symm)
    · exact Or.inr ⟨j, hj⟩

theorem mem_image_a_deform [DecidableEq V] {v : V} :
    v ∈ Finset.univ.image (L.deform h).a ↔
      v = s ∨ (v ∈ Finset.univ.image L.a ∧ v ≠ L.a i) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hq : q = i
    · subst hq
      left
      simp
    · right
      refine ⟨⟨q, ?_⟩, ?_⟩
      · exact (L.deform_a_away h hq).symm
      · rw [L.deform_a_away h hq]
        exact fun e => hq (L.a_injective e)
  · rintro (rfl | ⟨⟨q, rfl⟩, hne⟩)
    · exact ⟨i, by simp⟩
    · have hq : q ≠ i := fun hq => hne (hq ▸ rfl)
      exact ⟨q, L.deform_a_away h hq⟩

include hS hs in
/-- Passing from `C_a` to the deformed `C^{(0)}_a` only changes `S ⊕ C_a` at the two vertices
`s` and `a_i`, which are adjacent. -/
theorem mem_symmDiff_deform [DecidableEq V] {v : V} :
    v ∈ symmDiff S (Finset.univ.image L.a) ↔
      v = s ∨ v = L.a i ∨ v ∈ symmDiff S (Finset.univ.image (L.deform h).a) := by
  have hai : L.a i ∉ S := h.a_not_mem_indep hS (Finset.mem_coe.2 hs)
  have hmem : L.a i ∈ Finset.univ.image L.a := Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  have hsn := h.not_mem_image_a_finset
  simp only [Finset.mem_symmDiff, mem_image_a_deform h]
  by_cases hvs : v = s
  · subst hvs
    simp [hs, hsn]
  · by_cases hvi : v = L.a i
    · subst hvi
      simp [hai, hmem]
    · simp only [hvs, hvi, false_or]
      tauto

include hS hs in
/-- If the tail of a deformation path is untethered, so is the lengthened path: the component
`P` of `G[S ⊕ C^{(0)}_a]` grows by the adjacent pair `s ~ a_i`, and the path `s - a_i - s₁`
is closed under adjacency inside `S ⊕ C_a` by claw-freeness (`N_S(a_i) = {s, s₁}`). -/
theorem untethered_prepend [DecidableEq V] (hclaw : G.IsClawFree)
    (hU : P.Untethered) : (prepend hS hs h P hlink).Untethered := by
  have hai : L.a i ∉ S := h.a_not_mem_indep hS (Finset.mem_coe.2 hs)
  obtain ⟨hsub, hconn, hcl⟩ := hU
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_coe, mem_support_prepend hS hs h P hlink] at hv
    rw [Finset.mem_coe, mem_symmDiff_deform hS hs h]
    rcases hv with hv | hv | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (hsub (Finset.mem_coe.2 hv)))
  · have hset : (↑(prepend hS hs h P hlink).support : Set V) =
        insert s (insert (L.a i) ↑P.support) := by
      ext v
      simp [mem_support_prepend hS hs h P hlink]
    rw [hset]
    refine connected_induce_insert_of_adj (x := L.a i) ?_ (Set.mem_insert _ _)
      h.adj_original.symm
    exact connected_induce_insert_of_adj (x := P.s P.first) hconn
      (Finset.mem_coe.2 (P.s_mem_support _)) hlink
  · intro x y hx hy hxy
    rw [Finset.mem_coe, mem_support_prepend hS hs h P hlink] at hx ⊢
    rw [Finset.mem_coe, mem_symmDiff_deform hS hs h] at hy
    rcases hy with rfl | rfl | hy
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rcases hx with rfl | rfl | hx
      · exfalso
        simp only [Finset.mem_symmDiff, mem_image_a_deform h] at hy
        rcases hy with ⟨hyS, _⟩ | ⟨hyA, hyS⟩
        · exact hS (Finset.mem_coe.2 hs) (Finset.mem_coe.2 hyS) hxy.ne hxy
        · rcases hyA with rfl | ⟨hyA, hyne⟩
          · exact hyS hs
          · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyA
            exact hyne (by rw [(h.adj_a_iff_index q).1 hxy])
      · right; right
        simp only [Finset.mem_symmDiff, mem_image_a_deform h] at hy
        rcases hy with ⟨hyS, hyA⟩ | ⟨hyA, hyS⟩
        · have hys : y ≠ s := fun e => hyA (Or.inl e)
          have := eq_of_three_nbrs_of_indep (S := (↑S : Set V)) hclaw hS (v := L.a i) (x := s)
            (y := P.s P.first) (z := y) hs (P.s_mem _) hyS h.adj_original.symm hlink.symm
            hxy (tail_s_ne hS hs h P P.first).symm hys.symm
          rw [← this]
          exact P.s_mem_support _
        · rcases hyA with rfl | ⟨hyA, _⟩
          · exact (hyS hs).elim
          · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyA
            exact (L.adj_aa i q hxy).elim
      · exact Or.inr (Or.inr (Finset.mem_coe.1 (hcl (Finset.mem_coe.2 hx) hy hxy)))

include hS hs in
/-- If the tail of a deformation path is tethered to `t`, so is the lengthened path.  Here the
tether `t` is a clone of a `b`-vertex of the deformed hole `C^{(0)}`; it is also one for `C`,
because `t` is not adjacent to `s` and, by claw-freeness (`N_S(a_i) = {s, s₁}`), not to `a_i`. -/
theorem tetheredTo_prepend [DecidableEq V] (hclaw : G.IsClawFree) {t : V}
    (ht : P.TetheredTo t) : (prepend hS hs h P hlink).TetheredTo t := by
  obtain ⟨htS, htP, hadj, r, hr⟩ := ht
  have hne := tail_idx_ne hS hs h P P.last
  have hadj' : G.Adj t (L.a (P.idx P.last)) := by rwa [L.deform_a_away h hne] at hadj
  have hts : t ≠ s := by
    rintro rfl
    exact hne ((h.adj_a_iff_index _).1 hadj')
  refine ⟨htS, ?_, ?_, r, ?_⟩
  · rintro ⟨j, hj⟩
    cases j using Fin.cases with
    | zero => exact hts (by simpa [prepend] using hj.symm)
    | succ j0 => exact htP ⟨j0, by simpa [prepend] using hj⟩
  · rw [prepend_last hS hs h P hlink]
    simpa [prepend] using hadj'
  · have hai : L.a i ∉ S := h.a_not_mem_indep hS (Finset.mem_coe.2 hs)
    have hnadj_ts : ¬G.Adj t s := fun hadj =>
      hS (Finset.mem_coe.2 htS) (Finset.mem_coe.2 hs) hts hadj
    have hnadj_ta : ¬G.Adj t (L.a i) := by
      intro hta
      have := eq_of_three_nbrs_of_indep (S := (↑S : Set V)) hclaw hS (v := L.a i) (x := s)
        (y := P.s P.first) (z := t) hs (P.s_mem _) htS h.adj_original.symm hlink.symm
        hta.symm (tail_s_ne hS hs h P P.first).symm hts.symm
      exact htP ⟨P.first, this⟩
    have hcar : (L.deform h).swapColors.carrier = (L.deform h).carrier :=
      swapColors_carrier (L.deform h)
    have hsw := hr.adj_iff
    have hAr : G.Adj t ((L.deform h).a r) :=
      (hsw ((L.deform h).a r) (by rw [hcar]; exact (L.deform h).a_mem_carrier r)).2
        (Or.inr ((L.deform h).adj_a_b r).symm)
    have hAp : G.Adj t ((L.deform h).a (L.prev r)) :=
      (hsw ((L.deform h).a (L.prev r))
        (by rw [hcar]; exact (L.deform h).a_mem_carrier _)).2
        (Or.inr ((L.deform h).adj_a_prev_b r).symm)
    have hri : r ≠ i := by
      rintro rfl
      rw [L.deform_a_at h] at hAr
      exact hnadj_ts hAr
    have hpi : L.prev r ≠ i := by
      intro hp
      rw [hp, L.deform_a_at h] at hAp
      exact hnadj_ts hAp
    have hout : t ∉ (L.deform h).carrier := by
      have := hr.outside
      rwa [hcar] at this
    refine ⟨?_, ?_⟩
    · rw [swapColors_carrier]
      intro htc
      rw [L.deform_carrier h] at hout
      by_cases hti : t = L.a i
      · exact hai (hti ▸ htS)
      · exact hout (Or.inr ⟨htc, hti⟩)
    · intro v hv
      rw [swapColors_carrier] at hv
      by_cases hvi : v = L.a i
      · subst hvi
        constructor
        · intro hta
          exact (hnadj_ta hta).elim
        · rintro (hvb | hvb)
          · exact (L.color_disjoint i r hvb).elim
          · rcases (L.adj_ab_iff i r).1 hvb.symm with hr' | hr'
            · exact (hri hr').elim
            · exact (hpi (by rw [hr', L.prev_next])).elim
      · have hvM : v ∈ (L.deform h).carrier := by
          rw [L.deform_carrier h]
          exact Or.inr ⟨hv, hvi⟩
        exact hsw v (by rw [hcar]; exact hvM)

end PrependLemmas

/-! #### The step: Lemma 3 of v1 (repo `CloneAt.lemma8`) -/

section Step

variable {s : V} {i : Fin k}

/-- If `t ∉ C ∪ {s}` is not adjacent to `s` and has exactly the neighbours of a clone of `a_j`
among the vertices of `C` other than `a_i`, then `t` is a clone of `a_j` in the deformed hole
`C^{(0)}`. -/
theorem cloneAt_deform_of (h : L.CloneAt s i) {t : V} {j : Fin k} (hj : j ≠ i) (hts : t ≠ s)
    (hnadj : ¬G.Adj t s) (htC : t ∉ L.carrier)
    (hcond : ∀ v ∈ L.carrier, v ≠ L.a i → (G.Adj t v ↔ v = L.a j ∨ G.Adj (L.a j) v)) :
    (L.deform h).CloneAt t j := by
  have hs_not_adj : ¬G.Adj s (L.a j) := fun hadj => hj ((h.adj_a_iff_index j).1 hadj)
  refine ⟨?_, ?_⟩
  · rw [L.deform_carrier h]
    rintro (hte | ⟨htc, _⟩)
    · exact hts hte
    · exact htC htc
  · intro v hv
    rw [L.deform_carrier h] at hv
    rw [L.deform_a_away h hj]
    rcases hv with rfl | ⟨hvC, hvi⟩
    · constructor
      · intro hadj
        exact (hnadj hadj).elim
      · rintro (hv | hv)
        · exact (h.ne_a_vertex j hv).elim
        · exact (hs_not_adj hv.symm).elim
    · exact hcond v hvC hvi

/-- If `t ∉ C` has, among the vertices of `C`, exactly the neighbours of a clone of `b_r`, then
`t` is a clone of `b_r` for the colour-swapped labelling. -/
theorem swapColors_cloneAt_of {t : V} (r : Fin k) (htC : t ∉ L.carrier)
    (hcond : ∀ v ∈ L.carrier, G.Adj t v ↔ v = L.b r ∨ G.Adj (L.b r) v) :
    L.swapColors.CloneAt t r :=
  ⟨by rw [swapColors_carrier]; exact htC,
    fun v hv => by rw [swapColors_carrier] at hv; exact hcond v hv⟩

/-- **The step of the run (Lemma 3 of v1, repo `CloneAt.lemma8`).**  Let `s ∈ S` be a clone of
`a_i` and let `t ∈ S ∖ {s}` be adjacent to `a_i`.  Then either `t` is a clone in the deformed
hole `C^{(0)}` (cases (ii) and (iv) of Lemma 3: the run continues with `t`), or `t` has exactly
three neighbours in `C`, which form a clone of a `b`-vertex (cases (i) and (iii): the tether). -/
theorem step_cases (hclaw : G.IsClawFree) {S : Set V} (hS : G.IsIndepSet S) (h : L.CloneAt s i)
    (hs : s ∈ S) {t : V} (ht : t ∈ S) (hts : t ≠ s) (hadj : G.Adj t (L.a i)) :
    (∃ i', (L.deform h).CloneAt t i') ∨ ∃ r, L.swapColors.CloneAt t r := by
  have hnadj_ts : ¬G.Adj t s := fun hadj => hS ht hs hts hadj
  have hat_ne : ∀ q, t ≠ L.a q := fun q hq => L.adj_aa q i (hq ▸ hadj)
  have hbt_ne : ∀ q, t ≠ L.b q := by
    intro q htq
    subst htq
    rcases (L.adj_ab_iff i q).1 hadj.symm with rfl | rfl
    · exact hnadj_ts h.adj_b.symm
    · exact hnadj_ts h.adj_b_next.symm
  have htL : t ∉ L.carrier := by
    rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · exact hat_ne q hq.symm
    · exact hbt_ne q hq.symm
  have htC : t ∉ Set.insert s L.carrier := by
    intro hmem
    rcases Set.mem_insert_iff.1 hmem with e | hc
    · exact hts e
    · exact htL hc
  obtain ⟨u, hu, hcases⟩ := h.lemma8 hclaw htC (Or.inr ⟨hnadj_ts, hadj⟩)
  have hmem : ∀ v, v ∈ L.carrier → v ∈ Set.insert s L.carrier :=
    fun v hv => Set.mem_insert_of_mem _ hv
  rcases hu with rfl | rfl
  · exfalso
    rcases hcases with hc | hc | hc | hc <;>
      exact hnadj_ts ((hc u (Set.mem_insert _ _)).2 (by simp))
  · rcases hcases with hc | hc | hc | hc
    · -- (i): tether, clone of `b_i`
      right
      refine ⟨i, swapColors_cloneAt_of i htL fun v hv => ?_⟩
      rw [hc v (hmem v hv), L.adj_b_iff_of_mem hv]
      tauto
    · -- (ii): continue, clone of `a_{prev i}`
      left
      refine ⟨L.prev i, cloneAt_deform_of h (L.prev_ne i) hts hnadj_ts htL ?_⟩
      intro v hv hvi
      rw [hc v (hmem v hv), L.adj_a_iff_of_mem hv, L.next_prev]
      constructor
      · intro hh
        tauto
      · intro hh
        tauto
    · -- (iii): tether, clone of `b_{next i}`
      right
      refine ⟨L.next i, swapColors_cloneAt_of (L.next i) htL fun v hv => ?_⟩
      rw [hc v (hmem v hv), L.adj_b_iff_of_mem hv, L.prev_next]
      tauto
    · -- (iv): continue, clone of `a_{next i}`
      left
      refine ⟨L.next i, cloneAt_deform_of h (L.next_ne i) hts hnadj_ts htL ?_⟩
      intro v hv hvi
      rw [hc v (hmem v hv), L.adj_a_iff_of_mem hv]
      constructor
      · intro hh
        tauto
      · intro hh
        tauto

end Step

end Construction

end SetDeformationPath

/-! ### Existence of the run -/

/-- Auxiliary form of `CloneAt.exists_setDeformationPath`, by strong induction on the number of
`a`-vertices of the hole that do not yet lie in `S` (each step of the run replaces one
such vertex by an element of `S`). -/
theorem exists_setDeformationPath_aux [DecidableEq V] (hclaw : G.IsClawFree) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    ∀ (n : ℕ) {k : ℕ} (L : G.EvenHoleLabeling k),
      (Finset.univ.filter fun q => L.a q ∉ S).card = n →
      ∀ {s : V} {i : Fin k}, s ∈ S → L.CloneAt s i →
        ∃ P : L.SetDeformationPath S, P.s P.first = s ∧ P.idx P.first = i ∧
          (P.Untethered ∨ ∃ t, P.TetheredTo t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k L hn s i hs h
    by_cases hex : ∃ t ∈ S, t ≠ s ∧ G.Adj t (L.a i)
    · obtain ⟨t, htS, hts, hadj⟩ := hex
      rcases SetDeformationPath.step_cases hclaw hS h (Finset.mem_coe.2 hs)
          (Finset.mem_coe.2 htS) hts hadj with
        ⟨i', hi'⟩ | ⟨r, hr⟩
      · -- the run continues with `t`
        have hai : L.a i ∉ S := h.a_not_mem_indep hS (Finset.mem_coe.2 hs)
        have hlt : (Finset.univ.filter fun q => (L.deform h).a q ∉ S).card < n := by
          rw [← hn]
          refine Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩)
          · intro q hq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
            by_cases hqi : q = i
            · subst hqi
              exact hai
            · rwa [L.deform_a_away h hqi] at hq
          · simpa using hai
          · simpa using hs
        obtain ⟨P, hP0, hPi, hPd⟩ := ih _ hlt (L.deform h) rfl htS hi'
        have hlink : G.Adj (P.s P.first) (L.a i) := by
          rw [hP0]
          exact hadj
        refine ⟨SetDeformationPath.prepend hS hs h P hlink, rfl, rfl, ?_⟩
        rcases hPd with hU | ⟨t', ht'⟩
        · exact Or.inl (SetDeformationPath.untethered_prepend hS hs h P hlink hclaw hU)
        · exact Or.inr ⟨t', SetDeformationPath.tetheredTo_prepend hS hs h P hlink hclaw ht'⟩
      · -- the run stops: `t` is a tether
        exact ⟨SetDeformationPath.single hs h, rfl, rfl,
          Or.inr ⟨t, SetDeformationPath.single_tetheredTo hs h htS hts hadj ⟨r, hr⟩⟩⟩
    · exact ⟨SetDeformationPath.single hs h, rfl, rfl,
        Or.inl (SetDeformationPath.single_untethered hS hs h
          fun t ht hts hadj => hex ⟨t, ht, hts, hadj⟩)⟩

/-- **Deformation of a labelled even hole along an independent set** (v1, Section
"Neighboring Relations", L753-766; the construction behind Theorem 1 (ii), v1 L908-913).

Let `L` be a labelling of an even hole `C` (`|C| = 2k`) of a claw-free graph, `S` an independent
finset and `s₀ ∈ S` a clone of `a_{i₀}`.  Then there is a deformation path
`s₀ - a_{i₀} - s₁ - a_{i₁} - ⋯` along `S` starting at `(s₀, i₀)` which is either *untethered*
(its vertex set is a whole component of `G[S ⊕ C_a]`) or *tethered* to some `t ∈ S` (`t` is a
neighbour of the last replaced vertex and a clone of a `b`-vertex of `C`), and never both.

The hypothesis `hL` (full cyclic order of the labelling) is part of the setting of the
manuscript; the argument below does not use it. -/
theorem CloneAt.exists_setDeformationPath [DecidableEq V] (hclaw : G.IsClawFree) {k : ℕ}
    {L : G.EvenHoleLabeling k} (_hL : L.HasFullCyclicOrder) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) {s₀ : V} {i₀ : Fin k} (hs₀ : s₀ ∈ S)
    (h : L.CloneAt s₀ i₀) :
    ∃ P : L.SetDeformationPath S, P.s P.first = s₀ ∧ P.idx P.first = i₀ ∧
      (P.Untethered ∨ ∃ t, P.TetheredTo t) ∧ ¬(P.Untethered ∧ ∃ t, P.TetheredTo t) := by
  obtain ⟨P, hP0, hPi, hP⟩ := exists_setDeformationPath_aux hclaw hS _ L rfl hs₀ h
  exact ⟨P, hP0, hPi, hP, fun ⟨hU, t, ht⟩ => P.not_untethered_of_tetheredTo ht hU⟩

/-! ### Uniqueness of the run -/

section Uniqueness

variable {S : Set V} {k : ℕ}

/-- Two runs from the same hole that start with the same vertex `s` agree as long as both are
defined: one list of `(vertex, index)` pairs is a prefix of the other.  Here `L0` is the
reference labelling in which the `link` conditions are expressed, and the states `L` are
related to `L0` only through the indices still to be replaced.  The proof is by induction on
the run: the index of a clone is determined by the clone (`CloneAt.index_eq_of_clone`), and the
next vertex is determined because `a_{i_j}` has at most two neighbours in `S`
(claw-freeness), namely `s_j` and `s_{j+1}`. -/
theorem DeformsAlongAt.prefix_agree (hclaw : G.IsClawFree) (hS : G.IsIndepSet S)
    (L0 : G.EvenHoleLabeling k) :
    ∀ (ps' qs' : List (V × Fin k)) (s : V) (i i' : Fin k) (L L1 L2 : G.EvenHoleLabeling k),
      L.DeformsAlongAt S ((s, i) :: ps') L1 → L.DeformsAlongAt S ((s, i') :: qs') L2 →
      (((s, i) :: ps').map Prod.fst).Nodup → (((s, i') :: qs').map Prod.fst).Nodup →
      (((s, i) :: ps').map Prod.snd).Nodup → (((s, i') :: qs').map Prod.snd).Nodup →
      (∀ p ∈ (s, i) :: ps', L.a p.2 = L0.a p.2) →
      (∀ p ∈ (s, i') :: qs', L.a p.2 = L0.a p.2) →
      ((s, i) :: ps').IsChain (fun p p' => G.Adj p'.1 (L0.a p.2)) →
      ((s, i') :: qs').IsChain (fun p p' => G.Adj p'.1 (L0.a p.2)) →
      ((s, i) :: ps') <+: ((s, i') :: qs') ∨ ((s, i') :: qs') <+: ((s, i) :: ps') := by
  intro ps'
  induction ps' with
  | nil =>
      intro qs' s i i' L L1 L2 h1 h2 _ _ _ _ _ _ _ _
      cases h1 with
      | cons hs h _ =>
        cases h2 with
        | cons hs' h' _ =>
          have hii := h.index_eq_of_clone h'
          subst hii
          exact Or.inl ((List.prefix_cons_inj _).2 List.nil_prefix)
  | cons p' ps'' ih =>
      intro qs' s i i' L L1 L2 h1 h2 hnf1 hnf2 hns1 hns2 hL1 hL2 hc1 hc2
      cases h1 with
      | cons hs h hr1 =>
        cases h2 with
        | cons hs' h' hr2 =>
          have hii := h.index_eq_of_clone h'
          subst hii
          cases qs' with
          | nil => exact Or.inr ((List.prefix_cons_inj _).2 List.nil_prefix)
          | cons q' qs'' =>
              obtain ⟨s1, i1⟩ := p'
              obtain ⟨t1, j1⟩ := q'
              simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
                at hnf1 hnf2 hns1 hns2
              have hs1S : s1 ∈ S := hr1.mem_S (s1, i1) (List.mem_cons_self ..)
              have ht1S : t1 ∈ S := hr2.mem_S (t1, j1) (List.mem_cons_self ..)
              have hl1 := (List.isChain_cons_cons.1 hc1).1
              have hl2 := (List.isChain_cons_cons.1 hc2).1
              have hsi : G.Adj s (L0.a i) := by
                have := h.adj_original
                rwa [hL1 (s, i) (List.mem_cons_self ..)] at this
              have hs1t1 : s1 = t1 :=
                eq_of_three_nbrs_of_indep hclaw hS (v := L0.a i) (x := s) hs hs1S ht1S
                  hsi.symm hl1.symm hl2.symm hnf1.1.1 hnf2.1.1
              subst hs1t1
              have hne1 : ∀ p ∈ (s1, i1) :: ps'', p.2 ≠ i := by
                intro p hp e
                rcases List.mem_cons.1 hp with rfl | hp
                · exact hns1.1.1 e.symm
                · exact hns1.1.2 (List.mem_map.2 ⟨p, hp, e⟩)
              have hne2 : ∀ p ∈ (s1, j1) :: qs'', p.2 ≠ i := by
                intro p hp e
                rcases List.mem_cons.1 hp with rfl | hp
                · exact hns2.1.1 e.symm
                · exact hns2.1.2 (List.mem_map.2 ⟨p, hp, e⟩)
              have key := ih qs'' s1 i1 j1 (L.deform h) L1 L2 hr1 hr2
                (by simpa using hnf1.2) (by simpa using hnf2.2)
                (by simpa using hns1.2) (by simpa using hns2.2)
                (fun p hp => by
                  rw [L.deform_a_away h (hne1 p hp)]
                  exact hL1 p (List.mem_cons_of_mem _ hp))
                (fun p hp => by
                  rw [L.deform_a_away h (hne2 p hp)]
                  exact hL2 p (List.mem_cons_of_mem _ hp))
                (List.isChain_cons_cons.1 hc1).2 (List.isChain_cons_cons.1 hc2).2
              rcases key with hpre | hpre
              · exact Or.inl ((List.prefix_cons_inj _).2 hpre)
              · exact Or.inr ((List.prefix_cons_inj _).2 hpre)

/-- `prefix_agree` for two lists of pairs, with the common start expressed on the first
vertices. -/
theorem DeformsAlongAt.prefix_agree' (hclaw : G.IsClawFree) (hS : G.IsIndepSet S)
    {L L1 L2 : G.EvenHoleLabeling k} {ps qs : List (V × Fin k)}
    (h1 : L.DeformsAlongAt S ps L1) (h2 : L.DeformsAlongAt S qs L2)
    (hnf1 : (ps.map Prod.fst).Nodup) (hnf2 : (qs.map Prod.fst).Nodup)
    (hns1 : (ps.map Prod.snd).Nodup) (hns2 : (qs.map Prod.snd).Nodup)
    (hc1 : ps.IsChain (fun p p' => G.Adj p'.1 (L.a p.2)))
    (hc2 : qs.IsChain (fun p p' => G.Adj p'.1 (L.a p.2)))
    (hhead : ∀ p q, ps.head? = some p → qs.head? = some q → p.1 = q.1) :
    ps <+: qs ∨ qs <+: ps := by
  cases ps with
  | nil => exact Or.inl List.nil_prefix
  | cons p ps' =>
    cases qs with
    | nil => exact Or.inr List.nil_prefix
    | cons q qs' =>
      obtain ⟨s, i⟩ := p
      obtain ⟨t, j⟩ := q
      have hst : s = t := hhead _ _ rfl rfl
      subst hst
      exact DeformsAlongAt.prefix_agree hclaw hS L ps' qs' s i j L L1 L2 h1 h2 hnf1 hnf2
        hns1 hns2 (fun _ _ => rfl) (fun _ _ => rfl) hc1 hc2

end Uniqueness

namespace SetDeformationPath

section UniquenessPaths

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The list `[(s₀, i₀), …, (s_{ℓ-1}, i_{ℓ-1})]` of vertex-index pairs of a path. -/
abbrev pairs (P : L.SetDeformationPath S) : List (V × Fin k) :=
  List.ofFn fun j => (P.s j, P.idx j)

theorem isChain_pairs (P : L.SetDeformationPath S) :
    P.pairs.IsChain (fun p p' => G.Adj p'.1 (L.a p.2)) := by
  rw [List.isChain_iff_getElem]
  intro j hj
  simp only [List.length_ofFn] at hj
  simp only [List.getElem_ofFn]
  exact P.link ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl

theorem head?_pairs (P : L.SetDeformationPath S) :
    P.pairs.head? = some (P.s P.first, P.idx P.first) := by
  rw [List.head?_eq_getElem?, List.getElem?_ofFn]
  simp [first, P.len_pos]

theorem mem_support_iff_pairs [DecidableEq V] (P : L.SetDeformationPath S) {v : V} :
    v ∈ P.support ↔ ∃ p ∈ P.pairs, p.1 = v ∨ L.a p.2 = v := by
  rw [mem_support_iff]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(P.s j, P.idx j), List.mem_ofFn.2 ⟨j, rfl⟩, hj⟩
  · rintro ⟨p, hp, hv⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hp
    exact ⟨j, hv⟩

/-- If the pairs of `P` form a prefix of those of `Q`, the two paths agree on the common
positions. -/
theorem agree_of_prefix {P Q : L.SetDeformationPath S} (hpre : P.pairs <+: Q.pairs) {j : ℕ}
    (hjP : j < P.len) (hjQ : j < Q.len) :
    P.s ⟨j, hjP⟩ = Q.s ⟨j, hjQ⟩ ∧ P.idx ⟨j, hjP⟩ = Q.idx ⟨j, hjQ⟩ := by
  have := hpre.getElem (i := j) (by simpa using hjP)
  simpa [List.getElem_ofFn] using this

/-- A path that is a proper prefix of another path is neither untethered nor tethered: its
last replaced vertex has a further neighbour `t₀ ∈ S` (the next vertex of the longer path),
which is a clone of an `a`-vertex of an intermediate hole, hence has two `b`-neighbours, whereas
a tether has exactly one. -/
theorem false_of_prefix_lt [DecidableEq V] (hclaw : G.IsClawFree)
    (hS : G.IsIndepSet (S : Set V)) {P Q : L.SetDeformationPath S}
    (hpre : P.pairs <+: Q.pairs) (hlt : P.len < Q.len)
    (hP : P.Untethered ∨ ∃ t, P.TetheredTo t) : False := by
  have hP1 := P.len_pos
  have hlast := (agree_of_prefix hpre (j := P.len - 1) (by omega) (by omega)).2
  have hlink := Q.link ⟨P.len - 1, by omega⟩ ⟨P.len, hlt⟩ (by simp; omega)
  have ht0 : G.Adj (Q.s ⟨P.len, hlt⟩) (L.a (P.idx P.last)) := by
    have e : P.idx P.last = Q.idx ⟨P.len - 1, by omega⟩ := hlast
    rw [e]
    exact hlink
  have ht0P : Q.s ⟨P.len, hlt⟩ ∉ Set.range P.s := by
    rintro ⟨j, hj⟩
    have h1 := (agree_of_prefix hpre (j := j.val) j.isLt (by omega)).1
    have h2 : Q.s ⟨j.val, by omega⟩ = Q.s ⟨P.len, hlt⟩ := h1.symm.trans hj
    have h3 := Q.s_injective h2
    have h4 : j.val = P.len := by simpa using congrArg Fin.val h3
    have := j.isLt
    omega
  rcases hP with hU | ⟨t, htS, htP, hadj, r, hr⟩
  · exact P.not_untethered_of_ext (Finset.mem_coe.1 (Finset.mem_coe.2 (Q.s_mem _))) ht0P ht0 hU
  · have hteq : t = Q.s ⟨P.len, hlt⟩ :=
      eq_of_three_nbrs_of_indep (S := (↑S : Set V)) hclaw hS (v := L.a (P.idx P.last))
        (x := P.s P.last)
        (P.s_mem _) htS (Q.s_mem _) (P.adj_a_idx _).symm hadj.symm ht0.symm
        (fun e => htP ⟨P.last, e⟩) (fun e => ht0P ⟨P.last, e⟩)
    subst hteq
    obtain ⟨M, hM, hMb⟩ := Q.exists_clone ⟨P.len, hlt⟩
    have key : ∀ q, G.Adj (Q.s ⟨P.len, hlt⟩) (L.b q) → L.b q = L.b r := by
      intro q hq
      rcases (hr.adj_iff (L.b q) (by rw [swapColors_carrier]; exact L.b_mem_carrier q)).1 hq with
        e | hadj
      · exact e
      · exact (L.adj_bb r q hadj).elim
    have h1 := hM.adj_b
    have h2 := hM.adj_b_next
    rw [hMb] at h1 h2
    have e1 := key _ h1
    have e2 := key _ h2
    exact M.next_ne _ (L.b_injective (e1.trans e2.symm)).symm

/-- **Uniqueness of the run** (v1 L762: "there is a unique path associated to the sequence of
deformations").  Two maximal deformation paths (untethered or tethered) along `S` that start
with the same vertex `s₀` have identical lists of vertex-index pairs
`[(s₀, i₀), (s₁, i₁), …]`: the same length `ℓ` and the same vertices `s_j` and indices `i_j`
in every position.  (The first index `i₀` is already determined by `s₀`, by
`CloneAt.index_eq_of_clone`.)

As in `CloneAt.exists_setDeformationPath`, the hypothesis `_hL` is part of the manuscript's
setting and is not used. -/
theorem pairs_eq_of_start [DecidableEq V] (hclaw : G.IsClawFree) (_hL : L.HasFullCyclicOrder)
    (hS : G.IsIndepSet (S : Set V)) (P Q : L.SetDeformationPath S)
    (hP : P.Untethered ∨ ∃ t, P.TetheredTo t) (hQ : Q.Untethered ∨ ∃ t, Q.TetheredTo t)
    (h0 : P.s P.first = Q.s Q.first) : P.pairs = Q.pairs := by
  have hagree := DeformsAlongAt.prefix_agree' hclaw hS P.run Q.run P.nodup_fst Q.nodup_fst
    P.nodup_snd Q.nodup_snd P.isChain_pairs Q.isChain_pairs (by
      intro p q hp hq
      rw [P.head?_pairs] at hp
      rw [Q.head?_pairs] at hq
      cases hp
      cases hq
      exact h0)
  rcases hagree with hpre | hpre
  · have hlen : P.len = Q.len := by
      by_contra hne
      exact false_of_prefix_lt hclaw hS hpre
        (lt_of_le_of_ne (by simpa using hpre.length_le) hne) hP
    exact hpre.eq_of_length (by simpa using hlen)
  · have hlen : Q.len = P.len := by
      by_contra hne
      exact false_of_prefix_lt hclaw hS hpre
        (lt_of_le_of_ne (by simpa using hpre.length_le) hne) hQ
    exact (hpre.eq_of_length (by simpa using hlen)).symm

/-- **Uniqueness of the run, numerical form**: two maximal deformation paths along `S` that
start with the same vertex `s₀` have the same length `ℓ` and the same vertex set
(see `pairs_eq_of_start` for the full statement). -/
theorem eq_of_start [DecidableEq V] (hclaw : G.IsClawFree) (hL : L.HasFullCyclicOrder)
    (hS : G.IsIndepSet (S : Set V)) (P Q : L.SetDeformationPath S)
    (hP : P.Untethered ∨ ∃ t, P.TetheredTo t) (hQ : Q.Untethered ∨ ∃ t, Q.TetheredTo t)
    (h0 : P.s P.first = Q.s Q.first) : P.len = Q.len ∧ P.support = Q.support := by
  have heq := pairs_eq_of_start hclaw hL hS P Q hP hQ h0
  refine ⟨by simpa using congrArg List.length heq, ?_⟩
  ext v
  rw [mem_support_iff_pairs, mem_support_iff_pairs, heq]

/-! #### The path is an odd component: `2ℓ - 1` edges -/

/-- The `b`-vertices of the final labelling are those of `L`. -/
theorem final_b (P : L.SetDeformationPath S) (q : Fin k) : P.final.b q = L.b q :=
  P.run.b_eq q

/-- The `a`-vertex of the final hole at the replaced index `i_j` is the vertex `s_j`. -/
theorem final_a_idx (P : L.SetDeformationPath S) (j : Fin P.len) :
    P.final.a (P.idx j) = P.s j :=
  P.run.a_eq_of_mem P.nodup_snd (P.s j, P.idx j) (List.mem_ofFn.2 ⟨j, rfl⟩)

/-- The `a`-vertices at indices that are never replaced are unchanged. -/
theorem final_a_of_forall_ne (P : L.SetDeformationPath S) {q : Fin k}
    (hq : ∀ j, P.idx j ≠ q) : P.final.a q = L.a q := by
  refine P.run.a_eq_of_not_mem q fun hmem => ?_
  obtain ⟨p, hp, e⟩ := List.mem_map.1 hmem
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hp
  exact hq j e

/-- `s_j` is not adjacent to `a_{i_m}` for `j < m`. -/
theorem not_adj_of_lt (P : L.SetDeformationPath S) {j m : Fin P.len} (hjm : j < m) :
    ¬G.Adj (P.s j) (L.a (P.idx m)) := by
  have h := P.run.pairwise_not_adj P.nodup_snd
  rw [List.pairwise_iff_getElem] at h
  simpa using h j.val m.val (by simp) (by simp) hjm

/-- Each `a_{i_j}` lies outside `S` (it is adjacent to `s_j ∈ S`). -/
theorem a_idx_not_mem (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S)
    (j : Fin P.len) : L.a (P.idx j) ∉ S := fun ha =>
  hS (Finset.mem_coe.2 (P.s_mem j)) (Finset.mem_coe.2 ha) (P.adj_a_idx j).ne (P.adj_a_idx j)

/-- Each `s_j` lies outside the `a`-class of `C`. -/
theorem s_not_mem_image_a [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (j : Fin P.len) : P.s j ∉ Finset.univ.image L.a := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro q hq
  by_cases hqS : L.a q ∈ S
  · exact P.s_ne_of_a_mem hS hqS j hq.symm
  · exact hqS (hq ▸ P.s_mem j)

/-- The adjacencies between the `s_j` and the replaced `a_{i_m}` form the path
`s₀ - a_{i₀} - s₁ - a_{i₁} - ⋯ - s_{ℓ-1} - a_{i_{ℓ-1}}`: `s_j ~ a_{i_m}` iff `j = m` or
`j = m + 1`.  (Here claw-freeness enters twice: `a_{i_m}` has at most two neighbours in `S`, and
a clone is adjacent to exactly one `a`-vertex of the current hole.) -/
theorem adj_s_a_iff (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (j m : Fin P.len) :
    G.Adj (P.s j) (L.a (P.idx m)) ↔ j.val = m.val ∨ j.val = m.val + 1 := by
  constructor
  · intro hadj
    by_contra hnot
    rw [not_or] at hnot
    rcases lt_trichotomy j m with hlt | heq | hgt
    · exact P.not_adj_of_lt hlt hadj
    · exact hnot.1 (congrArg Fin.val heq)
    · have hm1 : m.val + 1 < P.len := by
        have := j.isLt
        have : m.val < j.val := hgt
        omega
      have hne1 : P.s m ≠ P.s ⟨m.val + 1, hm1⟩ := fun e => by
        have := congrArg Fin.val (P.s_injective e)
        simp at this
      have hne2 : P.s m ≠ P.s j := fun e => by
        have := congrArg Fin.val (P.s_injective e)
        omega
      have := eq_of_three_nbrs_of_indep (S := (↑S : Set V)) hclaw hS (v := L.a (P.idx m))
        (x := P.s m) (y := P.s ⟨m.val + 1, hm1⟩) (z := P.s j)
        (P.s_mem _) (P.s_mem _) (P.s_mem _) (P.adj_a_idx m).symm
        (P.link m ⟨m.val + 1, hm1⟩ rfl).symm hadj.symm hne1 hne2
      have h2 := congrArg Fin.val (P.s_injective this)
      exact hnot.2 h2.symm
  · rintro (h | h)
    · have : j = m := Fin.ext h
      subst this
      exact P.adj_a_idx j
    · exact P.link m j h.symm

/-- Numerical identity used for the cross count: `∑_{m<ℓ} (if m + 1 < ℓ then 2 else 1) = 2ℓ-1`. -/
theorem sum_two_or_one (len : ℕ) (hlen : 0 < len) :
    ∑ m ∈ Finset.range len, (if m + 1 < len then 2 else 1) = 2 * len - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hlen.ne'
  rw [Finset.sum_range_succ]
  have : ∑ m ∈ Finset.range n, (if m + 1 < n.succ then 2 else 1) =
      ∑ m ∈ Finset.range n, 2 :=
    Finset.sum_congr rfl fun m hm => by
      have := Finset.mem_range.1 hm
      simp [Nat.succ_eq_add_one]
      omega
  rw [this]
  simp [Nat.succ_eq_add_one]
  omega

/-- **The deformation path is an induced path with `2ℓ - 1` edges** (v1 L764: "the path `P`
has odd length `2ℓ - 1`").  Precisely: the number of adjacent pairs between `S ∩ P` (the `s_j`)
and `C_a ∩ P` (the `a_{i_j}`) is `2ℓ - 1`.  This holds for every deformation path, tethered or
not. -/
theorem crossCount_support [DecidableEq V] (hclaw : G.IsClawFree)
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) :
    G.crossCount (S ∩ P.support) (Finset.univ.image L.a ∩ P.support) = 2 * P.len - 1 := by
  classical
  have hSsupp : S ∩ P.support = Finset.univ.image P.s := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, mem_support_iff]
    constructor
    · rintro ⟨hxS, j, hj | hj⟩
      · exact ⟨j, hj⟩
      · exact (P.a_idx_not_mem hS j (hj ▸ hxS)).elim
    · rintro ⟨j, rfl⟩
      exact ⟨P.s_mem j, j, Or.inl rfl⟩
  have hAsupp : Finset.univ.image L.a ∩ P.support =
      Finset.univ.image (fun j => L.a (P.idx j)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, mem_support_iff]
    constructor
    · rintro ⟨⟨q, hq⟩, j, hj | hj⟩
      · exact (P.s_not_mem_image_a hS j
          (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hj ▸ hq⟩)).elim
      · exact ⟨j, hj⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨P.idx j, rfl⟩, j, Or.inr rfl⟩
  rw [hSsupp, hAsupp, crossCount_comm, crossCount_eq_sum_card_filter,
    Finset.sum_image (fun a _ b _ hab => P.idx_injective (L.a_injective hab))]
  have hcard : ∀ m : Fin P.len,
      ((Finset.univ.image P.s).filter (G.Adj (L.a (P.idx m)))).card =
        if m.val + 1 < P.len then 2 else 1 := by
    intro m
    have hfilt : (Finset.univ.image P.s).filter (G.Adj (L.a (P.idx m))) =
        (Finset.univ.filter fun j : Fin P.len =>
          j.val = m.val ∨ j.val = m.val + 1).image P.s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j, rfl⟩, hadj⟩
        exact ⟨j, (P.adj_s_a_iff hclaw hS j m).1 hadj.symm, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, ((P.adj_s_a_iff hclaw hS j m).2 hj).symm⟩
    rw [hfilt, Finset.card_image_of_injective _ P.s_injective]
    by_cases hm : m.val + 1 < P.len
    · have : (Finset.univ.filter fun j : Fin P.len => j.val = m.val ∨ j.val = m.val + 1) =
          {m, ⟨m.val + 1, hm⟩} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff]
      rw [this, if_pos hm, Finset.card_pair]
      intro e
      have := congrArg Fin.val e
      simp at this
    · have : (Finset.univ.filter fun j : Fin P.len => j.val = m.val ∨ j.val = m.val + 1) =
          {m} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff]
        have := j.isLt
        omega
      rw [this, if_neg hm, Finset.card_singleton]
  rw [Finset.sum_congr rfl fun m _ => hcard m]
  rw [Fin.sum_univ_eq_sum_range (fun m => if m + 1 < P.len then 2 else 1) P.len]
  exact sum_two_or_one P.len P.len_pos

/-- The deformation path has an odd number of edges, so (in the untethered case) it is an odd
component of `G[S ⊕ C_a]` in the sense of `card_and_tokenSlideReachable_symmDiff`. -/
theorem odd_crossCount_support [DecidableEq V] (hclaw : G.IsClawFree)
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) :
    Odd (G.crossCount (S ∩ P.support) (Finset.univ.image L.a ∩ P.support)) := by
  rw [P.crossCount_support hclaw hS]
  have := P.len_pos
  exact ⟨P.len - 1, by omega⟩

end UniquenessPaths

end SetDeformationPath

end EvenHoleLabeling

end SimpleGraph
