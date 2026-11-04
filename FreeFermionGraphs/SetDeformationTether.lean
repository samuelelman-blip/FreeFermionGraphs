import FreeFermionGraphs.SetDeformationPath
import FreeFermionGraphs.HoleChargeSigns

/-!
# The tether relation of a deformation path (v1 L762-764, L908-910)

This module proves the two claims about *tethering* that the manuscript (arXiv 2305.15625 v1)
only asserts.  In the proof of Theorem 1 (ii) (v1 L906-910) the deformation path
`P = s₀ - a₀ - s₁ - ⋯ - s_{ℓ-1} - a_{ℓ-1}` along an independent set `S` of the labelled even hole
`C` (module `FreeFermionGraphs.SetDeformationPath`, v1 L753-766 and Fig. `deformationsequence`)
may be *tethered* to a vertex `s_ℓ = t ∈ S` (v1 L762-763: "Letting `P'` be the path component of
`G[S ⊕ C_b]` with `s_ℓ` as an endpoint, we could similarly deform `C` along `P'` until we reach
the vertex `s₀`, so `s₀` and `s_ℓ` can be uniquely associated this way. We say that `s₀` and `s_ℓ`
are tethered"), and then (v1 L908-910) "if every such initializing vertex is tethered, then they
can be uniquely paired, which contradicts the assumption that `h_S` and `h_C` anticommute. Thus,
there is at least one untethered path".  Neither the symmetry of the association nor the pairing
is proved in v1.

## Results

* `SimpleGraph.EvenHoleLabeling.SetDeformationPath.tetheredTo_symm`: if the deformation path `P`
  of `L` initialised by `s₀` is tethered to `t`, then `t ≠ s₀`, `t ∈ A(C,S)`
  (`SimpleGraph.anticommutingVertices`: `t` has three neighbours in `C`), and `t` initialises a
  deformation path `Q` of `L.swapColors` (the `b`-class run) which is tethered back to `s₀`.
  Its general form is `tetheredTo_dual`, and `exists_reverse_path` additionally records that `Q`
  has the same length `ℓ` and visits `s_{ℓ-1}, …, s_1` in reverse order.  They hold for an
  arbitrary *dual* hole `T` of `L`
  (`IsDualTo`: same vertices, `T.a`-class = `L.b`-class, `T.b`-class = `L.a`-class); both
  `L.swapColors` and `L` (seen from `L.swapColors`) are duals, which is what lets the two colour
  classes be treated alike without the reindexing `L.swapColors.swapColors ≠ L`.
* `SetDeformationPath.TetheredTo.unique`, `TetheredTo.unique_of_start`: the tether is unique,
  and determined by the initialising vertex (claw-freeness at the last replaced vertex).
  `SetDeformationPath.s_first_mem_anticommutingVertices`: the initialising vertex lies in
  `A(C,S)` (it is a clone, hence has three neighbours in `C`).
* `SimpleGraph.EvenHoleLabeling.TetherPair`, `TetherPair.symm`, `TetherPair.unique`,
  `TetherPair.involutive`: `s ↦ tether(s)` is a fixed-point-free involution on the members of
  `A(C,S)` whose run (in either colour class) is tethered.
* `SimpleGraph.EvenHoleLabeling.exists_untethered_of_odd`: if `|A(C,S)|` is odd then some vertex
  of `A(C,S)` initialises an untethered deformation path, in the `a`-class of `L` or in the
  `a`-class of `L.swapColors`.  (By
  `PauliFrustrationRepresentation.labelingOperator_mul_independentProduct` the hypothesis is
  equivalent to `h_C` and `h_S` anticommuting.)

## The ladder

The key step is the "ladder" description of a tethered run (`TetherLadder`,
`SetDeformationPath.ladder_of_tetheredTo`): `s_{j-1}` and `s_j` share a `b`-vertex `y_j`, so the
`s_j` slide along the hole like windows of four consecutive vertices
`a_{i_{j-1}}, y_j, a_{i_j}, y_{j+1}` (three for `s₀` and for `t`).  The reverse run is then built by
`exists_dualPath_of_ladder` from *adjacency conditions alone*
(`exists_deformsAlongAt_of_conditions`: a list of vertices is a run as soon as each one has the
neighbourhood of the clone it replaces).  No orientation of the hole is needed, and the case
analysis of v1 Lemma 3 (repo `CloneAt.lemma8`) is not repeated: the claw-free argument at
`a_{i_{j-1}}` (neighbours `b_{i_{j-1}}, b_{next i_{j-1}}, s_{j-1}, s_j`; v1 Corollary 1, repo
`IsClawFree.adjacent_to_one_of_nonadjacent_neighbors`) and at `y_j` suffices.  Lemma 3 enters only
through the existence of the runs (`CloneAt.exists_setDeformationPath`).

## Deviations and remarks

* The hypothesis `[Fintype V]` of the work-package statement is not needed and is dropped.
* `tetheredTo_symm` does not use full cyclic order (`_hL`), as in `SetDeformationPath`; the
  parity statement `exists_untethered_of_odd` does, through the clone structure of `A(C,S)`
  (`cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet`) and the existence of runs.
* "Tethered back to `s₀`" is a statement about `L.swapColors.swapColors`, which has the carrier of
  `L` and the `a`-indices of `L` shifted by `prev`.  It is expressed at the level of carriers
  (`CloneAt.exists_swapColors_cloneAt_of_isDual`) and never through an identification
  `L.swapColors.swapColors = L`, which does not hold.
* v1 numbering used in the docstrings: v1 Lemma 3 is repo Lemma 8 (`CloneAt.lemma8`), v1
  Corollaries 1-2 are repo Corollaries 2-3.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-! ### Dual labellings -/

section Dual

variable {k : ℕ}

/-- `T` is a *dual* of `L`: both have the same vertices, the `a`-class of `T` is the `b`-class
of `L`, and the `b`-class of `T` is the `a`-class of `L`.  The colour-swapped labelling
`L.swapColors` is a dual of `L`, and `L` is a dual of `L.swapColors`; the relation is symmetric
(`IsDualTo.symm`), which lets us treat `L.swapColors.swapColors` (an index shift of `L`) without
reindexing. -/
def IsDualTo (L T : G.EvenHoleLabeling k) : Prop :=
  Set.range T.a = Set.range L.b ∧ Set.range T.b = Set.range L.a

theorem IsDualTo.symm {L T : G.EvenHoleLabeling k} (h : L.IsDualTo T) : T.IsDualTo L :=
  ⟨h.2.symm, h.1.symm⟩

theorem IsDualTo.carrier_eq {L T : G.EvenHoleLabeling k} (h : L.IsDualTo T) :
    T.carrier = L.carrier := by
  unfold carrier
  rw [h.1, h.2]
  exact Set.union_comm _ _

theorem isDualTo_swapColors (L : G.EvenHoleLabeling k) : L.IsDualTo L.swapColors := by
  refine ⟨rfl, ?_⟩
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨L.prev i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨L.next i, show L.a (L.prev (L.next i)) = L.a i by rw [L.prev_next]⟩

theorem nextIterate_swapColors (L : G.EvenHoleLabeling k) (n : ℕ) (i : Fin k) :
    L.swapColors.nextIterate n i = L.nextIterate n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [nextIterate_succ]
      exact congrArg L.next ih

theorem HasFullCyclicOrder.swapColors {L : G.EvenHoleLabeling k} (hL : L.HasFullCyclicOrder) :
    L.swapColors.HasFullCyclicOrder := by
  intro i n hn hk
  rw [nextIterate_swapColors]
  exact hL i n hn hk

/-- A clone `s ≺_C a_i` of `L` is a clone of a `b`-vertex for the colour swap of any dual `T`
of `L`: the `b`-class of `T` is the `a`-class of `L`. -/
theorem CloneAt.exists_swapColors_cloneAt_of_isDual {L T : G.EvenHoleLabeling k}
    (hLT : L.IsDualTo T) {s : V} {i : Fin k} (h : L.CloneAt s i) :
    ∃ r, T.swapColors.CloneAt s r := by
  have hmem : L.a i ∈ Set.range T.b := hLT.2 ▸ ⟨i, rfl⟩
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ⟨?_, fun v hv => ?_⟩⟩
  · rw [swapColors_carrier, hLT.carrier_eq]
    exact h.outside
  · rw [swapColors_carrier, hLT.carrier_eq] at hv
    rw [swapColors_a, hr]
    exact h.adj_iff v hv

/-- A clone has exactly three neighbours in the carrier: `a i`, `b i` and `b (next i)`. -/
theorem CloneAt.adjacencyCount_eq_three {L : G.EvenHoleLabeling k} {s : V} {i : Fin k}
    (h : L.CloneAt s i) : G.adjacencyCount s L.carrier = 3 := by
  have hset : G.adjacentIn s L.carrier = {L.a i, L.b i, L.b (L.next i)} := by
    ext v
    simp only [adjacentIn, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, hadj⟩
      rcases (h.adj_iff v hv).1 hadj with e | e
      · exact Or.inl e
      · exact Or.inr ((L.adj_a_iff_of_mem_carrier i hv).1 e)
    · intro hv
      have hv' : v ∈ L.carrier := by
        rcases hv with rfl | rfl | rfl
        · exact L.a_mem_carrier i
        · exact L.b_mem_carrier i
        · exact L.b_mem_carrier _
      refine ⟨hv', (h.adj_iff v hv').2 ?_⟩
      rcases hv with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (L.adj_a_b i)
      · exact Or.inr (L.adj_a_b_next i)
  unfold adjacencyCount
  rw [hset, Set.ncard_eq_three]
  refine ⟨L.a i, L.b i, L.b (L.next i), (L.color_disjoint i i), (L.color_disjoint i _), ?_, rfl⟩
  exact fun e => L.next_ne i (L.b_injective e).symm

end Dual

/-! ### Runs: the clone data at a given position, and runs from adjacency conditions -/

section Runs

variable {S : Set V} {k : ℕ}

/-- The `j`-th vertex of a run is a clone of the hole reached after `j` steps; that hole has
the `b`-vertices and the successor map of the starting hole, and the `a`-vertices of the starting
hole at all indices that were not replaced earlier. -/
theorem DeformsAlongAt.exists_clone_getElem {L L' : G.EvenHoleLabeling k}
    {ps : List (V × Fin k)} (hrun : L.DeformsAlongAt S ps L') :
    ∀ (j : ℕ) (hj : j < ps.length), ∃ M : G.EvenHoleLabeling k,
      M.CloneAt (ps[j]).1 (ps[j]).2 ∧ (∀ q, M.b q = L.b q) ∧ (∀ q, M.next q = L.next q) ∧
      ∀ q, (∀ m (hm : m < j), (ps[m]'(by omega)).2 ≠ q) → M.a q = L.a q := by
  induction hrun with
  | nil L => intro j hj; simp at hj
  | @cons L L' s i rest hs h hr ih =>
      intro j hj
      cases j with
      | zero => exact ⟨L, by simpa using h, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
      | succ j =>
          obtain ⟨M, hM, hMb, hMn, hMa⟩ := ih j (by simpa using hj)
          refine ⟨M, by simpa using hM, fun q => (hMb q).trans (L.deform_b h q),
            fun q => (hMn q).trans (L.deform_next h q), fun q hq => ?_⟩
          have hqi : q ≠ i := by
            have h0 : i ≠ q := by simpa using hq 0 (by omega)
            exact h0.symm
          rw [hMa q (fun m hm => by simpa using hq (m + 1) (by omega)),
            L.deform_a_away h hqi]

/-- **A run from adjacency conditions.**  Let `ps = [(v₀, i₀), (v₁, i₁), …]` be a list of
vertices of an independent set and indices such that, in the hole `M`,

* the `v_m` and the `i_m` are pairwise distinct and the `v_m` lie outside `M`;
* each `v_m` has the `b`-neighbours of `a_{i_m}` and is adjacent to `a_{i_m}`;
* the only `a`-vertices of `M` adjacent to `v_m` are the `a_{i_{m'}}` with `i_{m'}` in the list,
  and an earlier `v_{m'}` is not adjacent to a later `a_{i_m}`.

Then the vertices can be added one after the other as clones: `ps` is a run starting at `M`.
(Carrier-level description of a run; no orientation of the hole is involved.) -/
theorem exists_deformsAlongAt_of_conditions (hS : G.IsIndepSet S) :
    ∀ (ps : List (V × Fin k)) (M : G.EvenHoleLabeling k),
      (∀ p ∈ ps, p.1 ∈ S) → (ps.map Prod.fst).Nodup → (ps.map Prod.snd).Nodup →
      (∀ p ∈ ps, p.1 ∉ M.carrier) →
      (∀ p ∈ ps, ∀ q, G.Adj p.1 (M.b q) ↔ G.Adj (M.a p.2) (M.b q)) →
      (∀ p ∈ ps, G.Adj p.1 (M.a p.2)) →
      (∀ p ∈ ps, ∀ q, G.Adj p.1 (M.a q) → q ∈ ps.map Prod.snd) →
      ps.Pairwise (fun p p' => ¬G.Adj p.1 (M.a p'.2)) →
      ∃ M' : G.EvenHoleLabeling k, M.DeformsAlongAt S ps M' := by
  intro ps
  induction ps with
  | nil => intro M _ _ _ _ _ _ _ _; exact ⟨M, .nil M⟩
  | cons p ps ih =>
      intro M hmem hfst hsnd hout hb hadj hq hpw
      obtain ⟨v, i⟩ := p
      rw [List.map_cons, List.nodup_cons] at hfst hsnd
      have hvS : v ∈ S := hmem _ (List.mem_cons_self ..)
      have hclone : M.CloneAt v i := by
        refine ⟨hout _ (List.mem_cons_self ..), fun w hw => ?_⟩
        rcases hw with ⟨q, rfl⟩ | ⟨q, rfl⟩
        · constructor
          · intro hvq
            have hqm := hq _ (List.mem_cons_self ..) q hvq
            simp only [List.map_cons, List.mem_cons, List.mem_map] at hqm
            rcases hqm with rfl | ⟨p', hp', rfl⟩
            · exact Or.inl rfl
            · exact ((List.pairwise_cons.1 hpw).1 p' hp' hvq).elim
          · rintro (h | h)
            · rw [M.a_injective h]
              exact hadj _ (List.mem_cons_self ..)
            · exact (M.adj_aa i q h).elim
        · rw [hb _ (List.mem_cons_self ..) q]
          constructor
          · exact Or.inr
          · rintro (h | h)
            · exact (M.color_disjoint i q h.symm).elim
            · exact h
      have hne : ∀ p' ∈ ps, p'.2 ≠ i := fun p' hp' e => hsnd.1 (List.mem_map.2 ⟨p', hp', e⟩)
      have hnev : ∀ p' ∈ ps, p'.1 ≠ v := fun p' hp' e => hfst.1 (List.mem_map.2 ⟨p', hp', e⟩)
      obtain ⟨M', hM'⟩ := ih (M.deform hclone)
        (fun p' hp' => hmem p' (List.mem_cons_of_mem _ hp'))
        hfst.2 hsnd.2
        (fun p' hp' => by
          rw [M.deform_carrier hclone]
          rintro (h | ⟨h, _⟩)
          · exact hnev p' hp' h
          · exact hout p' (List.mem_cons_of_mem _ hp') h)
        (fun p' hp' q => by
          rw [M.deform_a_away hclone (hne p' hp')]
          exact hb p' (List.mem_cons_of_mem _ hp') q)
        (fun p' hp' => by
          rw [M.deform_a_away hclone (hne p' hp')]
          exact hadj p' (List.mem_cons_of_mem _ hp'))
        (fun p' hp' q hadjq => by
          by_cases hqi : q = i
          · subst hqi
            rw [M.deform_a_at] at hadjq
            exact (hS (hmem p' (List.mem_cons_of_mem _ hp')) hvS (hnev p' hp') hadjq).elim
          · rw [M.deform_a_away hclone hqi] at hadjq
            have := hq p' (List.mem_cons_of_mem _ hp') q hadjq
            simp only [List.map_cons, List.mem_cons] at this
            rcases this with rfl | h
            · exact (hqi rfl).elim
            · exact h)
        (by
          refine List.Pairwise.imp_of_mem ?_ (List.pairwise_cons.1 hpw).2
          intro p' p'' hp' hp'' h
          rwa [M.deform_a_away hclone (hne p'' hp'')])
      exact ⟨M', .cons hvS hclone hM'⟩

end Runs

/-! ### Ladders and the dual path -/

section Ladder

variable {k : ℕ}

/-- Three pairwise non-adjacent neighbours of a vertex are impossible in a claw-free graph:
a third `S`-neighbour of a vertex with two distinct `S`-neighbours `x, y` is one of them. -/
theorem eq_or_eq_of_three_nbrs {S : Set V} (hclaw : G.IsClawFree) (hS : G.IsIndepSet S)
    {v x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hvz : G.Adj v z) (hxy : x ≠ y) : z = x ∨ z = y := by
  by_contra h
  rw [not_or] at h
  exact h.2 (eq_of_three_nbrs_of_indep hclaw hS hx hy hz hvx hvy hvz hxy (Ne.symm h.1)).symm

/-- The *ladder* of a tethered deformation path (v1 L762-764, Fig. `deformationsequence`).

If `s₀ ≺_C a_{i₀}`, ..., `s_{ℓ-1}` is a deformation path along `S` tethered to `t = s_ℓ`, then
consecutive `s_{j-1}, s_j` (`1 ≤ j ≤ ℓ`) share a `b`-vertex `y_j`, the neighbours of `s_j` in `C`
are the four consecutive vertices `a_{i_{j-1}}, b, a_{i_j}, b'` (and `s₀`, `t` have three), so that
the `s_j` slide along the hole like a window; `y_j` is the `b`-vertex below `s_j`.  A ladder is
exactly the data needed to start the path from `t` along the `b`-class instead, with
`y_ℓ, y_{ℓ-1}, …, y_1` as the replaced vertices (`exists_dualPath_of_ladder`).

This is an auxiliary description: it is *produced* by `SetDeformationPath.ladder_of_tetheredTo`
from a tethered path, never assumed. -/
structure TetherLadder (L : G.EvenHoleLabeling k) (S : Finset V) (ℓ : ℕ) where
  /-- The vertices `s₀, …, s_{ℓ-1}, s_ℓ = t`. -/
  x : ℕ → V
  /-- The shared `b`-vertices `y_j` of `s_{j-1}` and `s_j`, `1 ≤ j ≤ ℓ`. -/
  y : ℕ → V
  x_mem : ∀ j, j ≤ ℓ → x j ∈ S
  x_inj : ∀ j j', j ≤ ℓ → j' ≤ ℓ → x j = x j' → j = j'
  x_not_mem : ∀ j, j ≤ ℓ → x j ∉ L.carrier
  y_mem : ∀ j, 1 ≤ j → j ≤ ℓ → y j ∈ Set.range L.b
  adj_prev : ∀ j, 1 ≤ j → j ≤ ℓ → G.Adj (x (j - 1)) (y j)
  adj_self : ∀ j, 1 ≤ j → j ≤ ℓ → G.Adj (x j) (y j)
  /-- `s_j` and `y_j` have the same neighbours among the `a`-vertices. -/
  adj_a_iff : ∀ j, 1 ≤ j → j ≤ ℓ → ∀ w ∈ Set.range L.a, (G.Adj (x j) w ↔ G.Adj (y j) w)
  /-- The only `b`-neighbours of `s_j` are `y_j` and `y_{j+1}`. -/
  adj_b_imp : ∀ j, 1 ≤ j → j ≤ ℓ → ∀ w ∈ Set.range L.b, G.Adj (x j) w →
    w = y j ∨ (j < ℓ ∧ w = y (j + 1))

namespace TetherLadder

variable {L : G.EvenHoleLabeling k} {S : Finset V} {ℓ : ℕ}

theorem x_eq_iff (D : TetherLadder L S ℓ) {j j' : ℕ} (hj : j ≤ ℓ) (hj' : j' ≤ ℓ) :
    D.x j = D.x j' ↔ j = j' :=
  ⟨D.x_inj j j' hj hj', fun h => h ▸ rfl⟩

/-- `y_j` has exactly the two `S`-neighbours `s_{j-1}` and `s_j` (claw-freeness). -/
theorem eq_of_adj_y (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (D : TetherLadder L S ℓ) {j : ℕ} (hj : 1 ≤ j) (hjℓ : j ≤ ℓ) {z : V} (hz : z ∈ S)
    (hadj : G.Adj z (D.y j)) : z = D.x (j - 1) ∨ z = D.x j := by
  have hne : D.x (j - 1) ≠ D.x j := fun h => by
    have := (D.x_eq_iff (by omega) hjℓ).1 h
    omega
  exact eq_or_eq_of_three_nbrs hclaw hS (v := D.y j) (Finset.mem_coe.2 (D.x_mem _ (by omega)))
    (Finset.mem_coe.2 (D.x_mem _ hjℓ)) (Finset.mem_coe.2 hz) (D.adj_prev j hj hjℓ).symm
    (D.adj_self j hj hjℓ).symm hadj.symm hne

/-- The shared `b`-vertices of a ladder are pairwise distinct. -/
theorem y_inj (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V)) (D : TetherLadder L S ℓ)
    {j j' : ℕ} (hj : 1 ≤ j) (hjℓ : j ≤ ℓ) (hj' : 1 ≤ j') (hj'ℓ : j' ≤ ℓ)
    (h : D.y j = D.y j') : j = j' := by
  have h1 := D.eq_of_adj_y hclaw hS hj hjℓ (D.x_mem j' hj'ℓ)
    (by rw [h]; exact D.adj_self j' hj' hj'ℓ)
  have h2 := D.eq_of_adj_y hclaw hS hj' hj'ℓ (D.x_mem j hjℓ)
    (by rw [← h]; exact D.adj_self j hj hjℓ)
  rw [D.x_eq_iff hj'ℓ (by omega), D.x_eq_iff hj'ℓ hjℓ] at h1
  rw [D.x_eq_iff hjℓ (by omega), D.x_eq_iff hjℓ hj'ℓ] at h2
  omega

end TetherLadder

/-- **The dual path of a ladder.**  Let `T` be a dual of `L` and `D` a ladder
`s₀, …, s_ℓ = t` of `L` (`ℓ ≥ 1`) along an independent set `S`.  Then `t = s_ℓ, s_{ℓ-1}, …, s_1`
is a deformation path of `T` along `S`: `s_{ℓ-m}` is a clone of the vertex `y_{ℓ-m}` (an
`a`-vertex of `T`), the replaced vertices being `y_ℓ, y_{ℓ-1}, …, y_1`.

The proof checks the hypotheses of `exists_deformsAlongAt_of_conditions` for `T`, using only
adjacencies: `y_j` is adjacent to exactly the `S`-vertices `s_{j-1}, s_j`. -/
theorem exists_dualPath_of_ladder [DecidableEq V] (hclaw : G.IsClawFree)
    {L T : G.EvenHoleLabeling k} (hLT : L.IsDualTo T) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) {ℓ : ℕ} (hℓ : 0 < ℓ) (D : TetherLadder L S ℓ) :
    ∃ Q : T.SetDeformationPath S, Q.len = ℓ ∧
      ∀ (m : ℕ) (hm : m < Q.len),
        Q.s ⟨m, hm⟩ = D.x (ℓ - m) ∧ T.a (Q.idx ⟨m, hm⟩) = D.y (ℓ - m) := by
  classical
  have hex : ∀ j : ℕ, ∃ r : Fin k, 1 ≤ j → j ≤ ℓ → T.a r = D.y j := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ ℓ
    · have hmem : D.y j ∈ Set.range T.a := hLT.1 ▸ D.y_mem j hj.1 hj.2
      obtain ⟨r, hr⟩ := hmem
      exact ⟨r, fun _ _ => hr⟩
    · exact ⟨⟨0, by have := T.two_le; omega⟩, fun h1 h2 => (hj ⟨h1, h2⟩).elim⟩
  choose ρ hρ using hex
  have hρa : ∀ m : Fin ℓ, T.a (ρ (ℓ - m)) = D.y (ℓ - m) := fun m =>
    hρ (ℓ - m) (by omega) (by omega)
  have hu_inj : Function.Injective (fun m : Fin ℓ => D.x (ℓ - m)) := by
    intro m m' h
    have := (D.x_eq_iff (by omega) (by omega)).1 h
    exact Fin.ext (by omega)
  have hr_inj : Function.Injective (fun m : Fin ℓ => ρ (ℓ - m)) := by
    intro m m' h
    have h1 : D.y (ℓ - m) = D.y (ℓ - m') := by
      rw [← hρa m, ← hρa m']
      exact congrArg T.a h
    have := D.y_inj hclaw hS (by omega) (by omega) (by omega) (by omega) h1
    exact Fin.ext (by omega)
  have hxS : ∀ m : Fin ℓ, D.x (ℓ - m) ∈ (↑S : Set V) := fun m =>
    Finset.mem_coe.2 (D.x_mem _ (by omega))
  obtain ⟨final, hrun⟩ := exists_deformsAlongAt_of_conditions (S := (↑S : Set V)) hS
    (List.ofFn fun m : Fin ℓ => (D.x (ℓ - m), ρ (ℓ - m))) T
    (by
      intro p hp
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      exact hxS m)
    (by simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.2 hu_inj)
    (by simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.2 hr_inj)
    (by
      intro p hp
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      rw [hLT.carrier_eq]
      exact D.x_not_mem _ (by omega))
    (by
      intro p hp q
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      show G.Adj (D.x (ℓ - m)) (T.b q) ↔ G.Adj (T.a (ρ (ℓ - m))) (T.b q)
      rw [hρa m]
      exact D.adj_a_iff _ (by omega) (by omega) _ (hLT.2 ▸ ⟨q, rfl⟩))
    (by
      intro p hp
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      show G.Adj (D.x (ℓ - m)) (T.a (ρ (ℓ - m)))
      rw [hρa m]
      exact D.adj_self _ (by omega) (by omega))
    (by
      intro p hp q hadj
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      have hadj' : G.Adj (D.x (ℓ - m)) (T.a q) := hadj
      have hqb : T.a q ∈ Set.range L.b := hLT.1 ▸ ⟨q, rfl⟩
      rcases D.adj_b_imp _ (by omega) (by omega) _ hqb hadj' with h | ⟨hlt, h⟩
      · have : q = ρ (ℓ - m) := T.a_injective (h.trans (hρa m).symm)
        exact List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨m, rfl⟩, this.symm⟩
      · have hm1 : 1 ≤ (m : ℕ) := by omega
        have h' : T.a q = T.a (ρ (ℓ - (m - 1))) := by
          rw [hρ (ℓ - (m - 1)) (by omega) (by omega), h]
          congr 1
          omega
        have : q = ρ (ℓ - (m - 1)) := T.a_injective h'
        exact List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨⟨m - 1, by omega⟩, rfl⟩, this.symm⟩)
    (by
      rw [List.pairwise_ofFn]
      intro m m' hmm' hadj
      have hadj' : G.Adj (D.x (ℓ - m)) (T.a (ρ (ℓ - m'))) := hadj
      rw [hρa m'] at hadj'
      have h := D.eq_of_adj_y hclaw hS (j := ℓ - m') (by omega) (by omega)
        (D.x_mem _ (by omega)) hadj'
      rw [D.x_eq_iff (by omega) (by omega), D.x_eq_iff (by omega) (by omega)] at h
      omega)
  refine ⟨{ len := ℓ, len_pos := hℓ, s := fun m => D.x (ℓ - m), idx := fun m => ρ (ℓ - m),
            s_mem := fun m => D.x_mem _ (by omega), s_injective := hu_inj,
            idx_injective := hr_inj, final := final, run := hrun, link := ?_ },
    rfl, fun m hm => by
      have hm' : m < ℓ := hm
      exact ⟨rfl, hρ (ℓ - m) (by omega) (by omega)⟩⟩
  intro j j' hjj'
  show G.Adj (D.x (ℓ - j')) (T.a (ρ (ℓ - j)))
  rw [hρa j]
  have := D.adj_prev (ℓ - j) (by omega) (by omega)
  have e : ℓ - j - 1 = ℓ - j' := by omega
  rwa [e] at this

end Ladder

/-! ### The ladder of a tethered deformation path -/

namespace SetDeformationPath

section FromPath

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The clone data of the `j`-th step of a deformation path: `s_j` is a clone of `a_{i_j}` in a
hole with the `b`-vertices and the successor map of `L`, and with the `a`-vertices of `L` at all
indices that are not replaced before step `j`. -/
theorem exists_stepClone_data (P : L.SetDeformationPath S) (j : Fin P.len) :
    ∃ M : G.EvenHoleLabeling k, M.CloneAt (P.s j) (P.idx j) ∧ (∀ q, M.b q = L.b q) ∧
      (∀ q, M.next q = L.next q) ∧
      ∀ q, (∀ m : Fin P.len, m.val < j.val → P.idx m ≠ q) → M.a q = L.a q := by
  obtain ⟨M, hM, hb, hn, ha⟩ := P.run.exists_clone_getElem j.val (by simp)
  refine ⟨M, by simpa using hM, hb, hn, fun q hq => ha q fun m hm => ?_⟩
  have hmj : m < P.len := lt_trans hm j.isLt
  simpa using hq ⟨m, hmj⟩ hm

/-- The first step of a deformation path is a clone of the starting hole. -/
theorem cloneAt_first_step (P : L.SetDeformationPath S) :
    L.CloneAt (P.s P.first) (P.idx P.first) := by
  obtain ⟨M, hM, hb, hn, ha⟩ := P.exists_stepClone_data P.first
  have hMa : ∀ q, M.a q = L.a q := fun q => ha q fun m hm => by simp [first] at hm
  have hcar : M.carrier = L.carrier := by
    unfold carrier
    have : M.a = L.a := funext hMa
    have h2 : M.b = L.b := funext hb
    rw [this, h2]
  refine ⟨hcar ▸ hM.outside, fun v hv => ?_⟩
  rw [← hcar] at hv
  have := hM.adj_iff v hv
  rwa [hMa] at this

/-- A deforming vertex lies outside the hole. -/
theorem s_not_mem_label_carrier [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (j : Fin P.len) : P.s j ∉ L.carrier := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · exact P.s_not_mem_image_a hS j (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
  · obtain ⟨M, hM, hb, -⟩ := P.exists_stepClone_data j
    exact hM.ne_b_vertex q (hq.symm.trans (hb q).symm)

/-- The `b`-neighbours of `s_j` are those of `a_{i_j}`: `b_{i_j}` and `b_{next i_j}`. -/
theorem adj_s_b_iff (P : L.SetDeformationPath S) (j : Fin P.len) (q : Fin k) :
    G.Adj (P.s j) (L.b q) ↔ q = P.idx j ∨ q = L.next (P.idx j) := by
  obtain ⟨M, hM, hb, hn, -⟩ := P.exists_stepClone_data j
  have h1 : G.Adj (P.s j) (L.b q) ↔ G.Adj (P.s j) (M.b q) := by rw [hb]
  rw [h1, hM.adj_iff _ (M.b_mem_carrier q), M.adj_ab_iff, hn]
  constructor
  · rintro (h | h)
    · exact (M.color_disjoint _ _ h.symm).elim
    · exact h
  · exact Or.inr

/-- The `a`-neighbours of `s_j` are `a_{i_j}` and, for `j ≥ 1`, `a_{i_{j-1}}`. -/
theorem adj_s_a_iff_all (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (j : Fin P.len) (q : Fin k) :
    G.Adj (P.s j) (L.a q) ↔
      q = P.idx j ∨ ∃ j' : Fin P.len, j'.val + 1 = j.val ∧ q = P.idx j' := by
  by_cases hq : ∃ m, P.idx m = q
  · obtain ⟨m, rfl⟩ := hq
    rw [P.adj_s_a_iff hclaw hS j m]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [Fin.ext h])
      · exact Or.inr ⟨m, h.symm, rfl⟩
    · rintro (h | ⟨j', hj', h⟩)
      · have := P.idx_injective h
        exact Or.inl (by rw [this])
      · have := P.idx_injective h
        subst this
        exact Or.inr hj'.symm
  · push Not at hq
    obtain ⟨M, hM, hb, hn, ha⟩ := P.exists_stepClone_data j
    have hMa : M.a q = L.a q := ha q fun m _ => hq m
    have hiff := hM.adj_iff (M.a q) (M.a_mem_carrier q)
    rw [hMa] at hiff
    constructor
    · intro hadj
      exfalso
      rcases hiff.1 hadj with h | h
      · exact hq j (M.a_injective (hMa.trans h)).symm
      · exact M.adj_aa (P.idx j) q (by rw [hMa]; exact h)
    · rintro (h | ⟨j', _, h⟩)
      · exact (hq j h.symm).elim
      · exact (hq j' h.symm).elim

/-- **A tethered deformation path has a ladder** (v1 L762-764, Fig. `deformationsequence`).

Let `P = s₀ - a_{i₀} - s₁ - ⋯ - s_{ℓ-1} - a_{i_{ℓ-1}}` be a deformation path of `L` along the
independent set `S` of a claw-free graph, tethered to `t`.  Then the vertices
`s₀, …, s_{ℓ-1}, s_ℓ = t` form a `TetherLadder`: `s_{j-1}` and `s_j` have a common `b`-neighbour
`y_j` (claw-freeness at `a_{i_{j-1}}`, whose neighbours are `b_{i_{j-1}}`, `b_{next i_{j-1}}`,
`s_{j-1}`, `s_j`), and `s_j` has the same `a`-neighbours as `y_j`, namely `a_{i_{j-1}}, a_{i_j}`
(for `j = ℓ`: those of the tether's clone vertex).  The case analysis of v1 Lemma 3
(`CloneAt.lemma8`) is not repeated: it is used only through the run `P`, whose steps are clones
(`exists_stepClone_data`). -/
theorem ladder_of_tetheredTo [DecidableEq V] (hclaw : G.IsClawFree)
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) {t : V} (ht : P.TetheredTo t) :
    ∃ D : TetherLadder L S P.len,
      (∀ j (h : j < P.len), D.x j = P.s ⟨j, h⟩) ∧ D.x P.len = t := by
  obtain ⟨htS, htP, hadj, r, hr⟩ := ht
  have hℓ := P.len_pos
  -- the tether is a clone of `b_r`
  have htC : t ∉ L.carrier := by
    have := hr.outside
    rwa [swapColors_carrier] at this
  have htb : ∀ q, G.Adj t (L.b q) ↔ q = r := by
    intro q
    have := hr.adj_iff (L.b q) (by rw [swapColors_carrier]; exact L.b_mem_carrier q)
    rw [swapColors_a] at this
    rw [this]
    constructor
    · rintro (h | h)
      · exact L.b_injective h
      · exact (L.adj_bb r q h).elim
    · rintro rfl
      exact Or.inl rfl
  have hta : ∀ p, G.Adj t (L.a p) ↔ G.Adj (L.b r) (L.a p) := by
    intro p
    have := hr.adj_iff (L.a p) (by rw [swapColors_carrier]; exact L.a_mem_carrier p)
    rw [swapColors_a] at this
    rw [this]
    constructor
    · rintro (h | h)
      · exact (L.color_disjoint p r h).elim
      · exact h
    · exact Or.inr
  -- the sequences `x_j = s_j` (`j < ℓ`), `x_ℓ = t`, and `α_j = i_j`
  obtain ⟨x, hx, hxt⟩ : ∃ x : ℕ → V, (∀ j (h : j < P.len), x j = P.s ⟨j, h⟩) ∧ x P.len = t :=
    ⟨fun j => if h : j < P.len then P.s ⟨j, h⟩ else t, fun j h => by simp [h], by simp⟩
  obtain ⟨α, hα⟩ : ∃ α : ℕ → Fin k, ∀ j (h : j < P.len), α j = P.idx ⟨j, h⟩ :=
    ⟨fun j => if h : j < P.len then P.idx ⟨j, h⟩ else P.idx P.first, fun j h => by simp [h]⟩
  have hxS : ∀ j, j ≤ P.len → x j ∈ S := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with h | h
    · rw [hx j h]
      exact P.s_mem _
    · rw [h, hxt]
      exact htS
  have hxinj : ∀ j j', j ≤ P.len → j' ≤ P.len → x j = x j' → j = j' := by
    intro j j' hj hj' h
    rcases Nat.lt_or_eq_of_le hj with h1 | h1 <;> rcases Nat.lt_or_eq_of_le hj' with h2 | h2
    · rw [hx j h1, hx j' h2] at h
      exact congrArg Fin.val (P.s_injective h)
    · exfalso
      rw [hx j h1, h2, hxt] at h
      exact htP ⟨_, h⟩
    · exfalso
      rw [hx j' h2, h1, hxt] at h
      exact htP ⟨_, h.symm⟩
    · omega
  have hxC : ∀ j, j ≤ P.len → x j ∉ L.carrier := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with h | h
    · rw [hx j h]
      exact P.s_not_mem_label_carrier hS _
    · rw [h, hxt]
      exact htC
  have hb : ∀ j (h : j < P.len) q, G.Adj (x j) (L.b q) ↔ q = α j ∨ q = L.next (α j) := by
    intro j h q
    rw [hx j h, hα j h]
    exact P.adj_s_b_iff _ q
  have ha : ∀ j (h : j < P.len) q,
      G.Adj (x j) (L.a q) ↔ q = α j ∨ (1 ≤ j ∧ q = α (j - 1)) := by
    intro j h q
    rw [hx j h, P.adj_s_a_iff_all hclaw hS ⟨j, h⟩ q, hα j h]
    constructor
    · rintro (h1 | ⟨j', hj', h1⟩)
      · exact Or.inl h1
      · have e : j' = ⟨j - 1, by have := j'.isLt; omega⟩ :=
          Fin.ext (by simp only at hj' ⊢; omega)
        rw [e] at h1
        exact Or.inr ⟨by simp only at hj'; omega, by rw [hα (j - 1) (by omega)]; exact h1⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl h1
      · refine Or.inr ⟨⟨j - 1, by omega⟩, by simp only; omega, ?_⟩
        rw [hα (j - 1) (by omega)] at h2
        exact h2
  have hlink : ∀ j, 1 ≤ j → j ≤ P.len → G.Adj (x j) (L.a (α (j - 1))) := by
    intro j hj1 hj2
    rcases Nat.lt_or_eq_of_le hj2 with h | h
    · rw [hx j h, hα (j - 1) (by omega)]
      exact P.link ⟨j - 1, by omega⟩ ⟨j, h⟩ (by simp only; omega)
    · rw [h, hxt, hα (P.len - 1) (by omega)]
      exact hadj
  -- consecutive vertices share a `b`-vertex
  have hchain : ∀ j, 1 ≤ j → j ≤ P.len →
      ∃ β : Fin k, G.Adj (x (j - 1)) (L.b β) ∧ G.Adj (x j) (L.b β) := by
    intro j hj1 hj2
    have hj' : j - 1 < P.len := by omega
    have hxj := hxC j hj2
    rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors (j := x j) (k := L.a (α (j - 1)))
        (u := L.b (α (j - 1))) (v := L.b (L.next (α (j - 1)))) (hlink j hj1 hj2)
        (L.adj_a_b _) (L.adj_a_b_next _) (fun e => hxj (e ▸ L.b_mem_carrier _))
        (fun e => hxj (e ▸ L.b_mem_carrier _)) (L.b_ne_next _).symm (L.adj_bb _ _) with h | h
    · exact ⟨α (j - 1), (hb (j - 1) hj' _).2 (Or.inl rfl), h⟩
    · exact ⟨L.next (α (j - 1)), (hb (j - 1) hj' _).2 (Or.inr rfl), h⟩
  have hy : ∀ j : ℕ, ∃ w : V, 1 ≤ j → j ≤ P.len →
      ∃ β : Fin k, w = L.b β ∧ G.Adj (x (j - 1)) w ∧ G.Adj (x j) w := by
    intro j
    by_cases h : 1 ≤ j ∧ j ≤ P.len
    · obtain ⟨β, h1, h2⟩ := hchain j h.1 h.2
      exact ⟨L.b β, fun _ _ => ⟨β, rfl, h1, h2⟩⟩
    · exact ⟨x 0, fun h1 h2 => (h ⟨h1, h2⟩).elim⟩
  choose y hy using hy
  have hyb : ∀ j, 1 ≤ j → j ≤ P.len → ∃ β : Fin k, y j = L.b β := by
    intro j h1 h2
    obtain ⟨β, h, -⟩ := hy j h1 h2
    exact ⟨β, h⟩
  have hyp : ∀ j, 1 ≤ j → j ≤ P.len → G.Adj (x (j - 1)) (y j) := by
    intro j h1 h2
    obtain ⟨β, -, h, -⟩ := hy j h1 h2
    exact h
  have hys : ∀ j, 1 ≤ j → j ≤ P.len → G.Adj (x j) (y j) := by
    intro j h1 h2
    obtain ⟨β, -, -, h⟩ := hy j h1 h2
    exact h
  have hyne : ∀ j, 1 ≤ j → j < P.len → y j ≠ y (j + 1) := by
    intro j hj1 hj2 e
    have h1 : G.Adj (x (j + 1)) (y j) := by
      rw [e]
      exact hys (j + 1) (by omega) hj2
    have hz := eq_or_eq_of_three_nbrs hclaw (S := (↑S : Set V)) hS (v := y j) (x := x (j - 1))
      (y := x j) (z := x (j + 1)) (Finset.mem_coe.2 (hxS _ (by omega)))
      (Finset.mem_coe.2 (hxS _ (by omega))) (Finset.mem_coe.2 (hxS _ (by omega)))
      (hyp j hj1 (by omega)).symm (hys j hj1 (by omega)).symm h1.symm
      (fun e' => by have := hxinj _ _ (by omega) (by omega) e'; omega)
    rcases hz with hz | hz
    · have := hxinj _ _ (by omega) (by omega) hz
      omega
    · have := hxinj _ _ (by omega) (by omega) hz
      omega
  refine ⟨{ x := x, y := y, x_mem := hxS, x_inj := hxinj, x_not_mem := hxC, y_mem := ?_,
            adj_prev := hyp, adj_self := hys, adj_a_iff := ?_, adj_b_imp := ?_ },
    hx, hxt⟩
  · intro j h1 h2
    obtain ⟨β, hβ⟩ := hyb j h1 h2
    exact ⟨β, hβ.symm⟩
  · intro j hj1 hj2 w hw
    obtain ⟨p, rfl⟩ := hw
    obtain ⟨β, hβ⟩ := hyb j hj1 hj2
    rcases Nat.lt_or_eq_of_le hj2 with hlt | heq
    · rw [ha j hlt p, hβ]
      have h0 : β = α (j - 1) ∨ β = L.next (α (j - 1)) :=
        (hb (j - 1) (by omega) β).1 (hβ ▸ hyp j hj1 hj2)
      have h1 : β = α j ∨ β = L.next (α j) := (hb j hlt β).1 (hβ ▸ hys j hj1 hj2)
      have hne : α j ≠ α (j - 1) := by
        rw [hα j hlt, hα (j - 1) (by omega)]
        intro e
        have := congrArg Fin.val (P.idx_injective e)
        simp only at this
        omega
      rw [L.adj_b_iff_of_mem (L.a_mem_carrier p), L.a_injective.eq_iff, L.a_injective.eq_iff]
      simp only [hj1, true_and]
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · exact (hne (h1.symm.trans h0)).elim
      · have : L.prev β = α j := by rw [h1, L.prev_next]
        rw [this, h0]
        tauto
      · have : L.prev β = α (j - 1) := by rw [h0, L.prev_next]
        rw [this, h1]
      · have := congrArg L.prev (h1.symm.trans h0)
        rw [L.prev_next, L.prev_next] at this
        exact (hne this).elim
    · subst heq
      rw [hxt, hta p, hβ]
      have hβr : β = r := (htb β).1 (by
        rw [← hβ]
        have := hys _ hj1 le_rfl
        rwa [hxt] at this)
      rw [hβr]
  · intro j hj1 hj2 w hw hadjw
    obtain ⟨q, rfl⟩ := hw
    obtain ⟨β, hβ⟩ := hyb j hj1 hj2
    rcases Nat.lt_or_eq_of_le hj2 with hlt | heq
    · obtain ⟨β', hβ'⟩ := hyb (j + 1) (by omega) hlt
      have hq := (hb j hlt q).1 hadjw
      have h1 : β = α j ∨ β = L.next (α j) := (hb j hlt β).1 (hβ ▸ hys j hj1 hj2)
      have h1' : β' = α j ∨ β' = L.next (α j) := by
        refine (hb j hlt β').1 (hβ' ▸ ?_)
        have := hyp (j + 1) (by omega) hlt
        simpa using this
      have hββ' : β ≠ β' := fun e => hyne j hj1 hlt (by rw [hβ, hβ', e])
      rw [hβ, hβ']
      simp only [L.b_injective.eq_iff, hlt, true_and]
      rcases hq with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h1' with rfl | rfl <;>
        first
        | exact absurd rfl hββ'
        | simp
    · subst heq
      rw [hxt] at hadjw
      left
      have hqr := (htb q).1 hadjw
      have hβr : β = r := (htb β).1 (by
        rw [← hβ]
        have := hys _ hj1 le_rfl
        rwa [hxt] at this)
      rw [hβ, hβr, hqr]

end FromPath

section Tether

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- **The reverse run of a tethered path.**  Let `P = s₀ - a_{i₀} - ⋯ - s_{ℓ-1} - a_{i_{ℓ-1}}` be a
deformation path of `L` along the independent set `S` of a claw-free graph, tethered to
`t = s_ℓ`, and let `T` be a dual of `L` (`L.swapColors`, or `L` seen from `L.swapColors`).  Then
there is a deformation path `Q` of `T` along `S` with `ℓ` steps which starts at `t`, passes through
`s_{ℓ-1}, …, s_1` in reverse order and is tethered to `s₀`.  At step `m` it replaces the vertex
`y_{ℓ-m}` of the `b`-class, the one shared by `s_{ℓ-m-1}` and `s_{ℓ-m}`
(v1 L763: "we could similarly deform `C` along `P'`"). -/
theorem exists_reverse_path [DecidableEq V] (hclaw : G.IsClawFree) {T : G.EvenHoleLabeling k}
    (hLT : L.IsDualTo T) (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) {t : V}
    (ht : P.TetheredTo t) :
    ∃ Q : T.SetDeformationPath S, Q.len = P.len ∧ Q.s ⟨0, Q.len_pos⟩ = t ∧
      (∀ (m : ℕ) (hm : m < Q.len) (hmP : m < P.len) (h1 : 1 ≤ m),
        Q.s ⟨m, hm⟩ = P.s ⟨P.len - m, by omega⟩) ∧
      Q.TetheredTo (P.s ⟨0, P.len_pos⟩) := by
  obtain ⟨D, hDx, hDℓ⟩ := P.ladder_of_tetheredTo hclaw hS ht
  have hD0 : D.x 0 = P.s ⟨0, P.len_pos⟩ := hDx 0 P.len_pos
  obtain ⟨Q, hlen, hQ⟩ := exists_dualPath_of_ladder hclaw hLT hS P.len_pos D
  refine ⟨Q, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (hQ 0 Q.len_pos).1
    rw [Nat.sub_zero, hDℓ] at this
    exact this
  · intro m hm hmP h1
    rw [(hQ m hm).1, hDx _ (by omega)]
  · exact P.s_mem _
  · rintro ⟨m, hm⟩
    have h1 := (hQ m.val m.isLt).1
    rw [← hD0] at hm
    have : D.x (P.len - m.val) = D.x 0 := by
      rw [← h1]
      exact hm
    have := D.x_inj _ _ (by omega) (by omega) this
    have := m.isLt
    omega
  · have h2 := (hQ (Q.len - 1) (by have := Q.len_pos; omega)).2
    have e : P.len - (Q.len - 1) = 1 := by
      have := Q.len_pos
      omega
    rw [e] at h2
    show G.Adj (P.s ⟨0, P.len_pos⟩) (T.a (Q.idx ⟨Q.len - 1, _⟩))
    rw [h2, ← hD0]
    exact D.adj_prev 1 le_rfl P.len_pos
  · exact CloneAt.exists_swapColors_cloneAt_of_isDual hLT P.cloneAt_first_step

/-- **The tether relation, for any dual hole.**  Let `P` be a deformation path of `L` along the
independent set `S` of a claw-free graph, tethered to `t`, and let `T` be a dual of `L`
(`L.swapColors`, or `L` seen from `L.swapColors`).  Then

* `t ≠ s₀`, and `t` lies in `A(C,S)`, the set of vertices of `S` anticommuting with `h_C`
  (it has three neighbours in `C`);
* the `b`-class run of `T` starting at `t` is a deformation path `Q` of `T` along `S` which is
  tethered to `s₀` (`exists_reverse_path`): it replaces `y_ℓ, y_{ℓ-1}, …, y_1` by
  `t = s_ℓ, s_{ℓ-1}, …, s_1` and stops at `s₀`, which has only two neighbours left in the hole.

See `tetheredTo_symm`. -/
theorem tetheredTo_dual [DecidableEq V] (hclaw : G.IsClawFree) {T : G.EvenHoleLabeling k}
    (hLT : L.IsDualTo T) (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) {t : V}
    (ht : P.TetheredTo t) :
    t ≠ P.s ⟨0, P.len_pos⟩ ∧ t ∈ G.anticommutingVertices L.carrier S ∧
      ∃ Q : T.SetDeformationPath S, Q.s ⟨0, Q.len_pos⟩ = t ∧
        Q.TetheredTo (P.s ⟨0, P.len_pos⟩) := by
  refine ⟨fun h => ht.2.1 ⟨⟨0, P.len_pos⟩, h.symm⟩, ?_, ?_⟩
  · refine mem_anticommutingVertices.2 ⟨ht.1, ?_⟩
    obtain ⟨r, hr⟩ := ht.2.2.2
    have h3 := hr.adjacencyCount_eq_three
    rw [swapColors_carrier] at h3
    unfold AnticommutesWithSet
    rw [h3]
  · obtain ⟨Q, -, hQ0, -, hQt⟩ := exists_reverse_path hclaw hLT hS P ht
    exact ⟨Q, hQ0, hQt⟩

/-- **Symmetry of the tether relation** (v1 L762-764: "Letting `P'` be the path component of
`G[S ⊕ C_b]` with `s_ℓ` as an endpoint, we could similarly deform `C` along `P'` until we reach
the vertex `s₀`, so `s₀` and `s_ℓ` can be uniquely associated this way").

If the deformation path `P` of `L` along `S` initialised by `s₀` is tethered to `t`, then

* `t ≠ s₀` and `t ∈ A(C,S)`;
* `t` initialises a deformation path `Q` of the colour-swapped hole `L.swapColors` along `S`
  (the `b`-class run) which is tethered back to `s₀`.

Here `Q.TetheredTo s₀` means that `s₀` is a clone of an `a`-vertex of
`L.swapColors.swapColors`; this labelling has the same carrier as `L` and its `a`-indices are
those of `L` shifted by `prev`, so the statement is up to that reindexing (the carrier-level
lemma `CloneAt.exists_swapColors_cloneAt_of_isDual` does the translation).

Neither the hypothesis `_hL` (full cyclic order) nor `[Fintype V]` is used. -/
theorem tetheredTo_symm [DecidableEq V] (hclaw : G.IsClawFree) (_hL : L.HasFullCyclicOrder)
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) {t : V} (ht : P.TetheredTo t) :
    t ≠ P.s ⟨0, P.len_pos⟩ ∧ t ∈ G.anticommutingVertices L.carrier S ∧
      ∃ Q : L.swapColors.SetDeformationPath S, Q.s ⟨0, Q.len_pos⟩ = t ∧
        Q.TetheredTo (P.s ⟨0, P.len_pos⟩) :=
  tetheredTo_dual hclaw (isDualTo_swapColors L) hS P ht

end Tether

/-! #### Uniqueness of the tether -/

section Unique

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The tether of a deformation path is unique: the last replaced vertex `a_{i_{ℓ-1}}` has at
most two neighbours in `S` (claw-freeness), namely `s_{ℓ-1}` and the tether. -/
theorem TetheredTo.unique (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    {P : L.SetDeformationPath S} {t t' : V} (ht : P.TetheredTo t) (ht' : P.TetheredTo t') :
    t = t' := by
  obtain ⟨htS, htP, hadj, -⟩ := ht
  obtain ⟨htS', htP', hadj', -⟩ := ht'
  exact eq_of_three_nbrs_of_indep (S := (↑S : Set V)) hclaw hS (v := L.a (P.idx P.last))
    (x := P.s P.last) (y := t) (z := t') (Finset.mem_coe.2 (P.s_mem _)) (Finset.mem_coe.2 htS)
    (Finset.mem_coe.2 htS') (P.adj_a_idx _).symm hadj.symm hadj'.symm
    (fun e => htP ⟨P.last, e⟩) (fun e => htP' ⟨P.last, e⟩)

/-- Two deformation paths with the same list of vertex-index pairs have the same tethers. -/
theorem tetheredTo_of_pairs_eq {P Q : L.SetDeformationPath S} (heq : P.pairs = Q.pairs) {t : V}
    (ht : Q.TetheredTo t) : P.TetheredTo t := by
  obtain ⟨htS, htQ, hadj, hr⟩ := ht
  have hlen : P.len = Q.len := by simpa using congrArg List.length heq
  have hpre : P.pairs <+: Q.pairs := ⟨[], by rw [List.append_nil, heq]⟩
  refine ⟨htS, ?_, ?_, hr⟩
  · rintro ⟨j, hj⟩
    refine htQ ⟨⟨j.val, by have := j.isLt; omega⟩, ?_⟩
    rw [← hj]
    exact (agree_of_prefix hpre j.isLt (by have := j.isLt; omega)).1.symm
  · have := (agree_of_prefix hpre (j := P.len - 1) (by have := P.len_pos; omega)
      (by have := P.len_pos; omega)).2
    have e : P.idx P.last = Q.idx Q.last := by
      refine this.trans ?_
      congr 1
      exact Fin.ext (by simp only [last]; omega)
    rw [e]
    exact hadj

/-- Two maximal deformation paths initialised by the same vertex have the same tether. -/
theorem TetheredTo.unique_of_start [DecidableEq V] (hclaw : G.IsClawFree)
    (hL : L.HasFullCyclicOrder) (hS : G.IsIndepSet (S : Set V)) {P Q : L.SetDeformationPath S} {t t' : V}
    (ht : P.TetheredTo t) (ht' : Q.TetheredTo t') (h0 : P.s P.first = Q.s Q.first) : t = t' :=
  TetheredTo.unique hclaw hS ht
    (tetheredTo_of_pairs_eq (pairs_eq_of_start hclaw hL hS P Q (Or.inr ⟨t, ht⟩)
      (Or.inr ⟨t', ht'⟩) h0) ht')

/-- The initialising vertex of a deformation path lies in `A(C,S)`: it is a clone, hence has
three neighbours in `C`. -/
theorem s_first_mem_anticommutingVertices (P : L.SetDeformationPath S) :
    P.s P.first ∈ G.anticommutingVertices L.carrier S := by
  refine mem_anticommutingVertices.2 ⟨P.s_mem _, ?_⟩
  unfold AnticommutesWithSet
  rw [P.cloneAt_first_step.adjacencyCount_eq_three]

end Unique

end SetDeformationPath

/-! ### The tether involution and the parity argument -/

section Parity

variable {k : ℕ}

/-- `TetherPair L S s t`: the vertex `s` initialises a deformation path along `S` of `L`, or of
the colour-swapped hole `L.swapColors`, which is tethered to `t` (v1 L763: "`s₀` is tethered to
`s_ℓ`"). -/
def TetherPair (L : G.EvenHoleLabeling k) (S : Finset V) (s t : V) : Prop :=
  (∃ P : L.SetDeformationPath S, P.s P.first = s ∧ P.TetheredTo t) ∨
    (∃ P : L.swapColors.SetDeformationPath S, P.s P.first = s ∧ P.TetheredTo t)

variable [DecidableEq V] {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The tether of an initialising vertex lies in `A(C,S)`, differs from it, and is itself
tethered back to it (`SetDeformationPath.tetheredTo_symm`, for both colour classes). -/
theorem TetherPair.symm (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V)) {s t : V}
    (h : TetherPair L S s t) :
    t ∈ G.anticommutingVertices L.carrier S ∧ t ≠ s ∧ TetherPair L S t s := by
  rcases h with ⟨P, hP0, ht⟩ | ⟨P, hP0, ht⟩
  · obtain ⟨hne, hmem, Q, hQ0, hQt⟩ :=
      SetDeformationPath.tetheredTo_dual hclaw (isDualTo_swapColors L) hS P ht
    exact ⟨hmem, hP0 ▸ hne, Or.inr ⟨Q, hQ0, hP0 ▸ hQt⟩⟩
  · obtain ⟨hne, hmem, Q, hQ0, hQt⟩ :=
      SetDeformationPath.tetheredTo_dual hclaw (isDualTo_swapColors L).symm hS P ht
    refine ⟨by rwa [swapColors_carrier] at hmem, hP0 ▸ hne, Or.inl ⟨Q, hQ0, hP0 ▸ hQt⟩⟩

omit [DecidableEq V] in
/-- The initialising vertex of a tether pair lies in `A(C,S)`. -/
theorem TetherPair.left_mem {s t : V} (h : TetherPair L S s t) :
    s ∈ G.anticommutingVertices L.carrier S := by
  rcases h with ⟨P, hP0, -⟩ | ⟨P, hP0, -⟩
  · exact hP0 ▸ P.s_first_mem_anticommutingVertices
  · have := P.s_first_mem_anticommutingVertices
    rw [swapColors_carrier] at this
    exact hP0 ▸ this

/-- The initialising vertex determines its tether. -/
theorem TetherPair.unique (hclaw : G.IsClawFree) (hL : L.HasFullCyclicOrder)
    (hS : G.IsIndepSet (S : Set V)) {s t t' : V} (h : TetherPair L S s t)
    (h' : TetherPair L S s t') : t = t' := by
  rcases h with ⟨P, hP0, ht⟩ | ⟨P, hP0, ht⟩ <;> rcases h' with ⟨Q, hQ0, ht'⟩ | ⟨Q, hQ0, ht'⟩
  · exact SetDeformationPath.TetheredTo.unique_of_start hclaw hL hS ht ht' (hP0.trans hQ0.symm)
  · exact (P.cloneAt_first_step.not_swapColors_cloneAt
      (hP0 ▸ hQ0 ▸ Q.cloneAt_first_step : L.swapColors.CloneAt (P.s P.first) _)).elim
  · exact (Q.cloneAt_first_step.not_swapColors_cloneAt
      (hQ0 ▸ hP0 ▸ P.cloneAt_first_step : L.swapColors.CloneAt (Q.s Q.first) _)).elim
  · exact SetDeformationPath.TetheredTo.unique_of_start hclaw hL.swapColors hS ht ht'
      (hP0.trans hQ0.symm)

/-- Tethering is an involution: the tether of the tether of `s` is `s`. -/
theorem TetherPair.involutive (hclaw : G.IsClawFree) (hL : L.HasFullCyclicOrder)
    (hS : G.IsIndepSet (S : Set V)) {s t u : V} (h : TetherPair L S s t)
    (h' : TetherPair L S t u) : u = s :=
  TetherPair.unique hclaw hL hS h' (TetherPair.symm hclaw hS h).2.2

/-- **An untethered run exists when `|A(C,S)|` is odd** (v1 proof of Theorem 1(ii), L906-910:
"There is at least one (and an odd number in general) vertex `s₀` in `S` such that `h_{s₀}` and
`h_C` anticommute, ..., each such vertex initializes a deformation path, but may be tethered.
If every such initializing vertex is tethered, then they can be uniquely paired, which
contradicts the assumption that `h_S` and `h_C` anticommute.  Thus, there is at least one
untethered path").

Let `L` be a labelling of an even hole `C` with full cyclic order in a claw-free graph and `S`
an independent set such that the number of vertices of `S` with an odd number of neighbours in
`C` (the set `A(C,S)`, `SimpleGraph.anticommutingVertices`) is odd.  Then some vertex of `A(C,S)`
initialises an untethered deformation path, along the `a`-class of `L` (a clone of some `a_i`) or
along the `a`-class of the colour-swapped hole `L.swapColors` (a clone of some `b_i`).

Proof: each `s ∈ A(C,S)` is a clone of an `a`-vertex of `L` or of `L.swapColors`
(`cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet`) and so initialises a maximal path
(`CloneAt.exists_setDeformationPath`).  If all of them were tethered, `s ↦ tether(s)` would be a
fixed-point-free involution of `A(C,S)` (`TetherPair.symm`, `TetherPair.unique`), so `|A(C,S)|`
would be even. -/
theorem exists_untethered_of_odd (hclaw : G.IsClawFree) (hL : L.HasFullCyclicOrder)
    (hS : G.IsIndepSet (S : Set V)) (hodd : Odd (G.anticommutingVertices L.carrier S).card) :
    (∃ P : L.SetDeformationPath S, P.Untethered) ∨
      ∃ P : L.swapColors.SetDeformationPath S, P.Untethered := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hno1, hno2⟩ := hcon
  have hpartner : ∀ s, s ∈ G.anticommutingVertices L.carrier S → ∃ t, TetherPair L S s t := by
    intro s hs
    obtain ⟨hsS, hanti⟩ := mem_anticommutingVertices.1 hs
    obtain ⟨-, hclone⟩ := L.cloneAt_or_swapColors_cloneAt_of_anticommutesWithSet hL hclaw hanti
    rcases hclone with ⟨i, hi⟩ | ⟨i, hi⟩
    · obtain ⟨P, hP0, -, hP, -⟩ := CloneAt.exists_setDeformationPath hclaw hL hS hsS hi
      rcases hP with hU | ⟨t, ht⟩
      · exact (hno1 ⟨P, hU⟩).elim
      · exact ⟨t, Or.inl ⟨P, hP0, ht⟩⟩
    · obtain ⟨P, hP0, -, hP, -⟩ :=
        CloneAt.exists_setDeformationPath hclaw hL.swapColors hS hsS hi
      rcases hP with hU | ⟨t, ht⟩
      · exact (hno2 ⟨P, hU⟩).elim
      · exact ⟨t, Or.inr ⟨P, hP0, ht⟩⟩
  choose τ hτ using hpartner
  have hsum : ∑ s ∈ G.anticommutingVertices L.carrier S, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun s hs => τ s hs) (fun s hs => by decide) ?_
      (fun s hs => (TetherPair.symm hclaw hS (hτ s hs)).1) ?_
    · intro s hs _
      exact (TetherPair.symm hclaw hS (hτ s hs)).2.1
    · intro s hs
      exact TetherPair.involutive hclaw hL hS (hτ s hs)
        (hτ _ (TetherPair.symm hclaw hS (hτ s hs)).1)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact Nat.not_even_iff_odd.2 hodd (ZMod.natCast_eq_zero_iff_even.1 hsum)

end Parity

end EvenHoleLabeling

end SimpleGraph
