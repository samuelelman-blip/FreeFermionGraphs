import FreeFermionGraphs.T3Interaction

/-!
# Interaction is symmetric inside a palindromic deformation

This module proves that the interaction relation `FPDeformation.Interacts` of
`FreeFermionGraphs.T3Interaction` is symmetric on the blocks of a *palindromic* fixed-pairing
deformation (arXiv 2305.15625 v1, Definition 19 `definition:fixedpairingtypedeformation`,
L978-994).  The statement is new: v1 does not state it.  It is an ingredient of the pairing
involution that v1 needs but does not argue at L1237-1241 (proof of Theorem 1(iii): the
fixed-pairing-type deformation chosen for `(C, C')` must be chosen again, reversed, for
`(C̃, C̃')`).  It lets the blocks of a valid deformation split into groups that do not interact
(used for toggle stability).

## Main results

* `FPDeformation.interacts_symm`: let `D` be palindromic and `P`, `Q` blocks of `D`.  Then
  `Interacts P Q → Interacts Q P`.  Hence `FPDeformation.interacts_comm`, `Interacts P Q ↔
  Interacts Q P`.
* `FPDeformation.Palindromic.stepConds_inr`: the side-2 version of
  `Palindromic.stepConds_inl` (the clone conditions of a side-2 block against the first class at
  the time of the block, in the forward and in the backward run), by `swapSides`.
* `FPDeformation.interacts_swap_iff`: `Interacts` is invariant under `SideBlock.swap`.

## Proof

Same-side blocks never interact unless they coincide (`not_interacts_inl_inl`,
`not_interacts_inr_inr`).  For a side-1 block `P` and a side-2 block `Q` of `D`, let `(j, k)` be a
step of `P` witnessing `Interacts P Q`.

* *Shared vertex.*  If `j ∈ supp Q` then `j` is the removed vertex of a step of `Q` (`j ∈ C'_c`,
  and `C'_c` is disjoint from `C'_d`), and if `k ∈ supp Q` then `k` is the introduced vertex of a
  step of `Q`; in both cases the step of `Q` has a vertex in `supp P`.
* *Separator.*  Let `v ∈ supp Q ∖ {j, k}` be adjacent to exactly one of `j`, `k`.  By the
  direction lemma (`FPDeformation.direction`), `Q` runs before `P` if `v ∈ C_b` (so `v = k'` is the
  removed vertex of a step `(j', k')` of `Q`), and after `P` if `v ∈ C'_d` (so `v = j'`).
  * `Q` before `P`.  The forward clone condition of `Q` (first class `C_a ⊕ T₁(pre)`, which still
    contains `k ∈ supp P`) gives `j' ~ k ↔ k' ~ k`.  At the time of `P` the vertex `j'` has been
    toggled into the second class, so the forward clone condition of `P` gives `j ~ j' ↔ k ~ j'`.
    Hence `j ~ j' ↔ v ~ k`; as `v` separates `(j, k)`, the vertex `j` separates `(j', k')`.
  * `Q` after `P`.  The backward clone condition of `Q` (first class `C'_c ⊕ T₁(post)`, which
    still contains `j`) gives `k' ~ j ↔ j' ~ j`.  At the time of `P` the vertex `k'` is still in
    the second class, so the forward clone condition of `P` gives `j ~ k' ↔ k ~ k'`.  Hence
    `k ~ k' ↔ v ~ j`; as `v` separates `(j, k)`, the vertex `k` separates `(j', k')`.

Only the forward step conditions of `P` are used; the backward step conditions of `P` are not
needed (in the first sub-case `j'` has been toggled into the second class by the time of `P`, and
in the second sub-case `k'` has not yet been toggled out of it, so the forward condition of `P`
applies to both).  The side-2 / side-1 case is the same statement for `D.swapSides`
(`FreeFermionGraphs.T3FixedPairingSymm`).

Claw-freeness is not used anywhere in this module.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-! ### Interaction and the side swap -/

/-- Interaction is invariant under exchanging the two sides of both blocks (the word and the
support of a side block do not change under `SideBlock.swap`). -/
theorem interacts_swap_iff (P Q : G.SideBlock s s') :
    Interacts P.swap Q.swap ↔ Interacts P Q := by
  simp [Interacts]

/-! ### Step conditions of a side-2 block -/

/-- **Step conditions at the time of a side-2 block.**  The side-2 version of
`Palindromic.stepConds_inl`: for a palindromic `D` whose blocks are cut as `pre ++ inr Q :: post`,
every step `(j, k)` of `Q` satisfies

* `j ∉ A` and `Γ_A(j) = Γ_A(k)` for `A = s.1 ⊕ T₁(pre)` (forward run), and
* `k ∉ A'` and `Γ_{A'}(k) = Γ_{A'}(j)` for `A' = s'.1 ⊕ T₁(post)` (backward run).

It is `Palindromic.stepConds_inl` for `D.swapSides`. -/
theorem Palindromic.stepConds_inr {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) {pre post : List (G.SideBlock s s')}
    {Q : G.OddBlock s.2 s'.2} (hdec : D.blocks = pre ++ Sum.inr Q :: post) :
    (∀ p ∈ Q.word, p.1 ∉ symmDiff s.1 (SideBlock.listToggle₁ pre) ∧
        ∀ v ∈ symmDiff s.1 (SideBlock.listToggle₁ pre), (G.Adj p.1 v ↔ G.Adj p.2 v)) ∧
      (∀ p ∈ Q.word, p.2 ∉ symmDiff s'.1 (SideBlock.listToggle₁ post) ∧
        ∀ v ∈ symmDiff s'.1 (SideBlock.listToggle₁ post), (G.Adj p.2 v ↔ G.Adj p.1 v)) := by
  have hdec' : D.swapSides.blocks =
      pre.map SideBlock.swap ++ (Sum.inl Q : G.SideBlock s.swap s'.swap) ::
        post.map SideBlock.swap := by
    rw [blocks_swapSides, hdec, List.map_append, List.map_cons]
    rfl
  obtain ⟨hF, hR⟩ := Palindromic.stepConds_inl hs.swap hs'.swap
    ((palindromic_swapSides_iff D).2 hD) hdec'
  rw [SideBlock.listToggle₂_map_swap] at hF hR
  exact ⟨hF, hR⟩

/-! ### Cutting a list at two positions -/

/-- A list cut at two positions `i < j`. -/
theorem exists_split_of_lt {α : Type*} (l : List α) {i j : Fin l.length} (h : i < j) :
    ∃ pre mid post : List α, l = pre ++ l.get i :: (mid ++ l.get j :: post) := by
  have hdec : l = l.take i ++ l.get i :: l.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i l]
    rw [List.drop_eq_getElem_cons i.isLt]
    rfl
  have hmem : l.get j ∈ l.drop (i + 1) := by
    have hj : (j : ℕ) - (i + 1) < (l.drop (i + 1)).length := by
      rw [List.length_drop]
      have := j.isLt
      have : (i : ℕ) < j := h
      omega
    have : (l.drop (i + 1))[(j : ℕ) - (i + 1)] = l.get j := by
      rw [List.getElem_drop]
      simp only [List.get_eq_getElem]
      congr 1
      have : (i : ℕ) < j := h
      omega
    rw [← this]
    exact List.getElem_mem hj
  obtain ⟨mid, post, hmp⟩ := List.append_of_mem hmem
  refine ⟨l.take i, mid, post, ?_⟩
  rw [← hmp]
  exact hdec

/-- The supports of a list cut at two positions: the later block is not in the prefix, the earlier
block is not in the suffix, and the prefix up to the earlier block has distinct supports. -/
theorem nodup_split₂ {pre mid post : List (G.SideBlock s s')} {X Y : G.SideBlock s s'}
    (h : ((pre ++ X :: (mid ++ Y :: post)).map SideBlock.support).Nodup) :
    ((pre ++ X :: mid).map SideBlock.support).Nodup ∧ Y.support ∉ pre.map SideBlock.support ∧
      X.support ∉ post.map SideBlock.support := by
  have e : pre ++ X :: (mid ++ Y :: post) = (pre ++ X :: mid) ++ Y :: post := by simp
  rw [e, List.map_append, List.nodup_append] at h
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨h1, fun hmem => ?_, fun hmem => ?_⟩
  · exact h3 Y.support (by rw [List.map_append]; exact List.mem_append_left _ hmem) Y.support
      (List.mem_map.2 ⟨Y, List.mem_cons_self .., rfl⟩) rfl
  · exact h3 X.support (List.mem_map.2 ⟨X, by simp, rfl⟩) X.support
      (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hmem) rfl

/-! ### The two cores of the symmetry -/

/-- **Core, the separating block runs first.**  Let `D` be palindromic with blocks cut as
`pre ++ inr Q :: (mid ++ inl P :: post)`, so that the side-2 block `Q` runs before the side-1 block
`P`.  If a vertex `v ∈ supp Q ∩ C_b` separates a step `(j, k)` of `P` (`v ≠ j`, adjacent to exactly
one of `j`, `k`), then `j` separates a step of `Q`: `Interacts Q P`.  (Here `v = k'` is the removed
vertex of a step `(j', k')` of `Q`; the forward clone conditions of `Q` and of `P` give
`j ~ j' ↔ v ~ k`.) -/
theorem interacts_symm_core_fwd (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {pre mid post : List (G.SideBlock s s')}
    {P : G.OddBlock s.1 s'.1} {Q : G.OddBlock s.2 s'.2}
    (hdec : D.blocks = pre ++ Sum.inr Q :: (mid ++ Sum.inl P :: post)) {p : V × V}
    (hp : p ∈ P.word) {v : V} (hvQ : v ∈ Q.support) (hv : v ∈ s.2) (hv1 : v ≠ p.1)
    (hne : ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) :
    Interacts (Sum.inr Q : G.SideBlock s s') (Sum.inl P) := by
  have hnd := D.nodup
  rw [hdec] at hnd
  obtain ⟨hndpre, hYpre, -⟩ := nodup_split₂ hnd
  -- `v` is the removed vertex of a step of `Q`
  obtain ⟨q, hq, hvq⟩ := OddBlock.mem_support_iff_exists_mem_word.1 hvQ
  have hq1 : q.1 ∈ s'.2 \ s.2 := OddBlock.fst_mem hq
  have hvq2 : v = q.2 := by
    rcases hvq with h | h
    · exact absurd (h ▸ hv) (Finset.mem_sdiff.1 hq1).2
    · exact h
  subst hvq2
  have hp1 : p.1 ∈ s'.1 \ s.1 := OddBlock.fst_mem hp
  have hp2 : p.2 ∈ s.1 \ s'.1 := OddBlock.snd_mem hp
  -- the step conditions of `Q` and of `P` at their times
  obtain ⟨hFQ, -⟩ := Palindromic.stepConds_inr hs hs' hD hdec
  have hdecP : D.blocks = (pre ++ Sum.inr Q :: mid) ++ Sum.inl P :: post := by
    rw [hdec]; simp
  obtain ⟨hFP, -⟩ := Palindromic.stepConds_inl hs hs' hD hdecP
  -- `k = p.2` is still in the first class when `Q` runs
  have hkA : p.2 ∈ symmDiff s.1 (SideBlock.listToggle₁ pre) := by
    refine Finset.mem_symmDiff.2 (Or.inl ⟨(Finset.mem_sdiff.1 hp2).1, ?_⟩)
    exact Finset.disjoint_left.1 (SideBlock.disjoint_listToggle₁ P pre hYpre)
      (OddBlock.snd_mem_support hp)
  -- `j' = q.1` has been toggled into the second class when `P` runs
  have hj'B : q.1 ∈ symmDiff s.2 (SideBlock.listToggle₂ (pre ++ Sum.inr Q :: mid)) := by
    refine Finset.mem_symmDiff.2 (Or.inr ⟨?_, (Finset.mem_sdiff.1 hq1).2⟩)
    exact (SideBlock.mem_listToggle₂ hndpre).2 ⟨Q, by simp, OddBlock.fst_mem_support hq⟩
  have h1 := ((hFQ q hq).2 p.2 hkA)
  have h2 := ((hFP p hp).2 q.1 hj'B)
  refine ⟨q, hq, Or.inr (Or.inr ⟨p.1, OddBlock.fst_mem_support hp, ?_, hv1.symm, ?_⟩)⟩
  · intro h
    exact Finset.disjoint_left.1 hs'.disjoint (Finset.mem_sdiff.1 hp1).1
      (h ▸ (Finset.mem_sdiff.1 hq1).1)
  · intro h
    apply hne
    rw [G.adj_comm q.1 p.1, G.adj_comm q.2 p.1] at h
    rw [G.adj_comm q.1 p.2] at h1
    rw [G.adj_comm p.2 q.1] at h2
    tauto

/-- **Core, the separating block runs last.**  Let `D` be palindromic with blocks cut as
`pre ++ inl P :: (mid ++ inr Q :: post)`, so that the side-1 block `P` runs before the side-2 block
`Q`.  If a vertex `v ∈ supp Q ∩ C'_d` separates a step `(j, k)` of `P` (`v ≠ k`, adjacent to exactly
one of `j`, `k`), then `k` separates a step of `Q`: `Interacts Q P`.  (Here `v = j'` is the
introduced vertex of a step `(j', k')` of `Q`; the backward clone condition of `Q` and the forward
clone condition of `P` give `k ~ k' ↔ v ~ j`.) -/
theorem interacts_symm_core_bwd (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {pre mid post : List (G.SideBlock s s')}
    {P : G.OddBlock s.1 s'.1} {Q : G.OddBlock s.2 s'.2}
    (hdec : D.blocks = pre ++ Sum.inl P :: (mid ++ Sum.inr Q :: post)) {p : V × V}
    (hp : p ∈ P.word) {v : V} (hvQ : v ∈ Q.support) (hv : v ∈ s'.2) (hv2 : v ≠ p.2)
    (hne : ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) :
    Interacts (Sum.inr Q : G.SideBlock s s') (Sum.inl P) := by
  have hnd := D.nodup
  rw [hdec] at hnd
  obtain ⟨-, hYpre, hXpost⟩ := nodup_split₂ hnd
  -- `v` is the introduced vertex of a step of `Q`
  obtain ⟨q, hq, hvq⟩ := OddBlock.mem_support_iff_exists_mem_word.1 hvQ
  have hq2 : q.2 ∈ s.2 \ s'.2 := OddBlock.snd_mem hq
  have hvq1 : v = q.1 := by
    rcases hvq with h | h
    · exact h
    · exact absurd (h ▸ hv) (Finset.mem_sdiff.1 hq2).2
  subst hvq1
  have hp2 : p.2 ∈ s.1 \ s'.1 := OddBlock.snd_mem hp
  have hp1 : p.1 ∈ s'.1 \ s.1 := OddBlock.fst_mem hp
  -- the step conditions of `P` and of `Q` at their times
  obtain ⟨hFP, -⟩ := Palindromic.stepConds_inl hs hs' hD hdec
  have hdecQ : D.blocks = (pre ++ Sum.inl P :: mid) ++ Sum.inr Q :: post := by
    rw [hdec]; simp
  obtain ⟨-, hRQ⟩ := Palindromic.stepConds_inr hs hs' hD hdecQ
  -- `j = p.1` is still in the first class of the backward run when `Q` runs backwards
  have hjA : p.1 ∈ symmDiff s'.1 (SideBlock.listToggle₁ post) := by
    refine Finset.mem_symmDiff.2 (Or.inl ⟨(Finset.mem_sdiff.1 hp1).1, ?_⟩)
    exact Finset.disjoint_left.1 (SideBlock.disjoint_listToggle₁ P post hXpost)
      (OddBlock.fst_mem_support hp)
  -- `k' = q.2` is still in the second class when `P` runs forwards
  have hk'B : q.2 ∈ symmDiff s.2 (SideBlock.listToggle₂ pre) := by
    refine Finset.mem_symmDiff.2 (Or.inl ⟨(Finset.mem_sdiff.1 hq2).1, ?_⟩)
    exact Finset.disjoint_left.1 (SideBlock.disjoint_listToggle₂ Q pre hYpre)
      (OddBlock.snd_mem_support hq)
  have h1 := ((hRQ q hq).2 p.1 hjA)
  have h2 := ((hFP p hp).2 q.2 hk'B)
  refine ⟨q, hq, Or.inr (Or.inr ⟨p.2, OddBlock.snd_mem_support hp, hv2.symm, ?_, ?_⟩)⟩
  · intro h
    exact Finset.disjoint_left.1 hs.disjoint (Finset.mem_sdiff.1 hp2).1
      (h ▸ (Finset.mem_sdiff.1 hq2).1)
  · intro h
    apply hne
    rw [G.adj_comm q.2 p.1] at h1
    rw [G.adj_comm q.1 p.2, G.adj_comm q.2 p.2] at h
    rw [G.adj_comm p.1 q.2] at h2
    rw [G.adj_comm p.2 q.1] at h
    tauto

/-! ### Symmetry of interaction -/

/-- A side-1 block and a side-2 block of a palindromic deformation: interaction of the side-1
block with the side-2 block implies interaction of the side-2 block with the side-1 block. -/
theorem interacts_symm_inl_inr (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {P : G.OddBlock s.1 s'.1}
    {Q : G.OddBlock s.2 s'.2} (hP : (Sum.inl P : G.SideBlock s s') ∈ D.blocks)
    (hQ : (Sum.inr Q : G.SideBlock s s') ∈ D.blocks)
    (h : Interacts (Sum.inl P : G.SideBlock s s') (Sum.inr Q)) :
    Interacts (Sum.inr Q : G.SideBlock s s') (Sum.inl P) := by
  obtain ⟨p, hp, h1 | h2 | ⟨v, hv, hv1, hv2, hne⟩⟩ := h
  · -- the introduced vertex `j` of a step of `P` is the removed vertex of a step of `Q`
    obtain ⟨q, hq, hq'⟩ := OddBlock.mem_support_iff_exists_mem_word.1 h1
    have hq1 : q.1 ∈ s'.2 \ s.2 := OddBlock.fst_mem hq
    have hp1 : p.1 ∈ s'.1 \ s.1 := OddBlock.fst_mem hp
    rcases hq' with h | h
    · exact absurd (h ▸ (Finset.mem_sdiff.1 hq1).1) (Finset.disjoint_left.1 hs'.disjoint
        (Finset.mem_sdiff.1 hp1).1)
    · refine ⟨q, hq, Or.inr (Or.inl ?_)⟩
      show q.2 ∈ P.support
      rw [← h]
      exact OddBlock.fst_mem_support hp
  · -- the removed vertex `k` of a step of `P` is the introduced vertex of a step of `Q`
    obtain ⟨q, hq, hq'⟩ := OddBlock.mem_support_iff_exists_mem_word.1 h2
    have hq2 : q.2 ∈ s.2 \ s'.2 := OddBlock.snd_mem hq
    have hp2 : p.2 ∈ s.1 \ s'.1 := OddBlock.snd_mem hp
    rcases hq' with h | h
    · refine ⟨q, hq, Or.inl ?_⟩
      show q.1 ∈ P.support
      rw [← h]
      exact OddBlock.snd_mem_support hp
    · exact absurd (h ▸ (Finset.mem_sdiff.1 hq2).1) (Finset.disjoint_left.1 hs.disjoint
        (Finset.mem_sdiff.1 hp2).1)
  · -- a separator `v` of the step `p`
    obtain ⟨r, hr⟩ := List.mem_iff_get.1 hP
    obtain ⟨q, hq⟩ := List.mem_iff_get.1 hQ
    have hvmem : v ∈ s.2 ∪ s'.2 := by
      have := OddBlock.support_subset_symmDiff Q hv
      rcases Finset.mem_symmDiff.1 this with ⟨h, -⟩ | ⟨h, -⟩
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
    obtain ⟨hnot, q', Q', hq', hvQ', hlt1, hlt2⟩ :=
      direction hs hs' D hD hr hp hvmem (Or.inl ⟨hv1, hv2, hne⟩)
    have hqq : q' = q := eq_of_mem_support_inr D hq' hq hvQ' hv
    subst hqq
    by_cases hvs : v ∈ s.2
    · obtain ⟨pre, mid, post, hdec⟩ := exists_split_of_lt D.blocks (hlt1 hvs)
      rw [hq, hr] at hdec
      exact interacts_symm_core_fwd hs hs' D hD hdec hp hv hvs hv1 hne
    · have hvs' : v ∈ s'.2 := (Finset.mem_union.1 hvmem).resolve_left hvs
      obtain ⟨pre, mid, post, hdec⟩ := exists_split_of_lt D.blocks (hlt2 hvs')
      rw [hq, hr] at hdec
      exact interacts_symm_core_bwd hs hs' D hD hdec hp hv hvs' hv2 hne

/-- **Interaction is symmetric inside a palindromic deformation** (new, not in v1; it is one
ingredient of the pairing involution that v1 leaves unargued at L1237-1241, which the
toggle-stability and `K*`-invariance packages complete).  Let `D` be a palindromic fixed-pairing
deformation and `P`, `Q` blocks of `D`.  If `P` interacts with `Q` then `Q` interacts with `P`.

* Blocks of the same side with distinct supports never interact
  (`not_interacts_inl_inl`, `not_interacts_inr_inr`), and a block of `D` is determined by its
  support (the supports of the blocks of `D` are pairwise distinct).
* For blocks of opposite sides, a shared vertex is the removed vertex of a step of one block and the
  introduced vertex of a step of the other; a separator `v` of a step of `P` forces, by the
  direction lemma (`direction`), `Q` to run before or after `P`, and the clone conditions of `P`
  and `Q` at their times show that a vertex of `P` separates a step of `Q`
  (`interacts_symm_core_fwd`, `interacts_symm_core_bwd`).
* The side-2 / side-1 case is the side-1 / side-2 case for `D.swapSides`.

Claw-freeness is not used. -/
theorem interacts_symm (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {P Q : G.SideBlock s s'}
    (hP : P ∈ D.blocks) (hQ : Q ∈ D.blocks) (h : Interacts P Q) : Interacts Q P := by
  by_cases hsupp : P.support = Q.support
  · have hPQ : P = Q := List.inj_on_of_nodup_map D.nodup hP hQ hsupp
    subst hPQ
    exact h
  · rcases P with P | P <;> rcases Q with Q | Q
    · exact absurd h (not_interacts_inl_inl hs hs' hsupp)
    · exact interacts_symm_inl_inr hs hs' D hD hP hQ h
    · -- the side-2 / side-1 case is the side-1 / side-2 case for the swapped deformation
      have hP' : (Sum.inl P : G.SideBlock s.swap s'.swap) ∈ D.swapSides.blocks :=
        List.mem_map.2 ⟨_, hP, rfl⟩
      have hQ' : (Sum.inr Q : G.SideBlock s.swap s'.swap) ∈ D.swapSides.blocks :=
        List.mem_map.2 ⟨_, hQ, rfl⟩
      have h' : Interacts (Sum.inl P : G.SideBlock s.swap s'.swap) (Sum.inr Q) :=
        (interacts_swap_iff (Sum.inr P : G.SideBlock s s') (Sum.inl Q)).2 h
      exact (interacts_swap_iff (Sum.inl Q : G.SideBlock s s') (Sum.inr P)).1
        (interacts_symm_inl_inr hs.swap hs'.swap D.swapSides
          ((palindromic_swapSides_iff D).2 hD) hP' hQ' h')
    · exact absurd h (not_interacts_inr_inr hs hs' hsupp)

/-- **Interaction is symmetric inside a palindromic deformation**, as an equivalence. -/
theorem interacts_comm (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {P Q : G.SideBlock s s'}
    (hP : P ∈ D.blocks) (hQ : Q ∈ D.blocks) : Interacts P Q ↔ Interacts Q P :=
  ⟨interacts_symm hs hs' D hD hP hQ, interacts_symm hs hs' D hD hQ hP⟩

end FPDeformation

end SimpleGraph
