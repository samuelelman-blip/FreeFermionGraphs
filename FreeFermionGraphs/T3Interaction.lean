import FreeFermionGraphs.T3BlockStep
import FreeFermionGraphs.T3FixedPairingSymm

/-!
# The interaction relation and the direction lemma

This module formalises, for the fixed-pairing-type deformations `SimpleGraph.FPDeformation s s'`
of `FreeFermionGraphs.T3FixedPairing` (arXiv 2305.15625 v1, Definition 19
`definition:fixedpairingtypedeformation`, L978-994), the relation "the block `P` depends on the
block `Q`" and the fact that, in a *palindromic* deformation, such a dependence between blocks
of opposite sides is oriented by the order of the blocks.

v1 uses this orientation only implicitly.  A vertex is *dependent* on a single-vertex deformation
`s ≺_L a` when it is adjacent to exactly one of `s`, `a` (v1 L706).  The dependent subsets
`U^{(r,s)} = Γ_{C'}(j_{s-1}^{(r)}) ∖ Γ_{C'}[k_{s-1}^{(r)}]` of Definition 20
`definition:anticommutingdependentsubsets` (L996-1011) collect the vertices of the second hole
which depend on the step `j_{s-1}^{(r)} ≺_{C^{(r,s-1)}} k_{s-1}^{(r)}` of the `r`-th path, and the
base case (i) of the proof of Theorem 1(iii) (L1814-1829, with Corollary 8
`corollary:vertextwopathcomponents`, L1053-1064) argues that such a vertex lies in a path
component of the *other* side graph, which has to be an earlier or a later path of the
deformation.  The "after" half is v1's `U^{(r,s)}`; the "before" half and the exclusion of the
vertices shared by both classes (`C_b ∩ C'_d`) are implicit in v1's arguments.

## Main definitions and results

* `FPDeformation.Interacts P Q` (for two side blocks `P`, `Q` of `G.SideBlock s s'`): some step
  `(j, k)` of `P` has `j ∈ supp Q`, or `k ∈ supp Q`, or a vertex `v ∈ supp Q ∖ {j, k}` adjacent to
  exactly one of `j`, `k`: the ways in which a vertex of `Q` can obstruct, or be dependent on, a
  clone step `j ≺ k` of `P`.
* `OddBlock.step_not_interacts_of_support_ne` and `FPDeformation.not_interacts_inl_inl`,
  `not_interacts_inr_inr`: **distinct blocks of the same side never interact.**  Their supports are
  distinct components of one side graph `G[C_a ⊕ C'_c]` (or `G[C_b ⊕ C'_d]`), hence disjoint and
  not adjacent (a component is closed under adjacency inside the side graph, and the support of
  the other block lies in the side graph).
* `FPDeformation.Palindromic.split_runs`: for a palindromic `D` cut as `pre ++ B :: post`, the block
  `B` runs from `(s.1 ⊕ T₁(pre), s.2 ⊕ T₂(pre))` and its reverse runs from
  `(s'.1 ⊕ T₁(post), s'.2 ⊕ T₂(post))` (`T_i(·)` is the side-`i` toggle of a list of blocks).
* `FPDeformation.Palindromic.stepConds_inl`: for a palindromic `D` with a side-1 block `P` in
  position `pre ++ [P] ++ post` the step conditions of the forward block lemma
  (`OddBlock.classRun_iff`) hold against the second class `s.2 ⊕ T₂(pre)` and those of the backward
  block lemma (`OddBlock.runsBack_iff`) against `s'.2 ⊕ T₂(post)`, where `T₂(·)` is the side-2
  toggle of a list of blocks.  This is the "state at the time of the block" bookkeeping.
* `FPDeformation.direction` (**Direction lemma**): let `D` be palindromic, `P = D.blocks[r]` a
  side-1 block, `(j, k)` a step of `P`, and `v ∈ s.2 ∪ s'.2` a vertex which separates `(j, k)`
  (`v ∉ {j, k}` and `v` adjacent to exactly one of `j`, `k`) or is the introduced vertex `j ∈ s.2`
  or the removed vertex `k ∈ s'.2`.  Then `v ∉ s.2 ∩ s'.2`, `v` lies in a side-2 block
  `D.blocks[q]`, and `q < r` if `v ∈ s.2` while `r < q` if `v ∈ s'.2`.  Intuitively: when the
  `r`-th block runs forward, no vertex of the current second class separates a step or sits on an
  introduced vertex; so such a vertex of `s.2` must already have been toggled out of the second
  class by an earlier side-2 block.  Symmetrically, on the backward run, such a vertex of `s'.2`
  must be toggled out of the second class of `s'` by a later block.  The proof applies the forward
  and backward block step lemmas of `FreeFermionGraphs.T3BlockStep` at the time of the block and
  uses the toggle bookkeeping of `FreeFermionGraphs.T3FixedPairing`.
* `FPDeformation.direction₂`: the side-2 version, obtained from `direction` by `swapSides`
  (`FreeFermionGraphs.T3FixedPairingSymm`).
* `FPDeformation.eq_of_mem_support_inr`, `eq_of_mem_support_inl` (small corollaries): a vertex lies
  in at most one block of each side, so the position `q` in `direction` is determined by `v`
  (distinct blocks of one side graph have disjoint supports, and the supports of the blocks of `D`
  are pairwise distinct).

Claw-freeness is not used anywhere in this module.  The hypotheses `hs`, `hs'` of
`not_interacts_inl_inl` and `not_interacts_inr_inr` are not needed for the proof
(`OddBlock.step_not_interacts_of_support_ne` is unconditional); they are kept so that these
statements have the signature recorded in the work package.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

/-- **Distinct blocks of one side graph do not interact, stepwise.**  If `P` and `Q` are blocks of
`G[X ⊕ Y]` with distinct supports (so distinct components), then no step `(j, k)` of `P` has its
vertices in `supp Q` or a vertex of `supp Q` adjacent to `j` or to `k`: the supports are disjoint,
and a component of `G[X ⊕ Y]` is closed under adjacency inside `X ⊕ Y ⊇ supp Q`
(v1 Corollaries 6-7, L1041-1049, read for components of one side graph). -/
theorem step_not_interacts_of_support_ne (P Q : G.OddBlock X Y) (h : P.support ≠ Q.support)
    {p : V × V} (hp : p ∈ P.word) :
    p.1 ∉ Q.support ∧ p.2 ∉ Q.support ∧ ∀ v ∈ Q.support, ¬ G.Adj p.1 v ∧ ¬ G.Adj p.2 v := by
  have hd := disjoint_of_support_ne P Q h
  refine ⟨Finset.disjoint_left.1 hd (fst_mem_support hp),
    Finset.disjoint_left.1 hd (snd_mem_support hp), fun v hv => ?_⟩
  have hvs : v ∈ (↑(symmDiff X Y) : Set V) := Finset.mem_coe.2 (Q.support_subset_symmDiff hv)
  constructor
  · intro hadj
    have := P.isInducedComponent_support.2.2 (Finset.mem_coe.2 (fst_mem_support hp)) hvs hadj
    exact Finset.disjoint_left.1 hd (Finset.mem_coe.1 this) hv
  · intro hadj
    have := P.isInducedComponent_support.2.2 (Finset.mem_coe.2 (snd_mem_support hp)) hvs hadj
    exact Finset.disjoint_left.1 hd (Finset.mem_coe.1 this) hv

end OddBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-! ### The interaction relation -/

/-- **Interaction** of two side blocks (v1 Definition 20 and L734: the vertices of the second hole
on which the clone steps of `P` depend).  `P` interacts with `Q` when some step `(j, k)` of `P`
has `j ∈ supp Q`, or `k ∈ supp Q`, or a vertex `v ∈ supp Q` different from `j` and `k` which is
adjacent to exactly one of `j`, `k` (so that `v` is a separator of the step `(j, k)`). -/
def Interacts (P Q : G.SideBlock s s') : Prop :=
  ∃ p ∈ P.word, p.1 ∈ Q.support ∨ p.2 ∈ Q.support ∨
    ∃ v ∈ Q.support, v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)

/-- **Distinct blocks of the side graph `G[C_a ⊕ C'_c]` never interact.**  The hypotheses `hs`,
`hs'` are not used (`OddBlock.step_not_interacts_of_support_ne`). -/
theorem not_interacts_inl_inl (_hs : G.IsHoleClasses s) (_hs' : G.IsHoleClasses s')
    {P Q : G.OddBlock s.1 s'.1} (h : P.support ≠ Q.support) :
    ¬ Interacts (Sum.inl P : G.SideBlock s s') (Sum.inl Q : G.SideBlock s s') := by
  rintro ⟨p, hp, h1 | h2 | ⟨v, hv, -, -, hne⟩⟩
  · exact (OddBlock.step_not_interacts_of_support_ne P Q h hp).1 h1
  · exact (OddBlock.step_not_interacts_of_support_ne P Q h hp).2.1 h2
  · obtain ⟨n1, n2⟩ := (OddBlock.step_not_interacts_of_support_ne P Q h hp).2.2 v hv
    exact hne ⟨fun a => absurd a n1, fun a => absurd a n2⟩

/-- **Distinct blocks of the side graph `G[C_b ⊕ C'_d]` never interact.** -/
theorem not_interacts_inr_inr (_hs : G.IsHoleClasses s) (_hs' : G.IsHoleClasses s')
    {P Q : G.OddBlock s.2 s'.2} (h : P.support ≠ Q.support) :
    ¬ Interacts (Sum.inr P : G.SideBlock s s') (Sum.inr Q : G.SideBlock s s') := by
  rintro ⟨p, hp, h1 | h2 | ⟨v, hv, -, -, hne⟩⟩
  · exact (OddBlock.step_not_interacts_of_support_ne P Q h hp).1 h1
  · exact (OddBlock.step_not_interacts_of_support_ne P Q h hp).2.1 h2
  · obtain ⟨n1, n2⟩ := (OddBlock.step_not_interacts_of_support_ne P Q h hp).2.2 v hv
    exact hne ⟨fun a => absurd a n1, fun a => absurd a n2⟩

/-! ### Cutting a deformation at a block -/

section Split

/-- If the supports of `pre ++ B :: post` are pairwise distinct, so are those of `pre` and `post`,
and the support of `B` is not the support of a block in `pre` or `post`. -/
theorem nodup_split {pre post : List (G.SideBlock s s')} {B : G.SideBlock s s'}
    (h : ((pre ++ B :: post).map SideBlock.support).Nodup) :
    (pre.map SideBlock.support).Nodup ∧ (post.map SideBlock.support).Nodup ∧
      B.support ∉ pre.map SideBlock.support ∧ B.support ∉ post.map SideBlock.support := by
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at h
  obtain ⟨hpre, ⟨hB, hpost⟩, hcross⟩ := h
  refine ⟨hpre, hpost, fun hmem => ?_, hB⟩
  exact hcross _ hmem _ (List.mem_cons_self ..) rfl

/-- The word of a deformation cut at a block. -/
theorem word_of_blocks_eq {D : G.FPDeformation s s'} {pre post : List (G.SideBlock s s')}
    {B : G.SideBlock s s'} (hdec : D.blocks = pre ++ B :: post) :
    D.word = pre.flatMap SideBlock.word ++ (B.word ++ post.flatMap SideBlock.word) := by
  simp [word, hdec, List.flatMap_append]

/-- **The states at the time of a block.**  Let `D` be palindromic and cut its list of blocks as
`pre ++ B :: post`.  Then the block `B` can be run from the state `(s.1 ⊕ T₁(pre), s.2 ⊕ T₂(pre))`
(where `T_i(·)` is the side-`i` toggle of a list of blocks), and the reversed block can be run from
`(s'.1 ⊕ T₁(post), s'.2 ⊕ T₂(post))`; both are hole-class states.

This is the toggle bookkeeping `SideBlock.eq_of_classRun_flatMap` applied to the prefix of the
forward run and to the (mirrored) suffix of the backward run. -/
theorem Palindromic.split_runs {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) {pre post : List (G.SideBlock s s')}
    {B : G.SideBlock s s'} (hdec : D.blocks = pre ++ B :: post) :
    G.IsHoleClasses (symmDiff s.1 (SideBlock.listToggle₁ pre),
        symmDiff s.2 (SideBlock.listToggle₂ pre)) ∧
      G.IsHoleClasses (symmDiff s'.1 (SideBlock.listToggle₁ post),
        symmDiff s'.2 (SideBlock.listToggle₂ post)) ∧
      (∃ t, G.ClassRun (symmDiff s.1 (SideBlock.listToggle₁ pre),
        symmDiff s.2 (SideBlock.listToggle₂ pre)) B.word t) ∧
      (∃ t, G.ClassRun (symmDiff s'.1 (SideBlock.listToggle₁ post),
        symmDiff s'.2 (SideBlock.listToggle₂ post)) (reverseWord B.word) t) := by
  obtain ⟨⟨sf, hf⟩, ⟨s'f, hb⟩⟩ := hD
  have hnd := D.nodup
  rw [hdec] at hnd
  obtain ⟨hndpre, hndpost, -, -⟩ := nodup_split hnd
  have hword := word_of_blocks_eq hdec
  -- forward: the prefix
  rw [hword] at hf
  obtain ⟨t₁, hpre, hrest⟩ := ClassRun.exists_of_append hf
  obtain ⟨t₂, hB, -⟩ := ClassRun.exists_of_append hrest
  obtain ⟨ht₁, -, -⟩ := SideBlock.eq_of_classRun_flatMap pre hndpre hs
    (fun _ _ hv => hv) (fun _ _ hv => hv) hpre
  -- backward: the mirrored suffix
  have hword' : reverseWord D.word =
      (SideBlock.mirrorList post).flatMap SideBlock.word ++
        (reverseWord B.word ++ reverseWord (pre.flatMap SideBlock.word)) := by
    rw [hword, reverseWord_append, reverseWord_append, SideBlock.flatMap_word_mirrorList,
      List.append_assoc]
  rw [hword'] at hb
  obtain ⟨t₁', hpost, hrest'⟩ := ClassRun.exists_of_append hb
  obtain ⟨t₂', hB', -⟩ := ClassRun.exists_of_append hrest'
  obtain ⟨ht₁', -, -⟩ := SideBlock.eq_of_classRun_flatMap (SideBlock.mirrorList post)
    (SideBlock.nodup_mirrorList hndpost) hs' (fun _ _ hv => hv) (fun _ _ hv => hv) hpost
  rw [SideBlock.listToggle₁_mirrorList hndpost, SideBlock.listToggle₂_mirrorList hndpost] at ht₁'
  have hcl₁ := hpre.isHoleClasses hs
  have hcl₁' := hpost.isHoleClasses hs'
  subst ht₁ ht₁'
  exact ⟨hcl₁, hcl₁', ⟨t₂, hB⟩, ⟨t₂', hB'⟩⟩

end Split

/-! ### The step conditions at the time of a side-1 block -/

/-- **Step conditions at the time of a side-1 block.**  Let `D` be palindromic, with its blocks cut
as `pre ++ inl P :: post`.  Then the forward block lemma `OddBlock.classRun_iff` applies to `P` and
the state `(s.1 ⊕ T₁(pre), s.2 ⊕ T₂(pre))`, and the backward block lemma `OddBlock.runsBack_iff`
applies to `P` and the state `(s'.1 ⊕ T₁(post), s'.2 ⊕ T₂(post))` (the supports of `P` and of the
other side-1 blocks are disjoint, so `P` is untoggled in the first classes).  Hence for every step
`(j, k)` of `P`,

* `j ∉ B` and `Γ_B(j) = Γ_B(k)` for `B = s.2 ⊕ T₂(pre)`, and
* `k ∉ B'` and `Γ_{B'}(k) = Γ_{B'}(j)` for `B' = s'.2 ⊕ T₂(post)`. -/
theorem Palindromic.stepConds_inl {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) {pre post : List (G.SideBlock s s')}
    {P : G.OddBlock s.1 s'.1} (hdec : D.blocks = pre ++ Sum.inl P :: post) :
    (∀ p ∈ P.word, p.1 ∉ symmDiff s.2 (SideBlock.listToggle₂ pre) ∧
        ∀ v ∈ symmDiff s.2 (SideBlock.listToggle₂ pre), (G.Adj p.1 v ↔ G.Adj p.2 v)) ∧
      (∀ p ∈ P.word, p.2 ∉ symmDiff s'.2 (SideBlock.listToggle₂ post) ∧
        ∀ v ∈ symmDiff s'.2 (SideBlock.listToggle₂ post), (G.Adj p.2 v ↔ G.Adj p.1 v)) := by
  obtain ⟨ht, ht', ⟨t, hrun⟩, ⟨t', hrun'⟩⟩ := hD.split_runs hs hs' hdec
  have hnd := D.nodup
  rw [hdec] at hnd
  obtain ⟨-, -, hpre, hpost⟩ := nodup_split hnd
  have hdpre : Disjoint P.support (SideBlock.listToggle₁ pre) :=
    SideBlock.disjoint_listToggle₁ P pre hpre
  have hdpost : Disjoint P.support (SideBlock.listToggle₁ post) :=
    SideBlock.disjoint_listToggle₁ P post hpost
  have hX := hs.isIndepSet_fst
  have hY := hs'.isIndepSet_fst
  have hsub₁ : SideBlock.listToggle₁ pre ⊆ symmDiff s.1 s'.1 := SideBlock.listToggle₁_subset pre
  have hsub₂ : SideBlock.listToggle₁ post ⊆ symmDiff s.1 s'.1 := SideBlock.listToggle₁_subset post
  constructor
  · have hAXY : symmDiff s.1 (SideBlock.listToggle₁ pre) ⊆ s.1 ∪ s'.1 := by
      intro v hv
      rcases Finset.mem_symmDiff.1 hv with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Finset.mem_union_left _ h1
      · rcases Finset.mem_symmDiff.1 (hsub₁ h1) with ⟨a, -⟩ | ⟨a, -⟩
        · exact absurd a h2
        · exact Finset.mem_union_right _ a
    have hPA : symmDiff s.1 (SideBlock.listToggle₁ pre) ∩ P.support = P.support ∩ s.1 := by
      have hL : ∀ v, v ∈ P.support → v ∉ SideBlock.listToggle₁ pre := fun v hv =>
        Finset.disjoint_left.1 hdpre hv
      ext v
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      have := hL v
      tauto
    exact (OddBlock.classRun_iff hX hY ht hAXY P hPA).1 ⟨t, hrun⟩
  · have hAXY : symmDiff s'.1 (SideBlock.listToggle₁ post) ⊆ s.1 ∪ s'.1 := by
      intro v hv
      rcases Finset.mem_symmDiff.1 hv with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Finset.mem_union_right _ h1
      · rcases Finset.mem_symmDiff.1 (hsub₂ h1) with ⟨a, -⟩ | ⟨a, -⟩
        · exact Finset.mem_union_left _ a
        · exact absurd a h2
    have hPA : symmDiff s'.1 (SideBlock.listToggle₁ post) ∩ P.support = P.support ∩ s'.1 := by
      have hL : ∀ v, v ∈ P.support → v ∉ SideBlock.listToggle₁ post := fun v hv =>
        Finset.disjoint_left.1 hdpost hv
      ext v
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      have := hL v
      tauto
    exact (OddBlock.runsBack_iff hX hY ht' hAXY P hPA).1 ⟨t', hrun'⟩

/-! ### The direction lemma -/

/-- A member of the first `r` entries of a list sits at an index `< r`. -/
theorem exists_fin_of_mem_take {α : Type*} {l : List α} {r : ℕ} {a : α} (h : a ∈ l.take r) :
    ∃ q : Fin l.length, q.val < r ∧ l.get q = a := by
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 h
  exact ⟨⟨j, lt_of_lt_of_le hj (min_le_right _ _)⟩, lt_of_lt_of_le hj (min_le_left _ _), rfl⟩

/-- A member of the list after the first `r + 1` entries sits at an index `> r`. -/
theorem exists_fin_of_mem_drop {α : Type*} {l : List α} {r : ℕ} {a : α}
    (h : a ∈ l.drop (r + 1)) : ∃ q : Fin l.length, r < q.val ∧ l.get q = a := by
  obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.1 h
  refine ⟨⟨r + 1 + j, by omega⟩, by simp only; omega, ?_⟩
  simp only [List.get_eq_getElem]

/-- Cutting the list of blocks at position `r`. -/
theorem blocks_eq_take_append_drop (D : G.FPDeformation s s') (r : Fin D.blocks.length) :
    D.blocks = D.blocks.take r ++ D.blocks.get r :: D.blocks.drop (r + 1) := by
  conv_lhs => rw [← List.take_append_drop r D.blocks]
  rw [List.drop_eq_getElem_cons r.isLt]
  rfl

/-- **Direction lemma** (v1 Definition 20 `U^{(r,s)}`, L996-1011; Corollary 8, L1053; base case (i),
L1814-1829).  Let `D` be a palindromic fixed-pairing deformation of `s = (C_a, C_b)` by
`s' = (C'_c, C'_d)`, let `P = D.blocks[r]` be a side-1 block (a component of `G[C_a ⊕ C'_c]`),
and let `(j, k)` be a step of `P`.  Let `v ∈ C_b ∪ C'_d` be

* a vertex separating the step (different from `j` and `k` and adjacent to exactly one of them), or
* the introduced vertex `v = j` with `v ∈ C_b`, or
* the removed vertex `v = k` with `v ∈ C'_d`.

Then `v ∉ C_b ∩ C'_d`, and `v` lies in a side-2 block `D.blocks[q]`; moreover `q < r` if
`v ∈ C_b` (the vertex was toggled out of the second class before the block `r` ran) and `r < q`
if `v ∈ C'_d` (it is toggled out of the second class of `C'` only after the block `r`, as seen
from the backward run).

The side-2 version is `direction₂`.  Only the palindromic property (the forward run of the word
from `s` and of the reversed word from `s'`) is used; the proof applies the forward and backward
block step lemmas (`Palindromic.stepConds_inl`) at the time of the block. -/
theorem direction (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (D : G.FPDeformation s s')
    (hD : D.Palindromic) {r : Fin D.blocks.length} {P : G.OddBlock s.1 s'.1}
    (hr : D.blocks.get r = Sum.inl P) {p : V × V} (hp : p ∈ P.word) {v : V}
    (hv : v ∈ s.2 ∪ s'.2)
    (hsep : (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) ∨ (v = p.1 ∧ v ∈ s.2) ∨
      (v = p.2 ∧ v ∈ s'.2)) :
    v ∉ s.2 ∩ s'.2 ∧ ∃ (q : Fin D.blocks.length) (Q : G.OddBlock s.2 s'.2),
      D.blocks.get q = Sum.inr Q ∧ v ∈ Q.support ∧ (v ∈ s.2 → q < r) ∧ (v ∈ s'.2 → r < q) := by
  have hdec := blocks_eq_take_append_drop D r
  rw [hr] at hdec
  obtain ⟨hF, hR⟩ := hD.stepConds_inl hs hs' hdec
  have hF' := hF p hp
  have hR' := hR p hp
  have hnd := D.nodup
  rw [hdec] at hnd
  obtain ⟨hndpre, hndpost, -, -⟩ := nodup_split hnd
  have hL₂ : SideBlock.listToggle₂ (D.blocks.take r) ⊆ symmDiff s.2 s'.2 :=
    SideBlock.listToggle₂_subset _
  have hd1 := hs.disjoint
  have hd2 := hs'.disjoint
  have hp1 : p.1 ∈ s'.1 \ s.1 := OddBlock.fst_mem hp
  have hp2 : p.2 ∈ s.1 \ s'.1 := OddBlock.snd_mem hp
  -- the vertex has left the second class of `s` before the block, if it started there
  have claim1 : v ∈ s.2 → v ∈ SideBlock.listToggle₂ (D.blocks.take r) := by
    intro hvs
    have hvB : v ∉ symmDiff s.2 (SideBlock.listToggle₂ (D.blocks.take r)) := by
      rcases hsep with ⟨-, -, hne⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · intro hB
        exact hne (hF'.2 v hB)
      · exact hF'.1
      · exact absurd hvs (Finset.disjoint_left.1 hd1 (Finset.mem_sdiff.1 hp2).1)
    by_contra hvL
    exact hvB (Finset.mem_symmDiff.2 (Or.inl ⟨hvs, hvL⟩))
  -- the vertex leaves the second class of `s'` after the block, if it is not in `s.2`
  have claim2 : v ∉ s.2 → v ∈ SideBlock.listToggle₂ (D.blocks.drop (r + 1)) := by
    intro hvs
    have hvs' : v ∈ s'.2 := (Finset.mem_union.1 hv).resolve_left hvs
    have hvB : v ∉ symmDiff s'.2 (SideBlock.listToggle₂ (D.blocks.drop (r + 1))) := by
      rcases hsep with ⟨-, -, hne⟩ | ⟨rfl, h2⟩ | ⟨rfl, -⟩
      · intro hB
        exact hne (hR'.2 v hB).symm
      · exact absurd h2 hvs
      · exact hR'.1
    by_contra hvL
    exact hvB (Finset.mem_symmDiff.2 (Or.inl ⟨hvs', hvL⟩))
  by_cases hvs : v ∈ s.2
  · have h1 := claim1 hvs
    have hnot : v ∉ s'.2 := by
      rcases Finset.mem_symmDiff.1 (hL₂ h1) with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact absurd hvs h
    obtain ⟨Q, hQ, hvQ⟩ := (SideBlock.mem_listToggle₂ hndpre).1 h1
    obtain ⟨q, hq, hget⟩ := exists_fin_of_mem_take hQ
    exact ⟨fun h => hnot (Finset.mem_inter.1 h).2, q, Q, hget, hvQ,
      fun _ => hq, fun h => absurd h hnot⟩
  · have h2 := claim2 hvs
    obtain ⟨Q, hQ, hvQ⟩ := (SideBlock.mem_listToggle₂ hndpost).1 h2
    obtain ⟨q, hq, hget⟩ := exists_fin_of_mem_drop hQ
    exact ⟨fun h => hvs (Finset.mem_inter.1 h).1, q, Q, hget, hvQ,
      fun h => absurd h hvs, fun _ => hq⟩

/-- **Direction lemma, side 2.**  The mirror image of `direction` for a side-2 block
`P = D.blocks[r]` (a component of `G[C_b ⊕ C'_d]`) and a vertex `v ∈ C_a ∪ C'_c`: then
`v ∉ C_a ∩ C'_c` and `v` lies in a side-1 block `D.blocks[q]`, with `q < r` if `v ∈ C_a` and
`r < q` if `v ∈ C'_c`.  It is `direction` for `D.swapSides`
(`FreeFermionGraphs.T3FixedPairingSymm`), a deformation of `s.swap` by `s'.swap` with the same
blocks (v1: "the other side is analogous"). -/
theorem direction₂ (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (D : G.FPDeformation s s')
    (hD : D.Palindromic) {r : Fin D.blocks.length} {P : G.OddBlock s.2 s'.2}
    (hr : D.blocks.get r = Sum.inr P) {p : V × V} (hp : p ∈ P.word) {v : V}
    (hv : v ∈ s.1 ∪ s'.1)
    (hsep : (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) ∨ (v = p.1 ∧ v ∈ s.1) ∨
      (v = p.2 ∧ v ∈ s'.1)) :
    v ∉ s.1 ∩ s'.1 ∧ ∃ (q : Fin D.blocks.length) (Q : G.OddBlock s.1 s'.1),
      D.blocks.get q = Sum.inl Q ∧ v ∈ Q.support ∧ (v ∈ s.1 → q < r) ∧ (v ∈ s'.1 → r < q) := by
  have hlen : D.swapSides.blocks.length = D.blocks.length := by simp
  have hr' : D.swapSides.blocks.get (Fin.cast hlen.symm r) = Sum.inl P := by
    have : D.blocks[r.val] = Sum.inr P := by simpa using hr
    simp [blocks_swapSides, this]
  obtain ⟨h1, q, Q, hq, hvQ, hq1, hq2⟩ :=
    direction hs.swap hs'.swap D.swapSides ((palindromic_swapSides_iff D).2 hD) hr' hp hv hsep
  have hq' : D.blocks.get (Fin.cast hlen q) = Sum.inl Q := by
    have h1 : SideBlock.swap (D.blocks.get (Fin.cast hlen q)) = Sum.inr Q := by
      simpa [blocks_swapSides] using hq
    have := congrArg SideBlock.swap h1
    rw [SideBlock.swap_swap] at this
    exact this
  exact ⟨h1, Fin.cast hlen q, Q, hq', hvQ, fun h => hq1 h, fun h => hq2 h⟩

/-- **Uniqueness of the block containing a vertex.**  Two side-2 blocks of `D` which contain a
common vertex are the same block, at the same position (blocks of one side graph with distinct
supports are disjoint, and the supports of the blocks of `D` are pairwise distinct). -/
theorem eq_of_mem_support_inr (D : G.FPDeformation s s') {q q' : Fin D.blocks.length}
    {Q Q' : G.OddBlock s.2 s'.2} (hq : D.blocks.get q = Sum.inr Q)
    (hq' : D.blocks.get q' = Sum.inr Q') {v : V} (hv : v ∈ Q.support) (hv' : v ∈ Q'.support) :
    q = q' := by
  have hsupp : Q.support = Q'.support := by
    by_contra hne
    exact Finset.disjoint_left.1 (OddBlock.disjoint_of_support_ne Q Q' hne) hv hv'
  have hmem : ∀ i : Fin D.blocks.length, D.blocks.get i ∈ D.blocks := fun i => List.get_mem _ _
  have hbl : D.blocks.get q = D.blocks.get q' := by
    refine List.inj_on_of_nodup_map D.nodup (hmem q) (hmem q') ?_
    rw [hq, hq']
    exact hsupp
  exact (List.Nodup.get_inj_iff (List.Nodup.of_map _ D.nodup)).1 hbl

/-- **Side 1 uniqueness.**  The side-1 version of `eq_of_mem_support_inr`. -/
theorem eq_of_mem_support_inl (D : G.FPDeformation s s') {q q' : Fin D.blocks.length}
    {Q Q' : G.OddBlock s.1 s'.1} (hq : D.blocks.get q = Sum.inl Q)
    (hq' : D.blocks.get q' = Sum.inl Q') {v : V} (hv : v ∈ Q.support) (hv' : v ∈ Q'.support) :
    q = q' := by
  have hsupp : Q.support = Q'.support := by
    by_contra hne
    exact Finset.disjoint_left.1 (OddBlock.disjoint_of_support_ne Q Q' hne) hv hv'
  have hmem : ∀ i : Fin D.blocks.length, D.blocks.get i ∈ D.blocks := fun i => List.get_mem _ _
  have hbl : D.blocks.get q = D.blocks.get q' := by
    refine List.inj_on_of_nodup_map D.nodup (hmem q) (hmem q') ?_
    rw [hq, hq']
    exact hsupp
  exact (List.Nodup.get_inj_iff (List.Nodup.of_map _ D.nodup)).1 hbl

end FPDeformation

end SimpleGraph
