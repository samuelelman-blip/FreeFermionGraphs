import FreeFermionGraphs.T3SeparatorParity
import FreeFermionGraphs.T3StepCondsTransport
import FreeFermionGraphs.T3ToggleStable

/-!
# The lift lemma

This module proves the *lift lemma* of the synthesised proof of Theorem 1(iii) of arXiv 2305.15625
v1 (label `theorem:conservedcharges`), package T3-24.  It replaces the rerouting step of v1
(L1155-1172) and the concatenation validity of Lemma 9(i) of the appendix (L1880-1915).

Let `s = (A, B)` and `s' = (A', B')` be the colouring classes of two even holes `C = A ∪ B` and
`C' = A' ∪ B'`, and let `Q` be a side-1 block of `(s; s')` (an odd component of `G[A ⊕ A']`) which
runs from `s`.  Let `D₁` be a palindromic fixed-pairing deformation at the intermediate state
`(s.1 ⊕ Q, s.2; s')`, i.e. a deformation from which `Q` has already been removed.  The lift lemma
says that `D₁` can be transported back to `(s; s')`, with `Q` either not used or used as a first
block, preserving palindromicity and the parity of the toggle:

* (a) `FPDeformation.ofToggle Q D₁` is palindromic at `(s, s')` and has the parity of `D₁`;
* (b) `FPDeformation.cons (inl Q) (FPDeformation.ofToggle Q D₁)` is palindromic at `(s, s')` and has
  the parity of `D₁`.

Here `IsOdd` of a deformation `D` with toggle `T` is the oddness of `c(T, C)`, the cross count of
`T` with the carrier of its start state, so that `D₁.IsOdd` is `Odd c(T₁, C ⊕ Q)`.

## The hypotheses

`Q` is *good* in the sense of the work package: `|Q ∩ W| = 1` with `W` the set of vertices of `C'`
which anticommute with `h_C` (`matchedW s s' ∪ crossedW s s'`, v1 Definition 20,
`definition:anticommutingdependentsubsets`), `|Q ∩ W'|` is even with `W'` the set of vertices of `C`
which anticommute with `h_{C'}`, and all separators of `Q` in `s'.2` (the vertices of `s'.2` which
obstruct a step of `Q`, `OddBlock.separators`) lie in one component of `G[s.2 ⊕ s'.2]`.  The last
hypothesis `hsep` is the conclusion of the separator lemma
`OddBlock.separators_sameComponent` (package T3-22), which holds under the balanced condition on
`W'`; it enters here as a hypothesis, so this module does not depend on that lemma.

## Proof

All the work is done by the step-condition criterion of palindromic deformations
(`FPDeformation.palindromic_iff_stepConds`): a deformation of hole-class states is palindromic iff
the steps of each block, at the time it runs forward from `s` and at the time it runs backward from
`s'`, separate no vertex of the class they are tested against (`SideBlock.StepConds`).

* The side-1 blocks `P` of `D₁` are components of `G[(s.1 ⊕ Q) ⊕ s'.1]`, i.e. components of
  `G[s.1 ⊕ s'.1]` other than `Q`.  No edge joins `P` to `Q` (`OddBlock.stepIndep_word_toggled`), so
  their steps separate no vertex of `Q`.
* A side-2 block `R` of `D₁` which contains no separator of `Q` in `s'.2` likewise separates no
  vertex of `Q` (`FPDeformation.stepIndep_word_of_inr`): the introduced vertices `j_t` of `Q` lie in
  both first classes of `D₁`, and the clone conditions of `R` against them are available, while a
  removed vertex `k_t` of `Q` which separates a step of `R` forces a separator of `Q` into `R`
  (the requirement lemma `OddBlock.requires_contains_separator`, T3-23 (e)).
* Case (a): no side-2 block of `D₁` contains a separator.  Then no block of `D₁` separates a vertex
  of `Q`, the forward test class `s.1 ⊕ T₁(pre)` of a side-2 block differs from that of `D₁`,
  `(s.1 ⊕ Q) ⊕ T₁(pre)`, by `Q`, and the step conditions transport
  (`FPDeformation.stepConds_ofToggle`).  For the parity, `c(T₁, Q)` is even
  (`SideBlock.crossCount_support_mod_two`).
* Case (b): some side-2 block `R₀` of `D₁` contains a separator.  By `hsep` it is unique and
  contains all separators.  The list `inl Q :: D₁.blocks` has the step conditions: the blocks of
  `D₁` are tested exactly as in `D₁` (`Q` is a side-1 block, so it has been removed from the first
  classes both in `D₁` and after running `Q` from `s`), and `Q` itself runs forward from `s`
  (T3-23 (a)) and backward from `s'` after the side-2 toggle `T₂(D₁)`, because the separators of
  `Q` in `s'.2` lie in `R₀` and are toggled out, while a vertex of `T₂(D₁) ∖ s'.2` lies in `s.2`
  and is not a separator.  Its support is new because `j_0` lies in no block of `D₁`.  For the
  parity, every block of `D₁` other than `R₀` separates no vertex of `Q` (a side-2 block `R ≠ R₀`
  contains no separator, since it is disjoint from `R₀`), so `c(T₁, Q) ≡ c(R₀, Q)`, and
  `c(R₀, Q) ≡ c(Q, s'.2) ≡ 1 + |Q ∩ W'| ≡ 1` because the steps of `Q` separate no vertex of
  `s'.2 ⊕ R₀` (T3-23 (a), (d)); also `c(Q, C) ≡ |Q ∩ W| = 1` (T3-23 (b)).  With
  `c(Q ⊕ T₁, C) ≡ c(Q, C) + c(T₁, C)` and `c(T₁, C ⊕ Q) ≡ c(T₁, C) + c(T₁, Q)` the parities agree.

The dichotomy (a) or (b) is the split on whether some side-2 block of `D₁` contains a separator of
`Q`.  The theorem does not claim that exactly one of (a), (b) holds.

## Main results

* `SideBlock.crossCount_tog_mod_two_of_forall`, `crossCount_tog_mod_two_of_unique`: parity of the
  cross count of the toggle of a list of blocks with a fixed set.
* `OddBlock.isHoleClasses_toggle`, `disjoint_support_snd`, `toggle_union`, `first_mem_inter`: the
  intermediate state `(s.1 ⊕ Q, s.2)` after a running side-1 block `Q`.
* `OddBlock.not_adj_of_toggled`, `stepIndep_word_toggled`: no edge joins a block of the intermediate
  state to `Q`.
* `FPDeformation.stepIndep_word_of_inr`: a side-2 block of a palindromic `D₁` without a separator of
  `Q` separates no vertex of `Q`.
* `FPDeformation.stepConds_ofToggle`: transport of the step conditions along `ofToggle`.
* `OddBlock.mem_support_of_mem_separators`, `cond_of_not_mem_separators`,
  `crossCount_separator_block_mod_two`: the block containing the separators.
* `FPDeformation.lift_of_no_separator` (case (a)), `FPDeformation.lift_cons_of_separator`
  (case (b)), and `FPDeformation.lift`: the lift lemma.

Claw-freeness is used only through T3-23 (b) and (d) (`OddBlock.crossCount_carrier_mod_two`,
`OddBlock.separatorIncidence_mod_two`), in case (b).  The lemma holds without `Fintype V`.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Toggles and cross counts of lists of blocks -/

namespace SideBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- If every block of a list has an even cross count with `Z`, so has the toggle of the list. -/
theorem crossCount_tog_mod_two_of_forall {L : List (G.SideBlock s s')} {Z : Finset V}
    (h : ∀ B ∈ L, G.crossCount B.support Z % 2 = 0) : G.crossCount (tog L) Z % 2 = 0 := by
  induction L with
  | nil => simp [tog_nil, crossCount_emptyset_left_eq_zero]
  | cons B L ih =>
    have h1 := h B (List.mem_cons_self ..)
    have h2 := ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    rw [tog_cons, crossCount_symmDiff_left_mod_two]
    omega

/-- If a list of blocks with pairwise distinct supports contains a block `B₀`, and every other block
has an even cross count with `Z`, then the cross count of the toggle of the list with `Z` has the
parity of that of `B₀`. -/
theorem crossCount_tog_mod_two_of_unique {L : List (G.SideBlock s s')}
    (hnd : (L.map SideBlock.support).Nodup) {B₀ : G.SideBlock s s'} (hB₀ : B₀ ∈ L) {Z : Finset V}
    (h : ∀ B ∈ L, B ≠ B₀ → G.crossCount B.support Z % 2 = 0) :
    G.crossCount (tog L) Z % 2 = G.crossCount B₀.support Z % 2 := by
  induction L with
  | nil => exact absurd hB₀ (List.not_mem_nil)
  | cons B L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hB : B = B₀
    · subst hB
      have hnot : ∀ B' ∈ L, B' ≠ B := by
        rintro B' hB' rfl
        exact hnd.1 (List.mem_map_of_mem hB')
      have := crossCount_tog_mod_two_of_forall (L := L) (Z := Z)
        (fun B' hB' => h B' (List.mem_cons_of_mem _ hB') (hnot B' hB'))
      rw [tog_cons, crossCount_symmDiff_left_mod_two]
      omega
    · have hmem : B₀ ∈ L := by
        rcases List.mem_cons.1 hB₀ with h' | h'
        · exact absurd h'.symm hB
        · exact h'
      have h1 := h B (List.mem_cons_self ..) hB
      have h2 := ih hnd.2 hmem (fun B' hB' hne => h B' (List.mem_cons_of_mem _ hB') hne)
      rw [tog_cons, crossCount_symmDiff_left_mod_two]
      omega

end SideBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- The toggle of a deformation is the toggle of its list of blocks. -/
theorem toggle_eq_tog (D : G.FPDeformation s s') : D.toggle = SideBlock.tog D.blocks := rfl

end FPDeformation

/-! ### The running block and the intermediate state -/

namespace OddBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- After a side-1 block `Q` has run from the hole-class state `s`, the state `(s.1 ⊕ Q, s.2)` is a
hole-class state. -/
theorem isHoleClasses_toggle (hs : G.IsHoleClasses s) (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s) : G.IsHoleClasses (symmDiff s.1 Q.support, s.2) := by
  obtain ⟨t', hrun⟩ := hQ
  have hrun' : G.ClassRun (s.1, s.2) Q.word t' := hrun
  have hend := classRun_end_of_indep hs.disjoint Q (Finset.inter_comm _ _) hrun'
  rw [← hend]
  exact hrun.isHoleClasses hs

/-- A side-1 block which runs from `s` is disjoint from the second class `s.2`: the introduced
vertices avoid it by the forward conditions, and the removed vertices lie in `s.1`. -/
theorem disjoint_support_snd (hs : G.IsHoleClasses s) (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s) : Disjoint Q.support s.2 := by
  rw [Finset.disjoint_left]
  intro v hv hvB
  obtain ⟨p, hp, rfl | rfl⟩ := mem_support_iff_exists_mem_word.1 hv
  · exact (forward_cond_of_runsFrom hs Q hQ p hp).1 hvB
  · exact Finset.disjoint_left.1 hs.disjoint (Finset.mem_sdiff.1 (snd_mem hp)).1 hvB

/-- The union of the first class of the intermediate state `(s.1 ⊕ Q, s.2)` with `s.2` is the
carrier `C ⊕ Q`. -/
theorem toggle_union (Q : G.OddBlock s.1 s'.1) (hd : Disjoint Q.support s.2) :
    symmDiff s.1 Q.support ∪ s.2 = symmDiff (s.1 ∪ s.2) Q.support := by
  ext v
  have := Finset.disjoint_left.1 hd
  simp only [Finset.mem_union, Finset.mem_symmDiff]
  by_cases h1 : v ∈ s.1 <;> by_cases h2 : v ∈ s.2 <;> by_cases h3 : v ∈ Q.support <;>
    simp_all

/-- The first vertex of a side-1 block `Q` which runs from `s` lies in the first class of the
intermediate state `(s.1 ⊕ Q, s.2)` and in `s'.1`, and in neither second class. -/
theorem first_mem_inter (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s) :
    Q.first ∈ symmDiff s.1 Q.support ∧ Q.first ∈ s'.1 ∧ Q.first ∉ s.2 ∧ Q.first ∉ s'.2 := by
  have h1 := Q.first_mem_Y
  rw [Finset.mem_sdiff] at h1
  refine ⟨Finset.mem_symmDiff.2 (Or.inr ⟨Q.first_mem_support, h1.2⟩), h1.1,
    Finset.disjoint_left.1 (Q.disjoint_support_snd hs hQ) Q.first_mem_support, ?_⟩
  intro h
  exact Finset.disjoint_left.1 hs'.disjoint h1.1 h

/-! ### Blocks of the intermediate state do not touch the running block -/

/-- **No edge joins a block of the intermediate state to the running block.**  Let `Q` be a
component of `G[X ⊕ Y]` and `P` a block of `G[(X ⊕ Q) ⊕ Y]`.  Then `P` is a component of
`G[X ⊕ Y]` other than `Q`, so no vertex of `P` is adjacent to a vertex of `Q`. -/
theorem not_adj_of_toggled {X Y : Finset V} (Q : G.OddBlock X Y)
    (P : G.OddBlock (symmDiff X Q.support) Y) {x y : V} (hx : x ∈ P.support)
    (hy : y ∈ Q.support) : ¬ G.Adj x y := by
  intro hadj
  have hQsub : Q.support ⊆ symmDiff X Y := Q.support_subset_symmDiff
  have hxU : x ∈ symmDiff (symmDiff X Q.support) Y := P.support_subset_symmDiff hx
  have hxXY : x ∈ symmDiff X Y := by
    by_cases hxQ : x ∈ Q.support
    · exact hQsub hxQ
    · simp only [Finset.mem_symmDiff] at hxU ⊢
      tauto
  have hxQ : x ∈ Q.support := by
    have := Q.isInducedComponent_support.2.2 (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hxXY)
      hadj.symm
    exact Finset.mem_coe.1 this
  have h2 := hQsub hxQ
  simp only [Finset.mem_symmDiff] at hxU h2
  tauto

/-- The steps of a block of the intermediate state `(X ⊕ Q, Y)` separate no vertex of `Q`. -/
theorem stepIndep_word_toggled {X Y : Finset V} (Q : G.OddBlock X Y)
    (P : G.OddBlock (symmDiff X Q.support) Y) : StepIndep G P.word Q.support := by
  intro p hp v hv
  have h1 := Q.not_adj_of_toggled P (fst_mem_support hp) hv
  have h2 := Q.not_adj_of_toggled P (snd_mem_support hp) hv
  exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end OddBlock

/-! ### Side-2 blocks without separators do not touch the running block -/

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **A side-2 block containing no separator of `Q` separates no vertex of `Q`.**  Let `Q` be a
side-1 block which runs from `s`, let `D₁` be a palindromic deformation at `(s.1 ⊕ Q, s.2; s')` and
`R` a side-2 block of `D₁` with no separator of `Q` in `s'.2` (`R.support ∩ Q.separators s'.2 = ∅`).
Then no step of `R` separates a vertex of `Q`.

An introduced vertex `j_t ∈ s'.1 ∖ s.1` of `Q` lies in the first class `(s.1 ⊕ Q) ⊕ T₁(pre)` of the
forward test of `R` (it lies in no side-1 block of `D₁`, since it is in both `s.1 ⊕ Q` and `s'.1`),
and the step conditions of `D₁` give the claim.  A removed vertex `k_t ∈ s.1 ∖ s'.1` of `Q` which
separated a step of `R` would force, by the requirement lemma
(`OddBlock.requires_contains_separator`), a separator of `Q` into `R`. -/
theorem stepIndep_word_of_inr (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s)
    {D₁ : G.FPDeformation (symmDiff s.1 Q.support, s.2) s'} (hD₁ : D₁.Palindromic)
    {R : G.OddBlock s.2 s'.2} (hR : Sum.inr R ∈ D₁.blocks)
    (hno : R.support ∩ Q.separators s'.2 = ∅) : StepIndep G R.word Q.support := by
  classical
  have hs₁ := Q.isHoleClasses_toggle hs hQ
  obtain ⟨pre, post, hdec⟩ := List.append_of_mem hR
  have hF : StepIndep G R.word (symmDiff (symmDiff s.1 Q.support) (SideBlock.listToggle₁ pre)) :=
    (Palindromic.stepConds hs₁ hs' hD₁ pre (Sum.inr R) post hdec).1
  intro p hp v hv
  rcases OddBlock.mem_support_of_mem_Y hv with ⟨hvY, hvX⟩ | ⟨hvX, hvY⟩
  · -- an introduced vertex of `Q`: it lies in the first class of the forward test
    refine hF p hp v ?_
    rw [Finset.mem_symmDiff]
    left
    refine ⟨Finset.mem_symmDiff.2 (Or.inr ⟨hv, hvX⟩), fun hmem => ?_⟩
    have hsub := SideBlock.listToggle₁_subset pre hmem
    simp only [Finset.mem_symmDiff] at hsub
    have hv1 : v ∈ symmDiff s.1 Q.support := Finset.mem_symmDiff.2 (Or.inr ⟨hv, hvX⟩)
    tauto
  · -- a removed vertex of `Q`
    by_contra hne
    have hpk : v = p.1 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) := by
      by_cases h1 : v = p.1
      · exact Or.inl h1
      · refine Or.inr ⟨h1, ?_, hne⟩
        intro h
        apply Finset.disjoint_left.1 hs.disjoint hvX
        rw [h]
        exact (Finset.mem_sdiff.1 (OddBlock.snd_mem hp)).1
    have hnon := OddBlock.requires_contains_separator hs hs' Q hQ hD₁ hR
      ⟨p, hp, v, Finset.mem_inter.2 ⟨hv, hvX⟩, hpk⟩
    rw [hno] at hnon
    exact Finset.not_nonempty_empty hnon

/-! ### Transport of the step conditions along `ofToggle` -/

/-- Cutting a transported list: a decomposition of `L.map (ofToggle Q)` comes from a decomposition
of `L`. -/
theorem map_ofToggle_decomp (Q : G.OddBlock s.1 s'.1)
    {L : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')} {pre post : List (G.SideBlock s s')}
    {B : G.SideBlock s s'} (hdec : L.map (SideBlock.ofToggle Q) = pre ++ B :: post) :
    ∃ (pre₁ : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s'))
      (B₁ : G.SideBlock (symmDiff s.1 Q.support, s.2) s')
      (post₁ : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')),
      L = pre₁ ++ B₁ :: post₁ ∧ pre = pre₁.map (SideBlock.ofToggle Q) ∧
        B = SideBlock.ofToggle Q B₁ ∧ post = post₁.map (SideBlock.ofToggle Q) := by
  obtain ⟨l₁, l₂, hL, hl₁, hl₂⟩ := List.map_eq_append_iff.1 hdec
  obtain ⟨a, l, hl₂', haX, hlpost⟩ := List.map_eq_cons_iff.1 hl₂
  exact ⟨l₁, a, l, by rw [hL, hl₂'], hl₁.symm, haX.symm, hlpost.symm⟩

theorem ofToggle_inl (Q : G.OddBlock s.1 s'.1) (P : G.OddBlock (symmDiff s.1 Q.support) s'.1) :
    SideBlock.ofToggle Q (Sum.inl P) =
      Sum.inl (P.ofToggle Q.support_subset_symmDiff Q.isInducedComponent_support) := rfl

theorem ofToggle_inr (Q : G.OddBlock s.1 s'.1) (R : G.OddBlock s.2 s'.2) :
    SideBlock.ofToggle Q (Sum.inr R : G.SideBlock (symmDiff s.1 Q.support, s.2) s') =
      Sum.inr R := rfl

/-- The second class tested by a side-1 block is unchanged by the transport. -/
theorem other_ofToggle_inl (Q : G.OddBlock s.1 s'.1) (t : Finset V × Finset V)
    (P : G.OddBlock (symmDiff s.1 Q.support) s'.1)
    (l : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')) :
    SideBlock.other t (SideBlock.ofToggle Q (Sum.inl P)) (l.map (SideBlock.ofToggle Q)) =
      symmDiff t.2 (SideBlock.listToggle₂ l) := by
  rw [ofToggle_inl, SideBlock.other_inl, SideBlock.listToggle₂_map_ofToggle]

/-- The first class tested by a side-2 block. -/
theorem other_ofToggle_inr (Q : G.OddBlock s.1 s'.1) (t : Finset V × Finset V)
    (R : G.OddBlock s.2 s'.2)
    (l : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')) :
    SideBlock.other t
      (SideBlock.ofToggle Q (Sum.inr R : G.SideBlock (symmDiff s.1 Q.support, s.2) s'))
      (l.map (SideBlock.ofToggle Q)) = symmDiff t.1 (SideBlock.listToggle₁ l) := by
  rw [ofToggle_inr, SideBlock.other_inr, SideBlock.listToggle₁_map_ofToggle]

/-- **Transport of the step conditions along `ofToggle`.**  Let `L` be a list of side blocks at the
intermediate state `(s.1 ⊕ Q, s.2; s')` with the step conditions, such that no side-2 block of `L`
separates a vertex of the side-1 block `Q`.  Then the transported list has the step conditions at
`(s; s')`.

The side-1 blocks are tested against the second class `s.2 ⊕ T₂(pre)`, the same on both sides.  A
side-2 block is tested against `s.1 ⊕ T₁(pre)` instead of `(s.1 ⊕ Q) ⊕ T₁(pre)`; the two differ by
`Q`, which its steps do not separate. -/
theorem stepConds_ofToggle (Q : G.OddBlock s.1 s'.1)
    {L : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')}
    (h : SideBlock.StepConds G (symmDiff s.1 Q.support, s.2) s' L)
    (hQ : ∀ R : G.OddBlock s.2 s'.2, Sum.inr R ∈ L → StepIndep G R.word Q.support) :
    SideBlock.StepConds G s s' (L.map (SideBlock.ofToggle Q)) := by
  intro pre B post hdec
  obtain ⟨pre₁, B₁, post₁, hL, rfl, rfl, rfl⟩ := map_ofToggle_decomp Q hdec
  obtain ⟨hF, hB⟩ := h pre₁ B₁ post₁ hL
  have hB₁ : B₁ ∈ L := by rw [hL]; exact List.mem_append_right _ (List.mem_cons_self ..)
  cases B₁ with
  | inl P =>
    refine ⟨?_, ?_⟩
    · rw [SideBlock.word_ofToggle, other_ofToggle_inl]
      exact hF
    · rw [SideBlock.word_ofToggle, ofToggle_inl, SideBlock.other_inl,
        SideBlock.listToggle₂_map_ofToggle]
      exact hB
  | inr R =>
    refine ⟨?_, ?_⟩
    · rw [SideBlock.word_ofToggle, other_ofToggle_inr]
      have h2 := hF.symmDiff' (hQ R hB₁)
      have e : symmDiff s.1 (SideBlock.listToggle₁ pre₁) =
          symmDiff (symmDiff (symmDiff s.1 Q.support) (SideBlock.listToggle₁ pre₁)) Q.support := by
        ext v
        simp only [Finset.mem_symmDiff]
        tauto
      rw [e]
      exact h2
    · rw [SideBlock.word_ofToggle, ofToggle_inr, SideBlock.other_inr,
        SideBlock.listToggle₁_map_ofToggle]
      exact hB

/-! ### Case (a): no side-2 block of `D₁` contains a separator -/

/-- **Lift, case (a).**  Let `Q` be a side-1 block which runs from `s`, and `D₁` a palindromic
deformation at `(s.1 ⊕ Q, s.2; s')` none of whose side-2 blocks contains a separator of `Q` in
`s'.2`.  Then `ofToggle Q D₁` is palindromic at `(s, s')` and has the parity of `D₁`.

No block of `D₁` separates a vertex of `Q` (`OddBlock.stepIndep_word_toggled` for the side-1 blocks,
`stepIndep_word_of_inr` for the side-2 blocks), so the step conditions transport
(`stepConds_ofToggle`) and `c(T₁, Q)` is even; the carrier of the intermediate state is
`C ⊕ Q`, so `c(T₁, C ⊕ Q) ≡ c(T₁, C) + c(T₁, Q) ≡ c(T₁, C)` (mod 2). -/
theorem lift_of_no_separator (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s)
    (D₁ : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') (hD₁ : D₁.Palindromic)
    (hno : ∀ R : G.OddBlock s.2 s'.2, Sum.inr R ∈ D₁.blocks → R.support ∩ Q.separators s'.2 = ∅) :
    (FPDeformation.ofToggle Q D₁).Palindromic ∧
      ((FPDeformation.ofToggle Q D₁).IsOdd ↔ D₁.IsOdd) := by
  have hs₁ := Q.isHoleClasses_toggle hs hQ
  have hall : ∀ B ∈ D₁.blocks, StepIndep G B.word Q.support := by
    intro B hB
    cases B with
    | inl P => exact Q.stepIndep_word_toggled P
    | inr R => exact stepIndep_word_of_inr hs hs' Q hQ hD₁ hB (hno R hB)
  have hconds : SideBlock.StepConds G s s' (FPDeformation.ofToggle Q D₁).blocks :=
    stepConds_ofToggle Q (Palindromic.stepConds hs₁ hs' hD₁) (fun R hR => hall _ hR)
  refine ⟨Palindromic.of_stepConds hs hs' _ hconds, ?_⟩
  have hT : G.crossCount D₁.toggle Q.support % 2 = 0 := by
    rw [toggle_eq_tog]
    exact SideBlock.crossCount_tog_mod_two_of_forall
      (fun B hB => SideBlock.crossCount_support_mod_two B (hall B hB))
  have hd := Q.disjoint_support_snd hs hQ
  unfold IsOdd
  rw [ofToggle_toggle]
  show Odd (G.crossCount D₁.toggle (s.1 ∪ s.2)) ↔
    Odd (G.crossCount D₁.toggle (symmDiff s.1 Q.support ∪ s.2))
  rw [OddBlock.toggle_union Q hd, Nat.odd_iff, Nat.odd_iff, crossCount_symmDiff_right_mod_two]
  omega

/-! ### Case (b): some side-2 block of `D₁` contains a separator -/

end FPDeformation

namespace OddBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **All separators lie in the block that contains one.**  If a side-2 block `R` of `(s; s')`
contains a separator `u` of `Q` in `s'.2`, and any two separators of `Q` in `s'.2` lie in one
component of `G[s.2 ⊕ s'.2]`, then every separator of `Q` in `s'.2` lies in `R`: the block `R` is
that component. -/
theorem mem_support_of_mem_separators (Q : G.OddBlock s.1 s'.1)
    (hsep : ∀ u ∈ Q.separators s'.2, ∀ v ∈ Q.separators s'.2,
      v ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u)
    {R : G.OddBlock s.2 s'.2} {u : V} (hu : u ∈ R.support) (huS : u ∈ Q.separators s'.2) {v : V}
    (hv : v ∈ Q.separators s'.2) : v ∈ R.support := by
  have huU : u ∈ (↑(symmDiff s.2 s'.2) : Set V) :=
    Finset.mem_coe.2 (R.support_subset_symmDiff hu)
  have hcomp := isInducedComponent_inducedComponentSet (G := G) huU
  have heq := eq_of_isInducedComponent_of_mem R.isInducedComponent_support hcomp
    (Finset.mem_coe.2 hu) ⟨huU, huU, Reachable.refl _⟩
  have := hsep u huS v hv
  rw [← heq] at this
  exact Finset.mem_coe.1 this

/-- A vertex of `s'.2` which is not a separator of `Q` is separated by no step of `Q`: its
adjacency to the introduced and the removed vertex of every step agree. -/
theorem cond_of_not_mem_separators (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) {v : V}
    (hv : v ∈ s'.2) (hnot : v ∉ Q.separators s'.2) :
    ∀ p ∈ Q.word, (G.Adj p.1 v ↔ G.Adj p.2 v) := by
  intro p hp
  by_contra hne
  apply hnot
  refine mem_separators.2 ⟨hv, p, hp, ?_⟩
  by_cases h2 : v = p.2
  · exact Or.inl h2
  · refine Or.inr ⟨?_, h2, hne⟩
    intro h1
    apply Finset.disjoint_left.1 hs'.disjoint (Finset.mem_sdiff.1 (fst_mem hp)).1
    rw [← h1]
    exact hv

/-- **The block containing the separators has odd cross count with `Q`.**  Let `Q` be a side-1
block which runs from `s`, with `|Q ∩ W'|` even, whose separators in `s'.2` lie in one component
of `G[s.2 ⊕ s'.2]`.  If a side-2 block `R` contains a separator, then `c(R, Q)` is odd.

Indeed the steps of `Q` separate no vertex of `s'.2 ⊕ R`: the vertices of `s.2` are not separated
by the forward conditions, and the separators lie in `R`.  Hence
`c(Q, R) ≡ c(Q, s'.2) ≡ 1 + |Q ∩ W'| ≡ 1` (T3-23 (d)). -/
theorem crossCount_separator_block_mod_two (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s)
    (hW' : Even (Q.support ∩ (G.matchedW s' s ∪ G.crossedW s' s)).card)
    (hsep : ∀ u ∈ Q.separators s'.2, ∀ v ∈ Q.separators s'.2,
      v ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u)
    {R : G.OddBlock s.2 s'.2} {u : V} (hu : u ∈ R.support) (huS : u ∈ Q.separators s'.2) :
    G.crossCount R.support Q.support % 2 = 1 := by
  have hc := forward_cond_of_runsFrom hs Q hQ
  have hstep : StepIndep G Q.word (symmDiff s'.2 R.support) := by
    intro p hp v hv
    rcases Finset.mem_symmDiff.1 hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · apply cond_of_not_mem_separators hs' Q hv1 ?_ p hp
      intro hvS
      exact hv2 (mem_support_of_mem_separators Q hsep hu huS hvS)
    · have hv3 : v ∈ s.2 := by
        rcases Finset.mem_symmDiff.1 (R.support_subset_symmDiff hv1) with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hv2
      exact (hc p hp).2 v hv3
  have h1 := Q.crossCount_support_mod_two hstep
  rw [crossCount_symmDiff_right_mod_two] at h1
  have h2 := separatorIncidence_mod_two hclaw hs hs' Q hQ
  have h3 := Nat.even_iff.1 hW'
  rw [crossCount_comm]
  omega

end OddBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Lift, case (b).**  Let `Q` be a side-1 block which runs from `s`, with `|Q ∩ W| = 1` and
`|Q ∩ W'|` even, whose separators in `s'.2` lie in one component of `G[s.2 ⊕ s'.2]`.  Let `D₁` be
a palindromic deformation at `(s.1 ⊕ Q, s.2; s')` having a side-2 block `R₀` which contains a
separator of `Q`.  Then `Q` can be put in front of the transported deformation: the result is
palindromic at `(s, s')` and has the parity of `D₁`. -/
theorem lift_cons_of_separator (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s)
    (hW : (Q.support ∩ (G.matchedW s s' ∪ G.crossedW s s')).card = 1)
    (hW' : Even (Q.support ∩ (G.matchedW s' s ∪ G.crossedW s' s)).card)
    (hsep : ∀ u ∈ Q.separators s'.2, ∀ v ∈ Q.separators s'.2,
      v ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u)
    (D₁ : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') (hD₁ : D₁.Palindromic)
    {R₀ : G.OddBlock s.2 s'.2} (hR₀ : Sum.inr R₀ ∈ D₁.blocks)
    (hR₀S : (R₀.support ∩ Q.separators s'.2).Nonempty) :
    ∃ hQ' : SideBlock.support (Sum.inl Q : G.SideBlock s s') ∉
        (FPDeformation.ofToggle Q D₁).blocks.map SideBlock.support,
      (FPDeformation.cons (.inl Q) (FPDeformation.ofToggle Q D₁) hQ').Palindromic ∧
        ((FPDeformation.cons (.inl Q) (FPDeformation.ofToggle Q D₁) hQ').IsOdd ↔ D₁.IsOdd) := by
  classical
  obtain ⟨u, huI⟩ := hR₀S
  obtain ⟨hu, huS⟩ := Finset.mem_inter.1 huI
  have hs₁ := Q.isHoleClasses_toggle hs hQ
  have hc := OddBlock.forward_cond_of_runsFrom hs Q hQ
  have hsepR : ∀ v ∈ Q.separators s'.2, v ∈ R₀.support := fun v hv =>
    OddBlock.mem_support_of_mem_separators Q hsep hu huS hv
  -- the support of `Q` is new: its first vertex lies in no block of `D₁`
  obtain ⟨hf1, hf2, hf3, hf4⟩ := Q.first_mem_inter hs hs' hQ
  have hQ' : SideBlock.support (Sum.inl Q : G.SideBlock s s') ∉
      (FPDeformation.ofToggle Q D₁).blocks.map SideBlock.support := by
    rw [ofToggle_support]
    intro hmem
    obtain ⟨B, -, hBeq⟩ := List.mem_map.1 hmem
    have hfs : Q.first ∈ B.support := by
      rw [hBeq]
      exact Q.first_mem_support
    cases B with
    | inl P =>
      have := P.support_subset_symmDiff hfs
      rw [Finset.mem_symmDiff] at this
      tauto
    | inr R =>
      have := R.support_subset_symmDiff hfs
      rw [Finset.mem_symmDiff] at this
      tauto
  refine ⟨hQ', ?_⟩
  -- the step conditions of `inl Q :: D₁.blocks`
  have hconds : SideBlock.StepConds G s s'
      (FPDeformation.cons (Sum.inl Q) (FPDeformation.ofToggle Q D₁) hQ').blocks := by
    intro pre B post hdec
    change Sum.inl Q :: (D₁.blocks.map (SideBlock.ofToggle Q)) = pre ++ B :: post at hdec
    rcases List.cons_eq_append_iff.1 hdec with ⟨rfl, hrest⟩ | ⟨pre', rfl, hrest⟩
    · -- the block `Q` itself
      obtain ⟨rfl, rfl⟩ := List.cons.inj hrest
      refine ⟨?_, ?_⟩
      · intro p hp v hv
        rw [SideBlock.other_inl, SideBlock.listToggle₂_nil, symmDiff_empty_right'] at hv
        exact (hc p hp).2 v hv
      · intro p hp v hv
        rw [SideBlock.other_inl, SideBlock.listToggle₂_map_ofToggle] at hv
        rcases Finset.mem_symmDiff.1 hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
        · apply OddBlock.cond_of_not_mem_separators hs' Q hv1 ?_ p hp
          intro hvS
          exact hv2 ((D₁.mem_toggle₂).2 ⟨R₀, hR₀, hsepR v hvS⟩)
        · have hv3 : v ∈ s.2 := by
            rcases Finset.mem_symmDiff.1 (D₁.toggle₂_subset hv1) with ⟨h, -⟩ | ⟨h, -⟩
            · exact h
            · exact absurd h hv2
          exact (hc p hp).2 v hv3
    · -- a block of the transported deformation
      obtain ⟨pre₁, B₁, post₁, hL, rfl, rfl, rfl⟩ := map_ofToggle_decomp Q hrest
      obtain ⟨hF, hB⟩ := Palindromic.stepConds hs₁ hs' hD₁ pre₁ B₁ post₁ hL
      cases B₁ with
      | inl P =>
        refine ⟨?_, ?_⟩
        · rw [SideBlock.word_ofToggle, ofToggle_inl, SideBlock.other_inl,
            SideBlock.listToggle₂_cons_inl, SideBlock.listToggle₂_map_ofToggle]
          exact hF
        · rw [SideBlock.word_ofToggle, other_ofToggle_inl]
          exact hB
      | inr R =>
        refine ⟨?_, ?_⟩
        · rw [SideBlock.word_ofToggle, ofToggle_inr, SideBlock.other_inr,
            SideBlock.listToggle₁_cons_inl, SideBlock.listToggle₁_map_ofToggle, ← symmDiff_assoc]
          exact hF
        · rw [SideBlock.word_ofToggle, other_ofToggle_inr]
          exact hB
  refine ⟨Palindromic.of_stepConds hs hs' _ hconds, ?_⟩
  -- the parity
  have hT : G.crossCount D₁.toggle Q.support % 2 = 1 := by
    rw [toggle_eq_tog]
    have key := SideBlock.crossCount_tog_mod_two_of_unique D₁.nodup hR₀ (Z := Q.support)
      (fun B hB hne => by
        cases B with
        | inl P =>
          exact SideBlock.crossCount_support_mod_two (Sum.inl P) (Q.stepIndep_word_toggled P)
        | inr R =>
          have hRne : R ≠ R₀ := fun h => hne (by rw [h])
          have hno : R.support ∩ Q.separators s'.2 = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro w hw
            obtain ⟨hwR, hwS⟩ := Finset.mem_inter.1 hw
            rcases OddBlock.eq_or_disjoint R R₀ with h | h
            · exact hRne h
            · exact Finset.disjoint_left.1 h hwR (hsepR w hwS)
          exact SideBlock.crossCount_support_mod_two (Sum.inr R)
            (stepIndep_word_of_inr hs hs' Q hQ hD₁ hB hno))
    rw [key]
    exact OddBlock.crossCount_separator_block_mod_two hclaw hs hs' Q hQ hW' hsep hu huS
  have hQC : G.crossCount Q.support (s.1 ∪ s.2) % 2 = 1 := by
    rw [OddBlock.crossCount_carrier_mod_two hclaw hs hs' Q, hW]
  have hd := Q.disjoint_support_snd hs hQ
  have htog : (FPDeformation.cons (Sum.inl Q) (FPDeformation.ofToggle Q D₁) hQ').toggle =
      symmDiff Q.support D₁.toggle := by
    simp only [toggle, toggle₁_cons_inl, toggle₂_cons_inl, ofToggle_toggle₁, ofToggle_toggle₂,
      symmDiff_assoc]
  unfold IsOdd
  rw [htog]
  show Odd (G.crossCount (symmDiff Q.support D₁.toggle) (s.1 ∪ s.2)) ↔
    Odd (G.crossCount D₁.toggle (symmDiff s.1 Q.support ∪ s.2))
  rw [OddBlock.toggle_union Q hd, Nat.odd_iff, Nat.odd_iff, crossCount_symmDiff_left_mod_two,
    crossCount_symmDiff_right_mod_two]
  omega

/-! ### The lift lemma -/

/-- **The lift lemma** (package T3-24; v1 has no counterpart: it replaces the rerouting step
L1155-1172 and the concatenation validity of Lemma 9(i), L1880-1915).

Let `G` be claw-free, `s = (A, B)` and `s' = (A', B')` the colouring classes of two even holes,
and `Q` a side-1 block of `(s; s')` which runs from `s`, with `|Q ∩ W| = 1`, `|Q ∩ W'|` even, where
`W = matchedW s s' ∪ crossedW s s'` and `W' = matchedW s' s ∪ crossedW s' s`, and all of whose
separators in `s'.2` lie in one component of `G[s.2 ⊕ s'.2]` (`hsep`; this is the conclusion of the
separator lemma `OddBlock.separators_sameComponent`).  Let `D₁` be a palindromic deformation at the
intermediate state `(s.1 ⊕ Q, s.2; s')`.  Then one of the following holds:

* (a) `ofToggle Q D₁` is palindromic at `(s, s')`, and it is odd iff `D₁` is;
* (b) `Q` is not the support of a block of `ofToggle Q D₁`, and `cons (inl Q) (ofToggle Q D₁)` is
  palindromic at `(s, s')`, and it is odd iff `D₁` is.

Here `IsOdd` is the oddness of `c(T, C)`, with `T` the toggle and `C` the carrier of the start
state, so that `D₁.IsOdd` is `Odd c(T₁, C ⊕ Q)`.

The split is on whether a side-2 block of `D₁` contains a separator of `Q` in `s'.2`: if none does,
(a) holds (`lift_of_no_separator`); if one does, it is unique by `hsep`, and (b) holds
(`lift_cons_of_separator`).  The conclusion is a disjunction; it is not claimed that exactly one of
(a), (b) holds.  No `Fintype` hypothesis is needed. -/
theorem lift (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s)
    (hW : (Q.support ∩ (G.matchedW s s' ∪ G.crossedW s s')).card = 1)
    (hW' : Even (Q.support ∩ (G.matchedW s' s ∪ G.crossedW s' s)).card)
    (hsep : ∀ u ∈ Q.separators s'.2, ∀ v ∈ Q.separators s'.2,
      v ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u)
    (D₁ : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') (hD₁ : D₁.Palindromic) :
    ((FPDeformation.ofToggle Q D₁).Palindromic ∧
        ((FPDeformation.ofToggle Q D₁).IsOdd ↔ D₁.IsOdd)) ∨
      ∃ hQ' : SideBlock.support (Sum.inl Q : G.SideBlock s s') ∉
          (FPDeformation.ofToggle Q D₁).blocks.map SideBlock.support,
        (FPDeformation.cons (.inl Q) (FPDeformation.ofToggle Q D₁) hQ').Palindromic ∧
          ((FPDeformation.cons (.inl Q) (FPDeformation.ofToggle Q D₁) hQ').IsOdd ↔ D₁.IsOdd) := by
  classical
  by_cases h : ∃ R : G.OddBlock s.2 s'.2, Sum.inr R ∈ D₁.blocks ∧
      (R.support ∩ Q.separators s'.2).Nonempty
  · obtain ⟨R₀, hR₀, hne⟩ := h
    exact Or.inr (lift_cons_of_separator hclaw hs hs' Q hQ hW hW' hsep D₁ hD₁ hR₀ hne)
  · refine Or.inl (lift_of_no_separator hs hs' Q hQ D₁ hD₁ (fun R hR => ?_))
    by_contra hne
    exact h ⟨R, hR, Finset.nonempty_iff_ne_empty.2 hne⟩

end FPDeformation

end SimpleGraph
