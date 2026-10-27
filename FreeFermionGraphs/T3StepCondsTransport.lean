import FreeFermionGraphs.T3PalindromicCriterion

/-!
# Operations on lists of side blocks which preserve the step conditions

This module collects the list operations used to build palindromic fixed-pairing deformations out
of others (see `FreeFermionGraphs.T3ToggleStable`).  All of them are statements about
`SimpleGraph.SideBlock.StepConds` (`FreeFermionGraphs.T3PalindromicCriterion`), which by the
criterion `FPDeformation.palindromic_iff_stepConds` is the palindromic property.

* `SideBlock.listToggle₁_append`, `listToggle₁_reverse`, `listToggle₁_map_of_support` (and the
  `₂` versions): the toggle of a concatenation, a reversal, and a retyping of blocks which keeps
  supports and sides.
* `SideBlock.stepIndep_listToggle₁` (and `₂`): if the steps of `w` separate no vertex of any block
  of `L`, they separate no vertex of its toggle.
* `SideBlock.stepConds_filter`: a sublist `L.filter p` of a list `L` with the step conditions has
  them, provided the steps of each selected block separate no vertex of an unselected block of `L`.
* `SideBlock.stepConds_append`: two lists with the step conditions whose blocks do not separate each
  other can be concatenated.
* `SideBlock.stepConds_map_untoggled`: retyping the blocks of a list to the pair of states
  `(s.1 ⊕ T₁, s.2 ⊕ T₂)`, `(s'.1 ⊕ T₁, s'.2 ⊕ T₂)`, keeping words and order, keeps the step
  conditions when the steps of each block separate no vertex of the toggle of the other side.
* `SideBlock.stepConds_map_reverse`: retyping the blocks to the same pair of states, reversing
  their words and the order of the list, keeps the step conditions when each block `B` satisfies
  the agreement property `SideBlock.Agree`: on the vertices separated by a step of `B`, the class
  `cls s B ⊕ T` agrees with `cls s' B` and `cls s' B ⊕ T` agrees with `cls s B`.

Claw-freeness is not used anywhere in this module.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The symmetric difference with the empty finset on the left (stated for `∅`, not `⊥`). -/
@[simp] theorem symmDiff_empty_left' [DecidableEq V] (A : Finset V) : symmDiff ∅ A = A :=
  bot_symmDiff A

namespace SideBlock

variable [DecidableEq V] {s s' t t' : Finset V × Finset V}

/-! ### Toggle algebra -/

theorem listToggle₁_append (a b : List (G.SideBlock s s')) :
    listToggle₁ (a ++ b) = symmDiff (listToggle₁ a) (listToggle₁ b) := by
  induction a with
  | nil => simp
  | cons B a ih =>
    cases B with
    | inl P => rw [List.cons_append, listToggle₁_cons_inl, ih, listToggle₁_cons_inl, symmDiff_assoc]
    | inr P => rw [List.cons_append, listToggle₁_cons_inr, ih, listToggle₁_cons_inr]

theorem listToggle₂_append (a b : List (G.SideBlock s s')) :
    listToggle₂ (a ++ b) = symmDiff (listToggle₂ a) (listToggle₂ b) := by
  induction a with
  | nil => simp
  | cons B a ih =>
    cases B with
    | inl P => rw [List.cons_append, listToggle₂_cons_inl, ih, listToggle₂_cons_inl]
    | inr P => rw [List.cons_append, listToggle₂_cons_inr, ih, listToggle₂_cons_inr, symmDiff_assoc]

theorem listToggle₁_reverse (L : List (G.SideBlock s s')) :
    listToggle₁ L.reverse = listToggle₁ L := by
  induction L with
  | nil => rfl
  | cons B L ih =>
    rw [List.reverse_cons, listToggle₁_append, ih]
    cases B with
    | inl P =>
      have h1 : listToggle₁ ([Sum.inl P] : List (G.SideBlock s s')) = P.support := by
        rw [listToggle₁_cons_inl]; simp
      rw [h1, listToggle₁_cons_inl, symmDiff_comm]
    | inr P =>
      have h1 : listToggle₁ ([Sum.inr P] : List (G.SideBlock s s')) = ∅ := by
        rw [listToggle₁_cons_inr]; rfl
      rw [h1, listToggle₁_cons_inr]; simp

theorem listToggle₂_reverse (L : List (G.SideBlock s s')) :
    listToggle₂ L.reverse = listToggle₂ L := by
  induction L with
  | nil => rfl
  | cons B L ih =>
    rw [List.reverse_cons, listToggle₂_append, ih]
    cases B with
    | inl P =>
      have h1 : listToggle₂ ([Sum.inl P] : List (G.SideBlock s s')) = ∅ := by
        rw [listToggle₂_cons_inl]; rfl
      rw [h1, listToggle₂_cons_inl]; simp
    | inr P =>
      have h1 : listToggle₂ ([Sum.inr P] : List (G.SideBlock s s')) = P.support := by
        rw [listToggle₂_cons_inr]; simp
      rw [h1, listToggle₂_cons_inr, symmDiff_comm]

/-- Retyping the blocks of a list by a map which keeps supports and sides keeps the side-1
toggle. -/
theorem listToggle₁_map_of_support (f : G.SideBlock s s' → G.SideBlock t t')
    (L : List (G.SideBlock s s'))
    (h : ∀ B ∈ L, (f B).support = B.support ∧ (f B).isLeft = B.isLeft) :
    listToggle₁ (L.map f) = listToggle₁ L := by
  induction L with
  | nil => rfl
  | cons B L ih =>
    rw [List.map_cons]
    obtain ⟨h1, h2⟩ := h B (List.mem_cons_self ..)
    have ih' := ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    cases B with
    | inl P =>
      obtain ⟨P', hP'⟩ : ∃ P', f (Sum.inl P) = Sum.inl P' := Sum.isLeft_iff.1 (by simpa using h2)
      rw [hP'] at h1 ⊢
      rw [listToggle₁_cons_inl, listToggle₁_cons_inl, ih']
      simp only [support_inl] at h1
      rw [h1]
    | inr Q =>
      obtain ⟨Q', hQ'⟩ : ∃ Q', f (Sum.inr Q) = Sum.inr Q' := by
        cases hfB : f (Sum.inr Q) with
        | inl P' => rw [hfB] at h2; simp at h2
        | inr Q' => exact ⟨Q', rfl⟩
      rw [hQ', listToggle₁_cons_inr, listToggle₁_cons_inr, ih']

theorem listToggle₂_map_of_support (f : G.SideBlock s s' → G.SideBlock t t')
    (L : List (G.SideBlock s s'))
    (h : ∀ B ∈ L, (f B).support = B.support ∧ (f B).isLeft = B.isLeft) :
    listToggle₂ (L.map f) = listToggle₂ L := by
  induction L with
  | nil => rfl
  | cons B L ih =>
    rw [List.map_cons]
    obtain ⟨h1, h2⟩ := h B (List.mem_cons_self ..)
    have ih' := ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    cases B with
    | inl P =>
      obtain ⟨P', hP'⟩ : ∃ P', f (Sum.inl P) = Sum.inl P' := Sum.isLeft_iff.1 (by simpa using h2)
      rw [hP', listToggle₂_cons_inl, listToggle₂_cons_inl, ih']
    | inr Q =>
      obtain ⟨Q', hQ'⟩ : ∃ Q', f (Sum.inr Q) = Sum.inr Q' := by
        cases hfB : f (Sum.inr Q) with
        | inl P' => rw [hfB] at h2; simp at h2
        | inr Q' => exact ⟨Q', rfl⟩
      rw [hQ'] at h1 ⊢
      rw [listToggle₂_cons_inr, listToggle₂_cons_inr, ih']
      simp only [support_inr] at h1
      rw [h1]

/-- If the steps of `w` separate no vertex of any block of `L`, they separate no vertex of the
side-1 toggle of `L`. -/
theorem stepIndep_listToggle₁ {w : List (V × V)} (L : List (G.SideBlock s s'))
    (h : ∀ B ∈ L, StepIndep G w B.support) : StepIndep G w (listToggle₁ L) := by
  induction L with
  | nil => exact StepIndep.empty
  | cons B L ih =>
    have ih' := ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    cases B with
    | inl P =>
      rw [listToggle₁_cons_inl]
      exact (h _ (List.mem_cons_self ..)).symmDiff' ih'
    | inr Q => rw [listToggle₁_cons_inr]; exact ih'

theorem stepIndep_listToggle₂ {w : List (V × V)} (L : List (G.SideBlock s s'))
    (h : ∀ B ∈ L, StepIndep G w B.support) : StepIndep G w (listToggle₂ L) := by
  induction L with
  | nil => exact StepIndep.empty
  | cons B L ih =>
    have ih' := ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    cases B with
    | inl P => rw [listToggle₂_cons_inl]; exact ih'
    | inr Q =>
      rw [listToggle₂_cons_inr]
      exact (h _ (List.mem_cons_self ..)).symmDiff' ih'

/-! ### The class tested and the toggle of the other side, uniformly -/

/-- The class of the state `t` against which the steps of `B` are tested: the second class for a
side-1 block, the first class for a side-2 block. -/
def cls (t : Finset V × Finset V) (B : G.SideBlock s s') : Finset V :=
  if B.isLeft then t.2 else t.1

/-- The toggle of the other side of a list of blocks, as seen by `B`. -/
def tgl (B : G.SideBlock s s') (L : List (G.SideBlock s s')) : Finset V :=
  if B.isLeft then listToggle₂ L else listToggle₁ L

/-- The toggle of the other side, as seen by `B`, for a pair of toggles `(T₁, T₂)`. -/
def tgOf (T₁ T₂ : Finset V) (B : G.SideBlock s s') : Finset V :=
  if B.isLeft then T₂ else T₁

theorem other_eq (t : Finset V × Finset V) (B : G.SideBlock s s') (L : List (G.SideBlock s s')) :
    other t B L = symmDiff (cls t B) (tgl B L) := by
  cases B <;> simp [cls, tgl]

/-! ### Sublists -/

/-- A sublist `L.filter p` of a list with the step conditions has the step conditions, provided the
steps of each selected block separate no vertex of an unselected block of `L`. -/
theorem stepConds_filter {bs : List (G.SideBlock s s')} (hnd : (bs.map SideBlock.support).Nodup)
    (h : StepConds G s s' bs) (p : G.SideBlock s s' → Bool)
    (hind : ∀ B ∈ bs, p B = true → ∀ C ∈ bs, p C = false → StepIndep G B.word C.support) :
    StepConds G s s' (bs.filter p) := by
  intro pre B post hdec
  have hBmem : B ∈ bs.filter p := by
    rw [hdec]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  rw [List.mem_filter] at hBmem
  obtain ⟨l₁, l₂, hbs, hl₁, hl₂⟩ : ∃ l₁ l₂, bs = l₁ ++ B :: l₂ ∧ l₁.filter p = pre ∧
      l₂.filter p = post := by
    have key : ∀ (l : List (G.SideBlock s s')) (pre post : List (G.SideBlock s s')),
        l.filter p = pre ++ B :: post →
        ∃ l₁ l₂, l = l₁ ++ B :: l₂ ∧ l₁.filter p = pre ∧ l₂.filter p = post := by
      intro l
      induction l with
      | nil => intro pre post hh; simp at hh
      | cons a l ih =>
        intro pre post hh
        by_cases hpa : p a = true
        · rw [List.filter_cons_of_pos hpa] at hh
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hh
            obtain ⟨rfl, hh⟩ := hh
            exact ⟨[], l, rfl, rfl, by simpa using hh⟩
          | cons b pre' =>
            simp only [List.cons_append, List.cons.injEq] at hh
            obtain ⟨rfl, hh⟩ := hh
            obtain ⟨l₁, l₂, hl, h1, h2⟩ := ih pre' post hh
            exact ⟨a :: l₁, l₂, by rw [hl]; rfl, by rw [List.filter_cons_of_pos hpa, h1], h2⟩
        · have hpa' : p a = false := by simpa using hpa
          rw [List.filter_cons_of_neg hpa] at hh
          obtain ⟨l₁, l₂, hl, h1, h2⟩ := ih pre post hh
          exact ⟨a :: l₁, l₂, by rw [hl]; rfl, by rw [List.filter_cons_of_neg hpa, h1], h2⟩
    exact key bs pre post hdec
  subst hl₁ hl₂
  have hnd' := hnd
  rw [hbs] at hnd'
  obtain ⟨hnd₁, hnd₂, -, -⟩ := FPDeformation.nodup_split hnd'
  obtain ⟨hf, hb⟩ := h l₁ B l₂ hbs
  have hBbs : B ∈ bs := hBmem.1
  have hsub₁ : ∀ C ∈ l₁, C ∈ bs := fun C hC => by rw [hbs]; exact List.mem_append_left _ hC
  have hsub₂ : ∀ C ∈ l₂, C ∈ bs := fun C hC => by
    rw [hbs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hC)
  have hnd₁f : ((l₁.filter p).map SideBlock.support).Nodup :=
    hnd₁.sublist ((List.filter_sublist).map _)
  have hnd₂f : ((l₂.filter p).map SideBlock.support).Nodup :=
    hnd₂.sublist ((List.filter_sublist).map _)
  -- membership in the toggles of a filtered list
  have hmem : ∀ (l : List (G.SideBlock s s')), (l.map SideBlock.support).Nodup →
      (∀ C ∈ l, C ∈ bs) → ∀ v : V, ¬ StepIndep G B.word {v} →
      ((v ∈ tgl B l) ↔ (v ∈ tgl B (l.filter p))) := by
    intro l hl hlbs v hv
    have hndf : ((l.filter p).map SideBlock.support).Nodup :=
      hl.sublist ((List.filter_sublist).map _)
    have hsel : ∀ C ∈ l, v ∈ C.support → p C = true := by
      intro C hC hvC
      by_contra hpC
      have hpC' : p C = false := by simpa using hpC
      apply hv
      exact (hind B hBbs hBmem.2 C (hlbs C hC) hpC').mono (by simpa using hvC)
    by_cases hl' : B.isLeft = true
    · simp only [tgl, hl', if_true]
      rw [mem_listToggle₂ hl, mem_listToggle₂ hndf]
      constructor
      · rintro ⟨Q, hQ, hvQ⟩
        exact ⟨Q, List.mem_filter.2 ⟨hQ, hsel _ hQ hvQ⟩, hvQ⟩
      · rintro ⟨Q, hQ, hvQ⟩
        exact ⟨Q, (List.mem_filter.1 hQ).1, hvQ⟩
    · have hl'' : B.isLeft = false := by simpa using hl'
      simp only [tgl, hl'', Bool.false_eq_true, if_false]
      rw [mem_listToggle₁ hl, mem_listToggle₁ hndf]
      constructor
      · rintro ⟨Q, hQ, hvQ⟩
        exact ⟨Q, List.mem_filter.2 ⟨hQ, hsel _ hQ hvQ⟩, hvQ⟩
      · rintro ⟨Q, hQ, hvQ⟩
        exact ⟨Q, (List.mem_filter.1 hQ).1, hvQ⟩
  constructor
  · refine hf.congr (fun v hv => ?_)
    rw [other_eq, other_eq, Finset.mem_symmDiff, Finset.mem_symmDiff, hmem l₁ hnd₁ hsub₁ v hv]
  · refine hb.congr (fun v hv => ?_)
    rw [other_eq, other_eq, Finset.mem_symmDiff, Finset.mem_symmDiff, hmem l₂ hnd₂ hsub₂ v hv]

/-! ### Concatenation -/

/-- Two lists with the step conditions, whose blocks do not separate each other, concatenate to a
list with the step conditions. -/
theorem stepConds_append {X Y : List (G.SideBlock s s')} (hX : StepConds G s s' X)
    (hY : StepConds G s s' Y)
    (hXY : ∀ B ∈ X, ∀ C ∈ Y, StepIndep G B.word C.support ∧ StepIndep G C.word B.support) :
    StepConds G s s' (X ++ Y) := by
  intro pre B post hdec
  -- the case where `B` lies in `Y`
  have hcaseY : ∀ as : List (G.SideBlock s s'), pre = X ++ as → Y = as ++ B :: post →
      StepIndep G B.word (other s B pre) ∧ StepIndep G B.word (other s' B post) := by
    intro as hpre hYas
    obtain ⟨hf, hb⟩ := hY as B post hYas
    have hBY : B ∈ Y := by rw [hYas]; exact List.mem_append_right _ (List.mem_cons_self ..)
    refine ⟨?_, hb⟩
    have hTX : ∀ C ∈ X, StepIndep G B.word C.support := fun C hC => (hXY C hC B hBY).2
    have h1 : StepIndep G B.word (tgl B X) := by
      unfold tgl
      split_ifs
      · exact stepIndep_listToggle₂ X hTX
      · exact stepIndep_listToggle₁ X hTX
    rw [other_eq] at hf ⊢
    rw [hpre]
    have : tgl B (X ++ as) = symmDiff (tgl B X) (tgl B as) := by
      unfold tgl
      split_ifs
      · exact listToggle₂_append _ _
      · exact listToggle₁_append _ _
    rw [this, ← symmDiff_assoc, symmDiff_right_comm]
    exact hf.symmDiff' h1
  rcases List.append_eq_append_iff.1 hdec with ⟨as, hpre, hYas⟩ | ⟨bs, hXbs, hBpost⟩
  · exact hcaseY as hpre hYas
  · cases bs with
    | nil =>
      simp only [List.nil_append] at hBpost
      refine hcaseY [] (by simpa using hXbs.symm) (by simpa using hBpost.symm)
    | cons B' bs' =>
      simp only [List.cons_append, List.cons.injEq] at hBpost
      obtain ⟨rfl, hpost⟩ := hBpost
      obtain ⟨hf, hb⟩ := hX pre B bs' hXbs
      have hBX : B ∈ X := by rw [hXbs]; exact List.mem_append_right _ (List.mem_cons_self ..)
      refine ⟨hf, ?_⟩
      have hTY : ∀ C ∈ Y, StepIndep G B.word C.support := fun C hC => (hXY B hBX C hC).1
      have h1 : StepIndep G B.word (tgl B Y) := by
        unfold tgl
        split_ifs
        · exact stepIndep_listToggle₂ Y hTY
        · exact stepIndep_listToggle₁ Y hTY
      rw [other_eq] at hb ⊢
      rw [hpost]
      have : tgl B (bs' ++ Y) = symmDiff (tgl B bs') (tgl B Y) := by
        unfold tgl
        split_ifs
        · exact listToggle₂_append _ _
        · exact listToggle₁_append _ _
      rw [this, ← symmDiff_assoc]
      exact hb.symmDiff' h1

/-! ### Retyping along a toggle, without reversal -/

/-- **Retyping along a toggle which the blocks do not touch.**  Let `L` have the step conditions
from the states `s`, `s'`, and let `f` map the blocks of `L` to side blocks from the states `t`,
`t'`, where `t = (s.1 ⊕ T₁, s.2 ⊕ T₂)` and `t' = (s'.1 ⊕ T₁, s'.2 ⊕ T₂)`, keeping supports, sides
and words.  If the steps of each block separate no vertex of the toggle `tgOf T₁ T₂ B` of the side
it is tested against, the image list has the step conditions from `t`, `t'`. -/
theorem stepConds_map_untoggled {L : List (G.SideBlock s s')} (h : StepConds G s s' L)
    (f : G.SideBlock s s' → G.SideBlock t t') (T₁ T₂ : Finset V)
    (ht₁ : t.1 = symmDiff s.1 T₁) (ht₂ : t.2 = symmDiff s.2 T₂)
    (ht₁' : t'.1 = symmDiff s'.1 T₁) (ht₂' : t'.2 = symmDiff s'.2 T₂)
    (hf : ∀ B ∈ L, (f B).support = B.support ∧ (f B).isLeft = B.isLeft ∧ (f B).word = B.word)
    (hT : ∀ B ∈ L, StepIndep G B.word (tgOf T₁ T₂ B)) :
    StepConds G t t' (L.map f) := by
  intro pre'' X post'' hdec
  obtain ⟨l₁, l₂, hL, hl₁, hl₂⟩ := List.map_eq_append_iff.1 hdec
  obtain ⟨a, l, hl₂', haX, hlpost⟩ := List.map_eq_cons_iff.1 hl₂
  subst hl₂' haX hl₁ hlpost
  obtain ⟨hF, hB⟩ := h l₁ a l hL
  have hsub₁ : ∀ C ∈ l₁, C ∈ L := fun C hC => by rw [hL]; exact List.mem_append_left _ hC
  have hsub₂ : ∀ C ∈ l, C ∈ L := fun C hC => by
    rw [hL]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hC)
  have haL : a ∈ L := by rw [hL]; exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨hfs, hfl, hfw⟩ := hf a haL
  have hm₁ := fun (l' : List (G.SideBlock s s')) (hl' : ∀ C ∈ l', C ∈ L) =>
    (⟨listToggle₁_map_of_support f l' (fun C hC => ⟨(hf C (hl' C hC)).1, (hf C (hl' C hC)).2.1⟩),
      listToggle₂_map_of_support f l' (fun C hC => ⟨(hf C (hl' C hC)).1, (hf C (hl' C hC)).2.1⟩)⟩ :
      listToggle₁ (l'.map f) = listToggle₁ l' ∧ listToggle₂ (l'.map f) = listToggle₂ l')
  have hcls : cls t (f a) = symmDiff (cls s a) (tgOf T₁ T₂ a) := by
    unfold cls tgOf
    rw [hfl]
    split_ifs
    · exact ht₂
    · exact ht₁
  have hcls' : cls t' (f a) = symmDiff (cls s' a) (tgOf T₁ T₂ a) := by
    unfold cls tgOf
    rw [hfl]
    split_ifs
    · exact ht₂'
    · exact ht₁'
  have htgl : ∀ l' : List (G.SideBlock s s'), (∀ C ∈ l', C ∈ L) →
      tgl (f a) (l'.map f) = tgl a l' := by
    intro l' hl'
    unfold tgl
    rw [hfl, (hm₁ l' hl').1, (hm₁ l' hl').2]
  rw [hfw, other_eq, other_eq, hcls, hcls', htgl _ hsub₁, htgl _ hsub₂]
  rw [other_eq] at hF hB
  refine ⟨?_, ?_⟩
  · rw [symmDiff_right_comm]
    exact hF.symmDiff' (hT a haL)
  · rw [symmDiff_right_comm]
    exact hB.symmDiff' (hT a haL)

/-! ### Retyping along a toggle, with reversal -/

theorem mem_symmDiff_congr {X X' Y : Finset V} {v : V} (h : v ∈ X ↔ v ∈ X') :
    v ∈ symmDiff X Y ↔ v ∈ symmDiff X' Y := by
  simp only [Finset.mem_symmDiff, h]

/-- **Agreement of the two classes along a toggle.**  For the block `B` and the toggle pair
`(T₁, T₂)`: on every vertex separated by a step of `B`, the class `cls s B ⊕ T` (the class of the
forward end state) is the class `cls s' B`, and the class `cls s' B ⊕ T` (the class of the backward
end state) is the class `cls s B`.  This is what makes a block of a palindromic deformation with
toggle `T` run in the opposite direction after the deformation. -/
def Agree (s s' : Finset V × Finset V) (T₁ T₂ : Finset V) (B : G.SideBlock s s') : Prop :=
  ∀ v, ¬ StepIndep G B.word {v} →
    (v ∈ symmDiff (cls s B) (tgOf T₁ T₂ B) ↔ v ∈ cls s' B) ∧
    (v ∈ symmDiff (cls s' B) (tgOf T₁ T₂ B) ↔ v ∈ cls s B)

/-- **Retyping along a toggle, with reversal of words and of the order.**  Let `L` have the step
conditions from `s`, `s'`, and let `f` map the blocks of `L` to side blocks from the states
`t = (s.1 ⊕ T₁, s.2 ⊕ T₂)`, `t' = (s'.1 ⊕ T₁, s'.2 ⊕ T₂)`, keeping supports and sides and reversing
the words.  If every block of `L` satisfies the agreement property `Agree`, the image of the
*reversed* list has the step conditions from `t`, `t'`. -/
theorem stepConds_map_reverse {L : List (G.SideBlock s s')} (h : StepConds G s s' L)
    (f : G.SideBlock s s' → G.SideBlock t t') (T₁ T₂ : Finset V)
    (ht₁ : t.1 = symmDiff s.1 T₁) (ht₂ : t.2 = symmDiff s.2 T₂)
    (ht₁' : t'.1 = symmDiff s'.1 T₁) (ht₂' : t'.2 = symmDiff s'.2 T₂)
    (hf : ∀ B ∈ L, (f B).support = B.support ∧ (f B).isLeft = B.isLeft ∧
      (f B).word = reverseWord B.word)
    (hA : ∀ B ∈ L, Agree s s' T₁ T₂ B) :
    StepConds G t t' (L.reverse.map f) := by
  intro pre'' X post'' hdec
  obtain ⟨l₁, l₂, hL, hl₁, hl₂⟩ := List.map_eq_append_iff.1 hdec
  obtain ⟨a, l, hl₂', haX, hlpost⟩ := List.map_eq_cons_iff.1 hl₂
  subst hl₂' haX hl₁ hlpost
  have hL' : L = l.reverse ++ a :: l₁.reverse := by
    have := List.reverse_eq_append_iff.1 hL
    rw [this]
    simp
  obtain ⟨hF, hB⟩ := h l.reverse a l₁.reverse hL'
  have hsub₁ : ∀ C ∈ l₁, C ∈ L := fun C hC => by
    rw [hL']
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_reverse.2 hC))
  have hsub₂ : ∀ C ∈ l, C ∈ L := fun C hC => by
    rw [hL']; exact List.mem_append_left _ (List.mem_reverse.2 hC)
  have haL : a ∈ L := by rw [hL']; exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨hfs, hfl, hfw⟩ := hf a haL
  have hm₁ := fun (l' : List (G.SideBlock s s')) (hl' : ∀ C ∈ l', C ∈ L) =>
    (⟨listToggle₁_map_of_support f l' (fun C hC => ⟨(hf C (hl' C hC)).1, (hf C (hl' C hC)).2.1⟩),
      listToggle₂_map_of_support f l' (fun C hC => ⟨(hf C (hl' C hC)).1, (hf C (hl' C hC)).2.1⟩)⟩ :
      listToggle₁ (l'.map f) = listToggle₁ l' ∧ listToggle₂ (l'.map f) = listToggle₂ l')
  have hcls : cls t (f a) = symmDiff (cls s a) (tgOf T₁ T₂ a) := by
    unfold cls tgOf
    rw [hfl]
    split_ifs
    · exact ht₂
    · exact ht₁
  have hcls' : cls t' (f a) = symmDiff (cls s' a) (tgOf T₁ T₂ a) := by
    unfold cls tgOf
    rw [hfl]
    split_ifs
    · exact ht₂'
    · exact ht₁'
  have htgl : ∀ l' : List (G.SideBlock s s'), (∀ C ∈ l', C ∈ L) →
      tgl (f a) (l'.map f) = tgl a l' := by
    intro l' hl'
    unfold tgl
    rw [hfl, (hm₁ l' hl').1, (hm₁ l' hl').2]
  have htgrev : ∀ l' : List (G.SideBlock s s'), tgl a l'.reverse = tgl a l' := by
    intro l'
    unfold tgl
    rw [listToggle₁_reverse, listToggle₂_reverse]
  have hag := hA a haL
  rw [hfw, other_eq, other_eq, hcls, hcls', htgl _ hsub₁, htgl _ hsub₂]
  simp only [stepIndep_reverseWord_iff]
  rw [other_eq, htgrev] at hF hB
  refine ⟨?_, ?_⟩
  · -- the forward run of the new deformation uses the backward conditions of `a`
    refine hB.congr (fun v hv => ?_)
    obtain ⟨h1, -⟩ := hag v hv
    exact (mem_symmDiff_congr h1).symm
  · refine hF.congr (fun v hv => ?_)
    obtain ⟨-, h2⟩ := hag v hv
    exact (mem_symmDiff_congr h2).symm

end SideBlock

end SimpleGraph
