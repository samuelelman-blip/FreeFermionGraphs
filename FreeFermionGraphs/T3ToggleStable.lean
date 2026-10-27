import FreeFermionGraphs.T3StepCondsTransport

/-!
# Toggle stability of palindromic deformations

Let `D` and `D'` be palindromic fixed-pairing-type deformations (arXiv 2305.15625 v1, Definition 19
`definition:fixedpairingtypedeformation`, L978-994) of the same pair of hole-class states
`s = (C_a, C_b)`, `s' = (C'_c, C'_d)`.  The main result is

* `FPDeformation.toggle_stable`: there is a palindromic deformation `D''` of the pair of end
  states `(D.fwdEnd, D.bwdEnd)` of `D` with the same toggle as `D'` and the same parity as `D'`:
  `D''.toggle = D'.toggle` and `D''.IsOdd ↔ D'.IsOdd`.

This is the heart of the pairing involution which v1 needs and does not argue at L1237-1241 ("we fix
a deformation to cancel terms pairwise"): after toggling `(C, C')` to `(C ⊕ T, C' ⊕ T)` along the
toggle `T` of an odd palindromic `D`, the toggle of any palindromic deformation of `(C, C')` is
again the toggle of a palindromic deformation of the new pair.  For `D' = D` the construction is the
reverse deformation, so the toggle `T` is again a toggle at the toggled pair.  The statement is new
and is not in v1.

## Construction

`D''` has the following blocks: first the blocks of `D'` which are blocks of `D`, retyped as blocks
of `(D.fwdEnd, D.bwdEnd)` and reversed (`OddBlock.retypeToggled`), in reverse `D'`-order; then the
blocks of `D'` which are not blocks of `D`, retyped untoggled (`OddBlock.retypeUntoggled`), in
`D'`-order.

## Proof

* **Key lemma** (`FPDeformation.not_interacts_of_mem_not_mem`): no block of `D' ∖ D` interacts with
  a block of `D`, in either direction.  If a block `Q` of `D'` interacts with a block `R` of
  `D`, then `R` is a block of `D'` (direction lemma in `D'`, `interacts_mem_of_mem`); by symmetry of
  interaction in `D'` (`interacts_symm`), `R` interacts with `Q`, and then `Q` is a block of `D`
  (direction lemma in `D`).
* **Validity** by the step-condition criterion (`FPDeformation.palindromic_iff_stepConds`):
  the filtered lists `D'.blocks ∩ D` and `D'.blocks ∖ D` keep the step conditions
  (`SideBlock.stepConds_filter`); the first, reversed and retyped, keeps them
  (`SideBlock.stepConds_map_reverse`, using `agree_of_mem`: a block `B` of `D` satisfies the
  agreement property: on a vertex separated by a step of `B` the class of `s` toggled by the
  other-side toggle of `D` agrees with the class of `s'`); the second, retyped untoggled, keeps them
  (`SideBlock.stepConds_map_untoggled`); and the concatenation keeps them since the two lists do not
  separate each other (`SideBlock.stepConds_append`).
* **Parity** (`FPDeformation.crossCount_toggle_toggle_mod_two`): `c(T', T)` is even, since the
  blocks common to `D` and `D'` give `c(U, U)` with `c(U, U)` even (twice the number of edges), and
  every other pair of blocks does not interact.

Claw-freeness is not used (`toggle_stable` carries the hypothesis of the manuscript setup).
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-! ### The swapped deformation has the swapped blocks -/

theorem mem_swapSides_iff (D : G.FPDeformation s s') (B : G.SideBlock s s') :
    B.swap ∈ D.swapSides.blocks ↔ B ∈ D.blocks := by
  rw [blocks_swapSides, List.mem_map]
  constructor
  · rintro ⟨C, hC, hCB⟩
    have : C = B := by
      have := congrArg SideBlock.swap hCB
      rwa [SideBlock.swap_swap, SideBlock.swap_swap] at this
    rwa [this] at hC
  · intro h
    exact ⟨B, h, rfl⟩

/-! ### The key lemma -/

/-- A side-1 block of a palindromic deformation which interacts with a side-2 block of the same
pair of states forces that side-2 block to be a block of the deformation: a vertex of the side-2
block which obstructs, or sits on, a step of the side-1 block lies in a side-2 block of the
deformation (direction lemma), and distinct blocks of one side graph are disjoint. -/
theorem mem_of_interacts_inl_inr (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {P : G.OddBlock s.1 s'.1}
    {Q : G.OddBlock s.2 s'.2} (hP : (Sum.inl P : G.SideBlock s s') ∈ D.blocks)
    (h : Interacts (Sum.inl P : G.SideBlock s s') (Sum.inr Q)) :
    (Sum.inr Q : G.SideBlock s s') ∈ D.blocks := by
  obtain ⟨r, hr⟩ := List.mem_iff_get.1 hP
  obtain ⟨p, hp, hcases⟩ := h
  have hQsub := Q.support_subset_symmDiff
  have hp1 : p.1 ∈ s'.1 \ s.1 := OddBlock.fst_mem hp
  have hp2 : p.2 ∈ s.1 \ s'.1 := OddBlock.snd_mem hp
  -- a vertex of `Q` which separates the step `p`, or sits on it, puts `Q` into `D`
  have main : ∀ v ∈ Q.support, ((v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) ∨
      (v = p.1 ∧ v ∈ s.2) ∨ (v = p.2 ∧ v ∈ s'.2)) →
      (Sum.inr Q : G.SideBlock s s') ∈ D.blocks := by
    intro v hvQ hsep
    have hvmem : v ∈ s.2 ∪ s'.2 := by
      rcases Finset.mem_symmDiff.1 (hQsub hvQ) with ⟨h, -⟩ | ⟨h, -⟩
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
    obtain ⟨-, q, Q', hq, hvQ', -, -⟩ := direction hs hs' D hD hr hp hvmem hsep
    have hQQ : Q' = Q := by
      rcases OddBlock.eq_or_disjoint Q' Q with h | h
      · exact h
      · exact absurd hvQ (Finset.disjoint_left.1 h hvQ')
    subst hQQ
    rw [← hq]
    exact List.get_mem _ _
  rcases hcases with h1 | h2 | ⟨v, hv, hv1, hv2, hne⟩
  · refine main p.1 h1 (Or.inr (Or.inl ⟨rfl, ?_⟩))
    rcases Finset.mem_symmDiff.1 (hQsub h1) with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (Finset.disjoint_left.1 hs'.disjoint (Finset.mem_sdiff.1 hp1).1)
  · refine main p.2 h2 (Or.inr (Or.inr ⟨rfl, ?_⟩))
    rcases Finset.mem_symmDiff.1 (hQsub h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (Finset.disjoint_left.1 hs.disjoint (Finset.mem_sdiff.1 hp2).1)
    · exact h
  · exact main v hv (Or.inl ⟨hv1, hv2, hne⟩)

/-- **Interaction from a block of a palindromic deformation stays inside the deformation.**  If `R`
is a block of the palindromic deformation `D` and `R` interacts with a side block `Q` of the same
pair of states, then `Q` is a block of `D`.  (Blocks of the same side with distinct supports never
interact; for opposite sides this is the direction lemma.) -/
theorem mem_of_interacts (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {R Q : G.SideBlock s s'}
    (hR : R ∈ D.blocks) (h : Interacts R Q) : Q ∈ D.blocks := by
  rcases R with P | P <;> rcases Q with Q | Q
  · by_cases hsupp : P.support = Q.support
    · have := OddBlock.eq_of_support_eq P Q hsupp
      subst this
      exact hR
    · exact absurd h (not_interacts_inl_inl hs hs' hsupp)
  · exact mem_of_interacts_inl_inr hs hs' D hD hR h
  · have hP' : (Sum.inl P : G.SideBlock s.swap s'.swap) ∈ D.swapSides.blocks :=
      (mem_swapSides_iff D (Sum.inr P)).2 hR
    have h' : Interacts (Sum.inl P : G.SideBlock s.swap s'.swap) (Sum.inr Q) :=
      (interacts_swap_iff (Sum.inr P : G.SideBlock s s') (Sum.inl Q)).2 h
    have := mem_of_interacts_inl_inr hs.swap hs'.swap D.swapSides
      ((palindromic_swapSides_iff D).2 hD) hP' h'
    exact (mem_swapSides_iff D (Sum.inl Q)).1 this
  · by_cases hsupp : P.support = Q.support
    · have := OddBlock.eq_of_support_eq P Q hsupp
      subst this
      exact hR
    · exact absurd h (not_interacts_inr_inr hs hs' hsupp)

/-- **Key lemma: no block of `D' ∖ D` interacts with a block of `D`, in either direction.**  Let
`D` and `D'` be palindromic deformations of the same pair of hole-class states, `Q` a block of `D'`
which is not a block of `D`, and `R` a block of `D`.  Then neither `Q` interacts with `R` nor `R`
with `Q`.

If `R` interacted with `Q`, then `Q` would be a block of `D` (`mem_of_interacts` in `D`).  If `Q`
interacted with `R`, then `R` would be a block of `D'` (`mem_of_interacts` in `D'`), so that `R`
interacts with `Q` by the symmetry of interaction in `D'` (`interacts_symm`), which was excluded. -/
theorem not_interacts_of_mem_not_mem (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D D' : G.FPDeformation s s') (hD : D.Palindromic) (hD' : D'.Palindromic)
    {Q R : G.SideBlock s s'} (hQ : Q ∈ D'.blocks) (hQn : Q ∉ D.blocks) (hR : R ∈ D.blocks) :
    ¬ Interacts Q R ∧ ¬ Interacts R Q := by
  have h2 : ¬ Interacts R Q := fun h => hQn (mem_of_interacts hs hs' D hD hR h)
  refine ⟨fun h => h2 ?_, h2⟩
  have hR' : R ∈ D'.blocks := mem_of_interacts hs hs' D' hD' hQ h
  exact interacts_symm hs hs' D' hD' hQ hR' h

/-- The key lemma in terms of separation of vertices by steps. -/
theorem stepIndep_of_mem_not_mem (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D D' : G.FPDeformation s s') (hD : D.Palindromic) (hD' : D'.Palindromic)
    {Q R : G.SideBlock s s'} (hQ : Q ∈ D'.blocks) (hQn : Q ∉ D.blocks) (hR : R ∈ D.blocks) :
    StepIndep G Q.word R.support ∧ StepIndep G R.word Q.support := by
  obtain ⟨h1, h2⟩ := not_interacts_of_mem_not_mem hs hs' D D' hD hD' hQ hQn hR
  exact ⟨(not_interacts_iff Q R).1 h1, (not_interacts_iff R Q).1 h2⟩

/-! ### Agreement of the classes along the toggle of a palindromic deformation -/

/-- **Agreement along the toggle, side 1.**  Let `P` be a side-1 block of the palindromic
deformation `D`, and `v` a vertex separated by a step of `P`.  Then `v` lies in the second class of
the forward end state exactly when it lies in `s'.2`, and in the second class of the backward end
state exactly when it lies in `s.2`.  (A separated vertex of `s.2 ∪ s'.2` lies in a side-2 block of
`D` by the direction lemma, hence in the side-2 toggle `T₂ ⊆ s.2 ⊕ s'.2`, where `⊕ T₂` exchanges the
two classes; a separated vertex outside `s.2 ∪ s'.2` is in none of the four sets.) -/
theorem agree_inl (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {P : G.OddBlock s.1 s'.1}
    (hP : (Sum.inl P : G.SideBlock s s') ∈ D.blocks) {v : V} (hv : ¬ StepIndep G P.word {v}) :
    (v ∈ symmDiff s.2 D.toggle₂ ↔ v ∈ s'.2) ∧ (v ∈ symmDiff s'.2 D.toggle₂ ↔ v ∈ s.2) := by
  obtain ⟨r, hr⟩ := List.mem_iff_get.1 hP
  obtain ⟨p, hp, hpv⟩ : ∃ p ∈ P.word, ¬(G.Adj p.1 v ↔ G.Adj p.2 v) := by
    by_contra h
    push Not at h
    exact hv (fun p hp u hu => by rw [Finset.mem_singleton] at hu; subst hu; exact h p hp)
  have hp1 : p.1 ∈ s'.1 \ s.1 := OddBlock.fst_mem hp
  have hp2 : p.2 ∈ s.1 \ s'.1 := OddBlock.snd_mem hp
  have hsub2 : D.toggle₂ ⊆ symmDiff s.2 s'.2 := D.toggle₂_subset
  by_cases hvm : v ∈ s.2 ∪ s'.2
  · have hsep : (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)) ∨ (v = p.1 ∧ v ∈ s.2) ∨
        (v = p.2 ∧ v ∈ s'.2) := by
      by_cases h1 : v = p.1
      · right; left
        refine ⟨h1, ?_⟩
        rcases Finset.mem_union.1 hvm with h | h
        · exact h
        · exact absurd (h1 ▸ h) (Finset.disjoint_left.1 hs'.disjoint (Finset.mem_sdiff.1 hp1).1)
      by_cases h2 : v = p.2
      · right; right
        refine ⟨h2, ?_⟩
        rcases Finset.mem_union.1 hvm with h | h
        · exact absurd (h2 ▸ h) (Finset.disjoint_left.1 hs.disjoint (Finset.mem_sdiff.1 hp2).1)
        · exact h
      · exact Or.inl ⟨h1, h2, hpv⟩
    obtain ⟨hnot, q, Q, hq, hvQ, -, -⟩ := direction hs hs' D hD hr hp hvm hsep
    have hvT : v ∈ D.toggle₂ := (mem_toggle₂ D).2 ⟨Q, List.mem_iff_get.2 ⟨q, hq⟩, hvQ⟩
    have hvsd := Finset.mem_symmDiff.1 (hsub2 hvT)
    simp only [Finset.mem_symmDiff]
    tauto
  · have hvs : v ∉ s.2 := fun h => hvm (Finset.mem_union_left _ h)
    have hvs' : v ∉ s'.2 := fun h => hvm (Finset.mem_union_right _ h)
    have hvT : v ∉ D.toggle₂ := fun h => by
      rcases Finset.mem_symmDiff.1 (hsub2 h) with ⟨h, -⟩ | ⟨h, -⟩
      · exact hvs h
      · exact hvs' h
    simp [Finset.mem_symmDiff, hvs, hvs', hvT]

/-- **Agreement along the toggle.**  Every block `B` of a palindromic deformation `D` satisfies the
agreement property `SideBlock.Agree` for the toggles of `D`: the side-2 version of `agree_inl` is
`agree_inl` for `D.swapSides`. -/
theorem agree_of_mem (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) {B : G.SideBlock s s'} (hB : B ∈ D.blocks) :
    SideBlock.Agree s s' D.toggle₁ D.toggle₂ B := by
  cases B with
  | inl P =>
    intro v hv
    have := agree_inl hs hs' D hD hB hv
    simpa [SideBlock.cls, SideBlock.tgOf] using this
  | inr P =>
    intro v hv
    have hB' : (Sum.inl P : G.SideBlock s.swap s'.swap) ∈ D.swapSides.blocks :=
      (mem_swapSides_iff D (Sum.inr P)).2 hB
    have := agree_inl hs.swap hs'.swap D.swapSides ((palindromic_swapSides_iff D).2 hD) hB' hv
    simpa [SideBlock.cls, SideBlock.tgOf] using this

end FPDeformation

/-! ### Parity calculus -/

/-- The cross count with the empty set on the left vanishes. -/
theorem crossCount_emptyset_left_eq_zero [DecidableEq V] (Y : Finset V) : G.crossCount ∅ Y = 0 := by
  classical
  rw [crossCount_eq_card_filter]
  simp

/-- The cross count of a set with itself is even: the edges inside the set are counted twice. -/
theorem crossCount_self_mod_two [DecidableEq V] (S : Finset V) : G.crossCount S S % 2 = 0 := by
  classical
  have h : ((G.crossCount S S : ℕ) : ZMod 2) = 0 := by
    rw [crossCount_eq_sum_sum]
    push_cast
    rw [← Finset.sum_product' (f := fun x y => if G.Adj x y then (1 : ZMod 2) else 0)]
    refine Finset.sum_involution (fun a _ => a.swap) ?_ ?_ ?_ ?_
    · intro a _
      by_cases hadj : G.Adj a.1 a.2
      · simp [hadj, hadj.symm]
        decide
      · have : ¬ G.Adj a.2 a.1 := fun h => hadj h.symm
        simp [hadj, this]
    · intro a _ ha hsw
      have hadj : G.Adj a.1 a.2 := by
        by_contra hn
        exact ha (by simp [hn])
      have h12 : a.2 = a.1 := congrArg Prod.fst hsw
      rw [h12] at hadj
      exact G.irrefl hadj
    · intro a ha
      rw [Finset.mem_product] at ha ⊢
      exact ⟨ha.2, ha.1⟩
    · intro a _
      simp
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).1 h)

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

/-- If the steps of a block separate no vertex of `Z`, then the block sends an even number of
edges to `Z`: its vertices come in pairs `(j, k)` with the same neighbours in `Z`. -/
theorem crossCount_support_mod_two (P : G.OddBlock X Y) {Z : Finset V}
    (h : StepIndep G P.word Z) : G.crossCount P.support Z % 2 = 0 := by
  classical
  rw [crossCount_eq_sum_card_filter, ← P.toFinset_wordVertices,
    List.sum_toFinset _ P.nodup_wordVertices]
  have key : ∀ w : List (V × V), StepIndep G w Z →
      ((wordVertices w).map fun x => (Z.filter (G.Adj x)).card).sum % 2 = 0 := by
    intro w
    induction w with
    | nil => intro _; simp
    | cons p w ih =>
      intro hw
      have hp := hw p (List.mem_cons_self ..)
      have hw' : StepIndep G w Z := fun q hq => hw q (List.mem_cons_of_mem _ hq)
      have heq : Z.filter (G.Adj p.1) = Z.filter (G.Adj p.2) :=
        Finset.filter_congr (fun v hv => hp v hv)
      simp only [wordVertices_cons, List.map_cons, List.sum_cons, heq]
      have := ih hw'
      omega
  exact key P.word h

end OddBlock

namespace SideBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

theorem crossCount_support_mod_two (B : G.SideBlock s s') {Z : Finset V}
    (h : StepIndep G B.word Z) : G.crossCount B.support Z % 2 = 0 := by
  cases B with
  | inl P => exact OddBlock.crossCount_support_mod_two P h
  | inr P => exact OddBlock.crossCount_support_mod_two P h

/-- The full toggle of a list of side blocks: `T₁ ⊕ T₂`. -/
def tog (L : List (G.SideBlock s s')) : Finset V := symmDiff (listToggle₁ L) (listToggle₂ L)

theorem tog_nil : tog ([] : List (G.SideBlock s s')) = ∅ := by simp [tog]

theorem tog_cons (B : G.SideBlock s s') (L : List (G.SideBlock s s')) :
    tog (B :: L) = symmDiff B.support (tog L) := by
  cases B with
  | inl P =>
    simp only [tog, listToggle₁_cons_inl, listToggle₂_cons_inl, support_inl, symmDiff_assoc]
  | inr P =>
    simp only [tog, listToggle₁_cons_inr, listToggle₂_cons_inr, support_inr]
    rw [symmDiff_left_comm]

theorem tog_append (a b : List (G.SideBlock s s')) :
    tog (a ++ b) = symmDiff (tog a) (tog b) := by
  simp only [tog, listToggle₁_append, listToggle₂_append]
  exact symmDiff_symmDiff_symmDiff_comm _ _ _ _

theorem listToggle₁_perm {a b : List (G.SideBlock s s')} (h : a.Perm b) :
    listToggle₁ a = listToggle₁ b := by
  unfold listToggle₁
  haveI : LeftCommutative (fun (B : G.SideBlock s s') (T : Finset V) =>
      match B with | .inl P => symmDiff P.support T | .inr _ => T) :=
    ⟨fun x y z => by cases x <;> cases y <;> simp [symmDiff_left_comm]⟩
  exact h.foldr_eq _

theorem listToggle₂_perm {a b : List (G.SideBlock s s')} (h : a.Perm b) :
    listToggle₂ a = listToggle₂ b := by
  unfold listToggle₂
  haveI : LeftCommutative (fun (B : G.SideBlock s s') (T : Finset V) =>
      match B with | .inr P => symmDiff P.support T | .inl _ => T) :=
    ⟨fun x y z => by cases x <;> cases y <;> simp [symmDiff_left_comm]⟩
  exact h.foldr_eq _

theorem tog_perm {a b : List (G.SideBlock s s')} (h : a.Perm b) : tog a = tog b := by
  simp only [tog, listToggle₁_perm h, listToggle₂_perm h]

theorem stepIndep_tog {w : List (V × V)} (L : List (G.SideBlock s s'))
    (h : ∀ B ∈ L, StepIndep G w B.support) : StepIndep G w (tog L) :=
  (stepIndep_listToggle₁ L h).symmDiff' (stepIndep_listToggle₂ L h)

/-- **Parity of the cross count of two toggles.**  If the steps of every block of `L₁` separate no
vertex of any block of `L₂`, then `c(tog L₁, tog L₂)` is even. -/
theorem crossCount_tog_tog_mod_two {L₁ L₂ : List (G.SideBlock s s')}
    (h : ∀ B ∈ L₁, ∀ C ∈ L₂, StepIndep G B.word C.support) :
    G.crossCount (tog L₁) (tog L₂) % 2 = 0 := by
  induction L₁ with
  | nil => simp [tog_nil, crossCount_emptyset_left_eq_zero]
  | cons B L₁ ih =>
    have ih' := ih (fun B' hB' => h B' (List.mem_cons_of_mem _ hB'))
    rw [tog_cons, crossCount_symmDiff_left_mod_two]
    have h1 : G.crossCount B.support (tog L₂) % 2 = 0 :=
      crossCount_support_mod_two B
        (stepIndep_tog L₂ (fun C hC => h B (List.mem_cons_self ..) C hC))
    omega

end SideBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **The cross count of two toggles is even.**  Let `D` and `D'` be palindromic deformations of the
same hole-class states, with toggles `T`, `T'`.  Then `c(T', T)` is even.  Split each toggle into
the blocks common to `D` and `D'` and the others: `c(U, U)` is even (it counts every edge twice),
and every other pair of blocks does not interact (the key lemma
`not_interacts_of_mem_not_mem`), so its steps separate no vertex and the cross count is even
(`SideBlock.crossCount_tog_tog_mod_two`). -/
theorem crossCount_toggle_toggle_mod_two (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D D' : G.FPDeformation s s') (hD : D.Palindromic) (hD' : D'.Palindromic) :
    G.crossCount D'.toggle D.toggle % 2 = 0 := by
  classical
  set p : G.SideBlock s s' → Bool := fun B => decide (B ∈ D.blocks) with hp
  set q : G.SideBlock s s' → Bool := fun B => decide (B ∈ D'.blocks) with hq
  have hD'split : D'.toggle = symmDiff (SideBlock.tog (D'.blocks.filter p))
      (SideBlock.tog (D'.blocks.filter fun B => !p B)) := by
    rw [← SideBlock.tog_append]
    exact SideBlock.tog_perm (List.filter_append_perm p D'.blocks).symm
  have hDsplit : D.toggle = symmDiff (SideBlock.tog (D.blocks.filter q))
      (SideBlock.tog (D.blocks.filter fun B => !q B)) := by
    rw [← SideBlock.tog_append]
    exact SideBlock.tog_perm (List.filter_append_perm q D.blocks).symm
  have hperm : (D.blocks.filter q).Perm (D'.blocks.filter p) := by
    rw [List.perm_ext_iff_of_nodup ((List.Nodup.of_map _ D.nodup).filter _)
      ((List.Nodup.of_map _ D'.nodup).filter _)]
    intro B
    simp only [List.mem_filter, hp, hq, decide_eq_true_eq]
    tauto
  rw [hD'split, hDsplit, SideBlock.tog_perm hperm, crossCount_symmDiff_symmDiff_mod_two]
  have h1 := crossCount_self_mod_two (G := G) (SideBlock.tog (D'.blocks.filter p))
  have h2 : G.crossCount (SideBlock.tog (D'.blocks.filter p))
      (SideBlock.tog (D.blocks.filter fun B => !q B)) % 2 = 0 := by
    refine SideBlock.crossCount_tog_tog_mod_two (fun B hB C hC => ?_)
    simp only [List.mem_filter, hp, hq, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hB hC
    exact (stepIndep_of_mem_not_mem hs hs' D' D hD' hD hC.1 hC.2 hB.1).2
  have h3 : G.crossCount (SideBlock.tog (D'.blocks.filter fun B => !p B))
      (SideBlock.tog (D'.blocks.filter p)) % 2 = 0 := by
    refine SideBlock.crossCount_tog_tog_mod_two (fun B hB C hC => ?_)
    simp only [List.mem_filter, hp, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hB hC
    exact (stepIndep_of_mem_not_mem hs hs' D D' hD hD' hB.1 hB.2 hC.2).1
  have h4 : G.crossCount (SideBlock.tog (D'.blocks.filter fun B => !p B))
      (SideBlock.tog (D.blocks.filter fun B => !q B)) % 2 = 0 := by
    refine SideBlock.crossCount_tog_tog_mod_two (fun B hB C hC => ?_)
    simp only [List.mem_filter, hp, hq, Bool.not_eq_true', decide_eq_false_iff_not] at hB hC
    exact (stepIndep_of_mem_not_mem hs hs' D D' hD hD' hB.1 hB.2 hC.1).1
  omega

/-! ### Retyping the blocks of `D'` for the end states of `D` -/

/-- The toggle of the side of a side block: `T₁` for a side-1 block, `T₂` for a side-2 block. -/
def ownToggle (D : G.FPDeformation s s') : G.SideBlock s s' → Finset V
  | .inl _ => D.toggle₁
  | .inr _ => D.toggle₂

/-- **Retyping a block as a block of the end states of `D`.**  A side block whose support lies in
the toggle of its own side is reversed (`OddBlock.retypeToggled`): the introduced vertices of the
block are in `C'_c ∖ C_a` and in the toggle, hence in `(C_a ⊕ T₁) ∖ (C'_c ⊕ T₁)`.  A side block
whose support is disjoint from the toggle of its own side keeps its path
(`OddBlock.retypeUntoggled`).  The junk value `junk` is returned for any other block; it is
never used below (it is only needed to have a total function). -/
def retype (D : G.FPDeformation s s') (junk : G.SideBlock D.fwdEnd D.bwdEnd) :
    G.SideBlock s s' → G.SideBlock D.fwdEnd D.bwdEnd
  | .inl P =>
    if h : P.support ⊆ D.toggle₁ then .inl (P.retypeToggled h)
    else if h' : Disjoint P.support D.toggle₁ then .inl (P.retypeUntoggled h')
    else junk
  | .inr P =>
    if h : P.support ⊆ D.toggle₂ then .inr (P.retypeToggled h)
    else if h' : Disjoint P.support D.toggle₂ then .inr (P.retypeUntoggled h')
    else junk

theorem not_subset_of_disjoint {X Y : Finset V} (P : G.OddBlock X Y) {T : Finset V}
    (h : Disjoint P.support T) : ¬ P.support ⊆ T := fun hsub =>
  Finset.disjoint_left.1 h P.first_mem_support (hsub P.first_mem_support)

/-- A block whose support lies in the toggle of its own side is reversed by `retype`. -/
theorem retype_of_subset (D : G.FPDeformation s s') (junk : G.SideBlock D.fwdEnd D.bwdEnd)
    {B : G.SideBlock s s'} (h : B.support ⊆ D.ownToggle B) :
    (D.retype junk B).support = B.support ∧ (D.retype junk B).isLeft = B.isLeft ∧
      (D.retype junk B).word = reverseWord B.word := by
  cases B with
  | inl P =>
    have h' : P.support ⊆ D.toggle₁ := h
    simp only [retype, h', dif_pos]
    exact ⟨P.retypeToggled_support h', rfl, P.retypeToggled_word h'⟩
  | inr P =>
    have h' : P.support ⊆ D.toggle₂ := h
    simp only [retype, h', dif_pos]
    exact ⟨P.retypeToggled_support h', rfl, P.retypeToggled_word h'⟩

/-- A block whose support is disjoint from the toggle of its own side keeps its word under
`retype`. -/
theorem retype_of_disjoint (D : G.FPDeformation s s') (junk : G.SideBlock D.fwdEnd D.bwdEnd)
    {B : G.SideBlock s s'} (h : Disjoint B.support (D.ownToggle B)) :
    (D.retype junk B).support = B.support ∧ (D.retype junk B).isLeft = B.isLeft ∧
      (D.retype junk B).word = B.word := by
  cases B with
  | inl P =>
    have h' : Disjoint P.support D.toggle₁ := h
    simp only [retype, not_subset_of_disjoint P h', dif_neg, h', dif_pos, not_false_eq_true]
    exact ⟨P.retypeUntoggled_support h', rfl, P.retypeUntoggled_word h'⟩
  | inr P =>
    have h' : Disjoint P.support D.toggle₂ := h
    simp only [retype, not_subset_of_disjoint P h', dif_neg, h', dif_pos, not_false_eq_true]
    exact ⟨P.retypeUntoggled_support h', rfl, P.retypeUntoggled_word h'⟩

/-- Some block of `s, s'` which is a block of the toggle or disjoint from it gives a block of the
end states. -/
theorem nonempty_target_of (D : G.FPDeformation s s') {B : G.SideBlock s s'}
    (h : B.support ⊆ D.ownToggle B ∨ Disjoint B.support (D.ownToggle B)) :
    Nonempty (G.SideBlock D.fwdEnd D.bwdEnd) := by
  cases B with
  | inl P =>
    rcases h with h | h
    · exact ⟨.inl (P.retypeToggled (T := D.toggle₁) h)⟩
    · exact ⟨.inl (P.retypeUntoggled (T := D.toggle₁) h)⟩
  | inr P =>
    rcases h with h | h
    · exact ⟨.inr (P.retypeToggled (T := D.toggle₂) h)⟩
    · exact ⟨.inr (P.retypeUntoggled (T := D.toggle₂) h)⟩

theorem support_subset_ownToggle (D : G.FPDeformation s s') {B : G.SideBlock s s'}
    (hB : B ∈ D.blocks) : B.support ⊆ D.ownToggle B := by
  cases B with
  | inl P => exact fun v hv => (D.mem_toggle₁).2 ⟨P, hB, hv⟩
  | inr P => exact fun v hv => (D.mem_toggle₂).2 ⟨P, hB, hv⟩

theorem disjoint_ownToggle_of_mem_not_mem (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D D' : G.FPDeformation s s') (hD : D.Palindromic) (hD' : D'.Palindromic)
    {B : G.SideBlock s s'} (hB : B ∈ D'.blocks) (hBn : B ∉ D.blocks) :
    Disjoint B.support (D.ownToggle B) := by
  have hall : ∀ R ∈ D.blocks, StepIndep G B.word R.support := fun R hR =>
    (stepIndep_of_mem_not_mem hs hs' D D' hD hD' hB hBn hR).1
  cases B with
  | inl P =>
    exact P.disjoint_of_stepIndep (SideBlock.stepIndep_listToggle₁ D.blocks hall)
  | inr P =>
    exact P.disjoint_of_stepIndep (SideBlock.stepIndep_listToggle₂ D.blocks hall)

/-- **Toggle stability** (new; repairs v1's unargued final pairing, L1237-1241).  Let `D` and `D'`
be palindromic fixed-pairing-type deformations (v1 Definition 19, L978-994) of the same pair of
hole-class states `s = (C_a, C_b)`, `s' = (C'_c, C'_d)`.  Then there is a palindromic deformation
`D''` of the pair of end states `(D.fwdEnd, D.bwdEnd) = (s ⊕ T, s' ⊕ T)` of `D`, with the toggle
and the parity of `D'`: `D''.toggle = D'.toggle` and `D''.IsOdd ↔ D'.IsOdd`.

`D''` consists of the blocks of `D'` which are blocks of `D`, retyped and reversed, in reverse
`D'`-order, followed by the blocks of `D'` which are not blocks of `D`, retyped untoggled, in
`D'`-order.  The proof is the key lemma `not_interacts_of_mem_not_mem` (no block of `D' ∖ D`
interacts with a block of `D`), the validity criterion `palindromic_iff_stepConds` and the list
operations of `FreeFermionGraphs.T3StepCondsTransport`, and the parity statement
`crossCount_toggle_toggle_mod_two`.  For `D' = D` it gives the reverse deformation, so the toggle
`T` is again a toggle at the toggled pair.

Both deformations are fixed-pairing-type deformations with the same pairing `(a ↔ c, b ↔ d)`
(`SideBlock`); nothing is claimed for deformations of different pairings.  Claw-freeness is not
used: the hypothesis is part of the manuscript setup of Theorem 1 and is carried for the shape of
the statement. -/
theorem toggle_stable (_hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D D' : G.FPDeformation s s') (hD : D.Palindromic) (hD' : D'.Palindromic) :
    ∃ D'' : G.FPDeformation D.fwdEnd D.bwdEnd, D''.Palindromic ∧ D''.toggle = D'.toggle ∧
      (D''.IsOdd ↔ D'.IsOdd) := by
  classical
  obtain ⟨hfe, hbe⟩ := hD.isHoleClasses_ends hs hs'
  have hc' := Palindromic.stepConds hs hs' hD'
  obtain ⟨D'', hP, htog⟩ : ∃ D'' : G.FPDeformation D.fwdEnd D.bwdEnd,
      D''.Palindromic ∧ D''.toggle = D'.toggle := by
    by_cases hnil : D'.blocks = []
    · -- no block: the empty deformation
      have h1 : D'.toggle₁ = ∅ := by rw [toggle₁_eq, hnil]; rfl
      have h2 : D'.toggle₂ = ∅ := by rw [toggle₂_eq, hnil]; rfl
      have h3 : D'.toggle = ∅ := by simp [toggle, h1, h2]
      refine ⟨⟨[], List.nodup_nil⟩, ⟨⟨_, ClassRun.nil _⟩, ⟨_, ClassRun.nil _⟩⟩, ?_⟩
      rw [h3]
      simp [toggle, toggle₁, toggle₂]
    · obtain ⟨B₀, hB₀⟩ := List.exists_mem_of_ne_nil _ hnil
      obtain ⟨junk⟩ : Nonempty (G.SideBlock D.fwdEnd D.bwdEnd) := by
        refine D.nonempty_target_of (B := B₀) ?_
        by_cases hB : B₀ ∈ D.blocks
        · exact Or.inl (support_subset_ownToggle D hB)
        · exact Or.inr (disjoint_ownToggle_of_mem_not_mem hs hs' D D' hD hD' hB₀ hB)
      set ret := D.retype junk with hret
      set p : G.SideBlock s s' → Bool := fun B => decide (B ∈ D.blocks) with hp
      set ℓin := D'.blocks.filter p with hℓin
      set ℓout := D'.blocks.filter (fun B => !p B) with hℓout
      have hin_mem : ∀ B ∈ ℓin, B ∈ D'.blocks ∧ B ∈ D.blocks := fun B hB => by
        rw [hℓin, List.mem_filter] at hB
        exact ⟨hB.1, by simpa [hp] using hB.2⟩
      have hout_mem : ∀ B ∈ ℓout, B ∈ D'.blocks ∧ B ∉ D.blocks := fun B hB => by
        rw [hℓout, List.mem_filter] at hB
        exact ⟨hB.1, by simpa [hp] using hB.2⟩
      -- the step conditions of the two sublists of `D'`
      have hinSC : SideBlock.StepConds G s s' ℓin := by
        refine SideBlock.stepConds_filter D'.nodup hc' p (fun B hB hpB C hC hpC => ?_)
        have hBD : B ∈ D.blocks := by simpa [hp] using hpB
        have hCD : C ∉ D.blocks := by simpa [hp] using hpC
        exact (stepIndep_of_mem_not_mem hs hs' D D' hD hD' hC hCD hBD).2
      have houtSC : SideBlock.StepConds G s s' ℓout := by
        refine SideBlock.stepConds_filter D'.nodup hc' (fun B => !p B) (fun B hB hpB C hC hpC => ?_)
        have hBD : B ∉ D.blocks := by simpa [hp] using hpB
        have hCD : C ∈ D.blocks := by simpa [hp] using hpC
        exact (stepIndep_of_mem_not_mem hs hs' D D' hD hD' hB hBD hCD).1
      -- retyping
      have hfin : ∀ B ∈ ℓin, (ret B).support = B.support ∧ (ret B).isLeft = B.isLeft ∧
          (ret B).word = reverseWord B.word := fun B hB =>
        D.retype_of_subset junk (support_subset_ownToggle D (hin_mem B hB).2)
      have hfout : ∀ B ∈ ℓout, (ret B).support = B.support ∧ (ret B).isLeft = B.isLeft ∧
          (ret B).word = B.word := fun B hB =>
        D.retype_of_disjoint junk
          (disjoint_ownToggle_of_mem_not_mem hs hs' D D' hD hD' (hout_mem B hB).1 (hout_mem B hB).2)
      have hX : SideBlock.StepConds G D.fwdEnd D.bwdEnd (ℓin.reverse.map ret) :=
        SideBlock.stepConds_map_reverse hinSC ret D.toggle₁ D.toggle₂ rfl rfl rfl rfl hfin
          (fun B hB => agree_of_mem hs hs' D hD (hin_mem B hB).2)
      have hT : ∀ B ∈ ℓout, StepIndep G B.word (SideBlock.tgOf D.toggle₁ D.toggle₂ B) := by
        intro B hB
        obtain ⟨hB1, hB2⟩ := hout_mem B hB
        have hall : ∀ R ∈ D.blocks, StepIndep G B.word R.support := fun R hR =>
          (stepIndep_of_mem_not_mem hs hs' D D' hD hD' hB1 hB2 hR).1
        cases B with
        | inl P =>
          simpa [SideBlock.tgOf, D.toggle₂_eq] using SideBlock.stepIndep_listToggle₂ D.blocks hall
        | inr P =>
          simpa [SideBlock.tgOf, D.toggle₁_eq] using SideBlock.stepIndep_listToggle₁ D.blocks hall
      have hY : SideBlock.StepConds G D.fwdEnd D.bwdEnd (ℓout.map ret) :=
        SideBlock.stepConds_map_untoggled houtSC ret D.toggle₁ D.toggle₂ rfl rfl rfl rfl hfout hT
      have hXY : ∀ B'' ∈ ℓin.reverse.map ret, ∀ C'' ∈ ℓout.map ret,
          StepIndep G B''.word C''.support ∧ StepIndep G C''.word B''.support := by
        intro B'' hB'' C'' hC''
        obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hB''
        obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC''
        rw [List.mem_reverse] at hB
        obtain ⟨-, hB2⟩ := hin_mem B hB
        obtain ⟨hC1, hC2⟩ := hout_mem C hC
        obtain ⟨h1, h2⟩ := stepIndep_of_mem_not_mem hs hs' D D' hD hD' hC1 hC2 hB2
        obtain ⟨a1, -, a3⟩ := hfin B hB
        obtain ⟨b1, -, b3⟩ := hfout C hC
        refine ⟨?_, ?_⟩
        · rw [a3, b1, stepIndep_reverseWord_iff]
          exact h2
        · rw [b3, a1]
          exact h1
      have hconds := SideBlock.stepConds_append hX hY hXY
      -- the permutation of blocks
      have hperm : (ℓin.reverse ++ ℓout).Perm D'.blocks :=
        ((List.reverse_perm ℓin).append_right ℓout).trans (List.filter_append_perm p D'.blocks)
      have hall : ∀ B ∈ ℓin.reverse ++ ℓout,
          (ret B).support = B.support ∧ (ret B).isLeft = B.isLeft := by
        intro B hB
        rcases List.mem_append.1 hB with hB | hB
        · exact ⟨(hfin B (List.mem_reverse.1 hB)).1, (hfin B (List.mem_reverse.1 hB)).2.1⟩
        · exact ⟨(hfout B hB).1, (hfout B hB).2.1⟩
      have hnodup : ((ℓin.reverse.map ret ++ ℓout.map ret).map SideBlock.support).Nodup := by
        have : (ℓin.reverse.map ret ++ ℓout.map ret).map SideBlock.support =
            (ℓin.reverse ++ ℓout).map SideBlock.support := by
          rw [← List.map_append, List.map_map]
          exact List.map_congr_left (fun B hB => (hall B hB).1)
        rw [this]
        exact (hperm.map _).nodup_iff.2 D'.nodup
      let D'' : G.FPDeformation D.fwdEnd D.bwdEnd := ⟨ℓin.reverse.map ret ++ ℓout.map ret, hnodup⟩
      refine ⟨D'', Palindromic.of_stepConds hfe hbe D'' hconds, ?_⟩
      have h1 : D''.toggle₁ = D'.toggle₁ := by
        rw [toggle₁_eq, toggle₁_eq]
        show SideBlock.listToggle₁ (ℓin.reverse.map ret ++ ℓout.map ret) = _
        rw [← List.map_append, SideBlock.listToggle₁_map_of_support ret _ hall]
        exact SideBlock.listToggle₁_perm hperm
      have h2 : D''.toggle₂ = D'.toggle₂ := by
        rw [toggle₂_eq, toggle₂_eq]
        show SideBlock.listToggle₂ (ℓin.reverse.map ret ++ ℓout.map ret) = _
        rw [← List.map_append, SideBlock.listToggle₂_map_of_support ret _ hall]
        exact SideBlock.listToggle₂_perm hperm
      simp only [toggle, h1, h2]
  refine ⟨D'', hP, htog, ?_⟩
  -- parity
  have hpar := crossCount_toggle_toggle_mod_two hs hs' D D' hD hD'
  unfold IsOdd
  rw [htog, carrier_fwdEnd hs hs' D hD, Nat.odd_iff, Nat.odd_iff, crossCount_symmDiff_right_mod_two]
  omega

/-- **The reverse deformation** (`toggle_stable` for `D' = D`).  A palindromic deformation `D` of
the hole-class states `s`, `s'` with toggle `T` gives a palindromic deformation of the toggled pair
`(D.fwdEnd, D.bwdEnd) = (s ⊕ T, s' ⊕ T)` with the same toggle and the same parity: `T` is again a
toggle at the toggled pair. -/
theorem exists_palindromic_toggle_at_ends (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (D : G.FPDeformation s s') (hD : D.Palindromic) :
    ∃ D'' : G.FPDeformation D.fwdEnd D.bwdEnd, D''.Palindromic ∧ D''.toggle = D.toggle ∧
      (D''.IsOdd ↔ D.IsOdd) :=
  toggle_stable hclaw hs hs' D D hD hD

end FPDeformation

end SimpleGraph
