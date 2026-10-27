import FreeFermionGraphs.T3FixedPairing
import FreeFermionGraphs.T3FrameSign

/-!
# Symmetries and transports of fixed-pairing deformations

This module formalises the reductions which arXiv 2305.15625 v1 uses silently in the proof of
Theorem 1 (iii), for the fixed-pairing-type deformations `SimpleGraph.FPDeformation s s'` of
`FreeFermionGraphs.T3FixedPairing` (v1 Definition 19 `definition:fixedpairingtypedeformation`,
L978-994): "we may assume the `(a, c)` pairing" (the `(a, d)` pairing of `(s, s')` is the `(a, c)`
pairing of `(s, s'.swap)`, v1 L982), and "the reversal `O⃖` of `O` is a deformation of `C'` by
vertices in `C`" (v1 L965-967, L1015-1016, L1120; the sufficient criterion is v1 Lemma 7
`lemma:solutioncriterion`, proof L1774-1800).

## Main definitions and results

* `FPDeformation.swapSides` exchanges the two sides: a deformation of `s = (C_a, C_b)` by
  `s' = (C'_c, C'_d)` becomes a deformation of `s.swap = (C_b, C_a)` by `s'.swap`, with the same
  blocks (`Sum.swap`).  It preserves the word (`word_swapSides`), the toggle (`toggle_swapSides`),
  `Palindromic` (`palindromic_swapSides_iff`) and `IsOdd` (`isOdd_swapSides_iff`), and exchanges
  the side toggles `toggle₁ ↔ toggle₂`.
* `FPDeformation.mirror` is the reverse deformation of `s'` by `s`: it reverses the list of blocks
  and reads each block backwards.  Its word is `reverseWord D.word` (`word_mirror`) and its toggle
  is that of `D` (`toggle_mirror`); the forward and backward end states are exchanged
  (`fwdEnd_mirror`, `bwdEnd_mirror`).  `Palindromic` is preserved in both directions
  (`palindromic_mirror_iff`, `palindromic_mirror`), `mirror_mirror` is the identity, and for a
  palindromic `D`, `D.mirror.IsOdd ↔ D.IsOdd` (`isOdd_mirror_iff`): the parity of `c(T, C)` is that
  of `c(T, C')` (`Palindromic.crossCount_toggle_mod_two_symm`).  This is the frame exponent
  symmetry `IsHoleClasses.crossCount_toggle_mod_two_symm` of `FreeFermionGraphs.T3FrameSign`
  applied to the two end states `(s.1 ⊕ T₁, s.2 ⊕ T₂)` and `(s'.1 ⊕ T₁, s'.2 ⊕ T₂)` of `D`: both
  parities equal that of `c(Y, Z)`, with `Y = (s.1 ∩ T₁) ∪ (s.2 ∩ T₂)` the toggled vertices of `C`
  and `Z = (s'.1 ∩ T₁) ∪ (s'.2 ∩ T₂)` those of `C'`; the proof there uses only that a vertex of a
  hole has an even number of neighbours in each of its two colouring classes.
* `FPDeformation.palindromic_single_iff`: a one-block deformation `single B` is palindromic iff `B`
  runs forward from `s` and backward from `s'`.
* `FPDeformation.ofToggle Q D` (and `ofToggle₂` on the second side) transports a deformation of
  `(s.1 ⊕ Q, s.2)` by `s'` into a deformation of `s` by `s'`, where `Q` is a block of the same side
  (so a component of `G[C_a ⊕ C'_c]`): toggling the closed component `Q` removes it from
  `G[C_a ⊕ C'_c]` and changes no other component (`OddBlock.ofToggle`).  The word
  (`ofToggle_word`), the blocks' supports and the toggles (`ofToggle_toggle`) are unchanged.

The two block types `OddBlock s.1 s'.1` and `OddBlock s.2 s'.2` of `SideBlock s s'` are exchanged
by `swap`, because `SideBlock s.swap s'.swap` reduces definitionally to
`OddBlock s.2 s'.2 ⊕ OddBlock s.1 s'.1`.

Claw-freeness is not used anywhere in this module.  The hypotheses `hs`, `hs'` of
`palindromic_mirror` are not needed for the proof (`palindromic_mirror_iff` holds without them);
they are kept so that the statement has the signature recorded in the work package.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

section RunSwap

variable [DecidableEq V] {s : Finset V × Finset V} {w : List (V × V)}

/-- The existence of a clone run of a word is invariant under swapping the two classes of the start
state (`ClassRun.swap_iff`). -/
theorem exists_classRun_swap_iff : (∃ t, G.ClassRun s.swap w t) ↔ ∃ t, G.ClassRun s w t := by
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t.swap, ClassRun.swap_iff.1 (by simpa using h)⟩
  · rintro ⟨t, h⟩
    exact ⟨t.swap, h.swap⟩

end RunSwap

namespace SideBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-! ### Swapping the two sides -/

/-- The side block with its side exchanged: a side-1 block of `(s, s')` is a side-2 block of
`(s.swap, s'.swap)` and conversely. -/
def swap : G.SideBlock s s' → G.SideBlock s.swap s'.swap
  | .inl P => .inr P
  | .inr P => .inl P

@[simp] theorem swap_inl (P : G.OddBlock s.1 s'.1) :
    SideBlock.swap (Sum.inl P : G.SideBlock s s') = Sum.inr P := rfl

@[simp] theorem swap_inr (P : G.OddBlock s.2 s'.2) :
    SideBlock.swap (Sum.inr P : G.SideBlock s s') = Sum.inl P := rfl

@[simp] theorem support_swap (B : G.SideBlock s s') : B.swap.support = B.support := by
  cases B <;> rfl

@[simp] theorem word_swap (B : G.SideBlock s s') : B.swap.word = B.word := by
  cases B <;> rfl

@[simp] theorem swap_swap (B : G.SideBlock s s') : B.swap.swap = B := by
  cases B <;> rfl

/-- Swapping the sides exchanges the two toggles of a list of blocks. -/
theorem listToggle₁_map_swap (bs : List (G.SideBlock s s')) :
    listToggle₁ (bs.map SideBlock.swap) = listToggle₂ bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    cases B with
    | inl P => exact ih
    | inr P =>
      show symmDiff P.support (listToggle₁ (bs.map SideBlock.swap)) =
        symmDiff P.support (listToggle₂ bs)
      rw [ih]

/-- Swapping the sides exchanges the two toggles of a list of blocks. -/
theorem listToggle₂_map_swap (bs : List (G.SideBlock s s')) :
    listToggle₂ (bs.map SideBlock.swap) = listToggle₁ bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    cases B with
    | inl P =>
      show symmDiff P.support (listToggle₂ (bs.map SideBlock.swap)) =
        symmDiff P.support (listToggle₁ bs)
      rw [ih]
    | inr P => exact ih

/-! ### Transport along a toggle of a side-1 (resp. side-2) block -/

/-- A side block of `(s.1 ⊕ Q, s.2; s')` is a side block of `(s; s')`, for a side-1 block `Q` of
`(s; s')`: a side-1 block is transported by `OddBlock.ofToggle` (`Q.support` is a component of
`G[s.1 ⊕ s'.1]`) and a side-2 block is unchanged. -/
def ofToggle (Q : G.OddBlock s.1 s'.1) :
    G.SideBlock (symmDiff s.1 Q.support, s.2) s' → G.SideBlock s s'
  | .inl P => .inl (P.ofToggle Q.support_subset_symmDiff Q.isInducedComponent_support)
  | .inr P => .inr P

@[simp] theorem support_ofToggle (Q : G.OddBlock s.1 s'.1)
    (B : G.SideBlock (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q B).support = B.support := by
  cases B <;> rfl

@[simp] theorem word_ofToggle (Q : G.OddBlock s.1 s'.1)
    (B : G.SideBlock (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q B).word = B.word := by
  cases B <;> rfl

theorem listToggle₁_map_ofToggle (Q : G.OddBlock s.1 s'.1)
    (bs : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')) :
    listToggle₁ (bs.map (ofToggle Q)) = listToggle₁ bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    cases B with
    | inl P =>
      show symmDiff P.support (listToggle₁ (bs.map (ofToggle Q))) =
        symmDiff P.support (listToggle₁ bs)
      rw [ih]
    | inr P => exact ih

theorem listToggle₂_map_ofToggle (Q : G.OddBlock s.1 s'.1)
    (bs : List (G.SideBlock (symmDiff s.1 Q.support, s.2) s')) :
    listToggle₂ (bs.map (ofToggle Q)) = listToggle₂ bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    cases B with
    | inl P => exact ih
    | inr P =>
      show symmDiff P.support (listToggle₂ (bs.map (ofToggle Q))) =
        symmDiff P.support (listToggle₂ bs)
      rw [ih]

/-- The second-side version of `ofToggle`: for a side-2 block `Q` of `(s; s')`, a side block of
`(s.1, s.2 ⊕ Q; s')` is a side block of `(s; s')`. -/
def ofToggle₂ (Q : G.OddBlock s.2 s'.2) :
    G.SideBlock (s.1, symmDiff s.2 Q.support) s' → G.SideBlock s s'
  | .inl P => .inl P
  | .inr P => .inr (P.ofToggle Q.support_subset_symmDiff Q.isInducedComponent_support)

@[simp] theorem support_ofToggle₂ (Q : G.OddBlock s.2 s'.2)
    (B : G.SideBlock (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q B).support = B.support := by
  cases B <;> rfl

@[simp] theorem word_ofToggle₂ (Q : G.OddBlock s.2 s'.2)
    (B : G.SideBlock (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q B).word = B.word := by
  cases B <;> rfl

theorem listToggle₁_map_ofToggle₂ (Q : G.OddBlock s.2 s'.2)
    (bs : List (G.SideBlock (s.1, symmDiff s.2 Q.support) s')) :
    listToggle₁ (bs.map (ofToggle₂ Q)) = listToggle₁ bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    cases B with
    | inl P =>
      show symmDiff P.support (listToggle₁ (bs.map (ofToggle₂ Q))) =
        symmDiff P.support (listToggle₁ bs)
      rw [ih]
    | inr P => exact ih

theorem listToggle₂_map_ofToggle₂ (Q : G.OddBlock s.2 s'.2)
    (bs : List (G.SideBlock (s.1, symmDiff s.2 Q.support) s')) :
    listToggle₂ (bs.map (ofToggle₂ Q)) = listToggle₂ bs := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    cases B with
    | inl P => exact ih
    | inr P =>
      show symmDiff P.support (listToggle₂ (bs.map (ofToggle₂ Q))) =
        symmDiff P.support (listToggle₂ bs)
      rw [ih]

end SideBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-! ### Swapping the two sides -/

/-- Exchanging the two sides: a fixed-pairing deformation of `s = (C_a, C_b)` by `s' = (C'_c, C'_d)`
with the pairing `a ↔ c`, `b ↔ d` is the same data as one of `s.swap = (C_b, C_a)` by
`s'.swap = (C'_d, C'_c)` with the pairing `b ↔ d`, `a ↔ c`.  This is the "without loss of
generality `(a, c)` pairing" of v1 Definition 19 (L982): the `(a, d)` pairing of `(s, s')` is
the `(a, c)` pairing of `(s, s'.swap)`. -/
def swapSides (D : G.FPDeformation s s') : G.FPDeformation s.swap s'.swap where
  blocks := D.blocks.map SideBlock.swap
  nodup := by
    simpa [List.map_map, Function.comp_def] using D.nodup

@[simp] theorem blocks_swapSides (D : G.FPDeformation s s') :
    D.swapSides.blocks = D.blocks.map SideBlock.swap := rfl

/-- Exchanging the sides does not change the word. -/
@[simp] theorem word_swapSides (D : G.FPDeformation s s') : D.swapSides.word = D.word := by
  simp [word, List.flatMap_map]

/-- The side-1 toggle of the swapped deformation is the side-2 toggle. -/
@[simp] theorem toggle₁_swapSides (D : G.FPDeformation s s') :
    D.swapSides.toggle₁ = D.toggle₂ :=
  SideBlock.listToggle₁_map_swap D.blocks

/-- The side-2 toggle of the swapped deformation is the side-1 toggle. -/
@[simp] theorem toggle₂_swapSides (D : G.FPDeformation s s') :
    D.swapSides.toggle₂ = D.toggle₁ :=
  SideBlock.listToggle₂_map_swap D.blocks

/-- Exchanging the sides does not change the toggle `T = T₁ ⊕ T₂`. -/
theorem toggle_swapSides (D : G.FPDeformation s s') : D.swapSides.toggle = D.toggle := by
  simp [toggle, symmDiff_comm]

/-- The forward end state of the swapped deformation is the swapped forward end state. -/
theorem fwdEnd_swapSides (D : G.FPDeformation s s') : D.swapSides.fwdEnd = D.fwdEnd.swap := by
  simp [fwdEnd]

/-- The backward end state of the swapped deformation is the swapped backward end state. -/
theorem bwdEnd_swapSides (D : G.FPDeformation s s') : D.swapSides.bwdEnd = D.bwdEnd.swap := by
  simp [bwdEnd]

/-- Exchanging the sides twice gives back the deformation. -/
@[simp] theorem swapSides_swapSides (D : G.FPDeformation s s') : D.swapSides.swapSides = D := by
  apply FPDeformation.ext
  simp only [blocks_swapSides, List.map_map, Function.comp_def, SideBlock.swap_swap]
  exact List.map_id' _

/-- Exchanging the sides preserves palindromicity: the clone runs out of `s` and `s'` correspond to
those out of `s.swap` and `s'.swap` (`ClassRun.swap_iff`). -/
theorem palindromic_swapSides_iff (D : G.FPDeformation s s') :
    D.swapSides.Palindromic ↔ D.Palindromic := by
  unfold Palindromic
  rw [word_swapSides, exists_classRun_swap_iff, exists_classRun_swap_iff]

/-- Exchanging the sides preserves oddness: `c(T, C)` only depends on the carrier `C = C_a ∪ C_b`
and on `T = T₁ ⊕ T₂`. -/
theorem isOdd_swapSides_iff (D : G.FPDeformation s s') : D.swapSides.IsOdd ↔ D.IsOdd := by
  unfold IsOdd
  rw [toggle_swapSides]
  simp only [Prod.fst_swap, Prod.snd_swap, Finset.union_comm]

/-! ### The mirror (reverse) deformation -/

/-- The reverse deformation `O⃖` of `D` (v1 L1015-1016: "reversing the order of the paths"; v1
L1120: `O⃖` is a deformation of `C'` by vertices in `C` when `D` is palindromic): the list of blocks
is reversed and each block is read backwards (`SideBlock.reverse`).  It is a deformation of `s'` by
`s` with the same pairing.  Whether its word is a clone run from `s'` is the second conjunct of
`D.Palindromic` (`palindromic_mirror_iff`). -/
def mirror (D : G.FPDeformation s s') : G.FPDeformation s' s :=
  ⟨SideBlock.mirrorList D.blocks, SideBlock.nodup_mirrorList D.nodup⟩

theorem blocks_mirror (D : G.FPDeformation s s') :
    D.mirror.blocks = (D.blocks.map SideBlock.reverse).reverse := rfl

/-- The word of the mirror is the reversed word (the reversed list of swapped pairs). -/
theorem word_mirror (D : G.FPDeformation s s') : D.mirror.word = reverseWord D.word :=
  SideBlock.flatMap_word_mirrorList D.blocks

/-- Mirroring does not change the side-1 toggle. -/
theorem toggle₁_mirror (D : G.FPDeformation s s') : D.mirror.toggle₁ = D.toggle₁ :=
  SideBlock.listToggle₁_mirrorList D.nodup

/-- Mirroring does not change the side-2 toggle. -/
theorem toggle₂_mirror (D : G.FPDeformation s s') : D.mirror.toggle₂ = D.toggle₂ :=
  SideBlock.listToggle₂_mirrorList D.nodup

/-- Mirroring does not change the toggle `T`. -/
theorem toggle_mirror (D : G.FPDeformation s s') : D.mirror.toggle = D.toggle := by
  simp only [toggle, toggle₁_mirror, toggle₂_mirror]

/-- The forward end state of the mirror is the backward end state of `D`. -/
theorem fwdEnd_mirror (D : G.FPDeformation s s') : D.mirror.fwdEnd = D.bwdEnd := by
  simp only [fwdEnd, bwdEnd, toggle₁_mirror, toggle₂_mirror]

/-- The backward end state of the mirror is the forward end state of `D`. -/
theorem bwdEnd_mirror (D : G.FPDeformation s s') : D.mirror.bwdEnd = D.fwdEnd := by
  simp only [fwdEnd, bwdEnd, toggle₁_mirror, toggle₂_mirror]

/-- Mirroring twice gives back the deformation. -/
@[simp] theorem mirror_mirror (D : G.FPDeformation s s') : D.mirror.mirror = D := by
  apply FPDeformation.ext
  simp [blocks_mirror, List.map_reverse, List.map_map, Function.comp_def]

/-- The mirror of a one-block deformation is the one-block deformation of the reversed block. -/
theorem mirror_single (B : G.SideBlock s s') : (single B).mirror = single B.reverse := by
  apply FPDeformation.ext
  simp [blocks_mirror]

/-- A deformation is palindromic iff its mirror is: the two conjuncts of `Palindromic` (the word
runs from `s`; the reversed word runs from `s'`) are exchanged, since
`reverseWord (reverseWord w) = w`. -/
theorem palindromic_mirror_iff (D : G.FPDeformation s s') :
    D.mirror.Palindromic ↔ D.Palindromic := by
  unfold Palindromic
  rw [word_mirror, reverseWord_reverseWord, and_comm]

/-- The mirror of a palindromic deformation is palindromic ("`O⃖` is a deformation of `C'` by
vertices in `C`", v1 L1120).  The hypotheses `hs`, `hs'` are not needed
(`palindromic_mirror_iff`). -/
theorem palindromic_mirror (_hs : G.IsHoleClasses s) (_hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) : D.mirror.Palindromic :=
  D.palindromic_mirror_iff.2 hD

/-! ### Parity of the toggle against the two carriers -/

/-- For a palindromic deformation, the parity of `c(T, C)` equals that of `c(T, C')`.  This is the
frame exponent symmetry (`IsHoleClasses.crossCount_toggle_mod_two_symm`) for the two end states
`(s.1 ⊕ T₁, s.2 ⊕ T₂)` and `(s'.1 ⊕ T₁, s'.2 ⊕ T₂)` of `D` (hole-class states by
`Palindromic.isHoleClasses_ends`), with `T₁ ⊆ s.1 ⊕ s'.1` and `T₂ ⊆ s.2 ⊕ s'.2`. -/
theorem Palindromic.crossCount_toggle_mod_two_symm {D : G.FPDeformation s s'}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (hD : D.Palindromic) :
    G.crossCount D.toggle (s.1 ∪ s.2) % 2 = G.crossCount D.toggle (s'.1 ∪ s'.2) % 2 := by
  obtain ⟨ht, ht'⟩ := hD.isHoleClasses_ends hs hs'
  exact IsHoleClasses.crossCount_toggle_mod_two_symm hs hs' ht ht' rfl rfl rfl rfl
    D.toggle₁_subset D.toggle₂_subset

/-- For a palindromic deformation, `c(T, C)` is odd iff `c(T, C')` is. -/
theorem Palindromic.odd_crossCount_toggle_iff {D : G.FPDeformation s s'}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (hD : D.Palindromic) :
    Odd (G.crossCount D.toggle (s.1 ∪ s.2)) ↔ Odd (G.crossCount D.toggle (s'.1 ∪ s'.2)) := by
  rw [Nat.odd_iff, Nat.odd_iff, hD.crossCount_toggle_mod_two_symm hs hs']

/-- For a palindromic `D`, the mirror is odd iff `D` is: `c(T, C') ≡ c(T, C)` (mod `2`), and the
toggle of the mirror is that of `D`. -/
theorem isOdd_mirror_iff (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) : D.mirror.IsOdd ↔ D.IsOdd := by
  unfold IsOdd
  rw [toggle_mirror]
  exact (hD.odd_crossCount_toggle_iff hs hs').symm

/-! ### One-block deformations -/

/-- A one-block deformation is palindromic iff its block runs forward from `s` and backward from
`s'` (v1 L965-967: the palindromic path). -/
theorem palindromic_single_iff (B : G.SideBlock s s') :
    (single B).Palindromic ↔ B.RunsFrom ∧ B.RunsBack := by
  simp [Palindromic, SideBlock.RunsFrom, SideBlock.RunsBack]

/-! ### Transport along a toggle of a block -/

/-- Transport along a toggle of a side-1 block: if `Q` is a block of `G[C_a ⊕ C'_c]`, a deformation
of `(C_a ⊕ Q, C_b)` by `s'` is a deformation of `s = (C_a, C_b)` by `s'` with the same blocks (their
side-1 blocks transported by `OddBlock.ofToggle`, since toggling the component `Q` of
`G[C_a ⊕ C'_c]` leaves the other components unchanged), hence the same word and the same toggle.
It is not claimed that the transported deformation is palindromic. -/
def ofToggle (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') : G.FPDeformation s s' where
  blocks := D.blocks.map (SideBlock.ofToggle Q)
  nodup := by
    simpa [List.map_map, Function.comp_def] using D.nodup

@[simp] theorem blocks_ofToggle (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q D).blocks = D.blocks.map (SideBlock.ofToggle Q) := rfl

/-- The transported deformation has the same word. -/
theorem ofToggle_word (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') : (ofToggle Q D).word = D.word := by
  simp [word, List.flatMap_map]

/-- The transported deformation has the same side-1 toggle. -/
theorem ofToggle_toggle₁ (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q D).toggle₁ = D.toggle₁ :=
  SideBlock.listToggle₁_map_ofToggle Q D.blocks

/-- The transported deformation has the same side-2 toggle. -/
theorem ofToggle_toggle₂ (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q D).toggle₂ = D.toggle₂ :=
  SideBlock.listToggle₂_map_ofToggle Q D.blocks

/-- The transported deformation has the same toggle. -/
theorem ofToggle_toggle (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q D).toggle = D.toggle := by
  simp only [toggle, ofToggle_toggle₁, ofToggle_toggle₂]

/-- The transported deformation has the same block supports. -/
theorem ofToggle_support (Q : G.OddBlock s.1 s'.1)
    (D : G.FPDeformation (symmDiff s.1 Q.support, s.2) s') :
    (ofToggle Q D).blocks.map SideBlock.support = D.blocks.map SideBlock.support := by
  simp [List.map_map, Function.comp_def]

/-- Transport along a toggle of a side-2 block: the second-side version of `ofToggle`. -/
def ofToggle₂ (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') : G.FPDeformation s s' where
  blocks := D.blocks.map (SideBlock.ofToggle₂ Q)
  nodup := by
    simpa [List.map_map, Function.comp_def] using D.nodup

@[simp] theorem blocks_ofToggle₂ (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q D).blocks = D.blocks.map (SideBlock.ofToggle₂ Q) := rfl

theorem ofToggle₂_word (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') : (ofToggle₂ Q D).word = D.word := by
  simp [word, List.flatMap_map]

theorem ofToggle₂_toggle₁ (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q D).toggle₁ = D.toggle₁ :=
  SideBlock.listToggle₁_map_ofToggle₂ Q D.blocks

theorem ofToggle₂_toggle₂ (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q D).toggle₂ = D.toggle₂ :=
  SideBlock.listToggle₂_map_ofToggle₂ Q D.blocks

theorem ofToggle₂_toggle (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q D).toggle = D.toggle := by
  simp only [toggle, ofToggle₂_toggle₁, ofToggle₂_toggle₂]

theorem ofToggle₂_support (Q : G.OddBlock s.2 s'.2)
    (D : G.FPDeformation (s.1, symmDiff s.2 Q.support) s') :
    (ofToggle₂ Q D).blocks.map SideBlock.support = D.blocks.map SideBlock.support := by
  simp [List.map_map, Function.comp_def]

end FPDeformation

end SimpleGraph
