import FreeFermionGraphs.T3GoodCandidate
import FreeFermionGraphs.T3PairingIndexUpdate
import FreeFermionGraphs.T3SeparatorComponent
import FreeFermionGraphs.T3Lift
import FreeFermionGraphs.T3PalindromicToggles

/-!
# Existence of an odd palindromic deformation when `Ψ < 0`

This module proves the existence statement behind the synthesised proof of Theorem 1(iii) of
arXiv 2305.15625 v1 (label `theorem:conservedcharges`), package T3-25.  v1 obtains an odd
palindromic deformation from the *obstruction search* (the "correctness of the search process",
L1170-1198: the search terminates in a palindromic deformation whose boundary `∂O` meets `W` in
an odd number of vertices, L1226-1227).  Here the same existence statement is proved by a different
route, an induction on the symmetric-difference measure of the pair of class states, which combines
the three ingredients proved in the earlier packages of this wave:

* the good candidate theorem (T3-20, `SimpleGraph.exists_goodCandidate`), which replaces the
  pigeonhole argument of v1 L1150-1172 that finds the starting vertex of the search;
* the update of `Ψ` after toggling a forward-running block (T3-21,
  `OddBlock.pairingIndex_fwdState`) and the separator lemma (T3-22,
  `OddBlock.separators_sameComponent`), which show that the good source can be removed without
  changing the sign of `Ψ` and that the lift hypothesis holds;
* the lift lemma (T3-24, `FPDeformation.lift`), which turns a palindromic deformation of the
  reduced pair into one of the original pair, preserving the parity of the toggle.

## Main results

* `SimpleGraph.symmDiffMeasure s s' = |s.1 ⊕ s'.1| + |s.2 ⊕ s'.2|`, the measure of the induction.
* `SimpleGraph.HasOddPalindromic G s s'`: some `D : G.FPDeformation s s'` is palindromic and odd.
* `SimpleGraph.FPDeformation.exists_palindromic_odd` (part (a) of the package): for a claw-free
  graph and hole-class states `s`, `s'` with `Ψ(s, s') < 0` there is a palindromic odd
  fixed-pairing-type deformation of `s` by `s'`.
* `SimpleGraph.palindromicToggles_nonempty` (part (b) of the package): if `c(C, C')` is odd, the
  candidate set `K*(C, C')` of palindromic toggles is nonempty.

## Proof of (a)

Strong induction on `n = |s.1 ⊕ s'.1| + |s.2 ⊕ s'.2|`, for all hole-class pairs with `Ψ < 0` at once.
By `exists_goodCandidate` one of three cases holds.

* (i) Some side block `B` runs forward from `s` and backward from `s'` and has
  `|B ∩ matchedW s s'| = 1`, `|B ∩ crossedW s s'| = 0`.  Then `D = single B` is palindromic
  (`palindromic_single_iff`) and odd: its toggle is `B`, and `c(B, C) ≡ |B ∩ W| = 1` (mod 2)
  by `OddBlock.crossCount_carrier_mod_two` (T3-23 (b)), with `W = matchedW s s' ∪ crossedW s s'`
  (`exists_of_key`).
* (ii) Some side block `B` of `(s, s')` is a good source.  By exchanging the two sides
  (`HasOddPalindromic.of_swap`, `GoodSource.swap`) we may assume that `B = Q` is a side-1 block.
  Let `t = (s.1 ⊕ Q, s.2)`.  It is a hole-class state, `Ψ(t, s') = Ψ(s, s') < 0` because the
  balanced condition `(m', x') ∈ {(0, 0), (1, 1)}` makes the correction of
  `pairingIndex_fwdState` vanish, and the measure drops by `|Q| ≥ 2`.  The induction hypothesis
  gives an odd palindromic `D₁` at `(t, s')`; the lift lemma, with the separator lemma supplying
  its hypothesis `hsep`, gives an odd palindromic deformation at `(s, s')`
  (`exists_of_goodSource_inl`).
* (iii) Some side block of `(s', s)` is a good source.  Case (ii) applied to `(s', s)`, which has the
  same `Ψ` (`pairingIndex_comm`) and the same measure, gives an odd palindromic deformation at
  `(s', s)`, and its mirror (`FPDeformation.mirror`, `isOdd_mirror_iff`) is one at `(s, s')`
  (`HasOddPalindromic.mirror`).

## Proof of (b)

If `c(C, C')` is odd then `Ψ(s, s') ≡ c(C, C')` is odd (`pairingIndex_emod_two`), so `Ψ(s, s') ≠ 0`.
If `Ψ(s, s') < 0`, part (a) gives a palindromic odd `D` and `D.toggle ∈ K*(C, C')`
(`mem_palindromicToggles_of_palindromic`).  If `Ψ(s, s') > 0`, then `Ψ(s, s'.swap) = -Ψ(s, s') < 0`
(`pairingIndex_swap_right`), `s'.swap` is a hole-class state with the same carrier `C'`, and the
same argument applies to `(s, s'.swap)`.

## Notes on the statement

* v1 argues existence by the obstruction search and records the oddness of the resulting
  deformation through `|W ∩ ∂O|` odd (L1226-1227).  The route here is different and gives the same
  conclusion; it is not a transcription of v1's search.
* No anticommutation hypothesis `[h_C, h_{C'}] ≠ 0` is used: part (a) holds for every pair of
  hole-class states with `Ψ < 0`, including commuting pairs.  Claw-freeness enters through the
  results of the earlier packages.
* The statement (a) has the single premise `Ψ(s, s') < 0`, which is the hypothesis of the
  manuscript's source-type case (v1 Definition 21, L1016-1019: the source set of the obstruction
  graph is the larger colouring class), and the setup hypotheses (claw-freeness, hole classes).
  The statement (b) has the single premise that `c(C, C')` is odd.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### The measure of the induction -/

section Measure

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- The measure of the induction for the pair of class states `(s, s')`:
`|s.1 ⊕ s'.1| + |s.2 ⊕ s'.2|`, the total size of the two side graphs `G[s.1 ⊕ s'.1]` and
`G[s.2 ⊕ s'.2]`. -/
def symmDiffMeasure (s s' : Finset V × Finset V) : ℕ :=
  (symmDiff s.1 s'.1).card + (symmDiff s.2 s'.2).card

/-- The measure is unchanged by exchanging the two classes of both states. -/
theorem symmDiffMeasure_swap : symmDiffMeasure s.swap s'.swap = symmDiffMeasure s s' := by
  simp only [symmDiffMeasure, Prod.fst_swap, Prod.snd_swap]
  exact Nat.add_comm _ _

/-- The measure is symmetric in the two states. -/
theorem symmDiffMeasure_comm : symmDiffMeasure s' s = symmDiffMeasure s s' := by
  simp only [symmDiffMeasure]
  rw [symmDiff_comm s'.1, symmDiff_comm s'.2]

/-- Toggling a side-1 block `Q` in the first class of the first state strictly decreases the
measure: the side-1 symmetric difference loses the (nonempty) support of `Q`. -/
theorem symmDiffMeasure_toggle_lt (Q : G.OddBlock s.1 s'.1) :
    symmDiffMeasure (symmDiff s.1 Q.support, s.2) s' < symmDiffMeasure s s' := by
  have hsub : Q.support ⊆ symmDiff s.1 s'.1 := Q.support_subset_symmDiff
  have hne : Q.support.Nonempty := ⟨Q.first, Q.first_mem_support⟩
  have h1 : symmDiff (symmDiff s.1 Q.support) s'.1 = symmDiff s.1 s'.1 \ Q.support := by
    rw [symmDiff_right_comm]
    exact symmDiff_of_ge hsub
  have h2 : (symmDiff s.1 s'.1 \ Q.support).card < (symmDiff s.1 s'.1).card :=
    Finset.card_lt_card (Finset.sdiff_ssubset hsub hne)
  simp only [symmDiffMeasure]
  rw [h1]
  omega

end Measure

/-! ### The existence predicate -/

/-- Some fixed-pairing-type deformation of `s` by `s'` is palindromic and odd. -/
def HasOddPalindromic (G : SimpleGraph V) [DecidableEq V] (s s' : Finset V × Finset V) : Prop :=
  ∃ D : G.FPDeformation s s', D.Palindromic ∧ D.IsOdd

section Predicate

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- Exchanging the two sides of both states preserves the existence of an odd palindromic
deformation (`FPDeformation.swapSides`). -/
theorem HasOddPalindromic.swap (h : G.HasOddPalindromic s s') :
    G.HasOddPalindromic s.swap s'.swap := by
  obtain ⟨D, hD, hodd⟩ := h
  exact ⟨D.swapSides, D.palindromic_swapSides_iff.2 hD, D.isOdd_swapSides_iff.2 hodd⟩

/-- An odd palindromic deformation of the swapped states gives one of the original states. -/
theorem HasOddPalindromic.of_swap (h : G.HasOddPalindromic s.swap s'.swap) :
    G.HasOddPalindromic s s' := by
  have h' := h.swap
  rwa [Prod.swap_swap, Prod.swap_swap] at h'

/-- An odd palindromic deformation of `(s, s')` gives one of `(s', s)`: its mirror
(`FPDeformation.mirror`), which has the same toggle. -/
theorem HasOddPalindromic.mirror (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (h : G.HasOddPalindromic s s') : G.HasOddPalindromic s' s := by
  obtain ⟨D, hD, hodd⟩ := h
  exact ⟨D.mirror, D.palindromic_mirror hs hs' hD, (D.isOdd_mirror_iff hs hs' hD).2 hodd⟩

end Predicate

/-! ### Counting lemmas -/

section Counting

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

omit [Fintype V] in
/-- The number of vertices of a set `S` in `W = matchedW s s' ∪ crossedW s s'` is the sum of the
numbers in the two disjoint parts. -/
theorem card_inter_matchedW_union_crossedW (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (S : Finset V) :
    (S ∩ (G.matchedW s s' ∪ G.crossedW s s')).card =
      (S ∩ G.matchedW s s').card + (S ∩ G.crossedW s s').card := by
  rw [Finset.inter_union_distrib_left]
  refine Finset.card_union_of_disjoint ?_
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (anticommutingVertices_eq_matchedW_union_crossedW hclaw hs hs').2)

end Counting

/-! ### The parity of a side block against the carrier -/

namespace SideBlock

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

omit [Fintype V] in
/-- **Parity of the incidence of a side block with the carrier `C`**: for both sides,
`c(B, C) ≡ |B ∩ W| (mod 2)` with `W = matchedW s s' ∪ crossedW s s'` (T3-23 (b),
`OddBlock.crossCount_carrier_mod_two`; a side-2 block is treated through the swapped states). -/
theorem crossCount_carrier_mod_two (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (B : G.SideBlock s s') :
    G.crossCount B.support (s.1 ∪ s.2) % 2 =
      (B.support ∩ (G.matchedW s s' ∪ G.crossedW s s')).card % 2 := by
  cases B with
  | inl Q => exact Q.crossCount_carrier_mod_two hclaw hs hs'
  | inr Q =>
    have h := OddBlock.crossCount_carrier_mod_two hclaw hs.swap hs'.swap
      (Q : G.OddBlock s.swap.1 s'.swap.1)
    rw [matchedW_swap_swap, crossedW_swap_swap] at h
    simpa only [support_inr, Prod.fst_swap, Prod.snd_swap, Finset.union_comm s.2 s.1] using h

end SideBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- The toggle of a one-block deformation is the support of the block. -/
theorem toggle_single (B : G.SideBlock s s') : (single B).toggle = B.support := by
  cases B with
  | inl P => simp [toggle, toggle₁_single_inl, toggle₂_single_inl]
  | inr P => simp [toggle, toggle₁_single_inr, toggle₂_single_inr]

end FPDeformation

/-! ### Case (i): the key block -/

section Key

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Case (i) of the induction**: a side block which runs forward from `s` and backward from `s'`
and meets `matchedW s s'` in one vertex and `crossedW s s'` in none gives the odd palindromic
deformation `single B`.  It is palindromic by `FPDeformation.palindromic_single_iff` and odd since
`c(B, C) ≡ |B ∩ W| = 1` (mod 2). -/
theorem exists_of_key (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (B : G.SideBlock s s') (h1 : B.RunsFrom) (h2 : B.RunsBack)
    (h3 : (B.support ∩ G.matchedW s s').card = 1) (h4 : (B.support ∩ G.crossedW s s').card = 0) :
    G.HasOddPalindromic s s' := by
  refine ⟨FPDeformation.single B, (FPDeformation.palindromic_single_iff B).2 ⟨h1, h2⟩, ?_⟩
  unfold FPDeformation.IsOdd
  rw [FPDeformation.toggle_single, Nat.odd_iff, SideBlock.crossCount_carrier_mod_two hclaw hs hs' B,
    card_inter_matchedW_union_crossedW hclaw hs hs', h3, h4]

end Key

/-! ### Case (ii): a good side-1 source -/

section GoodSource

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Case (ii) of the induction, side 1**: a good side-1 source `Q` of `(s, s')` together with the
induction hypothesis for pairs of smaller measure gives an odd palindromic deformation of
`(s, s')`.

The state `t = (s.1 ⊕ Q, s.2)` reached by the run of `Q` is a hole-class state with
`Ψ(t, s') = Ψ(s, s') < 0` (the balanced condition on `(m', x')` kills the correction of
`OddBlock.pairingIndex_fwdState`) and smaller measure (`symmDiffMeasure_toggle_lt`).  The induction
hypothesis gives an odd palindromic `D₁` at `(t, s')`, and the lift lemma `FPDeformation.lift`
transports it to `(s, s')` (its hypothesis `hsep` is the separator lemma
`OddBlock.separators_sameComponent`). -/
theorem exists_of_goodSource_inl (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hneg : G.pairingIndex s s' < 0) (Q : G.OddBlock s.1 s'.1)
    (hgood : SideBlock.GoodSource (Sum.inl Q : G.SideBlock s s'))
    (ih : ∀ t t' : Finset V × Finset V, G.IsHoleClasses t → G.IsHoleClasses t' →
      G.pairingIndex t t' < 0 → symmDiffMeasure t t' < symmDiffMeasure s s' →
        G.HasOddPalindromic t t') :
    G.HasOddPalindromic s s' := by
  obtain ⟨hQ, hm, hx, hbal⟩ := hgood
  have hQ' : Q.RunsFrom s := hQ
  have hm' : (Q.support ∩ G.matchedW s s').card = 1 := hm
  have hx' : (Q.support ∩ G.crossedW s s').card = 0 := hx
  have hbal' : ((Q.support ∩ G.matchedW s' s).card = 0 ∧ (Q.support ∩ G.crossedW s' s).card = 0) ∨
      ((Q.support ∩ G.matchedW s' s).card = 1 ∧ (Q.support ∩ G.crossedW s' s).card = 1) := hbal
  have ht : G.IsHoleClasses (symmDiff s.1 Q.support, s.2) := Q.isHoleClasses_toggle hs hQ'
  have hΨ : G.pairingIndex (symmDiff s.1 Q.support, s.2) s' < 0 := by
    rw [Q.pairingIndex_fwdState hclaw hs hs' hQ']
    rcases hbal' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  obtain ⟨D₁, hD₁, hodd₁⟩ := ih _ _ ht hs' hΨ (symmDiffMeasure_toggle_lt Q)
  have hW : (Q.support ∩ (G.matchedW s s' ∪ G.crossedW s s')).card = 1 := by
    rw [card_inter_matchedW_union_crossedW hclaw hs hs', hm', hx']
  have hW' : Even (Q.support ∩ (G.matchedW s' s ∪ G.crossedW s' s)).card := by
    rw [card_inter_matchedW_union_crossedW hclaw hs' hs]
    rcases hbal' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  have hsep : ∀ u ∈ Q.separators s'.2, ∀ v ∈ Q.separators s'.2,
      v ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u := fun u hu v hv =>
    Q.separators_sameComponent hclaw hs hs' hQ' hbal' hu hv
  rcases FPDeformation.lift hclaw hs hs' Q hQ' hW hW' hsep D₁ hD₁ with
    ⟨hpal, hiff⟩ | ⟨hQnew, hpal, hiff⟩
  · exact ⟨FPDeformation.ofToggle Q D₁, hpal, hiff.2 hodd₁⟩
  · exact ⟨FPDeformation.cons (.inl Q) (FPDeformation.ofToggle Q D₁) hQnew, hpal, hiff.2 hodd₁⟩

/-- **Case (ii) of the induction**: a good source among the side blocks of `(s, s')`, on either
side.  A side-2 good source is a side-1 good source of the swapped states
(`SideBlock.GoodSource.swap`), and the swap preserves the pairing index and the measure. -/
theorem exists_of_goodSource (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hneg : G.pairingIndex s s' < 0) (B : G.SideBlock s s')
    (hgood : B.GoodSource)
    (ih : ∀ t t' : Finset V × Finset V, G.IsHoleClasses t → G.IsHoleClasses t' →
      G.pairingIndex t t' < 0 → symmDiffMeasure t t' < symmDiffMeasure s s' →
        G.HasOddPalindromic t t') :
    G.HasOddPalindromic s s' := by
  cases B with
  | inl Q => exact exists_of_goodSource_inl hclaw hs hs' hneg Q hgood ih
  | inr Q =>
    refine HasOddPalindromic.of_swap ?_
    refine exists_of_goodSource_inl hclaw hs.swap hs'.swap ?_ Q hgood.swap ?_
    · rw [pairingIndex_swap_swap hs.disjoint hs'.disjoint]
      exact hneg
    · intro t t' ht ht' hlt hmeas
      rw [symmDiffMeasure_swap] at hmeas
      exact ih t t' ht ht' hlt hmeas

end GoodSource

/-! ### Existence -/

section Existence

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Existence of an odd palindromic deformation, by strong induction on the measure.**  For a
claw-free graph, every pair of hole-class states `(s, s')` with `Ψ(s, s') < 0` and
`|s.1 ⊕ s'.1| + |s.2 ⊕ s'.2| = n` has an odd palindromic fixed-pairing-type deformation.  This is
the induction behind `FPDeformation.exists_palindromic_odd`; the three cases of
`exists_goodCandidate` are handled by `exists_of_key`, `exists_of_goodSource` and, for a good source
of `(s', s)`, the same lemma at `(s', s)` followed by `HasOddPalindromic.mirror`. -/
theorem hasOddPalindromic_of_measure (hclaw : G.IsClawFree) :
    ∀ (n : ℕ) (s s' : Finset V × Finset V), G.IsHoleClasses s → G.IsHoleClasses s' →
      G.pairingIndex s s' < 0 → symmDiffMeasure s s' = n → G.HasOddPalindromic s s' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s s' hs hs' hneg hn
    have ih' : ∀ t t' : Finset V × Finset V, G.IsHoleClasses t → G.IsHoleClasses t' →
        G.pairingIndex t t' < 0 → symmDiffMeasure t t' < symmDiffMeasure s s' →
          G.HasOddPalindromic t t' := fun t t' ht ht' hlt hm =>
      ih _ (hn ▸ hm) t t' ht ht' hlt rfl
    rcases exists_goodCandidate hclaw hs hs' hneg with
      ⟨B, h1, h2, h3, h4⟩ | ⟨B, hB⟩ | ⟨B, hB⟩
    · exact exists_of_key hclaw hs hs' B h1 h2 h3 h4
    · exact exists_of_goodSource hclaw hs hs' hneg B hB ih'
    · refine HasOddPalindromic.mirror hs' hs ?_
      refine exists_of_goodSource hclaw hs' hs (by rwa [pairingIndex_comm]) B hB ?_
      intro t t' ht ht' hlt hm
      rw [symmDiffMeasure_comm (s := s) (s' := s')] at hm
      exact ih' t t' ht ht' hlt hm

end Existence

namespace FPDeformation

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Existence of an odd palindromic deformation when `Ψ < 0`** (package T3-25, part (a); the
existence claim of the correctness of the search process, v1 L1170-1198, with the oddness
`|W ∩ ∂O|` odd of v1 L1226-1227).  Let `G` be claw-free and `s`, `s'` hole-class states
(`IsHoleClasses`) with `Ψ(s, s') < 0` (`pairingIndex`).  Then some fixed-pairing-type deformation
`D : G.FPDeformation s s'` is palindromic and odd.

The proof is by strong induction on `|s.1 ⊕ s'.1| + |s.2 ⊕ s'.2|` (`symmDiffMeasure`), through the
good candidate theorem, the update of `Ψ`, the separator lemma and the lift lemma of the earlier
packages; it replaces the obstruction search of v1 and does not follow it.  No anticommutation
hypothesis is needed: the statement also holds for commuting pairs with `Ψ < 0`.  Its premises are
the manuscript setup (claw-freeness, hole classes) and the sign condition `Ψ(s, s') < 0`. -/
theorem exists_palindromic_odd (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hneg : G.pairingIndex s s' < 0) :
    ∃ D : G.FPDeformation s s', D.Palindromic ∧ D.IsOdd :=
  hasOddPalindromic_of_measure hclaw _ s s' hs hs' hneg rfl

end FPDeformation

/-! ### The candidate set is nonempty when `c(C, C')` is odd -/

section Toggles

variable [Fintype V] [DecidableEq V] {s s' : Finset V × Finset V}

/-- **The candidate set `K*(C, C')` is nonempty when `c(C, C')` is odd** (package T3-25, part (b);
v1 L1226-1227: `|W ∩ ∂O|` odd).  Let `G` be claw-free and `s`, `s'` hole-class states with carriers
`C = s.1 ∪ s.2` and `C' = s'.1 ∪ s'.2` such that `c(C, C')` (`crossCount`) is odd.  Then
`K*(C, C')` (`palindromicToggles`) is nonempty.

By `pairingIndex_emod_two` the pairing index `Ψ(s, s')` is odd, hence nonzero.  If `Ψ(s, s') < 0`
part (a) applies to `(s, s')`; otherwise `Ψ(s, s'.swap) = -Ψ(s, s') < 0`
(`pairingIndex_swap_right`) and part (a) applies to `(s, s'.swap)`, whose second state has the same
carrier `C'`.  The toggle of the resulting deformation lies in `K*(C, C')`
(`FPDeformation.mem_palindromicToggles_of_palindromic`). -/
theorem palindromicToggles_nonempty (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s')
    (hodd : Odd (G.crossCount (s.1 ∪ s.2) (s'.1 ∪ s'.2))) :
    (G.palindromicToggles (↑(s.1 ∪ s.2) : Set V) (↑(s'.1 ∪ s'.2) : Set V)).Nonempty := by
  have hmod : G.pairingIndex s s' % 2 = 1 := by
    rw [pairingIndex_emod_two hs.disjoint hs'.disjoint]
    have := Nat.odd_iff.1 hodd
    omega
  rcases lt_trichotomy (G.pairingIndex s s') 0 with hneg | hzero | hpos
  · obtain ⟨D, hD, hDodd⟩ := FPDeformation.exists_palindromic_odd hclaw hs hs' hneg
    exact ⟨D.toggle, FPDeformation.mem_palindromicToggles_of_palindromic hs hs' hneg hD hDodd⟩
  · rw [hzero] at hmod
    exact absurd hmod (by decide)
  · have hneg : G.pairingIndex s s'.swap < 0 := by
      rw [pairingIndex_swap_right hs'.disjoint]
      omega
    obtain ⟨D, hD, hDodd⟩ := FPDeformation.exists_palindromic_odd hclaw hs hs'.swap hneg
    refine ⟨D.toggle, mem_palindromicToggles.2
      ⟨s, s'.swap, hs, hs'.swap, rfl, ?_, hneg, D, hD, hDodd, rfl⟩⟩
    simp only [Prod.fst_swap, Prod.snd_swap, Finset.union_comm s'.2 s'.1]

end Toggles

end SimpleGraph
