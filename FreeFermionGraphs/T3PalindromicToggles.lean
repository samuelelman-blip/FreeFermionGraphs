import FreeFermionGraphs.T3PalindromicCancel
import FreeFermionGraphs.T3PairingIndex
import FreeFermionGraphs.ClawFree

/-!
# The candidate set `K*(C, C')` of palindromic toggles

This module defines the finite set `K*(C, C')` of toggles `T = D.toggle` of the odd palindromic
fixed-pairing-type deformations `D : G.FPDeformation s s'` whose class pairs `s`, `s'` are hole
classes (`SimpleGraph.IsHoleClasses`) with carriers `C = s.1 ∪ s.2` and `C' = s'.1 ∪ s'.2` and
negative pairing index `Ψ(s, s') < 0` (`SimpleGraph.pairingIndex`), in the synthesised proof of
Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, L1203-1241).  It is the (iii) analogue of
`SimpleGraph.untetheredSupports` (the set `𝒫(C, S)` of the proof of Theorem 1(ii)): a finite set
which depends on the pair of carriers `(C, C')` alone, not on a chosen deformation.

The condition `Ψ(s, s') < 0` selects v1's source type (Definition 21,
`definition:obstructiongraphcoloringclasses`, L1016-1019: the source set of the obstruction graph
is the larger colouring class).  Since `Ψ(s.swap, s'.swap) = Ψ(s, s')` and
`Ψ(s, s'.swap) = -Ψ(s, s')` (`pairingIndex_swap_swap`, `pairingIndex_swap_right`), the condition
fixes the class pair up to a simultaneous swap.  It plays no role in the three results below, which
hold for the toggle of every odd palindromic deformation of hole classes; it only restricts the
range of the set.

## Main results

* `SimpleGraph.palindromicToggles G C C'`: the finite set `K*(C, C')`, and its membership
  characterisation `SimpleGraph.mem_palindromicToggles`.
* `SimpleGraph.mem_palindromicToggles_of_palindromic`: the toggle of an odd palindromic deformation
  of hole classes with `Ψ(s, s') < 0` is in `K*(C, C')` (the converse direction of the
  characterisation, in introduction form).
* `SimpleGraph.palindromicToggles_toggle_data`: for `T ∈ K*(C, C')` the carriers `C ⊕ T` and
  `C' ⊕ T` lie in the even-hole deformation closures `⟨C⟩` and `⟨C'⟩` (v1 Definition 12, L700) and
  `T` is nonempty (`c(T, C)` is odd, so `T ≠ ∅`).
* `SimpleGraph.PauliFrustrationRepresentation.commutator_palindromicToggle`: for `T ∈ K*(C, C')`
  and every `PauliFrustrationRepresentation` over every ring,
  `[h_{C ⊕ T}, h_{C' ⊕ T}] = -[h_C, h_{C'}]` (the cancellation of v1 L1203-1241).

## Notes

* The hypothesis `G.IsClawFree` of `palindromicToggles_toggle_data` and
  `commutator_palindromicToggle` is part of the manuscript setup of Theorem 1 and is carried so that
  these statements have the same shape as the other results on the toggle sets (for instance
  `toggle_data_of_mem_untetheredSupports`).  The proofs do not use it: the underlying results
  (`FPDeformation.Palindromic.inClosure`, `commutator_palindromic_of_isOdd`) are unconditional.
* The set `K*(C, C')` may be empty, for instance when `C` and `C'` are not hole carriers or when no
  odd palindromic deformation exists; its non-emptiness for suitable `(C, C')` is a separate
  matter.  v1 only states the odd case of the sign, via `|W ∩ ∂O|` odd (L1219), which it does not
  argue (see `T3PalindromicCancel`).
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- **The candidate set `K*(C, C')` of palindromic toggles** (v1 L1203-1241; see the module
documentation): the set of toggles `T = D.toggle` of odd palindromic fixed-pairing-type
deformations `D : G.FPDeformation s s'` of hole-class states `s`, `s'` (`IsHoleClasses`) with
carriers `s.1 ∪ s.2 = C`, `s'.1 ∪ s'.2 = C'` and `Ψ(s, s') < 0` (`pairingIndex`).  The definition
is noncomputable so that the statements carry no choice of decidability instances as data. -/
noncomputable def palindromicToggles (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (C C' : Set V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun T => ∃ s s' : Finset V × Finset V,
    G.IsHoleClasses s ∧ G.IsHoleClasses s' ∧
      (↑(s.1 ∪ s.2) : Set V) = C ∧ (↑(s'.1 ∪ s'.2) : Set V) = C' ∧
      G.pairingIndex s s' < 0 ∧
      ∃ D : G.FPDeformation s s', D.Palindromic ∧ D.IsOdd ∧ D.toggle = T

/-- The cross count with the empty finset on the left vanishes. -/
private theorem crossCount_empty_left' (Y : Finset V) : G.crossCount ∅ Y = 0 := by
  classical
  rw [crossCount_eq_card_filter]
  simp

section Toggles

variable [Fintype V] [DecidableEq V]

/-- Membership in `K*(C, C')`: `T` is the toggle of an odd palindromic fixed-pairing-type
deformation of hole-class states `s`, `s'` with carriers `C`, `C'` and `Ψ(s, s') < 0`. -/
theorem mem_palindromicToggles {C C' : Set V} {T : Finset V} :
    T ∈ G.palindromicToggles C C' ↔ ∃ s s' : Finset V × Finset V,
      G.IsHoleClasses s ∧ G.IsHoleClasses s' ∧
        (↑(s.1 ∪ s.2) : Set V) = C ∧ (↑(s'.1 ∪ s'.2) : Set V) = C' ∧
        G.pairingIndex s s' < 0 ∧
        ∃ D : G.FPDeformation s s', D.Palindromic ∧ D.IsOdd ∧ D.toggle = T := by
  classical
  unfold palindromicToggles
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The toggle of an odd palindromic fixed-pairing-type deformation of hole-class states `s`, `s'`
with `Ψ(s, s') < 0` lies in `K*(s.1 ∪ s.2, s'.1 ∪ s'.2)`. -/
theorem FPDeformation.mem_palindromicToggles_of_palindromic {s s' : Finset V × Finset V}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (hΨ : G.pairingIndex s s' < 0)
    {D : G.FPDeformation s s'} (hD : D.Palindromic) (hodd : D.IsOdd) :
    D.toggle ∈ G.palindromicToggles (↑(s.1 ∪ s.2) : Set V) (↑(s'.1 ∪ s'.2) : Set V) :=
  mem_palindromicToggles.2 ⟨s, s', hs, hs', rfl, rfl, hΨ, D, hD, hodd, rfl⟩

omit [Fintype V] in
/-- The toggle of an odd deformation is nonempty: `c(∅, C) = 0` is even. -/
theorem FPDeformation.toggle_nonempty_of_isOdd {s s' : Finset V × Finset V}
    {D : G.FPDeformation s s'} (hodd : D.IsOdd) : D.toggle.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hT
  have h : Odd (G.crossCount (∅ : Finset V) (s.1 ∪ s.2)) := hT ▸ hodd
  rw [crossCount_empty_left'] at h
  exact (Nat.not_odd_zero h).elim

/-- **Toggle data of an element of `K*(C, C')`** (v1 L1219, L1236-1241).  If `T ∈ K*(C, C')`, then
the carriers `C ⊕ T` and `C' ⊕ T` lie in the even-hole deformation closures `⟨C⟩` and `⟨C'⟩`
(v1 Definition 12, L700) and `T` is nonempty.

This is `FPDeformation.Palindromic.inClosure` for the witnessing deformation, together with
`FPDeformation.toggle_nonempty_of_isOdd`.  The hypothesis `hclaw` is part of the manuscript setup of
Theorem 1 and is not used (see the module documentation). -/
theorem palindromicToggles_toggle_data (_hclaw : G.IsClawFree) {C C' : Set V} {T : Finset V}
    (hT : T ∈ G.palindromicToggles C C') :
    InEvenHoleDeformationClosure G C (symmDiff C ↑T) ∧
      InEvenHoleDeformationClosure G C' (symmDiff C' ↑T) ∧ T.Nonempty := by
  obtain ⟨s, s', hs, hs', rfl, rfl, -, D, hD, hodd, rfl⟩ := mem_palindromicToggles.1 hT
  obtain ⟨h₁, h₂⟩ := FPDeformation.Palindromic.inClosure hs hs' hD
  exact ⟨h₁, h₂, FPDeformation.toggle_nonempty_of_isOdd hodd⟩

end Toggles

namespace PauliFrustrationRepresentation

variable [Fintype V] [DecidableEq V] {A : Type w} [Ring A]

/-- **Cancellation by an element of `K*(C, C')`** (v1 L1203-1241).  For every
`PauliFrustrationRepresentation` `H` of `G` over every ring `A` and every `T ∈ K*(C, C')`, the
commutator of the hole operators of the toggled carriers is the negative of that of `C`, `C'`:
`[h_{C ⊕ T}, h_{C' ⊕ T}] = -[h_C, h_{C'}]`.

It is `commutator_palindromic_of_isOdd` for the odd palindromic deformation witnessing
`T ∈ K*(C, C')`.  The hypothesis `hclaw` is part of the manuscript setup of Theorem 1 and is not
used (see the module documentation). -/
theorem commutator_palindromicToggle (H : G.PauliFrustrationRepresentation A)
    (_hclaw : G.IsClawFree) {C C' : Set V} {T : Finset V}
    (hT : T ∈ G.palindromicToggles C C') :
    algebraCommutator (H.evenHoleOperator (symmDiff C ↑T))
        (H.evenHoleOperator (symmDiff C' ↑T)) =
      -algebraCommutator (H.evenHoleOperator C) (H.evenHoleOperator C') := by
  obtain ⟨s, s', hs, hs', rfl, rfl, -, D, hD, hodd, rfl⟩ := mem_palindromicToggles.1 hT
  exact H.commutator_palindromic_of_isOdd hs hs' hD hodd

end PauliFrustrationRepresentation

end SimpleGraph
