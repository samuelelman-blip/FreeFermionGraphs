import FreeFermionGraphs.T3FrameSign
import FreeFermionGraphs.T3FixedPairing

/-!
# Cancellation by a palindromic deformation

This module formalises the cancellation identity in the proof of cancellation in the proof of
Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, L1203-1241): the hole commutators
`[h_C, h_{C'}]` and `[h_{C̃}, h_{C̃'}]` of the two end carriers of a deformation are related by a
sign, so that for an odd deformation the two terms cancel.

For hole classes `s`, `s'` (`SimpleGraph.IsHoleClasses`) and a palindromic fixed-pairing-type
deformation `D : G.FPDeformation s s'` (`SimpleGraph.FPDeformation.Palindromic`, v1 L965-967 and
L1015-1021) with toggle `T` (`FPDeformation.toggle`, v1's `⊕_r P^{(r)}`, Definition 19, L986), the
carriers of the two end states are `C ⊕ T` and `C' ⊕ T` (`FPDeformation.carrier_fwdEnd`,
`carrier_bwdEnd`), and the end states are again hole-class states
(`FPDeformation.Palindromic.isHoleClasses_ends`).

## Main results

* `PauliFrustrationRepresentation.commutator_palindromic`:
  `[h_{C ⊕ T}, h_{C' ⊕ T}] = (-1)^{c(T, C)} [h_C, h_{C'}]`, with `c = crossCount`, `C = s.1 ∪ s.2`,
  `C' = s'.1 ∪ s'.2` and `[x, y] = x y - y x` (`algebraCommutator`).  It is the frame sign lemma
  `commutator_toggle_holeClasses` applied to the two end states of `D`.
* `PauliFrustrationRepresentation.commutator_palindromic_of_isOdd`: if `D.IsOdd`
  (`Odd (c(T, C))`), the commutator flips sign: `[h_{C ⊕ T}, h_{C' ⊕ T}] = -[h_C, h_{C'}]`.
* `PauliFrustrationRepresentation.commutator_palindromic_add_eq_zero_of_isOdd`: the cancellation
  itself, `[h_C, h_{C'}] + [h_{C ⊕ T}, h_{C' ⊕ T}] = 0` for an odd palindromic deformation.
* `PauliFrustrationRepresentation.commutator_palindromic_of_even`: for `Even (c(T, C))` the two
  commutators agree, so there is no cancellation.

## Relation to v1

v1 (L1203-1241) derives the sign from the scale-factor bookkeeping `h_O^2 = (h_O^†)^2`, the
anti-hermiticity of `h_O` and the claim that the number of vertices of `W` in the paths is odd.
Here the sign is *intrinsic*, `(-1)^{c(T, C)}`, where `c(T, C)` is the number of edges between the
toggle and the carrier `C`; no relation `h_j^2 = b_j^2`, no anticommutation hypothesis, no
claw-freeness and no conjugation by `h_O` is used, and the identities hold for every
`PauliFrustrationRepresentation` over every ring.  Whether a particular deformation is odd
(`FPDeformation.IsOdd`) is not argued here; v1 only states the odd case, via `|W ∩ ∂O|` odd,
which it does not argue.
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A] [DecidableEq V]
  {s s' : Finset V × Finset V}

/-- **Cancellation identity** (v1 L1203-1241, closed-form sign): for hole classes `s`, `s'` and a
palindromic fixed-pairing-type deformation `D : G.FPDeformation s s'` with toggle `T`,
`[h_{C ⊕ T}, h_{C' ⊕ T}] = (-1)^{c(T, C)} [h_C, h_{C'}]`, where `C = s.1 ∪ s.2`,
`C' = s'.1 ∪ s'.2`, `c = crossCount` and `[x, y] = x y - y x` is `algebraCommutator`.

It is `commutator_toggle_holeClasses` for the end states `t = D.fwdEnd`, `t' = D.bwdEnd`
(hole-class states by `Palindromic.isHoleClasses_ends`) with `Q₁ = D.toggle₁`, `Q₂ = D.toggle₂`
(`FPDeformation.toggle₁_subset`, `toggle₂_subset`), after rewriting their carriers as
`C ⊕ T` and `C' ⊕ T` (`FPDeformation.carrier_fwdEnd`, `carrier_bwdEnd`).  The statement holds for
every `PauliFrustrationRepresentation` over every ring. -/
theorem commutator_palindromic (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {D : G.FPDeformation s s'}
    (hD : D.Palindromic) :
    algebraCommutator (H.evenHoleOperator (symmDiff ↑(s.1 ∪ s.2) ↑D.toggle))
        (H.evenHoleOperator (symmDiff ↑(s'.1 ∪ s'.2) ↑D.toggle)) =
      (-1 : A) ^ G.crossCount D.toggle (s.1 ∪ s.2) *
        algebraCommutator (H.evenHoleOperator ↑(s.1 ∪ s.2))
          (H.evenHoleOperator ↑(s'.1 ∪ s'.2)) := by
  obtain ⟨ht, ht'⟩ := hD.isHoleClasses_ends hs hs'
  have key := H.commutator_toggle_holeClasses hs hs' ht ht' (Q₁ := D.toggle₁) (Q₂ := D.toggle₂)
    rfl rfl rfl rfl D.toggle₁_subset D.toggle₂_subset
  rw [FPDeformation.carrier_fwdEnd hs hs' D hD, FPDeformation.carrier_bwdEnd hs hs' D hD,
    Finset.coe_symmDiff, Finset.coe_symmDiff] at key
  exact key

/-- For an odd palindromic deformation (`D.IsOdd`, i.e. `Odd (c(T, C))`), the commutator of the
hole operators flips sign: `[h_{C ⊕ T}, h_{C' ⊕ T}] = -[h_C, h_{C'}]` (v1 L1203-1241). -/
theorem commutator_palindromic_of_isOdd (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {D : G.FPDeformation s s'}
    (hD : D.Palindromic) (hodd : D.IsOdd) :
    algebraCommutator (H.evenHoleOperator (symmDiff ↑(s.1 ∪ s.2) ↑D.toggle))
        (H.evenHoleOperator (symmDiff ↑(s'.1 ∪ s'.2) ↑D.toggle)) =
      -algebraCommutator (H.evenHoleOperator ↑(s.1 ∪ s.2))
        (H.evenHoleOperator ↑(s'.1 ∪ s'.2)) := by
  rw [H.commutator_palindromic hs hs' hD, hodd.neg_one_pow, neg_one_mul]

/-- The cancellation of v1 L1203-1241: for an odd palindromic deformation the two commutator terms
`[h_C, h_{C'}]` and `[h_{C ⊕ T}, h_{C' ⊕ T}]` of the end carriers sum to zero. -/
theorem commutator_palindromic_add_eq_zero_of_isOdd (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {D : G.FPDeformation s s'}
    (hD : D.Palindromic) (hodd : D.IsOdd) :
    algebraCommutator (H.evenHoleOperator ↑(s.1 ∪ s.2)) (H.evenHoleOperator ↑(s'.1 ∪ s'.2)) +
      algebraCommutator (H.evenHoleOperator (symmDiff ↑(s.1 ∪ s.2) ↑D.toggle))
        (H.evenHoleOperator (symmDiff ↑(s'.1 ∪ s'.2) ↑D.toggle)) = 0 := by
  rw [H.commutator_palindromic_of_isOdd hs hs' hD hodd, add_neg_cancel]

/-- When `c(T, C)` is even, the commutators of the end carriers agree, so there is no
cancellation: `[h_{C ⊕ T}, h_{C' ⊕ T}] = [h_C, h_{C'}]`. -/
theorem commutator_palindromic_of_even (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {D : G.FPDeformation s s'}
    (hD : D.Palindromic) (heven : Even (G.crossCount D.toggle (s.1 ∪ s.2))) :
    algebraCommutator (H.evenHoleOperator (symmDiff ↑(s.1 ∪ s.2) ↑D.toggle))
        (H.evenHoleOperator (symmDiff ↑(s'.1 ∪ s'.2) ↑D.toggle)) =
      algebraCommutator (H.evenHoleOperator ↑(s.1 ∪ s.2))
        (H.evenHoleOperator ↑(s'.1 ∪ s'.2)) := by
  rw [H.commutator_palindromic hs hs' hD, heven.neg_one_pow, one_mul]

end PauliFrustrationRepresentation

end SimpleGraph
