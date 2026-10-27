import FreeFermionGraphs.T3PalindromicToggles
import FreeFermionGraphs.T3ToggleStable
import FreeFermionGraphs.T3PairingIndexInvariance
import FreeFermionGraphs.T3FixedPairingSymm

/-!
# Invariance of `K*(C, C')` under its own toggles

For a claw-free graph `G` and `T ∈ K*(C, C')` (`SimpleGraph.palindromicToggles`, the set of toggles
of odd palindromic fixed-pairing-type deformations of hole-class states with carriers `C`, `C'` and
negative pairing index), the set of toggles at the toggled pair of carriers is the same set:
`K*(C ⊕ T, C' ⊕ T) = K*(C, C')`
(`SimpleGraph.palindromicToggles_toggle`).  This is the (iii) analogue of
`SimpleGraph.untetheredSupports_toggle` (the stability of the set `𝒫(C, S)` of the proof of
Theorem 1(ii)).

## Relation to v1

The proof of Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, L1203-1241) cancels the terms
`[h_C, h_{C'}]` and `[h_{C ⊕ T}, h_{C' ⊕ T}]` against each other "by fixing a deformation to cancel
terms pairwise" (L1237-1241).  For this to be a pairing of the terms, the fixed deformation chosen
for `(C, C')` has to be chosen again for `(C ⊕ T, C' ⊕ T)`, i.e. the pairing
`(C, C') ↦ (C ⊕ T, C' ⊕ T)` must be an involution on the pairs of carriers.  v1 does not argue this.
It holds because the candidate set `K*(C, C')` depends on the carriers alone and is invariant under
the toggles it contains; this module proves the invariance.

## Main results

* `SimpleGraph.palindromicToggles_toggle_of_mem`: if `T, T' ∈ K*(C, C')`, then
  `T' ∈ K*(C ⊕ T, C' ⊕ T)`.
* `SimpleGraph.palindromicToggles_toggle`: if `T ∈ K*(C, C')`, then
  `K*(C ⊕ T, C' ⊕ T) = K*(C, C')`.

## Proof

Let `T, T' ∈ K*(C, C')` with witnessing deformations `D : G.FPDeformation s s'` (toggle `T`) and
`D' : G.FPDeformation t t'` (toggle `T'`).  The class pairs have the same carriers, so
`t ∈ {s, s.swap}` and `t' ∈ {s', s'.swap}` (`IsHoleClasses.eq_or_eq_swap`).  The mixed cases
`(t, t') = (s, s'.swap)` and `(s.swap, s')` are excluded by the sign: the pairing index changes
sign under a single swap (`pairingIndex_swap_right`, `pairingIndex_swap_left`), while both
`Ψ(s, s')` and `Ψ(t, t')` are negative.  In the cases `(s, s')` and `(s.swap, s'.swap)` the
deformation `D'` (resp. its side-swap `D'.swapSides`) is a palindromic odd deformation of `(s, s')`
with the toggle `T'`.  Toggle stability (`FPDeformation.toggle_stable`) then transports it to a
palindromic deformation `D''` of the end states `(D.fwdEnd, D.bwdEnd)` with the same toggle and
parity.  The end states are hole-class states with carriers `C ⊕ T`, `C' ⊕ T`
(`FPDeformation.carrier_fwdEnd`, `carrier_bwdEnd`) and the same pairing index
(`FPDeformation.pairingIndex_ends`), so `T' ∈ K*(C ⊕ T, C' ⊕ T)`.

For the equality, `T ∈ K*(C ⊕ T, C' ⊕ T)` (apply the first result with `T' = T`), the inclusion
`K*(C, C') ⊆ K*(C ⊕ T, C' ⊕ T)` is the first result, and the reverse inclusion is the first result
applied to the toggled pair `(C ⊕ T, C' ⊕ T)` (at which `T` is again an element), followed by
`(C ⊕ T) ⊕ T = C`.

## Notes

* The hypothesis `G.IsClawFree` is part of the manuscript setup of Theorem 1 and is carried so that
  the statements have the same shape as `untetheredSupports_toggle_of_mem`.  The proofs do not use
  it (`toggle_stable` does not either).
* The witnessing deformations of two elements of `K*(C, C')` need not have the same pairing type:
  the sign condition `Ψ < 0` fixes the class pair up to a simultaneous swap, and the side swap
  `FPDeformation.swapSides` removes the remaining freedom.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

section Invariant

variable [Fintype V] [DecidableEq V]

/-- **Transport to a fixed pair of class states.**  Let `s, s'` and `t, t'` be hole-class states
with the same carriers and negative pairing indices.  Every palindromic deformation `D'` of
`(t, t')` is, up to exchanging the two sides, a palindromic deformation `E` of `(s, s')` with the
same toggle and the same parity.

By `IsHoleClasses.eq_or_eq_swap`, `t ∈ {s, s.swap}` and `t' ∈ {s', s'.swap}`; the two mixed cases
contradict the signs of the pairing indices (`pairingIndex_swap_right`, `pairingIndex_swap_left`),
and the case `(s.swap, s'.swap)` is handled by `FPDeformation.swapSides`. -/
theorem exists_fpDeformation_of_carriers_eq {s s' t t' : Finset V × Finset V}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (ht : G.IsHoleClasses t)
    (ht' : G.IsHoleClasses t') (hc : s.1 ∪ s.2 = t.1 ∪ t.2) (hc' : s'.1 ∪ s'.2 = t'.1 ∪ t'.2)
    (hΨ : G.pairingIndex s s' < 0) (hΨ' : G.pairingIndex t t' < 0)
    (D' : G.FPDeformation t t') (hD' : D'.Palindromic) :
    ∃ E : G.FPDeformation s s', E.Palindromic ∧ E.toggle = D'.toggle ∧ (E.IsOdd ↔ D'.IsOdd) := by
  rcases hs.eq_or_eq_swap ht hc with h | h <;>
    rcases hs'.eq_or_eq_swap ht' hc' with h' | h'
  · subst h h'
    exact ⟨D', hD', rfl, Iff.rfl⟩
  · subst h h'
    rw [pairingIndex_swap_right hs'.disjoint] at hΨ'
    omega
  · subst h h'
    rw [pairingIndex_swap_left hs.disjoint] at hΨ'
    omega
  · have e : s = t.swap := by rw [h, Prod.swap_swap]
    have e' : s' = t'.swap := by rw [h', Prod.swap_swap]
    subst e e'
    exact ⟨D'.swapSides, (FPDeformation.palindromic_swapSides_iff D').2 hD',
      FPDeformation.toggle_swapSides D', FPDeformation.isOdd_swapSides_iff D'⟩

/-- **Stability, the elements of `K*(C, C')` survive the toggle.**  If `T, T' ∈ K*(C, C')`, then
`T' ∈ K*(C ⊕ T, C' ⊕ T)` (v1 L1237-1241: the final pairing; see the module documentation).  For
`T' = T` this is the reverse deformation (`FPDeformation.exists_palindromic_toggle_at_ends`); in
general it is toggle stability (`FPDeformation.toggle_stable`) after transport of the witnessing
deformation of `T'` to the class pair of the witness of `T`
(`exists_fpDeformation_of_carriers_eq`).  The hypothesis `hclaw` is part of the manuscript setup of
Theorem 1 and is not used. -/
theorem palindromicToggles_toggle_of_mem (hclaw : G.IsClawFree) {C C' : Set V}
    {T T' : Finset V} (hT : T ∈ G.palindromicToggles C C')
    (hT' : T' ∈ G.palindromicToggles C C') :
    T' ∈ G.palindromicToggles (symmDiff C ↑T) (symmDiff C' ↑T) := by
  obtain ⟨s, s', hs, hs', rfl, rfl, hΨ, D, hD, -, rfl⟩ := mem_palindromicToggles.1 hT
  obtain ⟨t, t', ht, ht', hc, hc', hΨ', D', hD', hodd', rfl⟩ := mem_palindromicToggles.1 hT'
  obtain ⟨E, hE, htog, hpar⟩ := exists_fpDeformation_of_carriers_eq hs hs' ht ht'
    (Finset.coe_inj.1 hc.symm) (Finset.coe_inj.1 hc'.symm) hΨ hΨ' D' hD'
  obtain ⟨D'', hD'', htog'', hpar''⟩ := FPDeformation.toggle_stable hclaw hs hs' D E hD hE
  obtain ⟨hfe, hbe⟩ := FPDeformation.Palindromic.isHoleClasses_ends hs hs' hD
  refine mem_palindromicToggles.2 ⟨D.fwdEnd, D.bwdEnd, hfe, hbe, ?_, ?_, ?_, D'', hD'',
    hpar''.2 (hpar.2 hodd'), htog''.trans htog⟩
  · rw [FPDeformation.carrier_fwdEnd hs hs' D hD, Finset.coe_symmDiff]
  · rw [FPDeformation.carrier_bwdEnd hs hs' D hD, Finset.coe_symmDiff]
  · rw [FPDeformation.pairingIndex_ends hs hs' D hD]
    exact hΨ

/-- **Invariance of `K*(C, C')` under its own toggles** (the repair of the gap of v1 L1237-1241:
the pairing `(C, C') ↦ (C ⊕ T, C' ⊕ T)` must be an involution on the pairs of carriers).  For
`G` claw-free and `T ∈ K*(C, C')`,
`K*(C ⊕ T, C' ⊕ T) = K*(C, C')`.

The proof shows `⊆` by `palindromicToggles_toggle_of_mem` and `⊇` by applying it to the toggled
pair, using `T ∈ K*(C ⊕ T, C' ⊕ T)` (the reverse deformation) and `(C ⊕ T) ⊕ T = C`.  The statement
is the analogue of `untetheredSupports_toggle_of_mem`.  The hypothesis `hclaw` is part of the
manuscript setup of Theorem 1 and is not used. -/
theorem palindromicToggles_toggle (hclaw : G.IsClawFree) {C C' : Set V} {T : Finset V}
    (hT : T ∈ G.palindromicToggles C C') :
    G.palindromicToggles (symmDiff C ↑T) (symmDiff C' ↑T) = G.palindromicToggles C C' := by
  have hT₁ : T ∈ G.palindromicToggles (symmDiff C ↑T) (symmDiff C' ↑T) :=
    palindromicToggles_toggle_of_mem hclaw hT hT
  refine Finset.Subset.antisymm (fun T' hT'' => ?_) (fun T' hT'' =>
    palindromicToggles_toggle_of_mem hclaw hT hT'')
  have := palindromicToggles_toggle_of_mem hclaw hT₁ hT''
  rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this

end Invariant

end SimpleGraph
