import FreeFermionGraphs.TheoremOneIIIExpansion
import FreeFermionGraphs.T3FrameSign
import FreeFermionGraphs.T3PalindromicToggles
import FreeFermionGraphs.T3PairingInvolution
import FreeFermionGraphs.T3Existence
import FreeFermionGraphs.CycleSymmetrySectors

/-!
# Theorem 1 (iii): `[J_{C₀}, J_{C₀'}] = 0`

This module proves part (iii) of the Conserved Charges theorem of the manuscript (arXiv 2305.15625
v1, `theorem:conservedcharges` (iii), L864-871, proof L929-1243): the generalized cycle symmetries
`J_{C₀} = Σ_{C ∈ ⟨C₀⟩} h_C` (Definition 15, v1 L799) of a claw-free Hamiltonian commute with each
other.

* `PauliFrustrationRepresentation.paperTheorem1iii`: for a Hamiltonian representation `H` of a
  claw-free (finite) frustration graph `G` and even holes `C₀`, `C₀'`,
  `[J_{C₀}, J_{C₀'}] = 0`.  The only hypotheses are the setup of the manuscript (the
  representation `H`, finiteness of `V`), claw-freeness, and `C₀`, `C₀'` being even holes (v1
  defines `J_{C₀}` only for even holes).  The ring `A` is arbitrary, so the statement is more
  general than v1's (Pauli strings, and scaled terms `h_j² = b_j²`), and no invertibility of `2`
  is used: the cancellation is a pairing of terms, not a division.
* `PauliFrustrationRepresentation.cycleSymmetriesCommute`: the same, in the form
  `H.CycleSymmetriesCommute` (the hypothesis of the sector theory in
  `FreeFermionGraphs.CycleSymmetrySectors`, which had to take it as a premise before).
* `PauliFrustrationRepresentation.commutator_evenHoleOperator_eq_zero_of_palindromicToggles_eq_empty`:
  the vanishing of `[h_C, h_{C'}]` when `K*(C, C')` (`SimpleGraph.palindromicToggles`) is empty.

## The proof

The proof is that of `paperTheorem1ii` (`FreeFermionGraphs.TheoremOneII`), with the pairs of
deformation-closure members in place of the pairs `(C, S)`.

v1 expands `[J_{C₀}, J_{C₀'}] = Σ_{C ∈ ⟨C₀⟩, C' ∈ ⟨C₀'⟩} [h_C, h_{C'}]` (L934-936,
`commutator_generalizedCycleSymmetryOp_pair_eq_sum`) and, if `h_C` and `h_{C'}` anticommute, pairs
the term `(C, C')` with `(C ⊕ T, C' ⊕ T)` for a palindromic deformation of odd sign, which
cancels it (L1203-1241).  Here the pairing is the function `holePairToggle` of
`FreeFermionGraphs.T3PairingInvolution`: it toggles the chosen element `T` of the candidate set
`K*(C, C')` when this set is nonempty and is the identity otherwise.  Then `Finset.sum_involution`
finishes the proof:

* *Cancellation.*  If `K*(C, C')` is nonempty, the partner term is `-[h_C, h_{C'}]`
  (`commutator_holePairToggle`, i.e. `commutator_palindromicToggle`).  If `K*(C, C')` is empty, the
  pairing is the identity and the term itself vanishes.  Indeed the crossing number `c(C, C')`
  (the number of edges between `C` and `C'`) is then even, since an odd `c(C, C')` forces
  `K*(C, C') ≠ ∅` (`palindromicToggles_nonempty`, applied to hole-class states with carriers `C`
  and `C'`, `exists_isHoleClasses`), and `h_C h_{C'} = (-1)^{c(C, C')} h_{C'} h_C`
  (`evenHoleOperator_mul_evenHoleOperator_holeClasses`) is symmetric.
* *No fixed point among the nonzero terms.*  A nonzero term has `K*(C, C')` nonempty (otherwise it
  vanishes), and then `holePairToggle` moves the pair (`holePairToggle_ne`).
* *Closure.*  `holePairToggle` preserves `⟨C₀⟩ × ⟨C₀'⟩` (`holePairToggle_mem_closure`).
* *Involution.*  `holePairToggle_involutive`.

## Deviations from v1

1. *Existence of the cancelling deformation.*  v1 obtains an odd palindromic deformation from an
   obstruction search (L1170-1198; v1 Lemmas 8-10, repo Lemmas 14-16).  Here existence is
   `palindromicToggles_nonempty` (`FreeFermionGraphs.T3Existence`, proved by the source-block
   induction of the packages T3-19 to T3-25: good candidate, update of the pairing index,
   separator lemma, lift lemma).  The v1 Lemmas 8-10 (repo 14-16) are not used.
2. *The partner is an involution.*  v1 pairs each term with "a fixed deformation" (L1237-1241) and
   leaves unargued that the assignment is an involution without fixed points on the nonzero
   terms.  Here the partner is chosen from the set `K*(C, C')`, which depends on the pair of
   carriers only and is stable under the toggles it contains (`palindromicToggles_toggle`), so the
   toggled pair has the same `K*` and the same chosen element
   (`holePairToggle_involutive`).
3. *The sign.*  The sign of the cancellation is `c(T, C)` for the toggle `T` (the number of edges
   between `T` and `C`, `FPDeformation.IsOdd`), odd by the choice of `T ∈ K*(C, C')`; v1's
   criterion "`|W ∩ ∂O|` is odd" (L1226-1227) is never needed.

Moreover no relation `h_j² = b_j²` is used (v1 assumes scaled terms), and the ring is arbitrary.
-/

open scoped symmDiff BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A] [Fintype V] [DecidableEq V]

/-- **The terms with `K*(C, C') = ∅` vanish.**  If `C`, `C'` are even-hole carriers and no odd
palindromic deformation of hole classes of `C` and `C'` exists (`K*(C, C')` is empty), then
`[h_C, h_{C'}] = 0`.

Choose hole-class states `s`, `s'` with carriers `C`, `C'` (`exists_isHoleClasses`).  The crossing
number `c(C, C')` is even, for otherwise `K*(C, C')` would be nonempty
(`palindromicToggles_nonempty`), and `h_C h_{C'} = (-1)^{c(C, C')} h_{C'} h_C`
(`evenHoleOperator_mul_evenHoleOperator_holeClasses`).  This is the (iii) analogue of
`commutator_evenHoleOperator_eq_zero_of_untetheredSupports_eq_empty` (Theorem 1 (ii)). -/
theorem commutator_evenHoleOperator_eq_zero_of_palindromicToggles_eq_empty
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {C C' : Set V}
    (hC : G.IsEvenHoleCarrier C) (hC' : G.IsEvenHoleCarrier C')
    (h : ¬ (G.palindromicToggles C C').Nonempty) :
    algebraCommutator (H.evenHoleOperator C) (H.evenHoleOperator C') = 0 := by
  obtain ⟨s, hs, rfl⟩ := exists_isHoleClasses hC
  obtain ⟨s', hs', rfl⟩ := exists_isHoleClasses hC'
  have heven : Even (G.crossCount (s.1 ∪ s.2) (s'.1 ∪ s'.2)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact h (palindromicToggles_nonempty hclaw hs hs' hodd)
  unfold algebraCommutator
  rw [sub_eq_zero, H.evenHoleOperator_mul_evenHoleOperator_holeClasses hs hs',
    heven.neg_one_pow, one_mul]

/-- **Theorem 1 (iii)** (v1 `theorem:conservedcharges` (iii), L864-871, proof L929-1243).

For a Hamiltonian with claw-free (finite) frustration graph `G`, represented by
`H : G.PauliFrustrationRepresentation A`, and even holes `C₀`, `C₀'`, the generalized cycle
symmetries `J_{C₀} = Σ_{C ∈ ⟨C₀⟩} h_C` and `J_{C₀'}` commute: `[J_{C₀}, J_{C₀'}] = 0`.

There is no premise beyond the representation `H`, the finiteness of `V`, claw-freeness of `G`, and
`C₀`, `C₀'` being even holes (v1 defines `J_{C₀}` only for even holes); the ring `A` is arbitrary,
so the statement is more general than v1's (Pauli strings with scaled terms `h_j² = b_j²`).  It has
the same premise set as `paperTheorem1ii`.

The proof is v1's (L934-936, L1203-1241) in the form of `paperTheorem1ii`: expand
`[J_{C₀}, J_{C₀'}] = Σ_{C ∈ ⟨C₀⟩, C' ∈ ⟨C₀'⟩} [h_C, h_{C'}]`
(`commutator_generalizedCycleSymmetryOp_pair_eq_sum`), pair the term `(C, C')` with
`(C ⊕ T, C' ⊕ T)` for the chosen palindromic toggle `T ∈ K*(C, C')` (`holePairToggle`), which
cancels it, and kill the sum with `Finset.sum_involution`.  Pairs with `K*(C, C') = ∅` have
vanishing terms (`commutator_evenHoleOperator_eq_zero_of_palindromicToggles_eq_empty`).

Deviations from v1 (see the module documentation): (1) existence of the odd palindromic toggle is
`palindromicToggles_nonempty` (source-block induction), not v1's obstruction search (L1170-1198;
v1 Lemmas 8-10, repo 14-16, are not used); (2) the partner is chosen from the invariant set
`K*(C, C')`, which makes the pairing an involution (`holePairToggle_involutive`), a point that v1
leaves unargued (L1241); (3) the sign is `c(T, C)` for the toggle `T`, v1's "`|W ∩ ∂O|` odd" is
never needed. -/
theorem paperTheorem1iii
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {C₀ C₀' : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀) (hC₀' : G.IsEvenHoleCarrier C₀') :
    algebraCommutator (H.generalizedCycleSymmetryOp C₀) (H.generalizedCycleSymmetryOp C₀') = 0 := by
  classical
  rw [H.commutator_generalizedCycleSymmetryOp_pair_eq_sum]
  -- a nonzero term has `K*` nonempty
  have hzero : ∀ p ∈ G.deformationClosureFinset C₀ ×ˢ G.deformationClosureFinset C₀',
      ¬ (G.palindromicToggles p.1 p.2).Nonempty →
        algebraCommutator (H.evenHoleOperator p.1) (H.evenHoleOperator p.2) = 0 := by
    intro p hp h
    have hpc : InEvenHoleDeformationClosure G C₀ p.1 :=
      mem_deformationClosureFinset.1 (Finset.mem_product.1 hp).1
    have hpc' : InEvenHoleDeformationClosure G C₀' p.2 :=
      mem_deformationClosureFinset.1 (Finset.mem_product.1 hp).2
    exact H.commutator_evenHoleOperator_eq_zero_of_palindromicToggles_eq_empty hclaw
      (hpc.isEvenHoleCarrier hC₀) (hpc'.isEvenHoleCarrier hC₀') h
  refine Finset.sum_involution (fun p _ => G.holePairToggle p) ?_ ?_ ?_ ?_
  · -- the terms of `p` and its partner cancel
    intro p hp
    by_cases h : (G.palindromicToggles p.1 p.2).Nonempty
    · rw [H.commutator_holePairToggle hclaw h, add_neg_cancel]
    · rw [holePairToggle_of_not_nonempty h, hzero p hp h, add_zero]
  · -- no fixed points among the nonzero terms
    intro p hp hne
    by_cases h : (G.palindromicToggles p.1 p.2).Nonempty
    · exact holePairToggle_ne hclaw h
    · exact (hne (hzero p hp h)).elim
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    obtain ⟨h1, h2⟩ := holePairToggle_mem_closure hclaw (mem_deformationClosureFinset.1 hp1)
      (mem_deformationClosureFinset.1 hp2)
    exact Finset.mem_product.2
      ⟨mem_deformationClosureFinset.2 h1, mem_deformationClosureFinset.2 h2⟩
  · intro p _
    exact holePairToggle_involutive hclaw p

/-- **Theorem 1 (iii) as the hypothesis of the sector theory**: for a Hamiltonian representation of
a claw-free graph, the generalized cycle symmetries `J_{C₀}` of all even holes pairwise commute,
i.e. `H.CycleSymmetriesCommute` (defined in `FreeFermionGraphs.CycleSymmetrySectors`, where it had
to be taken as a premise).  This is `paperTheorem1iii` with `Commute` in place of
`algebraCommutator = 0`. -/
theorem cycleSymmetriesCommute
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) :
    H.CycleSymmetriesCommute := by
  intro C₀ C₀' hC₀ hC₀'
  have h := H.paperTheorem1iii hclaw hC₀ hC₀'
  unfold algebraCommutator at h
  exact sub_eq_zero.1 h

end PauliFrustrationRepresentation

end SimpleGraph
