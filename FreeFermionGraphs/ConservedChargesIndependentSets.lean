import FreeFermionGraphs.Lemma17Paper
import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.SymmDiffComponentToggle
import FreeFermionGraphs.ChargePairInvolution

/-!
# Theorem 1(i), unrefined: the independent-set charges `Q_{G\W}^(s)` commute

This module proves the unrefined form of part (i) of the Conserved Charges theorem of
the manuscript (arXiv 2305.15625 v1, `theorem:conservedcharges` (i), L864-873, proof
L880-902), for the independent-set charges of Definition 4 (`definition:independentsetcharges`,
L516-522) with an arbitrary deleted carrier `W`:

`[Q_{G\W}^(s), Q_{G\W}^(t)] = 0`  for all `s, t`.

* `PauliFrustrationRepresentation.deletedCharge_commute`: for a Hamiltonian
  representation `H` of a claw-free (finite) frustration graph `G` and any `W ⊆ V`,
  `Q_{G\W}^(s)` and `Q_{G\W}^(t)` commute.  There is no premise beyond the setup of the
  manuscript (the representation `H`, finiteness of `V`) and claw-freeness of `G`; the
  ring `A` is arbitrary.  The deleted charge `Q_{G\W}^(k)` is the repo's
  `PauliFrustrationRepresentation.deletedCharge`, the sum of `h_S` over the
  `k`-element independent sets `S` of `G` that avoid `W` (these are the independent sets
  of the induced subgraph `G \ W`, which is claw-free whenever `G` is).
* `PauliFrustrationRepresentation.charge_commute_charge` (`W = ∅`): `[Q_G^(s), Q_G^(t)] = 0`.
* `PauliFrustrationRepresentation.hamiltonian_commute_charge`: `H = Q_G^(1)` (v1 L522)
  commutes with every `Q_G^(t)`.

This is the sum over all token-sliding components `μ, ν` of the refined statement
`PauliFrustrationRepresentation.paperTheorem1i` (`FreeFermionGraphs.TheoremOneI`), but for
the deleted carrier `W`; the deleted charges are not sums of the token-sliding charges
of `G`, so the proof is redone for the pair-sum over independent sets avoiding `W`
rather than deduced from the refined statement.  The transfer-operator corollaries
(`T_{G\W}(u)` and `T_{G\W}(v)` commute, `Z_{G\W}(-u²) = T(u)T(-u)`) are not stated here:
the repo has no `transfer` operator yet, and they follow from `deletedCharge_commute` by
bilinearity once it is defined.

## The proof

v1 expands `[Q_s, Q_t] = Σ_{S, S'} [h_S, h_{S'}]` and pairs the term `(S, S')` with
`(S ⊕ P, S' ⊕ P)` for a fixed odd component `P` of `G[S ⊕ S']`.  Here the sum runs over
`S ∈ 𝒮_{G\W}^(s)`, `S' ∈ 𝒮_{G\W}^(t)` and the pairing is the involution

`g(S, S') = (S ⊕ Q, S' ⊕ Q)`, `Q = chosenOddComponent S S'`, if `𝒬(S, S') ≠ ∅`,
`g(S, S') = (S, S')` otherwise,

applied with `Finset.sum_involution`.  The new ingredient over the refined statement is
that `g` preserves the carrier of the deleted graph: a component `Q` of `G[S ⊕ S']` is
contained in `S ∪ S'`, so `S ⊕ Q ⊆ S ∪ S'` avoids `W` when `S` and `S'` do
(`symmDiff_mem_independentFinsetsOfCardAvoid`); the cardinality and independence are
preserved by `card_and_tokenSlideReachable_symmDiff` and
`isIndepSet_symmDiff_of_isInducedComponent`.  The cancellation of the paired terms is
`independentProduct_toggle_commutator_add_eq_zero`, and the terms with `𝒬(S, S') = ∅`
vanish since `c(S, S')` is then even.
-/

open scoped symmDiff BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Toggling an odd component preserves the independent sets avoiding `W` -/

/-- Toggling an odd component `Q ∈ 𝒬(S, T)` of `G[S ⊕ T]` in a `k`-element independent set
`S` avoiding `W` gives again a `k`-element independent set avoiding `W` (v1 L897: `S~ = S ⊕ P`
is an independent set of the same size, and `S ⊕ P ⊆ S ∪ S'` stays inside the carrier of
`G \ W`). -/
theorem symmDiff_mem_independentFinsetsOfCardAvoid [Fintype V] [DecidableEq V]
    (hclaw : G.IsClawFree) {W : Set V} {k l : ℕ} {S T Q : Finset V}
    (hS : S ∈ G.independentFinsetsOfCardAvoid W k)
    (hT : T ∈ G.independentFinsetsOfCardAvoid W l)
    (hQ : Q ∈ G.oddCrossComponents S T) :
    symmDiff S Q ∈ G.independentFinsetsOfCardAvoid W k := by
  rw [mem_independentFinsetsOfCardAvoid] at hS hT ⊢
  obtain ⟨hQc, hodd⟩ := mem_oddCrossComponents.mp hQ
  refine ⟨((card_and_tokenSlideReachable_symmDiff hclaw hS.2.1 hT.2.1 hQc hodd).1).trans hS.1,
    isIndepSet_symmDiff_of_isInducedComponent hS.2.1 hT.2.1 hQc, ?_⟩
  intro v hv
  rcases Finset.mem_symmDiff.mp hv with ⟨hvS, -⟩ | ⟨hvQ, -⟩
  · exact hS.2.2 v hvS
  · rcases mem_left_xor_right_of_isInducedComponent hQc hvQ with h | h
    · exact hS.2.2 v h.1
    · exact hT.2.2 v h.1

/-! ### The pairing involution on pairs of finite vertex sets -/

/-- The pairing of v1 L895-902 on pairs of vertex sets: if `𝒬(S, S')` is nonempty, toggle the
fixed odd component `Q = chosenOddComponent S S'` in both arguments; otherwise do nothing.
Unlike `chargePairToggle` it is defined on pairs of `Finset`s, so that it can be restricted to
the independent sets avoiding a deleted carrier. -/
noncomputable def finsetPairToggle [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (p : Finset V × Finset V) : Finset V × Finset V :=
  if (G.oddCrossComponents p.1 p.2).Nonempty then
    (symmDiff p.1 (G.chosenOddComponent p.1 p.2), symmDiff p.2 (G.chosenOddComponent p.1 p.2))
  else p

/-- On a pair with `𝒬(S, S')` nonempty, `finsetPairToggle` toggles the chosen odd component in
both arguments. -/
theorem finsetPairToggle_of_nonempty [Fintype V] [DecidableEq V] {p : Finset V × Finset V}
    (h : (G.oddCrossComponents p.1 p.2).Nonempty) :
    G.finsetPairToggle p =
      (symmDiff p.1 (G.chosenOddComponent p.1 p.2),
        symmDiff p.2 (G.chosenOddComponent p.1 p.2)) := by
  unfold finsetPairToggle
  rw [if_pos h]

/-- On a pair with `𝒬(S, S')` empty, `finsetPairToggle` is the identity. -/
theorem finsetPairToggle_of_not_nonempty [Fintype V] [DecidableEq V] {p : Finset V × Finset V}
    (h : ¬ (G.oddCrossComponents p.1 p.2).Nonempty) :
    G.finsetPairToggle p = p := by
  unfold finsetPairToggle
  rw [if_neg h]

/-- `finsetPairToggle` is an involution: the toggled pair has the same set of odd components
(`oddCrossComponents_symmDiff`), hence the same chosen component, and `Q ⊕ Q = ∅`. -/
theorem finsetPairToggle_involutive [Fintype V] [DecidableEq V] (p : Finset V × Finset V) :
    G.finsetPairToggle (G.finsetPairToggle p) = p := by
  by_cases h : (G.oddCrossComponents p.1 p.2).Nonempty
  · have hQ : G.chosenOddComponent p.1 p.2 ∈ G.oddCrossComponents p.1 p.2 :=
      chosenOddComponent_mem h
    have h1 := finsetPairToggle_of_nonempty (G := G) h
    set Q := G.chosenOddComponent p.1 p.2 with hQdef
    have hodd : G.oddCrossComponents (G.finsetPairToggle p).1 (G.finsetPairToggle p).2 =
        G.oddCrossComponents p.1 p.2 := by
      rw [h1]
      exact oddCrossComponents_symmDiff hQ
    have hne : (G.oddCrossComponents (G.finsetPairToggle p).1 (G.finsetPairToggle p).2).Nonempty := by
      rw [hodd]
      exact h
    have hchosen : G.chosenOddComponent (G.finsetPairToggle p).1 (G.finsetPairToggle p).2 = Q := by
      rw [h1]
      exact chosenOddComponent_symmDiff hQ
    rw [finsetPairToggle_of_nonempty hne, hchosen]
    refine Prod.ext ?_ ?_
    · simp only [h1]
      exact symmDiff_symmDiff_cancel_right _ _
    · simp only [h1]
      exact symmDiff_symmDiff_cancel_right _ _
  · rw [finsetPairToggle_of_not_nonempty h, finsetPairToggle_of_not_nonempty h]

/-- If `𝒬(S, S')` is nonempty then `finsetPairToggle` moves the pair: `Q` is a component of
`G[S ⊕ S']`, hence nonempty, and `S ⊕ Q = S` would force `Q = ∅`. -/
theorem finsetPairToggle_ne_of_nonempty [Fintype V] [DecidableEq V] {p : Finset V × Finset V}
    (h : (G.oddCrossComponents p.1 p.2).Nonempty) :
    G.finsetPairToggle p ≠ p := by
  intro heq
  have h1 := finsetPairToggle_of_nonempty (G := G) h
  have hQ := chosenOddComponent_mem h
  obtain ⟨hQc, -⟩ := mem_oddCrossComponents.mp hQ
  have hne : (G.chosenOddComponent p.1 p.2).Nonempty := by
    obtain ⟨x⟩ := hQc.2.1.nonempty
    exact ⟨x.1, Finset.mem_coe.mp x.2⟩
  have hfix : symmDiff p.1 (G.chosenOddComponent p.1 p.2) = p.1 := by
    have := congrArg Prod.fst (h1.symm.trans heq)
    exact this
  rw [symmDiff_eq_left] at hfix
  exact hne.ne_empty hfix

/-- `finsetPairToggle` maps pairs of `s`-element and `t`-element independent sets avoiding `W`
to such pairs. -/
theorem finsetPairToggle_mem_product [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {W : Set V} {s t : ℕ} {p : Finset V × Finset V}
    (hp : p ∈ G.independentFinsetsOfCardAvoid W s ×ˢ G.independentFinsetsOfCardAvoid W t) :
    G.finsetPairToggle p ∈
      G.independentFinsetsOfCardAvoid W s ×ˢ G.independentFinsetsOfCardAvoid W t := by
  rw [Finset.mem_product] at hp ⊢
  by_cases h : (G.oddCrossComponents p.1 p.2).Nonempty
  · have hQ := chosenOddComponent_mem h
    have hQ' : G.chosenOddComponent p.1 p.2 ∈ G.oddCrossComponents p.2 p.1 := by
      rw [oddCrossComponents_comm]
      exact hQ
    rw [finsetPairToggle_of_nonempty h]
    exact ⟨symmDiff_mem_independentFinsetsOfCardAvoid hclaw hp.1 hp.2 hQ,
      symmDiff_mem_independentFinsetsOfCardAvoid hclaw hp.2 hp.1 hQ'⟩
  · rw [finsetPairToggle_of_not_nonempty h]
    exact hp

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-! ### The commutator of two deleted charges as a sum over pairs -/

/-- Expansion of the commutator of two deleted charges as a sum over pairs of independent
sets avoiding `W` (v1 L882, `equation:conservedchargescommutator`, for `G \ W`). -/
theorem commutator_deletedCharge_eq_sum [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (W : Set V) (s t : ℕ) :
    H.deletedCharge W s * H.deletedCharge W t - H.deletedCharge W t * H.deletedCharge W s =
      ∑ p ∈ G.independentFinsetsOfCardAvoid W s ×ˢ G.independentFinsetsOfCardAvoid W t,
        (H.independentProduct p.1 * H.independentProduct p.2 -
          H.independentProduct p.2 * H.independentProduct p.1) := by
  classical
  have e : ∀ k, H.deletedCharge W k =
      ∑ S ∈ G.independentFinsetsOfCardAvoid W k, H.independentProduct S := fun k => rfl
  rw [e, e, Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (s := G.independentFinsetsOfCardAvoid W t),
    ← Finset.sum_sub_distrib, Finset.sum_product]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_sub_distrib]

/-! ### Theorem 1(i) for `G \ W` -/

/-- **Theorem 1(i), unrefined, with a deleted carrier** (v1 `theorem:conservedcharges` (i),
L864-873, proof L880-902, summed over all token-sliding components).

For a Hamiltonian with claw-free (finite) frustration graph `G`, represented by
`H : G.PauliFrustrationRepresentation A`, and any deleted carrier `W`, the charges
`Q_{G\W}^(s)` and `Q_{G\W}^(t)` commute: `[Q_{G\W}^(s), Q_{G\W}^(t)] = 0`.

There is no premise beyond the representation `H`, the finiteness of `V` and the
claw-freeness of `G` (induced subgraphs of claw-free graphs are claw-free, and
`G \ W` is realised as the independent sets of `G` avoiding `W`); the ring `A` is
arbitrary.

The proof is v1's: expand `[Q_s, Q_t] = Σ_{S, S'} [h_S, h_{S'}]` and pair the term `(S, S')`
with `(S ⊕ Q, S' ⊕ Q)` for the chosen odd component `Q` of `G[S ⊕ S']`
(`finsetPairToggle`); the two terms cancel. -/
theorem deletedCharge_commute [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree)
    (W : Set V) (s t : ℕ) :
    Commute (H.deletedCharge W s) (H.deletedCharge W t) := by
  classical
  rw [Commute, SemiconjBy, ← sub_eq_zero, H.commutator_deletedCharge_eq_sum]
  refine Finset.sum_involution (fun p _ => G.finsetPairToggle p) ?_ ?_ ?_ ?_
  · -- the terms of `p` and its partner cancel
    intro p hp
    rw [Finset.mem_product] at hp
    by_cases h : (G.oddCrossComponents p.1 p.2).Nonempty
    · rw [finsetPairToggle_of_nonempty h]
      exact H.independentProduct_toggle_commutator_add_eq_zero
        (mem_independentFinsetsOfCardAvoid.mp hp.1).2.1
        (mem_independentFinsetsOfCardAvoid.mp hp.2).2.1 (chosenOddComponent_mem h)
    · rw [finsetPairToggle_of_not_nonempty h]
      have hz : H.independentProduct p.1 * H.independentProduct p.2 -
          H.independentProduct p.2 * H.independentProduct p.1 = 0 := by
        have heven : Even (G.crossCount p.1 p.2) := by
          by_contra hodd
          exact h (oddCrossComponents_nonempty_of_odd
            (mem_independentFinsetsOfCardAvoid.mp hp.1).2.1
            (mem_independentFinsetsOfCardAvoid.mp hp.2).2.1 (Nat.not_even_iff_odd.mp hodd))
        rw [sub_eq_zero]
        exact H.independentProduct_mul_independentProduct_of_even
          (mem_independentFinsetsOfCardAvoid.mp hp.1).2.1
          (mem_independentFinsetsOfCardAvoid.mp hp.2).2.1 heven
      rw [hz]
      simp
  · -- no fixed points among the nonzero terms
    intro p hp hne
    rw [Finset.mem_product] at hp
    by_cases h : (G.oddCrossComponents p.1 p.2).Nonempty
    · exact finsetPairToggle_ne_of_nonempty h
    · exfalso
      apply hne
      have heven : Even (G.crossCount p.1 p.2) := by
        by_contra hodd
        exact h (oddCrossComponents_nonempty_of_odd
          (mem_independentFinsetsOfCardAvoid.mp hp.1).2.1
          (mem_independentFinsetsOfCardAvoid.mp hp.2).2.1 (Nat.not_even_iff_odd.mp hodd))
      rw [sub_eq_zero]
      exact H.independentProduct_mul_independentProduct_of_even
        (mem_independentFinsetsOfCardAvoid.mp hp.1).2.1
        (mem_independentFinsetsOfCardAvoid.mp hp.2).2.1 heven
  · intro p hp
    exact finsetPairToggle_mem_product hclaw hp
  · intro p _
    exact finsetPairToggle_involutive p

/-- **Theorem 1(i), unrefined, no deletion** (`W = ∅`): `[Q_G^(s), Q_G^(t)] = 0`. -/
theorem charge_commute_charge [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) (s t : ℕ) :
    Commute (H.charge s) (H.charge t) :=
  H.deletedCharge_commute hclaw ∅ s t

/-- **Conservation of `H` by the charges** (`W = ∅`): `[H, Q_G^(t)] = 0`, from
`Q_G^(1) = H` (v1 L522, `operatorIndependentSetChargeFull_one`) and `charge_commute_charge`. -/
theorem hamiltonian_commute_charge [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) (t : ℕ) :
    Commute H.hamiltonian (H.charge t) := by
  have h1 : H.charge 1 = H.hamiltonian := H.operatorIndependentSetChargeFull_one
  rw [← h1]
  exact H.charge_commute_charge hclaw 1 t

end PauliFrustrationRepresentation

end SimpleGraph
