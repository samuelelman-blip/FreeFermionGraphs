import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.SymmDiffComponentToggle
import FreeFermionGraphs.ChargePairInvolution

/-!
# Theorem 1(i): the token-sliding charges commute pairwise, and `H` is conserved

This module proves part (i) of the Conserved Charges theorem of the manuscript
(arXiv 2305.15625 v1, `theorem:conservedcharges` (i), L864-871, proof L880-902),
together with its last sentence ("in particular, these operators are conserved
charges of the Hamiltonian"), restricted to the charges `q_{t,ν}`: the Hamiltonian
`H = Q^(1) = Σ_{μ ∈ Ξ₁} q_{1,μ}` commutes with every `q_{t,ν}`.

* `PauliFrustrationRepresentation.paperTheorem1i`: for a Hamiltonian representation
  `H` of a claw-free (finite) frustration graph `G`, for all `s, t`, `μ ∈ Ξ_s` and
  `ν ∈ Ξ_t`, `[q_{s,μ}, q_{t,ν}] = 0`.  The only hypotheses are the setup of the
  manuscript (the representation `H`, finiteness of `V`) and claw-freeness; the
  statement holds in any ring `A` carrying the frustration relations, so it is more
  general than v1 (which works with Pauli strings).
* `PauliFrustrationRepresentation.hamiltonian_commute_tokenSlidingChargeOp`:
  `[H, q_{t,ν}] = 0`, from `Q^(1) = H` and `Σ_μ q_{1,μ} = Q^(1)`.

## The proof

v1 expands `[q_{s,μ}, q_{t,ν}] = Σ_{S ∈ μ, S' ∈ ν} [h_S, h_{S'}]` and pairs the terms
indexed by `(S, S')` with `S ⊕ S'` containing a path component `P` of odd length with
`(S ⊕ P, S' ⊕ P)`, for which `[h_S, h_{S'}] + [h_{S ⊕ P}, h_{S' ⊕ P}] = 0`.  Here the
sum runs over all pairs `(S, S')` of token configurations, with the indicator of
`S ∈ μ ∧ S' ∈ ν` in the summand, and the pairing is the involution

`g(S, S') = (S ⊕ Q, S' ⊕ Q)`, `Q = chosenOddComponent S S'`, if `𝒬(S, S') ≠ ∅`,
`g(S, S') = (S, S')` otherwise,

where `𝒬(S, S')` (`SimpleGraph.oddCrossComponents`) is the set of components `Q` of
`G[S ⊕ S']` with `c(S ∩ Q, S' ∩ Q)` odd (the "paths of odd length" of v1 L895).  It is
applied with `Finset.sum_involution`.

* `g` lands in `TokenConfiguration s × TokenConfiguration t`, preserves the
  components of `μ` and `ν`, by `card_and_tokenSlideReachable_symmDiff` and
  `tokenSlidingComponentMk_eq_of_tokenSlideReachable` (v1 L897: "`S ↔_TS S~`").
* `g` is an involution because `𝒬(S ⊕ Q, S' ⊕ Q) = 𝒬(S, S')`
  (`oddCrossComponents_symmDiff`), so the same `Q` is chosen again, and `Q ⊕ Q = ∅`.
* `g` has no fixed point where it is not the identity because `Q` is a component,
  hence nonempty.
* The summands of `(S, S')` and `g (S, S')` cancel by
  `independentProduct_toggle_commutator_add_eq_zero`.
* If `𝒬(S, S') = ∅` then `g` is the identity and the summand vanishes:
  `c(S, S')` would be odd, and `exists_isInducedComponent_odd` produces an element of
  `𝒬(S, S')`; so `h_S h_{S'} = h_{S'} h_S`.

Branching on `𝒬(S, S') ≠ ∅` instead of on `c(S, S')` being odd (as one may do in v1)
avoids having to know that the parity of `c(S ⊕ Q, S' ⊕ Q)` equals that of `c(S, S')`.
-/

open scoped symmDiff BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Toggling an odd component preserves token configurations and their component -/

/-- Toggling an odd component `Q ∈ 𝒬(S, T)` of `G[S ⊕ T]` in the `k`-configuration `S`
gives again a `k`-configuration (v1 L897: `S~ = S ⊕ P` is an independent set reached from
`S` by token slides). -/
theorem isNIndepSet_symmDiff_of_mem_oddCrossComponents [Fintype V] [DecidableEq V]
    (hclaw : G.IsClawFree) {k : ℕ} {S T Q : Finset V}
    (hS : G.IsNIndepSet k S) (hT : G.IsIndepSet (T : Set V))
    (hQ : Q ∈ G.oddCrossComponents S T) : G.IsNIndepSet k (symmDiff S Q) := by
  obtain ⟨hQc, hodd⟩ := mem_oddCrossComponents.mp hQ
  exact ⟨isIndepSet_symmDiff_of_isInducedComponent hS.isIndepSet hT hQc,
    (card_and_tokenSlideReachable_symmDiff hclaw hS.isIndepSet hT hQc hodd).1.trans
      hS.card_eq⟩

/-- Toggling an odd component `Q ∈ 𝒬(S, T)` of `G[S ⊕ T]` keeps the configuration `S`
in its component of the token-sliding solution graph (v1 L897: `S ↔_TS S~`, so `S~ ∈ μ`
if `S ∈ μ`). -/
theorem tokenSlidingComponentMk_eq_of_symmDiff_oddCrossComponents [Fintype V] [DecidableEq V]
    (hclaw : G.IsClawFree) {k : ℕ} (S S' : G.TokenConfiguration k) {T Q : Finset V}
    (hT : G.IsIndepSet (T : Set V)) (hQ : Q ∈ G.oddCrossComponents S.1 T)
    (hS' : S'.1 = symmDiff S.1 Q) :
    G.tokenSlidingComponentMk k S' = G.tokenSlidingComponentMk k S := by
  obtain ⟨hQc, hodd⟩ := mem_oddCrossComponents.mp hQ
  have hreach := (card_and_tokenSlideReachable_symmDiff hclaw S.2.isIndepSet hT hQc hodd).2
  rw [← hS'] at hreach
  exact (tokenSlidingComponentMk_eq_of_tokenSlideReachable hreach).symm

/-! ### The pairing involution on pairs of token configurations -/

/-- The pairing of v1 L895-902 on pairs of token configurations: if `𝒬(S, S')` is
nonempty, toggle the fixed odd component `Q = chosenOddComponent S S'` in both
arguments; otherwise do nothing. -/
noncomputable def chargePairToggle [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    (s t : ℕ) (p : G.TokenConfiguration s × G.TokenConfiguration t) :
    G.TokenConfiguration s × G.TokenConfiguration t :=
  if h : (G.oddCrossComponents p.1.1 p.2.1).Nonempty then
    (⟨symmDiff p.1.1 (G.chosenOddComponent p.1.1 p.2.1),
        isNIndepSet_symmDiff_of_mem_oddCrossComponents hclaw p.1.2 p.2.2.isIndepSet
          (chosenOddComponent_mem h)⟩,
      ⟨symmDiff p.2.1 (G.chosenOddComponent p.1.1 p.2.1),
        isNIndepSet_symmDiff_of_mem_oddCrossComponents hclaw p.2.2 p.1.2.isIndepSet
          ((oddCrossComponents_comm (G := G) p.1.1 p.2.1) ▸ chosenOddComponent_mem h)⟩)
  else p

/-- On a pair with `𝒬(S, S')` nonempty, `chargePairToggle` toggles the chosen odd component
in both arguments. -/
theorem chargePairToggle_of_nonempty [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {s t : ℕ} {p : G.TokenConfiguration s × G.TokenConfiguration t}
    (h : (G.oddCrossComponents p.1.1 p.2.1).Nonempty) :
    ((chargePairToggle hclaw s t p).1.1 =
        symmDiff p.1.1 (G.chosenOddComponent p.1.1 p.2.1)) ∧
      ((chargePairToggle hclaw s t p).2.1 =
        symmDiff p.2.1 (G.chosenOddComponent p.1.1 p.2.1)) := by
  unfold chargePairToggle
  rw [dif_pos h]
  exact ⟨rfl, rfl⟩

/-- On a pair with `𝒬(S, S')` empty, `chargePairToggle` is the identity. -/
theorem chargePairToggle_of_not_nonempty [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {s t : ℕ} {p : G.TokenConfiguration s × G.TokenConfiguration t}
    (h : ¬ (G.oddCrossComponents p.1.1 p.2.1).Nonempty) :
    chargePairToggle hclaw s t p = p := by
  unfold chargePairToggle
  rw [dif_neg h]

/-- `chargePairToggle` is an involution: the toggled pair has the same set of odd
components (`oddCrossComponents_symmDiff`), hence the same chosen component, and
`Q ⊕ Q = ∅`. -/
theorem chargePairToggle_involutive [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    (s t : ℕ) (p : G.TokenConfiguration s × G.TokenConfiguration t) :
    chargePairToggle hclaw s t (chargePairToggle hclaw s t p) = p := by
  by_cases h : (G.oddCrossComponents p.1.1 p.2.1).Nonempty
  · obtain ⟨h1, h2⟩ := chargePairToggle_of_nonempty hclaw h
    have hQ : G.chosenOddComponent p.1.1 p.2.1 ∈ G.oddCrossComponents p.1.1 p.2.1 :=
      chosenOddComponent_mem h
    have hodd : G.oddCrossComponents (chargePairToggle hclaw s t p).1.1
        (chargePairToggle hclaw s t p).2.1 = G.oddCrossComponents p.1.1 p.2.1 := by
      rw [h1, h2]
      exact oddCrossComponents_symmDiff hQ
    have hne : (G.oddCrossComponents (chargePairToggle hclaw s t p).1.1
        (chargePairToggle hclaw s t p).2.1).Nonempty := by
      rw [hodd]
      exact h
    have hchosen : G.chosenOddComponent (chargePairToggle hclaw s t p).1.1
        (chargePairToggle hclaw s t p).2.1 = G.chosenOddComponent p.1.1 p.2.1 := by
      rw [h1, h2]
      exact chosenOddComponent_symmDiff hQ
    obtain ⟨h3, h4⟩ := chargePairToggle_of_nonempty hclaw hne
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [h3, hchosen, h1]
      exact symmDiff_symmDiff_cancel_right _ _
    · rw [h4, hchosen, h2]
      exact symmDiff_symmDiff_cancel_right _ _
  · rw [chargePairToggle_of_not_nonempty hclaw h, chargePairToggle_of_not_nonempty hclaw h]

/-- If `𝒬(S, S')` is nonempty then `chargePairToggle` moves the pair: `Q` is a component
of `G[S ⊕ S']`, hence nonempty, and `S ⊕ Q = S` would force `Q = ∅`. -/
theorem chargePairToggle_ne_of_nonempty [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {s t : ℕ} {p : G.TokenConfiguration s × G.TokenConfiguration t}
    (h : (G.oddCrossComponents p.1.1 p.2.1).Nonempty) :
    chargePairToggle hclaw s t p ≠ p := by
  intro heq
  obtain ⟨h1, -⟩ := chargePairToggle_of_nonempty hclaw h
  have hQ := chosenOddComponent_mem h
  obtain ⟨hQc, -⟩ := mem_oddCrossComponents.mp hQ
  have hne : (G.chosenOddComponent p.1.1 p.2.1).Nonempty := by
    obtain ⟨x⟩ := hQc.2.1.nonempty
    exact ⟨x.1, Finset.mem_coe.mp x.2⟩
  have hfix : symmDiff p.1.1 (G.chosenOddComponent p.1.1 p.2.1) = p.1.1 := by
    rw [← h1, heq]
  rw [symmDiff_eq_left] at hfix
  exact hne.ne_empty hfix

/-! ### The commutator of two token-sliding charges as a sum over pairs -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- The summand of the expansion `[q_{s,μ}, q_{t,ν}] = Σ_{S ∈ μ, S' ∈ ν} [h_S, h_{S'}]`
(v1 L882), written over all pairs of token configurations with an indicator. -/
noncomputable def chargePairTerm [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {s t : ℕ}
    (μ : G.TokenSlidingComponent s) (ν : G.TokenSlidingComponent t)
    (p : G.TokenConfiguration s × G.TokenConfiguration t) : A := by
  classical
  exact if G.tokenSlidingComponentMk s p.1 = μ ∧ G.tokenSlidingComponentMk t p.2 = ν then
    H.independentProduct p.1.1 * H.independentProduct p.2.1 -
      H.independentProduct p.2.1 * H.independentProduct p.1.1 else 0

/-- `chargePairTerm` with its decidability instance made explicit. -/
theorem chargePairTerm_eq_ite [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {s t : ℕ}
    (μ : G.TokenSlidingComponent s) (ν : G.TokenSlidingComponent t)
    (p : G.TokenConfiguration s × G.TokenConfiguration t)
    [Decidable (G.tokenSlidingComponentMk s p.1 = μ ∧ G.tokenSlidingComponentMk t p.2 = ν)] :
    H.chargePairTerm μ ν p =
      if G.tokenSlidingComponentMk s p.1 = μ ∧ G.tokenSlidingComponentMk t p.2 = ν then
        H.independentProduct p.1.1 * H.independentProduct p.2.1 -
          H.independentProduct p.2.1 * H.independentProduct p.1.1 else 0 := by
  unfold chargePairTerm
  congr

open scoped Classical in
/-- Expansion of the commutator of two token-sliding charges as a sum over all pairs of
token configurations (v1 L882, `equation:conservedchargescommutator`). -/
theorem commutator_tokenSlidingChargeOp_eq_sum [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (s t : ℕ)
    (μ : G.TokenSlidingComponent s) (ν : G.TokenSlidingComponent t) :
    algebraCommutator (H.tokenSlidingChargeOp s μ) (H.tokenSlidingChargeOp t ν) =
      ∑ p : G.TokenConfiguration s × G.TokenConfiguration t, H.chargePairTerm μ ν p := by
  classical
  unfold tokenSlidingChargeOp tokenSlidingCharge algebraCommutator
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ)
      (t := Finset.univ), ← Finset.sum_sub_distrib, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [H.chargePairTerm_eq_ite]
  by_cases h1 : G.tokenSlidingComponentMk s S = μ <;>
    by_cases h2 : G.tokenSlidingComponentMk t T = ν <;> simp [h1, h2]

/-! ### Theorem 1(i) -/

/-- If `𝒬(S, S')` is empty then the independent products `h_S`, `h_{S'}` commute: otherwise
`c(S, S')` is odd (their product picks up the sign `(-1)^{c(S, S')}`), and some component
of `G[S ⊕ S']` has an odd count (`exists_isInducedComponent_odd`). -/
theorem commutator_independentProduct_eq_zero_of_oddCrossComponents_eq_empty
    [Fintype V] [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {S S' : Finset V} (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hempty : ¬ (G.oddCrossComponents S S').Nonempty) :
    H.independentProduct S * H.independentProduct S' -
      H.independentProduct S' * H.independentProduct S = 0 := by
  have heven : Even (G.crossCount S S') := by
    by_contra hodd
    exact hempty (oddCrossComponents_nonempty_of_odd hS hS' (Nat.not_even_iff_odd.mp hodd))
  rw [sub_eq_zero]
  exact H.independentProduct_mul_independentProduct_of_even hS hS' heven

/-- **Theorem 1(i)** (v1 `theorem:conservedcharges` (i), L864-871, proof L880-902).

For a Hamiltonian with claw-free (finite) frustration graph `G`, represented by
`H : G.PauliFrustrationRepresentation A`, the token-sliding charges commute pairwise:
`[q_{s,μ}, q_{t,ν}] = 0` for all `s, t`, `μ ∈ Ξ_s`, `ν ∈ Ξ_t`.

There is no premise beyond the representation `H`, the finiteness of `V` and the
claw-freeness of `G`; the ring `A` is arbitrary.

The proof is v1's: expand `[q_{s,μ}, q_{t,ν}] = Σ_{S ∈ μ, S' ∈ ν} [h_S, h_{S'}]` and pair
the term `(S, S')` with `(S ⊕ Q, S' ⊕ Q)` for the chosen odd component `Q` of
`G[S ⊕ S']` (`chargePairToggle`); the two terms cancel. -/
theorem paperTheorem1i [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree)
    (s t : ℕ) (μ : G.TokenSlidingComponent s) (ν : G.TokenSlidingComponent t) :
    algebraCommutator (H.tokenSlidingChargeOp s μ) (H.tokenSlidingChargeOp t ν) = 0 := by
  classical
  rw [H.commutator_tokenSlidingChargeOp_eq_sum]
  refine Finset.sum_involution (fun p _ => chargePairToggle hclaw s t p) ?_ ?_ ?_ ?_
  · -- the terms of `p` and its partner cancel
    intro p _
    by_cases h : (G.oddCrossComponents p.1.1 p.2.1).Nonempty
    · obtain ⟨h1, h2⟩ := chargePairToggle_of_nonempty hclaw h
      set Q := G.chosenOddComponent p.1.1 p.2.1 with hQdef
      have hQ : Q ∈ G.oddCrossComponents p.1.1 p.2.1 := chosenOddComponent_mem h
      have hQ' : Q ∈ G.oddCrossComponents p.2.1 p.1.1 := by
        rw [oddCrossComponents_comm]; exact hQ
      -- the partner lies in the same pair of components
      have c1 : G.tokenSlidingComponentMk s (chargePairToggle hclaw s t p).1 =
          G.tokenSlidingComponentMk s p.1 :=
        tokenSlidingComponentMk_eq_of_symmDiff_oddCrossComponents hclaw p.1 _ p.2.2.isIndepSet hQ h1
      have c2 : G.tokenSlidingComponentMk t (chargePairToggle hclaw s t p).2 =
          G.tokenSlidingComponentMk t p.2 :=
        tokenSlidingComponentMk_eq_of_symmDiff_oddCrossComponents hclaw p.2 _ p.1.2.isIndepSet hQ' h2
      rw [H.chargePairTerm_eq_ite μ ν p, H.chargePairTerm_eq_ite μ ν (chargePairToggle hclaw s t p),
        c1, c2]
      by_cases hc : G.tokenSlidingComponentMk s p.1 = μ ∧
          G.tokenSlidingComponentMk t p.2 = ν
      · rw [if_pos hc, if_pos hc, h1, h2]
        exact H.independentProduct_toggle_commutator_add_eq_zero p.1.2.isIndepSet
          p.2.2.isIndepSet hQ
      · rw [if_neg hc, if_neg hc, add_zero]
    · rw [chargePairToggle_of_not_nonempty hclaw h, H.chargePairTerm_eq_ite,
        commutator_independentProduct_eq_zero_of_oddCrossComponents_eq_empty H p.1.2.isIndepSet
          p.2.2.isIndepSet h]
      simp
  · -- no fixed points among the nonzero terms
    intro p _ hne
    by_cases h : (G.oddCrossComponents p.1.1 p.2.1).Nonempty
    · exact chargePairToggle_ne_of_nonempty hclaw h
    · exfalso
      apply hne
      rw [H.chargePairTerm_eq_ite,
        commutator_independentProduct_eq_zero_of_oddCrossComponents_eq_empty H p.1.2.isIndepSet
          p.2.2.isIndepSet h]
      simp
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact chargePairToggle_involutive hclaw s t p

/-- **Theorem 1(i), conservation of `H`** (the last sentence of v1 `theorem:conservedcharges`,
restricted to the charges `q_{t,ν}`): `[H, q_{t,ν}] = 0`.

By `Q^(1) = H` (`operatorIndependentSetChargeFull_one`) and `Σ_{μ ∈ Ξ₁} q_{1,μ} = Q^(1)`
(`sum_tokenSlidingChargeOp`), `H = Σ_μ q_{1,μ}`, and each `[q_{1,μ}, q_{t,ν}]` vanishes
by `paperTheorem1i`. -/
theorem hamiltonian_commute_tokenSlidingChargeOp [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree)
    (t : ℕ) (ν : G.TokenSlidingComponent t) :
    algebraCommutator H.hamiltonian (H.tokenSlidingChargeOp t ν) = 0 := by
  have hH : H.hamiltonian =
      ∑ μ ∈ G.tokenSlidingComponentFinset 1, H.tokenSlidingChargeOp 1 μ :=
    (H.operatorIndependentSetChargeFull_one).symm.trans (H.sum_tokenSlidingChargeOp 1).symm
  rw [hH]
  have hsum : algebraCommutator (∑ μ ∈ G.tokenSlidingComponentFinset 1,
        H.tokenSlidingChargeOp 1 μ) (H.tokenSlidingChargeOp t ν) =
      ∑ μ ∈ G.tokenSlidingComponentFinset 1,
        algebraCommutator (H.tokenSlidingChargeOp 1 μ) (H.tokenSlidingChargeOp t ν) := by
    simp only [algebraCommutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  exact Finset.sum_eq_zero fun μ _ => H.paperTheorem1i hclaw 1 t μ ν

end PauliFrustrationRepresentation

end SimpleGraph
