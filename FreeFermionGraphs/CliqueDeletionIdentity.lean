import FreeFermionGraphs.FundamentalIdentity
import FreeFermionGraphs.ConservedChargesIndependentSets
import FreeFermionGraphs.PauliCliqueHamiltonianOddSupport
import Mathlib.Tactic.Module

/-!
# The clique-deletion identity and the `χ`-sandwich

Manuscript (arXiv 2305.15625 v1), proof of Lemma 14 (`LadderAnticommutationRelations`,
L2060-2093): after the Fundamental Identity the proof "applies Eq.
(`transfermatrixrecursion`) again" (L2088-2093) to pass from

`{ψ_{J,+j}, χ} ∝ T_G(-u) χ T_G(u) χ + χ T_G(-u) χ T_G(u)`

to `4 Π Z_{G∖Ks}(-u²)/N`.  v1 does not derive the identity that this step needs.  This
module proves it.

Let `Ks` be a simplicial clique of the claw-free frustration graph `G` and let
`χ = Hp.term none` be the simplicial mode of the root-adjoined representation
`Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A`, `χ² = 1`.  With
`Hr = Hp.restrictSome` write

* `A(u) = T_{G∖Ks}(u) = Hr.transfer Ks u`,
* `B(u) = ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(u) = Hr.cliqueTransferSum Ks u`,
* `T(u) = T_G(u) = Hr.transfer ∅ u`,

so that `T = A - u B` (Eq. (`transfermatrixrecursion`), v1 L550; `transfer_eq_A_sub_B`).

## Main results

* `transfer_commute`, `hamiltonian_commute_transfer`: the transfer operators
  `T_{G∖W}(u)`, `T_{G∖W}(v)` of a claw-free `G` commute, and `H` commutes with
  `T_G(u)` (corollaries of Theorem 1(i), v1 L864-871, via
  `deletedCharge_commute`); `ConservedChargesIndependentSets` leaves these transfer-operator
  corollaries unstated.
* `anticomm_A_B_symm`: `{A(u), B(v)} = {B(u), A(v)}` for all `u, v`.
* `commutator_A_B_relation`: `v [A(u), B(v)] + u [B(u), A(v)] = 0` for all `u, v`.
* `transfer_cross_identity`: `A(-u) B(u) = B(-u) A(u)`.
* `transfer_mul_transfer_neg_eq_deleted`: `Z_G(-u²) = Z_{G∖Ks}(-u²) - u² B(-u) B(u)`, in the
  form `T(u) T(-u) = A(u) A(-u) - u² B(-u) B(u)`.
* `root_sandwich_anticomm`:
  `T(-v) χ T(v) χ + χ T(-v) χ T(v) = 4 Z_{G∖Ks}(-v²) - 2 Z_G(-v²)`.

## The proof (v1 gives none)

`χ` commutes with `A(u)` (the charges of `G∖Ks` involve no vertex of `Ks`) and anticommutes
with `B(u)` (each `h_j`, `j ∈ Ks`, anticommutes with `χ`, while `T_{G∖Γ[j]}` commutes with
`χ` because `Ks ⊆ Γ[j]`).  Hence `χ T(u) χ = A(u) + u B(u)`.

* `[T(u), T(v)] = 0` (Theorem 1(i) on `G`) and its `χ`-conjugate give
  `v [A(u), B(v)] + u [B(u), A(v)] = 0` (`commutator_A_B_relation`; this uses that `2` is
  invertible).
* The root-adjoined graph `G⁺ = G.adjoinRootAt Ks` is claw-free
  (`IsSimplicialClique.isClawFree_adjoinRootAt`), so Theorem 1(i) also gives
  `[Q^{G⁺,(k+1)}, Q^{G⁺,(l+1)}] = 0`.  Writing
  `Q^{G⁺,(k+1)} = Q^{(k+1)} + χ Q_{G∖Ks}^{(k)}`
  (`charge_succ_adjoinRoot`) and `Q^{(k+1)} = Q_{G∖Ks}^{(k+1)} + B_k`
  (`charge_succ_clique`, Eq. (50) of v1 on the clique `Ks`), this becomes, coefficient by
  coefficient and after cancelling `χ` (`χ² = 1`), the identity
  `{Q_{G∖Ks}^{(k)}, B_l} = {B_k, Q_{G∖Ks}^{(l)}}` for all `k, l ≥ 0`
  (`anticommutator_deletedCharge_cliqueCharge_symm`).  Its generating function is
  `anticomm_A_B_symm`.  Working with the coefficients avoids dividing by `u v`, so the
  identity holds for *all* `u, v` (including `0`) with no polynomial-extension argument.
* Setting `v = -u` in the two relations and adding gives the cross identity; the other
  identities are then direct expansions.

## Deviations from v1

* v1 takes `u` real; here `u` lies in a commutative ring `R` acting on `A`
  (a field of characteristic `0` where `2` has to be inverted).
* v1 states the relevant lemmas for "SCF Hamiltonians"; the hypotheses used here are
  claw-freeness of `G`, simpliciality of `Ks` and `χ² = 1`, all part of the v1 setup (a Pauli
  operator squares to the identity), and no field of the representation assumes a
  conclusion.  Hence the paper-facing names carry no `_of_` qualifier.
* `anticomm_A_B_symm` and its coefficient form need neither a field nor characteristic `0`;
  `commutator_A_B_relation` and everything after it need `2` to be invertible (a field of
  characteristic `0`, as in the target statements).
-/

open Set Finset
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w} [Ring A]
variable [Fintype V] [DecidableEq V]

/-! ### Commutation of the transfer operators (corollaries of Theorem 1(i)) -/

section Commutation

variable {R : Type*} [CommRing R] [Algebra R A]

/-- **Transfer operators commute** (corollary of v1 Theorem 1(i), L864-871): for a claw-free
`G` and any deleted carrier `W`, `T_{G∖W}(u) T_{G∖W}(v) = T_{G∖W}(v) T_{G∖W}(u)`.

The transfer operator is a linear combination of the charges `Q_{G∖W}^(k)`, which commute
pairwise by `deletedCharge_commute`. -/
theorem transfer_commute (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree)
    (W : Set V) (u v : R) :
    Commute (H.transfer W u) (H.transfer W v) := by
  unfold transfer
  refine Commute.sum_left _ _ _ (fun k _ => Commute.sum_right _ _ _ (fun l _ => ?_))
  exact ((H.deletedCharge_commute hclaw W k l).smul_left _).smul_right _

/-- `Z_{G∖W}(-u²) = T(u) T(-u) = T(-u) T(u)`: the two orderings agree
(`transfer_commute` with `v = -u`). -/
theorem transfer_mul_transfer_neg_comm (H : G.PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (W : Set V) (u : R) :
    H.transfer W u * H.transfer W (-u) = H.transfer W (-u) * H.transfer W u :=
  (H.transfer_commute hclaw W u (-u)).eq

/-- **The Hamiltonian commutes with the transfer operator** (corollary of v1 Theorem 1(i),
L864-871, and `Q^(1) = H`): `[H, T_G(u)] = 0` for claw-free `G`. -/
theorem hamiltonian_commute_transfer (H : G.PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (u : R) :
    Commute H.hamiltonian (H.transfer ∅ u) := by
  unfold transfer
  exact Commute.sum_right _ _ _
    (fun k _ => (H.hamiltonian_commute_charge hclaw k).smul_right _)

end Commutation

/-! ### The operators `A`, `B` and the recursion `T = A - u B` -/

section Clique

variable {R : Type*} [CommRing R] [Algebra R A]

/-- The coefficient `B_k = ∑_{j ∈ Ks} h_j Q_{G∖Γ[j]}^(k)` of the clique correction in the
charge recursion Eq. (50) of v1 (L529). -/
noncomputable def cliqueCharge (H : G.PauliFrustrationRepresentation A) (Ks : Set V)
    (k : ℕ) : A :=
  ∑ j ∈ verticesOfSet Ks, H.term j * H.deletedCharge (G.closedNeighborhood j) k

/-- The clique correction `B(u) = ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(u)` of the transfer-matrix
recursion Eq. (`transfermatrixrecursion`) (v1 L550): `T_G = T_{G∖Ks} - u B`. -/
noncomputable def cliqueTransferSum (H : G.PauliFrustrationRepresentation A) (Ks : Set V)
    (u : R) : A :=
  ∑ j ∈ verticesOfSet Ks, H.term j * H.transfer (G.closedNeighborhood j) u

/-- `B(u)` is the generating function of the coefficients `B_k`. -/
theorem cliqueTransferSum_eq_sum (H : G.PauliFrustrationRepresentation A) (Ks : Set V)
    (u : R) :
    H.cliqueTransferSum Ks u =
      ∑ k ∈ Finset.range (Fintype.card V + 1), (-u) ^ k • H.cliqueCharge Ks k := by
  unfold cliqueTransferSum cliqueCharge
  rw [sum_range_smul_sum_mul_left]
  rfl

/-- Eq. (50) of v1 on the clique `Ks`, in the notation of this module:
`Q^(k+1) = Q_{G∖Ks}^(k+1) + B_k`. -/
theorem charge_succ_clique (H : G.PauliFrustrationRepresentation A) {Ks : Set V}
    (hK : G.IsClique Ks) (k : ℕ) :
    H.charge (k + 1) = H.deletedCharge Ks (k + 1) + H.cliqueCharge Ks k :=
  operatorIndependentSetCharge_clique H.toOperatorModel hK k

/-- Eq. (`transfermatrixrecursion`) (v1 L550) for a clique `Ks`:
`T_G(u) = T_{G∖Ks}(u) - u ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(u)`, i.e. `T = A - u B`. -/
theorem transfer_eq_sub_cliqueTransferSum (H : G.PauliFrustrationRepresentation A)
    (hK : G.IsClique Ks) (u : R) :
    H.transfer ∅ u = H.transfer Ks u - u • H.cliqueTransferSum Ks u :=
  H.transfer_clique hK u

/-- Eq. (`transfermatrixrecursion`) (v1 L550) for a simplicial clique `Ks`:
`T_G(u) = T_{G∖Ks}(u) - u ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(u)`, i.e. `T = A - u B`. -/
theorem transfer_eq_A_sub_B (H : G.PauliFrustrationRepresentation A)
    (hKs : G.IsSimplicialClique Ks) (u : R) :
    H.transfer ∅ u = H.transfer Ks u - u • H.cliqueTransferSum Ks u :=
  H.transfer_eq_sub_cliqueTransferSum hKs.isClique u

end Clique

/-! ### Commutation with `χ` -/

omit [Fintype V] [DecidableEq V] in
/-- A clique is contained in the closed neighbourhood of each of its vertices. -/
theorem subset_closedNeighborhood_of_isClique {K : Set V} (hK : G.IsClique K) {j : V}
    (hj : j ∈ K) : K ⊆ G.closedNeighborhood j := by
  intro v hv
  by_cases hvj : v = j
  · exact Or.inl hvj
  · exact Or.inr (hK hj hv (Ne.symm hvj))

/-- If `χ` anticommutes with every `h_j` and commutes with every `Q_j` (`j ∈ s`), it
anticommutes with `∑_j h_j Q_j`. -/
theorem mul_sum_mul_eq_neg {ι : Type*} (s : Finset ι) (χ : A) (h Q : ι → A)
    (hanti : ∀ j ∈ s, χ * h j = -(h j * χ)) (hcomm : ∀ j ∈ s, χ * Q j = Q j * χ) :
    χ * ∑ j ∈ s, h j * Q j = -((∑ j ∈ s, h j * Q j) * χ) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  calc χ * (h j * Q j) = (χ * h j) * Q j := (mul_assoc _ _ _).symm
    _ = -(h j * χ) * Q j := by rw [hanti j hj]
    _ = -(h j * (χ * Q j)) := by rw [neg_mul, mul_assoc]
    _ = -(h j * (Q j * χ)) := by rw [hcomm j hj]
    _ = -(h j * Q j * χ) := by rw [mul_assoc]

section Root

variable (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
variable {R : Type*} [CommRing R] [Algebra R A]

/-- `χ` commutes with `T_{G∖W}(u)` whenever `Ks ⊆ W`. -/
theorem root_commute_transfer {W : Set V} (hKW : Ks ⊆ W) (u : R) :
    Commute (Hp.term none) (Hp.restrictSome.transfer W u) := by
  unfold transfer
  exact Commute.sum_right _ _ _
    (fun k _ => (Hp.root_commute_deletedCharge hKW k).smul_right _)

/-- `χ` anticommutes with `B_k = ∑_{j ∈ Ks} h_j Q_{G∖Γ[j]}^(k)`: it anticommutes with each
`h_j`, `j ∈ Ks`, and commutes with `Q_{G∖Γ[j]}` since `Ks ⊆ Γ[j]`. -/
theorem root_anticommute_cliqueCharge (hK : G.IsClique Ks) (k : ℕ) :
    Hp.term none * Hp.restrictSome.cliqueCharge Ks k =
      -(Hp.restrictSome.cliqueCharge Ks k * Hp.term none) := by
  unfold cliqueCharge
  refine mul_sum_mul_eq_neg _ _ (fun j => Hp.restrictSome.term j) _ ?_ ?_
  · intro j hj
    exact (Hp.root_anticommute_iff j).mp (mem_verticesOfSet.mp hj)
  · intro j hj
    exact (Hp.root_commute_deletedCharge
      (subset_closedNeighborhood_of_isClique hK (mem_verticesOfSet.mp hj)) k).eq

/-- `χ` anticommutes with `B(u) = ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(u)`. -/
theorem root_anticommute_cliqueTransferSum (hK : G.IsClique Ks) (u : R) :
    Hp.term none * Hp.restrictSome.cliqueTransferSum Ks u =
      -(Hp.restrictSome.cliqueTransferSum Ks u * Hp.term none) := by
  unfold cliqueTransferSum
  refine mul_sum_mul_eq_neg _ _ (fun j => Hp.restrictSome.term j) _ ?_ ?_
  · intro j hj
    exact (Hp.root_anticommute_iff j).mp (mem_verticesOfSet.mp hj)
  · intro j hj
    exact (Hp.root_commute_transfer
      (subset_closedNeighborhood_of_isClique hK (mem_verticesOfSet.mp hj)) u).eq

/-- Conjugation by `χ`: `χ T_G(u) χ = T_{G∖Ks}(u) + u B(u)` (when `χ² = 1`).  This is the
sign flip of the clique correction `B` under `χ`, v1 Definition 8 (L591). -/
theorem root_conj_transfer (hK : G.IsClique Ks) (hroot : Hp.term none * Hp.term none = 1)
    (u : R) :
    Hp.term none * Hp.restrictSome.transfer ∅ u * Hp.term none =
      Hp.restrictSome.transfer Ks u + u • Hp.restrictSome.cliqueTransferSum Ks u := by
  have hA := (Hp.root_commute_transfer (W := Ks) (subset_refl _) u).eq
  have hB := Hp.root_anticommute_cliqueTransferSum hK u
  set χ := Hp.term none with hχ
  set Au := Hp.restrictSome.transfer Ks u with hAu
  set Bu := Hp.restrictSome.cliqueTransferSum Ks u with hBu
  have hAχ : χ * Au * χ = Au := by rw [hA, mul_assoc, hroot, mul_one]
  have hBχ : χ * Bu * χ = -Bu := by rw [hB, neg_mul, mul_assoc, hroot, mul_one]
  rw [Hp.restrictSome.transfer_eq_sub_cliqueTransferSum hK u, mul_sub, sub_mul, mul_smul_comm,
    smul_mul_assoc, hAχ, hBχ, smul_neg, sub_neg_eq_add]

end Root

/-! ### The coefficient identity -/

/-- The pure-algebra core of `anticommutator_deletedCharge_cliqueCharge_symm`.

Let `χ² = 1` commute with `p, q, p', q'` and anticommute with `bk, bl`, let `p, p', q, q'`
commute pairwise as needed, and suppose `X = p' + bk` and `Y = q' + bl` commute and so do
`X + χ p` and `Y + χ q`.  Then `{p, bl} = {bk, q}`. -/
theorem anticomm_core {χ p q p' q' bk bl : A} (hχ : χ * χ = 1)
    (hp : χ * p = p * χ) (hq : χ * q = q * χ) (hp' : χ * p' = p' * χ)
    (hq' : χ * q' = q' * χ)
    (hbk : χ * bk = -(bk * χ)) (hbl : χ * bl = -(bl * χ))
    (hpq : p * q = q * p) (hp'q : p' * q = q * p') (hpq' : p * q' = q' * p)
    (hXY : (p' + bk) * (q' + bl) = (q' + bl) * (p' + bk))
    (h : (p' + bk + χ * p) * (q' + bl + χ * q) = (q' + bl + χ * q) * (p' + bk + χ * p)) :
    p * bl + bl * p = bk * q + q * bk := by
  have hp'χ : p' * χ = χ * p' := hp'.symm
  have hq'χ : q' * χ = χ * q' := hq'.symm
  have hpχ : p * χ = χ * p := hp.symm
  have hqχ : q * χ = χ * q := hq.symm
  have hbkχ : bk * χ = -(χ * bk) := by rw [hbk, neg_neg]
  have hblχ : bl * χ = -(χ * bl) := by rw [hbl, neg_neg]
  -- the four pieces of the commutator `[X + χ p, Y + χ q]`
  have f2 : (p' + bk) * (χ * q) - (χ * q) * (p' + bk) = -(χ * (bk * q + q * bk)) := by
    calc (p' + bk) * (χ * q) - (χ * q) * (p' + bk)
        = (p' * χ) * q + (bk * χ) * q - χ * (q * p') - χ * (q * bk) := by noncomm_ring
      _ = (χ * p') * q + (-(χ * bk)) * q - χ * (p' * q) - χ * (q * bk) := by
          rw [hp'χ, hbkχ, ← hp'q]
      _ = -(χ * (bk * q + q * bk)) := by noncomm_ring
  have f3 : (χ * p) * (q' + bl) - (q' + bl) * (χ * p) = χ * (p * bl + bl * p) := by
    calc (χ * p) * (q' + bl) - (q' + bl) * (χ * p)
        = χ * (p * q') + χ * (p * bl) - (q' * χ) * p - (bl * χ) * p := by noncomm_ring
      _ = χ * (q' * p) + χ * (p * bl) - (χ * q') * p - (-(χ * bl)) * p := by
          rw [hpq', hq'χ, hblχ]
      _ = χ * (p * bl + bl * p) := by noncomm_ring
  have f4 : (χ * p) * (χ * q) - (χ * q) * (χ * p) = 0 := by
    calc (χ * p) * (χ * q) - (χ * q) * (χ * p)
        = χ * (p * χ) * q - χ * (q * χ) * p := by noncomm_ring
      _ = χ * (χ * p) * q - χ * (χ * q) * p := by rw [hpχ, hqχ]
      _ = (χ * χ) * (p * q) - (χ * χ) * (q * p) := by noncomm_ring
      _ = 0 := by rw [hχ, hpq]; noncomm_ring
  have hsplit : (p' + bk + χ * p) * (q' + bl + χ * q) -
        (q' + bl + χ * q) * (p' + bk + χ * p) =
      ((p' + bk) * (q' + bl) - (q' + bl) * (p' + bk)) +
        ((p' + bk) * (χ * q) - (χ * q) * (p' + bk)) +
        ((χ * p) * (q' + bl) - (q' + bl) * (χ * p)) +
        ((χ * p) * (χ * q) - (χ * q) * (χ * p)) := by noncomm_ring
  have hzero : χ * (p * bl + bl * p - (bk * q + q * bk)) = 0 := by
    have h0 : (p' + bk + χ * p) * (q' + bl + χ * q) -
        (q' + bl + χ * q) * (p' + bk + χ * p) = 0 := sub_eq_zero.mpr h
    rw [hsplit, hXY, sub_self, zero_add, f2, f3, f4, add_zero] at h0
    calc χ * (p * bl + bl * p - (bk * q + q * bk))
        = -(χ * (bk * q + q * bk)) + χ * (p * bl + bl * p) := by rw [mul_sub]; abel
      _ = 0 := h0
  have := congrArg (fun x => χ * x) hzero
  simp only [← mul_assoc, hχ, one_mul, mul_zero] at this
  exact sub_eq_zero.mp this

/-- **The coefficient identity** (the cross relation behind v1 L2088-2093):
`{Q_{G∖Ks}^(k), B_l} = {B_k, Q_{G∖Ks}^(l)}` for all `k, l ≥ 0`, where
`B_k = ∑_{j ∈ Ks} h_j Q_{G∖Γ[j]}^(k)`.

It is the `χ`-component of `[Q^{G⁺,(k+1)}, Q^{G⁺,(l+1)}] = 0`, which is Theorem 1(i)
(v1 L864-871) for the claw-free root-adjoined graph `G⁺ = G.adjoinRootAt Ks`.  Claw-freeness
of `G⁺` is `IsSimplicialClique.isClawFree_adjoinRootAt`. -/
theorem anticommutator_deletedCharge_cliqueCharge_symm
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hroot : Hp.term none * Hp.term none = 1) (k l : ℕ) :
    Hp.restrictSome.deletedCharge Ks k * Hp.restrictSome.cliqueCharge Ks l +
        Hp.restrictSome.cliqueCharge Ks l * Hp.restrictSome.deletedCharge Ks k =
      Hp.restrictSome.cliqueCharge Ks k * Hp.restrictSome.deletedCharge Ks l +
        Hp.restrictSome.deletedCharge Ks l * Hp.restrictSome.cliqueCharge Ks k := by
  have hclaw' : (G.adjoinRootAt Ks).IsClawFree := hKs.isClawFree_adjoinRootAt hclaw
  have h := (Hp.charge_commute_charge hclaw' (k + 1) (l + 1)).eq
  have hXY := (Hp.restrictSome.charge_commute_charge hclaw (k + 1) (l + 1)).eq
  rw [Hp.charge_succ_adjoinRoot k, Hp.charge_succ_adjoinRoot l,
    Hp.restrictSome.charge_succ_clique hKs.isClique k,
    Hp.restrictSome.charge_succ_clique hKs.isClique l] at h
  rw [Hp.restrictSome.charge_succ_clique hKs.isClique k,
    Hp.restrictSome.charge_succ_clique hKs.isClique l] at hXY
  exact anticomm_core hroot
    (Hp.root_commute_deletedCharge (subset_refl Ks) k).eq
    (Hp.root_commute_deletedCharge (subset_refl Ks) l).eq
    (Hp.root_commute_deletedCharge (subset_refl Ks) (k + 1)).eq
    (Hp.root_commute_deletedCharge (subset_refl Ks) (l + 1)).eq
    (Hp.root_anticommute_cliqueCharge hKs.isClique k)
    (Hp.root_anticommute_cliqueCharge hKs.isClique l)
    (Hp.restrictSome.deletedCharge_commute hclaw Ks k l).eq
    (Hp.restrictSome.deletedCharge_commute hclaw Ks (k + 1) l).eq
    (Hp.restrictSome.deletedCharge_commute hclaw Ks k (l + 1)).eq
    hXY h

section Generating

variable {R : Type*} [CommRing R] [Algebra R A]

/-- The product of two generating functions, expanded as a double sum. -/
theorem sum_smul_mul_sum_smul (x y : ℕ → A) (s t : R) (n : ℕ) :
    (∑ k ∈ Finset.range n, s ^ k • x k) * (∑ l ∈ Finset.range n, t ^ l • y l) =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, (s ^ k * t ^ l) • (x k * y l) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_smul_comm]

/-- **`{A(u), B(v)} = {B(u), A(v)}`** for all `u, v` (v1 gives no proof; this is the
anticommutator half of the identity needed at v1 L2088-2093), where `A = T_{G∖Ks}` and
`B = ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}`.

It is the generating function of `anticommutator_deletedCharge_cliqueCharge_symm`; no
division by `u v` is needed, so it holds for all `u, v`, including `0`. -/
theorem anticomm_A_B_symm (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hroot : Hp.term none * Hp.term none = 1) (u v : R) :
    Hp.restrictSome.transfer Ks u * Hp.restrictSome.cliqueTransferSum Ks v +
        Hp.restrictSome.cliqueTransferSum Ks v * Hp.restrictSome.transfer Ks u =
      Hp.restrictSome.cliqueTransferSum Ks u * Hp.restrictSome.transfer Ks v +
        Hp.restrictSome.transfer Ks v * Hp.restrictSome.cliqueTransferSum Ks u := by
  have hA : ∀ w : R, Hp.restrictSome.transfer Ks w =
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        (-w) ^ k • Hp.restrictSome.deletedCharge Ks k :=
    fun w => rfl
  simp only [Hp.restrictSome.cliqueTransferSum_eq_sum, hA]
  rw [sum_smul_mul_sum_smul, sum_smul_mul_sum_smul, sum_smul_mul_sum_smul,
    sum_smul_mul_sum_smul]
  have e2 : ∀ x y : ℕ → A, ∑ l ∈ Finset.range (Fintype.card V + 1),
        ∑ k ∈ Finset.range (Fintype.card V + 1), ((-v) ^ l * (-u) ^ k) • (x l * y k) =
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        ∑ l ∈ Finset.range (Fintype.card V + 1), ((-u) ^ k * (-v) ^ l) • (x l * y k) := by
    intro x y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  rw [e2, e2]
  simp only [← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [anticommutator_deletedCharge_cliqueCharge_symm Hp hclaw hKs hroot k l]

end Generating

section CharZero

variable {R : Type*} [Field R] [CharZero R] [Algebra R A]

/-- In an algebra over a field of characteristic `0`, `2 x = 0` implies `x = 0`. -/
theorem eq_zero_of_two_smul_eq_zero {x : A} (h : (2 : R) • x = 0) : x = 0 := by
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  have := congrArg (fun y => (2 : R)⁻¹ • y) h
  simpa [smul_smul, inv_mul_cancel₀ h2] using this

omit [CharZero R] in
/-- In an algebra over a field, `c x = 0` with `c ≠ 0` implies `x = 0`. -/
theorem eq_zero_of_smul_eq_zero_of_ne {c : R} (hc : c ≠ 0) {x : A} (h : c • x = 0) :
    x = 0 := by
  have := congrArg (fun y => c⁻¹ • y) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using this

/-- **The commutator relation** `v [A(u), B(v)] + u [B(u), A(v)] = 0`, where
`A = T_{G∖Ks}` and `B = ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}`.

It follows from `[T_G(u), T_G(v)] = 0` (Theorem 1(i), v1 L864-871, `transfer_commute`) and
its conjugate by `χ`, `[A(u) + u B(u), A(v) + v B(v)] = 0` (`root_conj_transfer`): their
difference is `2 (v [A(u), B(v)] + u [B(u), A(v)])`. -/
theorem commutator_A_B_relation (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hroot : Hp.term none * Hp.term none = 1) (u v : R) :
    v • (Hp.restrictSome.transfer Ks u * Hp.restrictSome.cliqueTransferSum Ks v -
        Hp.restrictSome.cliqueTransferSum Ks v * Hp.restrictSome.transfer Ks u) +
      u • (Hp.restrictSome.cliqueTransferSum Ks u * Hp.restrictSome.transfer Ks v -
        Hp.restrictSome.transfer Ks v * Hp.restrictSome.cliqueTransferSum Ks u) = 0 := by
  have h1 := (Hp.restrictSome.transfer_commute hclaw ∅ u v).eq
  have c := fun w : R => Hp.root_conj_transfer hKs.isClique hroot w
  have hconj : ∀ x y : A, Hp.term none * x * Hp.term none * (Hp.term none * y * Hp.term none) =
      Hp.term none * (x * y) * Hp.term none := by
    intro x y
    calc Hp.term none * x * Hp.term none * (Hp.term none * y * Hp.term none)
        = Hp.term none * x * (Hp.term none * Hp.term none) * y * Hp.term none := by
          noncomm_ring
      _ = Hp.term none * (x * y) * Hp.term none := by rw [hroot]; noncomm_ring
  have h2 : (Hp.restrictSome.transfer Ks u + u • Hp.restrictSome.cliqueTransferSum Ks u) *
        (Hp.restrictSome.transfer Ks v + v • Hp.restrictSome.cliqueTransferSum Ks v) =
      (Hp.restrictSome.transfer Ks v + v • Hp.restrictSome.cliqueTransferSum Ks v) *
        (Hp.restrictSome.transfer Ks u + u • Hp.restrictSome.cliqueTransferSum Ks u) := by
    rw [← c u, ← c v, hconj, hconj, h1]
  rw [Hp.restrictSome.transfer_eq_A_sub_B hKs, Hp.restrictSome.transfer_eq_A_sub_B hKs] at h1
  apply eq_zero_of_two_smul_eq_zero (R := R)
  have key : (2 : R) • (v • (Hp.restrictSome.transfer Ks u *
          Hp.restrictSome.cliqueTransferSum Ks v -
        Hp.restrictSome.cliqueTransferSum Ks v * Hp.restrictSome.transfer Ks u) +
      u • (Hp.restrictSome.cliqueTransferSum Ks u * Hp.restrictSome.transfer Ks v -
        Hp.restrictSome.transfer Ks v * Hp.restrictSome.cliqueTransferSum Ks u)) =
      ((Hp.restrictSome.transfer Ks u + u • Hp.restrictSome.cliqueTransferSum Ks u) *
        (Hp.restrictSome.transfer Ks v + v • Hp.restrictSome.cliqueTransferSum Ks v) -
      (Hp.restrictSome.transfer Ks v + v • Hp.restrictSome.cliqueTransferSum Ks v) *
        (Hp.restrictSome.transfer Ks u + u • Hp.restrictSome.cliqueTransferSum Ks u)) -
      ((Hp.restrictSome.transfer Ks u - u • Hp.restrictSome.cliqueTransferSum Ks u) *
        (Hp.restrictSome.transfer Ks v - v • Hp.restrictSome.cliqueTransferSum Ks v) -
      (Hp.restrictSome.transfer Ks v - v • Hp.restrictSome.cliqueTransferSum Ks v) *
        (Hp.restrictSome.transfer Ks u - u • Hp.restrictSome.cliqueTransferSum Ks u)) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_add, smul_sub]
    module
  rw [key, sub_eq_zero.mpr h2, sub_eq_zero.mpr h1, sub_zero]

/-- **The cross identity** `A(-u) B(u) = B(-u) A(u)`, i.e.
`T_{G∖Ks}(-u) ∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(u) =
∑_{j ∈ Ks} h_j T_{G∖Γ[j]}(-u) T_{G∖Ks}(u)`.

This is the identity that v1 uses without proof when it "applies Eq.
(`transfermatrixrecursion`) again" (L2088-2093).  Adding the commutator relation
`commutator_A_B_relation` and the anticommutator relation `anticomm_A_B_symm` at `(-u, u)`
gives `2 A(-u) B(u) = 2 B(-u) A(u)`; both come from Theorem 1(i) (v1 L864-871) on `G` and on
the claw-free root-adjoined graph `G⁺`. -/
theorem transfer_cross_identity (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hroot : Hp.term none * Hp.term none = 1) (u : R) :
    Hp.restrictSome.transfer Ks (-u) * Hp.restrictSome.cliqueTransferSum Ks u =
      Hp.restrictSome.cliqueTransferSum Ks (-u) * Hp.restrictSome.transfer Ks u := by
  by_cases hu : u = 0
  · subst hu
    rw [neg_zero, Hp.restrictSome.transfer_zero, one_mul, mul_one]
  · have h1 := commutator_A_B_relation Hp hclaw hKs hroot (-u) u
    have h2 := anticomm_A_B_symm Hp hclaw hKs hroot (-u) u
    set a := Hp.restrictSome.transfer Ks (-u) with ha
    set b := Hp.restrictSome.cliqueTransferSum Ks u with hb
    set a' := Hp.restrictSome.transfer Ks u with ha'
    set b' := Hp.restrictSome.cliqueTransferSum Ks (-u) with hb'
    have h3 : u • ((a * b - b * a) - (b' * a' - a' * b')) = 0 := by
      rw [← h1, smul_sub, neg_smul]
      abel
    have h4 := eq_zero_of_smul_eq_zero_of_ne hu h3
    apply sub_eq_zero.mp
    apply eq_zero_of_two_smul_eq_zero (R := R)
    have key : (2 : R) • (a * b - b' * a') =
        ((a * b - b * a) - (b' * a' - a' * b')) + ((a * b + b * a) - (b' * a' + a' * b')) := by
      module
    rw [key, h4, sub_eq_zero.mpr h2, add_zero]

/-- **Clique-deletion identity for `Z`**: `Z_G(-u²) = Z_{G∖Ks}(-u²) - u² B(-u) B(u)`, with
`Z_G(-u²) = T_G(u) T_G(-u)` (v1 Definition 7) and
`Z_{G∖Ks}(-u²) = T_{G∖Ks}(u) T_{G∖Ks}(-u)`.

This is the second application of Eq. (`transfermatrixrecursion`) at v1 L2088-2093:
`T(u) T(-u) = T(-u) T(u) = (A(-u) + u B(-u)) (A(u) - u B(u))`, and the two cross terms cancel
by `transfer_cross_identity`. -/
theorem transfer_mul_transfer_neg_eq_deleted
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hroot : Hp.term none * Hp.term none = 1) (u : R) :
    Hp.restrictSome.transfer ∅ u * Hp.restrictSome.transfer ∅ (-u) =
      Hp.restrictSome.transfer Ks u * Hp.restrictSome.transfer Ks (-u) -
        u ^ 2 • (Hp.restrictSome.cliqueTransferSum Ks (-u) *
          Hp.restrictSome.cliqueTransferSum Ks u) := by
  have hAA := (Hp.restrictSome.transfer_commute hclaw Ks u (-u)).eq
  have hc := transfer_cross_identity Hp hclaw hKs hroot u
  rw [Hp.restrictSome.transfer_mul_transfer_neg_comm hclaw ∅ u,
    Hp.restrictSome.transfer_eq_A_sub_B hKs (-u), Hp.restrictSome.transfer_eq_A_sub_B hKs u,
    hAA]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub, neg_smul,
    smul_neg, neg_mul]
  rw [hc]
  module

/-- **The `χ`-sandwich**:
`T_G(-v) χ T_G(v) χ + χ T_G(-v) χ T_G(v) = 4 Z_{G∖Ks}(-v²) - 2 Z_G(-v²)`
(the step at v1 L2088-2093 that turns `{ψ_{J,+j}, χ}` into `4 Π Z_{G∖Ks}(-u_{J,j}²)/N`).

Conjugation by `χ` flips the sign of `B` (`root_conj_transfer`), so the left side is
`T(-v) (A(v) + v B(v)) + (A(-v) - v B(-v)) T(v) = 2 A(-v) A(v) + 2 v² B(-v) B(v)`, and
`Z_G(-v²) = Z_{G∖Ks}(-v²) - v² B(-v) B(v)` by `transfer_mul_transfer_neg_eq_deleted`. -/
theorem root_sandwich_anticomm (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hroot : Hp.term none * Hp.term none = 1) (v : R) :
    Hp.restrictSome.transfer ∅ (-v) * Hp.term none * Hp.restrictSome.transfer ∅ v *
          Hp.term none +
        Hp.term none * Hp.restrictSome.transfer ∅ (-v) * Hp.term none *
          Hp.restrictSome.transfer ∅ v =
      (4 : R) • (Hp.restrictSome.transfer Ks v * Hp.restrictSome.transfer Ks (-v)) -
        (2 : R) • (Hp.restrictSome.transfer ∅ v * Hp.restrictSome.transfer ∅ (-v)) := by
  have c1 := Hp.root_conj_transfer hKs.isClique hroot v
  have c2 := Hp.root_conj_transfer hKs.isClique hroot (-v)
  have e1 : Hp.restrictSome.transfer ∅ (-v) * Hp.term none * Hp.restrictSome.transfer ∅ v *
      Hp.term none = Hp.restrictSome.transfer ∅ (-v) *
        (Hp.restrictSome.transfer Ks v + v • Hp.restrictSome.cliqueTransferSum Ks v) := by
    rw [← c1]
    simp only [mul_assoc]
  have hAA := (Hp.restrictSome.transfer_commute hclaw Ks v (-v)).eq
  rw [e1, c2, transfer_mul_transfer_neg_eq_deleted Hp hclaw hKs hroot v,
    Hp.restrictSome.transfer_eq_A_sub_B hKs (-v), Hp.restrictSome.transfer_eq_A_sub_B hKs v,
    hAA]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_sub, neg_smul, smul_neg, neg_mul]
  module

end CharZero

end PauliFrustrationRepresentation
end SimpleGraph
