import FreeFermionGraphs.EvenHoleFamilies
import FreeFermionGraphs.ScaledPauliRepresentation

/-!
# The generalized characteristic polynomial (v1 Lemma 11) for a bare scaled Pauli representation

Manuscript reference: arXiv 2305.15625 v1, Lemma 11 (`lemma:generalizedcharacteristicpolynomial`,
statement L1266-1272, proof L1924-1985; the repository's revised numbering calls it Lemma 1).
Let `H` be a Hamiltonian with claw-free frustration graph `G`.  The generalized characteristic
polynomial `Z_G(-u²) := T_G(u) T_G(-u)` is

`Z_G(-u²) = ∑_{𝒳 ∈ 𝒞^{(even)}_G} (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖Γ[𝒳]}(-u²) ∏_{C ∈ 𝒳} h_C`.

`GeneralizedCharacteristicPolynomial` proves this for a Hamiltonian representation
`PauliCliqueHamiltonianRepresentation` of the root-adjoined graph `G⁺ = G.adjoinRootAt K`, which
carries a root operator `χ` and a clique `K` that v1's Lemma 11 does not mention (and which play
no role in its statement).  This module proves the same identity for the data that the manuscript
setup of Lemma 11 actually consists of: the frustration graph `G` itself, with Pauli terms `h_j`
squaring to the central scalars `b_j²` (v1 L93, L231-232), namely a
`ScaledPauliFrustrationRepresentation G ℝ A`.  No root, no clique and no simplicial mode are
involved.

## Main results

* `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial` : the
  identity above, in operator form, for the vertex-deleted graph `G ∖ W` of an arbitrary deleted
  carrier `W ⊆ V`, with a spectral parameter `u` in an arbitrary commutative `ℝ`-algebra `R` acting
  on `A`.  The only hypothesis beyond the setup (the representation `H`) is `G.IsClawFree`.
* `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial_empty` :
  the case `W = ∅`, which is v1 Lemma 11 itself.

The encoding of the manuscript objects (`G ∖ W`, `𝒞^{(even)}_{G∖W}`, `∂𝒳`, `Γ[𝒳]`, `I`, `h_C`, the
scalar `(-u²)^{|∂𝒳|/2} 2^{|𝒳|} I(-u²)` acting by `•`) is exactly the one documented in
`GeneralizedCharacteristicPolynomial`; here `T_{G∖W}(u)` is `PauliFrustrationRepresentation.transfer`
of `H.operator` itself (no `restrictSome`), `h_C` is read off `H.operator.familyOperator`, and the
couplings are `b_j = H.coupling j`.

## Proof

The proof of `GeneralizedCharacteristicPolynomial` re-run on the bare representation.  Two
facts about the representation were used there, and both are available for a
`PauliFrustrationRepresentation` with `h_j² = b_j²`:

* `transfer_mul_transfer_neg_eq_holeOnly` (the only place where claw-freeness is used) needs only
  the commutation structure of the terms, and
* `sum_holeOnlyPairs_fibre_of_sq` needs, besides that, `h_I h_I = ∏_{j ∈ I} b_j²` for independent
  `I`, which is `ScaledPauliFrustrationRepresentation.independentProduct_mul_self`.

## Deviations from the manuscript and from the task description

* v1 takes `u` real and the Hamiltonian terms in a matrix algebra; here `u` lies in any
  commutative `ℝ`-algebra `R` acting on `A` and `A` is any `ℝ`-algebra.
* v1's proof invokes Theorem 1 to discard the terms with `|S| + |T|` odd (L1936-1940); this is
  unnecessary (see `GeneralizedCharacteristicPolynomialPairs`), so the lemma needs claw-freeness
  only, exactly as printed.
* The package description suggested obtaining this by instantiating the root-adjoined version at
  `K = ∅` with a central root.  That reduction is avoided on purpose: a bare scaled
  representation determines the data of `PauliCliqueHamiltonianRepresentation G ∅ ℝ A` only when
  `A` is nontrivial, because the root must satisfy `χ h_j ≠ -(h_j χ)` for the nonadjacent pairs
  `(none, some j)` of `G.adjoinRootAt ∅`, which fails in the zero algebra.  The direct proof is not
  weaker: it assumes nothing about `A` beyond being an `ℝ`-algebra (and, unlike the reduction, it
  never uses `coupling_isUnit`, only `term_sq`).
* As for `GeneralizedCharacteristicPolynomial`, the final regrouping of v1 (L1981) into
  `∏ J_{⟨C₀⟩}` over deformation classes is not part of this file, and the weak compatibility of
  v1 L313 (`evenHoleFamilies`) is the one that makes the identity true.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace ScaledPauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A] [Algebra ℝ A]

/-- **The generalized characteristic polynomial (v1 Lemma 11), operator form, for `G ∖ W`, for a
bare scaled Pauli representation.**

Let `G` be claw-free, `H` a representation of it by Pauli terms `h_j` with `h_j² = b_j²`
(`ScaledPauliFrustrationRepresentation`, couplings `b_j = H.coupling j`), `W ⊆ V` a deleted
carrier and `u` an element of a commutative `ℝ`-algebra `R` acting on `A`.  Then
`T_{G∖W}(u) T_{G∖W}(-u) =
   ∑_{𝒳 ∈ 𝒞^{(even)}_{G∖W}} (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖(W ∪ Γ[𝒳])}(-u²) ∏_{C ∈ 𝒳} h_C`,
where `Γ[𝒳] = Γ[∂𝒳] = ∂𝒳 ∪ N(∂𝒳)` and `I_{G∖W'}` is the weighted independence polynomial for
the couplings `H.coupling` (`weightedIndependencePolynomial`).  The only hypothesis is
`G.IsClawFree`; there is no root operator and no clique.  See the module docstring. -/
theorem generalizedCharacteristicPolynomial [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra R A] [IsScalarTower ℝ R A]
    (H : G.ScaledPauliFrustrationRepresentation ℝ A) (hclaw : G.IsClawFree) (W : Set V)
    (u : R) :
    H.operator.transfer W u * H.operator.transfer W (-u) =
      ∑ X ∈ G.evenHoleFamilies W,
        ((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
          Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
            (W ∪ G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
          H.operator.familyOperator X := by
  classical
  rw [H.operator.transfer_mul_transfer_neg_eq_holeOnly hclaw W u]
  rw [← Finset.sum_fiberwise_of_maps_to (s := G.holeOnlyPairs W) (t := G.evenHoleFamilies W)
    (g := fun p => G.symmDiffHoleFamily p.1 p.2) (fun p hp => symmDiffHoleFamily_mem hp)]
  exact Finset.sum_congr rfl fun X hX =>
    H.operator.sum_holeOnlyPairs_fibre_of_sq H.coupling
      (fun _ hI => H.independentProduct_mul_self hI) W hX u

/-- **v1 Lemma 11 itself** (`W = ∅`), for a bare scaled Pauli representation: for claw-free `G`,
`Z_G(-u²) = T_G(u) T_G(-u) =
   ∑_{𝒳 ∈ 𝒞^{(even)}_G} (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖Γ[𝒳]}(-u²) ∏_{C ∈ 𝒳} h_C`.
This is `generalizedCharacteristicPolynomial` with nothing deleted.  Its premises are exactly the
setup of v1 Lemma 11: a claw-free frustration graph and Pauli terms with `h_j² = b_j²`. -/
theorem generalizedCharacteristicPolynomial_empty [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra R A] [IsScalarTower ℝ R A]
    (H : G.ScaledPauliFrustrationRepresentation ℝ A) (hclaw : G.IsClawFree) (u : R) :
    H.operator.transfer ∅ u * H.operator.transfer ∅ (-u) =
      ∑ X ∈ G.evenHoleFamilies ∅,
        ((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
          Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
            (G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
          H.operator.familyOperator X := by
  have h := H.generalizedCharacteristicPolynomial hclaw ∅ u
  simpa only [Set.empty_union] using h

end ScaledPauliFrustrationRepresentation

end SimpleGraph
