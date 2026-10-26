import FreeFermionGraphs.EvenHoleFamilies

/-!
# The generalized characteristic polynomial (v1 Lemma 11)

Manuscript reference: arXiv 2305.15625 v1, Lemma 11
(`lemma:generalizedcharacteristicpolynomial`, statement L1266-1272, proof L1924-1985; the
repository's revised numbering calls it Lemma 1).  Let `H` be a Hamiltonian with claw-free
frustration graph `G`.  The generalized characteristic polynomial
`Z_G(-u²) := T_G(u) T_G(-u)` is

`Z_G(-u²) = ∑_{𝒳 ∈ 𝒞^{(even)}_G} (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖Γ[𝒳]}(-u²) ∏_{C ∈ 𝒳} h_C`.

## Main result

* `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial` :
  the identity above, in operator form, for the vertex-deleted graph `G ∖ W` of an arbitrary
  deleted carrier `W ⊆ V` and a spectral parameter `u` in an arbitrary commutative `ℝ`-algebra
  `R` acting on the operator algebra `A`.  The only hypothesis is `G.IsClawFree`.
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial_empty` :
  the case `W = ∅`, which is v1 Lemma 11 itself.

## How the statement is encoded

* `G ∖ W` is represented by `G` together with the deleted carrier `W : Set V`, as in
  `FreeFermionGraphs.WeightedIndependencePolynomial`: `T_{G∖W}(u)` is
  `PauliFrustrationRepresentation.transfer`, applied to `H.operator.restrictSome`
  (the restriction of the representation of `G⁺ = G.adjoinRootAt K` to the original vertices),
  and `𝒞^{(even)}_{G∖W}` is `SimpleGraph.evenHoleFamilies G W` (families of pairwise separated
  even-hole carriers avoiding `W`, with the compatibility notion of v1 L313).
* `∂𝒳 = ⋃_{C ∈ 𝒳} C` is `G.familyBoundary X`, and `Γ[∂𝒳] = ∂𝒳 ∪ N(∂𝒳)` (closed
  neighbourhood) is written with the open neighbourhood, so `G ∖ (W ∪ Γ[𝒳])` is the carrier
  `W ∪ ∂𝒳 ∪ openNeighborhood ∂𝒳`; `I_{G∖Γ[𝒳]}` is `weightedIndependencePolynomial` for the
  couplings `b_j = H.coupling j`, evaluated at `-u²` with `Polynomial.aeval`.
* `∏_{C ∈ 𝒳} h_C` is `familyOperator X` (the factors commute pairwise because the carriers are
  separated), with `h_C` the even-hole operator `evenHoleOperator` of `EvenHoleOperators`.
* The scalar `(-u²)^{|∂𝒳|/2} 2^{|𝒳|} I(-u²)` acts on the operator by `•` (`R` acts on `A`).

## Proof

`T_{G∖W}(u) T_{G∖W}(-u)` equals the sum over the hole-only pairs `(S, T)` of
`(-u²)^{|S|} h_S h_T` (`transfer_mul_transfer_neg_eq_holeOnly`, the only place where
claw-freeness is used: the terms whose `G[S ⊕ T]` has a path component cancel in pairs).
Grouping the pairs by the family of components of `G[S ⊕ T]` (`symmDiffHoleFamily`, which lands
in `evenHoleFamilies W` by `symmDiffHoleFamily_mem`) and evaluating each fibre
(`sum_holeOnlyPairs_fibre`) gives the formula.  The fibre identity holds for *every*
`𝒳 ∈ 𝒞^{(even)}_{G∖W}`: the converse direction (every family in `evenHoleFamilies W` is the
component family of some hole-only pair, i.e. no fibre is empty) is built into it through the
bijection of the fibre with colourings of `G[∂𝒳]` times independent sets of `G ∖ (W ∪ Γ[𝒳])`
(`sum_holeOnlyPairs_filter_symmDiff_eq`, `symmDiffHoleFamily_eq`), so nothing more is needed here.

## Deviations from the manuscript

* v1 takes `u` real and the Hamiltonian terms in a matrix algebra; here `u` lies in any
  commutative `ℝ`-algebra `R` acting on `A` (so `ℂ` is allowed) and `A` is any `ℝ`-algebra.
* v1's proof invokes Theorem 1 (L1936-1940) to discard the terms with `|S| + |T|` odd; this is
  unnecessary (the path-component pairing cancels them too), so the lemma needs only
  claw-freeness, exactly as printed.  See `GeneralizedCharacteristicPolynomialPairs`.
* The final regrouping of v1 (L1981) into `∏ J_{⟨C₀⟩}` over deformation classes is not part of
  this file.
* The weak compatibility of v1 L313 is essential: with the strong notion of v1 L748 (disjoint
  closed neighbourhoods) the identity fails (see the docstring of `evenHoleFamilies`).
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace PauliCliqueHamiltonianRepresentation

variable {K : Set V} {A : Type w} [Ring A] [Algebra ℝ A]

/-- **The generalized characteristic polynomial (v1 Lemma 11), operator form, for `G ∖ W`.**

Let `G` be claw-free, `H` a Hamiltonian representation of it, `W ⊆ V` a deleted carrier and `u`
an element of a commutative `ℝ`-algebra `R` acting on `A`.  Then
`T_{G∖W}(u) T_{G∖W}(-u) =
   ∑_{𝒳 ∈ 𝒞^{(even)}_{G∖W}} (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖(W ∪ Γ[𝒳])}(-u²) ∏_{C ∈ 𝒳} h_C`,
where `Γ[𝒳] = Γ[∂𝒳] = ∂𝒳 ∪ N(∂𝒳)` and `I_{G∖W'}` is the weighted independence polynomial for
the couplings `H.coupling` (`weightedIndependencePolynomial`).  The only hypothesis is
`G.IsClawFree`.  See the module docstring for the encoding of the manuscript objects. -/
theorem generalizedCharacteristicPolynomial [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra R A] [IsScalarTower ℝ R A]
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) (hclaw : G.IsClawFree) (W : Set V)
    (u : R) :
    H.operator.restrictSome.transfer W u * H.operator.restrictSome.transfer W (-u) =
      ∑ X ∈ G.evenHoleFamilies W,
        ((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
          Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
            (W ∪ G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
          H.operator.restrictSome.familyOperator X := by
  classical
  rw [H.operator.restrictSome.transfer_mul_transfer_neg_eq_holeOnly hclaw W u]
  rw [← Finset.sum_fiberwise_of_maps_to (s := G.holeOnlyPairs W) (t := G.evenHoleFamilies W)
    (g := fun p => G.symmDiffHoleFamily p.1 p.2) (fun p hp => symmDiffHoleFamily_mem hp)]
  exact Finset.sum_congr rfl fun X hX => H.sum_holeOnlyPairs_fibre W hX u

/-- **v1 Lemma 11 itself** (`W = ∅`): for claw-free `G`,
`Z_G(-u²) = T_G(u) T_G(-u) =
   ∑_{𝒳 ∈ 𝒞^{(even)}_G} (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖Γ[𝒳]}(-u²) ∏_{C ∈ 𝒳} h_C`.
This is `generalizedCharacteristicPolynomial` with nothing deleted. -/
theorem generalizedCharacteristicPolynomial_empty [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra R A] [IsScalarTower ℝ R A]
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) (hclaw : G.IsClawFree) (u : R) :
    H.operator.restrictSome.transfer ∅ u * H.operator.restrictSome.transfer ∅ (-u) =
      ∑ X ∈ G.evenHoleFamilies ∅,
        ((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
          Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
            (G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
          H.operator.restrictSome.familyOperator X := by
  have h := H.generalizedCharacteristicPolynomial hclaw ∅ u
  simpa only [Set.empty_union] using h

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
