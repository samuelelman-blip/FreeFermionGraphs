import FreeFermionGraphs.DeformationTokenSliding

/-!
# Token-sliding charges

The combinatorial content of Definition 14 and equation (A6).  The operator
`h_S` is represented by an arbitrary additive weight on token configurations;
the component decomposition is therefore independent of the eventual
operator-algebra realization.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- The unrestricted `k`-independent-set sum, corresponding to `Q_G^(k)`. -/
noncomputable def independentSetCharge (G : SimpleGraph V) (k : Nat)
    [Fintype V] [DecidableEq V] {A : Type w} [AddCommMonoid A]
    (weight : TokenConfiguration G k → A) : A := by
  classical
  exact ∑ S : TokenConfiguration G k, weight S

/-- Definition 14, in generic additive form: sum the configuration weights
over a single connected component `μ ∈ Ξₖ`. -/
noncomputable def tokenSlidingCharge (G : SimpleGraph V) (k : Nat)
    [Fintype V] [DecidableEq V] {A : Type w} [AddCommMonoid A]
    (weight : TokenConfiguration G k → A)
    (μ : TokenSlidingComponent G k) : A := by
  classical
  exact ∑ S : TokenConfiguration G k,
    if G.tokenSlidingComponentMk k S = μ then weight S else 0

/-- A component charge depends only on weights from that component. -/
theorem tokenSlidingCharge_congr (G : SimpleGraph V) (k : Nat)
    [Fintype V] [DecidableEq V] {A : Type w} [AddCommMonoid A]
    {weight weight' : TokenConfiguration G k → A}
    (μ : TokenSlidingComponent G k)
    (h : ∀ S, G.tokenSlidingComponentMk k S = μ →
      weight S = weight' S) :
    G.tokenSlidingCharge k weight μ =
      G.tokenSlidingCharge k weight' μ := by
  classical
  unfold tokenSlidingCharge
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : G.tokenSlidingComponentMk k S = μ
  · simp [hS, h S hS]
  · simp [hS]

/-- Equation (A6): the unrestricted independent-set charge is the sum of the
token-sliding charges over all connected components. -/
theorem sum_tokenSlidingCharge_eq_independentSetCharge
    (G : SimpleGraph V) (k : Nat)
    [Fintype V] [DecidableEq V] {A : Type w} [AddCommMonoid A]
    (weight : TokenConfiguration G k → A) :
    (∑ μ : TokenSlidingComponent G k,
      G.tokenSlidingCharge k weight μ) =
      G.independentSetCharge k weight := by
  classical
  letI : Fintype (TokenSlidingComponent G k) :=
    Fintype.ofFinite (TokenSlidingComponent G k)
  simp [tokenSlidingCharge, independentSetCharge, Finset.sum_comm]

end SimpleGraph
