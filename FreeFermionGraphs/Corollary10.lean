import FreeFermionGraphs.DependentSubsets

/-!
# Corollary 10

Vertices singled out by Definition 20 occur in at most one path component.
For a dependent vertex outside the active path, the single-deformation
geometry also supplies a common hole neighbor.  The coloring-class facts
established in the paper are exposed as exact-membership hypotheses, after
which all uniqueness conclusions follow uniformly from Lemma 10.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- At most one path component of `O` contains `v`. -/
def AtMostOneContainingPath (O : FixedPairingPathFamily G) (v : V) : Prop :=
  ∀ ⦃P Q : Set V⦄,
    P ∈ O.containingPaths v →
    Q ∈ O.containingPaths v →
    P = Q

/-- Lemma 10 in an unpointed, at-most-one form. -/
theorem atMostOneContainingPath_of_exactlyOne
    (O : FixedPairingPathFamily G) {v : V}
    (hv : ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd) :
    O.AtMostOneContainingPath v := by
  intro P Q hP hQ
  exact O.lemma10 hv hP.1 hP.2 hQ.1 hQ.2

/-- Corollary 10.  Every anticommuting vertex `w ∈ W` occurs in at most one
path.  A dependent external vertex `u` has a common hole neighbor `v`
with the introduced and removed vertices, and `u`, the introduced vertex,
and `v` each occur in at most one path.

Definition 19's coloring bookkeeping supplies `hWexact`, `huExact`,
`hintroducedExact`, and `hcommonExact` in the paper's application. -/
theorem corollary10
    (O : FixedPairingPathFamily G)
    (cycleCarrier primeCarrier : Set V)
    (anticommutes : V → Prop)
    (hWexact : ∀ ⦃w : V⦄,
      w ∈ anticommutingSubset cycleCarrier primeCarrier anticommutes →
        ExactlyOneOfFour w O.Ca O.Cb O.Cc O.Cd)
    {C : IndexedInducedHole G} {Cprime : Set V}
    {introduced u : V} {i : Fin C.card}
    (hdeform : C.SingleVertexDeformation introduced i)
    (hclaw : G.IsClawFree)
    (hu : u ∈ G.dependentSubset Cprime introduced (C.vertex i))
    (huOutside : u ∉ Set.insert introduced (Set.range C.vertex))
    (huExact : ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd)
    (hintroducedExact :
      ExactlyOneOfFour introduced O.Ca O.Cb O.Cc O.Cd)
    (hcommonExact : ∀ ⦃v : V⦄,
      v ∈ Set.range C.vertex →
      G.Adj u v →
      G.Adj introduced v →
      G.Adj (C.vertex i) v →
      ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd) :
    (∀ ⦃w : V⦄,
      w ∈ anticommutingSubset cycleCarrier primeCarrier anticommutes →
        O.AtMostOneContainingPath w) ∧
      ∃ v ∈ Set.range C.vertex,
        (G.Adj u v ∧
          G.Adj introduced v ∧
          G.Adj (C.vertex i) v) ∧
        O.AtMostOneContainingPath u ∧
        O.AtMostOneContainingPath introduced ∧
        O.AtMostOneContainingPath v := by
  refine ⟨?_, ?_⟩
  · intro w hw
    exact O.atMostOneContainingPath_of_exactlyOne (hWexact hw)
  · obtain ⟨v, hvC, huv, hintroducedv, hremovedv⟩ :=
      dependentSubset_has_common_hole_neighbor
        hdeform hclaw hu huOutside
    refine ⟨v, hvC, ⟨huv, hintroducedv, hremovedv⟩,
      O.atMostOneContainingPath_of_exactlyOne huExact,
      O.atMostOneContainingPath_of_exactlyOne hintroducedExact,
      O.atMostOneContainingPath_of_exactlyOne ?_⟩
    exact hcommonExact hvC huv hintroducedv hremovedv

end FixedPairingPathFamily

end SimpleGraph
