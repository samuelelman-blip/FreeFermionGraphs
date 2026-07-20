import FreeFermionGraphs.Lemma11BOutsideDescent
import FreeFermionGraphs.Lemma11BOutsideCommonNeighborConfig

/-!
# Lemma 11(b): local Definition 19 outside recursion

The paper's remaining recursive argument is used only after the current
outside dependent vertex has been reduced to the consecutive-step
configuration. This module records that exact local target and derives the
former global outside-path rule from it.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The residual local recursion from the proof of Lemma 11(b).

It is required only for the concrete configuration produced from a
commuting outside dependent vertex and its immediately preceding step.
The conclusion gives the Definition 20 predecessor one or two steps back,
together with its common C_b neighbor. -/
def OutsideConsecutiveOneOrTwoStepRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    D.OutsideConsecutiveConfiguration s u →
    ∃ w : V,
      w ∈ O.Cb ∧
      G.Adj u w ∧
      ((∃ u' : V,
          D.Definition20DependentAt s u' ∧
            G.Adj u' w) ∨
        (∃ t : Nat, Nat.succ t = s ∧
          ∃ u' : V,
            D.Definition20DependentAt t u' ∧
              G.Adj u' w))

/-- The already-formalized Definition 19 mechanics reduce every
outside-path commuting dependent vertex to the local consecutive-step
recursion. -/
theorem outsidePathOneOrTwoStepCommonNeighborRule_of_consecutiveConfiguration
    {k : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hlocal : D.OutsideConsecutiveOneOrTwoStepRule) :
    D.OutsidePathOneOrTwoStepCommonNeighborRule := by
  intro s u hu huOutside hnotAnti
  exact hlocal
    (D.outsideConsecutiveConfiguration
      M A L hclaw horder hopposite
      (s := Nat.succ s) (u := u)
      hu huOutside hnotAnti)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
