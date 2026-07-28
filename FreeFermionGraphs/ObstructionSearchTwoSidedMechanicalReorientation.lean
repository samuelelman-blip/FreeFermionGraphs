import FreeFermionGraphs.ObstructionSearchTwoSidedReorientation

/-!
# Mechanical reorientation of Definition 19 blocks

Carrier-level reorientation preserves the actual path block, but the local
`ACHoleStepGeometry` field is orientation-sensitive.  A manuscript `bd` block
must therefore supply that geometry after exchanging the two colour pairs.

This module separates those two roles.  The path labels and outside-hole facts
transport automatically.  The only side-specific input is the local hole and
colour geometry for each reoriented step.  No obstruction-search side is chosen
here, and no execution, disjointness, or Lemma 14 conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace StepPathLabeling

/-- Definition 19 path indices and vertex equalities are unchanged by
carrier-level side reorientation. -/
def reorient
    {S : ConcreteDeformationStep O Cprime}
    (L : StepPathLabeling S)
    (side : DeformationSide) :
    StepPathLabeling (S.reorient side) := by
  cases side with
  | ac =>
      exact L
  | bd =>
      exact
        { introducedPathIndex := L.introducedPathIndex
          removedPathIndex := L.removedPathIndex
          introduced_eq := L.introduced_eq
          removed_eq := L.removed_eq
          prime_neighbor_precedes_introduced := by
            intro q hq hadj hprime
            exact L.prime_neighbor_precedes_introduced q hq hadj hprime }

end StepPathLabeling

namespace ConcretePathDeformation

/-- The genuinely orientation-sensitive local geometry of a concrete path
block.  For `.ac` this is the original `ACHoleStepGeometry`; for `.bd` it is the
same geometry in `O.swapSides` after carrier-level reorientation. -/
structure SideMechanicalGeometry
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) : Prop where
  stepGeometry :
    ∀ i : Fin D.deformation.stepCount,
      (side.family O).ACHoleStepGeometry
        ((D.deformation.step i).reorient side)

namespace MechanicalData

/-- Transport the orientation-insensitive fields of `MechanicalData` to the
selected manuscript side.  The caller supplies only the side-correct local
hole geometry. -/
def reorient
    {D : ConcretePathDeformation O Cprime}
    (M : D.MechanicalData)
    (side : DeformationSide)
    (H : D.SideMechanicalGeometry side) :
    (D.reorient side).MechanicalData := by
  cases side with
  | ac =>
      exact
        { stepGeometry := H.stepGeometry
          stepLabeling := M.stepLabeling
          outsideHole := M.outsideHole }
  | bd =>
      exact
        { stepGeometry := H.stepGeometry
          stepLabeling := fun i => (M.stepLabeling i).reorient .bd
          outsideHole := by
            intro i u hu
            exact M.outsideHole i hu }

end MechanicalData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
