import FreeFermionGraphs.ObstructionSearchTwoSidedCanonicalEntry

/-!
# Carrier-level reorientation of Definition 19 blocks

A manuscript `bd` block is analysed by exchanging the two original-hole
colours, the two prime-hole colours, and the two path-component families.  The
underlying holes, vertices, deformations, and indexed path do not change.

This module transports the carrier-level concrete deformation objects to the
family selected by a `DeformationSide`.  It deliberately does not transport
`MechanicalData` or choose the correct side of a block.  Those orientation-
sensitive facts must be supplied by the literal `OS` construction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcreteDeformationStep

/-- Reinterpret one concrete replacement in the family selected by `side`.
Only the family-level path-membership proof changes. -/
def reorient
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    ConcreteDeformationStep (side.family O) Cprime := by
  cases side with
  | ac =>
      exact S
  | bd =>
      exact
        { before := S.before
          introduced := S.introduced
          removedIndex := S.removedIndex
          deformation := S.deformation
          activePath := S.activePath
          activePath_mem := by
            simpa using S.activePath_mem
          introduced_mem_activePath := S.introduced_mem_activePath
          removed_mem_activePath := S.removed_mem_activePath }

@[simp] theorem reorient_before
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    (S.reorient side).before = S.before := by
  cases side <;> rfl

@[simp] theorem reorient_introduced
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    (S.reorient side).introduced = S.introduced := by
  cases side <;> rfl

/-- Reorientation preserves the actual removed vertex.  The raw removal indices
live in definitionally equal but syntactically different `Fin` types, so the
carrier vertex is the invariant relevant to the manuscript. -/
@[simp] theorem reorient_removedVertex
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    (S.reorient side).before.vertex (S.reorient side).removedIndex =
      S.before.vertex S.removedIndex := by
  cases side <;> rfl

@[simp] theorem reorient_activePath
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    (S.reorient side).activePath = S.activePath := by
  cases side <;> rfl

@[simp] theorem reorient_after
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    (S.reorient side).after = S.after := by
  cases side <;> rfl

@[simp] theorem reorient_dependentSet
    (S : ConcreteDeformationStep O Cprime)
    (side : DeformationSide) :
    (S.reorient side).dependentSet = S.dependentSet := by
  cases side <;> rfl

end ConcreteDeformationStep

namespace ConcreteDeformation

/-- Reinterpret every step of a concrete deformation in the selected family. -/
def reorient
    (D : ConcreteDeformation O Cprime)
    (side : DeformationSide) :
    ConcreteDeformation (side.family O) Cprime where
  stepCount := D.stepCount
  step i := (D.step i).reorient side
  carrier_chain := by
    intro i j hij
    cases side with
    | ac => exact D.carrier_chain hij
    | bd => exact D.carrier_chain hij

@[simp] theorem reorient_stepCount
    (D : ConcreteDeformation O Cprime)
    (side : DeformationSide) :
    (D.reorient side).stepCount = D.stepCount := rfl

@[simp] theorem reorient_step
    (D : ConcreteDeformation O Cprime)
    (side : DeformationSide)
    (i : Fin D.stepCount) :
    (D.reorient side).step i = (D.step i).reorient side := rfl

end ConcreteDeformation

namespace ConcretePathDeformation

/-- Carrier-level reorientation of one complete Definition 19 path block. -/
def reorient
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    ConcretePathDeformation (side.family O) Cprime where
  deformation := D.deformation.reorient side
  nonempty := D.nonempty
  path := D.path
  activePath_eq := by
    intro i
    simpa using D.activePath_eq i

@[simp] theorem reorient_path
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    (D.reorient side).path = D.path := rfl

@[simp] theorem reorient_path_range
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    Set.range (D.reorient side).path.vertex =
      Set.range D.path.vertex := rfl

@[simp] theorem reorient_stepCount
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    (D.reorient side).deformation.stepCount =
      D.deformation.stepCount := rfl

/-- Reorientation preserves the initial hole carrier of a path block. -/
@[simp] theorem reorient_initialHole
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    (D.reorient side).initialHole = D.initialHole := by
  cases side <;> rfl

/-- Reorientation preserves the initial-hole vertex set without exposing the
dependent `Fin` index type. -/
@[simp] theorem reorient_initialHole_range
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    Set.range (D.reorient side).initialHole.vertex =
      Set.range D.initialHole.vertex := by
  cases side <;> rfl

/-- Reorientation preserves the final hole carrier of a path block. -/
@[simp] theorem reorient_finalHole
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    (D.reorient side).finalHole = D.finalHole := by
  cases side <;> rfl

/-- Reorientation preserves the final-hole vertex set without exposing the
dependent `Fin` index type. -/
@[simp] theorem reorient_finalHole_range
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    Set.range (D.reorient side).finalHole.vertex =
      Set.range D.finalHole.vertex := by
  cases side <;> rfl

/-- Reorientation preserves the introduced vertex at every concrete step. -/
@[simp] theorem reorient_step_introduced
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (i : Fin D.deformation.stepCount) :
    ((D.reorient side).deformation.step i).introduced =
      (D.deformation.step i).introduced := by
  cases side <;> rfl

/-- Reorientation preserves every Nat-indexed Definition 20 dependent set. -/
theorem reorient_dependentAt
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (s : Nat) :
    (D.reorient side).dependentAt s = D.dependentAt s := by
  cases side <;> rfl

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph