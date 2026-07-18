import FreeFermionGraphs.Lemma11BFinal

/-!
# Concrete fixed-pairing deformation sequences

The original `FixedPairingPathFamily` records the unordered path-component
geometry of Definition 19.  Lemma 11 also needs the ordered deformation
steps: the hole before each replacement, the introduced and removed
vertices, the active path, and Definition 20's dependent set.

This module supplies that missing concrete layer.  In particular, the
dependent set and the pre/post-deformation degree functions are definitions,
so the one-step degree increase used by Lemma 11 is now a theorem of the
sequence data rather than an external hypothesis.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- One concrete single-vertex step in a fixed-pairing deformation.

The active path membership fields link the ordered step back to the
component family from Definition 19. -/
structure ConcreteDeformationStep
    (O : FixedPairingPathFamily G) (Cprime : Set V) where
  before : IndexedInducedHole G
  introduced : V
  removedIndex : Fin before.card
  deformation :
    before.SingleVertexDeformation introduced removedIndex
  activePath : IndexedInducedPath G
  activePath_mem :
    Set.range activePath.vertex ∈ O.paths
  introduced_mem_activePath :
    introduced ∈ Set.range activePath.vertex
  removed_mem_activePath :
    before.vertex removedIndex ∈ Set.range activePath.vertex

namespace ConcreteDeformationStep

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The indexed hole after this deformation step. -/
def after (S : ConcreteDeformationStep O Cprime) :
    IndexedInducedHole G :=
  S.before.deform S.deformation

/-- Definition 20's dependent subset for this concrete step. -/
def dependentSet (S : ConcreteDeformationStep O Cprime) : Set V :=
  G.dependentSubset Cprime S.introduced
    (S.before.vertex S.removedIndex)

@[simp]
theorem mem_dependentSet
    (S : ConcreteDeformationStep O Cprime) {u : V} :
    u ∈ S.dependentSet ↔
      u ∈ Cprime ∧
        G.Adj u S.introduced ∧
        u ≠ S.before.vertex S.removedIndex ∧
        ¬G.Adj u (S.before.vertex S.removedIndex) :=
  Iff.rfl

/-- Degree in the hole immediately before the replacement. -/
noncomputable def degreeBefore
    (S : ConcreteDeformationStep O Cprime) (u : V) : Nat :=
  S.before.externalDegree u

/-- Degree in the hole immediately after the replacement. -/
noncomputable def degreeAfter
    (S : ConcreteDeformationStep O Cprime) (u : V) : Nat :=
  S.after.externalDegree u

/-- A member of the concrete dependent set gains exactly one hole neighbor
at this deformation step. -/
theorem degreeAfter_eq_add_one_of_mem_dependentSet
    (S : ConcreteDeformationStep O Cprime) {u : V}
    (hu : u ∈ S.dependentSet) :
    S.degreeAfter u = S.degreeBefore u + 1 := by
  change
    (S.before.deform S.deformation).externalDegree u =
      S.before.externalDegree u + 1
  exact S.deformation.dependent_externalDegree_deform_eq_add_one hu

end ConcreteDeformationStep

/-- A finite ordered fixed-pairing deformation.

Successive steps are required to agree on the carrier of the intermediate
hole.  Carrier equality is sufficient for the set-level deformation
statements used later, while each step retains an indexed hole for the local
Lemma 11 arguments. -/
structure ConcreteDeformation
    (O : FixedPairingPathFamily G) (Cprime : Set V) where
  stepCount : Nat
  step : Fin stepCount → ConcreteDeformationStep O Cprime
  carrier_chain :
    ∀ ⦃i j : Fin stepCount⦄,
      i.val + 1 = j.val →
      Set.range (step i).after.vertex =
        Set.range (step j).before.vertex

namespace ConcreteDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The active induced path at a concrete deformation step. -/
def activePath
    (D : ConcreteDeformation O Cprime) (i : Fin D.stepCount) :
    IndexedInducedPath G :=
  (D.step i).activePath

/-- The dependent subset at a concrete deformation step. -/
def dependentAt
    (D : ConcreteDeformation O Cprime) (i : Fin D.stepCount) :
    Set V :=
  (D.step i).dependentSet

/-- Pre-deformation degree at a concrete step. -/
noncomputable def degreeBeforeAt
    (D : ConcreteDeformation O Cprime)
    (i : Fin D.stepCount) (u : V) : Nat :=
  (D.step i).degreeBefore u

/-- Post-deformation degree at a concrete step. -/
noncomputable def degreeAfterAt
    (D : ConcreteDeformation O Cprime)
    (i : Fin D.stepCount) (u : V) : Nat :=
  (D.step i).degreeAfter u

theorem activePath_mem
    (D : ConcreteDeformation O Cprime) (i : Fin D.stepCount) :
    Set.range (D.activePath i).vertex ∈ O.paths :=
  (D.step i).activePath_mem

/-- Sequence-level form of the dependent degree increase in Lemma 11(a). -/
theorem degreeAfterAt_eq_add_one
    (D : ConcreteDeformation O Cprime)
    {i : Fin D.stepCount} {u : V}
    (hu : u ∈ D.dependentAt i) :
    D.degreeAfterAt i u = D.degreeBeforeAt i u + 1 := by
  change
    (D.step i).degreeAfter u =
      (D.step i).degreeBefore u + 1
  exact (D.step i).degreeAfter_eq_add_one_of_mem_dependentSet hu

end ConcreteDeformation

end FixedPairingPathFamily

end SimpleGraph
