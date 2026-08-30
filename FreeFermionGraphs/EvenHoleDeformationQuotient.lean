import FreeFermionGraphs.GeneralizedCycleSymmetry

/-!
# Quotient classes of even-hole deformations

The manuscript label `⟨C₀⟩` is an equivalence class, not a distinguished
carrier set.  This module forms that quotient explicitly and factors the
generalized-cycle sum through it.  Any eigenvalue indexed by this quotient is
therefore representative-independent by construction.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- The finite-deformation closure relation as a setoid on carrier sets. -/
def evenHoleDeformationSetoid (G : SimpleGraph V) : Setoid (Set V) where
  r := InEvenHoleDeformationClosure G
  iseqv :=
    { refl := InEvenHoleDeformationClosure.refl
      symm := InEvenHoleDeformationClosure.symm
      trans := InEvenHoleDeformationClosure.trans }

/-- The manuscript deformation-class label `⟨C₀⟩`. -/
abbrev EvenHoleDeformationClass (G : SimpleGraph V) :=
  Quotient (evenHoleDeformationSetoid G)

/-- Send one concrete carrier to its even-hole deformation class. -/
def evenHoleDeformationClassOf (G : SimpleGraph V) (C : Set V) :
    EvenHoleDeformationClass G :=
  Quotient.mk (evenHoleDeformationSetoid G) C

/-- Two concrete carriers name the same quotient class exactly when a finite
Definition 10 deformation sequence relates them. -/
theorem evenHoleDeformationClassOf_eq_iff
    {G : SimpleGraph V} {C D : Set V} :
    G.evenHoleDeformationClassOf C = G.evenHoleDeformationClassOf D ↔
      InEvenHoleDeformationClosure G C D := by
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound _ (evenHoleDeformationSetoid G) C D h

/-- A single even-hole deformation step does not change the quotient label. -/
theorem evenHoleDeformationClassOf_eq_of_step
    {G : SimpleGraph V} {C D : Set V}
    (h : EvenHoleDeformationStep G C D) :
    G.evenHoleDeformationClassOf C = G.evenHoleDeformationClassOf D :=
  Quotient.sound h.inClosure

/-- Definition 15 as a function of the actual quotient class rather than an
arbitrary representative carrier. -/
noncomputable def generalizedCycleSymmetryOnClass
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    {A : Type w} [AddCommMonoid A]
    (weight : Set V → A) : EvenHoleDeformationClass G → A :=
  Quotient.lift
    (fun C => G.generalizedCycleSymmetry C weight)
    (fun _C _D h => generalizedCycleSymmetry_eq_of_mem weight h)

@[simp]
theorem generalizedCycleSymmetryOnClass_mk
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    {A : Type w} [AddCommMonoid A]
    (weight : Set V → A) (C : Set V) :
    G.generalizedCycleSymmetryOnClass weight
        (G.evenHoleDeformationClassOf C) =
      G.generalizedCycleSymmetry C weight :=
  rfl

end SimpleGraph
