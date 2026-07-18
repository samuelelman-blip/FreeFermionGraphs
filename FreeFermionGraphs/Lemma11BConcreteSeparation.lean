import FreeFermionGraphs.FixedPairingDeformation

/-!
# Lemma 11(b): concrete pairing-side separation

For an `(a,c)` deformation step, the introduced vertex lies in `C'꜀`
and the active path is a component of the `Cₐ ∪ C'꜀` side.  A dependent
vertex is adjacent to the introduced vertex.  Independence excludes it
from `C'꜀`; component coverage and its absence from the active path
exclude it from `Cₐ`.  It is therefore separated from the whole
`(a,c)` side.

This proves the path-uniqueness condition in the final Lemma 11(b) data
from concrete Definition 19/20 geometry.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Every edge between `C'꜀` and `Cₐ` is carried by an `acPaths`
component.  This is the edge-level consequence of those paths being the
connected components of the induced graph on `Cₐ ∪ C'꜀`. -/
def CoversACEdges (O : FixedPairingPathFamily G) : Prop :=
  ∀ ⦃x w : V⦄,
    x ∈ O.Cc →
    w ∈ O.Ca →
    G.Adj x w →
    ∃ P : Set V,
      P ∈ O.acPaths ∧ x ∈ P ∧ w ∈ P

/-- The Definition 19 coloring and component facts for one concrete
`(a,c)` deformation step. -/
structure ACStepGeometry
    {Cprime : Set V}
    (O : FixedPairingPathFamily G)
    (S : ConcreteDeformationStep O Cprime) : Prop where
  activePath_ac :
    Set.range S.activePath.vertex ∈ O.acPaths
  introduced_cc :
    S.introduced ∈ O.Cc
  cc_independent :
    IsIndependentClass G O.Cc
  edgeCoverage :
    O.CoversACEdges

/-- A dependent vertex cannot lie in the same independent prime class as
the introduced vertex to which it is adjacent. -/
theorem ConcreteDeformationStep.dependent_not_mem_cc
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACStepGeometry S)
    {u : V} (hu : u ∈ S.dependentSet) :
    u ∉ O.Cc := by
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet S).1 hu
  exact hgeom.cc_independent hmem.2.1 hgeom.introduced_cc

/-- A dependent vertex outside the active path cannot lie in `Cₐ`:
otherwise its edge to the introduced `C'꜀` vertex belongs to an
`acPaths` component, which must be the active component. -/
theorem ConcreteDeformationStep.dependent_not_mem_ca
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACStepGeometry S)
    {u : V} (hu : u ∈ S.dependentSet)
    (huOutside : u ∉ Set.range S.activePath.vertex) :
    u ∉ O.Ca := by
  intro huCa
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet S).1 hu
  obtain ⟨Q, hQ, hintroducedQ, huQ⟩ :=
    hgeom.edgeCoverage hgeom.introduced_cc huCa hmem.2.1.symm
  have hactiveQ :
      Set.range S.activePath.vertex = Q :=
    O.eq_of_mem_acPaths
      hgeom.activePath_ac hQ
      S.introduced_mem_activePath hintroducedQ
  apply huOutside
  rw [hactiveQ]
  exact huQ

/-- The pairing-side separation field of Lemma 11(b), discharged for a
concrete `(a,c)` deformation step. -/
theorem ConcreteDeformationStep.dependent_pairingSideSeparated
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACStepGeometry S)
    {u : V} (hu : u ∈ S.dependentSet)
    (huOutside : u ∉ Set.range S.activePath.vertex) :
    O.PairingSideSeparated u := by
  have huCa : u ∉ O.Ca :=
    S.dependent_not_mem_ca hgeom hu huOutside
  have huCc : u ∉ O.Cc :=
    S.dependent_not_mem_cc hgeom hu
  intro hboth
  exact hboth.1.elim huCa huCc

/-- Sequence-level discharge of pairing-side separation. -/
theorem ConcreteDeformation.dependent_pairingSideSeparated
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (D : ConcreteDeformation O Cprime)
    (hgeom : ∀ i : Fin D.stepCount,
      O.ACStepGeometry (D.step i))
    (houtside : ∀ (i : Fin D.stepCount) ⦃u : V⦄,
      u ∈ D.dependentAt i →
      u ∉ Set.range (D.activePath i).vertex) :
    ∀ (i : Fin D.stepCount) ⦃u : V⦄,
      u ∈ D.dependentAt i →
      O.PairingSideSeparated u := by
  intro i u hu
  have huStep : u ∈ (D.step i).dependentSet := by
    exact hu
  have huOutside :
      u ∉ Set.range (D.step i).activePath.vertex := by
    exact houtside i hu
  exact (D.step i).dependent_pairingSideSeparated
    (hgeom i) huStep huOutside

end FixedPairingPathFamily

end SimpleGraph
