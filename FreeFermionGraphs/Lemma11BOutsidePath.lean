import FreeFermionGraphs.Lemma11BTerminalContainment

/-!
# Lemma 11(b): dependent vertices lie outside the active path

Definition 19 labels each deformation step by an introduced prime-side
vertex and a removed original-side vertex on the active induced path.
Every other path neighbor of the introduced vertex is also original-side
and hence lies outside the prime carrier.  Definition 20's dependent
vertices lie in the prime carrier, neighbor the introduced vertex, and are
not the removed vertex.

These facts force every dependent vertex to lie outside the active path,
discharging another field of `Lemma11BNeighborhoodData`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The local portion of Definition 19's alternating path labeling needed
at one deformation step. -/
structure StepPathLabeling
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime) where
  introducedPathIndex : Fin S.activePath.card
  removedPathIndex : Fin S.activePath.card
  introduced_eq :
    S.activePath.vertex introducedPathIndex = S.introduced
  removed_eq :
    S.activePath.vertex removedPathIndex =
      S.before.vertex S.removedIndex
  otherNeighbor_outsidePrime :
    ∀ q : Fin S.activePath.card,
      q ≠ removedPathIndex →
      G.Adj
        (S.activePath.vertex introducedPathIndex)
        (S.activePath.vertex q) →
      S.activePath.vertex q ∉ Cprime

/-- A concrete dependent vertex cannot be a vertex of its active path. -/
theorem ConcreteDeformationStep.dependent_not_mem_activePath
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hlabel : StepPathLabeling S)
    {u : V} (hu : u ∈ S.dependentSet) :
    u ∉ Set.range S.activePath.vertex := by
  intro huPath
  obtain ⟨q, hqu⟩ := huPath
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet S).1 hu
  have hqRemoved : q ≠ hlabel.removedPathIndex := by
    intro hq
    subst q
    apply hmem.2.2.1
    calc
      u = S.activePath.vertex hlabel.removedPathIndex :=
        hqu.symm
      _ = S.before.vertex S.removedIndex :=
        hlabel.removed_eq
  have hadj :
      G.Adj
        (S.activePath.vertex hlabel.introducedPathIndex)
        (S.activePath.vertex q) := by
    rw [hlabel.introduced_eq, hqu]
    exact hmem.2.1.symm
  have hqOutside :
      S.activePath.vertex q ∉ Cprime :=
    hlabel.otherNeighbor_outsidePrime q hqRemoved hadj
  apply hqOutside
  rw [hqu]
  exact hmem.1

/-- Pairing-side separation now follows from the concrete path labeling,
without an outside-path hypothesis supplied by the caller. -/
theorem ConcreteDeformationStep.dependent_pairingSideSeparated_of_labeling
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACStepGeometry S)
    (hlabel : StepPathLabeling S)
    {u : V} (hu : u ∈ S.dependentSet) :
    O.PairingSideSeparated u :=
  S.dependent_pairingSideSeparated
    hgeom hu (S.dependent_not_mem_activePath hlabel hu)

/-- Sequence-level discharge of the outside-active-path condition. -/
theorem ConcreteDeformation.dependent_not_mem_activePath
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (D : ConcreteDeformation O Cprime)
    (hlabel : ∀ i : Fin D.stepCount,
      StepPathLabeling (D.step i)) :
    ∀ (i : Fin D.stepCount) ⦃u : V⦄,
      u ∈ D.dependentAt i →
      u ∉ Set.range (D.activePath i).vertex := by
  intro i u hu
  exact (D.step i).dependent_not_mem_activePath
    (hlabel i) hu

/-- Sequence-level pairing-side separation with the outside-path argument
fully discharged by Definition 19's labeling. -/
theorem ConcreteDeformation.dependent_pairingSideSeparated_of_labeling
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (D : ConcreteDeformation O Cprime)
    (hgeom : ∀ i : Fin D.stepCount,
      O.ACStepGeometry (D.step i))
    (hlabel : ∀ i : Fin D.stepCount,
      StepPathLabeling (D.step i)) :
    ∀ (i : Fin D.stepCount) ⦃u : V⦄,
      u ∈ D.dependentAt i →
      O.PairingSideSeparated u := by
  exact D.dependent_pairingSideSeparated hgeom
    (D.dependent_not_mem_activePath hlabel)

end FixedPairingPathFamily

end SimpleGraph
