import FreeFermionGraphs.Lemma11BTerminalContainment

/-!
# Lemma 11(b): overlap-aware active-path labels

Definition 19 labels each deformation step by an introduced prime-side
vertex and a removed original-side vertex on the active induced path.  The
original interface in this file excluded every other prime-carrier neighbor
of the introduced vertex.  That is too strong when the two holes overlap:
the immediately preceding removed vertex `k_(s-2)` may also lie in the prime
hole and hence in the next Definition 20 dependent set.

The corrected interface allows precisely that predecessor.  It still proves
that a first-step dependent vertex is outside the path, while later callers
split explicitly between the in-path overlap branch and the outside branch.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The overlap-aware local portion of Definition 19's alternating path
labeling at one deformation step.  Any prime-carrier path neighbor other
than the displayed removed vertex must immediately precede the introduced
vertex. -/
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
  prime_neighbor_precedes_introduced :
    ∀ q : Fin S.activePath.card,
      q ≠ removedPathIndex →
      G.Adj
        (S.activePath.vertex introducedPathIndex)
        (S.activePath.vertex q) →
      S.activePath.vertex q ∈ Cprime →
      q.val + 1 = introducedPathIndex.val

/-- A concrete dependent vertex cannot lie on the active path when the
introduced vertex is its first vertex.  This is the base-step consequence
needed by Lemma 11(b); later steps intentionally retain the overlap case. -/
theorem ConcreteDeformationStep.dependent_not_mem_activePath_of_introduced_first
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hlabel : StepPathLabeling S)
    (hfirst : hlabel.introducedPathIndex.val = 0)
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
  have hqPrime : S.activePath.vertex q ∈ Cprime := by
    rw [hqu]
    exact hmem.1
  have hprecedes :=
    hlabel.prime_neighbor_precedes_introduced
      q hqRemoved hadj hqPrime
  omega

/-- Pairing-side separation for the outside-path branch. -/
theorem ConcreteDeformationStep.dependent_pairingSideSeparated_of_outside
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACStepGeometry S)
    {u : V} (hu : u ∈ S.dependentSet)
    (huOutside : u ∉ Set.range S.activePath.vertex) :
    O.PairingSideSeparated u :=
  S.dependent_pairingSideSeparated
    hgeom hu huOutside

/-- Sequence-level base-step exclusion from the active path. -/
theorem ConcreteDeformation.baseDependent_not_mem_activePath
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (D : ConcreteDeformation O Cprime)
    (hlabel : ∀ i : Fin D.stepCount,
      StepPathLabeling (D.step i))
    (hfirst : ∀ i : Fin D.stepCount, i.val = 0 →
      (hlabel i).introducedPathIndex.val = 0)
    (i : Fin D.stepCount) (hi : i.val = 0) ⦃u : V⦄
    (hu : u ∈ D.dependentAt i) :
    u ∉ Set.range (D.activePath i).vertex :=
  (D.step i).dependent_not_mem_activePath_of_introduced_first
    (hlabel i) (hfirst i hi) hu

/-- Sequence-level pairing-side separation in the outside-path branch. -/
theorem ConcreteDeformation.dependent_pairingSideSeparated_of_outside
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
  exact D.dependent_pairingSideSeparated hgeom houtside

end FixedPairingPathFamily

end SimpleGraph
