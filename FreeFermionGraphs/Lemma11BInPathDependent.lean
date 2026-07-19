import FreeFermionGraphs.Lemma11BStrictDefinition20Descent

/-!
# Lemma 11(b): dependent vertices on the active path

The general proof explicitly allows an old path vertex `k_(s-2)` to also
belong to the prime hole. Such a vertex can lie in the dependent set at the
next deformation step. The earlier `StepPathLabeling` interface excluded
this overlap entirely.

This module gives a paper-faithful relaxed labeling. A prime-carrier path
neighbor of the introduced vertex is allowed, but it must be the immediately
preceding path vertex. Consequently a dependent vertex lying on the active
path is exactly that predecessor. At the first step no predecessor exists,
so base dependent vertices are still automatically outside the path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Definition 19's local path labeling with the possible overlap vertex
`k_(s-2) ∈ C ∩ C'` retained. -/
structure StepPathOverlapLabeling
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

/-- A dependent vertex on the active path is the path vertex immediately
preceding the introduced vertex. -/
theorem ConcreteDeformationStep.dependent_path_vertex_precedes_introduced
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hlabel : StepPathOverlapLabeling S)
    {u : V}
    (hu : u ∈ S.dependentSet)
    (huPath : u ∈ Set.range S.activePath.vertex) :
    ∃ q : Fin S.activePath.card,
      S.activePath.vertex q = u ∧
      q.val + 1 = hlabel.introducedPathIndex.val := by
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
  exact ⟨q, hqu,
    hlabel.prime_neighbor_precedes_introduced
      q hqRemoved hadj hqPrime⟩

/-- The full ordered path labeling while retaining possible
cycle/prime-carrier overlaps. -/
structure Definition19OverlapPathOrder
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (D : ConcretePathDeformation O Cprime) where
  stepLabeling :
    ∀ i : Fin D.deformation.stepCount,
      StepPathOverlapLabeling (D.deformation.step i)
  introduced_index_val :
    ∀ i : Fin D.deformation.stepCount,
      (stepLabeling i).introducedPathIndex.val = 2 * i.val
  removed_index_val :
    ∀ i : Fin D.deformation.stepCount,
      (stepLabeling i).removedPathIndex.val = 2 * i.val + 1

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Although later dependent vertices may be path-overlap vertices, the
ordered labeling proves that no dependent vertex at the first step lies on
the active path. -/
theorem baseDependent_not_mem_path_of_overlapOrder
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19OverlapPathOrder D)
    {u : V}
    (hu : u ∈ D.dependentAt 0) :
    u ∉ Set.range D.path.vertex := by
  intro huPath
  let i : Fin D.deformation.stepCount := D.firstIndex
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [i, firstIndex] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huActive :
      u ∈ Set.range (D.deformation.step i).activePath.vertex := by
    rw [D.activePath_eq i]
    exact huPath
  obtain ⟨q, _hqu, hq⟩ :=
    (D.deformation.step i).dependent_path_vertex_precedes_introduced
      (L.stepLabeling i) huStep huActive
  have hzero :
      (L.stepLabeling i).introducedPathIndex.val = 0 := by
    simpa [i, firstIndex] using L.introduced_index_val i
  omega

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
