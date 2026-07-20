import FreeFermionGraphs.Lemma11BOutsidePath

/-!
# Concrete deformation along one fixed-pairing path

Lemma 11 fixes one path `P⁽ʳ⁾` and considers all of its successive
single-vertex replacements.  This module groups those concrete steps into
one nonempty block with a common active path and supplies the natural
Nat-indexed dependent subsets used in the paper.

The mechanical Definition 19/20 geometry constructs every nonlocal field
of `Lemma11BNeighborhoodData`: pairing-side separation, terminal path
containment, exclusion from the active path where it is needed, and
component edge coverage.  The remaining obligations are exactly the
degree-four local case analysis and the strict predecessor construction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- A nonempty consecutive block of deformation steps sharing one active
induced path. -/
structure ConcretePathDeformation
    (O : FixedPairingPathFamily G) (Cprime : Set V) where
  deformation : ConcreteDeformation O Cprime
  nonempty : 0 < deformation.stepCount
  path : IndexedInducedPath G
  activePath_eq :
    ∀ i : Fin deformation.stepCount,
      (deformation.step i).activePath = path

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Index of the first replacement along the path. -/
def firstIndex (D : ConcretePathDeformation O Cprime) :
    Fin D.deformation.stepCount :=
  ⟨0, D.nonempty⟩

/-- Index of the final replacement along the path. -/
def lastIndex (D : ConcretePathDeformation O Cprime) :
    Fin D.deformation.stepCount :=
  ⟨D.deformation.stepCount - 1, by
    have hpos : 0 < D.deformation.stepCount := D.nonempty
    omega⟩

/-- Hole immediately before deforming along this path. -/
def initialHole (D : ConcretePathDeformation O Cprime) :
    IndexedInducedHole G :=
  (D.deformation.step D.firstIndex).before

/-- Hole after all replacements along this path. -/
def finalHole (D : ConcretePathDeformation O Cprime) :
    IndexedInducedHole G :=
  (D.deformation.step D.lastIndex).after

/-- Definition 20's dependent subset, extended by the empty set outside
the finite range of steps. -/
def dependentAt
    (D : ConcretePathDeformation O Cprime) (s : Nat) : Set V :=
  if hs : s < D.deformation.stepCount then
    (D.deformation.step ⟨s, hs⟩).dependentSet
  else
    ∅

/-- The degree `Δ_{C⁽ʳ⁾}(u)` in the final hole of this path
deformation.  It is independent of the internal step index `s`. -/
noncomputable def finalDegree
    (D : ConcretePathDeformation O Cprime) (_s : Nat) (u : V) : Nat :=
  D.finalHole.externalDegree u

theorem index_lt_of_mem_dependentAt
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V} (hu : u ∈ D.dependentAt s) :
    s < D.deformation.stepCount := by
  by_cases hs : s < D.deformation.stepCount
  · exact hs
  · simp [dependentAt, hs] at hu

theorem mem_step_dependentSet_of_mem_dependentAt
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V} (hu : u ∈ D.dependentAt s) :
    u ∈ (D.deformation.step
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependentSet := by
  have hs := D.index_lt_of_mem_dependentAt hu
  simpa [dependentAt, hs] using hu

/-- Mechanical data attached to a one-path deformation block.  This is
data-valued because the step labelings contain explicit path indices. -/
structure MechanicalData
    (D : ConcretePathDeformation O Cprime) where
  stepGeometry :
    ∀ i : Fin D.deformation.stepCount,
      O.ACHoleStepGeometry (D.deformation.step i)
  stepLabeling :
    ∀ i : Fin D.deformation.stepCount,
      StepPathLabeling (D.deformation.step i)
  outsideHole :
    ∀ (i : Fin D.deformation.stepCount) ⦃u : V⦄,
      u ∈ (D.deformation.step i).dependentSet →
      u ∉ Set.insert (D.deformation.step i).introduced
        (Set.range (D.deformation.step i).before.vertex)

namespace MechanicalData

variable {D : ConcretePathDeformation O Cprime}

/-- Pairing-side separation, derived from the concrete path labels and
component geometry. -/
theorem sideSeparated
    (M : D.MechanicalData) {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex) :
    O.PairingSideSeparated u := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep : u ∈ (D.deformation.step i).dependentSet := by
    exact D.mem_step_dependentSet_of_mem_dependentAt hu
  have huOutsideActive :
      u ∉ Set.range (D.deformation.step i).activePath.vertex := by
    rw [D.activePath_eq i]
    exact huOutside
  exact (D.deformation.step i).dependent_pairingSideSeparated_of_outside
    (M.stepGeometry i).base huStep huOutsideActive

/-- Terminal path containment, in fact proved for every dependent vertex
in the path block. -/
theorem contained
    (M : D.MechanicalData) (hclaw : G.IsClawFree)
    {s : Nat} {u : V} (hu : u ∈ D.dependentAt s) :
    ∃ Q : Set V, Q ∈ O.paths ∧ u ∈ Q := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep : u ∈ (D.deformation.step i).dependentSet := by
    exact D.mem_step_dependentSet_of_mem_dependentAt hu
  exact (D.deformation.step i).dependent_mem_path
    (M.stepGeometry i) hclaw huStep (M.outsideHole i huStep)

/-- The `(b,d)` component edge-coverage field, read from the first
nonempty step. -/
theorem edgeCoverage
    (M : D.MechanicalData) :
    O.CoversBDEdges :=
  (M.stepGeometry D.firstIndex).bdEdgeCoverage

/-- Construct the final Lemma 11(b) neighborhood package from concrete
Definition 19/20 data and the two genuinely local remaining rules. -/
def toLemma11BNeighborhoodData
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s → O.PairingSideSeparated u)
    (degree : Nat → V → Nat)
    (hdegreeFour : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
        degree s u = 4)
    (hpred :
      O.CommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith) :
    O.Lemma11BNeighborhoodData D.path D.dependentAt degree where
  sideSeparated := by
    intro s u hu
    exact hside hu
  terminalContained := by
    intro s u hu _
    exact M.contained hclaw hu
  degree_four := hdegreeFour
  edgeCoverage := M.edgeCoverage
  predecessor := hpred

end MechanicalData

/-- Lemma 11(b) for a concrete one-path deformation.  All bookkeeping
assumptions are now consequences; only the degree-four case analysis and
the common-neighbor predecessor rule remain. -/
theorem lemma11b_of_concretePathDeformation
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s → O.PairingSideSeparated u)
    (degree : Nat → V → Nat)
    (hdegreeFour : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
        degree s u = 4)
    (hpred :
      O.CommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  O.lemma11b D.path D.dependentAt degree
    (M.toLemma11BNeighborhoodData
      hclaw hside degree hdegreeFour hpred)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
