import FreeFermionGraphs.ObstructionSearchFiniteMixedPairing

/-!
# Final-selection branches for finite mixed-side executions

At initialization, a returned dependent vertex has two genuinely different
provenances.  An initial-tether stop may return the initializing source while
the output deformation is still empty.  A later Definition 20 stop selects
the returned vertex from a dependent set of an actual finite output block and
that vertex anticommutes with the block path.

This module keeps those branches separate.  It proves that two distinct
same-pairing searches cannot share a later-selected dependent vertex, and
therefore any shared returned dependent vertex must come from one initial
branch and one later branch.  No implication from an empty output to an empty
dependent set is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- The literal initial-tether provenance of a returned dependent vertex.
At initialization the current vertex is the source, and no path need have
been appended before the obstruction is found. -/
structure FiniteMixedSideInitialFinalSelection
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node) (u : V) : Prop where
  output_empty : (I.output source).run = none
  dependent_eq_source : u = (source : V)

/-- The literal later Definition 20 provenance of a returned dependent
vertex in an actual finite ordered block. -/
structure FiniteMixedSideLaterFinalSelection
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node) (u : V) : Prop where
  blockIndex : Fin (X.ordered source).blockCount
  stepIndex : Nat
  dependent :
    u ∈ ((X.ordered source).block blockIndex).dependentAt stepIndex
  anticommutes :
    ((X.ordered source).block blockIndex).path.AnticommutesWith u

/-- The two faithful final-selection branches of an initialized finite
mixed-side obstruction search. -/
inductive FiniteMixedSideFinalSelectionWitness
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node) (u : V) : Prop where
  | initialTether
      (selection : FiniteMixedSideInitialFinalSelection X source u)
  | laterDefinition20
      (selection : FiniteMixedSideLaterFinalSelection X source u)

/-- Literal finite executions together with the branch provenance of every
returned dependent vertex. -/
structure InitializationFiniteMixedSideFinalSelectionData
    (I : ObstructionSearchInitialization families Cprime)
    extends I.InitializationFiniteMixedSideOSExecutionData where
  finalSelection : ∀ (source : I.Node) (u : V),
    I.dependent source = some u →
      FiniteMixedSideFinalSelectionWitness
        toInitializationFiniteMixedSideOSExecutionData source u

namespace FiniteMixedSideInitialFinalSelection

/-- Two initial-tether selections of the same returned vertex have the same
source. -/
theorem source_eq
    {X : I.InitializationFiniteMixedSideOSExecutionData}
    {source source' : I.Node} {u : V}
    (A : FiniteMixedSideInitialFinalSelection X source u)
    (B : FiniteMixedSideInitialFinalSelection X source' u) :
    source = source' := by
  apply Subtype.ext
  calc
    (source : V) = u := A.dependent_eq_source.symm
    _ = (source' : V) := B.dependent_eq_source

end FiniteMixedSideInitialFinalSelection

namespace InitializationFiniteMixedSideOSExecutionData

/-- Two distinct same-pairing searches cannot select the same returned
vertex from later Definition 20 dependent sets.  Their selected blocks are
actual output paths, hence distinct by finite same-pairing path disjointness;
cross-context Corollary 11 excludes the shared dependent anticommuting
witness. -/
theorem noSharedLaterFinalSelection
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (hclaw : G.IsClawFree)
    {source source' : I.Node} {u : V}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source')
    (A : FiniteMixedSideLaterFinalSelection X source u)
    (B : FiniteMixedSideLaterFinalSelection X source' u) :
    False := by
  let Q := (X.ordered source).path A.blockIndex
  let R := (X.ordered source').path B.blockIndex
  have hQ : Q ∈ (I.output source).paths :=
    (X.ordered source).path_mem' A.blockIndex
  have hR : R ∈ (I.output source').paths :=
    (X.ordered source').path_mem' B.blockIndex
  have hpaths :
      Disjoint (I.output source).paths (I.output source').paths :=
    X.samePairing_paths_disjoint hclaw hne hpair
  have hQR : Q ≠ R := by
    intro hEq
    exact (Set.disjoint_left.mp hpaths) hQ (hEq ▸ hR)
  have hforbidden :=
    ConcretePathDeformation.FiniteMixedSideLemma11AContext.
      noSharedDependentAnticommutingWitness_of_pairing_eq
        (X.orderedContextAt source A.blockIndex)
        (X.orderedContextAt source' B.blockIndex)
        hpair hclaw (by
          simpa [Q, R, FiniteMixedSideOrderedOSExecution.path] using hQR)
  apply hforbidden
  exact ⟨u, A.stepIndex, B.stepIndex,
    A.dependent, B.dependent, A.anticommutes, B.anticommutes⟩

end InitializationFiniteMixedSideOSExecutionData

namespace InitializationFiniteMixedSideFinalSelectionData

/-- For distinct same-pairing searches, any shared returned dependent vertex
has exactly the unresolved mixed provenance: one initial-tether branch and
one later Definition 20 branch.  The initial-initial case forces equal
sources, and the later-later case is excluded by finite Corollary 11. -/
theorem sharedDependent_branch_split
    (X : I.InitializationFiniteMixedSideFinalSelectionData)
    (hclaw : G.IsClawFree)
    {source source' : I.Node} {u : V}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source')
    (hu : u ∈ I.dependentSet source)
    (hu' : u ∈ I.dependentSet source') :
    (FiniteMixedSideInitialFinalSelection
        X.toInitializationFiniteMixedSideOSExecutionData source u ∧
      FiniteMixedSideLaterFinalSelection
        X.toInitializationFiniteMixedSideOSExecutionData source' u) ∨
    (FiniteMixedSideLaterFinalSelection
        X.toInitializationFiniteMixedSideOSExecutionData source u ∧
      FiniteMixedSideInitialFinalSelection
        X.toInitializationFiniteMixedSideOSExecutionData source' u) := by
  let Y := X.toInitializationFiniteMixedSideOSExecutionData
  have hsource : I.dependent source = some u := hu
  have hsource' : I.dependent source' = some u := hu'
  have A := X.finalSelection source u hsource
  have B := X.finalSelection source' u hsource'
  cases A with
  | initialTether A0 =>
      cases B with
      | initialTether B0 =>
          exact (hne (A0.source_eq B0)).elim
      | laterDefinition20 B1 =>
          exact Or.inl ⟨A0, B1⟩
  | laterDefinition20 A1 =>
      cases B with
      | initialTether B0 =>
          exact Or.inr ⟨A1, B0⟩
      | laterDefinition20 B1 =>
          exact
            (Y.noSharedLaterFinalSelection
              hclaw hne hpair A1 B1).elim

end InitializationFiniteMixedSideFinalSelectionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
