import FreeFermionGraphs.ObstructionSearchTwoSidedCorollary11

/-!
# Two-sided first-common-path data

The manuscript proof of Lemma 14(iii) combines the ordered obstruction-search
trace with Corollary 11.  Once the least common path produces two distinct
earlier blocks and a shared dependent anticommuting vertex, the two-sided
Corollary 11 theorem excludes that witness.

This module introduces the side-correct first-common-path interface and derives
same-pairing path disjointness, canonical path ownership, and the generic
initialization geometry.  The finite least-common-path construction from
`TwoSidedOrderedOSExecution` remains the next step.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace TwoSidedSearchPathHistoryWitness

/-- Eliminate equality of pairing indices before applying the two-sided
history-backed Corollary 11 theorem. -/
theorem noSharedDependentAnticommutingWitness_of_pairing_eq
    {families : PairingType → FixedPairingPathFamily G}
    {p q : PairingType}
    {Cprime : Set V}
    {S : SearchDeformation (families p) Cprime}
    {T : SearchDeformation (families q) Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (B : TwoSidedSearchPathHistoryWitness T originalHole Q)
    (hpq : p = q)
    (hclaw : G.IsClawFree)
    (hne : P ≠ Q) :
    ¬SharedDependentAnticommutingWitness
      A.block.path B.block.path
      A.block.dependentAt B.block.dependentAt := by
  subst q
  exact A.noSharedDependentAnticommutingWitness B hclaw hne

end TwoSidedSearchPathHistoryWitness

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Side-correct data produced by the finite first-common-path trace in the
proof of Lemma 14(iii).

For every output path, `history` supplies the actual Definition 19 block, its
recorded component side, and its finite Lemma 11 history.  If two distinct
same-pairing searches contain a common path, `firstCommonWitness` supplies the
two distinct earlier blocks and the shared dependent anticommuting witness
obtained at the least common path.

The structure does not assume path disjointness or a path-owner function. -/
structure InitializationTwoSidedFirstCommonPathData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  history : ∀ source : I.Node,
    TwoSidedSearchHistoryData (I.output source) originalHole
  firstCommonWitness :
    ∀ ⦃source source' : I.Node⦄ ⦃P : Set V⦄,
      source ≠ source' →
      I.pairing source = I.pairing source' →
      P ∈ (I.output source).paths →
      P ∈ (I.output source').paths →
        ∃ (Q R : Set V)
          (hQ : Q ∈ (I.output source).paths)
          (hR : R ∈ (I.output source').paths),
          Q ≠ R ∧
            SharedDependentAnticommutingWitness
              (((history source).witness hQ).block.path)
              (((history source').witness hR).block.path)
              (((history source).witness hQ).block.dependentAt)
              (((history source').witness hR).block.dependentAt)

namespace InitializationTwoSidedFirstCommonPathData

/-- The first-common-path trace and two-sided Corollary 11 imply that distinct
searches of one pairing type have disjoint output-path collections. -/
theorem samePairing_paths_disjoint
    (X : I.InitializationTwoSidedFirstCommonPathData)
    (hclaw : G.IsClawFree)
    {source source' : I.Node}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source') :
    Disjoint (I.output source).paths (I.output source').paths := by
  apply Set.disjoint_left.mpr
  intro P hP hP'
  obtain ⟨Q, R, hQ, hR, hQR, hshared⟩ :=
    X.firstCommonWitness hne hpair hP hP'
  exact
    (TwoSidedSearchPathHistoryWitness.noSharedDependentAnticommutingWitness_of_pairing_eq
      ((X.history source).witness hQ)
      ((X.history source').witness hR)
      hpair hclaw hQR) hshared

/-- Choose the unique source of pairing type `p` whose output contains `P`,
when such a source exists. -/
noncomputable def pathOwner
    (_X : I.InitializationTwoSidedFirstCommonPathData)
    (p : PairingType) (P : Set V) : Option I.Node := by
  classical
  exact if h : ∃ source : I.Node,
      I.pairing source = p ∧ P ∈ (I.output source).paths then
    some (Classical.choose h)
  else
    none

/-- Every output path is assigned to its actual source by the canonical owner
function. -/
theorem path_owner_eq
    (X : I.InitializationTwoSidedFirstCommonPathData)
    (hclaw : G.IsClawFree)
    (source : I.Node) {P : Set V}
    (hP : P ∈ (I.output source).paths) :
    X.pathOwner (I.pairing source) P = some source := by
  classical
  unfold pathOwner
  split
  · rename_i hExists
    have hspec := Classical.choose_spec hExists
    have hchosen : Classical.choose hExists = source := by
      by_contra hne
      have hdisjoint := X.samePairing_paths_disjoint
        hclaw hne hspec.1
      exact (Set.disjoint_left.mp hdisjoint) hspec.2 hP
    exact congrArg some hchosen
  · rename_i hNone
    exact (hNone ⟨source, rfl, hP⟩).elim

/-- Construct the generic Lemma 14 geometry without assuming path ownership.
The owner and its correctness are derived from the side-correct first-common
trace. -/
noncomputable def toInitializationGeometry
    (X : I.InitializationTwoSidedFirstCommonPathData)
    (hclaw : G.IsClawFree)
    (noSelfLoop : ∀ source : I.Node,
      I.obstruction source ≠ some source)
    (obstructionOpposite : ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        I.pairing target = (I.pairing source).opposite)
    (incomingSlot : I.Node → I.Node → ObstructionSlot)
    (incomingSlot_injective :
      ∀ ⦃source source' target : I.Node⦄,
        I.graph.Arc source target →
        I.graph.Arc source' target →
        incomingSlot source target = incomingSlot source' target →
          source = source') :
    I.InitializationGeometry where
  noSelfLoop := noSelfLoop
  obstructionOpposite := obstructionOpposite
  pathOwner := X.pathOwner
  path_owner_eq := X.path_owner_eq hclaw
  incomingSlot := incomingSlot
  incomingSlot_injective := incomingSlot_injective

end InitializationTwoSidedFirstCommonPathData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
