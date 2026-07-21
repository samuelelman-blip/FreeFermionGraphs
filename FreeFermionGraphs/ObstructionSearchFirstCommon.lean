import FreeFermionGraphs.ObstructionSearchHistory

/-!
# First-common-path ownership in the obstruction search

Suppose two initialized searches of the same pairing type contain a common
path.  The manuscript chooses the first such path.  Unless one of its first
introduced vertices is an initializing source of the wrong pairing type, the
preceding portions of the two searches contain distinct path blocks with one
shared dependent anticommuting witness.  The history form of Corollary 11
excludes that configuration.

This module records the output of that finite first-common-path trace, derives
pairwise path disjointness, and constructs a canonical path owner.  Thus the
owner used in Lemma 14(iii) is no longer primitive initialization data.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace SearchPathHistoryWitness

/-- Corollary 11 for two concrete history witnesses whose fixed-pairing
families are indexed by equal pairing types.  Equality is eliminated here so
the first-common-path argument does not have to perform dependent casts. -/
theorem noSharedDependentAnticommutingWitness_of_pairing_eq
    {families : PairingType → FixedPairingPathFamily G}
    {p q : PairingType}
    {Cprime : Set V}
    {S : SearchDeformation (families p) Cprime}
    {T : SearchDeformation (families q) Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : SearchPathHistoryWitness S originalHole P)
    (B : SearchPathHistoryWitness T originalHole Q)
    (hpq : p = q)
    (hclaw : G.IsClawFree)
    (hne : P ≠ Q) :
    ¬SharedDependentAnticommutingWitness
      A.block.path B.block.path
      A.block.dependentAt B.block.dependentAt := by
  subst q
  exact A.noSharedDependentAnticommutingWitness B hclaw hne

end SearchPathHistoryWitness

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Concrete data produced by the first-common-path trace in the proof of
Lemma 14(iii).

For every output path, `history` supplies the actual Definition 19 block and
its Lemma 11 history.  If two distinct same-pairing searches contain a common
path, `firstCommonWitness` supplies the two distinct earlier blocks and the
shared dependent anticommuting witness obtained at the first common path.
It does not assume path disjointness or an owner function. -/
structure InitializationFirstCommonPathData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  history : ∀ source : I.Node,
    SearchHistoryData (I.output source) originalHole
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

namespace InitializationFirstCommonPathData

/-- The first-common-path trace and Corollary 11 imply that distinct searches
of one pairing type have disjoint output-path collections. -/
theorem samePairing_paths_disjoint
    (X : I.InitializationFirstCommonPathData)
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
    (SearchPathHistoryWitness.noSharedDependentAnticommutingWitness_of_pairing_eq
        ((X.history source).witness hQ)
        ((X.history source').witness hR)
        hpair hclaw hQR) hshared

/-- Choose the unique source of pairing type `p` whose output contains `P`,
when such a source exists.  Uniqueness is proved below from the
first-common-path theorem. -/
noncomputable def pathOwner
    (_X : I.InitializationFirstCommonPathData)
    (p : PairingType) (P : Set V) : Option I.Node := by
  classical
  exact if h : ∃ source : I.Node,
      I.pairing source = p ∧ P ∈ (I.output source).paths then
    some (Classical.choose h)
  else
    none

/-- Every output path is assigned to its actual source by the canonical
owner function. -/
theorem path_owner_eq
    (X : I.InitializationFirstCommonPathData)
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

/-- Construct the generic Lemma 14 geometry without assuming a path owner.
The owner and its correctness are derived from the first-common-path trace. -/
noncomputable def toInitializationGeometry
    (X : I.InitializationFirstCommonPathData)
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

end InitializationFirstCommonPathData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
