import FreeFermionGraphs.ObstructionSearchFiniteMixedFirstCommon
import FreeFermionGraphs.ObstructionSearchFiniteMixedOrderedContext

/-!
# Same-pairing disjointness for literal finite mixed-side executions

The finite least-common-path theorem produces two distinct earlier literal
blocks and a shared dependent anticommuting witness.  The cross-context
Corollary 11 theorem excludes that witness after recovering the exact
zero-or-positive bounded context of each block.

This yields the manuscript's same-pairing path-disjointness conclusion directly
from the inductively generated finite `OS` executions.  No total `Nat` history,
path ownership, or Lemma 14 conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

namespace FiniteMixedSideLemma11AContext

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}
  {p q : PairingType}
  {D : ConcretePathDeformation (families p) Cprime}
  {E : ConcretePathDeformation (families q) Cprime}
  {originalHole : IndexedInducedHole G}

/-- Eliminate equality of pairing indices before applying the finite
cross-context Corollary 11 theorem. -/
theorem noSharedDependentAnticommutingWitness_of_pairing_eq
    (A : FiniteMixedSideLemma11AContext D originalHole)
    (B : FiniteMixedSideLemma11AContext E originalHole)
    (hpq : p = q)
    (hclaw : G.IsClawFree)
    (hpathNe :
      Set.range D.path.vertex ≠ Set.range E.path.vertex) :
    ¬SharedDependentAnticommutingWitness
      D.path E.path D.dependentAt E.dependentAt := by
  subst q
  exact A.noSharedDependentAnticommutingWitness B hclaw hpathNe

end FiniteMixedSideLemma11AContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationFiniteMixedSideOSExecutionData

/-- Distinct initialized searches of the same pairing type have disjoint
output-path collections. -/
theorem samePairing_paths_disjoint
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (hclaw : G.IsClawFree)
    {source source' : I.Node}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source') :
    Disjoint (I.output source).paths (I.output source').paths := by
  apply Set.disjoint_left.mpr
  intro P hP hP'
  obtain ⟨q, r, hqr, hshared⟩ :=
    X.firstCommonWitness hne hpair hP hP'
  have hpathNe :
      Set.range ((X.ordered source).block q).path.vertex ≠
        Set.range ((X.ordered source').block r).path.vertex := by
    simpa [FiniteMixedSideOrderedOSExecution.path] using hqr
  exact
    (ConcretePathDeformation.FiniteMixedSideLemma11AContext.noSharedDependentAnticommutingWitness_of_pairing_eq
      (X.orderedContextAt source q) (X.orderedContextAt source' r)
      hpair hclaw hpathNe) hshared

/-- Choose the unique source of pairing type `p` whose finite output contains
`P`, when such a source exists. -/
noncomputable def pathOwner
    (_X : I.InitializationFiniteMixedSideOSExecutionData)
    (p : PairingType) (P : Set V) : Option I.Node := by
  classical
  exact if h : ∃ source : I.Node,
      I.pairing source = p ∧ P ∈ (I.output source).paths then
    some (Classical.choose h)
  else
    none

/-- Every finite output path is assigned to its actual initialized source by
the canonical owner function. -/
theorem path_owner_eq
    (X : I.InitializationFiniteMixedSideOSExecutionData)
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

/-- Construct the generic Lemma 14 initialization geometry from the literal
finite executions, deriving path ownership rather than accepting it as a
field. -/
noncomputable def toInitializationGeometry
    (X : I.InitializationFiniteMixedSideOSExecutionData)
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

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
