import FreeFermionGraphs.ObstructionSearchFiniteMixedOrderedContext

/-!
# Same-pairing path disjointness from finite mixed-side executions

The least-common-path theorem produces two distinct earlier literal blocks and
a shared dependent anticommuting witness.  Their ordered indices recover the
finite contexts of those blocks, and cross-trace Corollary 11 excludes the
witness.  Therefore two distinct initialized searches of one pairing type have
disjoint output-path collections.

This is the manuscript's Lemma 14(iii) path-disjointness argument on the
literal bounded execution data.  No path owner or disjointness certificate is
an input.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

namespace FiniteMixedSideLemma11AContext

/-- Eliminate equality of pairing indices before applying cross-trace finite
Corollary 11. -/
theorem noSharedDependentAnticommutingWitness_of_pairing_eq
    {families : PairingType → FixedPairingPathFamily G}
    {p q : PairingType}
    {Cprime : Set V}
    {D : ConcretePathDeformation (families p) Cprime}
    {E : ConcretePathDeformation (families q) Cprime}
    {originalHole : IndexedInducedHole G}
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

/-- Distinct initialized searches of the same pairing type have disjoint path
outputs, derived entirely from literal finite executions and Corollary 11. -/
theorem samePairing_paths_disjoint
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (hclaw : G.IsClawFree)
    {source source' : I.Node}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source') :
    Disjoint (I.output source).paths (I.output source').paths := by
  apply Set.disjoint_left.mpr
  intro P hP hP'
  obtain ⟨q, r, hpathNe, hshared⟩ :=
    X.firstCommonWitness hne hpair hP hP'
  have hpathNe' :
      Set.range ((X.ordered source).block q).path.vertex ≠
        Set.range ((X.ordered source').block r).path.vertex := by
    simpa [FiniteMixedSideOrderedOSExecution.path] using hpathNe
  exact
    (ConcretePathDeformation.FiniteMixedSideLemma11AContext.noSharedDependentAnticommutingWitness_of_pairing_eq
        (X.orderedContextAt source q)
        (X.orderedContextAt source' r)
        hpair hclaw hpathNe') hshared

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
