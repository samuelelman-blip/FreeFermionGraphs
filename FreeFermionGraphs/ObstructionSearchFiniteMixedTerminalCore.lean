import FreeFermionGraphs.ObstructionSearchFiniteMixedFinalSelection
import FreeFermionGraphs.ObstructionSearchNearest
import FreeFermionGraphs.ObstructionSearchTerminalSameClone

/-!
# Terminal core from finite mixed-side obstruction-search executions

The literal finite execution now supplies path disjointness, pairing labels,
and the two final-selection branches.  This module combines those facts with
the nearest-target rule and terminal endpoint data.

The only apparent gap in final-dependent disjointness is the mixed case in
which one search stops at its initial tether and the other stops after a
Definition 20 selection.  Equal terminal slots rule out that case: the first
source would be the endpoint occupied by the second search, hence the nearest
allowed target of the second search.  The common target would then equal the
first source, making the first incoming arc a self-loop.

Thus terminal-slot injectivity and the generic Lemma 14 initialization
geometry are derived from literal finite data, without the legacy total
`Nat`-indexed execution trace.  The same-clone branch of the two-incoming
terminal argument is then discharged on this finite core.
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

namespace InitializationNearestTargetData

variable
  {terminalPath : I.Node → IndexedInducedPath G}
  {currentSlot : I.Node → I.Node → ObstructionSlot}

/-- If the terminal endpoint occupied by an incoming search is itself an
allowed obstruction vertex, then it is necessarily the selected nearest
target. -/
theorem target_eq_obstructionEndpoint_of_endpoint_mem_allowed
    (N : I.InitializationNearestTargetData terminalPath currentSlot)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hEndpoint :
      (terminalPath target).obstructionEndpoint
          (currentSlot source target) ∈
        I.allowedVertices source) :
    (target : V) =
      (terminalPath target).obstructionEndpoint
        (currentSlot source target) := by
  let P := terminalPath target
  let e := P.obstructionEndpointIndex (currentSlot source target)
  obtain ⟨q, htarget, hnearest⟩ := N.obstruction_nearest incoming
  have heNearest :
      P.IsNearestFrom (currentSlot source target)
        (I.allowedVertices source) e := by
    refine ⟨?_, ?_⟩
    · simpa [P, e, IndexedInducedPath.obstructionEndpoint] using hEndpoint
    · intro j _hj
      cases hslot : currentSlot source target <;>
        simp [e, IndexedInducedPath.obstructionEndpointIndex, hslot] <;>
        omega
  have hq : q = e :=
    P.nearestFrom_unique
      (currentSlot source target) (I.allowedVertices source)
      hnearest heNearest
  calc
    (target : V) = P.vertex q := htarget.symm
    _ = P.vertex e := by rw [hq]
    _ = P.obstructionEndpoint (currentSlot source target) := by
      rfl

end InitializationNearestTargetData

/-- Finite mixed-side data through the terminal endpoint stage of the
initialized obstruction search. -/
structure InitializationFiniteMixedSideTerminalCoreData
    (I : ObstructionSearchInitialization families Cprime) where
  execution : I.InitializationFiniteMixedSideFinalSelectionData
  pairingLabels :
    I.InitializationFiniteMixedSidePairingLabelData
      execution.toInitializationFiniteMixedSideOSExecutionData
  stoppingPairing :
    I.InitializationFiniteMixedSideStoppingPairingData
      execution.toInitializationFiniteMixedSideOSExecutionData
  terminalPath : I.Node → IndexedInducedPath G
  currentSlot : I.Node → I.Node → ObstructionSlot
  nearestTarget :
    I.InitializationNearestTargetData terminalPath currentSlot
  dependent_is_current_endpoint :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        I.dependent source = some
          ((terminalPath target).obstructionEndpoint
            (currentSlot source target))

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Every finite obstruction arc crosses pairing types. -/
theorem obstructionOpposite
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target) :
    I.pairing target = (I.pairing source).opposite :=
  T.pairingLabels.obstructionOpposite
    T.stoppingPairing hclaw incoming

/-- Two incoming finite searches cannot occupy the same terminal endpoint.
Later/later equality is excluded by finite Corollary 11, initial/initial
equality forces equal sources, and each mixed case would force a self-loop by
the nearest-target rule. -/
theorem currentSlot_source_injective
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    ⦃source source' target : I.Node⦄
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target)
    (hslot : T.currentSlot source target =
      T.currentSlot source' target) :
    source = source' := by
  by_contra hne
  have hopposite :
      (I.pairing source).opposite =
        (I.pairing source').opposite :=
    (T.obstructionOpposite hclaw incoming).symm.trans
      (T.obstructionOpposite hclaw incoming')
  have hpair : I.pairing source = I.pairing source' := by
    have h := congrArg PairingType.opposite hopposite
    simpa using h
  let P := T.terminalPath target
  let u := P.obstructionEndpoint (T.currentSlot source target)
  have hu : u ∈ I.dependentSet source := by
    change I.dependent source = some u
    exact T.dependent_is_current_endpoint incoming
  have hu' : u ∈ I.dependentSet source' := by
    change I.dependent source' = some u
    calc
      I.dependent source' =
          some (P.obstructionEndpoint
            (T.currentSlot source' target)) :=
        T.dependent_is_current_endpoint incoming'
      _ = some u := by rw [← hslot]
  rcases T.execution.sharedDependent_branch_split
      hclaw hne hpair hu hu' with hmix | hmix
  · rcases hmix with ⟨hInitial, _hLater⟩
    have hEndpointEq :
        P.obstructionEndpoint (T.currentSlot source' target) =
          (source : V) := by
      calc
        P.obstructionEndpoint (T.currentSlot source' target) = u := by
          rw [← hslot]
        _ = (source : V) := hInitial.dependent_eq_source
    have hEndpointAllowed :
        P.obstructionEndpoint (T.currentSlot source' target) ∈
          I.allowedVertices source' := by
      rw [hEndpointEq]
      refine ⟨source.property, ?_⟩
      intro hvalue
      exact hne (Subtype.ext hvalue)
    have htargetEndpoint :=
      T.nearestTarget.target_eq_obstructionEndpoint_of_endpoint_mem_allowed
        incoming' hEndpointAllowed
    have htargetSource : target = source := by
      apply Subtype.ext
      exact htargetEndpoint.trans hEndpointEq
    apply T.nearestTarget.noSelfLoop source
    simpa [htargetSource] using incoming
  · rcases hmix with ⟨_hLater, hInitial⟩
    have hEndpointEq :
        P.obstructionEndpoint (T.currentSlot source target) =
          (source' : V) :=
      hInitial.dependent_eq_source
    have hEndpointAllowed :
        P.obstructionEndpoint (T.currentSlot source target) ∈
          I.allowedVertices source := by
      rw [hEndpointEq]
      refine ⟨source'.property, ?_⟩
      intro hvalue
      exact hne (Subtype.ext hvalue.symm)
    have htargetEndpoint :=
      T.nearestTarget.target_eq_obstructionEndpoint_of_endpoint_mem_allowed
        incoming hEndpointAllowed
    have htargetSource' : target = source' := by
      apply Subtype.ext
      exact htargetEndpoint.trans hEndpointEq
    apply T.nearestTarget.noSelfLoop source'
    simpa [htargetSource'] using incoming'

/-- The finite terminal core constructs the generic initialization geometry
used for Lemma 14(i)--(iii) and the indegree-two part of (iv). -/
noncomputable def toInitializationGeometry
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree) :
    I.InitializationGeometry :=
  T.execution.toInitializationFiniteMixedSideOSExecutionData.toInitializationGeometry
    hclaw
    T.nearestTarget.noSelfLoop
    (T.obstructionOpposite hclaw)
    T.currentSlot
    (T.currentSlot_source_injective hclaw)

end InitializationFiniteMixedSideTerminalCoreData

/-- The concrete equal-clone branch for two finite mixed-side searches
entering one target.  The field supplies the alternating terminal
neighborhood, not the desired endpoint conclusion. -/
structure FiniteMixedSideSameCloneTerminalAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        Nonempty
          ((T.terminalPath target).SameCloneTerminalNeighborhood
            (target : V))

namespace InitializationFiniteMixedSideTerminalCoreData

/-- The common-clone local claw theorem yields the exact two-incoming
endpoint alternative on the finite mixed-side terminal core. -/
theorem target_is_current_endpoint_of_twoIncoming_of_sameClone
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (S : FiniteMixedSideSameCloneTerminalAnalysis T)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) :
    ((T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V) ∨
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)) := by
  have hslots :
      T.currentSlot source target ≠
        T.currentSlot source' target := by
    intro hs
    exact hne
      (T.currentSlot_source_injective hclaw incoming incoming' hs)
  exact
    (T.terminalPath target).target_eq_selectedEndpoint_of_sameClone
      (target : V)
      (T.currentSlot source target)
      (T.currentSlot source' target)
      (by
        intro hfirst hlast
        obtain ⟨X⟩ :=
          S.interiorGeometry hne incoming incoming' hfirst hlast
        cases hsource : T.currentSlot source target <;>
            cases hsource' : T.currentSlot source' target
        · exact (hslots (hsource.trans hsource'.symm)).elim
        · exact X.toInteriorGeometry
            (by simpa [hsource] using hfirst)
            (by simpa [hsource'] using hlast)
        · exact X.toInteriorGeometry
            (by simpa [hsource'] using hlast)
            (by simpa [hsource] using hfirst)
        · exact (hslots (hsource.trans hsource'.symm)).elim)
      hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
