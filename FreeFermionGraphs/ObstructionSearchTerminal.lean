import FreeFermionGraphs.ObstructionSearchNearest
import FreeFermionGraphs.ObstructionSearchExecutionTrace

/-!
# Terminal-path certificates for obstruction-search initialization

For an initialized obstruction-search arc, the current dependent vertex is
an endpoint of the terminal path component.  Two distinct searches entering
one target cannot use the same endpoint orientation.  The difficult final
case of Lemma 14(iv) proves the pair-specific statement that, when two such
arcs have the same target, the target equals one of their two current
endpoints.

That quantifier is important: the target of an arbitrary single arc may lie
strictly inside its terminal path.  This module therefore assumes no
per-arc target endpoint.  It derives the exact-one-dependent-set conclusion
only from the manuscript's two-incoming terminal theorem.
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

/-- The terminal-path data produced by initialization of `OS` before the
long two-search claw case is discharged.

For an arc `source → target`, `currentSlot source target` selects the
endpoint returned as the singleton dependent set.  Equal-slot source
injectivity is derived below from the final-selection invariant and
Corollary 11, rather than stored as input.  Keeping this core separate
prevents the final endpoint alternative from being hidden among the primitive
obstruction-search data. -/
structure InitializationTerminalCoreData
    (I : ObstructionSearchInitialization families Cprime) where
  obstructionOpposite : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      I.pairing target = (I.pairing source).opposite
  executionTrace : I.InitializationOSExecutionData
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

/-- Complete terminal-path data after the long two-search case of
Lemma 14(iv) has been proved.  The added field has the exact pairwise
quantifier from the manuscript: no endpoint claim is made for a single
incoming arc. -/
structure InitializationTerminalData
    (I : ObstructionSearchInitialization families Cprime)
    extends InitializationTerminalCoreData I where
  target_is_current_endpoint_of_twoIncoming :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
        ((terminalPath target).obstructionEndpoint
            (currentSlot source target) = (target : V) ∨
          (terminalPath target).obstructionEndpoint
            (currentSlot source' target) = (target : V))

namespace InitializationTerminalCoreData

/-- Two incoming searches cannot occupy the same terminal orientation.
Both sources have the same pairing type because they obstruct the same
target.  Equality of their slots would therefore make their singleton final
dependent vertices equal, contradicting the Corollary 11 disjointness theorem
derived from their concrete execution traces. -/
theorem currentSlot_source_injective
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    ⦃source source' target : I.Node⦄
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target)
    (hslot : T.currentSlot source target =
      T.currentSlot source' target) :
    source = source' := by
  by_contra hne
  have hopposite :
      (I.pairing source).opposite =
        (I.pairing source').opposite := by
    exact (T.obstructionOpposite h).symm.trans (T.obstructionOpposite h')
  have hpair : I.pairing source = I.pairing source' := by
    have hopposite' := congrArg PairingType.opposite hopposite
    simpa using hopposite'
  have hdisjoint :=
    T.executionTrace.samePairing_dependentSets_disjoint
      hclaw hne hpair
  let u := (T.terminalPath target).obstructionEndpoint
    (T.currentSlot source target)
  have hu : u ∈ I.dependentSet source := by
    exact T.dependent_is_current_endpoint h
  have hu' : u ∈ I.dependentSet source' := by
    change I.dependent source' = some u
    calc
      I.dependent source' =
          some ((T.terminalPath target).obstructionEndpoint
            (T.currentSlot source' target)) :=
        T.dependent_is_current_endpoint h'
      _ = some u := by rw [← hslot]
  exact (Set.disjoint_left.mp hdisjoint) hu hu'

end InitializationTerminalCoreData

namespace InitializationTerminalData

/-- The terminal-path certificate constructs the generic two-slot geometry
used for Lemma 14(i)--(iii) and the indegree bound. -/
noncomputable def toInitializationGeometry
    (T : I.InitializationTerminalData)
    (hclaw : G.IsClawFree) :
    I.InitializationGeometry :=
  ((InitializationOSExecutionData.toInitializationOrderedTraceData
      T.executionTrace).toInitializationFirstCommonPathData).toInitializationGeometry
    hclaw
    T.nearestTarget.noSelfLoop T.obstructionOpposite
    T.currentSlot (T.currentSlot_source_injective hclaw)

/-- If two distinct sources obstruct one target, the pair-specific terminal
theorem and distinct endpoint orientations make the target the unique
dependent vertex of exactly one search. -/
theorem target_onlyDependent_of_twoIncoming
    (T : I.InitializationTerminalData)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target) :
    ((I.dependentSet source = {(target : V)} ∧
        I.dependentSet source' ≠ {(target : V)}) ∨
      (I.dependentSet source ≠ {(target : V)} ∧
        I.dependentSet source' = {(target : V)})) := by
  let P := T.terminalPath target
  have hinjective : Function.Injective P.obstructionEndpoint :=
    P.obstructionEndpoint_injective
      (T.nearestTarget.terminalPath_nontrivial h)
  have hslots :
      T.currentSlot source target ≠
        T.currentSlot source' target := by
    intro hEq
    exact hne (T.currentSlot_source_injective hclaw h h' hEq)
  have hendpointNe :
      P.obstructionEndpoint (T.currentSlot source target) ≠
        P.obstructionEndpoint (T.currentSlot source' target) := by
    intro hEq
    exact hslots (hinjective hEq)
  rcases T.target_is_current_endpoint_of_twoIncoming hne h h' with
      hleft | hright
  · left
    constructor
    · apply (I.dependentSet_eq_singleton_iff source (target : V)).2
      calc
        I.dependent source =
            some (P.obstructionEndpoint
              (T.currentSlot source target)) :=
          T.dependent_is_current_endpoint h
        _ = some (target : V) := by rw [hleft]
    · intro hset
      have hdep :=
        (I.dependentSet_eq_singleton_iff source' (target : V)).1 hset
      have hrightEq :
          P.obstructionEndpoint (T.currentSlot source' target) =
            (target : V) := by
        apply Option.some.inj
        calc
          some (P.obstructionEndpoint
              (T.currentSlot source' target)) =
              I.dependent source' :=
            (T.dependent_is_current_endpoint h').symm
          _ = some (target : V) := hdep
      exact hendpointNe (hleft.trans hrightEq.symm)
  · right
    constructor
    · intro hset
      have hdep :=
        (I.dependentSet_eq_singleton_iff source (target : V)).1 hset
      have hleftEq :
          P.obstructionEndpoint (T.currentSlot source target) =
            (target : V) := by
        apply Option.some.inj
        calc
          some (P.obstructionEndpoint
              (T.currentSlot source target)) =
              I.dependent source :=
            (T.dependent_is_current_endpoint h).symm
          _ = some (target : V) := hdep
      exact hendpointNe (hleftEq.trans hright.symm)
    · apply (I.dependentSet_eq_singleton_iff source' (target : V)).2
      calc
        I.dependent source' =
            some (P.obstructionEndpoint
              (T.currentSlot source' target)) :=
          T.dependent_is_current_endpoint h'
        _ = some (target : V) := by rw [hright]

/-- Lemma 14 from faithful terminal-path output of the initialized
obstruction searches. -/
theorem lemma14_of_initializationTerminalData
    (T : I.InitializationTerminalData)
    (hclaw : G.IsClawFree) :
    (∀ source : I.Node,
      (I.output source).run = none ∨
        ∃ F : FullDefinition19Deformation
            (families (I.pairing source)) Cprime,
          (I.output source).run = some F) ∧
    I.graph.IsBipartiteByPairing I.pairing ∧
    (∀ ⦃source source' : I.Node⦄,
      source ≠ source' →
      I.pairing source = I.pairing source' →
        Disjoint (I.output source).paths
          (I.output source').paths) ∧
    ((∀ target : I.Node, I.graph.AtMostTwoIncoming target) ∧
      ∀ ⦃source source' target : I.Node⦄,
        source ≠ source' →
        I.graph.Arc source target →
        I.graph.Arc source' target →
          ((I.dependentSet source = {(target : V)} ∧
              I.dependentSet source' ≠ {(target : V)}) ∨
            (I.dependentSet source ≠ {(target : V)} ∧
              I.dependentSet source' = {(target : V)}))) := by
  obtain ⟨hi, hii, hiii, hindegree⟩ :=
    I.lemma14_core_of_initializationGeometry
      (T.toInitializationGeometry hclaw)
  refine ⟨hi, hii, hiii, hindegree, ?_⟩
  intro source source' target hne h h'
  exact T.target_onlyDependent_of_twoIncoming hclaw hne h h'

end InitializationTerminalData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
