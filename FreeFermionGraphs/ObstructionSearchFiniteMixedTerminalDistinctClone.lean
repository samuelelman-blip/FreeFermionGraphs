import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalCore
import FreeFermionGraphs.ObstructionSearchTerminalDistinctClone

/-!
# Distinct-clone terminal contradiction for finite mixed-side executions

This module ports the final graph-theoretic part of Lemma 14(iv) from the
legacy total execution trace to the literal finite mixed-side execution.
The propagation data is tied to an actual finite ordered block and the fixed
original hole.  The first-block degree-two conclusion, all exact
neighborhood bounds, and all three claw leaf nonedges are derived.

The remaining boundary after this module is construction of the propagation
data from the literal finite obstruction-search loop.  No endpoint conclusion
or Lemma 14 conclusion is stored in that propagation data.
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

namespace InitializationFiniteMixedSideOSExecutionData

/-- A dependent vertex of a first finite block whose final degree is three
has degree two on the fixed initialized original hole.  The first-block
carrier equality is supplied directly, while the local degree change is
derived from the side-oriented Definition 19 data. -/
theorem originalDegree_two_of_firstBlock_dependent
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (q : Fin (X.ordered source).blockCount)
    (hOriginal :
      Set.range ((X.ordered source).block q).initialHole.vertex =
        Set.range X.originalHole.vertex)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ ((X.ordered source).block q).dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : ((X.ordered source).block q).path.AnticommutesWith u)
    (hthree :
      ((X.ordered source).block q).finalHole.externalDegree u = 3) :
    X.originalHole.externalDegree u = 2 := by
  let D := (X.ordered source).block q
  let side := (X.ordered source).side q
  let A := D.reorient side
  have hData : A.FullDefinition19Lemma11AData := by
    simpa [A, D, side] using (X.ordered source).localData q
  have huA : u ∈ A.dependentAt s := by
    change u ∈ (D.reorient side).dependentAt s
    rw [D.reorient_dependentAt side s]
    exact hu
  have hantiA : A.path.AnticommutesWith u := by
    simpa [A, D, ConcretePathDeformation.reorient_path] using hanti
  have hlocal :=
    (A.lemma11a_membership_iff_ne_first_and_degree
      hData hclaw huPrime hantiA).mp ⟨s, huA⟩
  have hstep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1 := by
    cases side <;> exact hlocal.2
  have hinitial : D.initialHole.externalDegree u = 2 := by
    change D.finalHole.externalDegree u = 3 at hthree
    omega
  have hdegree :
      D.initialHole.externalDegree u =
        X.originalHole.externalDegree u :=
    D.initialHole.externalDegree_eq_of_range_eq
      X.originalHole (by simpa [D] using hOriginal)
  rw [← hdegree]
  exact hinitial

end InitializationFiniteMixedSideOSExecutionData

/-- The final distinct-clone propagation data tied to one literal finite
initialized execution.  It stores the displayed manuscript incidences and
inequalities, but neither derived degree-two fact nor any eventual claw
nonedge. -/
structure FiniteMixedSideDistinctClonePropagationData
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node) where
  incoming : I.graph.Arc source target
  dependentBlockIndex : Fin
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).blockCount
  dependentBlock_initial_eq_original :
    Set.range
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block dependentBlockIndex).initialHole.vertex =
      Set.range
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  dependentStep : Nat
  previous : V
  previous_mem_dependent :
    previous ∈
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block dependentBlockIndex).dependentAt dependentStep
  previous_mem_prime : previous ∈ Cprime
  previous_anticommutes :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block dependentBlockIndex).path.AnticommutesWith previous
  previous_finalDegree_three :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block dependentBlockIndex).finalHole.externalDegree previous = 3
  center : V
  propagatedNeighbor : V
  cloneIndex : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  target_clone :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
      (target : V) cloneIndex
  previousNeighbor0Index : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  previousNeighbor1Index : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  previousNeighbor0_ne_previousNeighbor1 :
    previousNeighbor0Index ≠ previousNeighbor1Index
  adj_previousNeighbor0 :
    G.Adj previous
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index)
  adj_previousNeighbor1 :
    G.Adj previous
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index)
  cloneNeighbor0Index : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  cloneNeighbor1Index : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  cloneNeighbor0_ne_cloneNeighbor1 :
    cloneNeighbor0Index ≠ cloneNeighbor1Index
  cloneNeighbor0_cyclic :
    CyclicAdjacent cloneIndex cloneNeighbor0Index
  cloneNeighbor1_cyclic :
    CyclicAdjacent cloneIndex cloneNeighbor1Index
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  adj_cloneCenter :
    G.Adj center
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex)
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  previous_ne_cloneCenter :
    previous ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex
  propagatedNeighbor_ne_cloneCenter :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index
  cloneCenter_ne_previousNeighbor0 :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  propagatedNeighbor_ne_cloneNeighbor0 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneNeighbor0Index
  propagatedNeighbor_ne_cloneNeighbor1 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneNeighbor1Index

namespace FiniteMixedSideDistinctClonePropagationData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}

/-- The preceding terminal vertex has degree two on the initialized original
hole by its literal first-block dependent occurrence. -/
theorem previous_originalDegree_two
    (X : FiniteMixedSideDistinctClonePropagationData T source target)
    (hclaw : G.IsClawFree) :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.externalDegree
      X.previous = 2 :=
  T.execution.toInitializationFiniteMixedSideOSExecutionData.originalDegree_two_of_firstBlock_dependent
    source X.dependentBlockIndex X.dependentBlock_initial_eq_original
    hclaw X.previous_mem_dependent X.previous_mem_prime
    X.previous_anticommutes X.previous_finalDegree_three

/-- Construct the final neighborhood object.  Its exact neighborhoods and
three claw leaf nonedges are then consequences of degree two. -/
def toFinalNeighborhood
    (X : FiniteMixedSideDistinctClonePropagationData T source target)
    (hclaw : G.IsClawFree) :
    DistinctCloneFinalNeighborhood G where
  originalHole :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole
  center := X.center
  previous := X.previous
  propagatedNeighbor := X.propagatedNeighbor
  otherClone :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
      X.cloneIndex
  previousNeighbor0 :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
      X.previousNeighbor0Index
  previousNeighbor1 :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
      X.previousNeighbor1Index
  b0 :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
      X.cloneNeighbor0Index
  b1 :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
      X.cloneNeighbor1Index
  adj_previous := X.adj_previous
  adj_propagatedNeighbor := X.adj_propagatedNeighbor
  adj_otherClone := X.adj_cloneCenter
  previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
  previous_ne_otherClone := X.previous_ne_cloneCenter
  propagatedNeighbor_ne_otherClone := X.propagatedNeighbor_ne_cloneCenter
  previousNeighbor0_mem_originalHole :=
    ⟨X.previousNeighbor0Index, rfl⟩
  previousNeighbor1_mem_originalHole :=
    ⟨X.previousNeighbor1Index, rfl⟩
  previousNeighbor0_ne_previousNeighbor1 := by
    intro h
    exact X.previousNeighbor0_ne_previousNeighbor1
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.injective h)
  adj_previousNeighbor0 := X.adj_previousNeighbor0
  adj_previousNeighbor1 := X.adj_previousNeighbor1
  previous_externalDegree_two := X.previous_originalDegree_two hclaw
  propagatedNeighbor_ne_previousNeighbor0 :=
    X.propagatedNeighbor_ne_previousNeighbor0
  propagatedNeighbor_ne_previousNeighbor1 :=
    X.propagatedNeighbor_ne_previousNeighbor1
  otherClone_ne_previousNeighbor0 := X.cloneCenter_ne_previousNeighbor0
  otherClone_ne_previousNeighbor1 := X.cloneCenter_ne_previousNeighbor1
  propagatedNeighbor_mem_originalHole := X.propagatedNeighbor_mem_originalHole
  otherClone_mem_originalHole := ⟨X.cloneIndex, rfl⟩
  b0_mem_originalHole := ⟨X.cloneNeighbor0Index, rfl⟩
  b1_mem_originalHole := ⟨X.cloneNeighbor1Index, rfl⟩
  b0_ne_b1 := by
    intro h
    exact X.cloneNeighbor0_ne_cloneNeighbor1
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.injective h)
  adj_otherClone_b0 :=
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.adj_iff
      _ _).2 X.cloneNeighbor0_cyclic
  adj_otherClone_b1 :=
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.adj_iff
      _ _).2 X.cloneNeighbor1_cyclic
  propagatedNeighbor_ne_b0 := X.propagatedNeighbor_ne_cloneNeighbor0
  propagatedNeighbor_ne_b1 := X.propagatedNeighbor_ne_cloneNeighbor1

/-- The finite execution-level distinct-clone propagation contradicts
claw-freeness. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationData T source target)
    (hclaw : G.IsClawFree) : False :=
  (X.toFinalNeighborhood hclaw).false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationData

/-- The two interior alternatives on the finite terminal core. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometry
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometry T source source' target
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationData T source target) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationData T source' target)) →
      FiniteMixedSideTwoIncomingInteriorGeometry T source source' target

/-- Pairwise finite terminal analysis under the negation of both endpoint
alternatives. -/
structure FiniteMixedSideTwoIncomingTerminalClawAnalysis
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
        FiniteMixedSideTwoIncomingInteriorGeometry T source source' target

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Both clone-centre alternatives contradict claw-freeness, so the common
target is one of the two current terminal endpoints. -/
theorem target_is_current_endpoint_of_twoIncoming_of_clawAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalClawAnalysis T)
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
      T.currentSlot source target ≠ T.currentSlot source' target := by
    intro hslot
    exact hne
      (T.currentSlot_source_injective hclaw incoming incoming' hslot)
  by_cases hsource :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V)
  · exact Or.inl hsource
  by_cases hsource' :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)
  · exact Or.inr hsource'
  rcases A.interiorGeometry hne incoming incoming' hsource hsource' with
      hsame | hdistinct
  · obtain ⟨X⟩ := hsame
    have hgeometry : Nonempty
        ((T.terminalPath target).SameCloneInteriorGeometry
          (target : V)) := by
      cases hslot : T.currentSlot source target <;>
          cases hslot' : T.currentSlot source' target
      · exact (hslots (hslot.trans hslot'.symm)).elim
      · exact X.toInteriorGeometry
          (by simpa [hslot] using hsource)
          (by simpa [hslot'] using hsource')
      · exact X.toInteriorGeometry
          (by simpa [hslot'] using hsource')
          (by simpa [hslot] using hsource)
      · exact (hslots (hslot.trans hslot'.symm)).elim
    obtain ⟨Y⟩ := hgeometry
    exact (Y.false_of_clawFree hclaw).elim
  · rcases hdistinct with ⟨⟨X⟩⟩ | ⟨⟨X⟩⟩
    · exact (X.false_of_clawFree hclaw).elim
    · exact (X.false_of_clawFree hclaw).elim

end InitializationFiniteMixedSideTerminalCoreData

/-- Complete finite terminal data once the two-incoming endpoint alternative
has been proved. -/
structure InitializationFiniteMixedSideTerminalData
    (I : ObstructionSearchInitialization families Cprime)
    extends I.InitializationFiniteMixedSideTerminalCoreData where
  target_is_current_endpoint_of_twoIncoming :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
        ((terminalPath target).obstructionEndpoint
            (currentSlot source target) = (target : V) ∨
          (terminalPath target).obstructionEndpoint
            (currentSlot source' target) = (target : V))

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Promote the finite terminal core after proving both interior-claw
alternatives. -/
def toInitializationFiniteMixedSideTerminalData_of_clawAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree) :
    I.InitializationFiniteMixedSideTerminalData where
  toInitializationFiniteMixedSideTerminalCoreData := T
  target_is_current_endpoint_of_twoIncoming := by
    intro source source' target hne incoming incoming'
    exact T.target_is_current_endpoint_of_twoIncoming_of_clawAnalysis
      A hclaw hne incoming incoming'

end InitializationFiniteMixedSideTerminalCoreData

namespace InitializationFiniteMixedSideTerminalData

/-- If two distinct sources obstruct one target, the endpoint alternative and
slot injectivity make the target the unique dependent vertex of exactly one
search. -/
theorem target_onlyDependent_of_twoIncoming
    (T : I.InitializationFiniteMixedSideTerminalData)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) :
    ((I.dependentSet source = {(target : V)} ∧
        I.dependentSet source' ≠ {(target : V)}) ∨
      (I.dependentSet source ≠ {(target : V)} ∧
        I.dependentSet source' = {(target : V)})) := by
  let P := T.terminalPath target
  have hinjective : Function.Injective P.obstructionEndpoint :=
    P.obstructionEndpoint_injective
      (T.nearestTarget.terminalPath_nontrivial incoming)
  have hslots :
      T.currentSlot source target ≠
        T.currentSlot source' target := by
    intro hEq
    exact hne
      (T.currentSlot_source_injective hclaw incoming incoming' hEq)
  have hendpointNe :
      P.obstructionEndpoint (T.currentSlot source target) ≠
        P.obstructionEndpoint (T.currentSlot source' target) := by
    intro hEq
    exact hslots (hinjective hEq)
  rcases T.target_is_current_endpoint_of_twoIncoming
      hne incoming incoming' with hleft | hright
  · left
    constructor
    · apply (I.dependentSet_eq_singleton_iff source (target : V)).2
      calc
        I.dependent source =
            some (P.obstructionEndpoint
              (T.currentSlot source target)) :=
          T.dependent_is_current_endpoint incoming
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
            (T.dependent_is_current_endpoint incoming').symm
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
            (T.dependent_is_current_endpoint incoming).symm
          _ = some (target : V) := hdep
      exact hendpointNe (hleftEq.trans hright.symm)
    · apply (I.dependentSet_eq_singleton_iff source' (target : V)).2
      calc
        I.dependent source' =
            some (P.obstructionEndpoint
              (T.currentSlot source' target)) :=
          T.dependent_is_current_endpoint incoming'
        _ = some (target : V) := by rw [hright]

/-- Lemma 14 from complete finite mixed-side terminal data. -/
theorem lemma14_of_initializationFiniteMixedSideTerminalData
    (T : I.InitializationFiniteMixedSideTerminalData)
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
  intro source source' target hne incoming incoming'
  exact T.target_onlyDependent_of_twoIncoming
    hclaw hne incoming incoming'

end InitializationFiniteMixedSideTerminalData

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from the finite terminal core and the two explicit interior-claw
branches. -/
theorem lemma14_of_terminalClawAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalClawAnalysis T)
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
              I.dependentSet source' = {(target : V)}))) :=
  (T.toInitializationFiniteMixedSideTerminalData_of_clawAnalysis A hclaw).
    lemma14_of_initializationFiniteMixedSideTerminalData hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
