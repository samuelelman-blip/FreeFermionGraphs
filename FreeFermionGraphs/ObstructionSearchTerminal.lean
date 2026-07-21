import FreeFermionGraphs.Lemma14Core

/-!
# Terminal-path certificates for obstruction-search initialization

When an initialized obstruction search terminates at a vertex of `W`, its
current dependent vertex is an endpoint of the terminal path component.  Two
searches entering the same obstruction from the same endpoint coincide; a
path has only two endpoint orientations.  This is the finite mechanism behind
the indegree bound in Lemma 14(iv).

The manuscript's long claw-free argument proves the remaining local fact that
the obstruction target itself is one of those two endpoints.  Once that fact
is supplied by the concrete `OS` traversal, the statement that the target is
the dependent vertex of exactly one of two incoming searches follows here.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The endpoint index selected by an obstruction-search orientation. -/
def obstructionEndpointIndex
    (P : IndexedInducedPath G) : ObstructionSlot → Fin P.card
  | .first => ⟨0, P.nonempty⟩
  | .last => ⟨P.card - 1, by
      have hpositive := P.nonempty
      omega⟩

/-- The endpoint vertex selected by an obstruction-search orientation. -/
def obstructionEndpoint
    (P : IndexedInducedPath G) (e : ObstructionSlot) : V :=
  P.vertex (P.obstructionEndpointIndex e)

/-- A path with at least two vertices has distinct endpoint orientations. -/
theorem obstructionEndpoint_injective
    (P : IndexedInducedPath G) (htwo : 2 ≤ P.card) :
    Function.Injective P.obstructionEndpoint := by
  intro e f hef
  apply P.injective at hef
  cases e <;> cases f
  · rfl
  · exfalso
    have hval := congrArg Fin.val hef
    simp [obstructionEndpointIndex] at hval
    omega
  · exfalso
    have hval := congrArg Fin.val hef
    simp [obstructionEndpointIndex] at hval
    omega
  · rfl

end IndexedInducedPath

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Concrete terminal-path data produced by initialization of `OS`.

For an arc `source → target`, `currentSlot source target` selects the endpoint
which is returned as the singleton dependent set.  `targetSlot target`
selects the endpoint occupied by the obstruction target.  The source
injectivity field is the no-shared-terminal-state consequence of Corollary 11;
`target_at_endpoint` is the specific claw-free terminal-path fact proved in
the final part of Lemma 14(iv). -/
structure InitializationTerminalData
    (I : ObstructionSearchInitialization families Cprime) where
  noSelfLoop : ∀ source : I.Node,
    I.obstruction source ≠ some source
  obstructionOpposite : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      I.pairing target = (I.pairing source).opposite
  pathOwner : PairingType → Set V → Option I.Node
  path_owner_eq : ∀ (source : I.Node) ⦃P : Set V⦄,
    P ∈ (I.output source).paths →
      pathOwner (I.pairing source) P = some source
  terminalPath : I.Node → IndexedInducedPath G
  terminalPath_nontrivial : ∀ target : I.Node,
    2 ≤ (terminalPath target).card
  currentSlot : I.Node → I.Node → ObstructionSlot
  targetSlot : I.Node → ObstructionSlot
  dependent_is_current_endpoint :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        I.dependent source = some
          ((terminalPath target).obstructionEndpoint
            (currentSlot source target))
  target_at_endpoint : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      (target : V) =
        (terminalPath target).obstructionEndpoint (targetSlot target)
  currentSlot_source_injective :
    ∀ ⦃source source' target : I.Node⦄,
      I.graph.Arc source target →
      I.graph.Arc source' target →
      currentSlot source target = currentSlot source' target →
        source = source'

namespace InitializationTerminalData

/-- The terminal-path certificate constructs the generic two-slot geometry
used by the finite Lemma 14 argument. -/
def toInitializationGeometry
    (T : I.InitializationTerminalData) :
    I.InitializationGeometry where
  noSelfLoop := T.noSelfLoop
  obstructionOpposite := T.obstructionOpposite
  pathOwner := T.pathOwner
  path_owner_eq := T.path_owner_eq
  incomingSlot := T.currentSlot
  targetSlot := T.targetSlot
  incomingSlot_injective := T.currentSlot_source_injective
  dependent_target_iff_slot := by
    intro source target h
    let P := T.terminalPath target
    have hinjective : Function.Injective P.obstructionEndpoint :=
      P.obstructionEndpoint_injective (T.terminalPath_nontrivial target)
    constructor
    · intro hdependent
      have hvertices :
          P.obstructionEndpoint (T.currentSlot source target) =
            P.obstructionEndpoint (T.targetSlot target) := by
        apply Option.some.inj
        calc
          some (P.obstructionEndpoint (T.currentSlot source target)) =
              I.dependent source := (T.dependent_is_current_endpoint h).symm
          _ = some (target : V) := hdependent
          _ = some (P.obstructionEndpoint (T.targetSlot target)) := by
            rw [T.target_at_endpoint h]
      exact hinjective hvertices
    · intro hslot
      calc
        I.dependent source =
            some (P.obstructionEndpoint (T.currentSlot source target)) :=
          T.dependent_is_current_endpoint h
        _ = some (P.obstructionEndpoint (T.targetSlot target)) := by
          rw [hslot]
        _ = some (target : V) := by
          rw [T.target_at_endpoint h]

/-- Lemma 14 from the faithful terminal-path output of the initialized
obstruction searches. -/
theorem lemma14_of_initializationTerminalData
    (T : I.InitializationTerminalData) :
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
  exact I.lemma14_of_initializationGeometry T.toInitializationGeometry

end InitializationTerminalData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
