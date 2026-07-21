import FreeFermionGraphs.Lemma14Core

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

For an arc `source → target`, `currentSlot source target` selects the
endpoint returned as the singleton dependent set.  The source-injectivity
field is the no-shared-terminal-state consequence of Corollary 11.  The
last field is exactly the long terminal case in Lemma 14(iv): it applies
only to two distinct incoming searches and says that their common target is
one of the two current endpoints. -/
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
  dependent_is_current_endpoint :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        I.dependent source = some
          ((terminalPath target).obstructionEndpoint
            (currentSlot source target))
  currentSlot_source_injective :
    ∀ ⦃source source' target : I.Node⦄,
      I.graph.Arc source target →
      I.graph.Arc source' target →
      currentSlot source target = currentSlot source' target →
        source = source'
  target_is_current_endpoint_of_twoIncoming :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
        ((terminalPath target).obstructionEndpoint
            (currentSlot source target) = (target : V) ∨
          (terminalPath target).obstructionEndpoint
            (currentSlot source' target) = (target : V))

namespace InitializationTerminalData

/-- The terminal-path certificate constructs the generic two-slot geometry
used for Lemma 14(i)--(iii) and the indegree bound. -/
def toInitializationGeometry
    (T : I.InitializationTerminalData) :
    I.InitializationGeometry where
  noSelfLoop := T.noSelfLoop
  obstructionOpposite := T.obstructionOpposite
  pathOwner := T.pathOwner
  path_owner_eq := T.path_owner_eq
  incomingSlot := T.currentSlot
  incomingSlot_injective := T.currentSlot_source_injective

/-- If two distinct sources obstruct one target, the pair-specific terminal
theorem and distinct endpoint orientations make the target the unique
dependent vertex of exactly one search. -/
theorem target_onlyDependent_of_twoIncoming
    (T : I.InitializationTerminalData)
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
    P.obstructionEndpoint_injective (T.terminalPath_nontrivial target)
  have hslots :
      T.currentSlot source target ≠
        T.currentSlot source' target := by
    intro hEq
    exact hne (T.currentSlot_source_injective h h' hEq)
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
  obtain ⟨hi, hii, hiii, hindegree⟩ :=
    I.lemma14_core_of_initializationGeometry T.toInitializationGeometry
  exact ⟨hi, hii, hiii, hindegree,
    fun hne h h' => T.target_onlyDependent_of_twoIncoming hne h h'⟩

end InitializationTerminalData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
