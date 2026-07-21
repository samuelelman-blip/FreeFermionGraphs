import FreeFermionGraphs.Lemma14Core

/-!
# Nearest-target selection in the obstruction search

At a terminating iteration of `OS`, the current vertex is an endpoint of an
induced path and the obstruction is the closest vertex of `W \ {source}` on
that path.  This module records that rule directly.  In particular, absence
of self-loops is derived from the search set rather than stored as a separate
certificate.
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

/-- `i` is the closest index in `S` when the path is viewed from the
selected endpoint. -/
def IsNearestFrom
    (P : IndexedInducedPath G) (e : ObstructionSlot)
    (S : Set V) (i : Fin P.card) : Prop :=
  P.vertex i ∈ S ∧
    ∀ j : Fin P.card, P.vertex j ∈ S →
      match e with
      | .first => i.val ≤ j.val
      | .last => j.val ≤ i.val

/-- The nearest eligible vertex from a fixed path endpoint is unique. -/
theorem nearestFrom_unique
    (P : IndexedInducedPath G) (e : ObstructionSlot)
    (S : Set V) {i j : Fin P.card}
    (hi : P.IsNearestFrom e S i)
    (hj : P.IsNearestFrom e S j) :
    i = j := by
  apply Fin.ext
  cases e
  · exact Nat.le_antisymm (hi.2 j hj.1) (hj.2 i hi.1)
  · exact Nat.le_antisymm (hj.2 i hi.1) (hi.2 j hj.1)

/-- The corresponding nearest eligible path vertex is unique as well. -/
theorem nearestVertex_unique
    (P : IndexedInducedPath G) (e : ObstructionSlot)
    (S : Set V) {i j : Fin P.card}
    (hi : P.IsNearestFrom e S i)
    (hj : P.IsNearestFrom e S j) :
    P.vertex i = P.vertex j := by
  rw [P.nearestFrom_unique e S hi hj]

end IndexedInducedPath

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- The initialization call for `source` searches precisely the other
vertices of `W`. -/
def allowedVertices
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node) : Set V :=
  {v | v ∈ I.W ∧ v ≠ (source : V)}

@[simp]
theorem mem_allowedVertices_iff
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node) (v : V) :
    v ∈ I.allowedVertices source ↔
      v ∈ I.W ∧ v ≠ (source : V) :=
  Iff.rfl

/-- The concrete target-selection part of the initialized `OS` trace.

For every obstruction arc, the chosen target lies on the terminal path and
is the closest allowed vertex from the endpoint occupied by the current
dependent vertex.  Terminal paths are nontrivial only under this arc
quantifier, which is the strength actually used in Lemma 14(iv). -/
structure InitializationNearestTargetData
    (I : ObstructionSearchInitialization families Cprime)
    (terminalPath : I.Node → IndexedInducedPath G)
    (currentSlot : I.Node → I.Node → ObstructionSlot) : Prop where
  terminalPath_nontrivial :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        2 ≤ (terminalPath target).card
  obstruction_nearest :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        ∃ q : Fin (terminalPath target).card,
          (terminalPath target).vertex q = (target : V) ∧
            (terminalPath target).IsNearestFrom
              (currentSlot source target)
              (I.allowedVertices source) q

namespace InitializationNearestTargetData

variable
  {terminalPath : I.Node → IndexedInducedPath G}
  {currentSlot : I.Node → I.Node → ObstructionSlot}

/-- An obstruction target belongs to the initialization search set. -/
theorem target_mem_allowed
    (N : I.InitializationNearestTargetData terminalPath currentSlot)
    {source target : I.Node}
    (h : I.graph.Arc source target) :
    (target : V) ∈ I.allowedVertices source := by
  obtain ⟨q, htarget, hnearest⟩ := N.obstruction_nearest h
  rw [← htarget]
  exact hnearest.1

/-- Initialization cannot create a self-loop because the source is excluded
from its candidate set. -/
theorem noSelfLoop
    (N : I.InitializationNearestTargetData terminalPath currentSlot)
    (source : I.Node) :
    I.obstruction source ≠ some source := by
  intro hself
  have hallowed : (source : V) ∈ I.allowedVertices source :=
    N.target_mem_allowed (source := source) (target := source) hself
  exact hallowed.2 rfl

/-- The closest-target rule also gives the explicit target/source
inequality used by the initialized obstruction graph. -/
theorem target_ne_source
    (N : I.InitializationNearestTargetData terminalPath currentSlot)
    {source target : I.Node}
    (h : I.graph.Arc source target) :
    target ≠ source := by
  intro hEq
  subst target
  exact N.noSelfLoop source h

/-- An obstruction arc has a unique closest eligible target index on its
terminal path. -/
theorem existsUnique_obstructionIndex
    (N : I.InitializationNearestTargetData terminalPath currentSlot)
    {source target : I.Node}
    (h : I.graph.Arc source target) :
    ∃! q : Fin (terminalPath target).card,
      (terminalPath target).vertex q = (target : V) ∧
        (terminalPath target).IsNearestFrom
          (currentSlot source target)
          (I.allowedVertices source) q := by
  obtain ⟨q, htarget, hnearest⟩ := N.obstruction_nearest h
  refine ⟨q, ⟨htarget, hnearest⟩, ?_⟩
  intro q' hq'
  exact ((terminalPath target).nearestFrom_unique
    (currentSlot source target) (I.allowedVertices source)
    hnearest hq'.2).symm

end InitializationNearestTargetData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
