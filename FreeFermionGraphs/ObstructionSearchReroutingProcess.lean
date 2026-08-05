import FreeFermionGraphs.ObstructionSearchFiniteMixedLemma14History
import FreeFermionGraphs.ObstructionSearchReroutingConcat

/-!
# Finite corrective obstruction-search rerouting

Lemma 15 iterates the initialized obstruction search on strictly smaller
initializer sets.  At one corrective step a source and a common obstruction
are removed, all surviving searches except one are retained, and the
remaining distinguished source is rerun from the concatenation prescribed by
Eq. (C32).

This module records that literal finite process.  Every state carries the
Definition 19/20 execution history used to specify its nondeterministic search
runs, rather than any clause of Lemma 14.  The transition data record the
source/obstruction deletion, the embedding of the new initializer set into the
old one, the retained Eq. (C31) outputs, and the exact optional concatenation
and continuation of the Eq. (C32) rerun.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

/-- One fully specified finite obstruction-search state.  The history is the
literal data of all Definition 19/20 runs at this state and contains no
`PaperLemma14Conclusion`. -/
structure ObstructionSearchReroutingState : Type (u + 1) where
  initialization : ObstructionSearchInitialization families Cprime
  history :
    initialization.InitializationFiniteMixedSideLemma14History

namespace ObstructionSearchReroutingState

abbrev Node (S : ObstructionSearchReroutingState
    (families := families) (Cprime := Cprime)) :=
  S.initialization.Node

end ObstructionSearchReroutingState

/-- One literal corrective update from state `S` to state `T`.

`removedSource` is the source `j'` deleted in the manuscript and
`removedObstruction` is the common obstruction `j''`.  `oldRerouted` is the
surviving source `j`.  The map `survivor` identifies every new node with the
same underlying vertex in the old state.  Sources other than `rerouted` obey
Eq. (C31).  For Eq. (C32), `reroutingPrefix` is the exact optional
concatenation of the deleted and surviving parent searches, and
`reroutedOutput` is a finite continuation of that prefix.
-/
structure ObstructionSearchReroutingTransition
    (S T : ObstructionSearchReroutingState
      (families := families) (Cprime := Cprime)) : Type (u + 1) where
  removedSource : S.Node
  removedObstruction : S.Node
  removed_ne : removedSource ≠ removedObstruction
  oldRerouted : S.Node
  oldRerouted_ne_removedSource : oldRerouted ≠ removedSource
  oldRerouted_ne_removedObstruction : oldRerouted ≠ removedObstruction
  removedSource_arc :
    S.initialization.graph.Arc removedSource removedObstruction
  oldRerouted_arc :
    S.initialization.graph.Arc oldRerouted removedObstruction
  parent_pairing_eq :
    S.initialization.pairing removedSource =
      S.initialization.pairing oldRerouted
  removedObstruction_in_removedDependent :
    (removedObstruction : V) ∈
      S.initialization.dependentSet removedSource
  rerouteInitializer : V
  rerouteInitializer_mem_oldDependent :
    rerouteInitializer ∈
      S.initialization.dependentSet oldRerouted
  rerouteInitializer_ne_removedObstruction :
    rerouteInitializer ≠ (removedObstruction : V)
  next_W :
    T.initialization.W =
      S.initialization.W \
        ({(removedSource : V), (removedObstruction : V)} : Set V)
  survivor : T.Node → S.Node
  survivor_value : ∀ source : T.Node,
    (survivor source : V) = (source : V)
  pairing_preserved : ∀ source : T.Node,
    T.initialization.pairing source =
      S.initialization.pairing (survivor source)
  rerouted : T.Node
  rerouted_source_eq : survivor rerouted = oldRerouted
  rerouted_pairing_eq :
    T.initialization.pairing rerouted =
      S.initialization.pairing oldRerouted
  rerouteInitializer_not_mem_searchSet :
    rerouteInitializer ∉
      T.initialization.W \ {(rerouted : V)}
  retained_paths : ∀ source : T.Node,
    source ≠ rerouted →
      (T.initialization.output source).paths =
        (S.initialization.output (survivor source)).paths
  retained_dependent : ∀ source : T.Node,
    source ≠ rerouted →
      T.initialization.dependentSet source =
        S.initialization.dependentSet (survivor source)
  retained_arcs :
    ∀ {source target : T.Node}, source ≠ rerouted →
      (T.initialization.graph.Arc source target ↔
        S.initialization.graph.Arc
          (survivor source) (survivor target))
  reroutingPrefix :
    SearchDeformation
      (families (S.initialization.pairing oldRerouted)) Cprime
  prefix_is_concatenation :
    SearchDeformation.IsConcatenation
      (SearchDeformation.castFamily
        (families := families) parent_pairing_eq
        (S.initialization.output removedSource))
      (S.initialization.output oldRerouted)
      reroutingPrefix
  reroutedOutput :
    SearchDeformation
      (families (S.initialization.pairing oldRerouted)) Cprime
  reroutedOutput_eq :
    reroutedOutput =
      SearchDeformation.castFamily
        (families := families) rerouted_pairing_eq
        (T.initialization.output rerouted)
  rerouted_continuation :
    SearchDeformation.IsContinuation reroutingPrefix reroutedOutput

namespace ObstructionSearchReroutingTransition

variable {S T : ObstructionSearchReroutingState
  (families := families) (Cprime := Cprime)}

/-- The survivor embedding is injective because it preserves underlying
vertices. -/
theorem survivor_injective
    (R : ObstructionSearchReroutingTransition S T) :
    Function.Injective R.survivor := by
  intro source source' hEq
  apply Subtype.ext
  rw [← R.survivor_value source, ← R.survivor_value source', hEq]

/-- Neither deleted vertex occurs in the next initializer set. -/
theorem removedSource_not_mem_next
    (R : ObstructionSearchReroutingTransition S T) :
    (R.removedSource : V) ∉ T.initialization.W := by
  rw [R.next_W]
  simp

/-- Neither deleted vertex occurs in the next initializer set. -/
theorem removedObstruction_not_mem_next
    (R : ObstructionSearchReroutingTransition S T) :
    (R.removedObstruction : V) ∉ T.initialization.W := by
  rw [R.next_W]
  simp

/-- Every new source is an old source distinct from both deleted vertices. -/
theorem survivor_ne_removedSource
    (R : ObstructionSearchReroutingTransition S T)
    (source : T.Node) :
    R.survivor source ≠ R.removedSource := by
  intro hEq
  have hmem : (R.removedSource : V) ∈ T.initialization.W := by
    rw [← R.survivor_value source, hEq]
    exact source.property
  exact R.removedSource_not_mem_next hmem

/-- Every new source is an old source distinct from both deleted vertices. -/
theorem survivor_ne_removedObstruction
    (R : ObstructionSearchReroutingTransition S T)
    (source : T.Node) :
    R.survivor source ≠ R.removedObstruction := by
  intro hEq
  have hmem : (R.removedObstruction : V) ∈ T.initialization.W := by
    rw [← R.survivor_value source, hEq]
    exact source.property
  exact R.removedObstruction_not_mem_next hmem

/-- Equation (C32) forces every path from both parent deformations to occur in
the rerouted output.  This is derived from the exact optional concatenation and
continuation, rather than stored as a transition field. -/
theorem rerouted_prefix_paths
    (R : ObstructionSearchReroutingTransition S T) :
    (S.initialization.output R.removedSource).paths ∪
        (S.initialization.output R.oldRerouted).paths ⊆
      (T.initialization.output R.rerouted).paths := by
  intro P hP
  have hparent :
      P ∈ R.reroutingPrefix.paths := by
    apply R.prefix_is_concatenation.union_paths_subset
    rcases hP with hleft | hright
    · left
      rw [SearchDeformation.paths_castFamily]
      exact hleft
    · exact Or.inr hright
  have hresult : P ∈ R.reroutedOutput.paths :=
    R.rerouted_continuation.prefix_paths_subset hparent
  rw [R.reroutedOutput_eq,
    SearchDeformation.paths_castFamily] at hresult
  exact hresult

end ObstructionSearchReroutingTransition

/-- A finite execution of the corrective search process.  State zero is the
initialization of Lemma 14.  Each following state is connected to its
predecessor by one literal Eq. (C31)/(C32) transition. -/
structure ObstructionSearchReroutingProcess : Type (u + 1) where
  stepCount : Nat
  state : Fin (stepCount + 1) →
    ObstructionSearchReroutingState
      (families := families) (Cprime := Cprime)
  transition : ∀ i : Fin stepCount,
    ObstructionSearchReroutingTransition
      (state (Fin.castSucc i)) (state (Fin.succ i))

namespace ObstructionSearchReroutingProcess

/-- Exact statement of manuscript Lemma 15 for a finite corrective search
process: the four-part statement of Lemma 14 holds at every represented step. -/
def PaperLemma15Conclusion
    (P : ObstructionSearchReroutingProcess
      (families := families) (Cprime := Cprime)) : Prop :=
  ∀ i : Fin (P.stepCount + 1),
    ObstructionSearchInitialization.PaperLemma14Conclusion
      (P.state i).initialization

/-- Manuscript Lemma 15.  Each state is a literal finite Definition 19/20
search history, so the completed Lemma 14 theorem applies uniformly at every
step of the corrective rerouting process. -/
theorem paperLemma15
    (P : ObstructionSearchReroutingProcess
      (families := families) (Cprime := Cprime))
    (hclaw : G.IsClawFree) :
    P.PaperLemma15Conclusion := by
  intro i
  exact (P.state i).history.paperLemma14 hclaw

end ObstructionSearchReroutingProcess

end FixedPairingPathFamily
end SimpleGraph
