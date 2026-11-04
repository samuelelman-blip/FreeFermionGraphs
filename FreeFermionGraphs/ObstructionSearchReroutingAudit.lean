import FreeFermionGraphs.ObstructionSearchReroutingProcess

/-!
# Audit of the finite corrective rerouting model

This module settles whether the corrective-update structure
`ObstructionSearchReroutingTransition` of the finite Lemma 15 model can be
inhabited.  It cannot: no transition exists between any two states, so every
`ObstructionSearchReroutingProcess` has `stepCount = 0`, and the model of
Lemma 15 collapses to Lemma 14 at the single state `0`.

## Why the model is vacuous

In v1 (arXiv 2305.15625, Lemma 9 `lemma:searchprocessinduction`, Eqs.
`searchprocesstrivialupdate`/`searchprocessupdate`, and the signature of `OS`
at the start of the search-process subsection) the rerouted source `j` is rerun
as `OS(O_{j'} ‖ O_j, u_{j,f}, W^{(i+1)} ∖ {j})`.  The initial deformation of
this call is the concatenation of the deleted source's deformation `O_{j'}`
with `O_j`.  Since `j''` is the only member of `U_{j'}` and `j'' ≠ j'`,
the deformation `O_{j'}` is nonempty, and its first path was initialised by
`j'`, not by `j`.

The Lean model of one `OS` call
(`NonemptyFiniteMixedSideOSExecution`) encodes only the case in which the
search begins with the empty deformation and the initialising vertex is the
source itself: its field `source_mem_first` places the source in the first path
block.  Its field `avoidsOtherSources` excludes every other initializer from
every path.  The transition structure asks for exactly one `OS` call of this
kind for `rerouted`, whose first path block is, by the exact concatenation and
continuation fields, the first path block of the search of the deleted source
`j'`.  By `avoidsOtherSources` for `j'`, that block avoids the surviving source
`j`, while `source_mem_first` for `rerouted` (which has underlying vertex `j`)
demands that it contain `j`.

Proof chain, each step using only existing structure fields:

1. `removedObstruction_in_removedDependent` with `removed_ne` excludes the
   initial-tether branch of `finalSelection`, and the empty execution has no
   blocks, so the execution of `j'` in `S` is nonempty.
2. The first path of the run of `j'` is the carrier of its block `0`
   (`FiniteMixedSideSearchTrace.firstPathIs`), and it avoids `j`.
3. The optional concatenation and the continuation both keep the first path of
   the left argument (`IsConcatenation.firstPathIs_left`), and family
   transport does not change the first path (`FirstPathIs.castFamily_iff`).
4. Hence the run of `rerouted` in `T` is nonempty with the same first path,
   and its own execution is nonempty with `source_mem_first`, placing `j`
   in it.

No hypothesis beyond the structure fields is used; in particular claw-freeness
is not needed.  This is an audit of the repository model, not a statement of
the paper.  The consequence for the documentation is that `paperLemma15` is
`paperLemma14` at state `0` only, and Lemma 15 must be rebuilt on an
obstruction-search model that can start from a nonempty prefix.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace SearchDeformation

/-- `P` is the carrier of the active path of the first single-vertex
replacement of the run of `S`.  In particular `S.run` is nonempty. -/
def FirstPathIs (S : SearchDeformation O Cprime) (P : Set V) : Prop :=
  ∃ F : FullDefinition19Deformation O Cprime,
    S.run = some F ∧
      Set.range (F.deformation.step ⟨0, F.nonempty⟩).activePath.vertex = P

namespace FirstPathIs

variable {S : SearchDeformation O Cprime} {P Q : Set V}

/-- A search output with a first path has a nonempty run. -/
theorem run_ne_none (h : S.FirstPathIs P) : S.run ≠ none := by
  obtain ⟨F, hF, _⟩ := h
  rw [hF]
  exact Option.some_ne_none F

/-- The first path of a search output is determined by the output. -/
theorem unique (h : S.FirstPathIs P) (h' : S.FirstPathIs Q) : P = Q := by
  obtain ⟨F, hF, hP⟩ := h
  obtain ⟨F', hF', hQ⟩ := h'
  have hFF : F = F' := Option.some.inj (hF.symm.trans hF')
  subst hFF
  exact hP.symm.trans hQ

/-- Transport across equality of the pairing-family index preserves the first
path. -/
theorem castFamily_iff {p q : PairingType} (h : p = q)
    (S : SearchDeformation (families p) Cprime) (P : Set V) :
    (castFamily (families := families) h S).FirstPathIs P ↔
      S.FirstPathIs P := by
  subst h
  exact Iff.rfl

end FirstPathIs

namespace IsConcatenation

variable {A B C : SearchDeformation O Cprime} {P : Set V}

/-- An optional concatenation whose left argument is nonempty keeps the first
path of the left argument.  In the `nonempty` branch the first step of
`left.concat right` is the first step of `left`. -/
theorem firstPathIs_left
    (H : IsConcatenation A B C) (hA : A.FirstPathIs P) :
    C.FirstPathIs P := by
  obtain ⟨F, hF, hP⟩ := hA
  cases H.branch with
  | leftEmpty left_empty _ =>
      rw [hF] at left_empty
      exact absurd left_empty (Option.some_ne_none F)
  | rightEmpty _ result_eq_left =>
      exact ⟨F, result_eq_left.trans hF, hP⟩
  | nonempty left right left_eq right_eq boundary result_eq =>
      have hleft : left = F := Option.some.inj (left_eq.symm.trans hF)
      subst hleft
      refine ⟨left.concat right boundary, result_eq, ?_⟩
      have hstep :=
        FullDefinition19Deformation.concat_deformation_step_left
          left right boundary ⟨0, left.nonempty⟩
      rw [← hP]
      exact congrArg (fun st => Set.range st.activePath.vertex) hstep

end IsConcatenation

namespace IsContinuation

variable {initial result : SearchDeformation O Cprime} {P : Set V}

/-- A continuation of a nonempty initial deformation keeps its first path. -/
theorem firstPathIs
    (H : IsContinuation initial result) (hi : initial.FirstPathIs P) :
    result.FirstPathIs P := by
  obtain ⟨tail, htail⟩ := H
  exact htail.firstPathIs_left hi

end IsContinuation

end SearchDeformation

namespace ConcretePathDeformation
namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime} {originalHole : IndexedInducedHole G}

/-- The first path of the flattened run of a finite trace is the carrier of its
block `0`. -/
theorem firstPathIs
    (X : FiniteMixedSideSearchTrace S originalHole) :
    S.FirstPathIs (Set.range (X.block X.firstIndex).path.vertex) := by
  refine ⟨X.flattened, X.run_eq, ?_⟩
  obtain ⟨i, s, his⟩ :=
    X.stepIndex_surjective ⟨0, X.flattened.nonempty⟩
  have hi : i.val = 0 := by
    by_contra hne
    have hlt := X.stepIndex_order X.firstIndex i
      (X.block X.firstIndex).firstIndex s
      (Or.inl (by simp only [firstIndex]; omega))
    rw [his] at hlt
    exact Nat.not_lt_zero _ hlt
  have hii : i = X.firstIndex := Fin.ext hi
  subst hii
  have hpath :
      (X.flattened.deformation.step ⟨0, X.flattened.nonempty⟩).activePath =
        (X.block X.firstIndex).path := by
    rw [← his, X.step_eq, (X.block X.firstIndex).activePath_eq]
  rw [hpath]

end FiniteMixedSideSearchTrace
end ConcretePathDeformation

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace NonemptyFiniteMixedSideOSExecution

/-- The first path of the initialized output is the carrier of block `0` of a
nonempty finite execution. -/
theorem firstPathIs
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole) :
    (I.output source).FirstPathIs
      (X.path ⟨0, X.literal.trace.blockCount_pos⟩) := by
  obtain ⟨F, hF, hP⟩ := X.literal.trace.firstPathIs
  exact ⟨F, by rw [← X.output_eq]; exact hF, hP⟩

end NonemptyFiniteMixedSideOSExecution

end ObstructionSearchInitialization

/-- **Audit theorem.**  The corrective transition structure of the finite
rerouting model is uninhabited: for any two states `S` and `T` there is no
`ObstructionSearchReroutingTransition S T`.

The deleted source `j'` has nonempty search (its dependent set contains
`j'' ≠ j'`, which excludes the initial-tether branch), and the exact
concatenation/continuation of Eq. (C32) makes the first path block of the
rerouted search the first path block of the search of `j'`.  That block avoids
the surviving source `j` by `avoidsOtherSources` in `S`, but must contain `j`
by `source_mem_first` in `T`.

This is a statement about the repository model, not about the manuscript:
in v1 the rerun `OS(O_{j'} ‖ O_j, u, W ∖ {j})` starts from the nonempty
prefix `O_{j'} ‖ O_j`, which the one-call execution model
(`NonemptyFiniteMixedSideOSExecution`, whose `source_mem_first` field assumes
the search starts from the empty deformation at its own source) cannot
represent.  No hypothesis beyond the structure fields (in particular no
claw-freeness) is used. -/
theorem ObstructionSearchReroutingTransition.isEmpty
    {S T : ObstructionSearchReroutingState
      (families := families) (Cprime := Cprime)} :
    IsEmpty (ObstructionSearchReroutingTransition S T) := by
  refine ⟨fun R => ?_⟩
  -- The execution of the removed source in `S` is nonempty.
  let Ys := S.history.core.execution.toInitializationFiniteMixedSideOSExecutionData
  have hdep : S.initialization.dependent R.removedSource =
      some (R.removedObstruction : V) :=
    (S.initialization.mem_dependentSet_iff _ _).1
      R.removedObstruction_in_removedDependent
  obtain ⟨Xs⟩ : Nonempty
      (ObstructionSearchInitialization.NonemptyFiniteMixedSideOSExecution
        S.initialization R.removedSource Ys.originalHole) := by
    rcases hE : Ys.execution R.removedSource with hrun | Xs
    · exfalso
      have W := S.history.core.execution.finalSelection
        R.removedSource _ hdep
      cases W with
      | initialTether sel =>
          exact R.removed_ne (Subtype.ext sel.dependent_eq_source.symm)
      | laterDefinition20 sel =>
          obtain ⟨q, _⟩ := sel
          have h0 : ∀ E : ObstructionSearchInitialization.FiniteMixedSideOSExecution
              S.initialization R.removedSource Ys.originalHole,
              E = .empty hrun → E.toOrdered.blockCount = 0 := by
            intro E hEE
            subst hEE
            rfl
          have h1 :
              (S.history.core.execution.ordered R.removedSource).blockCount =
                0 := h0 _ hE
          have h2 : q.val <
              (S.history.core.execution.ordered R.removedSource).blockCount :=
            q.isLt
          omega
    · exact ⟨Xs⟩
  -- Its first block avoids the surviving source.
  have hXs := Xs.firstPathIs
  have hcast := (SearchDeformation.FirstPathIs.castFamily_iff
    (families := families) R.parent_pairing_eq _ _).2 hXs
  have hprefix := R.prefix_is_concatenation.firstPathIs_left hcast
  have hout := R.rerouted_continuation.firstPathIs hprefix
  rw [R.reroutedOutput_eq] at hout
  have hT := (SearchDeformation.FirstPathIs.castFamily_iff
    (families := families) R.rerouted_pairing_eq _ _).1 hout
  -- The execution of the rerouted source in `T` is nonempty with the same
  -- first block.
  let Yt := T.history.core.execution.toInitializationFiniteMixedSideOSExecutionData
  rcases hE : Yt.execution R.rerouted with hrun | Xt
  · exact hT.run_ne_none hrun
  · have hXt := Xt.firstPathIs
    have hpath := hXt.unique hT
    have hmem : (R.rerouted : V) ∈
        Xt.path ⟨0, Xt.literal.trace.blockCount_pos⟩ :=
      Xt.source_mem_first ⟨0, Xt.literal.trace.blockCount_pos⟩ rfl
    rw [hpath] at hmem
    have hval : (R.rerouted : V) = (R.oldRerouted : V) := by
      rw [← R.survivor_value R.rerouted, R.rerouted_source_eq]
    rw [hval] at hmem
    exact Xs.otherSource_not_mem_path _ R.oldRerouted
      R.oldRerouted_ne_removedSource hmem

namespace ObstructionSearchReroutingProcess

/-- Every finite rerouting process of the repository model has no corrective
step.  The model therefore only represents the initialization state, and
`paperLemma15` is Lemma 14 at state `0`. -/
theorem stepCount_eq_zero
    (P : ObstructionSearchReroutingProcess
      (families := families) (Cprime := Cprime)) :
    P.stepCount = 0 := by
  by_contra h
  exact (ObstructionSearchReroutingTransition.isEmpty.false
    (P.transition ⟨0, Nat.pos_of_ne_zero h⟩))

/-- Consequently the four-part Lemma 15 conclusion of a process is exactly the
Lemma 14 conclusion of its initial state. -/
theorem paperLemma15Conclusion_iff_state_zero
    (P : ObstructionSearchReroutingProcess
      (families := families) (Cprime := Cprime)) :
    P.PaperLemma15Conclusion ↔
      ObstructionSearchInitialization.PaperLemma14Conclusion
        (P.state 0).initialization := by
  constructor
  · intro h
    exact h 0
  · intro h i
    have hi : i = 0 := by
      apply Fin.ext
      have := P.stepCount_eq_zero
      have := i.isLt
      simp only [Fin.val_zero]
      omega
    rw [hi]
    exact h

end ObstructionSearchReroutingProcess

end FixedPairingPathFamily
end SimpleGraph
