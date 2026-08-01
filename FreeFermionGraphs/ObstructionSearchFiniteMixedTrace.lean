import FreeFermionGraphs.ObstructionSearchTwoSidedMixedExactHistory

/-!
# Finite mixed-side obstruction-search traces

Definition 19 uses a finite sequence of path blocks.  The legacy
`PathBlockHistory` interface instead stores a total `Nat`-indexed sequence and
requires its local data and carrier chain at every natural number, even though
the proofs use only a bounded prefix.  That is stronger than the manuscript
and cannot be emitted directly by a terminating obstruction search.

`SearchDeformation.run` has a separate loss of information: it retains the
flattened single-vertex replacements but forgets the division into path blocks
and the `ac` or `bd` side of each block.  This module introduces the finite
trace that the literal search loop must construct.  Its `stepIndex` maps every
local block step to the corresponding step of the flattened run, and
`stepIndex_surjective` proves that no flattened step is omitted.

The structure contains only Definition 19 data and execution provenance.  It
does not assume a conclusion of Lemma 11 or Lemma 14, and it does not yet
construct the trace from an executable `OS` loop.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- A nonempty finite, mixed-side block decomposition of one concrete search
run.

The `stepIndex_order` field states that the block order and each local step
order agree with the flattened execution order.  Removed vertices retain their
literal Definition 19 membership in the fixed original hole. -/
structure FiniteMixedSideSearchTrace
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G) where
  flattened : FullDefinition19Deformation O Cprime
  run_eq : S.run = some flattened
  blockCount : Nat
  blockCount_pos : 0 < blockCount
  block : Fin blockCount → ConcretePathDeformation O Cprime
  side : Fin blockCount → DeformationSide
  localData : ∀ i : Fin blockCount,
    ((block i).reorient (side i)).FullDefinition19Lemma11AData
  chain : ∀ {i j : Fin blockCount}, i.val + 1 = j.val →
    Set.range (block i).finalHole.vertex =
      Set.range (block j).initialHole.vertex
  originalHole_eq :
    Set.range (block ⟨0, blockCount_pos⟩).initialHole.vertex =
      Set.range originalHole.vertex
  removed_mem_original : ∀ (i : Fin blockCount)
      (s : Fin (block i).deformation.stepCount),
    ((block i).deformation.step s).before.vertex
        ((block i).deformation.step s).removedIndex ∈
      Set.range originalHole.vertex
  path_pairwise : ∀ {i j : Fin blockCount}, i ≠ j →
    Set.range (block i).path.vertex ≠
      Set.range (block j).path.vertex
  stepIndex : ∀ i : Fin blockCount,
    Fin (block i).deformation.stepCount →
      Fin flattened.deformation.stepCount
  step_eq : ∀ (i : Fin blockCount)
      (s : Fin (block i).deformation.stepCount),
    flattened.deformation.step (stepIndex i s) =
      (block i).deformation.step s
  stepIndex_surjective : ∀ k : Fin flattened.deformation.stepCount,
    ∃ (i : Fin blockCount)
      (s : Fin (block i).deformation.stepCount),
        stepIndex i s = k
  stepIndex_order : ∀ (i j : Fin blockCount)
      (s : Fin (block i).deformation.stepCount)
      (t : Fin (block j).deformation.stepCount),
    (i.val < j.val ∨ (i.val = j.val ∧ s.val < t.val)) →
      (stepIndex i s).val < (stepIndex j t).val

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Index of the first path block in the nonempty finite trace. -/
def firstIndex
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Fin X.blockCount :=
  ⟨0, X.blockCount_pos⟩

/-- The `i`th block presented in the component side selected by Definition 19. -/
def orientedBlock
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    ConcretePathDeformation ((X.side i).family O) Cprime :=
  (X.block i).reorient (X.side i)

@[simp] theorem orientedBlock_path
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    (X.orientedBlock i).path = (X.block i).path :=
  rfl

/-- The finite block trace has exactly the active paths retained by the
flattened `SearchDeformation.run`. -/
theorem output_path_iff
    (X : FiniteMixedSideSearchTrace S originalHole)
    (P : Set V) :
    P ∈ S.paths ↔
      ∃ i : Fin X.blockCount,
        Set.range (X.block i).path.vertex = P := by
  constructor
  · rintro ⟨F, hrun, k, hk⟩
    have hF : F = X.flattened :=
      Option.some.inj (hrun.symm.trans X.run_eq)
    subst F
    obtain ⟨i, s, his⟩ := X.stepIndex_surjective k
    refine ⟨i, ?_⟩
    rw [← (X.block i).activePath_eq s, ← X.step_eq i s, his, hk]
  · rintro ⟨i, hi⟩
    let s : Fin (X.block i).deformation.stepCount :=
      (X.block i).firstIndex
    refine ⟨X.flattened, X.run_eq, X.stepIndex i s, ?_⟩
    rw [X.step_eq i s, (X.block i).activePath_eq s, hi]

/-- Every finite trace contains at least one output path. -/
theorem paths_nonempty
    (X : FiniteMixedSideSearchTrace S originalHole) :
    S.paths.Nonempty := by
  let i := X.firstIndex
  refine ⟨Set.range (X.block i).path.vertex, ?_⟩
  exact (X.output_path_iff _).2 ⟨i, rfl⟩

/-- Every block belongs to the component family selected by its side tag. -/
theorem path_mem_selectedSide
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    (X.side i = .ac ∧
        Set.range (X.block i).path.vertex ∈ O.acPaths) ∨
      (X.side i = .bd ∧
        Set.range (X.block i).path.vertex ∈ O.bdPaths) := by
  have hactive :
      Set.range
          (((X.block i).reorient (X.side i)).path.vertex) ∈
        ((X.side i).family O).acPaths := by
    rw [← ((X.block i).reorient (X.side i)).activePath_eq
      ((X.block i).reorient (X.side i)).firstIndex]
    exact
      ((X.localData i).neighborhood.mechanical.stepGeometry
        ((X.block i).reorient (X.side i)).firstIndex).base.activePath_ac
  cases hside : X.side i with
  | ac =>
      left
      exact ⟨hside, by
        simpa [hside, DeformationSide.family] using hactive⟩
  | bd =>
      right
      exact ⟨hside, by
        simpa [hside, DeformationSide.family, swapSides] using hactive⟩

/-- Forgetting the side tag puts every finite trace block in the full
fixed-pairing path family. -/
theorem path_mem_family
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    Set.range (X.block i).path.vertex ∈ O.paths := by
  change Set.range (X.block i).path.vertex ∈ O.acPaths ∪ O.bdPaths
  rcases X.path_mem_selectedSide i with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
