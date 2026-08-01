import FreeFermionGraphs.ObstructionSearchFiniteMixedExecution

/-!
# Finite mixed-side initialized obstruction-search executions

An initialized call to `OS` may return the empty deformation.  Otherwise it
returns an inductively generated finite mixed-side execution together with the
literal local search invariants: the stopping condition against the other
sources, uniqueness of the source on the first block, maximal-step selection
of every later entry, and selection of a final dependent vertex.

This module records that exact empty/nonempty split without rebuilding the
legacy total `Nat` history.  No path-disjointness, terminal-claw conclusion,
or conclusion of Lemma 14 is stored.
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

/-- The nonempty branch of one initialized `OS` call, expressed on the
inductively generated finite mixed-side trace.

Every field after `output_eq` is a literal execution invariant or the local
Corollary 10 source-uniqueness consequence. -/
structure NonemptyFiniteMixedSideOSExecution
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  literal : ConcretePathDeformation.LiteralFiniteMixedSideSearchExecution
    (O := families (I.pairing source)) (Cprime := Cprime) originalHole
  output_eq : literal.output = I.output source
  source_mem_first : ∀ i : Fin literal.trace.blockCount,
    i.val = 0 →
      (source : V) ∈ Set.range (literal.trace.block i).path.vertex
  source_block_zero : ∀ i : Fin literal.trace.blockCount,
    (source : V) ∈ Set.range (literal.trace.block i).path.vertex →
      i.val = 0
  avoidsOtherSources : ∀ i : Fin literal.trace.blockCount,
    Disjoint (Set.range (literal.trace.block i).path.vertex)
      (I.W \ {(source : V)})
  earlierSelection :
    ∀ (i : Fin literal.trace.blockCount) (_ : 0 < i.val),
      ∃ (q : Fin literal.trace.blockCount) (s : Nat),
        q.val < i.val ∧
          ((literal.trace.block i).deformation.step
              (literal.trace.block i).firstIndex).introduced ∈
            (literal.trace.block q).dependentAt s ∧
          (literal.trace.block q).path.AnticommutesWith
            ((literal.trace.block i).deformation.step
              (literal.trace.block i).firstIndex).introduced
  finalSelection :
    ∀ ⦃u : V⦄, I.dependent source = some u →
      ∃ (q : Fin literal.trace.blockCount) (s : Nat),
        u ∈ (literal.trace.block q).dependentAt s ∧
          (literal.trace.block q).path.AnticommutesWith u

namespace NonemptyFiniteMixedSideOSExecution

/-- Number of literal path blocks in the nonempty initialized execution. -/
abbrev blockCount
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole) : Nat :=
  X.literal.trace.blockCount

/-- The `i`th literal path block. -/
abbrev block
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    ConcretePathDeformation (families (I.pairing source)) Cprime :=
  X.literal.trace.block i

/-- The manuscript component side selected for block `i`. -/
abbrev side
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) : DeformationSide :=
  X.literal.trace.side i

/-- Carrier of the `i`th output path. -/
def path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) : Set V :=
  Set.range (X.block i).path.vertex

/-- First introduced vertex of the `i`th path block. -/
def entry
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) : V :=
  ((X.block i).deformation.step (X.block i).firstIndex).introduced

/-- Every indexed path is an actual path of the initialized search output. -/
theorem path_mem
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    X.path i ∈ (I.output source).paths := by
  rw [← X.output_eq]
  exact (X.literal.output_path_iff (X.path i)).2 ⟨i, rfl⟩

/-- Every path of the initialized output occurs at a finite block index. -/
theorem output_path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    {P : Set V} (hP : P ∈ (I.output source).paths) :
    ∃ i : Fin X.blockCount, X.path i = P := by
  have hPLiteral : P ∈ X.literal.output.paths := by
    rw [X.output_eq]
    exact hP
  exact (X.literal.output_path_iff P).1 hPLiteral

/-- Every indexed block belongs to its selected component side. -/
theorem path_mem_selectedSide
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    match X.side i with
    | .ac => X.path i ∈ (families (I.pairing source)).acPaths
    | .bd => X.path i ∈ (families (I.pairing source)).bdPaths := by
  rcases X.literal.trace.path_mem_selectedSide i with h | h
  · simpa [path, h.1] using h.2
  · simpa [path, h.1] using h.2

/-- The stopping rule excludes every initializer other than `source` from
every path actually appended by this execution. -/
theorem otherSource_not_mem_path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) (v : I.Node)
    (hne : v ≠ source) :
    (v : V) ∉ X.path i := by
  intro hvPath
  have hvNe : (v : V) ≠ (source : V) := by
    intro hval
    exact hne (Subtype.ext hval)
  have hvOther : (v : V) ∈ I.W \ {(source : V)} := by
    exact ⟨v.property, by simpa using hvNe⟩
  exact (Set.disjoint_left.mp (X.avoidsOtherSources i)) hvPath hvOther

/-- Source incidence is exactly the first-block condition. -/
theorem initializer_mem_path_iff
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.blockCount) (v : I.Node) :
    (v : V) ∈ X.path i ↔ v = source ∧ i.val = 0 := by
  constructor
  · intro hv
    by_cases hvs : v = source
    · subst v
      exact ⟨rfl, X.source_block_zero i hv⟩
    · exact (X.otherSource_not_mem_path i v hvs hv).elim
  · rintro ⟨rfl, hi⟩
    exact X.source_mem_first i hi

/-- Exact finite-history Lemma 11(a.ii) holds for every path of this literal
initialized execution. -/
theorem output_path_has_lemma11aii_exact
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : NonemptyFiniteMixedSideOSExecution I source originalHole)
    {P : Set V} (hP : P ∈ (I.output source).paths)
    (hclaw : G.IsClawFree) :
    ∃ i : Fin X.blockCount,
      X.path i = P ∧
        ∀ {s : Nat} {u : V},
          u ∈ (X.block i).dependentAt s →
          u ∈ Cprime →
          (X.block i).path.AnticommutesWith u →
            ((X.block i).finalHole.externalDegree u = 4 ↔
              originalHole.externalDegree u = 3 ∧
                (families (I.pairing source)).HasTypedClone
                  .ad originalHole u) := by
  have hPLiteral : P ∈ X.literal.output.paths := by
    rw [X.output_eq]
    exact hP
  simpa [path, block] using
    X.literal.output_path_has_lemma11aii_exact hPLiteral hclaw

end NonemptyFiniteMixedSideOSExecution

/-- One initialized `OS` call is either literally empty or carries the full
generated nonempty finite execution and its local search invariants. -/
inductive FiniteMixedSideOSExecution
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  | empty (run_eq : (I.output source).run = none)
  | nonempty
      (data : NonemptyFiniteMixedSideOSExecution I source originalHole)

namespace FiniteMixedSideOSExecution

/-- The exact empty/nonempty provenance split for one initialized call. -/
theorem run_eq_none_or_nonempty
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole) :
    (I.output source).run = none ∨
      Nonempty (NonemptyFiniteMixedSideOSExecution I source originalHole) := by
  cases X with
  | empty h => exact Or.inl h
  | nonempty data => exact Or.inr ⟨data⟩

end FiniteMixedSideOSExecution

/-- Literal finite initialized executions for every source vertex. -/
structure InitializationFiniteMixedSideOSExecutionData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  execution : ∀ source : I.Node,
    FiniteMixedSideOSExecution I source originalHole

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
