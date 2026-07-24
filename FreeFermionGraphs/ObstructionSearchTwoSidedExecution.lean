import FreeFermionGraphs.ObstructionSearchExecutionTrace
import FreeFermionGraphs.ObstructionSearchTwoSidedHistory

/-!
# Two-sided ordered obstruction-search executions

The original `OrderedOSExecution` stores the one-sided `SearchHistoryData`
interface.  The manuscript search may append blocks from both fixed-pairing
component sides, so this module introduces the side-correct ordered path layer.

This layer records the finite block enumeration and the literal initializer
stopping invariants.  The maximal-`L_{r,s}` earlier-selection rule is not yet
migrated, because its dependent-set statement must be transported between the
side-indexed block types without erasing the selected side.
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

/-- The ordered path-block data of one initialized `OS` execution, using the
paper-faithful two-sided history interface.

Every field is literal execution data or the local Corollary 10 source
uniqueness statement.  No common-path, disjointness, terminal-hole, or Lemma 14
conclusion is stored. -/
structure TwoSidedOrderedPathExecution
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  history : TwoSidedSearchHistoryData (I.output source) originalHole
  blockCount : Nat
  path : Fin blockCount → Set V
  path_mem : ∀ i : Fin blockCount,
    path i ∈ (I.output source).paths
  output_path : ∀ ⦃P : Set V⦄,
    P ∈ (I.output source).paths →
      ∃ i : Fin blockCount, path i = P
  source_mem_first : ∀ i : Fin blockCount,
    i.val = 0 → (source : V) ∈ path i
  source_block_zero : ∀ i : Fin blockCount,
    (source : V) ∈ path i → i.val = 0
  avoidsOtherSources : ∀ i : Fin blockCount,
    Disjoint (path i) (I.W \ {(source : V)})

namespace TwoSidedOrderedPathExecution

/-- The side-aware concrete witness attached to indexed block `i`. -/
def blockWitness
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedPathExecution I source originalHole)
    (i : Fin X.blockCount) :
    TwoSidedSearchPathHistoryWitness
      (I.output source) originalHole (X.path i) :=
  X.history.witness (X.path_mem i)

/-- The manuscript component side of indexed block `i`. -/
def blockSide
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedPathExecution I source originalHole)
    (i : Fin X.blockCount) : DeformationSide :=
  (X.blockWitness i).side

/-- Every indexed block belongs to the component family selected by its
recorded manuscript side. -/
theorem path_mem_selectedSide
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedPathExecution I source originalHole)
    (i : Fin X.blockCount) :
    match X.blockSide i with
    | .ac => X.path i ∈ (families (I.pairing source)).acPaths
    | .bd => X.path i ∈ (families (I.pairing source)).bdPaths := by
  exact (X.blockWitness i).path_mem_selectedSide

/-- Forgetting the side recovers membership in the full fixed-pairing family. -/
theorem path_mem_family
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedPathExecution I source originalHole)
    (i : Fin X.blockCount) :
    X.path i ∈ (families (I.pairing source)).paths :=
  (X.blockWitness i).path_mem_family

/-- The stopping rule excludes every initializer other than `source` from
all paths actually appended by the execution. -/
theorem otherSource_not_mem_path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedPathExecution I source originalHole)
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

/-- Corollary 10 source uniqueness together with the stopping rule gives the
exact initializer-incidence statement used by the ordered search argument. -/
theorem initializer_mem_path_iff
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedPathExecution I source originalHole)
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

end TwoSidedOrderedPathExecution

namespace OrderedOSExecution

/-- The existing one-sided execution embeds into the side-correct ordered path
layer as the `.ac` special case.  This is a compatibility map only; it does not
construct the missing `.bd` blocks of the manuscript search. -/
def toTwoSidedOrderedPathExecution
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole) :
    TwoSidedOrderedPathExecution I source originalHole where
  history := X.history.toTwoSided
  blockCount := X.blockCount
  path := X.path
  path_mem := X.path_mem
  output_path := X.output_path
  source_mem_first := X.source_mem_first
  source_block_zero := X.source_block_zero
  avoidsOtherSources := X.avoidsOtherSources

end OrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
