import FreeFermionGraphs.ObstructionSearchOrderedTrace

/-!
# Concrete execution traces for initialized obstruction searches

`InitializationOrderedTraceData` is the finite object consumed by the
first-common-path argument, but an execution of `OS` does not produce its
fields as unrelated certificates.  It produces an ordered sequence of path
blocks and three local invariants:

* the search stops before appending a path meeting `W \ {source}`;
* Corollary 10 makes the source belong only to the first block;
* the entry of every later block is selected from a dependent set of a
  strictly earlier block and anticommutes with that earlier path.

This module packages exactly those local execution facts and derives the
ordered trace.  The equality of entries on a common same-pairing path is
also derived from a per-path canonical orientation, rather than stored as a
pairwise conclusion.
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

/-- Local data emitted by one initialized execution of `OS`.

`avoidsOtherSources` is the literal stopping condition before a path is
appended.  `source_block_zero` is the Corollary 10 uniqueness statement for
the initializing vertex.  `earlierSelection` is the update rule based on the
eligible pair with maximal global step value `L_{r,s}`; only strict block
precedence is needed by Lemma 14(iii).
-/
structure OrderedOSExecution
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  history : SearchHistoryData (I.output source) originalHole
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
  earlierSelection :
    ∀ (i : Fin blockCount) (_ : 0 < i.val),
      ∃ (q : Fin blockCount) (s : Nat),
        q.val < i.val ∧
          (((history.witness (path_mem i)).block.deformation.step
              (history.witness (path_mem i)).block.firstIndex).introduced) ∈
            ((history.witness (path_mem q)).block.dependentAt s) ∧
          ((history.witness (path_mem q)).block.path).AnticommutesWith
            (((history.witness (path_mem i)).block.deformation.step
              (history.witness (path_mem i)).block.firstIndex).introduced)

namespace OrderedOSExecution

/-- The oriented entry vertex of a concrete path block. -/
def entry
    (X : OrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) : V :=
  (((X.history.witness (X.path_mem i)).block.deformation.step
      (X.history.witness (X.path_mem i)).block.firstIndex).introduced)

/-- The stopping rule excludes every initializer other than `source` from
every path that was actually appended. -/
theorem otherSource_not_mem_path
    (X : OrderedOSExecution I source originalHole)
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

/-- Combining the stopping rule with Corollary 10 gives the exact
initializer-incidence statement used in the least-common-path proof. -/
theorem initializer_mem_path_iff
    (X : OrderedOSExecution I source originalHole)
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

/-- Translate the local `OS` execution invariants into the ordered trace
consumed by the finite first-common-path theorem. -/
noncomputable def toOrderedSearchTrace
    (X : OrderedOSExecution I source originalHole) :
    OrderedSearchTrace I source originalHole where
  history := X.history
  blockCount := X.blockCount
  path := X.path
  path_mem := X.path_mem
  output_path := X.output_path
  entry := X.entry
  entry_is_firstIntroduced := by
    intro i
    rfl
  initializer_mem_path_iff := X.initializer_mem_path_iff
  earlierWitness := by
    intro i hi
    simpa [entry] using X.earlierSelection i hi

end OrderedOSExecution

/-- Concrete initialized executions for every source.

The orientation datum is local to one pairing type and one path carrier.
Thus two searches of the same pairing type that traverse the same path have
equal entries by rewriting, with no pairwise entry-equality certificate.
-/
structure InitializationOSExecutionData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  execution : ∀ source : I.Node,
    OrderedOSExecution I source originalHole
  canonicalEntry : PairingType → Set V → V
  entry_eq_canonical :
    ∀ (source : I.Node)
      (i : Fin (execution source).blockCount),
      (execution source).entry i =
        canonicalEntry (I.pairing source) ((execution source).path i)

namespace InitializationOSExecutionData

/-- The local executions and canonical path orientations construct all
ordered trace data required by Lemma 14(iii). -/
noncomputable def toInitializationOrderedTraceData
    (X : I.InitializationOSExecutionData) :
    I.InitializationOrderedTraceData where
  originalHole := X.originalHole
  trace source := (X.execution source).toOrderedSearchTrace
  commonPath_entry_eq := by
    intro source source' i j hpair hpath
    change (X.execution source).entry i =
      (X.execution source').entry j
    change (X.execution source).path i =
      (X.execution source').path j at hpath
    calc
      (X.execution source).entry i =
          X.canonicalEntry (I.pairing source)
            ((X.execution source).path i) :=
        X.entry_eq_canonical source i
      _ = X.canonicalEntry (I.pairing source')
            ((X.execution source').path j) := by
        rw [hpair, hpath]
      _ = (X.execution source').entry j :=
        (X.entry_eq_canonical source' j).symm

end InitializationOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
