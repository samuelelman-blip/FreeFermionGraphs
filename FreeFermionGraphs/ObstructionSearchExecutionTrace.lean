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
derived from the Definition 19 endpoint colors, rather than stored as a
pairwise conclusion.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G}

/-- The first introduced vertex is an endpoint of the complete alternating
path block, so it anticommutes with that path. -/
theorem firstIntroduced_anticommutesWith
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData) :
    D.path.AnticommutesWith
      (D.deformation.step D.firstIndex).introduced := by
  let L := F.neighborhood.pathOrder
  let first := L.introducedPathIndex D.firstIndex
  let next := L.removedPathIndex D.firstIndex
  have hfirst : first.val = 0 := by
    simpa [first, ConcretePathDeformation.firstIndex] using
      L.introduced_index_val D.firstIndex
  have hnext : next.val = 1 := by
    simpa [next, ConcretePathDeformation.firstIndex] using
      L.removed_index_val D.firstIndex
  have hadj :
      G.Adj (D.path.vertex first) (D.path.vertex next) := by
    apply (D.path.adj_iff first next).2
    left
    omega
  have hanti : D.path.AnticommutesWith (D.path.vertex first) :=
    D.path.anticommutesWith_of_unique_neighbor hadj (by
      intro q hq
      have hindices := (D.path.adj_iff first q).1 hq
      apply Fin.ext
      rcases hindices with hforward | hbackward <;> omega)
  simpa only [first, L.introduced_eq] using hanti

/-- Equal carriers of two complete Definition 19 path blocks have the same
oriented first introduced endpoint.  The only other possible endpoint is
the terminal removed vertex in `C_a`; the first introduced vertex lies in
the prime `C'_c` class and therefore cannot be that endpoint. -/
theorem firstIntroduced_eq_of_path_range_eq
    (D E : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (H : E.FullDefinition19Lemma11AData)
    (hpath : Set.range D.path.vertex = Set.range E.path.vertex) :
    (D.deformation.step D.firstIndex).introduced =
      (E.deformation.step E.firstIndex).introduced := by
  let LD := F.neighborhood.pathOrder
  let LE := H.neighborhood.pathOrder
  let dFirst := LD.introducedPathIndex D.firstIndex
  have hdFirst :
      D.path.vertex dFirst =
        (D.deformation.step D.firstIndex).introduced := by
    exact LD.introduced_eq D.firstIndex
  have hmemE :
      (D.deformation.step D.firstIndex).introduced ∈
        Set.range E.path.vertex := by
    rw [← hpath]
    exact ⟨dFirst, hdFirst⟩
  have hantiD := D.firstIntroduced_anticommutesWith F
  have hantiE :
      E.path.AnticommutesWith
        (D.deformation.step D.firstIndex).introduced := by
    simpa only [IndexedInducedPath.AnticommutesWith, hpath] using hantiD
  obtain ⟨q, hq, hendpoint⟩ :=
    E.path.endpoint_of_mem_range_of_anticommutesWith hmemE hantiE
  rcases hendpoint with hfirst | hlast
  · have hqFirst : q = LE.introducedPathIndex E.firstIndex := by
      apply Fin.ext
      rw [LE.introduced_index_val]
      simpa [ConcretePathDeformation.firstIndex] using hfirst
    calc
      (D.deformation.step D.firstIndex).introduced =
          E.path.vertex q := hq.symm
      _ = E.path.vertex (LE.introducedPathIndex E.firstIndex) := by
        rw [hqFirst]
      _ = (E.deformation.step E.firstIndex).introduced :=
        LE.introduced_eq E.firstIndex
  · exfalso
    have hdPrime :
        (D.deformation.step D.firstIndex).introduced ∈ Cprime := by
      exact F.neighborhood.primeHole.introduced_mem D.firstIndex
    have hdCc :
        (D.deformation.step D.firstIndex).introduced ∈ O.Cc := by
      exact
        (F.neighborhood.mechanical.stepGeometry D.firstIndex).base.introduced_cc
    have hdNotCa :
        (D.deformation.step D.firstIndex).introduced ∉ O.Ca :=
      (F.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        hdPrime hdCc).1
    have heLastCa :
        (E.deformation.step E.lastIndex).before.vertex
            (E.deformation.step E.lastIndex).removedIndex ∈ O.Ca :=
      (H.neighborhood.mechanical.stepGeometry E.lastIndex).removed_ca
    have hlastVertex := H.lastPathVertex_eq_terminalRemoved q hlast
    apply hdNotCa
    rw [← hq, hlastVertex]
    exact heLastCa

/-- Pairing-indexed form of oriented path equality. -/
theorem firstIntroduced_eq_of_pairing_eq
    {p q : PairingType}
    (D : ConcretePathDeformation (families p) Cprime)
    (E : ConcretePathDeformation (families q) Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (H : E.FullDefinition19Lemma11AData)
    (hpq : p = q)
    (hpath : Set.range D.path.vertex = Set.range E.path.vertex) :
    (D.deformation.step D.firstIndex).introduced =
      (E.deformation.step E.firstIndex).introduced := by
  subst q
  exact D.firstIntroduced_eq_of_path_range_eq E F H hpath

end ConcretePathDeformation

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

/-- Concrete initialized executions for every source.  No common-path
orientation certificate is stored: Definition 19 forces the first introduced
endpoint of a path carrier to be unique. -/
structure InitializationOSExecutionData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  execution : ∀ source : I.Node,
    OrderedOSExecution I source originalHole

namespace InitializationOSExecutionData

/-- The local executions and the derived endpoint orientation construct all
ordered trace data required by Lemma 14(iii). -/
noncomputable def toInitializationOrderedTraceData
    (X : I.InitializationOSExecutionData) :
    I.InitializationOrderedTraceData where
  originalHole := X.originalHole
  trace source := (X.execution source).toOrderedSearchTrace
  commonPath_entry_eq := by
    intro source source' i j hpair hpath
    let A :=
      (X.execution source).history.witness
        ((X.execution source).path_mem i)
    let B :=
      (X.execution source').history.witness
        ((X.execution source').path_mem j)
    have hblockPath :
        Set.range A.block.path.vertex =
          Set.range B.block.path.vertex := by
      calc
        Set.range A.block.path.vertex =
            (X.execution source).path i := A.path_eq
        _ = (X.execution source').path j := hpath
        _ = Set.range B.block.path.vertex := B.path_eq.symm
    have hfirst :=
      A.block.firstIntroduced_eq_of_pairing_eq B.block
        A.context.currentData B.context.currentData hpair hblockPath
    change
      (X.execution source).entry i =
        (X.execution source').entry j
    simpa only [OrderedOSExecution.entry, A, B] using hfirst

end InitializationOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
