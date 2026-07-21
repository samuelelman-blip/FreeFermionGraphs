import FreeFermionGraphs.Lemma11AEliminateEarlierAnti
import FreeFermionGraphs.Lemma11AThreeNeighborClone
import FreeFermionGraphs.Lemma11OppositePairing
import FreeFermionGraphs.Lemma11AEndpointPersistence

/-!
# Lemma 11(a.ii): full Definition 19 history

Lemma 11(a.ii) compares the current path block with the original hole.  The
local block data alone cannot represent that comparison, so this module
records the finite prefix of earlier Definition 19 blocks, the exact
Corollary-11 non-overlap statement, and the Corollary-10 persistence of
earlier path endpoints.  From those geometric facts the endpoint conclusion
of Corollary 12 and the no-earlier-anticommutation invariant are theorems,
not additional assumptions.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Every concrete path block is one of the path components recorded by its
fixed-pairing family. -/
theorem path_range_mem
    (D : ConcretePathDeformation O Cprime) :
    Set.range D.path.vertex ∈ O.paths := by
  rw [← D.activePath_eq D.firstIndex]
  exact D.deformation.activePath_mem D.firstIndex

/-- The cross-path Definition 19 data used in Lemma 11(a.ii).  The two
global fields are exactly the paper's Corollary 11 non-overlap conclusion
and Corollary 10 endpoint persistence; neither field states a degree or
commutation conclusion of Lemma 11. -/
structure FullDefinition19Lemma11AHistoryData
    (D : ConcretePathDeformation O Cprime) where
  current : D.FullDefinition19Lemma11AData
  history : PathBlockHistory (O := O) (Cprime := Cprime)
  priorCount : Nat
  priorCount_pos : 0 < priorCount
  prior : ∀ r : Nat, (history.block r).FullDefinition19Lemma11AData
  final_before_current :
    Set.range (history.block (priorCount - 1)).finalHole.vertex =
      Set.range D.initialHole.vertex
  corollary11 : O.Corollary11Property O
    (fun r => (history.block r).path)
    (fun _ => D.path)
    (fun r => (history.block r).dependentAt)
    (fun _ => D.dependentAt)
  priorPath_ne_current : ∀ r : Nat, r < priorCount →
    Set.range (history.block r).path.vertex ≠ Set.range D.path.vertex
  priorPath_pairwise : ∀ r q : Nat,
    r < priorCount → q < priorCount → r ≠ q →
      Set.range (history.block r).path.vertex ≠
        Set.range (history.block q).path.vertex
  earlierFirstIntroduced_uniquePath : ∀ r : Nat, r < priorCount →
    O.IsUniqueContainingPath
      ((history.block r).deformation.step
        (history.block r).firstIndex).introduced
      (Set.range (history.block r).path.vertex)

/-- Corollary 10 makes the first introduced vertex of an earlier path unique
to that path.  Since all later paths in the finite Definition 19 history are
distinct, it is never removed by them; carrier transport then puts it on the
initial hole of the current block. -/
theorem earlierFirstIntroduced_mem_currentInitial
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    {r : Nat} (hr : r < X.priorCount) :
    ((X.history.block r).deformation.step
      (X.history.block r).firstIndex).introduced ∈
      Set.range D.initialHole.vertex := by
  let A := X.history.block r
  let v : V := (A.deformation.step A.firstIndex).introduced
  let last : Nat := X.priorCount - 1
  have hlastLt : last < X.priorCount := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hrLast : r ≤ last := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hvPath : v ∈ Set.range A.path.vertex := by
    rw [← A.activePath_eq A.firstIndex]
    exact (A.deformation.step A.firstIndex).introduced_mem_activePath
  have hvFinal : v ∈ Set.range A.finalHole.vertex := by
    exact A.introduced_mem_finalHole
      (X.prior r).neighborhood.pathOrder A.firstIndex
  have hnotLater : ∀ q : Nat, r < q → q ≤ last →
      v ∉ Set.range (X.history.block q).path.vertex := by
    intro q hrq hqLast hvq
    have hEq :
        Set.range (X.history.block q).path.vertex =
          Set.range A.path.vertex :=
      (X.earlierFirstIntroduced_uniquePath r hr).2.2
        ((X.history.block q).path_range_mem) hvq
    exact (X.priorPath_pairwise r q hr
      (by omega) (by omega)) hEq.symm
  have hvLast : v ∈ Set.range (X.history.block last).finalHole.vertex :=
    X.history.mem_finalHole_of_mem_finalHole_through
      hrLast (by simpa [A] using hvFinal) (by
        intro q hrq hqLast
        simpa [A, v] using hnotLater q hrq hqLast)
  rw [X.final_before_current] at hvLast
  simpa [A, v] using hvLast

/-- Corollary 11 supplies the no-shared-dependent premise for each earlier
path, and the completed local path-block equivalence turns it into the
Corollary-12 endpoint alternative. -/
theorem earlierAnticommutingEndpointRule_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.EarlierAnticommutingEndpointRule
      X.history X.priorCount u := by
  intro r hr hantiEarlier
  have hnoShared :
      ¬SharedDependentAnticommutingWitness
        (X.history.block r).path D.path
        (X.history.block r).dependentAt D.dependentAt :=
    X.corollary11.2 (r := r) (g := 0)
      ((X.history.block r).path_range_mem)
      D.path_range_mem
      (X.priorPath_ne_current r hr)
  exact
    (X.history.block r).anticommutes_endpoint_of_noSharedDependent
      D (X.prior r) X.current hclaw hnoShared
      huPrime hantiEarlier hanti

/-- Corollary 10's persistence field excludes the earlier endpoint case of
Corollary 12, while Definition 20 membership excludes the current endpoint.
Thus every earlier path in the finite Definition 19 prefix commutes with the
current dependent vertex. -/
theorem no_earlierAnticommutation_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (huOutsideCurrentInitial : u ∉ Set.range D.initialHole.vertex) :
    ∀ r : Nat, r < X.priorCount →
      ¬(X.history.block r).path.AnticommutesWith u := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      X.current hclaw huPrime hanti).mp ⟨s, hu⟩
  have hendpoint :=
    D.earlierAnticommutingEndpointRule_of_fullDefinition19History
      X hclaw huPrime hanti
  intro r hr hantiEarlier
  rcases hendpoint r hr hantiEarlier with hprevious | hcurrent
  · apply huOutsideCurrentInitial
    rw [hprevious]
    exact D.earlierFirstIntroduced_mem_currentInitial X hr
  · exact (hlocal.1 hcurrent).elim

/-- The degree equivalence in Lemma 11(a.ii), now with the earlier-path
commutation condition derived from the Definition 19 history rather than
passed in as a raw hypothesis. -/
theorem lemma11aii_degree_iff_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (horiginalOutside :
      u ∉ Set.range (X.history.block 0).initialHole.vertex)
    (hcurrentInitialOutside : u ∉ Set.range D.initialHole.vertex) :
    D.finalHole.externalDegree u = 4 ↔
      (X.history.block 0).initialHole.externalDegree u = 3 := by
  have hno := D.no_earlierAnticommutation_of_fullDefinition19History
    X hclaw hu huPrime hanti hcurrentInitialOutside
  have horiginalEven : Even (X.history.block 0).initialHole.card :=
    (X.prior 0).neighborhood.alternating.initialHole_even
  have hcurrentInitialEven : Even D.initialHole.card :=
    X.current.neighborhood.alternating.initialHole_even
  apply D.finalDegree_four_iff_originalDegree_three_of_noEarlierAnticommutation_through
    X.current hclaw hu huPrime hanti X.history
      (X.priorCount - 1) X.final_before_current
  · intro r hr
    apply hno r
    have hpos := X.priorCount_pos
    omega
  · exact horiginalOutside
  · exact hcurrentInitialOutside
  · exact horiginalEven
  · exact hcurrentInitialEven

/-- Full degree-and-clone form of Lemma 11(a.ii).  The clone itself is
constructed from the original degree-three neighborhood; the remaining
`C_a` color identification is the final local color fact from the paper. -/
theorem lemma11aii_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    (σ : PairingType)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (horiginalOutside :
      u ∉ Set.range (X.history.block 0).initialHole.vertex)
    (hcurrentInitialOutside : u ∉ Set.range D.initialHole.vertex)
    (hcloneInCa : ∀ q : Fin (X.history.block 0).initialHole.card,
      (X.history.block 0).initialHole.SingleVertexDeformation u q →
        (X.history.block 0).initialHole.vertex q ∈ O.Ca)
    (huClass : u ∈ σ.classFromB O.Cc O.Cd) :
    D.finalHole.externalDegree u = 4 ↔
      (X.history.block 0).initialHole.externalDegree u = 3 ∧
        O.HasTypedClone σ.opposite (X.history.block 0).initialHole u := by
  have hdegree := D.lemma11aii_degree_iff_of_fullDefinition19History
    X hclaw hu huPrime hanti horiginalOutside hcurrentInitialOutside
  constructor
  · intro hfour
    have hthree := hdegree.mp hfour
    obtain ⟨q, hclone⟩ :=
      IndexedInducedHole.exists_singleVertexDeformation_of_externalDegree_eq_three
        (X.history.block 0).initialHole hclaw horiginalOutside hthree
    refine ⟨hthree, ?_⟩
    exact O.hasTypedClone_opposite σ (X.history.block 0).initialHole
      hclone (hcloneInCa q hclone) huClass
  · rintro ⟨hthree, _⟩
    exact hdegree.mpr hthree

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
