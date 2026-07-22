import FreeFermionGraphs.ObstructionSearchTerminalSameClone

/-!
# Lemma 14(iv): the distinct-clone terminal case

The second terminal case in the manuscript begins with distinct clone centres
for the common obstruction target.  Its neighborhood propagation ends with
four explicitly identified vertices forming a claw.  This module isolates
that final graph-theoretic contradiction and combines it with the common-clone
case.

The resulting pairwise theorem keeps the remaining vertex identifications and
inequalities produced by the long obstruction-search propagation explicit.
It now ties the preceding terminal vertex to a concrete first block of one of
the two incoming executions, and ties the alternative clone centre to the
manuscript relation `j'' ≺_C v''`.  Lemma 11(a), the clone relation, and the
indexed-hole cycle then derive both exact neighbourhood bounds and all three
leaf nonedges of the eventual claw.  The theorem does not assume that the
target is an endpoint.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The final local configuration in the distinct-clone branch of
Lemma 14(iv).  In the manuscript these vertices are the center `u'` and the
three leaves `j_{p-2}`, `w'`, and `v''` (with the exact adornments determined
by the two incoming searches). -/
structure DistinctCloneInteriorGeometry (G : SimpleGraph V) where
  center : V
  previous : V
  originalNeighbor : V
  otherClone : V
  adj_previous : G.Adj center previous
  adj_originalNeighbor : G.Adj center originalNeighbor
  adj_otherClone : G.Adj center otherClone
  previous_ne_originalNeighbor : previous ≠ originalNeighbor
  previous_ne_otherClone : previous ≠ otherClone
  originalNeighbor_ne_otherClone : originalNeighbor ≠ otherClone
  previous_not_adj_originalNeighbor : ¬G.Adj previous originalNeighbor
  previous_not_adj_otherClone : ¬G.Adj previous otherClone
  originalNeighbor_not_adj_otherClone : ¬G.Adj originalNeighbor otherClone

namespace DistinctCloneInteriorGeometry

/-- The terminal distinct-clone configuration contradicts claw-freeness. -/
theorem false_of_clawFree
    (X : DistinctCloneInteriorGeometry G)
    (hclaw : G.IsClawFree) : False := by
  rcases hclaw X.adj_previous X.adj_originalNeighbor X.adj_otherClone
      X.previous_ne_originalNeighbor X.previous_ne_otherClone
      X.originalNeighbor_ne_otherClone with
    hpreviousOriginal | hpreviousClone | horiginalClone
  · exact X.previous_not_adj_originalNeighbor hpreviousOriginal
  · exact X.previous_not_adj_otherClone hpreviousClone
  · exact X.originalNeighbor_not_adj_otherClone horiginalClone

end DistinctCloneInteriorGeometry

/-- Two distinct known neighbours exhaust the neighbours of a vertex on an
indexed hole when its external degree is two.  This is the set-cardinality
step used twice in the final distinct-clone argument. -/
theorem IndexedInducedHole.neighbor_eq_of_externalDegree_two
    (C : IndexedInducedHole G) {u x y : V}
    (hdegree : C.externalDegree u = 2)
    (hxMem : x ∈ Set.range C.vertex)
    (hyMem : y ∈ Set.range C.vertex)
    (hxy : x ≠ y)
    (hux : G.Adj u x)
    (huy : G.Adj u y)
    {z : V}
    (hzMem : z ∈ Set.range C.vertex)
    (huz : G.Adj u z) :
    z = x ∨ z = y := by
  obtain ⟨ix, rfl⟩ := hxMem
  obtain ⟨iy, rfl⟩ := hyMem
  obtain ⟨iz, rfl⟩ := hzMem
  have hixiy : ix ≠ iy := by
    intro hEq
    exact hxy (congrArg C.vertex hEq)
  have hpairSubset :
      ({ix, iy} : Set (Fin C.card)) ⊆ C.neighborIndexSet u := by
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact hux
    · have hqiy : q = iy := Set.mem_singleton_iff.mp hq
      subst q
      exact huy
  have hpairCard :
      ({ix, iy} : Set (Fin C.card)).ncard = 2 := by
    simp [hixiy]
  have hneighborCard : (C.neighborIndexSet u).ncard = 2 := by
    simpa [IndexedInducedHole.externalDegree] using hdegree
  have hpairEq :
      ({ix, iy} : Set (Fin C.card)) = C.neighborIndexSet u :=
    Set.eq_of_subset_of_ncard_le hpairSubset (by
      rw [hpairCard, hneighborCard])
  have hiz : iz ∈ ({ix, iy} : Set (Fin C.card)) := by
    rw [hpairEq]
    exact huz
  rcases Set.mem_insert_iff.mp hiz with hiz | hiz
  · left
    exact congrArg C.vertex hiz
  · right
    exact congrArg C.vertex (Set.mem_singleton_iff.mp hiz)

/-- The final neighbourhood information obtained at the end of the
distinct-clone propagation in Lemma 14(iv).

In the manuscript, `center`, `previous`, `propagatedNeighbor`, and
`otherClone` are respectively `u'`, `j_{p-2}`, `w'` (printed as `w''` in the
last displayed claw), and `v''`.  The vertices `b0` and `b1` are the two
original-hole neighbours of `v''`.  The separately named
`previousNeighbor0` and `previousNeighbor1` are the two already established
original-hole neighbours of `j_{p-2}`; the paper does not identify that pair
with `b0,b1`.

Unlike `DistinctCloneInteriorGeometry`, this structure does not contain any
of the three nonedges required by a claw, or either exact-neighbourhood
function.  Those conclusions follow from the two degree-two facts and the
displayed neighbours obtained by the preceding propagation. -/
structure DistinctCloneFinalNeighborhood (G : SimpleGraph V) where
  originalHole : IndexedInducedHole G
  center : V
  previous : V
  propagatedNeighbor : V
  otherClone : V
  previousNeighbor0 : V
  previousNeighbor1 : V
  b0 : V
  b1 : V
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  adj_otherClone : G.Adj center otherClone
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  previous_ne_otherClone : previous ≠ otherClone
  propagatedNeighbor_ne_otherClone : propagatedNeighbor ≠ otherClone
  previousNeighbor0_mem_originalHole :
    previousNeighbor0 ∈ Set.range originalHole.vertex
  previousNeighbor1_mem_originalHole :
    previousNeighbor1 ∈ Set.range originalHole.vertex
  previousNeighbor0_ne_previousNeighbor1 :
    previousNeighbor0 ≠ previousNeighbor1
  adj_previousNeighbor0 : G.Adj previous previousNeighbor0
  adj_previousNeighbor1 : G.Adj previous previousNeighbor1
  previous_externalDegree_two : originalHole.externalDegree previous = 2
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠ previousNeighbor0
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠ previousNeighbor1
  otherClone_ne_previousNeighbor0 : otherClone ≠ previousNeighbor0
  otherClone_ne_previousNeighbor1 : otherClone ≠ previousNeighbor1
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range originalHole.vertex
  otherClone_mem_originalHole :
    otherClone ∈ Set.range originalHole.vertex
  b0_mem_originalHole : b0 ∈ Set.range originalHole.vertex
  b1_mem_originalHole : b1 ∈ Set.range originalHole.vertex
  b0_ne_b1 : b0 ≠ b1
  adj_otherClone_b0 : G.Adj otherClone b0
  adj_otherClone_b1 : G.Adj otherClone b1
  propagatedNeighbor_ne_b0 : propagatedNeighbor ≠ b0
  propagatedNeighbor_ne_b1 : propagatedNeighbor ≠ b1

namespace DistinctCloneFinalNeighborhood

/-- The two named neighbours of the preceding terminal vertex exhaust its
original-hole neighbourhood. -/
theorem previous_originalHole_neighbors
    (X : DistinctCloneFinalNeighborhood G) {x : V}
    (hxMem : x ∈ Set.range X.originalHole.vertex)
    (hxAdj : G.Adj X.previous x) :
    x = X.previousNeighbor0 ∨ x = X.previousNeighbor1 :=
  X.originalHole.neighbor_eq_of_externalDegree_two
    X.previous_externalDegree_two
    X.previousNeighbor0_mem_originalHole
    X.previousNeighbor1_mem_originalHole
    X.previousNeighbor0_ne_previousNeighbor1
    X.adj_previousNeighbor0 X.adj_previousNeighbor1 hxMem hxAdj

/-- Since `otherClone` is itself an original-hole vertex, its external degree
on that hole is two. -/
theorem otherClone_externalDegree_two
    (X : DistinctCloneFinalNeighborhood G) :
    X.originalHole.externalDegree X.otherClone = 2 := by
  obtain ⟨i, hi⟩ := X.otherClone_mem_originalHole
  rw [← hi]
  exact X.originalHole.externalDegree_vertex_eq_two i

/-- The displayed vertices `b0,b1` exhaust the original-hole neighbours of
the alternative clone. -/
theorem otherClone_originalHole_neighbors
    (X : DistinctCloneFinalNeighborhood G) {x : V}
    (hxMem : x ∈ Set.range X.originalHole.vertex)
    (hxAdj : G.Adj X.otherClone x) :
    x = X.b0 ∨ x = X.b1 :=
  X.originalHole.neighbor_eq_of_externalDegree_two
    X.otherClone_externalDegree_two X.b0_mem_originalHole
    X.b1_mem_originalHole X.b0_ne_b1 X.adj_otherClone_b0
    X.adj_otherClone_b1 hxMem hxAdj

/-- The propagated original-hole neighbour is not adjacent to the preceding
terminal vertex, because that vertex has no original-hole neighbours beyond
its two separately named neighbours. -/
theorem previous_not_adj_propagatedNeighbor
    (X : DistinctCloneFinalNeighborhood G) :
    ¬G.Adj X.previous X.propagatedNeighbor := by
  intro h
  rcases X.previous_originalHole_neighbors
      X.propagatedNeighbor_mem_originalHole h with h0 | h1
  · exact X.propagatedNeighbor_ne_previousNeighbor0 h0
  · exact X.propagatedNeighbor_ne_previousNeighbor1 h1

/-- The preceding terminal vertex is not adjacent to the alternative clone
for the same reason. -/
theorem previous_not_adj_otherClone
    (X : DistinctCloneFinalNeighborhood G) :
    ¬G.Adj X.previous X.otherClone := by
  intro h
  rcases X.previous_originalHole_neighbors
      X.otherClone_mem_originalHole h with h0 | h1
  · exact X.otherClone_ne_previousNeighbor0 h0
  · exact X.otherClone_ne_previousNeighbor1 h1

/-- The propagated neighbour is not adjacent to the alternative clone,
whose only neighbours in the original hole are `b0` and `b1`. -/
theorem propagatedNeighbor_not_adj_otherClone
    (X : DistinctCloneFinalNeighborhood G) :
    ¬G.Adj X.propagatedNeighbor X.otherClone := by
  intro h
  rcases X.otherClone_originalHole_neighbors
      X.propagatedNeighbor_mem_originalHole h.symm with h0 | h1
  · exact X.propagatedNeighbor_ne_b0 h0
  · exact X.propagatedNeighbor_ne_b1 h1

/-- The paper's final neighbourhood bounds construct the explicit local claw
geometry; none of its leaf nonedges is supplied separately. -/
def toInteriorGeometry
    (X : DistinctCloneFinalNeighborhood G) :
    DistinctCloneInteriorGeometry G where
  center := X.center
  previous := X.previous
  originalNeighbor := X.propagatedNeighbor
  otherClone := X.otherClone
  adj_previous := X.adj_previous
  adj_originalNeighbor := X.adj_propagatedNeighbor
  adj_otherClone := X.adj_otherClone
  previous_ne_originalNeighbor := X.previous_ne_propagatedNeighbor
  previous_ne_otherClone := X.previous_ne_otherClone
  originalNeighbor_ne_otherClone := X.propagatedNeighbor_ne_otherClone
  previous_not_adj_originalNeighbor :=
    X.previous_not_adj_propagatedNeighbor
  previous_not_adj_otherClone := X.previous_not_adj_otherClone
  originalNeighbor_not_adj_otherClone :=
    X.propagatedNeighbor_not_adj_otherClone

/-- The final distinct-clone neighbourhood contradicts claw-freeness. -/
theorem false_of_clawFree
    (X : DistinctCloneFinalNeighborhood G)
    (hclaw : G.IsClawFree) : False :=
  X.toInteriorGeometry.false_of_clawFree hclaw

end DistinctCloneFinalNeighborhood

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- A concrete first-block `Definition 20` witness with final degree three
has degree two on the initialized original hole.

This is the exact numerical implication used near the end of the
distinct-clone branch of Lemma 14(iv): membership in `U^{(r,1)}` increases
the degree by one, while the fact that this is the first block identifies its
initial hole with the original hole of the initialized search. -/
theorem originalDegree_two_of_firstBlock_dependent
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hclaw : G.IsClawFree)
    (q : Fin X.blockCount)
    (hfirst :
      ∃ F : (X.concreteBlock q).FullDefinition19Lemma11AData,
        X.blockContext q =
          ConcretePathDeformation.Lemma11AHistoryContext.first F)
    {s : Nat} {u : V}
    (hu : u ∈ (X.concreteBlock q).dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : (X.concreteBlock q).path.AnticommutesWith u)
    (hthree : (X.concreteBlock q).finalHole.externalDegree u = 3) :
    originalHole.externalDegree u = 2 := by
  have hlocal :=
    ((X.concreteBlock q).lemma11a_complete
      (X.blockContext q) hclaw huPrime hanti).1
  have hdegree := hlocal.mp ⟨s, hu⟩
  have hinitial :
      (X.concreteBlock q).initialHole.externalDegree u = 2 := by
    omega
  obtain ⟨F, hF⟩ := hfirst
  have hroot := X.blockContext_originalHole q
  rw [hF] at hroot
  have hinitialHole :
      (X.concreteBlock q).initialHole = originalHole := by
    simpa [ConcretePathDeformation.Lemma11AHistoryContext.originalHole]
      using hroot
  rw [← hinitialHole]
  exact hinitial

end OrderedOSExecution

/-- Paper-level inputs remaining after the final distinct-clone propagation.

Unlike `DistinctCloneFinalNeighborhood`, this structure does not store either
degree-two conclusion, any hole-membership field for the named neighbours,
or any of the three eventual claw nonedges.  The preceding terminal vertex is
tied to a concrete first block of one initialized `OS` execution.  The other
clone is the actual centre of a single-vertex deformation of the common
target on the same initialized original hole. -/
structure DistinctClonePropagationData
    (T : I.InitializationTerminalCoreData)
    (source target : I.Node) where
  incoming : I.graph.Arc source target
  dependentBlockIndex :
    Fin (T.executionTrace.execution source).blockCount
  dependentBlock_is_first :
    ∃ F :
        ((T.executionTrace.execution source).concreteBlock
          dependentBlockIndex).FullDefinition19Lemma11AData,
      (T.executionTrace.execution source).blockContext
          dependentBlockIndex =
        ConcretePathDeformation.Lemma11AHistoryContext.first F
  dependentStep : Nat
  previous : V
  previous_mem_dependent :
    previous ∈
      ((T.executionTrace.execution source).concreteBlock
        dependentBlockIndex).dependentAt dependentStep
  previous_mem_prime : previous ∈ Cprime
  previous_anticommutes :
    ((T.executionTrace.execution source).concreteBlock
      dependentBlockIndex).path.AnticommutesWith previous
  previous_finalDegree_three :
    ((T.executionTrace.execution source).concreteBlock
      dependentBlockIndex).finalHole.externalDegree previous = 3
  center : V
  propagatedNeighbor : V
  cloneIndex : Fin T.executionTrace.originalHole.card
  target_clone :
    T.executionTrace.originalHole.SingleVertexDeformation
      (target : V) cloneIndex
  previousNeighbor0Index : Fin T.executionTrace.originalHole.card
  previousNeighbor1Index : Fin T.executionTrace.originalHole.card
  previousNeighbor0_ne_previousNeighbor1 :
    previousNeighbor0Index ≠ previousNeighbor1Index
  adj_previousNeighbor0 :
    G.Adj previous
      (T.executionTrace.originalHole.vertex previousNeighbor0Index)
  adj_previousNeighbor1 :
    G.Adj previous
      (T.executionTrace.originalHole.vertex previousNeighbor1Index)
  cloneNeighbor0Index : Fin T.executionTrace.originalHole.card
  cloneNeighbor1Index : Fin T.executionTrace.originalHole.card
  cloneNeighbor0_ne_cloneNeighbor1 :
    cloneNeighbor0Index ≠ cloneNeighbor1Index
  cloneNeighbor0_cyclic :
    CyclicAdjacent cloneIndex cloneNeighbor0Index
  cloneNeighbor1_cyclic :
    CyclicAdjacent cloneIndex cloneNeighbor1Index
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  adj_cloneCenter :
    G.Adj center (T.executionTrace.originalHole.vertex cloneIndex)
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  previous_ne_cloneCenter :
    previous ≠ T.executionTrace.originalHole.vertex cloneIndex
  propagatedNeighbor_ne_cloneCenter :
    propagatedNeighbor ≠ T.executionTrace.originalHole.vertex cloneIndex
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex previousNeighbor0Index
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex previousNeighbor1Index
  cloneCenter_ne_previousNeighbor0 :
    T.executionTrace.originalHole.vertex cloneIndex ≠
      T.executionTrace.originalHole.vertex previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    T.executionTrace.originalHole.vertex cloneIndex ≠
      T.executionTrace.originalHole.vertex previousNeighbor1Index
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range T.executionTrace.originalHole.vertex
  propagatedNeighbor_ne_cloneNeighbor0 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex cloneNeighbor0Index
  propagatedNeighbor_ne_cloneNeighbor1 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex cloneNeighbor1Index

namespace DistinctClonePropagationData

variable {T : I.InitializationTerminalCoreData}
  {source target : I.Node}

/-- The common obstruction target is adjacent to its displayed alternative
clone centre, directly from the manuscript relation `j'' ≺_C v''`. -/
theorem target_adj_cloneCenter
    (X : DistinctClonePropagationData T source target) :
    G.Adj (target : V)
      (T.executionTrace.originalHole.vertex X.cloneIndex) :=
  X.target_clone.adj_clone

/-- The predecessor's original-hole degree is a consequence of the literal
first-block dependent-set witness, rather than a terminal certificate. -/
theorem previous_originalDegree_two
    (X : DistinctClonePropagationData T source target)
    (hclaw : G.IsClawFree) :
    T.executionTrace.originalHole.externalDegree X.previous = 2 :=
  OrderedOSExecution.originalDegree_two_of_firstBlock_dependent
    (T.executionTrace.execution source)
    hclaw X.dependentBlockIndex X.dependentBlock_is_first
    X.previous_mem_dependent X.previous_mem_prime
    X.previous_anticommutes X.previous_finalDegree_three

/-- Construct the final neighborhood object from the execution witness and
the indexed clone geometry. -/
def toFinalNeighborhood
    (X : DistinctClonePropagationData T source target)
    (hclaw : G.IsClawFree) :
    DistinctCloneFinalNeighborhood G where
  originalHole := T.executionTrace.originalHole
  center := X.center
  previous := X.previous
  propagatedNeighbor := X.propagatedNeighbor
  otherClone := T.executionTrace.originalHole.vertex X.cloneIndex
  previousNeighbor0 :=
    T.executionTrace.originalHole.vertex X.previousNeighbor0Index
  previousNeighbor1 :=
    T.executionTrace.originalHole.vertex X.previousNeighbor1Index
  b0 := T.executionTrace.originalHole.vertex X.cloneNeighbor0Index
  b1 := T.executionTrace.originalHole.vertex X.cloneNeighbor1Index
  adj_previous := X.adj_previous
  adj_propagatedNeighbor := X.adj_propagatedNeighbor
  adj_otherClone := X.adj_cloneCenter
  previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
  previous_ne_otherClone := X.previous_ne_cloneCenter
  propagatedNeighbor_ne_otherClone := X.propagatedNeighbor_ne_cloneCenter
  previousNeighbor0_mem_originalHole :=
    ⟨X.previousNeighbor0Index, rfl⟩
  previousNeighbor1_mem_originalHole :=
    ⟨X.previousNeighbor1Index, rfl⟩
  previousNeighbor0_ne_previousNeighbor1 := by
    intro h
    exact X.previousNeighbor0_ne_previousNeighbor1
      (T.executionTrace.originalHole.injective h)
  adj_previousNeighbor0 := X.adj_previousNeighbor0
  adj_previousNeighbor1 := X.adj_previousNeighbor1
  previous_externalDegree_two := X.previous_originalDegree_two hclaw
  propagatedNeighbor_ne_previousNeighbor0 :=
    X.propagatedNeighbor_ne_previousNeighbor0
  propagatedNeighbor_ne_previousNeighbor1 :=
    X.propagatedNeighbor_ne_previousNeighbor1
  otherClone_ne_previousNeighbor0 := X.cloneCenter_ne_previousNeighbor0
  otherClone_ne_previousNeighbor1 := X.cloneCenter_ne_previousNeighbor1
  propagatedNeighbor_mem_originalHole :=
    X.propagatedNeighbor_mem_originalHole
  otherClone_mem_originalHole := ⟨X.cloneIndex, rfl⟩
  b0_mem_originalHole := ⟨X.cloneNeighbor0Index, rfl⟩
  b1_mem_originalHole := ⟨X.cloneNeighbor1Index, rfl⟩
  b0_ne_b1 := by
    intro h
    exact X.cloneNeighbor0_ne_cloneNeighbor1
      (T.executionTrace.originalHole.injective h)
  adj_otherClone_b0 :=
    (T.executionTrace.originalHole.adj_iff _ _).2 X.cloneNeighbor0_cyclic
  adj_otherClone_b1 :=
    (T.executionTrace.originalHole.adj_iff _ _).2 X.cloneNeighbor1_cyclic
  propagatedNeighbor_ne_b0 := X.propagatedNeighbor_ne_cloneNeighbor0
  propagatedNeighbor_ne_b1 := X.propagatedNeighbor_ne_cloneNeighbor1

/-- The execution-level distinct-clone propagation contradicts
claw-freeness after all neighborhood and nonedge facts are derived. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationData T source target)
    (hclaw : G.IsClawFree) : False :=
  (X.toFinalNeighborhood hclaw).false_of_clawFree hclaw

end DistinctClonePropagationData

/-- The two local alternatives obtained by the manuscript's comparison of
the clone centres in the terminal holes. -/
inductive TwoIncomingInteriorGeometry
    (T : I.InitializationTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometry T source source' target
  | distinctClone :
      (Nonempty (DistinctClonePropagationData T source target) ∨
        Nonempty (DistinctClonePropagationData T source' target)) →
      TwoIncomingInteriorGeometry T source source' target

/-- Pairwise terminal analysis from the concrete `OS` trace.  The field is
only requested under the negation of both endpoint alternatives.  It returns
either the same-clone neighborhood or the remaining distinct-clone propagation
data tied to one of the two incoming executions. -/
structure TwoIncomingTerminalClawAnalysis
    (T : I.InitializationTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        TwoIncomingInteriorGeometry T source source' target

namespace InitializationTerminalCoreData

/-- Both clone-centre alternatives contradict claw-freeness, so a common
target of two distinct incoming searches is one of their current terminal
endpoints. -/
theorem target_is_current_endpoint_of_twoIncoming_of_clawAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target) :
    ((T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V) ∨
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)) := by
  have hslots :
      T.currentSlot source target ≠ T.currentSlot source' target := by
    intro hslot
    exact hne (T.currentSlot_source_injective hclaw h h' hslot)
  by_cases hsource :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) = (target : V)
  · exact Or.inl hsource
  by_cases hsource' :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) = (target : V)
  · exact Or.inr hsource'
  rcases A.interiorGeometry hne h h' hsource hsource' with
      hsame | hdistinct
  · obtain ⟨X⟩ := hsame
    have hgeometry : Nonempty
        ((T.terminalPath target).SameCloneInteriorGeometry
          (target : V)) := by
      cases hslot : T.currentSlot source target <;>
          cases hslot' : T.currentSlot source' target
      · exact (hslots (hslot.trans hslot'.symm)).elim
      · exact X.toInteriorGeometry
          (by simpa [hslot] using hsource)
          (by simpa [hslot'] using hsource')
      · exact X.toInteriorGeometry
          (by simpa [hslot'] using hsource')
          (by simpa [hslot] using hsource)
      · exact (hslots (hslot.trans hslot'.symm)).elim
    obtain ⟨Y⟩ := hgeometry
    exact (Y.false_of_clawFree hclaw).elim
  · rcases hdistinct with ⟨⟨X⟩⟩ | ⟨⟨X⟩⟩
    · exact (X.false_of_clawFree hclaw).elim
    · exact (X.false_of_clawFree hclaw).elim

/-- Promote the terminal core to the complete certificate after proving the
two concrete interior-claw alternatives. -/
def toInitializationTerminalData_of_clawAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree) :
    I.InitializationTerminalData where
  toInitializationTerminalCoreData := T
  target_is_current_endpoint_of_twoIncoming := by
    intro source source' target hne h h'
    exact T.target_is_current_endpoint_of_twoIncoming_of_clawAnalysis
      A hclaw hne h h'

/-- Lemma 14 from the terminal core and the two explicit interior-claw
branches.  In particular, this theorem has no endpoint-alternative premise. -/
theorem lemma14_of_terminalClawAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalClawAnalysis T)
    (hclaw : G.IsClawFree) :
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
  exact InitializationTerminalData.lemma14_of_initializationTerminalData
    (T.toInitializationTerminalData_of_clawAnalysis A hclaw) hclaw

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
