import FreeFermionGraphs.Lemma12ReverseStep

/-!
# The reverse clone criterion for Lemma 12

This module isolates the local step in the proof of Lemma 12.  A reverse
auxiliary hole is compared with the corresponding forward after-hole by the
constant symmetric-difference invariant from equations (C26)--(C27).  Lemma
13 then proves three facts without any path-end assumption:

* the forward introduced vertex lies on the reverse hole;
* the forward removed vertex lies outside the reverse hole;
* the closed reverse-hole neighbourhood of the introduced vertex is
  contained in the neighbourhood of the removed vertex.

Any neighbour in the other set difference is forced into
`C' \ C^(m)` and is outside the deformation boundary.  The path endpoint
and interior alternatives will eliminate precisely that residual case.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

open scoped symmDiff

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace FullDefinition19Deformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Concrete data for two consecutive replacements on the same alternating
Definition 19 path. -/
structure Lemma12Continuation
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount) where
  next : Fin F.deformation.stepCount
  consecutive : i.val + 1 = next.val
  samePath :
    (F.deformation.step next).activePath =
      (F.deformation.step i).activePath
  removed_adj_nextIntroduced :
    G.Adj
      ((F.deformation.step i).before.vertex
        (F.deformation.step i).removedIndex)
      (F.deformation.step next).introduced
  introduced_ne_nextIntroduced :
    (F.deformation.step i).introduced ≠
      (F.deformation.step next).introduced
  introduced_ne_nextRemoved :
    (F.deformation.step i).introduced ≠
      (F.deformation.step next).before.vertex
        (F.deformation.step next).removedIndex
  introduced_not_adj_nextIntroduced :
    ¬G.Adj
      (F.deformation.step i).introduced
      (F.deformation.step next).introduced
  introduced_not_adj_nextRemoved :
    ¬G.Adj
      (F.deformation.step i).introduced
      ((F.deformation.step next).before.vertex
        (F.deformation.step next).removedIndex)

/-- The remaining complete-Definition-19 data used by Lemma 12.

The endpoint alternative is component maximality: every prime-hole neighbour
of the terminal removed vertex is already on its active path.  The other
alternative gives the next alternating pair on that same path.  These are
the two path-specific inputs in the manuscript's endpoint and five-neighbour
arguments, rather than assumptions about the desired reverse clone. -/
structure Lemma12Definition19Data
    (F : FullDefinition19Deformation O Cprime) where
  primeHole : IndexedInducedHole G
  primeHole_carrier : Set.range primeHole.vertex = Cprime
  primeHole_even : Even primeHole.card
  removed_mem_original :
    ∀ i : Fin F.deformation.stepCount,
      (F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex ∈
        Set.range F.initialHole.vertex
  activePath_subset_boundary :
    ∀ i : Fin F.deformation.stepCount,
      Set.range (F.deformation.step i).activePath.vertex ⊆ F.boundary
  endpoint_or_continuation :
    ∀ i : Fin F.deformation.stepCount,
      (∀ {v : V}, v ∈ Cprime →
        G.Adj
          ((F.deformation.step i).before.vertex
            (F.deformation.step i).removedIndex) v →
        v ∈ Set.range (F.deformation.step i).activePath.vertex) ∨
      Nonempty (Lemma12Continuation F i)

/-- The introduced vertex of a forward step lies on any reverse auxiliary
hole satisfying the constant symmetric-difference invariant. -/
theorem introduced_mem_reverse_of_symmDiff
    (F : FullDefinition19Deformation O Cprime)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex) :
    (F.deformation.step i).introduced ∈ Set.range R.vertex := by
  let j : V := (F.deformation.step i).introduced
  have hjForward :
      j ∈ Set.range (F.deformation.step i).after.vertex :=
    (F.deformation.step i).introduced_mem_after
  by_contra hjReverse
  have hjLeft :
      j ∈ Set.range R.vertex ∆
        Set.range (F.deformation.step i).after.vertex :=
    Set.mem_symmDiff.mpr (Or.inr ⟨hjForward, hjReverse⟩)
  have hjPrimeTerminal :
      j ∈ Cprime ∆ Set.range F.terminalHole.vertex := by
    rw [← hsymm]
    exact hjLeft
  have hjNotBoundary := F.lemma13 hcriterion hjPrimeTerminal
  apply hjNotBoundary
  exact F.mem_boundary_iff.mpr ⟨i, Or.inl rfl⟩

/-- The removed vertex of a forward step is outside every corresponding
reverse auxiliary hole satisfying the symmetric-difference invariant. -/
theorem removed_not_mem_reverse_of_symmDiff
    (F : FullDefinition19Deformation O Cprime)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex) :
    (F.deformation.step i).before.vertex
        (F.deformation.step i).removedIndex ∉ Set.range R.vertex := by
  let k : V :=
    (F.deformation.step i).before.vertex
      (F.deformation.step i).removedIndex
  have hkForward :
      k ∉ Set.range (F.deformation.step i).after.vertex :=
    (F.deformation.step i).removed_not_mem_after
  intro hkReverse
  have hkLeft :
      k ∈ Set.range R.vertex ∆
        Set.range (F.deformation.step i).after.vertex :=
    Set.mem_symmDiff.mpr (Or.inl ⟨hkReverse, hkForward⟩)
  have hkPrimeTerminal :
      k ∈ Cprime ∆ Set.range F.terminalHole.vertex := by
    rw [← hsymm]
    exact hkLeft
  have hkNotBoundary := F.lemma13 hcriterion hkPrimeTerminal
  apply hkNotBoundary
  exact F.mem_boundary_iff.mpr ⟨i, Or.inr rfl⟩

/-- A reverse-hole vertex which is absent from the corresponding forward
after-hole lies on exactly one of the prime and terminal holes. -/
theorem mem_prime_symmDiff_terminal_of_reverse_not_forward
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex)
    {v : V}
    (hvReverse : v ∈ Set.range R.vertex)
    (hvForward :
      v ∉ Set.range (F.deformation.step i).after.vertex) :
    v ∈ Cprime ∆ Set.range F.terminalHole.vertex := by
  rw [← hsymm]
  exact Set.mem_symmDiff.mpr (Or.inl ⟨hvReverse, hvForward⟩)

/-- The criterion rules out a neighbour of the introduced vertex which is
not a neighbour of the removed vertex.  This is the first neighbourhood
inclusion in the proof of Lemma 12. -/
theorem introduced_neighbor_implies_removed_neighbor
    (F : FullDefinition19Deformation O Cprime)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex)
    {v : V}
    (hvReverse : v ∈ Set.range R.vertex)
    (hjv : G.Adj (F.deformation.step i).introduced v) :
    G.Adj
      ((F.deformation.step i).before.vertex
        (F.deformation.step i).removedIndex) v := by
  let S := F.deformation.step i
  let j : V := S.introduced
  let k : V := S.before.vertex S.removedIndex
  have hreverse : S.after.SingleVertexDeformation k S.removedIndex :=
    S.deformation.reverse
  have hcenter : S.after.vertex S.removedIndex = j := by
    simp [ConcreteDeformationStep.after, j]
  by_contra hkv
  have hvForward : v ∉ Set.range S.after.vertex := by
    rintro ⟨q, hqv⟩
    have hjq : G.Adj j (S.after.vertex q) := by
      simpa [j, hqv] using hjv
    have hkq : G.Adj k (S.after.vertex q) :=
      (hreverse.adj_iff q).2 (Or.inr (by
        rw [hcenter]
        exact hjq))
    exact hkv (by simpa [k, hqv] using hkq)
  have hvPrimeTerminal :=
    F.mem_prime_symmDiff_terminal_of_reverse_not_forward
      i R hsymm hvReverse (by simpa [S] using hvForward)
  have hvNotBoundary := F.lemma13 hcriterion hvPrimeTerminal
  rcases Set.mem_symmDiff.mp hvPrimeTerminal with
      ⟨hvPrime, hvNotTerminal⟩ | ⟨hvTerminal, _hvNotPrime⟩
  · have hvNeRemoved : v ≠ k := by
      intro hvk
      subst v
      exact F.removed_not_mem_reverse_of_symmDiff
        hcriterion i R hsymm hvReverse
    have hvDependent : v ∈ S.dependentSet := by
      exact ⟨hvPrime, by simpa [j] using hjv.symm,
        by simpa [k] using hvNeRemoved, by
          intro hvk'
          exact hkv (by simpa [k] using hvk'.symm)⟩
    apply hvNotTerminal
    apply hcriterion
    exact F.mem_dependentUnion_iff.mpr ⟨i, by simpa [S] using hvDependent⟩
  · exact hvForward
      (F.mem_after_of_mem_terminal_of_not_mem_boundary
        i hvTerminal hvNotBoundary)

/-- Classification of the only possible residual reverse-neighbourhood
mismatch.  Such a vertex is prime, absent from the terminal and current
forward holes, and outside `∂O`. -/
theorem residual_reverse_neighbor
    (F : FullDefinition19Deformation O Cprime)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex)
    {v : V}
    (hvReverse : v ∈ Set.range R.vertex)
    (hkv : G.Adj
      ((F.deformation.step i).before.vertex
        (F.deformation.step i).removedIndex) v)
    (hvIntroduced : v ≠ (F.deformation.step i).introduced)
    (hjv : ¬G.Adj (F.deformation.step i).introduced v) :
    v ∈ Cprime ∧
      v ∉ Set.range F.terminalHole.vertex ∧
      v ∉ F.boundary ∧
      v ∉ Set.range (F.deformation.step i).after.vertex := by
  let S := F.deformation.step i
  let j : V := S.introduced
  let k : V := S.before.vertex S.removedIndex
  have hreverse : S.after.SingleVertexDeformation k S.removedIndex :=
    S.deformation.reverse
  have hcenter : S.after.vertex S.removedIndex = j := by
    simp [ConcreteDeformationStep.after, j]
  have hvForward : v ∉ Set.range S.after.vertex := by
    rintro ⟨q, hqv⟩
    have hkq : G.Adj k (S.after.vertex q) := by
      simpa [k, hqv] using hkv
    rcases (hreverse.adj_iff q).1 hkq with hqi | hjq
    · have hvj : v = j := by
        subst q
        exact hqv.symm.trans hcenter
      exact hvIntroduced (by simpa [j] using hvj)
    · apply hjv
      change G.Adj j v
      rw [← hqv, ← hcenter]
      exact hjq
  have hvPrimeTerminal :=
    F.mem_prime_symmDiff_terminal_of_reverse_not_forward
      i R hsymm hvReverse (by simpa [S] using hvForward)
  have hvNotBoundary := F.lemma13 hcriterion hvPrimeTerminal
  rcases Set.mem_symmDiff.mp hvPrimeTerminal with
      ⟨hvPrime, hvNotTerminal⟩ | ⟨hvTerminal, hvNotPrime⟩
  · exact ⟨hvPrime, hvNotTerminal, hvNotBoundary,
      by simpa [S] using hvForward⟩
  · exact (hvForward
      (F.mem_after_of_mem_terminal_of_not_mem_boundary
        i hvTerminal hvNotBoundary)).elim

/-- Once the residual neighbour case is impossible, the removed vertex is
a clone of the introduced vertex on the reverse auxiliary hole. -/
theorem exists_reverse_deformation_of_residual_impossible
    (F : FullDefinition19Deformation O Cprime)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex)
    (hresidual : ∀ {v : V},
      v ∈ Set.range R.vertex →
      G.Adj
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) v →
      v ≠ (F.deformation.step i).introduced →
      ¬G.Adj (F.deformation.step i).introduced v → False) :
    ∃ q : Fin R.card,
      R.vertex q = (F.deformation.step i).introduced ∧
      R.SingleVertexDeformation
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) q := by
  let S := F.deformation.step i
  let j : V := S.introduced
  let k : V := S.before.vertex S.removedIndex
  have hjReverse :=
    F.introduced_mem_reverse_of_symmDiff hcriterion i R hsymm
  obtain ⟨q, hqj⟩ := hjReverse
  refine ⟨q, hqj, ?_⟩
  constructor
  · exact F.removed_not_mem_reverse_of_symmDiff
      hcriterion i R hsymm
  · intro t
    constructor
    · intro hkt
      by_cases htq : t = q
      · exact Or.inl htq
      · right
        by_contra hjt
        have htNeIntroduced : R.vertex t ≠ S.introduced := by
          intro htj
          apply htq
          apply R.injective
          exact htj.trans hqj.symm
        exact hresidual
          ⟨t, rfl⟩
          (by simpa [S, k] using hkt)
          (by simpa [S] using htNeIntroduced)
          (by simpa [S, j, hqj] using hjt)
    · rintro (rfl | hjt)
      · have hjk : G.Adj S.introduced k := S.deformation.adj_clone
        simpa [S, k, hqj] using hjk.symm
      · exact F.introduced_neighbor_implies_removed_neighbor
          hcriterion i R hsymm ⟨t, rfl⟩
          (by simpa [S, j, hqj] using hjt)

/-- Endpoint case of the reverse step.  Component maximality puts any
residual prime neighbour on the active path, while the active path is part
of `∂O`; Lemma 13 says that the same vertex is outside `∂O`. -/
theorem exists_reverse_deformation_of_endpoint
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12Definition19Data F)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex)
    (hendpoint : ∀ {v : V}, v ∈ Cprime →
      G.Adj
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) v →
      v ∈ Set.range (F.deformation.step i).activePath.vertex) :
    ∃ q : Fin R.card,
      R.vertex q = (F.deformation.step i).introduced ∧
      R.SingleVertexDeformation
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) q := by
  apply F.exists_reverse_deformation_of_residual_impossible
    hcriterion i R hsymm
  intro v hvR hkv hvj hjv
  obtain ⟨hvPrime, _hvNotTerminal, hvNotBoundary, _hvNotForward⟩ :=
    F.residual_reverse_neighbor
      hcriterion i R hsymm hvR hkv hvj hjv
  exact hvNotBoundary
    (L.activePath_subset_boundary i (hendpoint hvPrime hkv))

/-- Interior case of the reverse step.  The already-constructed next reverse
step supplies the preceding reverse even hole.  A residual neighbour would
give the removed vertex five distinct neighbours on that hole: the current
introduced vertex, its two cycle neighbours, the residual vertex, and the
next introduced path vertex.  Lemma 7 forces a five-hole, contradicting
evenness. -/
theorem exists_reverse_deformation_of_continuation
    (F : FullDefinition19Deformation O Cprime)
    (hclaw : G.IsClawFree)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (K : Lemma12Continuation F i)
    (nextIndex : Fin F.deformation.stepCount)
    (hnextIndex : nextIndex = K.next)
    (Rnext : IndexedInducedHole G)
    (qnext : Fin Rnext.card)
    (hqnext :
      Rnext.vertex qnext =
        (F.deformation.step nextIndex).introduced)
    (hnext : Rnext.SingleVertexDeformation
      ((F.deformation.step nextIndex).before.vertex
        (F.deformation.step nextIndex).removedIndex) qnext)
    (hnextEven : Even Rnext.card)
    (hsymm :
      Set.range (Rnext.deform hnext).vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex) :
    ∃ q : Fin (Rnext.deform hnext).card,
      (Rnext.deform hnext).vertex q =
          (F.deformation.step i).introduced ∧
      (Rnext.deform hnext).SingleVertexDeformation
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) q := by
  subst nextIndex
  let S := F.deformation.step i
  let T := F.deformation.step K.next
  let R := Rnext.deform hnext
  let j : V := S.introduced
  let k : V := S.before.vertex S.removedIndex
  let jnext : V := T.introduced
  let knext : V := T.before.vertex T.removedIndex
  apply F.exists_reverse_deformation_of_residual_impossible
    hcriterion i R hsymm
  intro v hvR hkv hvj hjv
  obtain ⟨hvPrime, hvNotTerminal, hvNotBoundary, hvNotForward⟩ :=
    F.residual_reverse_neighbor
      hcriterion i R hsymm hvR hkv hvj hjv
  have hjR : j ∈ Set.range R.vertex := by
    simpa [j, R] using
      F.introduced_mem_reverse_of_symmDiff hcriterion i R hsymm
  obtain ⟨q, hqj⟩ := hjR
  obtain ⟨p, r, hpr, hjp, hjr, hprNonadj⟩ :=
    R.exists_two_nonadjacent_neighbors q
  have hjp' : G.Adj j (R.vertex p) := by
    rw [← hqj]
    exact hjp
  have hjr' : G.Adj j (R.vertex r) := by
    rw [← hqj]
    exact hjr
  have hkp : G.Adj k (R.vertex p) := by
    simpa [k, R] using
      F.introduced_neighbor_implies_removed_neighbor
        hcriterion i R hsymm ⟨p, rfl⟩ (by simpa [j] using hjp')
  have hkr : G.Adj k (R.vertex r) := by
    simpa [k, R] using
      F.introduced_neighbor_implies_removed_neighbor
        hcriterion i R hsymm ⟨r, rfl⟩ (by simpa [j] using hjr')
  have hjNeKnext : j ≠ knext := by
    simpa [j, knext, S, T] using K.introduced_ne_nextRemoved
  have hpNeKnext : R.vertex p ≠ knext := by
    intro hpEq
    apply K.introduced_not_adj_nextRemoved
    have : G.Adj S.introduced knext := by
      simpa [j, hpEq] using hjp'
    simpa [knext, S, T] using this
  have hrNeKnext : R.vertex r ≠ knext := by
    intro hrEq
    apply K.introduced_not_adj_nextRemoved
    have : G.Adj S.introduced knext := by
      simpa [j, hrEq] using hjr'
    simpa [knext, S, T] using this
  have hvNeKnext : v ≠ knext := by
    intro hvEq
    apply hvNotBoundary
    exact F.mem_boundary_iff.mpr ⟨K.next, Or.inr (by
      simpa [knext, T] using hvEq)⟩
  have hjRnext : j ∈ Set.range Rnext.vertex := by
    exact hnext.mem_original_of_mem_deform_of_ne_introduced
      (by simpa [R] using (⟨q, hqj⟩ : j ∈ Set.range R.vertex))
      (by simpa [knext] using hjNeKnext)
  have hpRnext : R.vertex p ∈ Set.range Rnext.vertex := by
    exact hnext.mem_original_of_mem_deform_of_ne_introduced
      (by simp [R])
      (by simpa [knext] using hpNeKnext)
  have hrRnext : R.vertex r ∈ Set.range Rnext.vertex := by
    exact hnext.mem_original_of_mem_deform_of_ne_introduced
      (by simp [R])
      (by simpa [knext] using hrNeKnext)
  have hvRnext : v ∈ Set.range Rnext.vertex := by
    exact hnext.mem_original_of_mem_deform_of_ne_introduced
      (by simpa [R] using hvR)
      (by simpa [knext] using hvNeKnext)
  have hkNeJnext : k ≠ jnext := by
    intro hkEq
    have hloop : G.Adj jnext jnext := by
      simpa [k, jnext, S, T, hkEq] using K.removed_adj_nextIntroduced
    exact G.loopless.irrefl jnext hloop
  have hkOutsideRnext : k ∉ Set.range Rnext.vertex := by
    intro hkRnext
    have hkNeRemoved : k ≠ Rnext.vertex qnext := by
      intro hkEq
      apply hkNeJnext
      exact hkEq.trans hqnext
    have hkR : k ∈ Set.range R.vertex := by
      simpa [R] using
        hnext.mem_deform_of_mem_original_of_ne_removed hkRnext hkNeRemoved
    exact F.removed_not_mem_reverse_of_symmDiff
      hcriterion i R hsymm (by simpa [k, S] using hkR)
  obtain ⟨a, ha⟩ := hjRnext
  obtain ⟨b, hb⟩ := hpRnext
  obtain ⟨c, hc⟩ := hrRnext
  obtain ⟨d, hd⟩ := hvRnext
  have hkj : G.Adj k j := by
    simpa [k, j, S] using S.deformation.adj_clone.symm
  have hka : G.Adj k (Rnext.vertex a) := by
    simpa [ha] using hkj
  have hkb : G.Adj k (Rnext.vertex b) := by
    simpa [hb] using hkp
  have hkc : G.Adj k (Rnext.vertex c) := by
    simpa [hc] using hkr
  have hkd : G.Adj k (Rnext.vertex d) := by
    simpa [hd] using hkv
  have hke : G.Adj k (Rnext.vertex qnext) := by
    simpa [k, jnext, S, T, hqnext] using K.removed_adj_nextIntroduced
  have adj_ne : ∀ {x y : V}, G.Adj x y → x ≠ y := by
    intro x y hxy hEq
    subst y
    exact G.loopless.irrefl x hxy
  have hjpNe : j ≠ R.vertex p := adj_ne hjp'
  have hjrNe : j ≠ R.vertex r := adj_ne hjr'
  have hprNe : R.vertex p ≠ R.vertex r := by
    intro hEq
    exact hpr (R.injective hEq)
  have hjvNe : j ≠ v := hvj.symm
  have hpvNe : R.vertex p ≠ v := by
    intro hEq
    apply hjv
    simpa [hEq] using hjp'
  have hrvNe : R.vertex r ≠ v := by
    intro hEq
    apply hjv
    simpa [hEq] using hjr'
  have hjJnextNe : j ≠ jnext := by
    simpa [j, jnext, S, T] using K.introduced_ne_nextIntroduced
  have hpJnextNe : R.vertex p ≠ jnext := by
    intro hEq
    apply K.introduced_not_adj_nextIntroduced
    have : G.Adj S.introduced T.introduced := by
      simpa [j, jnext, hEq] using hjp'
    exact this
  have hrJnextNe : R.vertex r ≠ jnext := by
    intro hEq
    apply K.introduced_not_adj_nextIntroduced
    have : G.Adj S.introduced T.introduced := by
      simpa [j, jnext, hEq] using hjr'
    exact this
  have hvJnextNe : v ≠ jnext := by
    intro hEq
    apply hvNotBoundary
    exact F.mem_boundary_iff.mpr ⟨K.next, Or.inl (by
      simpa [jnext, T] using hEq)⟩
  have index_ne : ∀ {x y : Fin Rnext.card} {vx vy : V},
      Rnext.vertex x = vx → Rnext.vertex y = vy → vx ≠ vy → x ≠ y := by
    intro x y vx vy hx hy hvxy hxy
    apply hvxy
    calc
      vx = Rnext.vertex x := hx.symm
      _ = Rnext.vertex y := congrArg Rnext.vertex hxy
      _ = vy := hy
  have hab : a ≠ b := index_ne ha hb hjpNe
  have hac : a ≠ c := index_ne ha hc hjrNe
  have had : a ≠ d := index_ne ha hd hjvNe
  have hae : a ≠ qnext := index_ne ha hqnext hjJnextNe
  have hbc : b ≠ c := index_ne hb hc hprNe
  have hbd : b ≠ d := index_ne hb hd hpvNe
  have hbe : b ≠ qnext := index_ne hb hqnext hpJnextNe
  have hcd : c ≠ d := index_ne hc hd hrvNe
  have hce : c ≠ qnext := index_ne hc hqnext hrJnextNe
  have hde : d ≠ qnext := index_ne hd hqnext hvJnextNe
  have hcardFive :=
    Rnext.five_external_neighbors_force_card_five hclaw
      (by simpa [k] using hkOutsideRnext)
      hab hac had hae hbc hbd hbe hcd hce hde
      (by simpa [k] using hka) (by simpa [k] using hkb)
      (by simpa [k] using hkc) (by simpa [k] using hkd)
      (by simpa [k] using hke)
  rcases hnextEven with ⟨w, hw⟩
  omega

end FullDefinition19Deformation

end FixedPairingPathFamily

end SimpleGraph
