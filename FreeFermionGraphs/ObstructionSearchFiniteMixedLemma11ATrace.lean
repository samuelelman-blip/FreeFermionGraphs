import FreeFermionGraphs.ObstructionSearchFiniteMixedLemma11AExact

/-!
# Exact Lemma 11(a.ii) for every finite trace block

The first trace block is analysed directly, while every later block receives
its canonical bounded prefix.  Equality of hole carriers is enough to
transport single-vertex clones and their fixed-pairing types between different
indexings of the same original hole.

Thus every path represented by a `FiniteMixedSideSearchTrace` satisfies the
exact Lemma 11(a.ii) conclusion without an infinite history.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A single-vertex deformation transports to any indexed hole with the same
carrier, with the same centre vertex. -/
theorem SingleVertexDeformation.exists_of_range_eq
    (C D : IndexedInducedHole G)
    (hRange : Set.range C.vertex = Set.range D.vertex)
    {s : V} {i : Fin C.card}
    (hclone : C.SingleVertexDeformation s i) :
    ∃ j : Fin D.card,
      D.vertex j = C.vertex i ∧
        D.SingleVertexDeformation s j := by
  have hiD : C.vertex i ∈ Set.range D.vertex := by
    rw [← hRange]
    exact ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hiD
  refine ⟨j, hj, ?_⟩
  constructor
  · intro hsD
    apply hclone.outside
    rw [hRange]
    exact hsD
  · intro q
    have hqC : D.vertex q ∈ Set.range C.vertex := by
      rw [hRange]
      exact ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hqC
    constructor
    · intro hsq
      have hsp : G.Adj s (C.vertex p) := by
        rw [hp]
        exact hsq
      rcases (hclone.adj_iff p).mp hsp with hpi | hcenter
      · left
        apply D.injective
        calc
          D.vertex q = C.vertex p := hp.symm
          _ = C.vertex i := by rw [hpi]
          _ = D.vertex j := hj.symm
      · right
        simpa only [hj, hp] using hcenter
    · intro hq
      rcases hq with hqj | hcenter
      · subst q
        rw [hj]
        exact hclone.adj_clone
      · have hcenterC : G.Adj (C.vertex i) (C.vertex p) := by
          simpa only [hj, hp] using hcenter
        have hsp := hclone.adj_of_clone_adj hcenterC
        rw [hp] at hsp
        exact hsp

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G}
  {Cprime : Set V}

/-- Typed clone existence depends only on the carrier of the indexed hole. -/
theorem hasTypedClone_iff_of_range_eq
    (O : FixedPairingPathFamily G)
    (σ : PairingType)
    (C D : IndexedInducedHole G)
    (hRange : Set.range C.vertex = Set.range D.vertex)
    (prime : V) :
    O.HasTypedClone σ C prime ↔
      O.HasTypedClone σ D prime := by
  constructor
  · rintro ⟨i, hclone, htyped⟩
    obtain ⟨j, hj, hcloneD⟩ :=
      hclone.exists_of_range_eq C D hRange
    refine ⟨j, hcloneD, ?_⟩
    rw [hj]
    exact htyped
  · rintro ⟨j, hclone, htyped⟩
    obtain ⟨i, hi, hcloneC⟩ :=
      hclone.exists_of_range_eq D C hRange.symm
    refine ⟨i, hcloneC, ?_⟩
    rw [hi]
    exact htyped

namespace ConcretePathDeformation

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Exact Lemma 11(a.ii) for every block of a finite mixed-side trace. -/
theorem block_lemma11aii_exact
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ (X.block i).dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : (X.block i).path.AnticommutesWith u) :
    (X.block i).finalHole.externalDegree u = 4 ↔
      originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad originalHole u := by
  by_cases hi : i.val = 0
  · have hindex : i = X.firstIndex := by
      apply Fin.ext
      exact hi
    subst i
    have hfirst :=
      (X.block X.firstIndex).lemma11aii_of_firstBlock_mixedSide
        (X.side X.firstIndex) (X.localData X.firstIndex)
        hclaw hu huPrime hanti
    have hdegree :
        (X.block X.firstIndex).initialHole.externalDegree u =
          originalHole.externalDegree u :=
      (X.block X.firstIndex).initialHole.externalDegree_eq_of_range_eq
        originalHole (by
          simpa [FiniteMixedSideSearchTrace.firstIndex] using
            X.originalHole_eq)
    have htyped :
        O.HasTypedClone .ad (X.block X.firstIndex).initialHole u ↔
          O.HasTypedClone .ad originalHole u :=
      O.hasTypedClone_iff_of_range_eq .ad
        (X.block X.firstIndex).initialHole originalHole (by
          simpa [FiniteMixedSideSearchTrace.firstIndex] using
            X.originalHole_eq) u
    constructor
    · intro hfour
      obtain ⟨hthree, hclone⟩ := hfirst.mp hfour
      exact ⟨by
        rw [← hdegree]
        exact hthree, htyped.mp hclone⟩
    · rintro ⟨hthree, hclone⟩
      apply hfirst.mpr
      exact ⟨by
        rw [hdegree]
        exact hthree, htyped.mpr hclone⟩
  · let H := X.finiteHistoryAt i (Nat.pos_of_ne_zero hi)
    exact H.lemma11aii_exact hclaw hu huPrime hanti

/-- Every output path represented by the finite trace has a concrete block on
which exact Lemma 11(a.ii) holds over the fixed original hole. -/
theorem output_path_has_lemma11aii_exact
    (X : FiniteMixedSideSearchTrace S originalHole)
    {P : Set V} (hP : P ∈ S.paths)
    (hclaw : G.IsClawFree) :
    ∃ i : Fin X.blockCount,
      Set.range (X.block i).path.vertex = P ∧
        ∀ {s : Nat} {u : V},
          u ∈ (X.block i).dependentAt s →
          u ∈ Cprime →
          (X.block i).path.AnticommutesWith u →
            ((X.block i).finalHole.externalDegree u = 4 ↔
              originalHole.externalDegree u = 3 ∧
                O.HasTypedClone .ad originalHole u) := by
  obtain ⟨i, hi⟩ := (X.output_path_iff P).mp hP
  refine ⟨i, hi, ?_⟩
  intro s u hu huPrime hanti
  exact X.block_lemma11aii_exact i hclaw hu huPrime hanti

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
