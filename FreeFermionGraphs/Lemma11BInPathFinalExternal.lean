import FreeFermionGraphs.Lemma11BInPathCurrentExternal

/-!
# Lemma 11(b): final-hole externality in the in-path branch

An in-path dependent vertex at step `s` has odd common-path index
`2s - 1`. Every vertex introduced at a later step `j` has even
common-path index `2j`, so injectivity of the path labeling shows that
the dependent vertex is never introduced again.

Starting from its exclusion from the after-hole at step `s`, the carrier
chain and single-step externality transport then keep the vertex outside
every later hole, including the final hole of the path deformation.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- An in-path dependent vertex at step `s` is distinct from every vertex
introduced at a later deformation step. -/
theorem dependent_mem_path_ne_later_introduced
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (j : Fin D.deformation.stepCount)
    (hsj : s < j.val) :
    u ≠ (D.deformation.step j).introduced := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ D.dependentAt i.val := by
    simpa [i] using hu
  obtain ⟨q, hqu, hqval⟩ :=
    D.dependent_mem_path_global_index L i hui huPath
  have hqval' : q.val + 1 = 2 * s := by
    simpa [i] using hqval
  intro huj
  have hvertices :
      D.path.vertex q =
        D.path.vertex (L.introducedPathIndex j) := by
    calc
      D.path.vertex q = u := hqu
      _ = (D.deformation.step j).introduced := huj
      _ = D.path.vertex (L.introducedPathIndex j) :=
        (L.introduced_eq j).symm
  have hindices :
      q = L.introducedPathIndex j :=
    D.path.injective hvertices
  have hvals :
      q.val = (L.introducedPathIndex j).val :=
    congrArg Fin.val hindices
  have hjval := L.introduced_index_val j
  omega

/-- Once an in-path dependent vertex has left the hole, it remains outside
the after-hole at every subsequent step. -/
theorem dependent_mem_path_not_mem_later_after
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (n : Nat)
    (hsn : s ≤ n)
    (hn : n < D.deformation.stepCount) :
    u ∉
      Set.range
        (D.deformation.step ⟨n, hn⟩).after.vertex := by
  induction n, hsn using Nat.le_induction with
  | base =>
      simpa using
        D.dependent_mem_path_not_mem_current_after L hu huPath
  | succ n hsn ih =>
      have hnCount : n < D.deformation.stepCount := by
        omega
      let previous : Fin D.deformation.stepCount :=
        ⟨n, hnCount⟩
      let current : Fin D.deformation.stepCount :=
        ⟨n + 1, hn⟩
      have huPrevious :
          u ∉
            Set.range
              (D.deformation.step previous).after.vertex := by
        simpa [previous] using ih hnCount
      have hchain :
          Set.range
              (D.deformation.step previous).after.vertex =
            Set.range
              (D.deformation.step current).before.vertex :=
        D.deformation.carrier_chain (i := previous) (j := current) (by
          simp [previous, current])
      have huBefore :
          u ∉
            Set.range
              (D.deformation.step current).before.vertex := by
        intro humem
        apply huPrevious
        rw [hchain]
        exact humem
      have huIntroduced :
          u ≠ (D.deformation.step current).introduced :=
        D.dependent_mem_path_ne_later_introduced
          L hu huPath current (by
            dsimp [current]
            omega)
      have huAfter :
          u ∉
            Set.range
              (D.deformation.step current).after.vertex :=
        (D.deformation.step current).not_mem_after_of_not_mem_before_of_ne
          huBefore huIntroduced
      simpa [current] using huAfter

/-- The in-path branch of Lemma 11(b) is genuinely external to the final
hole, even though the dependent vertex may lie in the overlap of the two
path families. -/
theorem dependent_mem_path_not_mem_finalHole
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    u ∉ Set.range D.finalHole.vertex := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  have hlast :
      D.deformation.stepCount - 1 <
        D.deformation.stepCount := by
    omega
  have hsLast :
      s ≤ D.deformation.stepCount - 1 := by
    omega
  have huLast :=
    D.dependent_mem_path_not_mem_later_after
      L hu huPath
      (D.deformation.stepCount - 1) hsLast hlast
  simpa [finalHole, lastIndex] using huLast

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
