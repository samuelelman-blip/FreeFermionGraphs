import FreeFermionGraphs.Lemma11BInPathDegree

/-!
# Lemma 11(b): two forced final neighbors in the in-path branch

Every introduced path vertex remains on all later holes: Definition 19
assigns introduced vertices even path indices and later removed vertices
odd path indices, so a later deformation never removes an earlier
introduced vertex.

For an in-path dependent vertex at step `s`, the vertex is the one removed
at step `s - 1`. It is adjacent both to the clone introduced at that
previous step and, by Definition 20, to the vertex introduced at the current
step. Both are distinct `C'_c` vertices on the final hole. Thus two of the
three neighbors used in the paper's local degree-four obstruction are
forced by the existing deformation geometry.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcreteDeformationStep

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The introduced vertex belongs to the hole immediately after its step. -/
theorem introduced_mem_after
    (S : ConcreteDeformationStep O Cprime) :
    S.introduced ∈ Set.range S.after.vertex := by
  refine ⟨S.removedIndex, ?_⟩
  simp [after]

/-- A before-hole vertex other than the removed vertex remains on the
after-hole. -/
theorem mem_after_of_mem_before_of_ne_removed
    (S : ConcreteDeformationStep O Cprime)
    {u : V}
    (huBefore : u ∈ Set.range S.before.vertex)
    (huRemoved :
      u ≠ S.before.vertex S.removedIndex) :
    u ∈ Set.range S.after.vertex := by
  obtain ⟨q, hqu⟩ := huBefore
  have hqi : q ≠ S.removedIndex := by
    intro hqi
    subst q
    exact huRemoved hqu.symm
  refine ⟨q, ?_⟩
  calc
    S.after.vertex q = S.before.vertex q := by
      simpa [after] using
        S.before.deform_vertex_away S.deformation hqi
    _ = u := hqu

end ConcreteDeformationStep

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- An introduced vertex is distinct from every vertex removed at a later
step, by the even/odd common-path indices of Definition 19. -/
theorem introduced_ne_later_removed
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (i j : Fin D.deformation.stepCount)
    (hij : i.val < j.val) :
    (D.deformation.step i).introduced ≠
      (D.deformation.step j).before.vertex
        (D.deformation.step j).removedIndex := by
  intro hEq
  have hvertices :
      D.path.vertex (L.introducedPathIndex i) =
        D.path.vertex (L.removedPathIndex j) := by
    calc
      D.path.vertex (L.introducedPathIndex i) =
          (D.deformation.step i).introduced :=
        L.introduced_eq i
      _ = (D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex := hEq
      _ = D.path.vertex (L.removedPathIndex j) :=
        (L.removed_eq j).symm
  have hindices :
      L.introducedPathIndex i = L.removedPathIndex j :=
    D.path.injective hvertices
  have hvals := congrArg Fin.val hindices
  have hiVal := L.introduced_index_val i
  have hjVal := L.removed_index_val j
  omega

/-- Distinct deformation steps introduce distinct common-path vertices. -/
theorem introduced_ne_later_introduced
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (i j : Fin D.deformation.stepCount)
    (hij : i.val < j.val) :
    (D.deformation.step i).introduced ≠
      (D.deformation.step j).introduced := by
  intro hEq
  have hvertices :
      D.path.vertex (L.introducedPathIndex i) =
        D.path.vertex (L.introducedPathIndex j) := by
    calc
      D.path.vertex (L.introducedPathIndex i) =
          (D.deformation.step i).introduced :=
        L.introduced_eq i
      _ = (D.deformation.step j).introduced := hEq
      _ = D.path.vertex (L.introducedPathIndex j) :=
        (L.introduced_eq j).symm
  have hindices :
      L.introducedPathIndex i = L.introducedPathIndex j :=
    D.path.injective hvertices
  have hvals := congrArg Fin.val hindices
  have hiVal := L.introduced_index_val i
  have hjVal := L.introduced_index_val j
  omega

/-- A vertex introduced at step `i` remains on the after-hole of every
step at or after `i`. -/
theorem introduced_mem_later_after
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (i : Fin D.deformation.stepCount)
    (n : Nat)
    (hin : i.val ≤ n)
    (hn : n < D.deformation.stepCount) :
    (D.deformation.step i).introduced ∈
      Set.range
        (D.deformation.step ⟨n, hn⟩).after.vertex := by
  induction n, hin using Nat.le_induction with
  | base =>
      simpa using (D.deformation.step i).introduced_mem_after
  | succ n hin ih =>
      have hnCount : n < D.deformation.stepCount := by
        omega
      let previous : Fin D.deformation.stepCount :=
        ⟨n, hnCount⟩
      let current : Fin D.deformation.stepCount :=
        ⟨n + 1, hn⟩
      have hmemPrevious :
          (D.deformation.step i).introduced ∈
            Set.range
              (D.deformation.step previous).after.vertex := by
        simpa [previous] using ih hnCount
      have hchain :
          Set.range
              (D.deformation.step previous).after.vertex =
            Set.range
              (D.deformation.step current).before.vertex :=
        D.deformation.carrier_chain
          (i := previous) (j := current) (by
            simp [previous, current])
      have hmemBefore :
          (D.deformation.step i).introduced ∈
            Set.range
              (D.deformation.step current).before.vertex := by
        rw [← hchain]
        exact hmemPrevious
      have hneRemoved :
          (D.deformation.step i).introduced ≠
            (D.deformation.step current).before.vertex
              (D.deformation.step current).removedIndex :=
        D.introduced_ne_later_removed L i current (by
          dsimp [current]
          omega)
      have hmemAfter :=
        (D.deformation.step current).mem_after_of_mem_before_of_ne_removed
          hmemBefore hneRemoved
      simpa [current] using hmemAfter

/-- Every introduced vertex of the path-deformation block belongs to the
final hole. -/
theorem introduced_mem_finalHole
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (i : Fin D.deformation.stepCount) :
    (D.deformation.step i).introduced ∈
      Set.range D.finalHole.vertex := by
  have hlast :
      D.deformation.stepCount - 1 <
        D.deformation.stepCount := by
    omega
  have hiLast :
      i.val ≤ D.deformation.stepCount - 1 := by
    omega
  have hmem :=
    D.introduced_mem_later_after
      L i (D.deformation.stepCount - 1) hiLast hlast
  simpa [finalHole, lastIndex] using hmem

/-- Two distinct final-hole neighbors in `C'_c`. -/
def HasTwoDistinctCCFinalNeighbors
    (D : ConcretePathDeformation O Cprime) (u : V) : Prop :=
  ∃ p q : Fin D.finalHole.card,
    p ≠ q ∧
    G.Adj u (D.finalHole.vertex p) ∧
    G.Adj u (D.finalHole.vertex q) ∧
    D.finalHole.vertex p ∈ O.Cc ∧
    D.finalHole.vertex q ∈ O.Cc

/-- An in-path dependent vertex has the two consecutive introduced
vertices as distinct `C'_c` neighbors on the final hole. -/
theorem hasTwoDistinctCCFinalNeighbors_of_mem_path
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    D.HasTwoDistinctCCFinalNeighbors u := by
  obtain ⟨t, ht, hsucc, huRemoved⟩ :=
    D.dependent_mem_path_eq_previous_removed L hu huPath
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hpreviousCurrent : previous.val < current.val := by
    simpa [previous, current, Nat.succ_eq_add_one] using
      (show t < s by omega)
  have hprevFinal :
      (D.deformation.step previous).introduced ∈
        Set.range D.finalHole.vertex :=
    D.introduced_mem_finalHole L previous
  have hcurrFinal :
      (D.deformation.step current).introduced ∈
        Set.range D.finalHole.vertex :=
    D.introduced_mem_finalHole L current
  obtain ⟨p, hp⟩ := hprevFinal
  obtain ⟨q, hq⟩ := hcurrFinal
  have hintroduced :
      (D.deformation.step previous).introduced ≠
        (D.deformation.step current).introduced :=
    D.introduced_ne_later_introduced
      L previous current hpreviousCurrent
  have hpq : p ≠ q := by
    intro hpq
    apply hintroduced
    calc
      (D.deformation.step previous).introduced =
          D.finalHole.vertex p := hp.symm
      _ = D.finalHole.vertex q := by rw [hpq]
      _ = (D.deformation.step current).introduced := hq
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huCurrent :
      G.Adj u (D.deformation.step current).introduced :=
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep).2.1
  have huPrevious :
      G.Adj u (D.deformation.step previous).introduced := by
    rw [huRemoved]
    exact
      (D.deformation.step previous).deformation.adj_clone.symm
  refine ⟨p, q, hpq, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact huPrevious
  · rw [hq]
    exact huCurrent
  · rw [hp]
    exact (M.stepGeometry previous).base.introduced_cc
  · rw [hq]
    exact (M.stepGeometry current).base.introduced_cc

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
