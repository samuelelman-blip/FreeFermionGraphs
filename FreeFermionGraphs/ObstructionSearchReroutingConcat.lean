import FreeFermionGraphs.ObstructionSearchFiniteMixedAppend

/-!
# Optional search concatenation for corrective rerouting

Equation (C32) starts one obstruction search from the concatenation of two
possibly empty fixed-pairing deformations.  This module lifts the concrete
`FullDefinition19Deformation.concat` constructor to the optional search-output
layer and records the four literal empty/nonempty cases.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace SearchDeformation

/-- Transport a search output across equality of its pairing-family index. -/
def castFamily {p q : PairingType} (h : p = q)
    (S : SearchDeformation (families p) Cprime) :
    SearchDeformation (families q) Cprime := by
  subst q
  exact S

@[simp] theorem castFamily_rfl
    (p : PairingType)
    (S : SearchDeformation (families p) Cprime) :
    castFamily (families := families) rfl S = S := rfl

/-- Family transport leaves the underlying path collection unchanged. -/
theorem paths_castFamily {p q : PairingType} (h : p = q)
    (S : SearchDeformation (families p) Cprime) :
    (castFamily (families := families) h S).paths = S.paths := by
  subst q
  rfl

/-- Literal concatenation of two possibly empty search deformations.

The nonempty/nonempty constructor uses the exact intermediate-hole carrier
condition and the concrete finite Definition 19 concatenation. -/
inductive IsConcatenation
    (A B C : SearchDeformation O Cprime) : Prop where
  | leftEmpty
      (left_empty : A.run = none)
      (result_eq_right : C.run = B.run) :
      IsConcatenation A B C
  | rightEmpty
      (right_empty : B.run = none)
      (result_eq_left : C.run = A.run) :
      IsConcatenation A B C
  | nonempty
      (left : FullDefinition19Deformation O Cprime)
      (right : FullDefinition19Deformation O Cprime)
      (left_eq : A.run = some left)
      (right_eq : B.run = some right)
      (boundary :
        Set.range left.terminalHole.vertex =
          Set.range right.initialHole.vertex)
      (result_eq : C.run = some (left.concat right boundary)) :
      IsConcatenation A B C

namespace IsConcatenation

variable {A B C : SearchDeformation O Cprime}

/-- Every path in the left input occurs in the concatenated output. -/
theorem left_paths_subset
    (H : IsConcatenation A B C) :
    A.paths ⊆ C.paths := by
  intro P hP
  rcases hP with ⟨F, hF, i, hi⟩
  cases H with
  | leftEmpty hA hC =>
      rw [hA] at hF
      contradiction
  | rightEmpty hB hC =>
      exact ⟨F, hC.trans hF, i, hi⟩
  | nonempty left right hA hB hboundary hC =>
      have hEq : F = left :=
        Option.some.inj (hF.symm.trans hA)
      subst F
      refine ⟨left.concat right hboundary, hC,
        left.deformation.concatLeftIndex right.deformation i, ?_⟩
      change Set.range
          (((left.concat right hboundary).deformation.step
            (left.deformation.concatLeftIndex right.deformation i)).activePath.vertex) = P
      rw [ConcreteDeformation.concat_step_left]
      exact hi

/-- Every path in the right input occurs in the concatenated output. -/
theorem right_paths_subset
    (H : IsConcatenation A B C) :
    B.paths ⊆ C.paths := by
  intro P hP
  rcases hP with ⟨F, hF, i, hi⟩
  cases H with
  | leftEmpty hA hC =>
      exact ⟨F, hC.trans hF, i, hi⟩
  | rightEmpty hB hC =>
      rw [hB] at hF
      contradiction
  | nonempty left right hA hB hboundary hC =>
      have hEq : F = right :=
        Option.some.inj (hF.symm.trans hB)
      subst F
      refine ⟨left.concat right hboundary, hC,
        left.deformation.concatRightIndex right.deformation i, ?_⟩
      change Set.range
          (((left.concat right hboundary).deformation.step
            (left.deformation.concatRightIndex right.deformation i)).activePath.vertex) = P
      rw [ConcreteDeformation.concat_step_right]
      exact hi

/-- Both old path collections occur in the concatenated output. -/
theorem union_paths_subset
    (H : IsConcatenation A B C) :
    A.paths ∪ B.paths ⊆ C.paths := by
  intro P hP
  rcases hP with hP | hP
  · exact H.left_paths_subset hP
  · exact H.right_paths_subset hP

end IsConcatenation

/-- A result extends a prefix by one possibly empty finite obstruction-search
tail. -/
def IsContinuation
    (prefix result : SearchDeformation O Cprime) : Prop :=
  ∃ tail : SearchDeformation O Cprime,
    IsConcatenation prefix tail result

namespace IsContinuation

variable {prefix result : SearchDeformation O Cprime}

/-- Every prefix path remains in the result of the rerun. -/
theorem prefix_paths_subset
    (H : IsContinuation prefix result) :
    prefix.paths ⊆ result.paths := by
  obtain ⟨tail, hconcat⟩ := H
  exact hconcat.left_paths_subset

end IsContinuation

end SearchDeformation

end FixedPairingPathFamily
end SimpleGraph
