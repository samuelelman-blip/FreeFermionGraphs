import FreeFermionGraphs.ObstructionSearchFiniteMixedAppend

/-!
# Optional search concatenation for corrective rerouting

Equation (C32) starts one obstruction search from the concatenation of two
possibly empty fixed-pairing deformations.  This module lifts the concrete
`FullDefinition19Deformation.concat` constructor to the optional search-output
layer and records the literal empty/nonempty branches.

The branch data identify the exact run-level concatenation.  Path containment
is kept explicit at this interface because the optional output representation
forgets the dependent index equivalence between the concrete concatenated
steps and the resulting `FullDefinition19Deformation`.
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

/-- The exact run-level branch of an optional concatenation. -/
inductive ConcatenationBranch
    (A B C : SearchDeformation O Cprime) : Prop where
  | leftEmpty
      (left_empty : A.run = none)
      (result_eq_right : C.run = B.run) :
      ConcatenationBranch A B C
  | rightEmpty
      (right_empty : B.run = none)
      (result_eq_left : C.run = A.run) :
      ConcatenationBranch A B C
  | nonempty
      (left : FullDefinition19Deformation O Cprime)
      (right : FullDefinition19Deformation O Cprime)
      (left_eq : A.run = some left)
      (right_eq : B.run = some right)
      (boundary :
        Set.range left.terminalHole.vertex =
          Set.range right.initialHole.vertex)
      (result_eq : C.run = some (left.concat right boundary)) :
      ConcatenationBranch A B C

/-- Literal optional concatenation together with the path provenance needed by
later rerouting arguments.  Neither containment field is a conclusion of
Lemma 14: both say only that the two input sequences occur as the prefix of
the output sequence specified by the exact branch above. -/
structure IsConcatenation
    (A B C : SearchDeformation O Cprime) : Prop where
  branch : ConcatenationBranch A B C
  left_paths_subset : A.paths ⊆ C.paths
  right_paths_subset : B.paths ⊆ C.paths

namespace IsConcatenation

variable {A B C : SearchDeformation O Cprime}

/-- Both input path collections occur in the concatenated output. -/
theorem union_paths_subset
    (H : IsConcatenation A B C) :
    A.paths ∪ B.paths ⊆ C.paths := by
  intro P hP
  rcases hP with hP | hP
  · exact H.left_paths_subset hP
  · exact H.right_paths_subset hP

end IsConcatenation

/-- A result extends an initial optional deformation by one possibly empty
finite obstruction-search tail. -/
def IsContinuation
    (initial result : SearchDeformation O Cprime) : Prop :=
  ∃ tail : SearchDeformation O Cprime,
    IsConcatenation initial tail result

namespace IsContinuation

variable {initial result : SearchDeformation O Cprime}

/-- Every initial path remains in the result of the rerun. -/
theorem prefix_paths_subset
    (H : IsContinuation initial result) :
    initial.paths ⊆ result.paths := by
  obtain ⟨tail, hconcat⟩ := H
  exact hconcat.left_paths_subset

end IsContinuation

end SearchDeformation

end FixedPairingPathFamily
end SimpleGraph
