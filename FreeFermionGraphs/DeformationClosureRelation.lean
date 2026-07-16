import FreeFermionGraphs.Lemma9

/-!
# Relation properties of deformation closure

Single-vertex deformation steps were defined reversibly.  Consequently their
finite closure is reflexive, symmetric, and transitive, as required for the
paper's notation `⟨C₀⟩`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- Reverse a single even-hole deformation step. -/
theorem EvenHoleDeformationStep.symm {G : SimpleGraph V} {A B : Set V}
    (h : EvenHoleDeformationStep G A B) :
    EvenHoleDeformationStep G B A := by
  rcases h with ⟨k, C, s, i, hclone, hforward | hbackward⟩
  · exact ⟨k, C, s, i, hclone, Or.inr ⟨hforward.2, hforward.1⟩⟩
  · exact ⟨k, C, s, i, hclone, Or.inl ⟨hbackward.2, hbackward.1⟩⟩

/-- A single deformation step belongs to the generated closure. -/
theorem EvenHoleDeformationStep.inClosure {G : SimpleGraph V}
    {A B : Set V} (h : EvenHoleDeformationStep G A B) :
    InEvenHoleDeformationClosure G A B :=
  InEvenHoleDeformationClosure.tail
    (InEvenHoleDeformationClosure.refl A) h

/-- Concatenate two finite deformation sequences. -/
theorem InEvenHoleDeformationClosure.trans {G : SimpleGraph V}
    {A B C : Set V}
    (hAB : InEvenHoleDeformationClosure G A B)
    (hBC : InEvenHoleDeformationClosure G B C) :
    InEvenHoleDeformationClosure G A C := by
  induction hBC with
  | refl => exact hAB
  | tail hBC hstep ih =>
      exact InEvenHoleDeformationClosure.tail ih hstep

/-- Reverse a finite deformation sequence. -/
theorem InEvenHoleDeformationClosure.symm {G : SimpleGraph V}
    {A B : Set V} (hAB : InEvenHoleDeformationClosure G A B) :
    InEvenHoleDeformationClosure G B A := by
  induction hAB with
  | refl => exact InEvenHoleDeformationClosure.refl _
  | tail hAB hstep ih =>
      exact InEvenHoleDeformationClosure.trans
        (EvenHoleDeformationStep.inClosure
          (EvenHoleDeformationStep.symm hstep)) ih

/-- Membership in the same deformation closure is symmetric. -/
theorem inEvenHoleDeformationClosure_comm {G : SimpleGraph V}
    {A B : Set V} :
    InEvenHoleDeformationClosure G A B ↔
      InEvenHoleDeformationClosure G B A := by
  constructor
  · exact InEvenHoleDeformationClosure.symm
  · exact InEvenHoleDeformationClosure.symm

end SimpleGraph
