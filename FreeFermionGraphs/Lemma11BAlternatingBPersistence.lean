import FreeFermionGraphs.Lemma11BAlternatingLabelingSequence
import FreeFermionGraphs.Lemma11BInPathTwoNeighbors
import FreeFermionGraphs.Lemma11BOutsideLaterAgreement

/-!
# Lemma 11(b): persistence of alternating `b`-vertices

A transported alternating labeling replaces only `a`-vertices.  Its
`b`-map is therefore constant along the whole deformation block.  Since
the removed vertex at every step is an `a`-vertex, each such `b`-vertex
also survives the final replacement and belongs to the final hole.

These are the paper's persistent common vertices `w_s`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation
namespace AlternatingLabelingSequence

variable {D : ConcretePathDeformation O Cprime} {k : Nat}

/-- Consecutive transported labelings have the same `b`-vertex at every
cyclic index. -/
theorem b_eq_of_succ
    (A : D.AlternatingLabelingSequence k)
    {i j : Fin D.deformation.stepCount}
    (hij : i.val + 1 = j.val)
    (q : Fin k) :
    (A.labeling j).b q = (A.labeling i).b q := by
  rw [A.transport_eq hij]
  simp

/-- The `b`-map is unchanged at every later step of the transported
sequence. -/
theorem b_eq_later_nat
    (A : D.AlternatingLabelingSequence k)
    (i : Fin D.deformation.stepCount)
    (n : Nat)
    (hin : i.val ≤ n)
    (hn : n < D.deformation.stepCount)
    (q : Fin k) :
    (A.labeling ⟨n, hn⟩).b q = (A.labeling i).b q := by
  induction n, hin using Nat.le_induction with
  | base =>
      rfl
  | succ n hin ih =>
      have hn' : n < D.deformation.stepCount := by
        omega
      let previous : Fin D.deformation.stepCount := ⟨n, hn'⟩
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      have hij : previous.val + 1 = current.val := by
        rfl
      calc
        (A.labeling ⟨n + 1, hn⟩).b q =
            (A.labeling current).b q := by rfl
        _ = (A.labeling previous).b q :=
          A.b_eq_of_succ hij q
        _ = (A.labeling i).b q := by
          simpa [previous] using ih hn'

/-- Fin-indexed form of `b`-label persistence. -/
theorem b_eq_later
    (A : D.AlternatingLabelingSequence k)
    (i j : Fin D.deformation.stepCount)
    (hij : i.val ≤ j.val)
    (q : Fin k) :
    (A.labeling j).b q = (A.labeling i).b q := by
  simpa using
    A.b_eq_later_nat i j.val hij j.isLt q

/-- Every `b`-vertex of every transported labeling belongs to the final
indexed hole. -/
theorem b_mem_finalHole
    (A : D.AlternatingLabelingSequence k)
    (i : Fin D.deformation.stepCount)
    (q : Fin k) :
    (A.labeling i).b q ∈ Set.range D.finalHole.vertex := by
  let last : Fin D.deformation.stepCount := D.lastIndex
  have hilast : i.val ≤ last.val := by
    dsimp [last, lastIndex]
    have hi := i.isLt
    omega
  have hbEq :
      (A.labeling last).b q = (A.labeling i).b q :=
    A.b_eq_later i last hilast q
  have hbBefore :
      (A.labeling i).b q ∈
        Set.range (D.deformation.step last).before.vertex := by
    rw [← A.carrier_eq last]
    rw [← hbEq]
    exact (A.labeling last).b_mem_carrier q
  have hbNeRemoved :
      (A.labeling i).b q ≠
        (D.deformation.step last).before.vertex
          (D.deformation.step last).removedIndex := by
    rw [A.removed_eq last]
    rw [← hbEq]
    exact
      ((A.labeling last).color_disjoint
        (A.removedAIndex last) q).symm
  have hbAfter :=
    (D.deformation.step last).mem_after_of_mem_before_of_ne_removed
      hbBefore hbNeRemoved
  simpa [finalHole, last, lastIndex] using hbAfter

end AlternatingLabelingSequence
end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
