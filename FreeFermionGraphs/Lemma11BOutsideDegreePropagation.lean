import FreeFermionGraphs.Lemma11BHalfLengthThreeDegree

/-!
# Lemma 11(b): propagation of an outside-path degree

After the local outside-path analysis establishes degree four at a given
deformation step, only one uniform bookkeeping fact remains.  Every later
replacement preserves the degree whenever the dependent vertex has matching
adjacency to that step's introduced and removed vertices.

This module proves the finite recurrence once and identifies its endpoint
with the final hole.  The geometric branches can therefore concentrate on
proving the later adjacency agreement.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- Every replacement strictly after step `s` introduces and removes
vertices with the same adjacency to `u`. -/
def LaterReplacementAdjacencyAgreement
    (D : ConcretePathDeformation O Cprime)
    (s : Nat) (u : V) : Prop :=
  ∀ j : Fin D.deformation.stepCount,
    s < j.val →
      (G.Adj u (D.deformation.step j).introduced ↔
        G.Adj u
          ((D.deformation.step j).before.vertex
            (D.deformation.step j).removedIndex))

/-- A later step satisfying the adjacency agreement preserves external
degree. -/
theorem later_degreeAfter_eq_degreeBefore_of_adjacencyAgreement
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V}
    (hagreement : D.LaterReplacementAdjacencyAgreement s u)
    (j : Fin D.deformation.stepCount)
    (hsj : s < j.val) :
    (D.deformation.step j).degreeAfter u =
      (D.deformation.step j).degreeBefore u := by
  have hadj :
      G.Adj u (D.deformation.step j).introduced ↔
        G.Adj u
          ((D.deformation.step j).before.vertex
            (D.deformation.step j).removedIndex) :=
    hagreement j hsj
  simpa [ConcreteDeformationStep.degreeAfter,
    ConcreteDeformationStep.degreeBefore,
    ConcreteDeformationStep.after] using
    (D.deformation.step j).deformation.externalDegree_deform_eq hadj

/-- Degree four after step `s` propagates through every later step. -/
theorem later_degreeAfter_eq_four_of_adjacencyAgreement
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V}
    (hs : s < D.deformation.stepCount)
    (hcurrent :
      (D.deformation.step ⟨s, hs⟩).degreeAfter u = 4)
    (hagreement : D.LaterReplacementAdjacencyAgreement s u)
    (n : Nat)
    (hsn : s ≤ n)
    (hn : n < D.deformation.stepCount) :
    (D.deformation.step ⟨n, hn⟩).degreeAfter u = 4 := by
  induction hsn with
  | refl =>
      simpa using hcurrent
  | @step n hsn ih =>
      have hn' : n < D.deformation.stepCount := by
        omega
      let previous : Fin D.deformation.stepCount := ⟨n, hn'⟩
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      have hij : previous.val + 1 = current.val := by
        rfl
      have hprevious :
          (D.deformation.step previous).degreeAfter u = 4 := by
        simpa [previous] using ih hn'
      have hcurrentBefore :
          (D.deformation.step current).degreeBefore u = 4 := by
        rw [← D.deformation.degreeAfter_eq_nextDegreeBefore
          (i := previous) (j := current) hij u]
        exact hprevious
      have hcurrentAfter :
          (D.deformation.step current).degreeAfter u =
            (D.deformation.step current).degreeBefore u :=
        D.later_degreeAfter_eq_degreeBefore_of_adjacencyAgreement
          hagreement current (by
            change s < n + 1
            exact Nat.lt_succ_of_le hsn)
      calc
        (D.deformation.step ⟨n + 1, hn⟩).degreeAfter u =
            (D.deformation.step current).degreeAfter u := by
              rfl
        _ = (D.deformation.step current).degreeBefore u :=
          hcurrentAfter
        _ = 4 := hcurrentBefore

/-- Degree four at one step plus later adjacency agreement gives degree four
in the final hole. -/
theorem finalDegree_eq_four_of_current_and_laterAgreement
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V}
    (hs : s < D.deformation.stepCount)
    (hcurrent :
      (D.deformation.step ⟨s, hs⟩).degreeAfter u = 4)
    (hagreement : D.LaterReplacementAdjacencyAgreement s u) :
    D.finalDegree s u = 4 := by
  have hlast :
      D.deformation.stepCount - 1 <
        D.deformation.stepCount := by
    omega
  have hsLast :
      s ≤ D.deformation.stepCount - 1 := by
    omega
  have hdegree :=
    D.later_degreeAfter_eq_four_of_adjacencyAgreement
      hs hcurrent hagreement
      (D.deformation.stepCount - 1) hsLast hlast
  simpa [finalDegree, finalHole, lastIndex,
    ConcreteDeformationStep.degreeAfter] using hdegree

/-- The half-length-three result upgraded to the final hole once the common
later-step adjacency invariant is supplied. -/
theorem previous_introduced_or_finalDegree_eq_four_of_halfLength_three
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence 3)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (hagreement : D.LaterReplacementAdjacencyAgreement s u) :
    ∃ previous : Fin D.deformation.stepCount,
      previous.val + 1 = s ∧
        (G.Adj u (D.deformation.step previous).introduced ∨
          D.finalDegree s u = 4) := by
  obtain ⟨previous, hprevious, hbranch⟩ :=
    D.previous_introduced_or_current_degreeAfter_eq_four_of_halfLength_three
      M A L hclaw hInitialEven horder hopposite
      hu huOutside hnotAnti
  rcases hbranch with huPrevious | hcurrent
  · exact ⟨previous, hprevious, Or.inl huPrevious⟩
  · refine ⟨previous, hprevious, Or.inr ?_⟩
    exact D.finalDegree_eq_four_of_current_and_laterAgreement
      (D.index_lt_of_mem_dependentAt hu)
      hcurrent hagreement

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
