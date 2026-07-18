import FreeFermionGraphs.Lemma11BDefinition20Attachment

/-!
# Lemma 11(b): final-hole color exclusion

The final hole in an `(a,c)` path deformation uses only vertices from
`C_a ∪ C_b ∪ C'_c`: every old hole vertex lies in `C_a ∪ C_b`, and
the final replacement introduces a `C'_c` vertex. A dependent vertex is
in `C'_d`. Exact four-color membership therefore proves that it is
outside the final hole.

This removes final-hole exclusion from each local three-neighbor
certificate used in the degree-four branch.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Exact membership in the fourth class excludes membership in each of
the first three classes. -/
theorem ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
    {v : V} {A B C D : Set V}
    (h : ExactlyOneOfFour v A B C D)
    (hvD : v ∈ D) :
    v ∉ A ∧ v ∉ B ∧ v ∉ C := by
  rcases h with hA | hB | hC | hD
  · exact (hA.2.2.2 hvD).elim
  · exact (hB.2.2.2 hvD).elim
  · exact (hC.2.2.2 hvD).elim
  · exact ⟨hD.2.1, hD.2.2.1, hD.2.2.2⟩

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The prime carrier inherits the exact four-coloring used throughout
Definition 19. -/
def PrimeCarrierExactlyColored
    (O : FixedPairingPathFamily G) (Cprime : Set V) : Prop :=
  ∀ ⦃u : V⦄,
    u ∈ Cprime →
      ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd

namespace ConcretePathDeformation

namespace MechanicalData

variable {D : ConcretePathDeformation O Cprime}

/-- Every vertex of the final hole belongs to one of the three classes
used on the nondependent side of an `(a,c)` deformation. -/
theorem finalHole_subset_ca_cb_cc
    (M : D.MechanicalData) :
    Set.range D.finalHole.vertex ⊆
      (O.Ca ∪ O.Cb) ∪ O.Cc := by
  rintro x ⟨q, rfl⟩
  change
    (D.deformation.step D.lastIndex).after.vertex q ∈
      (O.Ca ∪ O.Cb) ∪ O.Cc
  by_cases hq :
      q = (D.deformation.step D.lastIndex).removedIndex
  · subst q
    have hcc :
        (D.deformation.step D.lastIndex).introduced ∈ O.Cc :=
      (M.stepGeometry D.lastIndex).base.introduced_cc
    simpa [ConcreteDeformationStep.after] using
      (show
        (D.deformation.step D.lastIndex).introduced ∈
          (O.Ca ∪ O.Cb) ∪ O.Cc
        from Or.inr hcc)
  · have hbefore :
        (D.deformation.step D.lastIndex).before.vertex q ∈
          O.Ca ∪ O.Cb := by
      apply (M.stepGeometry D.lastIndex).before_subset
      exact ⟨q, rfl⟩
    have hvertex :
        (D.deformation.step D.lastIndex).after.vertex q =
          (D.deformation.step D.lastIndex).before.vertex q := by
      simpa [ConcreteDeformationStep.after] using
        (IndexedInducedHole.deform_vertex_away
          (D.deformation.step D.lastIndex).before
          (D.deformation.step D.lastIndex).deformation hq)
    rw [hvertex]
    exact Or.inl hbefore

/-- A dependent vertex receives exact four-color membership from its
membership in the prime carrier. -/
theorem dependent_exactlyOne
    (M : D.MechanicalData)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [i] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huPrime : u ∈ Cprime :=
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step i)).1 huStep).1
  exact hcolors huPrime

/-- Exact coloring and the mechanical final-hole color bound prove that a
dependent vertex is external to the final hole. -/
theorem dependent_not_mem_finalHole
    (M : D.MechanicalData)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    u ∉ Set.range D.finalHole.vertex := by
  have hnot :
      u ∉ O.Ca ∧ u ∉ O.Cb ∧ u ∉ O.Cc :=
    ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
      (M.dependent_exactlyOne hcolors hu)
      (M.dependent_mem_cd hu)
  intro huFinal
  rcases M.finalHole_subset_ca_cb_cc huFinal with hab | hcc
  · exact hab.elim hnot.1 hnot.2.1
  · exact hnot.2.2 hcc

end MechanicalData

/-- The local named-neighbor data for the degree-four obstruction. The
externality of `u` is omitted because it follows globally from the color
geometry. -/
def HasCCIsolatedFinalNeighborData
    (D : ConcretePathDeformation O Cprime) (u : V) : Prop :=
  ∃ a b c : V,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a ∈ Set.range D.finalHole.vertex ∧
    b ∈ Set.range D.finalHole.vertex ∧
    c ∈ Set.range D.finalHole.vertex ∧
    G.Adj u a ∧ G.Adj u b ∧ G.Adj u c ∧
    a ∈ O.Cc ∧ b ∈ O.Cc ∧
    ¬G.Adj a c

/-- The reduced neighbor data and exact coloring construct the existing
isolated final triple certificate. -/
theorem hasCCIsolatedFinalTriple_of_neighborData
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hdata : D.HasCCIsolatedFinalNeighborData u) :
    D.HasCCIsolatedFinalTriple u :=
  ⟨M.dependent_not_mem_finalHole hcolors hu, hdata⟩

/-- Concrete Lemma 11(b) with final-hole exclusion discharged from the
global four-coloring and deformation geometry. Local degree data now names
only the three final-hole neighbors and their branch-specific relations. -/
theorem lemma11b_of_initialEven_ccNeighborData_baseParity_and_definition20Attachments
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hneighbors : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalNeighborData u)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20AttachmentRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  apply
    D.lemma11b_of_initialEven_ccTriples_baseParity_and_definition20Attachments
      M hclaw hInitialEven
      (htriple := by
        intro s' u' hu' hcomm'
        exact D.hasCCIsolatedFinalTriple_of_neighborData
          M hcolors hu' (hneighbors hu' hcomm'))
      horder hopposite hraw hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
