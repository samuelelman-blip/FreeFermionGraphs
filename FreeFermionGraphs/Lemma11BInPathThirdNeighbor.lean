import FreeFermionGraphs.Lemma11BInPathTwoNeighbors

/-!
# Lemma 11(b): the remaining in-path neighbor

Two distinct `C'_c` neighbors of an in-path dependent vertex are forced
by consecutive deformation steps. The only remaining input to the local
degree-four obstruction is therefore one further final-hole neighbor,
distinct from those two and nonadjacent to one of them.

This module states that single residual obligation and proves that it
constructs the complete indexed neighbor certificate and hence degree four.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A third final-hole neighbor, distinct from two specified neighbors and
nonadjacent to the first. -/
def HasAdditionalIsolatedFinalNeighbor
    (D : ConcretePathDeformation O Cprime)
    (u : V) (p q : Fin D.finalHole.card) : Prop :=
  ∃ r : Fin D.finalHole.card,
    p ≠ r ∧ q ≠ r ∧
    G.Adj u (D.finalHole.vertex r) ∧
    ¬G.Adj (D.finalHole.vertex p) (D.finalHole.vertex r)

/-- If every forced pair of distinct `C'_c` neighbors admits the paper's
additional isolated neighbor, the full indexed three-neighbor certificate
follows. -/
theorem hasCCIsolatedFinalNeighborIndexData_of_two_and_additional
    (D : ConcretePathDeformation O Cprime)
    {u : V}
    (htwo : D.HasTwoDistinctCCFinalNeighbors u)
    (hadditional :
      ∀ p q : Fin D.finalHole.card,
        p ≠ q →
        G.Adj u (D.finalHole.vertex p) →
        G.Adj u (D.finalHole.vertex q) →
        D.finalHole.vertex p ∈ O.Cc →
        D.finalHole.vertex q ∈ O.Cc →
        D.HasAdditionalIsolatedFinalNeighbor u p q) :
    D.HasCCIsolatedFinalNeighborIndexData u := by
  obtain ⟨p, q, hpq, hup, huq, hpCc, hqCc⟩ := htwo
  obtain ⟨r, hpr, hqr, hur, hnpr⟩ :=
    hadditional p q hpq hup huq hpCc hqCc
  exact
    ⟨p, q, r, hpq, hpr, hqr,
      hup, huq, hur, hpCc, hqCc, hnpr⟩

/-- In the in-path branch, the two-neighbor premise of the preceding
construction is automatic. -/
theorem hasCCIsolatedFinalNeighborIndexData_of_mem_path_and_additional
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (hadditional :
      ∀ p q : Fin D.finalHole.card,
        p ≠ q →
        G.Adj u (D.finalHole.vertex p) →
        G.Adj u (D.finalHole.vertex q) →
        D.finalHole.vertex p ∈ O.Cc →
        D.finalHole.vertex q ∈ O.Cc →
        D.HasAdditionalIsolatedFinalNeighbor u p q) :
    D.HasCCIsolatedFinalNeighborIndexData u := by
  exact D.hasCCIsolatedFinalNeighborIndexData_of_two_and_additional
    (D.hasTwoDistinctCCFinalNeighbors_of_mem_path M L hu huPath)
    hadditional

/-- The in-path degree-four branch now requires only the single additional
isolated-neighbor construction from the paper. -/
theorem finalDegree_eq_four_of_mem_path_and_additionalNeighbor
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (hadditional :
      ∀ p q : Fin D.finalHole.card,
        p ≠ q →
        G.Adj u (D.finalHole.vertex p) →
        G.Adj u (D.finalHole.vertex q) →
        D.finalHole.vertex p ∈ O.Cc →
        D.finalHole.vertex q ∈ O.Cc →
        D.HasAdditionalIsolatedFinalNeighbor u p q) :
    D.finalDegree s u = 4 := by
  exact D.finalDegree_eq_four_of_mem_path_and_ccNeighborIndices
    M L hclaw hInitialEven hu huPath
    (D.hasCCIsolatedFinalNeighborIndexData_of_mem_path_and_additional
      M L hu huPath hadditional)

/-- Paper-level family form of the residual in-path local obligation. -/
def InPathAdditionalNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    u ∈ Set.range D.path.vertex →
    ¬D.path.AnticommutesWith u →
    ∀ p q : Fin D.finalHole.card,
      p ≠ q →
      G.Adj u (D.finalHole.vertex p) →
      G.Adj u (D.finalHole.vertex q) →
      D.finalHole.vertex p ∈ O.Cc →
      D.finalHole.vertex q ∈ O.Cc →
      D.HasAdditionalIsolatedFinalNeighbor u p q

/-- A paper-level additional-neighbor rule discharges the whole in-path
degree-four family. -/
theorem finalDegreeFourRule_on_path_of_additionalNeighborRule
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hadditional : D.InPathAdditionalNeighborRule) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      u ∈ Set.range D.path.vertex →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu huPath hnotAnti
  exact D.finalDegree_eq_four_of_mem_path_and_additionalNeighbor
    M L hclaw hInitialEven hu huPath
    (hadditional hu huPath hnotAnti)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
