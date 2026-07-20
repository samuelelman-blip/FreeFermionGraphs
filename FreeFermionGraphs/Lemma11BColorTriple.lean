import FreeFermionGraphs.Lemma11BIsolatedTriple

/-!
# Lemma 11(b): color-class construction of the isolated triple

In the local branches of Lemma 11(b), two of the displayed final-hole
neighbors lie in the same introduced-side coloring class. Independence of
that class supplies one of the two nonedges needed for the isolated-triple
obstruction. The other nonedge is the branch condition in the paper.

This module derives the first nonedge from the concrete step geometry and
leaves only the named vertices and the branch-specific nonadjacency.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Build an isolated external-neighbor triple when the isolated vertex and
the second vertex lie in one independent class. -/
theorem hasIsolatedExternalNeighborTriple_of_independent_pair
    (C : IndexedInducedHole G)
    {u a b c : V} {I : Set V}
    (hOutside : u ∉ Set.range C.vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haCarrier : a ∈ Set.range C.vertex)
    (hbCarrier : b ∈ Set.range C.vertex)
    (hcCarrier : c ∈ Set.range C.vertex)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hIndependent : IsIndependentClass G I)
    (haI : a ∈ I) (hbI : b ∈ I)
    (hnac : ¬G.Adj a c) :
    C.HasIsolatedExternalNeighborTriple u := by
  refine ⟨hOutside, a, b, c, hab, hac, hbc,
    haCarrier, hbCarrier, hcCarrier,
    hua, hub, huc, ?_, hnac⟩
  exact hIndependent haI hbI

end IndexedInducedHole

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The named-vertex data in the paper's introduced-class obstruction.
The nonedge between a and b is deliberately absent: it follows from
the introduced-class independence already stored in MechanicalData. -/
def HasCCIsolatedFinalTriple
    (D : ConcretePathDeformation O Cprime) (u : V) : Prop :=
  u ∉ Set.range D.finalHole.vertex ∧
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∈ Set.range D.finalHole.vertex ∧
      b ∈ Set.range D.finalHole.vertex ∧
      c ∈ Set.range D.finalHole.vertex ∧
      G.Adj u a ∧ G.Adj u b ∧ G.Adj u c ∧
      a ∈ O.Cc ∧ b ∈ O.Cc ∧
      ¬G.Adj a c

/-- Concrete step geometry supplies the missing same-color nonedge. -/
theorem hasIsolatedExternalNeighborTriple_of_ccFinalTriple
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (htriple : D.HasCCIsolatedFinalTriple u) :
    D.finalHole.HasIsolatedExternalNeighborTriple u := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  obtain ⟨hOutside, a, b, c, hab, hac, hbc,
    haCarrier, hbCarrier, hcCarrier,
    hua, hub, huc, haCc, hbCc, hnac⟩ := htriple
  exact D.finalHole.hasIsolatedExternalNeighborTriple_of_independent_pair
    hOutside hab hac hbc
    haCarrier hbCarrier hcCarrier
    hua hub huc
    (M.stepGeometry i).base.cc_independent
    haCc hbCc hnac

/-- Introduced-class triples discharge the concrete final-degree rule using
the independence already present in the mechanical data. -/
theorem finalDegreeFourRule_of_ccIsolatedFinalTriples
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  refine D.finalDegreeFourRule_of_isolatedNeighborTriples
    hclaw hEven ?_
  intro s u hu hnotAnti
  exact D.hasIsolatedExternalNeighborTriple_of_ccFinalTriple
    M hu (htriple hu hnotAnti)

/-- Lemma 11(b) with the final-degree input reduced to the paper's
introduced-color-class triple. -/
theorem lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s → O.PairingSideSeparated u)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u)
    (hpred :
      O.CommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_concretePathDeformation
    M hclaw hside D.finalDegree
    (D.finalDegreeFourRule_of_ccIsolatedFinalTriples
      M hclaw hEven htriple)
    hpred hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
