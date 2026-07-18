import FreeFermionGraphs.FixedPairingPathDeformation

/-!
# Lemma 11(b): concrete degree-four certificate

The final degree statement in Lemma 11(b) concerns an even induced hole.
Lemma 7 says that an external vertex has at most five neighbors on a hole,
and its five-neighbor case forces the hole itself to have cardinality five.
Consequently, four explicit distinct neighbors on an even hole certify that
the external degree is exactly four.

This turns the remaining degree obligation for a concrete one-path
deformation into the local geometric task appearing in the paper: exhibit
four distinct final-hole neighbors of the commuting dependent vertex.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- An explicit certificate that a vertex outside an indexed hole has four
distinct neighbors on that hole. -/
def HasFourDistinctExternalNeighbors
    (C : IndexedInducedHole G) (u : V) : Prop :=
  u ∉ Set.range C.vertex ∧
    ∃ p q r s : Fin C.card,
      p ≠ q ∧ p ≠ r ∧ p ≠ s ∧
      q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      G.Adj u (C.vertex p) ∧
      G.Adj u (C.vertex q) ∧
      G.Adj u (C.vertex r) ∧
      G.Adj u (C.vertex s)

/-- Four explicitly distinct hole neighbors give the corresponding lower
bound on external degree. -/
theorem four_le_externalDegree_of_hasFourDistinctExternalNeighbors
    (C : IndexedInducedHole G) {u : V}
    (hfour : C.HasFourDistinctExternalNeighbors u) :
    4 ≤ C.externalDegree u := by
  classical
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs,
    hp, hq, hr, hs⟩ := hfour.2
  have hsubset :
      ({p, q, r, s} : Set (Fin C.card)) ⊆
        C.neighborIndexSet u := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
    · exact hs
  have hcard :
      ({p, q, r, s} : Set (Fin C.card)).ncard = 4 := by
    apply Set.ncard_eq_four.mpr
    exact ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩
  unfold externalDegree
  calc
    4 = ({p, q, r, s} : Set (Fin C.card)).ncard := hcard.symm
    _ ≤ (C.neighborIndexSet u).ncard :=
      Set.ncard_le_ncard hsubset

/-- On an even induced hole, a four-neighbor certificate is exact.  The
only larger case allowed by Lemma 7 would force the odd cardinality five. -/
theorem externalDegree_eq_four_of_even_card
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree)
    {u : V} (hEven : Even C.card)
    (hfour : C.HasFourDistinctExternalNeighbors u) :
    C.externalDegree u = 4 := by
  have hlower :
      4 ≤ (C.neighborIndexSet u).ncard := by
    simpa [externalDegree] using
      C.four_le_externalDegree_of_hasFourDistinctExternalNeighbors hfour
  rcases C.lemma7 hclaw hfour.1 with
    hzero | htwo | hthree | hexactFour | hfive
  · omega
  · omega
  · omega
  · simpa [externalDegree] using hexactFour.1
  · obtain ⟨m, hm⟩ := hEven
    have hcardFive : C.card = 5 := hfive.2
    omega

end IndexedInducedHole

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The concrete final-degree form of the even-hole certificate theorem. -/
theorem finalDegree_eq_four_of_hasFourDistinctExternalNeighbors
    (D : ConcretePathDeformation O Cprime)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    {s : Nat} {u : V}
    (hfour : D.finalHole.HasFourDistinctExternalNeighbors u) :
    D.finalDegree s u = 4 := by
  simpa [finalDegree] using
    D.finalHole.externalDegree_eq_four_of_even_card
      hclaw hEven hfour

/-- A family of concrete four-neighbor certificates supplies exactly the
degree-four rule required by the final Lemma 11(b) assembly. -/
theorem finalDegreeFourRule_of_fourNeighborCertificates
    (D : ConcretePathDeformation O Cprime)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (hfour : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasFourDistinctExternalNeighbors u) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu hnotAnti
  exact D.finalDegree_eq_four_of_hasFourDistinctExternalNeighbors
    hclaw hEven (hfour hu hnotAnti)

namespace MechanicalData

variable {D : ConcretePathDeformation O Cprime}

/-- Construct the final neighborhood package with its degree field fixed to
the paper's final-hole degree and its degree theorem discharged by explicit
four-neighbor certificates. -/
def toLemma11BNeighborhoodData_of_fourNeighborCertificates
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (hfour : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasFourDistinctExternalNeighbors u)
    (hpred :
      O.CommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith) :
    O.Lemma11BNeighborhoodData
      D.path D.dependentAt D.finalDegree :=
  M.toLemma11BNeighborhoodData
    hclaw D.finalDegree
    (D.finalDegreeFourRule_of_fourNeighborCertificates
      hclaw hEven hfour)
    hpred

end MechanicalData

/-- Lemma 11(b) for a concrete path deformation, with the final degree
obligation reduced to explicit local four-neighbor certificates. -/
theorem lemma11b_of_concretePathDeformation_of_fourNeighborCertificates
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (hfour : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasFourDistinctExternalNeighbors u)
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
    M hclaw D.finalDegree
    (D.finalDegreeFourRule_of_fourNeighborCertificates
      hclaw hEven hfour)
    hpred hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
