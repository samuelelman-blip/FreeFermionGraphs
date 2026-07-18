import FreeFermionGraphs.Lemma11BThreeNeighborObstruction

/-!
# Lemma 11(b): isolated triples of final-hole neighbors

The local proof of Lemma 11(b) is written with named hole vertices rather
than indices.  Its recurring obstruction consists of three neighbors of the
dependent vertex, one of which is nonadjacent to the other two.  Such a
triple cannot induce a path.

This module converts that carrier-level configuration into the indexed
three-neighbor obstruction, discharging the choice of indices, their
distinctness, and the three possible induced-path orderings.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Three named vertices on a hole all neighbor the external vertex, while
the first is isolated from the other two inside their induced graph. -/
def HasIsolatedExternalNeighborTriple
    (C : IndexedInducedHole G) (u : V) : Prop :=
  u ∉ Set.range C.vertex ∧
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∈ Set.range C.vertex ∧
      b ∈ Set.range C.vertex ∧
      c ∈ Set.range C.vertex ∧
      G.Adj u a ∧ G.Adj u b ∧ G.Adj u c ∧
      ¬G.Adj a b ∧ ¬G.Adj a c

/-- A carrier-level isolated triple gives the indexed non-path triple used
by the Lemma 7 obstruction. -/
theorem hasThreeDistinctExternalNeighborsNotInducedPath_of_isolatedTriple
    (C : IndexedInducedHole G) {u : V}
    (h : C.HasIsolatedExternalNeighborTriple u) :
    C.HasThreeDistinctExternalNeighborsNotInducedPath u := by
  obtain ⟨hOutside, a, b, c, hab, hac, hbc,
    haCarrier, hbCarrier, hcCarrier,
    hua, hub, huc, hnab, hnac⟩ := h
  obtain ⟨p, hpa⟩ := haCarrier
  obtain ⟨q, hqb⟩ := hbCarrier
  obtain ⟨r, hrc⟩ := hcCarrier
  have hpq : p ≠ q := by
    intro hpq
    apply hab
    calc
      a = C.vertex p := hpa.symm
      _ = C.vertex q := congrArg C.vertex hpq
      _ = b := hqb
  have hpr : p ≠ r := by
    intro hpr
    apply hac
    calc
      a = C.vertex p := hpa.symm
      _ = C.vertex r := congrArg C.vertex hpr
      _ = c := hrc
  have hqr : q ≠ r := by
    intro hqr
    apply hbc
    calc
      b = C.vertex q := hqb.symm
      _ = C.vertex r := congrArg C.vertex hqr
      _ = c := hrc
  have hup : G.Adj u (C.vertex p) := by
    simpa [hpa] using hua
  have huq : G.Adj u (C.vertex q) := by
    simpa [hqb] using hub
  have hur : G.Adj u (C.vertex r) := by
    simpa [hrc] using huc
  refine ⟨hOutside, p, q, r, hpq, hpr, hqr,
    hup, huq, hur, ?_⟩
  rintro (hcenterP | hcenterQ | hcenterR)
  · apply hnab
    simpa [hpa, hqb] using hcenterP.1.symm
  · apply hnab
    simpa [hpa, hqb] using hcenterQ.1
  · apply hnac
    simpa [hpa, hrc] using hcenterR.1

/-- An isolated neighbor triple on an even hole forces external degree
four. -/
theorem externalDegree_eq_four_of_isolated_neighbor_triple
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree)
    {u : V} (hEven : Even C.card)
    (h : C.HasIsolatedExternalNeighborTriple u) :
    C.externalDegree u = 4 := by
  exact C.externalDegree_eq_four_of_three_neighbors_not_inducedPath
    hclaw hEven
    (C.hasThreeDistinctExternalNeighborsNotInducedPath_of_isolatedTriple h)

/-- The same carrier configuration produces the explicit four-neighbor
certificate, with existence of the fourth neighbor supplied by Lemma 7. -/
theorem hasFourDistinctExternalNeighbors_of_isolatedTriple
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree)
    {u : V} (hEven : Even C.card)
    (h : C.HasIsolatedExternalNeighborTriple u) :
    C.HasFourDistinctExternalNeighbors u := by
  exact C.hasFourDistinctExternalNeighbors_of_three_neighbors_not_inducedPath
    hclaw hEven
    (C.hasThreeDistinctExternalNeighborsNotInducedPath_of_isolatedTriple h)

end IndexedInducedHole

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Carrier-level isolated triples at commuting dependent vertices provide
the concrete final-degree rule. -/
theorem finalDegreeFourRule_of_isolatedNeighborTriples
    (D : ConcretePathDeformation O Cprime)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasIsolatedExternalNeighborTriple u) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu hnotAnti
  simpa [finalDegree] using
    D.finalHole.externalDegree_eq_four_of_isolated_neighbor_triple
      hclaw hEven (htriple hu hnotAnti)

/-- Lemma 11(b) with the degree case stated in the named-vertex form used
in the paper's local argument. -/
theorem lemma11b_of_concretePathDeformation_of_isolatedNeighborTriples
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasIsolatedExternalNeighborTriple u)
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
    (D.finalDegreeFourRule_of_isolatedNeighborTriples
      hclaw hEven htriple)
    hpred hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
