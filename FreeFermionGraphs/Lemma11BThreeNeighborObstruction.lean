import FreeFermionGraphs.Lemma11BConcreteDegree

/-!
# Lemma 11(b): the three-neighbor obstruction

Several local branches in the proof of Lemma 11(b) display three neighbors
of the commuting dependent vertex and observe that those three vertices do
not induce a path.  If they were all of its hole neighbors, Lemma 7 would
force exactly such an induced path.  Hence there is a fourth neighbor.
On an even hole the five-neighbor alternative is impossible, so the final
external degree is exactly four.

This module isolates that recurring argument and connects it directly to
the concrete one-path deformation theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Three distinct external neighbors which cannot have any of the three
induced-path orderings forced by the exact degree-three case of Lemma 7. -/
def HasThreeDistinctExternalNeighborsNotInducedPath
    (C : IndexedInducedHole G) (u : V) : Prop :=
  u ∉ Set.range C.vertex ∧
    ∃ p q r : Fin C.card,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      G.Adj u (C.vertex p) ∧
      G.Adj u (C.vertex q) ∧
      G.Adj u (C.vertex r) ∧
      ¬(G.IsInducedPathTriple
          (C.vertex q) (C.vertex p) (C.vertex r) ∨
        G.IsInducedPathTriple
          (C.vertex p) (C.vertex q) (C.vertex r) ∨
        G.IsInducedPathTriple
          (C.vertex p) (C.vertex r) (C.vertex q))

/-- Three explicitly distinct neighbors give external degree at least
three. -/
theorem three_le_externalDegree_of_hasThreeDistinctExternalNeighborsNotInducedPath
    (C : IndexedInducedHole G) {u : V}
    (hthree : C.HasThreeDistinctExternalNeighborsNotInducedPath u) :
    3 ≤ C.externalDegree u := by
  classical
  obtain ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, _⟩ := hthree.2
  have hsubset :
      ({p, q, r} : Set (Fin C.card)) ⊆
        C.neighborIndexSet u := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hcard :
      ({p, q, r} : Set (Fin C.card)).ncard = 3 := by
    apply Set.ncard_eq_three.mpr
    exact ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  unfold externalDegree
  calc
    3 = ({p, q, r} : Set (Fin C.card)).ncard := hcard.symm
    _ ≤ (C.neighborIndexSet u).ncard :=
      Set.ncard_le_ncard hsubset

/-- The paper's recurring local reduction: a non-path triple of external
neighbors on an even hole forces external degree four. -/
theorem externalDegree_eq_four_of_three_neighbors_not_inducedPath
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree)
    {u : V} (hEven : Even C.card)
    (hthree : C.HasThreeDistinctExternalNeighborsNotInducedPath u) :
    C.externalDegree u = 4 := by
  have hlower :
      3 ≤ C.externalDegree u :=
    C.three_le_externalDegree_of_hasThreeDistinctExternalNeighborsNotInducedPath
      hthree
  obtain ⟨hOutside, p, q, r, hpq, hpr, hqr,
    hp, hq, hr, hnotPath⟩ := hthree
  rcases C.lemma7 hclaw hOutside with
    hzero | htwo | hexactThree | hexactFour | hfive
  · simp only [externalDegree] at hlower
    omega
  · simp only [externalDegree] at hlower
    omega
  · have hall : ∀ k : Fin C.card,
        G.Adj u (C.vertex k) →
          k = p ∨ k = q ∨ k = r := by
      intro k hk
      by_contra hkCases
      have hpk : p ≠ k := by
        intro h
        exact hkCases (Or.inl h.symm)
      have hqk : q ≠ k := by
        intro h
        exact hkCases (Or.inr (Or.inl h.symm))
      have hrk : r ≠ k := by
        intro h
        exact hkCases (Or.inr (Or.inr h.symm))
      have hfour :
          C.HasFourDistinctExternalNeighbors u := by
        exact ⟨hOutside, p, q, r, k,
          hpq, hpr, hpk, hqr, hqk, hrk,
          hp, hq, hr, hk⟩
      have hgeFour :
          4 ≤ C.externalDegree u :=
        C.four_le_externalDegree_of_hasFourDistinctExternalNeighbors
          hfour
      have heqThree :
          C.externalDegree u = 3 := by
        simpa [externalDegree] using hexactThree.1
      omega
    exact (hnotPath
      (hexactThree.2 p q r hpq hpr hqr
        hp hq hr hall)).elim
  · simpa [externalDegree] using hexactFour.1
  · obtain ⟨m, hm⟩ := hEven
    have hcardFive : C.card = 5 := hfive.2
    omega

/-- The obstruction argument also constructs the explicit four-neighbor
certificate used by the previous concrete-degree module. -/
theorem hasFourDistinctExternalNeighbors_of_three_neighbors_not_inducedPath
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree)
    {u : V} (hEven : Even C.card)
    (hthree : C.HasThreeDistinctExternalNeighborsNotInducedPath u) :
    C.HasFourDistinctExternalNeighbors u := by
  classical
  have hdegree :
      C.externalDegree u = 4 :=
    C.externalDegree_eq_four_of_three_neighbors_not_inducedPath
      hclaw hEven hthree
  have hncard :
      (C.neighborIndexSet u).ncard = 4 := by
    simpa [externalDegree] using hdegree
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hset⟩ :=
    Set.ncard_eq_four.mp hncard
  refine ⟨hthree.1, p, q, r, s,
    hpq, hpr, hps, hqr, hqs, hrs, ?_, ?_, ?_, ?_⟩
  · change p ∈ C.neighborIndexSet u
    rw [hset]
    simp
  · change q ∈ C.neighborIndexSet u
    rw [hset]
    simp
  · change r ∈ C.neighborIndexSet u
    rw [hset]
    simp
  · change s ∈ C.neighborIndexSet u
    rw [hset]
    simp

end IndexedInducedHole

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Non-path triples at every commuting dependent vertex discharge the
concrete final-degree rule. -/
theorem finalDegreeFourRule_of_threeNeighborNonpathCertificates
    (D : ConcretePathDeformation O Cprime)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (hthree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasThreeDistinctExternalNeighborsNotInducedPath u) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu hnotAnti
  simpa [finalDegree] using
    D.finalHole.externalDegree_eq_four_of_three_neighbors_not_inducedPath
      hclaw hEven (hthree hu hnotAnti)

/-- Lemma 11(b) with the degree case reduced to the non-path triple that
the paper exhibits in its local claw-free analysis. -/
theorem lemma11b_of_concretePathDeformation_of_threeNeighborNonpathCertificates
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s → O.PairingSideSeparated u)
    (hEven : Even D.finalHole.card)
    (hthree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalHole.HasThreeDistinctExternalNeighborsNotInducedPath u)
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
    (D.finalDegreeFourRule_of_threeNeighborNonpathCertificates
      hclaw hEven hthree)
    hpred hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
