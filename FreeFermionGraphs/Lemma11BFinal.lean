import FreeFermionGraphs.Lemma11BSideSeparation

/-!
# Lemma 11(b): final assembly

This module collects the remaining local neighborhood facts from the
case analysis of Lemma 11(b) into one structure.  The previously proved
component and well-founded-descent results then yield the complete
degree-four, earlier-anticommuting-witness, and unique-path conclusion in
one theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The local information needed after the concrete Definition 19/20
bookkeeping has been discharged.

The degree field is stated exactly as in Lemma 11(b): a commuting
dependent vertex has degree four in the final hole.  The former path-count
lower bound and count-identification fields were proof-internal
decompositions rather than hypotheses of the paper. -/
structure Lemma11BNeighborhoodData
    (O : FixedPairingPathFamily G)
    (P : IndexedInducedPath G)
    (U : Nat → Set V)
    (degree : Nat → V → Nat) : Prop where
  sideSeparated : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s → O.PairingSideSeparated u
  terminalContained : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s →
    P.AnticommutesWith u →
    ∃ Q : Set V, Q ∈ O.paths ∧ u ∈ Q
  degree_four : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s →
    ¬P.AnticommutesWith u →
    degree s u = 4
  edgeCoverage : O.CoversBDEdges
  predecessor :
    O.CommonBPredecessorRule .ac U P.AnticommutesWith

/-- Lemma 11(b).  A commuting dependent vertex has degree four, and there
is a strictly earlier anticommuting dependent vertex whose unique
fixed-pairing path component also contains the original vertex. -/
theorem lemma11b
    (O : FixedPairingPathFamily G)
    (P : IndexedInducedPath G)
    (U : Nat → Set V)
    (degree : Nat → V → Nat)
    (hdata : O.Lemma11BNeighborhoodData P U degree)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬P.AnticommutesWith u) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        U P.AnticommutesWith s u := by
  have hcapture : O.CapturesClassConnections .ac :=
    O.capturesClassConnections_ac_of_coversBDEdges
      hdata.edgeCoverage
  have hdesc :
      DependentDescentRule U P.AnticommutesWith O.SharesPath :=
    O.dependentDescentRule_of_commonBPredecessors
      .ac U P.AnticommutesWith hcapture hdata.predecessor
  have hlocal :
      O.Lemma11BLocalData U P.AnticommutesWith degree := by
    refine ⟨?_, hdata.degree_four, hdesc⟩
    intro t v hv
    exact O.atMostOneContainingPath_of_pairingSideSeparated
      (hdata.sideSeparated hv)
  apply O.lemma11b_with_uniquePath
    U P.AnticommutesWith degree hlocal hu hcomm
  intro t v _ hv hanti
  obtain ⟨Q, hQ, hvQ⟩ := hdata.terminalContained hv hanti
  exact ⟨Q,
    O.isUniqueContainingPath_of_pairingSideSeparated
      hQ hvQ (hdata.sideSeparated hv)⟩

end FixedPairingPathFamily

end SimpleGraph
