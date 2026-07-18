import FreeFermionGraphs.Lemma11BComponents

/-!
# Lemma 11(b): final assembly

This module collects the remaining local neighborhood facts from the
case analysis of Lemma 11(b) into one structure.  The previously proved
parity, coloring, component, and well-founded-descent results then yield
the complete degree-four, earlier-anticommuting-witness, and unique-path
conclusion in one theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The local neighborhood information established by the detailed
claw-free case analysis in the proof of Lemma 11(b).

The path-count fields identify the post-deformation degree with the active
path count and force at least three neighbors in the commuting case.  The
last two fields encode the component decomposition and the strictly earlier
common-neighbor predecessor constructed in the paper. -/
structure Lemma11BNeighborhoodData
    (O : FixedPairingPathFamily G)
    (P : IndexedInducedPath G)
    (U : Nat → Set V)
    (degree : Nat → V → Nat) : Prop where
  exactColoring : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s → ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd
  contained : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s →
    ∃ Q : Set V, Q ∈ O.paths ∧ u ∈ Q
  outsidePath : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s → u ∉ Set.range P.vertex
  three_le : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s → ¬P.AnticommutesWith u →
      3 ≤ (P.neighborIndexSet u).ncard
  degree_eq_pathCount : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s →
      degree s u = (P.neighborIndexSet u).ncard
  edgeCoverage : O.CoversBDEdges
  predecessor :
    O.CommonBPredecessorRule .ac U P.AnticommutesWith

/-- Lemma 11(b).  A commuting dependent vertex has degree four, and there
is a strictly earlier anticommuting dependent vertex whose unique
fixed-pairing path component also contains the original vertex. -/
theorem lemma11b
    (O : FixedPairingPathFamily G)
    (P : IndexedInducedPath G)
    (hclaw : G.IsClawFree)
    (U : Nat → Set V)
    (degree : Nat → V → Nat)
    (hdata : O.Lemma11BNeighborhoodData P U degree)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬P.AnticommutesWith u) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        U P.AnticommutesWith s u := by
  have hdegree : ∀ ⦃t : Nat⦄ ⦃v : V⦄,
      v ∈ U t → ¬P.AnticommutesWith v →
        degree t v = 4 :=
    P.lemma11b_degree_four_rule_of_path_count
      hclaw U degree hdata.outsidePath hdata.three_le
        hdata.degree_eq_pathCount
  exact O.lemma11b_of_bdEdgeCoverage
    U P.AnticommutesWith degree
    hdata.exactColoring hdata.contained hdegree
    hdata.edgeCoverage hdata.predecessor hu hcomm

end FixedPairingPathFamily

end SimpleGraph
