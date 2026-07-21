import FreeFermionGraphs.ObstructionSearch

/-!
# Lemma 14: generic initialization argument

This module assembles the four conclusions of Lemma 14 from the concrete
initialization geometry of the obstruction search.  The nontrivial finite
directed-graph reasoning is proved here; a later module constructs the
`InitializationGeometry` certificate from the `OS` traversal and the
graph-theoretic results in Corollaries 9--11.

The theorem is therefore intentionally named
`lemma14_of_initializationGeometry` rather than `lemma14`: the paper name is
reserved for the theorem in which that final translation layer has been
discharged.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

/-- Lemma 14 from the local initialization geometry.

The four conjuncts are, in manuscript order:

1. every output is empty or a complete fixed-pairing Definition 19
   deformation;
2. the obstruction graph is bipartite with pairing-type coloring;
3. same-pairing outputs from distinct sources are path-disjoint;
4. every target has indegree at most two, and two distinct incoming arcs
   make the target the unique dependent vertex of exactly one source.
-/
theorem lemma14_of_initializationGeometry
    (I : ObstructionSearchInitialization families Cprime)
    (X : I.InitializationGeometry) :
    (∀ source : I.Node,
      (I.output source).run = none ∨
        ∃ F : FullDefinition19Deformation
            (families (I.pairing source)) Cprime,
          (I.output source).run = some F) ∧
    I.graph.IsBipartiteByPairing I.pairing ∧
    (∀ ⦃source source' : I.Node⦄,
      source ≠ source' →
      I.pairing source = I.pairing source' →
        Disjoint (I.output source).paths
          (I.output source').paths) ∧
    ((∀ target : I.Node, I.graph.AtMostTwoIncoming target) ∧
      ∀ ⦃source source' target : I.Node⦄,
        source ≠ source' →
        I.graph.Arc source target →
        I.graph.Arc source' target →
          ((I.dependentSet source = {(target : V)} ∧
              I.dependentSet source' ≠ {(target : V)}) ∨
            (I.dependentSet source ≠ {(target : V)} ∧
              I.dependentSet source' = {(target : V)}))) := by
  refine ⟨?_, X.graph_isBipartiteByPairing, ?_, ?_⟩
  · intro source
    exact (I.output source).empty_or_complete
  · intro source source' hne hpair
    exact X.samePairing_paths_disjoint hne hpair
  · constructor
    · intro target
      exact X.atMostTwoIncoming target
    · intro source source' target hne h h'
      exact X.target_onlyDependent_of_twoIncoming hne h h'

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
