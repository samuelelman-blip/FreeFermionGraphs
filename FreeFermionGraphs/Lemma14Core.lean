import FreeFermionGraphs.ObstructionSearch

/-!
# Lemma 14: generic initialization argument

This module assembles Lemma 14(i)--(iii) and the indegree bound in (iv)
from the generic initialization geometry.  The remaining pair-specific
claim in (iv), that a common obstruction target is the dependent vertex of
exactly one incoming search, is proved from terminal-path data in
`ObstructionSearchTerminal`.

The theorem is intentionally named `lemma14_core_of_initializationGeometry`:
the paper name is reserved for the theorem in which the terminal case has
also been discharged.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

/-- Lemma 14(i)--(iii) and the indegree-two half of (iv) from generic
initialization geometry. -/
theorem lemma14_core_of_initializationGeometry
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
    (∀ target : I.Node, I.graph.AtMostTwoIncoming target) := by
  refine ⟨?_, X.graph_isBipartiteByPairing, ?_, ?_⟩
  · intro source
    exact (I.output source).empty_or_complete
  · intro source source' hne hpair
    exact X.samePairing_paths_disjoint hne hpair
  · intro target
    exact X.atMostTwoIncoming target

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
