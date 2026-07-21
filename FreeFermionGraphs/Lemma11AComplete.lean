import FreeFermionGraphs.Lemma11AExact

/-!
# Lemma 11(a): complete statement

This module exposes the exact finite-history theorem under the conventional
`lemma11a_complete` name.  It includes the zero-history case, derives the
original-hole and colour conclusions, and uses the concrete Corollary 11
proof rather than an abstract non-overlap premise.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- All three clauses of Lemma 11(a), uniformly over zero or more earlier
Definition 19 path blocks. -/
theorem lemma11a_complete
    (D : ConcretePathDeformation O Cprime)
    (X : D.Lemma11AHistoryContext)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    ((∃ s : Nat, u ∈ D.dependentAt s) ↔
      u ≠ (D.deformation.step D.firstIndex).introduced ∧
        D.finalHole.externalDegree u =
          D.initialHole.externalDegree u + 1) ∧
    (∀ (s : Nat), u ∈ D.dependentAt s →
      ∀ q : Fin D.finalHole.card,
        D.finalHole.externalDegree u = 3 →
        D.finalHole.SingleVertexDeformation u q →
          D.finalHole.vertex q ∈ Set.range X.originalHole.vertex ∧
            O.HasPairingType .ac u (D.finalHole.vertex q)) ∧
    (∀ (s : Nat), u ∈ D.dependentAt s →
      (D.finalHole.externalDegree u = 4 ↔
        X.originalHole.externalDegree u = 3 ∧
          O.HasTypedClone .ad X.originalHole u)) := by
  exact D.lemma11a_of_historyContext X hclaw huPrime hanti

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
