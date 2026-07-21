import FreeFermionGraphs.Lemma11APathBlock

/-!
# Lemma 11(a): degree parity across a path block

A complete Definition 19 path block preserves the parity of the external
degree exactly when the vertex commutes with that path.  This is the
degree-history invariant used in the global argument of Lemma 11(a.ii).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A commuting path block preserves external-degree parity. -/
theorem finalDegree_mod_two_eq_initial_of_commutes
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hcard : D.path.card = 2 * D.deformation.stepCount)
    (u : V)
    (hcomm : D.path.CommutesWith u) :
    D.finalHole.externalDegree u % 2 =
      D.initialHole.externalDegree u % 2 := by
  have hpath := D.pathNeighborCount_eq_introduced_add_removed L hcard u
  have hparity :=
    (D.path.commutesWith_iff_neighborIndexSet_mod_eq_zero u).mp hcomm
  have hdegree := D.final_degree_balance u
  omega

/-- An anticommuting path block flips external-degree parity. -/
theorem finalDegree_mod_two_ne_initial_of_anticommutes
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hcard : D.path.card = 2 * D.deformation.stepCount)
    (u : V)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u % 2 ≠
      D.initialHole.externalDegree u % 2 := by
  have hpath := D.pathNeighborCount_eq_introduced_add_removed L hcard u
  have hparity :=
    (D.path.anticommutesWith_iff_neighborIndexSet_mod_eq_one u).mp hanti
  have hdegree := D.final_degree_balance u
  omega

/-- Parity also telescopes across consecutive commuting path blocks when
their final and initial hole carriers agree. -/
theorem finalDegree_mod_two_eq_initial_of_commuting_consecutive_blocks
    (D : ConcretePathDeformation O Cprime)
    (E : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (M : Definition19GlobalOverlapPathOrder E)
    (hDcard : D.path.card = 2 * D.deformation.stepCount)
    (hEcard : E.path.card = 2 * E.deformation.stepCount)
    (hchain :
      Set.range D.finalHole.vertex = Set.range E.initialHole.vertex)
    (u : V)
    (hDcomm : D.path.CommutesWith u)
    (hEcomm : E.path.CommutesWith u) :
    E.finalHole.externalDegree u % 2 =
      D.initialHole.externalDegree u % 2 := by
  have hD := D.finalDegree_mod_two_eq_initial_of_commutes
    L hDcard u hDcomm
  have hE := E.finalDegree_mod_two_eq_initial_of_commutes
    M hEcard u hEcomm
  have hmiddle :
      D.finalHole.externalDegree u = E.initialHole.externalDegree u :=
    D.finalHole.externalDegree_eq_of_range_eq E.initialHole hchain
  rw [← hmiddle] at hE
  exact hE.trans hD

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
