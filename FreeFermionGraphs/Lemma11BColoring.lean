import FreeFermionGraphs.Lemma11B

/-!
# Lemma 11(b): coloring-class discharge

Corollary 10 supplies the path-uniqueness input used by Lemma 11(b).
This module turns exact membership in one of the four coloring classes into
the uniqueness field of `Lemma11BLocalData`.  If dependent vertices are
also known to occur in the deformation path family, the earlier
anticommuting witness has a unique containing path, and the original
commuting vertex belongs to that path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Exact four-coloring membership discharges the unique-containing-path
obligation in the local data for Lemma 11(b). -/
theorem lemma11BLocalData_of_exactColoring
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (degree : Nat → V → Nat)
    (hexact : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd)
    (hdegree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ¬Anticommutes u → degree s u = 4)
    (hdesc : DependentDescentRule U Anticommutes O.SharesPath) :
    O.Lemma11BLocalData U Anticommutes degree := by
  refine ⟨?_, hdegree, hdesc⟩
  intro s u hu
  exact O.atMostOneContainingPath_of_exactlyOne (hexact hu)

/-- Lemma 11(b) after all coloring and path-membership bookkeeping has
been discharged.  Only the two genuinely local graph obligations remain:
degree four for a commuting dependent vertex and construction of a strict
component-linked predecessor. -/
theorem lemma11b_of_coloring_and_localRules
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (degree : Nat → V → Nat)
    (hexact : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd)
    (hcontained : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s →
      ∃ P : Set V, P ∈ O.paths ∧ u ∈ P)
    (hdegree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ¬Anticommutes u → degree s u = 4)
    (hdesc : DependentDescentRule U Anticommutes O.SharesPath)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        U Anticommutes s u := by
  have hlocal : O.Lemma11BLocalData U Anticommutes degree :=
    O.lemma11BLocalData_of_exactColoring
      U Anticommutes degree hexact hdegree hdesc
  apply O.lemma11b_with_uniquePath
    U Anticommutes degree hlocal hu hcomm
  intro s' u' _ hu' _
  obtain ⟨P, hP, huP⟩ := hcontained hu'
  exact ⟨P,
    O.isUniqueContainingPath_of_exactlyOne hP huP (hexact hu')⟩

end FixedPairingPathFamily

end SimpleGraph
