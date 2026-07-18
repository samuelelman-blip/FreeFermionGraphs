import FreeFermionGraphs.Lemma11BFinal

/-!
# Corollary 11: comparison setup

Corollary 11 compares two possibly equal deformations having the same
fixed-pairing type.  This module records that compatibility relation and
the forbidden configuration from the paper: one vertex lying in dependent
sets for two distinct active path components and anticommuting with both
path operators.

The final theorem needs the local endpoint and claw-free analysis from the
proof of Corollary 11.  Here we isolate its first uniform consequence:
each of the two anticommutation assumptions gives exactly one or three
neighbors on the corresponding induced path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Two deformation families use the same four coloring classes and hence
the same fixed-pairing type.

A `FixedPairingPathFamily` represents the `(a,c)` convention by putting
its two component families in `Cₐ ∪ C'꜀` and `C_b ∪ C'ḓ`.  Equality of
the four classes is therefore the compatibility required when comparing
two such deformations in Corollary 11. -/
def SameFixedPairingType
    (O O' : FixedPairingPathFamily G) : Prop :=
  O.Ca = O'.Ca ∧
    O.Cb = O'.Cb ∧
    O.Cc = O'.Cc ∧
    O.Cd = O'.Cd

theorem sameFixedPairingType_refl
    (O : FixedPairingPathFamily G) :
    O.SameFixedPairingType O :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sameFixedPairingType_symm
    {O O' : FixedPairingPathFamily G}
    (h : O.SameFixedPairingType O') :
    O'.SameFixedPairingType O := by
  rcases h with ⟨hCa, hCb, hCc, hCd⟩
  exact ⟨hCa.symm, hCb.symm, hCc.symm, hCd.symm⟩

theorem sameFixedPairingType_trans
    {O O' O'' : FixedPairingPathFamily G}
    (h₁ : O.SameFixedPairingType O')
    (h₂ : O'.SameFixedPairingType O'') :
    O.SameFixedPairingType O'' := by
  rcases h₁ with ⟨hCa₁, hCb₁, hCc₁, hCd₁⟩
  rcases h₂ with ⟨hCa₂, hCb₂, hCc₂, hCd₂⟩
  exact ⟨hCa₁.trans hCa₂, hCb₁.trans hCb₂,
    hCc₁.trans hCc₂, hCd₁.trans hCd₂⟩

/-- Exact coloring-class membership transports between deformations of the
same fixed-pairing type. -/
theorem exactlyOneOfFour_iff_of_sameFixedPairingType
    {O O' : FixedPairingPathFamily G}
    (h : O.SameFixedPairingType O') (u : V) :
    ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd ↔
      ExactlyOneOfFour u O'.Ca O'.Cb O'.Cc O'.Cd := by
  rcases h with ⟨hCa, hCb, hCc, hCd⟩
  simp only [hCa, hCb, hCc, hCd]

/-- The bad configuration excluded by Corollary 11 for two fixed active
paths.  The functions `U` and `U'` are their dependent subsets indexed
by the deformation step. -/
def SharedDependentAnticommutingWitness
    (P Q : IndexedInducedPath G)
    (U U' : Nat → Set V) : Prop :=
  ∃ (u : V) (s t : Nat),
    u ∈ U s ∧
      u ∈ U' t ∧
      P.AnticommutesWith u ∧
      Q.AnticommutesWith u

theorem sharedDependentAnticommutingWitness_symm
    (P Q : IndexedInducedPath G)
    (U U' : Nat → Set V) :
    SharedDependentAnticommutingWitness P Q U U' ↔
      SharedDependentAnticommutingWitness Q P U' U := by
  constructor
  · rintro ⟨u, s, t, hu, hu', hP, hQ⟩
    exact ⟨u, t, s, hu', hu, hQ, hP⟩
  · rintro ⟨u, t, s, hu', hu, hQ, hP⟩
    exact ⟨u, s, t, hu, hu', hP, hQ⟩

/-- The first reduction in Corollary 11.  A shared witness has either one
or three neighbors on each active path. -/
theorem SharedDependentAnticommutingWitness.neighborCount_cases
    (P Q : IndexedInducedPath G)
    (hclaw : G.IsClawFree)
    (U U' : Nat → Set V)
    (hPoutside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → u ∉ Set.range P.vertex)
    (hQoutside : ∀ ⦃t : Nat⦄ ⦃u : V⦄,
      u ∈ U' t → u ∉ Set.range Q.vertex)
    (h : SharedDependentAnticommutingWitness P Q U U') :
    ∃ (u : V) (s t : Nat),
      u ∈ U s ∧
        u ∈ U' t ∧
        ((P.neighborIndexSet u).ncard = 1 ∨
          (P.neighborIndexSet u).ncard = 3) ∧
        ((Q.neighborIndexSet u).ncard = 1 ∨
          (Q.neighborIndexSet u).ncard = 3) := by
  obtain ⟨u, s, t, hu, hu', hP, hQ⟩ := h
  exact ⟨u, s, t, hu, hu',
    P.anticommutesWith_count_eq_one_or_three
      hclaw (hPoutside hu) hP,
    Q.anticommutesWith_count_eq_one_or_three
      hclaw (hQoutside hu') hQ⟩

/-- The exact no-shared-witness conclusion of Corollary 11, formulated for
indexed families of active paths and their dependent subsets. -/
def Corollary11Property
    (O O' : FixedPairingPathFamily G)
    (P Q : Nat → IndexedInducedPath G)
    (U U' : Nat → Nat → Set V) : Prop :=
  O.SameFixedPairingType O' ∧
    ∀ ⦃r g : Nat⦄,
      Set.range (P r).vertex ∈ O.paths →
      Set.range (Q g).vertex ∈ O'.paths →
      Set.range (P r).vertex ≠ Set.range (Q g).vertex →
      ¬SharedDependentAnticommutingWitness
        (P r) (Q g) (U r) (U' g)

end FixedPairingPathFamily

end SimpleGraph
