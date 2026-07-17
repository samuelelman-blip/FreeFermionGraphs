import FreeFermionGraphs.Lemma11Pairing

/-!
# Lemma 11(a.ii): degree four and opposite pairing

This module formalizes the one-step form of Lemma 11(a.ii).  A typed clone
records both the graph-theoretic relation `prime ≺_C original` and the
fixed-pairing type of that pair.  At a dependent deformation step, external
degree increases by one, so degree four after the step is equivalent to
degree three before it.  The coloring classes identify the clone pair as
having the pairing type opposite to the active deformation.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

/-- A clone of a vertex of `C`, together with its fixed-pairing type. -/
def HasTypedClone
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (C : IndexedInducedHole G) (prime : V) : Prop :=
  ∃ i : Fin C.card,
    C.SingleVertexDeformation prime i ∧
    O.HasPairingType σ prime (C.vertex i)

/-- If the original is in `Cₐ` and the prime vertex is in the class paired
with `C_b` by `σ`, their pairing type is opposite to `σ`. -/
theorem hasOppositePairingType_of_mem_a
    (O : FixedPairingPathFamily G) (σ : PairingType)
    {prime original : V}
    (horiginal : original ∈ O.Ca)
    (hprime : prime ∈ σ.classFromB O.Cc O.Cd) :
    O.HasPairingType σ.opposite prime original := by
  cases σ with
  | ac =>
      change prime ∈ O.Cd at hprime
      change O.HasPairingType .ad prime original
      exact Or.inl ⟨horiginal, hprime⟩
  | ad =>
      change prime ∈ O.Cc at hprime
      change O.HasPairingType .ac prime original
      exact Or.inl ⟨horiginal, hprime⟩

/-- Package an existing clone relation with the opposite pairing type forced
by its coloring classes. -/
theorem hasTypedClone_opposite
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (C : IndexedInducedHole G) {prime : V} {q : Fin C.card}
    (hclone : C.SingleVertexDeformation prime q)
    (horiginal : C.vertex q ∈ O.Ca)
    (hprime : prime ∈ σ.classFromB O.Cc O.Cd) :
    O.HasTypedClone σ.opposite C prime := by
  exact ⟨q, hclone,
    O.hasOppositePairingType_of_mem_a σ horiginal hprime⟩

end FixedPairingPathFamily

namespace IndexedInducedHole

/-- At a dependent one-vertex deformation, degree four after the replacement
is equivalent to degree three before it. -/
theorem SingleVertexDeformation.dependent_externalDegree_four_iff_three
    {C : IndexedInducedHole G} {Cprime : Set V}
    {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hu : u ∈ G.dependentSubset Cprime introduced (C.vertex i)) :
    (C.deform h).externalDegree u = 4 ↔
      C.externalDegree u = 3 := by
  rw [h.dependent_externalDegree_deform_eq_add_one hu]
  omega

end IndexedInducedHole

namespace FixedPairingPathFamily

/-- Lemma 11(a.ii), in one-step form.  Under the explicit clone and
coloring-class hypotheses supplied by the fixed-pairing construction,
degree four in the deformed hole is equivalent to degree three in the
original hole together with an oppositely typed clone pair. -/
theorem lemma11aii_opposite_pairing
    (O : FixedPairingPathFamily G) (σ : PairingType)
    {C : IndexedInducedHole G} {Cprime : Set V}
    {introduced u : V} {i q : Fin C.card}
    (hdeform : C.SingleVertexDeformation introduced i)
    (huDependent :
      u ∈ G.dependentSubset Cprime introduced (C.vertex i))
    (hclone : C.SingleVertexDeformation u q)
    (horiginal : C.vertex q ∈ O.Ca)
    (huClass : u ∈ σ.classFromB O.Cc O.Cd) :
    (C.deform hdeform).externalDegree u = 4 ↔
      C.externalDegree u = 3 ∧
        O.HasTypedClone σ.opposite C u := by
  have hdegree :
      (C.deform hdeform).externalDegree u = 4 ↔
        C.externalDegree u = 3 :=
    hdeform.dependent_externalDegree_four_iff_three huDependent
  have htyped : O.HasTypedClone σ.opposite C u :=
    O.hasTypedClone_opposite σ C hclone horiginal huClass
  constructor
  · intro hfour
    exact ⟨hdegree.mp hfour, htyped⟩
  · rintro ⟨hthree, _⟩
    exact hdegree.mpr hthree

end FixedPairingPathFamily

end SimpleGraph
