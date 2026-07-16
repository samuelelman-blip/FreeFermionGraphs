import FreeFermionGraphs.BubbleWandHoppingArc

/-!
# Fixed-pairing path families and Lemma 10

The path-family content of Definition 19.  For `(a,c)` pairing, deformation
paths split into components inside `Cₐ ∪ C'꜀` and components inside
`C_b ∪ C'ḓ`.  Components of each induced subgraph are pairwise disjoint.
These are precisely the facts used by Lemma 10.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- A vertex belongs to exactly one of four coloring classes. -/
def ExactlyOneOfFour (v : V) (A B C D : Set V) : Prop :=
  (v ∈ A ∧ v ∉ B ∧ v ∉ C ∧ v ∉ D) ∨
  (v ∈ B ∧ v ∉ A ∧ v ∉ C ∧ v ∉ D) ∨
  (v ∈ C ∧ v ∉ A ∧ v ∉ B ∧ v ∉ D) ∨
  (v ∈ D ∧ v ∉ A ∧ v ∉ B ∧ v ∉ C)

/-- Exact membership in one class prevents simultaneous membership in the
two fixed-pairing unions. -/
theorem ExactlyOneOfFour.not_mem_ac_and_bd
    {v : V} {A B C D : Set V} (h : ExactlyOneOfFour v A B C D) :
    ¬(v ∈ A ∪ C ∧ v ∈ B ∪ D) := by
  rintro ⟨hac, hbd⟩
  rcases h with hA | hB | hC | hD
  · exact hbd.elim hA.2.1 hA.2.2.2
  · exact hac.elim hB.2.1 hB.2.2.1
  · exact hbd.elim hC.2.2.1 hC.2.2.2
  · exact hac.elim hD.2.1 hD.2.2.2

/-- The two component families associated with a fixed `(a,c)` pairing.
Each member is represented by an indexed induced path in the ambient graph. -/
structure FixedPairingPathFamily (G : SimpleGraph V) where
  Ca : Set V
  Cb : Set V
  Cc : Set V
  Cd : Set V
  acPaths : Set (Set V)
  bdPaths : Set (Set V)
  ac_pairwise : acPaths.Pairwise Disjoint
  bd_pairwise : bdPaths.Pairwise Disjoint
  ac_subset : ∀ P ∈ acPaths, P ⊆ Ca ∪ Cc
  bd_subset : ∀ P ∈ bdPaths, P ⊆ Cb ∪ Cd
  ac_induced : ∀ P ∈ acPaths,
    ∃ Q : IndexedInducedPath G, Set.range Q.vertex = P
  bd_induced : ∀ P ∈ bdPaths,
    ∃ Q : IndexedInducedPath G, Set.range Q.vertex = P

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The full set `O` of paths in the fixed-pairing-type deformation. -/
def paths (O : FixedPairingPathFamily G) : Set (Set V) :=
  O.acPaths ∪ O.bdPaths

theorem eq_of_mem_acPaths (O : FixedPairingPathFamily G)
    {v : V} {P Q : Set V}
    (hP : P ∈ O.acPaths) (hQ : Q ∈ O.acPaths)
    (hvP : v ∈ P) (hvQ : v ∈ Q) : P = Q := by
  by_contra hne
  have hdisjoint := O.ac_pairwise hP hQ hne
  exact Set.disjoint_left.mp hdisjoint hvP hvQ

theorem eq_of_mem_bdPaths (O : FixedPairingPathFamily G)
    {v : V} {P Q : Set V}
    (hP : P ∈ O.bdPaths) (hQ : Q ∈ O.bdPaths)
    (hvP : v ∈ P) (hvQ : v ∈ Q) : P = Q := by
  by_contra hne
  have hdisjoint := O.bd_pairwise hP hQ hne
  exact Set.disjoint_left.mp hdisjoint hvP hvQ

/-- Lemma 10: a vertex in exactly one of the four coloring classes occurs in
at most one path component of a fixed-pairing-type deformation. -/
theorem lemma10 (O : FixedPairingPathFamily G) {v : V}
    (hv : ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd) :
    ∀ ⦃P : Set V⦄, P ∈ O.paths → v ∈ P →
      ∀ ⦃Q : Set V⦄, Q ∈ O.paths → v ∈ Q → P = Q := by
  intro P hP hvP Q hQ hvQ
  change P ∈ O.acPaths ∨ P ∈ O.bdPaths at hP
  change Q ∈ O.acPaths ∨ Q ∈ O.bdPaths at hQ
  rcases hP with hPac | hPbd
  · rcases hQ with hQac | hQbd
    · exact O.eq_of_mem_acPaths hPac hQac hvP hvQ
    · exfalso
      apply hv.not_mem_ac_and_bd
      exact ⟨O.ac_subset P hPac hvP, O.bd_subset Q hQbd hvQ⟩
  · rcases hQ with hQac | hQbd
    · exfalso
      apply hv.not_mem_ac_and_bd
      exact ⟨O.ac_subset Q hQac hvQ, O.bd_subset P hPbd hvP⟩
    · exact O.eq_of_mem_bdPaths hPbd hQbd hvP hvQ

end FixedPairingPathFamily

end SimpleGraph
