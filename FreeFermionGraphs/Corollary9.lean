import FreeFermionGraphs.Corollary8

/-!
# Corollary 9

A vertex occurs in at most one path from each of the two fixed-pairing
families, hence in at most two paths overall.  If two distinct paths meet,
one is an `ac` path and the other is a `bd` path; their shared vertex lies
in both corresponding coloring-class unions.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The paths of `O` that contain `v`. -/
def containingPaths (O : FixedPairingPathFamily G) (v : V) : Set (Set V) :=
  {P | P ∈ O.paths ∧ v ∈ P}

/-- A carrier-level formulation of “at most two path components contain
`v`”: among any three such paths, two are equal. -/
def AtMostTwoContainingPaths (O : FixedPairingPathFamily G) (v : V) : Prop :=
  ∀ ⦃P Q R : Set V⦄,
    P ∈ O.containingPaths v →
    Q ∈ O.containingPaths v →
    R ∈ O.containingPaths v →
    P = Q ∨ P = R ∨ Q = R

theorem atMostTwoContainingPaths (O : FixedPairingPathFamily G) (v : V) :
    O.AtMostTwoContainingPaths v := by
  intro P Q R hP hQ hR
  rcases hP with ⟨hP, hvP⟩
  rcases hQ with ⟨hQ, hvQ⟩
  rcases hR with ⟨hR, hvR⟩
  change P ∈ O.acPaths ∨ P ∈ O.bdPaths at hP
  change Q ∈ O.acPaths ∨ Q ∈ O.bdPaths at hQ
  change R ∈ O.acPaths ∨ R ∈ O.bdPaths at hR
  rcases hP with hPac | hPbd
  · rcases hQ with hQac | hQbd
    · exact Or.inl (O.eq_of_mem_acPaths hPac hQac hvP hvQ)
    · rcases hR with hRac | hRbd
      · exact Or.inr (Or.inl (O.eq_of_mem_acPaths hPac hRac hvP hvR))
      · exact Or.inr (Or.inr (O.eq_of_mem_bdPaths hQbd hRbd hvQ hvR))
  · rcases hQ with hQac | hQbd
    · rcases hR with hRac | hRbd
      · exact Or.inr (Or.inr (O.eq_of_mem_acPaths hQac hRac hvQ hvR))
      · exact Or.inr (Or.inl (O.eq_of_mem_bdPaths hPbd hRbd hvP hvR))
    · exact Or.inl (O.eq_of_mem_bdPaths hPbd hQbd hvP hvQ)

/-- Two distinct paths containing the same vertex lie on opposite pairing
sides.  This is the set-level content of the labeled intersection conclusion
in Corollary 9. -/
theorem distinct_containingPaths_cross_pairing
    (O : FixedPairingPathFamily G) {v : V} {P Q : Set V}
    (hP : P ∈ O.containingPaths v)
    (hQ : Q ∈ O.containingPaths v)
    (hne : P ≠ Q) :
    (((P ∈ O.acPaths ∧ Q ∈ O.bdPaths) ∨
        (P ∈ O.bdPaths ∧ Q ∈ O.acPaths)) ∧
      v ∈ (O.Ca ∪ O.Cc) ∩ (O.Cb ∪ O.Cd)) := by
  rcases hP with ⟨hP, hvP⟩
  rcases hQ with ⟨hQ, hvQ⟩
  change P ∈ O.acPaths ∨ P ∈ O.bdPaths at hP
  change Q ∈ O.acPaths ∨ Q ∈ O.bdPaths at hQ
  rcases hP with hPac | hPbd
  · rcases hQ with hQac | hQbd
    · exact (hne (O.eq_of_mem_acPaths hPac hQac hvP hvQ)).elim
    · exact ⟨Or.inl ⟨hPac, hQbd⟩,
        ⟨O.ac_subset P hPac hvP, O.bd_subset Q hQbd hvQ⟩⟩
  · rcases hQ with hQac | hQbd
    · exact ⟨Or.inr ⟨hPbd, hQac⟩,
        ⟨O.ac_subset Q hQac hvQ, O.bd_subset P hPbd hvP⟩⟩
    · exact (hne (O.eq_of_mem_bdPaths hPbd hQbd hvP hvQ)).elim

/-- Corollary 9: every vertex belongs to at most two path components, and
distinct components meeting at a vertex have opposite pairing sides. -/
theorem corollary9 (O : FixedPairingPathFamily G) :
    (∀ v, O.AtMostTwoContainingPaths v) ∧
      ∀ ⦃v : V⦄ ⦃P Q : Set V⦄,
        P ∈ O.containingPaths v →
        Q ∈ O.containingPaths v →
        P ≠ Q →
        (((P ∈ O.acPaths ∧ Q ∈ O.bdPaths) ∨
            (P ∈ O.bdPaths ∧ Q ∈ O.acPaths)) ∧
          v ∈ (O.Ca ∪ O.Cc) ∩ (O.Cb ∪ O.Cd)) := by
  refine ⟨O.atMostTwoContainingPaths, ?_⟩
  intro v P Q hP hQ hne
  exact O.distinct_containingPaths_cross_pairing hP hQ hne

end FixedPairingPathFamily

end SimpleGraph
