import FreeFermionGraphs.Lemma11BComponents

/-!
# Lemma 11(b): pairing-side separation

Path uniqueness in Lemma 11 does not require a vertex to lie in exactly one
of all four coloring classes.  It only requires that the vertex cannot lie
on both fixed-pairing sides simultaneously.  This distinction matters when
the original and primed holes overlap.

This module isolates the weaker, exact hypothesis and derives the
at-most-one and unique-containing-path conclusions used by the
well-founded descent proof.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- A vertex cannot simultaneously belong to the two coloring-class unions
supporting the two fixed-pairing component families. -/
def PairingSideSeparated
    (O : FixedPairingPathFamily G) (v : V) : Prop :=
  ¬(v ∈ O.Ca ∪ O.Cc ∧ v ∈ O.Cb ∪ O.Cd)

/-- Exact membership in one of four classes implies pairing-side
separation, so all earlier exact-coloring results remain usable. -/
theorem pairingSideSeparated_of_exactlyOne
    (O : FixedPairingPathFamily G) {v : V}
    (h : ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd) :
    O.PairingSideSeparated v :=
  h.not_mem_ac_and_bd

/-- Pairing-side separation is precisely what is needed to show that at
most one fixed-pairing component contains a vertex. -/
theorem atMostOneContainingPath_of_pairingSideSeparated
    (O : FixedPairingPathFamily G) {v : V}
    (hv : O.PairingSideSeparated v) :
    O.AtMostOneContainingPath v := by
  intro P Q hP hQ
  rcases hP with ⟨hP, hvP⟩
  rcases hQ with ⟨hQ, hvQ⟩
  change P ∈ O.acPaths ∨ P ∈ O.bdPaths at hP
  change Q ∈ O.acPaths ∨ Q ∈ O.bdPaths at hQ
  rcases hP with hPac | hPbd
  · rcases hQ with hQac | hQbd
    · exact O.eq_of_mem_acPaths hPac hQac hvP hvQ
    · exact (hv ⟨O.ac_subset P hPac hvP,
        O.bd_subset Q hQbd hvQ⟩).elim
  · rcases hQ with hQac | hQbd
    · exact (hv ⟨O.ac_subset Q hQac hvQ,
        O.bd_subset P hPbd hvP⟩).elim
    · exact O.eq_of_mem_bdPaths hPbd hQbd hvP hvQ

/-- A displayed containing component is unique under pairing-side
separation. -/
theorem isUniqueContainingPath_of_pairingSideSeparated
    (O : FixedPairingPathFamily G) {v : V} {P : Set V}
    (hP : P ∈ O.paths) (hvP : v ∈ P)
    (hv : O.PairingSideSeparated v) :
    O.IsUniqueContainingPath v P := by
  refine ⟨hP, hvP, ?_⟩
  intro Q hQ hvQ
  exact O.atMostOneContainingPath_of_pairingSideSeparated hv
    ⟨hQ, hvQ⟩ ⟨hP, hvP⟩

end FixedPairingPathFamily

end SimpleGraph
