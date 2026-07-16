import FreeFermionGraphs.FixedPairingPaths

/-!
# Corollary 7

The endpoints of a path in a fixed-pairing-type deformation occur in no
other path of the deformation.  This is the direct endpoint application of
Lemma 10.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- `P` is the unique path in `O` containing `v`. -/
def IsUniqueContainingPath (O : FixedPairingPathFamily G)
    (v : V) (P : Set V) : Prop :=
  P ∈ O.paths ∧ v ∈ P ∧
    ∀ ⦃Q : Set V⦄, Q ∈ O.paths → v ∈ Q → Q = P

/-- A vertex in exactly one coloring class has a unique containing path,
provided it belongs to a path of the deformation. -/
theorem isUniqueContainingPath_of_exactlyOne
    (O : FixedPairingPathFamily G) {v : V} {P : Set V}
    (hP : P ∈ O.paths) (hvP : v ∈ P)
    (hv : ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd) :
    O.IsUniqueContainingPath v P := by
  refine ⟨hP, hvP, ?_⟩
  intro Q hQ hvQ
  exact O.lemma10 hv hQ hvQ hP hvP

/-- Corollary 7: the initializing and terminal endpoints of a deformation
path are not contained in any other path in `O`.  Definition 19 supplies the
two exact-coloring-class hypotheses for its displayed endpoints. -/
theorem corollary7 (O : FixedPairingPathFamily G)
    {P : Set V} (hP : P ∈ O.paths) {initial terminal : V}
    (hinitialP : initial ∈ P) (hterminalP : terminal ∈ P)
    (hinitial : ExactlyOneOfFour initial O.Ca O.Cb O.Cc O.Cd)
    (hterminal : ExactlyOneOfFour terminal O.Ca O.Cb O.Cc O.Cd) :
    O.IsUniqueContainingPath initial P ∧
      O.IsUniqueContainingPath terminal P := by
  exact ⟨O.isUniqueContainingPath_of_exactlyOne hP hinitialP hinitial,
    O.isUniqueContainingPath_of_exactlyOne hP hterminalP hterminal⟩

end FixedPairingPathFamily

end SimpleGraph
