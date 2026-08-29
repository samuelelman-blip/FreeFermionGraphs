import FreeFermionGraphs.InducedPathDeformationPrefixes
import FreeFermionGraphs.WeightedHoppingMatrix

/-!
# Eq. (E1) weights on corresponding deformation prefixes

For a deformation at index `i`, manuscript Lemma 18 compares arcs among the
prefixes `P_m` and `P̃_m` for `m ≥ i`.  This file proves the tree-arc part of
that comparison: corresponding forward extensions both have weight one, and
corresponding reverse contractions remove the same unchanged terminal vertex
and hence both have weight `b_j ^ 2`.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]

/-- Corresponding forward arcs between consecutive prefixes both have the
unit weight from the first case of Eq. (E1). -/
theorem eqE1_deformedPrefix_forward_weight
    (W : EqE1WeightData G K R)
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (m : Nat) (hm : m + 1 < P.path.card) :
    eqE1WeightedAdjacency G K W
        (P.initialSegment ⟨m, by omega⟩)
        (P.initialSegment ⟨m + 1, hm⟩) =
      eqE1WeightedAdjacency G K W
        (P.deformedPrefix h ⟨m, by omega⟩)
        (P.deformedPrefix h ⟨m + 1, hm⟩) := by
  rw [eqE1WeightedAdjacency_of_extension W
      (P.prefix_isOneVertexExtension_succ m hm)]
  rw [eqE1WeightedAdjacency_of_extension W
      (P.deformedPrefix_isOneVertexExtension_succ h m hm)]

/-- After the deformation index, the terminal vertex of a later prefix is
unchanged.  This is the local fact needed for equal reverse-tree weights. -/
theorem deformedPrefix_terminalVertex_eq
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (m : Nat) (him : i.val ≤ m) (hm : m + 1 < P.path.card) :
    (P.deformedPrefix h ⟨m + 1, hm⟩).terminalVertex =
      (P.initialSegment ⟨m + 1, hm⟩).terminalVertex := by
  let q : Fin ((m + 1) + 1) := ⟨m + 1, by omega⟩
  have hiPrefix : i.val ≤ (m + 1) := by omega
  have hqi : q ≠ deformationPrefixIndex
      (P := P) (i := i) (m := ⟨m + 1, hm⟩) hiPrefix := by
    intro hEq
    have hval : m + 1 = i.val := congrArg Fin.val hEq
    omega
  change
    (P.deformedPrefix h ⟨m + 1, hm⟩).path.vertex q =
      (P.initialSegment ⟨m + 1, hm⟩).path.vertex q
  exact P.deformedPrefix_vertex_away h
    (m := ⟨m + 1, hm⟩) hiPrefix q hqi

/-- Corresponding reverse arcs between consecutive prefixes both have the
same contraction weight `b_j ^ 2`. -/
theorem eqE1_deformedPrefix_backward_weight
    (W : EqE1WeightData G K R)
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (m : Nat) (him : i.val ≤ m) (hm : m + 1 < P.path.card) :
    eqE1WeightedAdjacency G K W
        (P.initialSegment ⟨m + 1, hm⟩)
        (P.initialSegment ⟨m, by omega⟩) =
      eqE1WeightedAdjacency G K W
        (P.deformedPrefix h ⟨m + 1, hm⟩)
        (P.deformedPrefix h ⟨m, by omega⟩) := by
  rw [eqE1WeightedAdjacency_of_contraction W
      (P.prefix_isOneVertexExtension_succ m hm)]
  rw [eqE1WeightedAdjacency_of_contraction W
      (P.deformedPrefix_isOneVertexExtension_succ h m hm)]
  unfold EqE1WeightData.contractionWeight
  rw [P.deformedPrefix_terminalVertex_eq h m him hm]

end RootedInducedPath

end SimpleGraph
