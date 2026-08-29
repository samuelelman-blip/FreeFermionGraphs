import FreeFermionGraphs.InducedPathDeformationBubbleWand

/-!
# Local Eq. (E1) invariance under a path deformation

This file combines the tree and generalized-cycle cases of manuscript Lemma
18.  For any two prefix indices at or after the changed vertex, the complete
Eq. (E1) entry agrees with the entry between the corresponding deformed
prefixes.  The only algebraic input is that the chosen generalized-cycle
closure label and normalization assign the same bubble weight to the two
concrete bubble-wand arcs whose equivalence was proved graph-theoretically.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {root : V}

/-- One prefix is a one-vertex extension of another exactly when its endpoint
index is the successor endpoint index. -/
theorem initialSegment_isOneVertexExtension_iff
    (P : RootedInducedPath G root) (r s : Fin P.path.card) :
    (P.initialSegment r).IsOneVertexExtension (P.initialSegment s) ↔
      r.val + 1 = s.val := by
  constructor
  · rintro ⟨hcard, _⟩
    change (r.val + 1) + 1 = s.val + 1 at hcard
    omega
  · intro hrs
    refine ⟨by change (r.val + 1) + 1 = s.val + 1; omega, ?_⟩
    intro q
    rfl

end RootedInducedPath

namespace EqE1WeightData

variable {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]

/-- The normalization choice in Eq. (E1) is compatible with the concrete
deformation transport of generalized-cycle arcs.

This is a semantic law of the Eq. (E1) weight data, not an amplitude or walk
invariance assumption.  It says that the same hoop deformation class carries
the same generalized-cycle eigenvalue and normalization after replacing a
handle vertex, exactly as in the generalized-cycle paragraph of the paper. -/
structure IsDeformationCompatible (W : EqE1WeightData G K R) : Prop where
  bubbleWeight_eq :
    ∀ (P : CliqueRootedInducedPath G K) {k j : V}
      {i : Fin P.path.card}
      (h : P.path.SingleVertexDeformation (some k) i)
      (hj : P.path.vertex i = some j)
      (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val),
      EvenHoopBubbleWandArc G K (P.initialSegment r) (P.initialSegment s) →
      W.bubbleWeight (P.initialSegment r) (P.initialSegment s) =
        W.bubbleWeight (P.deformedPrefix h r) (P.deformedPrefix h s)

end EqE1WeightData

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]

/-- Every local Eq. (E1) entry among prefixes at or after the deformation
index is preserved.  This is the complete local arc comparison used in the
walk substitution of manuscript Lemma 18. -/
theorem eqE1_deformedPrefix_weight
    (hK : G.IsClique K) (hclaw : G.IsClawFree)
    (W : EqE1WeightData G K R) (hW : W.IsDeformationCompatible)
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val) :
    eqE1WeightedAdjacency G K W (P.initialSegment r) (P.initialSegment s) =
      eqE1WeightedAdjacency G K W
        (P.deformedPrefix h r) (P.deformedPrefix h s) := by
  have hforward :
      (P.initialSegment r).IsOneVertexExtension (P.initialSegment s) ↔
        (P.deformedPrefix h r).IsOneVertexExtension
          (P.deformedPrefix h s) := by
    rw [P.initialSegment_isOneVertexExtension_iff r s]
    exact ((P.deform h).initialSegment_isOneVertexExtension_iff r s).symm
  have hbackward :
      (P.initialSegment s).IsOneVertexExtension (P.initialSegment r) ↔
        (P.deformedPrefix h s).IsOneVertexExtension
          (P.deformedPrefix h r) := by
    rw [P.initialSegment_isOneVertexExtension_iff s r]
    exact ((P.deform h).initialSegment_isOneVertexExtension_iff s r).symm
  have hbubble := P.evenHoopBubbleWandArc_deformedPrefix_iff
    hclaw h hj r s hir his
  by_cases hf : (P.initialSegment r).IsOneVertexExtension (P.initialSegment s)
  · have hf' := hforward.mp hf
    rw [eqE1WeightedAdjacency_of_extension W hf]
    rw [eqE1WeightedAdjacency_of_extension W hf']
  · have hf' : ¬(P.deformedPrefix h r).IsOneVertexExtension
        (P.deformedPrefix h s) := by
      exact fun hcontra => hf (hforward.mpr hcontra)
    by_cases hb : (P.initialSegment s).IsOneVertexExtension (P.initialSegment r)
    · have hb' := hbackward.mp hb
      rw [eqE1WeightedAdjacency_of_contraction W hb]
      rw [eqE1WeightedAdjacency_of_contraction W hb']
      unfold EqE1WeightData.contractionWeight
      have hterminal : (P.deformedPrefix h r).terminalVertex =
          (P.initialSegment r).terminalVertex := by
        by_cases hri : r.val = i.val
        · have hcard : (P.initialSegment s).path.card + 1 =
              (P.initialSegment r).path.card := hb.choose
          change s.val + 1 + 1 = r.val + 1 at hcard
          omega
        · let m := r.val - 1
          have hm : m + 1 < P.path.card := by
            dsimp [m]
            omega
          have him : i.val ≤ m := by
            dsimp [m]
            omega
          have hrm : r = ⟨m + 1, hm⟩ := by
            apply Fin.ext
            dsimp [m]
            omega
          rw [hrm]
          exact P.deformedPrefix_terminalVertex_eq h m him hm
      rw [hterminal]
    · have hb' : ¬(P.deformedPrefix h s).IsOneVertexExtension
          (P.deformedPrefix h r) := by
        exact fun hcontra => hb (hbackward.mpr hcontra)
      by_cases hc : EvenHoopBubbleWandArc G K
          (P.initialSegment r) (P.initialSegment s)
      · have hc' := hbubble.mp hc
        have htree : ¬(G.inducedPathTreeAtClique K hK).Adj
            (P.initialSegment r) (P.initialSegment s) := by
          exact fun hadj => hadj.elim hf hb
        have htree' : ¬(G.inducedPathTreeAtClique K hK).Adj
            (P.deformedPrefix h r) (P.deformedPrefix h s) := by
          exact fun hadj => hadj.elim hf' hb'
        rw [eqE1WeightedAdjacency_of_bubbleWand hK W htree hc]
        rw [eqE1WeightedAdjacency_of_bubbleWand hK W htree' hc']
        exact hW.bubbleWeight_eq P h hj r s hir his hc
      · have hc' : ¬EvenHoopBubbleWandArc G K
            (P.deformedPrefix h r) (P.deformedPrefix h s) := by
          exact fun hcontra => hc (hbubble.mpr hcontra)
        simp [eqE1WeightedAdjacency, hf, hf', hb, hb', hc, hc']

end RootedInducedPath

end SimpleGraph
