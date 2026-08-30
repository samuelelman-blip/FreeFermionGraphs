import FreeFermionGraphs.BubbleWandArcEvent
import FreeFermionGraphs.EvenHoleDeformationQuotient
import FreeFermionGraphs.InducedPathDeformationBubbleWand

/-!
# Event-level bubble-wand transport under path deformation

The Boolean generalized-cycle arc used by Eq. (E1) forgets the bubble vertex,
wand, and even-hole labeling.  The underlying proof transports all of that
data and changes only a vertex in the handle.  This module retains the full
event and proves that its canonical hoop carrier, hence its quotient class,
is unchanged.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- A concrete even-hoop event transports through a deformation at or before
both displayed prefix endpoints.  The same bubble vertex and alternating
even-hole labeling are retained. -/
noncomputable def evenHoopBubbleWandEvent_deformedPrefix
    (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k j bubble : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val)
    (E : EvenHoopBubbleWandEvent G K
      (P.initialSegment r) (P.initialSegment s) bubble) :
    EvenHoopBubbleWandEvent G K
      (P.deformedPrefix h r) (P.deformedPrefix h s) bubble := by
  let B : BubbleWand G := E.wand
  let replacement := P.exists_pathVertexReplacement_of_originalCarrier_eq
    h r hir B.path (by simpa [B] using E.source) hj
  let q := Classical.choose replacement
  have hqj : B.path.vertex q = j :=
    (Classical.choose_spec replacement).1
  have hreplace : B.path.PathVertexReplacement k q :=
    (Classical.choose_spec replacement).2
  have hjTarget : j ∈ (P.initialSegment s).originalCarrier :=
    (P.mem_originalCarrier_initialSegment_iff s j).2 ⟨i, his, hj⟩
  have hjHandle : j ∈ B.handle := by
    rw [← E.target]
    exact hjTarget
  let q' := Classical.choose hjHandle
  have hq'split : q'.val ≤ B.split.val :=
    (Classical.choose_spec hjHandle).1
  have hq'j : B.path.vertex q' = j :=
    (Classical.choose_spec hjHandle).2
  have hq'q : q' = q := by
    apply B.path.injective
    exact hq'j.trans hqj.symm
  have hqsplit : q.val ≤ B.split.val := by
    rw [← hq'q]
    exact hq'split
  let B' : BubbleWand G :=
    { path := B.path.replace hreplace
      bubble := B.bubble
      split := ⟨B.split.val, by simpa using B.split.isLt⟩
      gap := by simpa using B.gap
      outside := by
        intro hb
        rcases (B.path.mem_range_replace_iff hreplace B.bubble).1 hb with
          hbk | ⟨hbRange, _⟩
        · exact B.replacement_ne_bubble hreplace hqsplit hbk.symm
        · exact B.outside hbRange
      adj_iff := by
        intro t
        by_cases htq : t = q
        · subst t
          rw [B.path.replace_vertex_at hreplace]
          rw [B.bubble_adj_replacement_iff_split hclaw hreplace hqsplit]
          change q = B.split ↔
            q.val = B.split.val ∨ q.val = B.split.val + 1 ∨
              q.val + 1 = B.path.card
          constructor
          · intro hqsplit
            exact Or.inl (congrArg Fin.val hqsplit)
          · intro hindices
            apply Fin.ext
            rcases hindices with hEq | hEq | hEq
            · exact hEq
            · omega
            · have hgap := B.gap
              omega
        · rw [B.path.replace_vertex_away hreplace htq]
          exact B.adj_iff t }
  refine
    { wand := B'
      source := ?_
      target := ?_
      bubble := ?_
      halfLength := E.halfLength
      labeling := E.labeling
      labelCarrier := ?_ }
  · ext v
    rw [P.mem_originalCarrier_deformedPrefix_iff_replace h r hir hj v]
    rw [B.path.mem_range_replace_iff hreplace v]
    rw [← E.source]
    simp [B, hqj]
  · ext v
    rw [P.mem_originalCarrier_deformedPrefix_iff_replace h s his hj v]
    change v = k ∨
        (v ∈ (P.initialSegment s).originalCarrier ∧ v ≠ j) ↔
      ∃ t : Fin B.path.card,
        t.val ≤ B.split.val ∧ (B.path.replace hreplace).vertex t = v
    rw [B.mem_handle_replace_iff hreplace hqsplit v]
    rw [E.target, hqj]
  · simpa [B, B'] using E.bubble
  · rw [E.labelCarrier]
    exact (B.hoop_replace_eq hreplace hqsplit).symm

@[simp]
theorem evenHoopBubbleWandEvent_deformedPrefix_labeling
    (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k j bubble : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val)
    (E : EvenHoopBubbleWandEvent G K
      (P.initialSegment r) (P.initialSegment s) bubble) :
    (P.evenHoopBubbleWandEvent_deformedPrefix
      hclaw h hj r s hir his E).labeling = E.labeling := by
  rfl

/-- The event-level transport leaves the canonical hoop carrier literally
unchanged. -/
theorem bubbleWandArcHoopCarrier_deformedPrefix_eq
    (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k j bubble : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val)
    (E : EvenHoopBubbleWandEvent G K
      (P.initialSegment r) (P.initialSegment s) bubble) :
    bubbleWandArcHoopCarrier
        (P.initialSegment r) (P.initialSegment s) bubble =
      bubbleWandArcHoopCarrier
        (P.deformedPrefix h r) (P.deformedPrefix h s) bubble := by
  let E' := P.evenHoopBubbleWandEvent_deformedPrefix
    hclaw h hj r s hir his E
  rw [← E.labelCarrier_eq_canonical]
  rw [← E'.labelCarrier_eq_canonical]
  change E.labeling.carrier =
    (P.evenHoopBubbleWandEvent_deformedPrefix
      hclaw h hj r s hir his E).labeling.carrier
  rw [P.evenHoopBubbleWandEvent_deformedPrefix_labeling]
  rfl

/-- Consequently the generalized-cycle quotient label attached to a retained
event is unchanged by the handle deformation. -/
theorem bubbleWandArcHoopClass_deformedPrefix_eq
    (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k j bubble : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val)
    (E : EvenHoopBubbleWandEvent G K
      (P.initialSegment r) (P.initialSegment s) bubble) :
    G.evenHoleDeformationClassOf
        (bubbleWandArcHoopCarrier
          (P.initialSegment r) (P.initialSegment s) bubble) =
      G.evenHoleDeformationClassOf
        (bubbleWandArcHoopCarrier
          (P.deformedPrefix h r) (P.deformedPrefix h s) bubble) := by
  rw [P.bubbleWandArcHoopCarrier_deformedPrefix_eq
    hclaw h hj r s hir his E]

end RootedInducedPath

end SimpleGraph
