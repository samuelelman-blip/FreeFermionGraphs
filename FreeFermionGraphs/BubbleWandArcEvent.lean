import FreeFermionGraphs.BubbleWandHoop
import FreeFermionGraphs.BubbleWandHoppingArc

/-!
# Event-level provenance for generalized-cycle arcs

The Boolean Definition 18 arc relation records only that some bubble wand
exists.  Eq. (E1), however, attaches a generalized-cycle class to the actual
bubble event.  This module retains that event and proves that its hoop carrier
is canonical from the source carrier, target carrier, and bubble vertex.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace BubbleWand

variable {G : SimpleGraph V} {K : Set V}

/-- Once a bubble wand is presented as an arc from `P` to its handle `Q`, its
hoop is the source-minus-target suffix together with the bubble vertex. -/
theorem hoop_eq_source_diff_target_union_bubble
    (B : BubbleWand G)
    (P Q : CliqueRootedInducedPath G K)
    (hsource : P.originalCarrier = Set.range B.path.vertex)
    (htarget : Q.originalCarrier = B.handle) :
    B.hoop =
      (P.originalCarrier \ Q.originalCarrier) ∪ {B.bubble} := by
  ext v
  constructor
  · rintro ⟨hvCarrier, hvTarget⟩
    rcases hvCarrier with hvPath | hvBubble
    · left
      exact ⟨by simpa [hsource] using hvPath,
        by simpa [htarget] using hvTarget⟩
    · right
      exact hvBubble
  · rintro (⟨hvSource, hvTarget⟩ | hvBubble)
    · refine ⟨?_, by simpa [htarget] using hvTarget⟩
      left
      simpa [hsource] using hvSource
    · have hv : v = B.bubble := by simpa using hvBubble
      subst v
      exact ⟨B.bubble_mem_carrier, B.bubble_not_mem_handle⟩

end BubbleWand

/-- The hoop carrier determined by one directed bubble event. -/
def bubbleWandArcHoopCarrier
    {G : SimpleGraph V} {K : Set V}
    (P Q : CliqueRootedInducedPath G K) (j : V) : Set V :=
  (P.originalCarrier \ Q.originalCarrier) ∪ {j}

/-- A Definition 18 event retains the bubble vertex and its literal wand,
rather than truncating them to Boolean adjacency. -/
structure EvenHoopBubbleWandEvent
    (G : SimpleGraph V) (K : Set V)
    (P Q : CliqueRootedInducedPath G K) (j : V) where
  wand : BubbleWand G
  source : P.originalCarrier = Set.range wand.path.vertex
  target : Q.originalCarrier = wand.handle
  bubble : wand.bubble = j
  halfLength : Nat
  labeling : EvenHoleLabeling G halfLength
  labelCarrier : labeling.carrier = wand.hoop

namespace EvenHoopBubbleWandEvent

variable {G : SimpleGraph V} {K : Set V}
variable {P Q : CliqueRootedInducedPath G K} {j : V}

/-- The alternating even-hole label of an event has the canonical carrier
determined by its source, target, and bubble vertex. -/
theorem labelCarrier_eq_canonical
    (E : EvenHoopBubbleWandEvent G K P Q j) :
    E.labeling.carrier = bubbleWandArcHoopCarrier P Q j := by
  rw [E.labelCarrier]
  rw [E.wand.hoop_eq_source_diff_target_union_bubble
    P Q E.source E.target]
  simp [bubbleWandArcHoopCarrier, E.bubble]

/-- Every retained event gives the Boolean Definition 18 arc. -/
theorem toArc (E : EvenHoopBubbleWandEvent G K P Q j) :
    EvenHoopBubbleWandArc G K P Q :=
  ⟨E.wand, E.source, E.target, E.halfLength,
    E.labeling, E.labelCarrier⟩

end EvenHoopBubbleWandEvent

/-- Boolean Definition 18 adjacency is exactly nonemptiness of the
event-level relation for some bubble vertex. -/
theorem evenHoopBubbleWandArc_iff_exists_event
    {G : SimpleGraph V} {K : Set V}
    {P Q : CliqueRootedInducedPath G K} :
    EvenHoopBubbleWandArc G K P Q ↔
      ∃ j : V, Nonempty (EvenHoopBubbleWandEvent G K P Q j) := by
  constructor
  · rintro ⟨B, hsource, htarget, k, C, hcarrier⟩
    exact ⟨B.bubble, ⟨
      { wand := B
        source := hsource
        target := htarget
        bubble := rfl
        halfLength := k
        labeling := C
        labelCarrier := hcarrier }⟩⟩
  · rintro ⟨j, ⟨E⟩⟩
    exact E.toArc

end SimpleGraph
