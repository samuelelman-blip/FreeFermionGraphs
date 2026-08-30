import FreeFermionGraphs.IndexedInducedHoleEvenLabeling
import FreeFermionGraphs.IndexedPathClosure
import FreeFermionGraphs.BubbleWand

/-!
# The indexed hoop of a bubble wand

The part of a bubble wand after its handle is an induced path of at least
three vertices.  Closing its endpoints with the bubble vertex constructs the
literal indexed induced hole whose carrier is `B.hoop`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace BubbleWand

variable {G : SimpleGraph V}

/-- The path suffix strictly after the handle of a bubble wand. -/
def hoopPath (B : BubbleWand G) : IndexedInducedPath G where
  card := B.path.card - (B.split.val + 1)
  nonempty := by
    have := B.gap
    omega
  vertex q := B.path.vertex
    ⟨q.val + B.split.val + 1, by
      have hq := q.isLt
      have := B.gap
      omega⟩
  injective := by
    intro p q hpq
    apply Fin.ext
    have hindex := B.path.injective hpq
    have hval := congrArg Fin.val hindex
    change p.val + B.split.val + 1 =
      q.val + B.split.val + 1 at hval
    omega
  adj_iff := by
    intro p q
    rw [B.path.adj_iff]
    change
      (p.val + B.split.val + 1 + 1 =
          q.val + B.split.val + 1 ∨
        q.val + B.split.val + 1 + 1 =
          p.val + B.split.val + 1) ↔
      p.val + 1 = q.val ∨ q.val + 1 = p.val
    omega

@[simp]
theorem hoopPath_card (B : BubbleWand G) :
    B.hoopPath.card = B.path.card - (B.split.val + 1) :=
  rfl

/-- The bubble is adjacent exactly to the two endpoints of the hoop suffix. -/
theorem hoopPath_endpointClosureData (B : BubbleWand G) :
    B.hoopPath.EndpointClosureData B.bubble := by
  refine
    { three_le := by
        change 3 ≤ B.path.card - (B.split.val + 1)
        have := B.gap
        omega
      outside := ?_
      adj_iff := ?_ }
  · rintro ⟨q, hq⟩
    apply B.outside
    exact ⟨⟨q.val + B.split.val + 1, by
      have hqLt := q.isLt
      change q.val < B.path.card - (B.split.val + 1) at hqLt
      have := B.gap
      omega⟩, hq⟩
  · intro q
    change G.Adj B.bubble
        (B.path.vertex ⟨q.val + B.split.val + 1, by
          have hqLt := q.isLt
          change q.val < B.path.card - (B.split.val + 1) at hqLt
          have := B.gap
          omega⟩) ↔
      q.val = 0 ∨ q.val + 1 = B.path.card - (B.split.val + 1)
    rw [B.adj_iff]
    change
      (q.val + B.split.val + 1 = B.split.val ∨
        q.val + B.split.val + 1 = B.split.val + 1 ∨
        q.val + B.split.val + 1 + 1 = B.path.card) ↔
      q.val = 0 ∨
        q.val + 1 = B.path.card - (B.split.val + 1)
    constructor
    · rintro (hsplit | hnext | hterminal)
      · omega
      · left
        omega
      · right
        omega
    · rintro (hfirst | hlast)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))

/-- The indexed induced hole obtained by closing the post-handle path suffix
with the bubble vertex. -/
def hoopHole (B : BubbleWand G) : IndexedInducedHole G :=
  B.hoopPath.closeToHole B.hoopPath_endpointClosureData

/-- The constructed indexed hole has exactly the set-theoretic hoop carrier
from Definition 11. -/
theorem range_hoopHole (B : BubbleWand G) :
    Set.range B.hoopHole.vertex = B.hoop := by
  rw [hoopHole, IndexedInducedPath.range_closeToHole]
  ext v
  constructor
  · rintro (⟨q, hq⟩ | hvBubble)
    · refine ⟨Or.inl ?_, ?_⟩
      · exact ⟨⟨q.val + B.split.val + 1, by
          have hqLt := q.isLt
          change q.val < B.path.card - (B.split.val + 1) at hqLt
          have := B.gap
          omega⟩, hq⟩
      · rintro ⟨r, hrle, hr⟩
        have heq := B.path.injective (hr.trans hq.symm)
        have hval := congrArg Fin.val heq
        change r.val = q.val + B.split.val + 1 at hval
        omega
    · have hv : v = B.bubble := by simpa using hvBubble
      subst v
      exact B.bubble_mem_hoop
  · rintro ⟨hvCarrier, hvHandle⟩
    rcases hvCarrier with ⟨q, hq⟩ | hvBubble
    · have hqAfter : B.split.val < q.val := by
        by_contra hle
        apply hvHandle
        exact ⟨q, by omega, hq⟩
      let r : Fin B.hoopPath.card :=
        ⟨q.val - (B.split.val + 1), by
          change q.val - (B.split.val + 1) <
            B.path.card - (B.split.val + 1)
          have hqLt := q.isLt
          omega⟩
      left
      refine ⟨r, ?_⟩
      change B.path.vertex
          ⟨r.val + B.split.val + 1, by
            have hrLt := r.isLt
            change r.val < B.path.card - (B.split.val + 1) at hrLt
            have := B.gap
            omega⟩ = v
      rw [← hq]
      apply congrArg B.path.vertex
      apply Fin.ext
      dsimp [r]
      omega
    · right
      simpa only [Set.mem_singleton_iff] using hvBubble

end BubbleWand

end SimpleGraph
