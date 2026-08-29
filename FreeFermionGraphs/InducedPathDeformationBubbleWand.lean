import FreeFermionGraphs.InducedPathDeformationPrefixWeights

/-!
# Bubble-wand arcs under an induced-path deformation

This file treats the generalized-cycle case in the local arc comparison for
manuscript Lemma 18.  Its first layer records the carrier facts needed to
transport an even-hoop bubble wand through a deformation of a clique-rooted
path.  In particular, every non-root path vertex and every deformation clone
is an original `V`-vertex rather than the adjoined clique root.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The path-preserving part of a vertex replacement.  Unlike manuscript
Definition 10, this structure deliberately permits replacing an endpoint.
That slightly more general operation is needed when an internal vertex of a
clique-rooted path is the first vertex of the same path after the fresh root
has been discarded from a bubble-wand witness. -/
structure PathVertexReplacement
    (P : IndexedInducedPath G) (s : V) (i : Fin P.card) : Prop where
  outside : s ∉ Set.range P.vertex
  adj_iff : ∀ q : Fin P.card,
    G.Adj s (P.vertex q) ↔
      q = i ∨ G.Adj (P.vertex i) (P.vertex q)

/-- Perform a path-preserving replacement, retaining the path order. -/
def replace (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.PathVertexReplacement s i) : IndexedInducedPath G where
  card := P.card
  nonempty := P.nonempty
  vertex := P.replaceVertex s i
  injective := by
    intro p q hpq
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · exact hq.symm
      · have hsq : s = P.vertex q := by
          simpa [replaceVertex, hq] using hpq
        exact (h.outside ⟨q, hsq.symm⟩).elim
    · by_cases hq : q = i
      · subst q
        have hps : P.vertex p = s := by
          simpa [replaceVertex, hp] using hpq
        exact (h.outside ⟨p, hps⟩).elim
      · exact P.injective (by
          simpa [replaceVertex, hp, hq] using hpq)
  adj_iff := by
    intro p q
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · subst q
        apply iff_of_false
        · simpa [replaceVertex] using G.loopless.irrefl s
        · omega
      · simp only [replaceVertex, if_pos, if_neg hq]
        rw [h.adj_iff q, P.adj_iff i q]
        simp [hq]
    · by_cases hq : q = i
      · subst q
        simp only [replaceVertex, if_neg hp, if_pos]
        have hs :
            G.Adj s (P.vertex p) ↔
              i.val + 1 = p.val ∨ p.val + 1 = i.val := by
          rw [h.adj_iff p, P.adj_iff i p]
          simp [hp]
        constructor
        · intro hps
          rcases hs.mp hps.symm with hip | hpi
          · exact Or.inr hip
          · exact Or.inl hpi
        · intro hlin
          apply (hs.mpr ?_).symm
          rcases hlin with hpi | hip
          · exact Or.inr hpi
          · exact Or.inl hip
      · simp only [replaceVertex, if_neg hp, if_neg hq]
        exact P.adj_iff p q

@[simp]
theorem replace_card (P : IndexedInducedPath G) {s : V}
    {i : Fin P.card} (h : P.PathVertexReplacement s i) :
    (P.replace h).card = P.card :=
  rfl

@[simp]
theorem replace_vertex_at (P : IndexedInducedPath G) {s : V}
    {i : Fin P.card} (h : P.PathVertexReplacement s i) :
    (P.replace h).vertex i = s := by
  simp [replace]

@[simp]
theorem replace_vertex_away (P : IndexedInducedPath G) {s : V}
    {i q : Fin P.card} (h : P.PathVertexReplacement s i) (hqi : q ≠ i) :
    (P.replace h).vertex q = P.vertex q := by
  simp [replace, hqi]

/-- The carrier of a path-preserving replacement is obtained by deleting the
old indexed vertex and inserting the replacement vertex. -/
theorem mem_range_replace_iff
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.PathVertexReplacement s i) (v : V) :
    v ∈ Set.range (P.replace h).vertex ↔
      v = s ∨ (v ∈ Set.range P.vertex ∧ v ≠ P.vertex i) := by
  constructor
  · rintro ⟨q, hq⟩
    by_cases hqi : q = i
    · subst q
      exact Or.inl (hq.symm.trans (P.replace_vertex_at h))
    · right
      have hvertex : P.vertex q = v :=
        (P.replace_vertex_away h hqi).symm.trans hq
      refine ⟨⟨q, hvertex⟩, ?_⟩
      intro hvi
      exact hqi (P.injective (hvertex.trans hvi))
  · rintro (rfl | ⟨⟨q, hq⟩, hne⟩)
    · exact ⟨i, P.replace_vertex_at h⟩
    · have hqi : q ≠ i := by
        intro hEq
        subst q
        exact hne hq.symm
      exact ⟨q, (P.replace_vertex_away h hqi).trans hq⟩

/-- Taking an initial segment respects equality of indexed paths, with the
index transported across the induced equality of cardinalities. -/
theorem initialSegment_congr
    {P Q : IndexedInducedPath G} (h : P = Q) (m : Fin P.card) :
    P.initialSegment m =
      Q.initialSegment (Fin.cast (congrArg IndexedInducedPath.card h) m) := by
  subst Q
  rfl

end IndexedInducedPath

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- Rooted induced paths are determined by their indexed path; the root
certificate is proof-irrelevant. -/
theorem ext_path {root : Option V}
    {P Q : RootedInducedPath (G.adjoinRootAt K) root}
    (h : P.path = Q.path) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Every positive-index vertex of a clique-rooted path is an original graph
vertex.  The only occurrence of the adjoined `none` vertex is the root at
index zero. -/
theorem vertex_eq_some_of_pos
    (P : CliqueRootedInducedPath G K) (i : Fin P.path.card)
    (hi : 0 < i.val) :
    ∃ v : V, P.path.vertex i = some v := by
  cases hvertex : P.path.vertex i with
  | some v => exact ⟨v, rfl⟩
  | none =>
      have hroot : P.path.vertex ⟨0, P.path.nonempty⟩ = none := P.root_eq
      have hii : i = ⟨0, P.path.nonempty⟩ :=
        P.path.injective (hvertex.trans hroot.symm)
      have hval : i.val = 0 := congrArg Fin.val hii
      omega

/-- A Definition 10 deformation of a clique-rooted path cannot insert the
fresh root, since that root already occurs in the path. -/
theorem deformation_vertex_eq_some
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i) :
    ∃ v : V, s = some v := by
  cases s with
  | some v => exact ⟨v, rfl⟩
  | none =>
      exact (h.outside ⟨⟨0, P.path.nonempty⟩, P.root_eq⟩).elim

/-- Membership in the original carrier of `P_m`, written using the ambient
indexing of `P`. -/
theorem mem_originalCarrier_initialSegment_iff
    (P : CliqueRootedInducedPath G K) (m : Fin P.path.card) (v : V) :
    v ∈ (P.initialSegment m).originalCarrier ↔
      ∃ q : Fin P.path.card,
        q.val ≤ m.val ∧ P.path.vertex q = some v := by
  constructor
  · rintro ⟨⟨q, hq_lt⟩, hq⟩
    change q < m.val + 1 at hq_lt
    exact ⟨⟨q, by omega⟩, (show q ≤ m.val by omega), hq⟩
  · rintro ⟨q, hqm, hq⟩
    refine ⟨⟨q.val, by change q.val < m.val + 1; omega⟩, ?_⟩
    exact hq

/-- Membership in the original carrier of the deformed prefix `P̃_m`,
again written using the ambient indexing shared by `P` and `P.deform h`. -/
theorem mem_originalCarrier_deformedPrefix_iff
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (m : Fin P.path.card) (v : V) :
    v ∈ (P.deformedPrefix h m).originalCarrier ↔
      ∃ q : Fin P.path.card,
        q.val ≤ m.val ∧ (P.path.deform h).vertex q = some v := by
  constructor
  · rintro ⟨⟨q, hq_lt⟩, hq⟩
    change q < m.val + 1 at hq_lt
    exact ⟨⟨q, by omega⟩, (show q ≤ m.val by omega), hq⟩
  · rintro ⟨q, hqm, hq⟩
    refine ⟨⟨q.val, by change q.val < m.val + 1; omega⟩, ?_⟩
    exact hq

/-- The original carrier of a deformed prefix is obtained by replacing the
old vertex by its clone. -/
theorem mem_originalCarrier_deformedPrefix_iff_replace
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (m : Fin P.path.card) (him : i.val ≤ m.val)
    (hj : P.path.vertex i = some j) (v : V) :
    v ∈ (P.deformedPrefix h m).originalCarrier ↔
      v = k ∨
        (v ∈ (P.initialSegment m).originalCarrier ∧ v ≠ j) := by
  rw [P.mem_originalCarrier_deformedPrefix_iff h m v]
  constructor
  · rintro ⟨q, hqm, hq⟩
    by_cases hqi : q = i
    · subst q
      exact Or.inl (Option.some.inj
        (hq.symm.trans (P.path.deform_vertex_at h)))
    · right
      have hvertex : P.path.vertex q = some v :=
        (P.path.deform_vertex_away h hqi).symm.trans hq
      refine ⟨(P.mem_originalCarrier_initialSegment_iff m v).2
        ⟨q, hqm, hvertex⟩, ?_⟩
      intro hvj
      apply hqi
      apply P.path.injective
      exact hvertex.trans (congrArg some hvj) |>.trans hj.symm
  · rintro (rfl | ⟨hvmem, hvj⟩)
    · exact ⟨i, him, P.path.deform_vertex_at h⟩
    · rcases (P.mem_originalCarrier_initialSegment_iff m v).1 hvmem with
        ⟨q, hqm, hq⟩
      have hqi : q ≠ i := by
        intro hEq
        subst q
        exact hvj (Option.some.inj (hq.symm.trans hj))
      exact ⟨q, hqm, (P.path.deform_vertex_away h hqi).trans hq⟩

/-- Transfer the local replacement law from a clique-rooted prefix to any
indexed original-graph path with the same carrier.  No orientation choice is
needed: inducedness and injectivity identify the changed vertex intrinsically
by its value. -/
theorem exists_pathVertexReplacement_of_originalCarrier_eq
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (m : Fin P.path.card) (him : i.val ≤ m.val)
    (B : IndexedInducedPath G)
    (hcarrier : (P.initialSegment m).originalCarrier = Set.range B.vertex)
    (hj : P.path.vertex i = some j) :
    ∃ q : Fin B.card,
      B.vertex q = j ∧ B.PathVertexReplacement k q := by
  have hjmem : j ∈ (P.initialSegment m).originalCarrier :=
    (P.mem_originalCarrier_initialSegment_iff m j).2 ⟨i, him, hj⟩
  rw [hcarrier] at hjmem
  rcases hjmem with ⟨q, hqj⟩
  refine ⟨q, hqj, ?_⟩
  refine
    { outside := ?_
      adj_iff := ?_ }
  · rintro ⟨t, htk⟩
    have hkmem : k ∈ (P.initialSegment m).originalCarrier := by
      rw [hcarrier]
      exact ⟨t, htk⟩
    rcases (P.mem_originalCarrier_initialSegment_iff m k).1 hkmem with
      ⟨p, _, hpk⟩
    exact h.outside ⟨p, hpk⟩
  · intro t
    have htmem : B.vertex t ∈ (P.initialSegment m).originalCarrier := by
      rw [hcarrier]
      exact ⟨t, rfl⟩
    rcases (P.mem_originalCarrier_initialSegment_iff m (B.vertex t)).1 htmem with
      ⟨p, _, hp⟩
    have hpi_iff : p = i ↔ t = q := by
      constructor
      · intro hpi
        subst p
        apply B.injective
        exact Option.some.inj (hp.symm.trans (hj.trans (congrArg some hqj.symm)))
      · intro htq
        subst t
        apply P.path.injective
        exact hp.trans (congrArg some hqj) |>.trans hj.symm
    simpa [hp, hj, hpi_iff, hqj] using h.adj_iff p

end RootedInducedPath

namespace BubbleWand

variable {G : SimpleGraph V}

/-- A replacement inside the handle cannot equal the bubble vertex.  The
bubble is adjacent to the terminal path vertex, while the replacement law
makes the new vertex nonadjacent to it. -/
theorem replacement_ne_bubble
    (B : BubbleWand G) {k : V} {q : Fin B.path.card}
    (h : B.path.PathVertexReplacement k q)
    (hq : q.val ≤ B.split.val) :
    k ≠ B.bubble := by
  have hqlast : q ≠ B.lastIndex := by
    intro hEq
    have hval : q.val = B.lastIndex.val := congrArg Fin.val hEq
    change q.val = B.path.card - 1 at hval
    have hgap := B.gap
    omega
  have hq_last_nonadj : ¬G.Adj (B.path.vertex q)
      (B.path.vertex B.lastIndex) := by
    rw [B.path.adj_iff q B.lastIndex]
    change ¬(q.val + 1 = B.path.card - 1 ∨
      B.path.card - 1 + 1 = q.val)
    have hgap := B.gap
    omega
  have hk_last_nonadj : ¬G.Adj k (B.path.vertex B.lastIndex) := by
    rw [h.adj_iff B.lastIndex]
    exact not_or_intro hqlast.symm hq_last_nonadj
  intro hkb
  subst k
  exact hk_last_nonadj B.adj_last

/-- The claw-free case split used in the generalized-cycle paragraph of the
proof of Lemma 18.  After replacing a handle vertex, the bubble is adjacent
to the new vertex exactly when the replaced vertex was the handle endpoint.

At the endpoint, nonadjacency would create the manuscript claw on the next
two path vertices.  Strictly inside the handle, adjacency would create a claw
with the first and last vertices of the hoop. -/
theorem bubble_adj_replacement_iff_split
    (B : BubbleWand G) (hclaw : G.IsClawFree)
    {k : V} {q : Fin B.path.card}
    (h : B.path.PathVertexReplacement k q)
    (hq : q.val ≤ B.split.val) :
    G.Adj B.bubble k ↔ q = B.split := by
  have hkb : k ≠ B.bubble := B.replacement_ne_bubble h hq
  constructor
  · intro hbk
    apply Fin.ext
    by_contra hval
    have hq_lt : q.val < B.split.val := by omega
    have hqnext : q ≠ B.nextIndex := by
      intro hEq
      have := congrArg Fin.val hEq
      dsimp [nextIndex] at this
      omega
    have hq_last : q ≠ B.lastIndex := by
      intro hEq
      have := congrArg Fin.val hEq
      change q.val = B.path.card - 1 at this
      have hgap := B.gap
      omega
    have hq_next_nonadj : ¬G.Adj (B.path.vertex q)
        (B.path.vertex B.nextIndex) := by
      rw [B.path.adj_iff q B.nextIndex]
      dsimp [nextIndex]
      omega
    have hq_last_nonadj : ¬G.Adj (B.path.vertex q)
        (B.path.vertex B.lastIndex) := by
      rw [B.path.adj_iff q B.lastIndex]
      change ¬(q.val + 1 = B.path.card - 1 ∨
        B.path.card - 1 + 1 = q.val)
      have hgap := B.gap
      omega
    have hk_next_nonadj : ¬G.Adj k (B.path.vertex B.nextIndex) := by
      rw [h.adj_iff B.nextIndex]
      exact not_or_intro hqnext.symm hq_next_nonadj
    have hk_last_nonadj : ¬G.Adj k (B.path.vertex B.lastIndex) := by
      rw [h.adj_iff B.lastIndex]
      exact not_or_intro hq_last.symm hq_last_nonadj
    have hnext_last_nonadj : ¬G.Adj (B.path.vertex B.nextIndex)
        (B.path.vertex B.lastIndex) := by
      rw [B.path.adj_iff B.nextIndex B.lastIndex]
      change ¬(B.split.val + 1 + 1 = B.path.card - 1 ∨
        B.path.card - 1 + 1 = B.split.val + 1)
      have hgap := B.gap
      omega
    have hk_next : k ≠ B.path.vertex B.nextIndex := by
      intro hEq
      exact h.outside ⟨B.nextIndex, hEq.symm⟩
    have hk_last : k ≠ B.path.vertex B.lastIndex := by
      intro hEq
      exact h.outside ⟨B.lastIndex, hEq.symm⟩
    have hnext_last : B.path.vertex B.nextIndex ≠
        B.path.vertex B.lastIndex := by
      intro hEq
      have hindex := B.path.injective hEq
      have hvalue := congrArg Fin.val hindex
      change B.split.val + 1 = B.path.card - 1 at hvalue
      have hgap := B.gap
      omega
    rcases hclaw hbk B.adj_next B.adj_last
        hk_next hk_last hnext_last with hknext | hklast | hnextlast
    · exact hk_next_nonadj hknext
    · exact hk_last_nonadj hklast
    · exact hnext_last_nonadj hnextlast
  · intro hqsplit
    subst q
    by_contra hbk
    let afterNext : Fin B.path.card :=
      ⟨B.split.val + 2, by have hgap := B.gap; omega⟩
    have hnext_after : G.Adj (B.path.vertex B.nextIndex)
        (B.path.vertex afterNext) := by
      rw [B.path.adj_iff B.nextIndex afterNext]
      exact Or.inl rfl
    have hk_next : G.Adj k (B.path.vertex B.nextIndex) := by
      rw [h.adj_iff B.nextIndex]
      right
      exact (B.path.adj_iff B.split B.nextIndex).2 (Or.inl rfl)
    have hb_after_nonadj : ¬G.Adj B.bubble (B.path.vertex afterNext) := by
      rw [B.adj_iff afterNext]
      change ¬(B.split.val + 2 = B.split.val ∨
        B.split.val + 2 = B.split.val + 1 ∨
        B.split.val + 2 + 1 = B.path.card)
      have hgap := B.gap
      omega
    have hsplit_after_nonadj : ¬G.Adj (B.path.vertex B.split)
        (B.path.vertex afterNext) := by
      rw [B.path.adj_iff B.split afterNext]
      dsimp [afterNext]
      omega
    have hk_after_nonadj : ¬G.Adj k (B.path.vertex afterNext) := by
      rw [h.adj_iff afterNext]
      exact not_or_intro (by
        intro hEq
        have := congrArg Fin.val hEq
        dsimp [afterNext] at this
        omega) hsplit_after_nonadj
    have hb_after : B.bubble ≠ B.path.vertex afterNext := by
      intro hEq
      exact B.outside ⟨afterNext, hEq.symm⟩
    have hk_after : k ≠ B.path.vertex afterNext := by
      intro hEq
      exact h.outside ⟨afterNext, hEq.symm⟩
    rcases hclaw B.adj_next.symm hk_next.symm hnext_after
        hkb.symm hb_after hk_after with hbK | hbAfter | hkAfter
    · exact hbk hbK
    · exact hb_after_nonadj hbAfter
    · exact hk_after_nonadj hkAfter

/-- Replacing a vertex in the handle deletes its old value from the handle
carrier and inserts the replacement value. -/
theorem mem_handle_replace_iff
    (B : BubbleWand G) {k : V} {q : Fin B.path.card}
    (h : B.path.PathVertexReplacement k q)
    (hq : q.val ≤ B.split.val) (v : V) :
    (∃ t : Fin B.path.card,
        t.val ≤ B.split.val ∧ (B.path.replace h).vertex t = v) ↔
      v = k ∨ (v ∈ B.handle ∧ v ≠ B.path.vertex q) := by
  constructor
  · rintro ⟨t, ht, htvertex⟩
    by_cases htq : t = q
    · subst t
      exact Or.inl ((B.path.replace_vertex_at h).symm.trans htvertex).symm
    · right
      have hvertex : B.path.vertex t = v :=
        (B.path.replace_vertex_away h htq).symm.trans htvertex
      refine ⟨⟨t, ht, hvertex⟩, ?_⟩
      intro hvq
      exact htq (B.path.injective (hvertex.trans hvq))
  · rintro (rfl | ⟨⟨t, ht, htvertex⟩, hvq⟩)
    · exact ⟨q, hq, B.path.replace_vertex_at h⟩
    · have htq : t ≠ q := by
        intro hEq
        subst t
        exact hvq htvertex.symm
      exact ⟨t, ht, (B.path.replace_vertex_away h htq).trans htvertex⟩

/-- Replacing a handle vertex leaves the hoop carrier unchanged. -/
theorem hoop_replace_eq
    (B : BubbleWand G) {k : V} {q : Fin B.path.card}
    (h : B.path.PathVertexReplacement k q)
    (hq : q.val ≤ B.split.val) :
    ((Set.range (B.path.replace h).vertex ∪ {B.bubble}) \
      {v | ∃ t : Fin B.path.card,
        t.val ≤ B.split.val ∧ (B.path.replace h).vertex t = v}) =
      B.hoop := by
  have hkBubble : k ≠ B.bubble := B.replacement_ne_bubble h hq
  have hqHandle : B.path.vertex q ∈ B.handle := ⟨q, hq, rfl⟩
  ext v
  constructor
  · rintro ⟨hvCarrier, hvHandle⟩
    have hvHandle' : ¬(v = k ∨
        (v ∈ B.handle ∧ v ≠ B.path.vertex q)) := by
      intro hv
      exact hvHandle ((B.mem_handle_replace_iff h hq v).2 hv)
    refine ⟨?_, ?_⟩
    · rcases hvCarrier with hvRange | rfl
      · rcases (B.path.mem_range_replace_iff h v).1 hvRange with
          rfl | ⟨hvOld, _⟩
        · exact (hvHandle' (Or.inl rfl)).elim
        · exact Or.inl hvOld
      · exact Or.inr rfl
    · intro hvOldHandle
      by_cases hvq : v = B.path.vertex q
      · subst v
        rcases hvCarrier with hvRange | hbq
        · rcases (B.path.mem_range_replace_iff h (B.path.vertex q)).1 hvRange with
            hqk | ⟨_, hne⟩
          · subst k
            exact h.outside ⟨q, rfl⟩
          · exact hne rfl
        · exact B.outside ⟨q, hbq⟩
      · exact hvHandle' (Or.inr ⟨hvOldHandle, hvq⟩)
  · rintro ⟨hvCarrier, hvHandle⟩
    refine ⟨?_, ?_⟩
    · rcases hvCarrier with hvRange | rfl
      · have hvq : v ≠ B.path.vertex q := by
          intro hEq
          subst v
          exact hvHandle hqHandle
        exact Or.inl ((B.path.mem_range_replace_iff h v).2
          (Or.inr ⟨hvRange, hvq⟩))
      · exact Or.inr rfl
    · intro hvNewHandle
      rcases (B.mem_handle_replace_iff h hq v).1 hvNewHandle with
        hvk | ⟨hvOldHandle, _⟩
      · subst v
        rcases hvCarrier with hkRange | hkb
        · exact h.outside hkRange
        · exact hkBubble hkb
      · exact hvHandle hvOldHandle

end BubbleWand

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The generalized-cycle arc comparison in the proof of manuscript Lemma
18.  An even-hoop bubble-wand arc between two prefixes at or after the
deformation index transports to the corresponding deformed prefixes. -/
theorem evenHoopBubbleWandArc_deformedPrefix
    (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val)
    (harc : EvenHoopBubbleWandArc G K
      (P.initialSegment r) (P.initialSegment s)) :
    EvenHoopBubbleWandArc G K
      (P.deformedPrefix h r) (P.deformedPrefix h s) := by
  rcases harc with ⟨B, hsource, htarget, n, C, hhoop⟩
  rcases P.exists_pathVertexReplacement_of_originalCarrier_eq
      h r hir B.path hsource hj with ⟨q, hqj, hreplace⟩
  have hjTarget : j ∈ (P.initialSegment s).originalCarrier :=
    (P.mem_originalCarrier_initialSegment_iff s j).2 ⟨i, his, hj⟩
  rw [htarget] at hjTarget
  rcases hjTarget with ⟨q', hq'split, hq'j⟩
  have hq'q : q' = q := by
    apply B.path.injective
    exact hq'j.trans hqj.symm
  subst q'
  let B' : BubbleWand G :=
    { path := B.path.replace hreplace
      bubble := B.bubble
      split := ⟨B.split.val, by simpa using B.split.isLt⟩
      gap := by simpa using B.gap
      outside := by
        intro hb
        rcases (B.path.mem_range_replace_iff hreplace B.bubble).1 hb with
          hbk | ⟨hbRange, _⟩
        · exact B.replacement_ne_bubble hreplace hq'split hbk.symm
        · exact B.outside hbRange
      adj_iff := by
        intro t
        by_cases htq : t = q
        · subst t
          rw [B.path.replace_vertex_at hreplace]
          rw [B.bubble_adj_replacement_iff_split hclaw hreplace hq'split]
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
  refine ⟨B', ?_, ?_, n, C, ?_⟩
  · ext v
    rw [P.mem_originalCarrier_deformedPrefix_iff_replace h r hir hj v]
    rw [B.path.mem_range_replace_iff hreplace v]
    rw [← hsource]
    simp [hqj]
  · ext v
    rw [P.mem_originalCarrier_deformedPrefix_iff_replace h s his hj v]
    change v = k ∨
        (v ∈ (P.initialSegment s).originalCarrier ∧ v ≠ j) ↔
      ∃ t : Fin B.path.card,
        t.val ≤ B.split.val ∧ (B.path.replace hreplace).vertex t = v
    rw [B.mem_handle_replace_iff hreplace hq'split v]
    rw [htarget, hqj]
  · rw [hhoop]
    exact (B.hoop_replace_eq hreplace hq'split).symm

/-- The generalized-cycle comparison is bidirectional.  The reverse
implication is the same claw-free transport applied to the reversible
Definition 10 generator. -/
theorem evenHoopBubbleWandArc_deformedPrefix_iff
    (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val) :
    EvenHoopBubbleWandArc G K
        (P.initialSegment r) (P.initialSegment s) ↔
      EvenHoopBubbleWandArc G K
        (P.deformedPrefix h r) (P.deformedPrefix h s) := by
  constructor
  · exact P.evenHoopBubbleWandArc_deformedPrefix
      hclaw h hj r s hir his
  · intro harc
    let hreverse : (P.path.deform h).SingleVertexDeformation (some j) i := by
      simpa [hj] using h.reverse
    have hpath : (P.path.deform h).deform hreverse = P.path := by
      simpa [hreverse, hj] using h.deform_reverse_eq P.path
    have htransport := (P.deform h).evenHoopBubbleWandArc_deformedPrefix
      hclaw hreverse (P.path.deform_vertex_at h) r s hir his harc
    change EvenHoopBubbleWandArc G K
      (((P.deform h).deform hreverse).initialSegment r)
      (((P.deform h).deform hreverse).initialSegment s) at htransport
    have hr : ((P.deform h).deform hreverse).initialSegment r =
        P.initialSegment r := by
      apply ext_path
      change ((P.path.deform h).deform hreverse).initialSegment r =
        P.path.initialSegment r
      have hrPath := IndexedInducedPath.initialSegment_congr hpath r
      simpa using hrPath
    have hs : ((P.deform h).deform hreverse).initialSegment s =
        P.initialSegment s := by
      apply ext_path
      change ((P.path.deform h).deform hreverse).initialSegment s =
        P.path.initialSegment s
      have hsPath := IndexedInducedPath.initialSegment_congr hpath s
      simpa using hsPath
    rwa [hr, hs] at htransport

end RootedInducedPath

end SimpleGraph
