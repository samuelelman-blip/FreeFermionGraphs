import FreeFermionGraphs.KrylovTreeMatrix
import FreeFermionGraphs.BubbleWandArcEvent
import FreeFermionGraphs.PauliCliqueHamiltonianResolvedSupport

/-!
# Bubble wands on clique-rooted paths, root handle included

Definition 11 (bubble wand, handle, hoop; arXiv 2305.15625v1,
L692-698) and Definition 18 (directed hopping graph; L854-858), together with
the use `0 ≤ s < ℓ - 2` in case (b.iv) of the proof of Theorem 3 (L1520).

Let `P = (j₀ = j*, j₁, ..., j_ℓ)` be a rooted induced path of `G*`, and let
`j ∉ P` have `Γ_P(j) = {j_s, j_{s+1}, j_ℓ}` with `0 ≤ s < ℓ - 2`.  Then

* the handle is the prefix `P_s`, and `P_0 = {j*}` is allowed;
* the hoop `C = {j_{s+1}, ..., j_ℓ, j}` is an induced hole of `G` with
  `ℓ - s + 1 ≥ 4` vertices;
* the bubble `j` determines `s` (`CliqueBubbleWand.ext_of_bubble_eq`);
* `Λ` has an extra arc `P → Q` iff some such `j` has handle `Q` and an even
  hoop (`EvenHoopArc`).

v1 needs no separate clause for `s = 0`: its labeling starts at `j₀ = j*`
(L303, L692), so `i = 0` is allowed in Definition 11 and the proof of Theorem 3
uses `0 ≤ s` (L1520).  The repo's `EvenHoopBubbleWandArc` instantiates the
graph-generic `BubbleWand` on the original carrier with the root deleted, so a
root handle (`s = 0`, i.e. `P_0 = {j*}`) never produces an arc there; that
omission is a defect of the repo relation, not of v1.  This file instantiates
the literal v1 definition at `G*` instead and leaves the old relation
unchanged.  `evenHoopBubbleWandArc_iff_evenHoopArc` compares the two: for a
clique `K` with `G*` claw-free they differ exactly by the arcs into the root
path (a premise on claw-freeness is genuinely required there, see
`EvenHoopBubbleWandArc.evenHoopArc`).

Main declarations.

* `CliqueBubbleWand` with `handle`, `hoopCard`, `hoopCarrier`,
  `exists_hoopHole`, `ext_of_bubble_eq`, `handle_eq_cliqueRootPath_iff`;
* the exclusion of the other one-step cases for a wand bubble
  (`anticommutesWith`, `terminalVertex_ne`, `not_terminalExtensionData`,
  `not_singleVertexDeformation`);
* `EvenHoopArc` and `cliqueDirectedHoppingGraph` (Definition 18, root handle
  included);
* the classification bridge `RootedInducedPath.exists_cliqueBubbleWand_iff` and
  `PauliCliqueHamiltonianRepresentation.exists_cliqueBubbleWand_of_resolved`:
  an anticommuting vertex that is not the terminal vertex, a terminal extension
  or a clone is a wand bubble (the root-hoop and bubble-wand branches of
  `ResolvedOneTermParityCase`, now with the full neighbour pattern).

Paths in `G*` are `Option V`-valued (`none` plays `j*`).  A bubble `j` is an
original vertex `j : V`; its adjacency to a path vertex is read in `G*`
(`G.adjoinRootAt K`), so adjacency to the root is the membership `j ∈ K`.

Indices: a clique-rooted path with `ℓ + 1` vertices `j₀, ..., j_ℓ` has
`P.path.card = ℓ + 1`, and the split index `s` is `split.val`.  The condition
`s < ℓ - 2` is `split.val + 3 < P.path.card`.

The hoop has `ℓ - s + 1 = P.path.card - split.val` vertices.
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

/-- A bubble wand on a clique-rooted induced path `P` of `G* = G + j*`
(v1 Definition 11, L692-698, with `j₀ = j*`): an original vertex `bubble`
outside `P` whose neighbours on `P` are exactly
`Γ_P(j) = {j_s, j_{s+1}, j_ℓ}` with `0 ≤ s < ℓ - 2`.  The split index
`s = split.val` is allowed to be `0`, in which case the handle is the root path
`{j*}`.  Adjacency is read in `G*`. -/
structure CliqueBubbleWand (G : SimpleGraph V) (K : Set V)
    (P : CliqueRootedInducedPath G K) where
  /-- The bubble vertex `j`. -/
  bubble : V
  /-- The split index `s`: `j` is adjacent to `j_s` and `j_{s+1}`. -/
  split : Fin P.path.card
  /-- `s < ℓ - 2`, i.e. `s + 3 < ℓ + 1`. -/
  gap : split.val + 3 < P.path.card
  /-- `j` is not on the path. -/
  outside : some bubble ∉ Set.range P.path.vertex
  /-- `Γ_P(j) = {j_s, j_{s+1}, j_ℓ}` in `G*`. -/
  adj_iff : ∀ q : Fin P.path.card,
    (G.adjoinRootAt K).Adj (some bubble) (P.path.vertex q) ↔
      q.val = split.val ∨ q.val = split.val + 1 ∨ q.val + 1 = P.path.card

namespace CliqueBubbleWand

variable {G : SimpleGraph V} {K : Set V} {P : CliqueRootedInducedPath G K}

/-- The handle `P_s = (j₀, ..., j_s)` of the wand, a clique-rooted path
(v1 L692-698).  For `s = 0` this is the root path `{j*}`. -/
def handle (w : CliqueBubbleWand G K P) : CliqueRootedInducedPath G K :=
  P.initialSegment w.split

/-- The number `ℓ - s + 1` of vertices of the hoop `C`. -/
def hoopCard (w : CliqueBubbleWand G K P) : ℕ :=
  P.path.card - w.split.val

/-- The carrier of the hoop `C = {j_{s+1}, ..., j_ℓ, j}` (the original
vertices of `P` outside the handle, together with the bubble). -/
def hoopCarrier (w : CliqueBubbleWand G K P) : Set V :=
  bubbleWandArcHoopCarrier P w.handle w.bubble

theorem four_le_card (w : CliqueBubbleWand G K P) : 4 ≤ P.path.card := by
  have := w.gap
  omega

theorem two_le_card (w : CliqueBubbleWand G K P) : 2 ≤ P.path.card := by
  have := w.gap
  omega

@[simp]
theorem handle_card (w : CliqueBubbleWand G K P) :
    w.handle.path.card = w.split.val + 1 :=
  rfl

@[simp]
theorem handle_vertex (w : CliqueBubbleWand G K P)
    (q : Fin (w.split.val + 1)) :
    w.handle.path.vertex q = P.path.vertex ⟨q.val, by omega⟩ :=
  rfl

/-- The hoop has at least four vertices. -/
theorem four_le_hoopCard (w : CliqueBubbleWand G K P) : 4 ≤ w.hoopCard := by
  have := w.gap
  unfold hoopCard
  omega

/-- The handle leaves room for the hoop: `|P_s| + 3 ≤ |P|`. -/
theorem handle_card_add_three_le (w : CliqueBubbleWand G K P) :
    w.handle.path.card + 3 ≤ P.path.card := by
  have := w.gap
  simp only [handle_card]
  omega

/-- The bubble is adjacent (in `G*`) to the last handle vertex `j_s`. -/
theorem adj_split (w : CliqueBubbleWand G K P) :
    (G.adjoinRootAt K).Adj (some w.bubble) (P.path.vertex w.split) :=
  (w.adj_iff w.split).2 (Or.inl rfl)

/-- The bubble is adjacent to the first hoop vertex `j_{s+1}`. -/
theorem adj_next (w : CliqueBubbleWand G K P) :
    (G.adjoinRootAt K).Adj (some w.bubble)
      (P.path.vertex ⟨w.split.val + 1, by have := w.gap; omega⟩) :=
  (w.adj_iff _).2 (Or.inr (Or.inl rfl))

/-- The bubble is adjacent to the terminal vertex `j_ℓ`. -/
theorem adj_terminal (w : CliqueBubbleWand G K P) :
    (G.adjoinRootAt K).Adj (some w.bubble) (P.path.vertex P.terminalIndex) := by
  apply (w.adj_iff _).2
  right
  right
  change P.path.card - 1 + 1 = P.path.card
  have := P.path.nonempty
  omega

/-! ### Uniqueness of the split index -/

/-- The bubble determines the wand (v1: "the bubble `j` determines `s`").
Equivalently, the split index is the smallest path index adjacent to the
bubble, so a given bubble vertex gives at most one wand on `P`. -/
theorem ext_of_bubble_eq (w w' : CliqueBubbleWand G K P)
    (h : w.bubble = w'.bubble) : w = w' := by
  obtain ⟨b, s, gap, outside, adj⟩ := w
  obtain ⟨b', s', gap', outside', adj'⟩ := w'
  change b = b' at h
  subst h
  have hs : s = s' := by
    have h1 := (adj s).2 (Or.inl rfl)
    have h2 := (adj' s).1 h1
    have h3 := (adj s').1 ((adj' s').2 (Or.inl rfl))
    have h4 := (adj' ⟨s.val + 1, by omega⟩).1
      ((adj ⟨s.val + 1, by omega⟩).2 (Or.inr (Or.inl rfl)))
    have h5 := (adj ⟨s'.val + 1, by omega⟩).1
      ((adj' ⟨s'.val + 1, by omega⟩).2 (Or.inr (Or.inl rfl)))
    apply Fin.ext
    simp only at h2 h3 h4 h5 gap gap'
    omega
  subst hs
  rfl

/-- The split index is determined by the bubble. -/
theorem split_eq_of_bubble_eq (w w' : CliqueBubbleWand G K P)
    (h : w.bubble = w'.bubble) : w.split = w'.split :=
  congrArg CliqueBubbleWand.split (ext_of_bubble_eq w w' h)

/-! ### The handle -/

/-- The handle of a wand is the root path `{j*}` exactly when `s = 0`
(v1 allows `i = 0`; L692-698 and L1520). -/
theorem handle_eq_cliqueRootPath_iff (w : CliqueBubbleWand G K P) :
    w.handle = cliqueRootPath G K ↔ w.split.val = 0 := by
  rw [RootedInducedPath.eq_cliqueRootPath_iff]
  simp only [handle_card]
  omega

/-- The original carrier of the handle is `{j₁, ..., j_s}`. -/
theorem mem_handle_originalCarrier_iff (w : CliqueBubbleWand G K P) (v : V) :
    v ∈ w.handle.originalCarrier ↔
      ∃ q : Fin P.path.card, q.val ≤ w.split.val ∧
        P.path.vertex q = some v :=
  P.mem_originalCarrier_initialSegment_iff w.split v

/-! ### The hoop is an induced hole -/

/-- The path index `q + s + 1` of the `q`-th hoop vertex `j_{s+1+q}`. -/
def hoopIndex (w : CliqueBubbleWand G K P)
    (q : Fin (P.path.card - (w.split.val + 1))) : Fin P.path.card :=
  ⟨q.val + w.split.val + 1, by
    have := q.isLt
    omega⟩

/-- The original vertex at the `q`-th hoop position (every vertex of positive
index of a clique-rooted path is an original vertex). -/
noncomputable def hoopVertex (w : CliqueBubbleWand G K P)
    (q : Fin (P.path.card - (w.split.val + 1))) : V :=
  P.originalTailVertex w.two_le_card
    ⟨q.val + w.split.val, by
      have := q.isLt
      have := w.gap
      omega⟩

theorem path_vertex_hoopIndex (w : CliqueBubbleWand G K P)
    (q : Fin (P.path.card - (w.split.val + 1))) :
    P.path.vertex (w.hoopIndex q) = some (w.hoopVertex q) :=
  P.path_vertex_originalTailIndex w.two_le_card
    ⟨q.val + w.split.val, by
      have := q.isLt
      have := w.gap
      omega⟩

/-- The path suffix `(j_{s+1}, ..., j_ℓ)` after the handle, as an indexed
induced path of the original graph `G`: it avoids the root because its
indices are positive. -/
noncomputable def hoopPath (w : CliqueBubbleWand G K P) :
    IndexedInducedPath G where
  card := P.path.card - (w.split.val + 1)
  nonempty := by
    have := w.gap
    omega
  vertex := w.hoopVertex
  injective := by
    intro p q hpq
    have hidx := P.path.injective
      ((w.path_vertex_hoopIndex p).trans
        ((congrArg some hpq).trans (w.path_vertex_hoopIndex q).symm))
    apply Fin.ext
    have hval := congrArg Fin.val hidx
    change p.val + w.split.val + 1 = q.val + w.split.val + 1 at hval
    omega
  adj_iff := by
    intro p q
    rw [← G.adjoinRootAt_adj_some_some K, ← w.path_vertex_hoopIndex p,
      ← w.path_vertex_hoopIndex q, P.path.adj_iff]
    change
      (p.val + w.split.val + 1 + 1 = q.val + w.split.val + 1 ∨
        q.val + w.split.val + 1 + 1 = p.val + w.split.val + 1) ↔
      p.val + 1 = q.val ∨ q.val + 1 = p.val
    omega

@[simp]
theorem hoopPath_card (w : CliqueBubbleWand G K P) :
    w.hoopPath.card = P.path.card - (w.split.val + 1) :=
  rfl

/-- The bubble is adjacent exactly to the two endpoints of the hoop suffix. -/
theorem hoopPath_endpointClosureData (w : CliqueBubbleWand G K P) :
    w.hoopPath.EndpointClosureData w.bubble := by
  refine
    { three_le := ?_
      outside := ?_
      adj_iff := ?_ }
  · change 3 ≤ P.path.card - (w.split.val + 1)
    have := w.gap
    omega
  · rintro ⟨q, hq⟩
    apply w.outside
    exact ⟨w.hoopIndex q, by rw [w.path_vertex_hoopIndex q]; exact congrArg some hq⟩
  · intro q
    change G.Adj w.bubble (w.hoopVertex q) ↔
      q.val = 0 ∨ q.val + 1 = P.path.card - (w.split.val + 1)
    rw [← G.adjoinRootAt_adj_some_some K, ← w.path_vertex_hoopIndex q, w.adj_iff]
    change
      (q.val + w.split.val + 1 = w.split.val ∨
        q.val + w.split.val + 1 = w.split.val + 1 ∨
        q.val + w.split.val + 1 + 1 = P.path.card) ↔
      q.val = 0 ∨ q.val + 1 = P.path.card - (w.split.val + 1)
    have hq := q.isLt
    change q.val < P.path.card - (w.split.val + 1) at hq
    omega

/-- The hoop `C`, closed up by the bubble: an indexed induced hole of `G`. -/
noncomputable def hoopHole (w : CliqueBubbleWand G K P) :
    IndexedInducedHole G :=
  w.hoopPath.closeToHole w.hoopPath_endpointClosureData

@[simp]
theorem hoopHole_card (w : CliqueBubbleWand G K P) :
    w.hoopHole.card = w.hoopCard := by
  change P.path.card - (w.split.val + 1) + 1 = P.path.card - w.split.val
  have := w.gap
  omega

/-- The vertices of the hoop path are the original vertices of `P` outside
the handle. -/
theorem range_hoopVertex (w : CliqueBubbleWand G K P) :
    Set.range w.hoopVertex =
      P.originalCarrier \ w.handle.originalCarrier := by
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨⟨w.hoopIndex q, w.path_vertex_hoopIndex q⟩, ?_⟩
    rintro hmem
    obtain ⟨r, hrs, hr⟩ := (w.mem_handle_originalCarrier_iff _).1 hmem
    have hidx := P.path.injective
      (hr.trans (w.path_vertex_hoopIndex q).symm)
    have hval := congrArg Fin.val hidx
    change r.val = q.val + w.split.val + 1 at hval
    omega
  · rintro ⟨⟨r, hr⟩, hnot⟩
    have hrpos : w.split.val < r.val := by
      by_contra hle
      exact hnot ((w.mem_handle_originalCarrier_iff v).2
        ⟨r, by omega, hr⟩)
    let q : Fin (P.path.card - (w.split.val + 1)) :=
      ⟨r.val - (w.split.val + 1), by
        have := r.isLt
        omega⟩
    refine ⟨q, ?_⟩
    have hidx : w.hoopIndex q = r := by
      apply Fin.ext
      change r.val - (w.split.val + 1) + w.split.val + 1 = r.val
      omega
    have h1 := w.path_vertex_hoopIndex q
    rw [hidx, hr] at h1
    exact (Option.some.inj h1).symm

/-- The hole obtained by closing the hoop path with the bubble has exactly the
carrier `{j_{s+1}, ..., j_ℓ, j}` of the hoop (v1 Definition 11). -/
theorem range_hoopHole (w : CliqueBubbleWand G K P) :
    Set.range w.hoopHole.vertex = w.hoopCarrier := by
  rw [hoopHole, IndexedInducedPath.range_closeToHole]
  change Set.range w.hoopVertex ∪ {w.bubble} =
    (P.originalCarrier \ w.handle.originalCarrier) ∪ {w.bubble}
  rw [range_hoopVertex]

/-- The hoop `C = {j_{s+1}, ..., j_ℓ, j}` is an induced hole of `G` with
`ℓ - s + 1 ≥ 4` vertices (v1 Definition 11: "the hoop defined as the hole
`C = B \ P_i`"; L692-698). -/
theorem exists_hoopHole (w : CliqueBubbleWand G K P) :
    ∃ C : G.IndexedInducedHole,
      Set.range C.vertex = w.hoopCarrier ∧ C.card = w.hoopCard :=
  ⟨w.hoopHole, w.range_hoopHole, w.hoopHole_card⟩

/-! ### The wand bubble is none of the other one-step cases -/

/-- The path indices adjacent to the bubble are exactly `s`, `s + 1` and
`ℓ`. -/
theorem neighborIndexSet_eq (w : CliqueBubbleWand G K P) :
    P.path.neighborIndexSet (some w.bubble) =
      {w.split, ⟨w.split.val + 1, by have := w.gap; omega⟩,
        P.terminalIndex} := by
  ext q
  rw [IndexedInducedPath.mem_neighborIndexSet, w.adj_iff q]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff,
    RootedInducedPath.terminalIndex]
  have := P.path.nonempty
  omega

/-- The bubble of a wand has exactly three neighbours on the path, so it
anticommutes with the path operator (`h_P h_j = - h_j h_P`). -/
theorem anticommutesWith (w : CliqueBubbleWand G K P) :
    P.path.AnticommutesWith (some w.bubble) := by
  have hgap := w.gap
  have hcard : (P.path.neighborIndexSet (some w.bubble)).ncard = 3 := by
    rw [w.neighborIndexSet_eq, Set.ncard_eq_three]
    refine ⟨w.split, ⟨w.split.val + 1, by omega⟩, P.terminalIndex, ?_, ?_, ?_, rfl⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · intro h
      have := congrArg Fin.val h
      simp only [RootedInducedPath.terminalIndex] at this
      omega
    · intro h
      have := congrArg Fin.val h
      simp only [RootedInducedPath.terminalIndex] at this
      omega
  apply (P.path.anticommutesWith_iff_neighborIndexSet_mod_eq_one _).2
  omega

/-- The bubble is not the terminal vertex of `P`. -/
theorem terminalVertex_ne (w : CliqueBubbleWand G K P) :
    P.terminalVertex ≠ some w.bubble := by
  intro h
  exact w.outside ⟨P.terminalIndex, h⟩

/-- The bubble is not a terminal extension of `P` (it has three neighbours on
`P`, not one). -/
theorem not_terminalExtensionData (w : CliqueBubbleWand G K P) :
    ¬ P.path.TerminalExtensionData (some w.bubble) := by
  intro h
  have h1 := (h.adj_iff w.split).1 w.adj_split
  have := w.gap
  omega

/-- The bubble is not a clone of any path vertex (a Definition 10 deformation
has three *consecutive* neighbours, a wand does not). -/
theorem not_singleVertexDeformation (w : CliqueBubbleWand G K P)
    (i : Fin P.path.card) :
    ¬ P.path.SingleVertexDeformation (some w.bubble) i := by
  intro h
  have hgap := w.gap
  have hit := h.internal_left
  have hir := h.internal_right
  have key : ∀ q : Fin P.path.card,
      (q.val = w.split.val ∨ q.val = w.split.val + 1 ∨
        q.val + 1 = P.path.card) ↔
      (q = i ∨ i.val + 1 = q.val ∨ q.val + 1 = i.val) := by
    intro q
    rw [← w.adj_iff q, h.adj_iff q, P.path.adj_iff i q]
  have k1 := key w.split
  have k2 := key ⟨w.split.val + 1, by omega⟩
  have k3 := key P.terminalIndex
  have k4 := key ⟨i.val - 1, by omega⟩
  have k5 := key i
  have k6 := key ⟨i.val + 1, by omega⟩
  simp only [RootedInducedPath.terminalIndex, Fin.ext_iff, true_or, or_true,
    true_iff, iff_true] at k1 k2 k3 k4 k5 k6
  omega

end CliqueBubbleWand

/-! ### Rigidity of induced paths -/

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- Two indexed induced paths with the same vertex set and the same first
vertex list their vertices in the same order. -/
theorem vertex_eq_of_range_eq_of_first_eq (X Y : IndexedInducedPath G)
    (hrange : Set.range X.vertex = Set.range Y.vertex)
    (h0 : X.vertex ⟨0, X.nonempty⟩ = Y.vertex ⟨0, Y.nonempty⟩) :
    ∀ (k : ℕ) (hx : k < X.card) (hy : k < Y.card),
      X.vertex ⟨k, hx⟩ = Y.vertex ⟨k, hy⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hx hy
    rcases k with _ | k
    · exact h0
    · have ihk := ih k (Nat.lt_succ_self k) (by omega) (by omega)
      have hadjX : G.Adj (X.vertex ⟨k + 1, hx⟩) (X.vertex ⟨k, by omega⟩) :=
        (X.adj_iff _ _).2 (Or.inr rfl)
      have hmem : X.vertex ⟨k + 1, hx⟩ ∈ Set.range Y.vertex := by
        rw [← hrange]
        exact ⟨_, rfl⟩
      obtain ⟨m, hm⟩ := hmem
      have hadjY : G.Adj (Y.vertex m) (Y.vertex ⟨k, by omega⟩) := by
        rw [hm, ← ihk]
        exact hadjX
      rcases (Y.adj_iff _ _).1 hadjY with h | h
      · exfalso
        change m.val + 1 = k at h
        have hXm := ih m.val (by omega) (by omega) m.isLt
        have hinj := X.injective (hXm.trans hm)
        have h2 : m.val = k + 1 := congrArg Fin.val hinj
        omega
      · change k + 1 = m.val at h
        have hmeq : m = ⟨k + 1, hy⟩ := Fin.ext h.symm
        rw [← hm, hmeq]

/-- Two indexed induced paths with the same vertex set and the same first
vertex have the same cardinality. -/
theorem card_le_of_range_eq_of_first_eq (X Y : IndexedInducedPath G)
    (hrange : Set.range X.vertex = Set.range Y.vertex)
    (h0 : X.vertex ⟨0, X.nonempty⟩ = Y.vertex ⟨0, Y.nonempty⟩) :
    X.card ≤ Y.card := by
  by_contra hlt
  have hlt : Y.card < X.card := by omega
  have hmem : X.vertex ⟨Y.card, hlt⟩ ∈ Set.range Y.vertex := by
    rw [← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := hmem
  have hXm := X.vertex_eq_of_range_eq_of_first_eq Y hrange h0 m.val
    (by have := m.isLt; omega) m.isLt
  have hinj := X.injective (hm.symm.trans hXm.symm)
  have h2 : Y.card = m.val := congrArg Fin.val hinj
  have := m.isLt
  omega

/-- Two indexed induced paths with the same vertex set and the same first
vertex are equal: the induced subgraph is a path graph, and its vertex order
from a fixed endpoint is unique. -/
theorem eq_of_range_eq_of_first_eq (X Y : IndexedInducedPath G)
    (hrange : Set.range X.vertex = Set.range Y.vertex)
    (h0 : X.vertex ⟨0, X.nonempty⟩ = Y.vertex ⟨0, Y.nonempty⟩) :
    X = Y := by
  have hcard : X.card = Y.card := le_antisymm
    (X.card_le_of_range_eq_of_first_eq Y hrange h0)
    (Y.card_le_of_range_eq_of_first_eq X hrange.symm h0.symm)
  apply ext_card_vertex hcard
  apply Function.hfunext (congrArg Fin hcard)
  intro a b hab
  have hval : a.val = b.val := (Fin.heq_ext_iff hcard).1 hab
  exact heq_of_eq (X.vertex_eq_of_range_eq_of_first_eq Y hrange h0 a.val a.isLt
    (by have := b.isLt; omega) |>.trans (congrArg Y.vertex (Fin.ext hval)))

end IndexedInducedPath

/-! ### The extra arcs of the directed hopping graph, root handle included -/

variable {G : SimpleGraph V} {K : Set V}

/-- The extra arcs of the directed hopping graph `Λ_K(G)` (v1 Definition 18,
L854-858): there is an arc `P → Q` iff some vertex `j ∉ P` makes `P ∪ {j}` a
bubble wand with handle `Q` (an *ordered* prefix of `P`, possibly the root
path `{j*}`) and an even hoop.

Unlike `EvenHoopBubbleWandArc`, which works on the original carrier with the
root deleted, this relation includes the root-handle arcs `P → {j*}`
(`s = 0`), which Theorem 3 needs (proof of case (b.iv), L1520). -/
def EvenHoopArc (G : SimpleGraph V) (K : Set V)
    (P Q : CliqueRootedInducedPath G K) : Prop :=
  ∃ w : CliqueBubbleWand G K P, w.handle = Q ∧ Even w.hoopCard

/-- The directed hopping graph `Λ_K(G)` of v1 Definition 18 (L854-858) on the
rooted induced paths of `G* = G + j*`: both orientations of every edge of the
induced-path tree `I(K, G)`, plus the even-hoop bubble-wand arcs `EvenHoopArc`
(root handle included). -/
def cliqueDirectedHoppingGraph (G : SimpleGraph V) (K : Set V)
    (hK : G.IsClique K) : ArcGraph (CliqueRootedInducedPath G K) :=
  directedHoppingGraph (G.inducedPathTreeAtClique K hK) (EvenHoopArc G K)

@[simp]
theorem cliqueDirectedHoppingGraph_arc_iff (G : SimpleGraph V) (K : Set V)
    (hK : G.IsClique K) (P Q : CliqueRootedInducedPath G K) :
    (cliqueDirectedHoppingGraph G K hK).Arc P Q ↔
      (G.inducedPathTreeAtClique K hK).Adj P Q ∨ EvenHoopArc G K P Q :=
  Iff.rfl

/-- Every tree edge supplies its forward hopping arc. -/
theorem cliqueDirectedHoppingGraph_arc_of_adj {hK : G.IsClique K}
    {P Q : CliqueRootedInducedPath G K}
    (h : (G.inducedPathTreeAtClique K hK).Adj P Q) :
    (cliqueDirectedHoppingGraph G K hK).Arc P Q :=
  Or.inl h

/-- Every even-hoop bubble wand supplies its extra arc. -/
theorem cliqueDirectedHoppingGraph_arc_of_evenHoopArc {hK : G.IsClique K}
    {P Q : CliqueRootedInducedPath G K} (h : EvenHoopArc G K P Q) :
    (cliqueDirectedHoppingGraph G K hK).Arc P Q :=
  Or.inr h

namespace EvenHoopArc

variable {P Q : CliqueRootedInducedPath G K}

/-- An extra arc `P → Q` shortens the path by at least three vertices:
`|Q| + 3 ≤ |P|`. -/
theorem card_add_three_le (h : EvenHoopArc G K P Q) :
    Q.path.card + 3 ≤ P.path.card := by
  obtain ⟨w, rfl, _⟩ := h
  exact w.handle_card_add_three_le

/-- The extra arcs are never edges of the induced-path tree (a one-vertex
extension changes the cardinality by exactly one). -/
theorem not_treeAdjacent (h : EvenHoopArc G K P Q) : ¬P.TreeAdjacent Q := by
  have hcard := h.card_add_three_le
  rintro (⟨hc, _⟩ | ⟨hc, _⟩) <;> omega

/-- The extra arcs are not edges of the induced-path tree `I(K, G)`. -/
theorem not_inducedPathTree_adj (hK : G.IsClique K) (h : EvenHoopArc G K P Q) :
    ¬(G.inducedPathTreeAtClique K hK).Adj P Q :=
  h.not_treeAdjacent

/-- An extra arc is never a loop. -/
theorem ne (h : EvenHoopArc G K P Q) : P ≠ Q := by
  rintro rfl
  have := h.card_add_three_le
  omega

/-- The wand of an extra arc contains, as its hoop, an induced hole of even
cardinality. -/
theorem exists_even_hole (h : EvenHoopArc G K P Q) :
    ∃ C : G.IndexedInducedHole, Even C.card := by
  obtain ⟨w, _, hev⟩ := h
  exact ⟨w.hoopHole, by rw [w.hoopHole_card]; exact hev⟩

/-- A bubble wand with an even hoop exhibits an alternating even-hole
labeling of its hoop carrier. -/
theorem exists_evenHoleLabeling (h : EvenHoopArc G K P Q) :
    ∃ (w : CliqueBubbleWand G K P) (k : Nat) (E : EvenHoleLabeling G k),
      w.handle = Q ∧ E.carrier = w.hoopCarrier := by
  obtain ⟨w, hQ, hev⟩ := h
  obtain ⟨k, E, hE⟩ := w.hoopHole.exists_evenHoleLabeling
    (by rw [w.hoopHole_card]; exact hev)
  exact ⟨w, k, E, hQ, hE.trans w.range_hoopHole⟩

end EvenHoopArc

/-- An extra arc into the root path `{j*}` is exactly a wand with split index
`s = 0` and an even hoop. -/
theorem evenHoopArc_cliqueRootPath_iff
    (P : CliqueRootedInducedPath G K) :
    EvenHoopArc G K P (cliqueRootPath G K) ↔
      ∃ w : CliqueBubbleWand G K P, w.split.val = 0 ∧ Even w.hoopCard := by
  constructor
  · rintro ⟨w, hw, hev⟩
    exact ⟨w, (w.handle_eq_cliqueRootPath_iff).1 hw, hev⟩
  · rintro ⟨w, hs, hev⟩
    exact ⟨w, (w.handle_eq_cliqueRootPath_iff).2 hs, hev⟩

/-! ### Classification bridge: an anticommuting vertex that is neither terminal,
a terminal extension nor a clone is a bubble wand -/

namespace RootedInducedPath

/-- Resolve an endpoint together with an *ordered* adjacent pair.  Suppose
the neighbours of `j` on `P` are exactly `endpoint`, `left` and `right`, where
`endpoint` is an endpoint index of `P` and `right = left + 1`.  Then either `j`
deforms `P` (a Definition 10 clone, excluded by `hnotDef`) or `j` is the
bubble of a `CliqueBubbleWand` on `P`.  When the endpoint is the terminal and
the pair is `(s, s + 1)` with `s + 3 < |P|`, the wand has split index `s`;
`s = 0` is the root hoop `Γ_P(j) = {j*, j₁, j_ℓ}`.  This mirrors
`resolve_ordered_endpoint_pair` but returns the wand data (including the
neighbour pattern at the root) instead of only its carrier. -/
theorem exists_cliqueBubbleWand_of_ordered_endpoint_pair
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {endpoint left right : Fin P.path.card}
    (hel : endpoint ≠ left) (her : endpoint ≠ right)
    (hlr : left ≠ right)
    (hjEndpoint : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex endpoint))
    (hjLeft : (G.adjoinRootAt K).Adj (some j) (P.path.vertex left))
    (hjRight : (G.adjoinRootAt K).Adj (some j) (P.path.vertex right))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = endpoint ∨ q = left ∨ q = right)
    (hendpoint : P.path.IsEndpointIndex endpoint)
    (horder : left.val + 1 = right.val)
    (hnotDef : ∀ i, ¬ P.path.SingleVertexDeformation (some j) i) :
    ∃ w : CliqueBubbleWand G K P, w.bubble = j := by
  have helVal : endpoint.val ≠ left.val := fun h => hel (Fin.ext h)
  have herVal : endpoint.val ≠ right.val := fun h => her (Fin.ext h)
  have hlrVal : left.val ≠ right.val := fun h => hlr (Fin.ext h)
  have hcardThree : 3 ≤ P.path.card := by omega
  -- the exact neighbourhood rewritten as a statement about indices
  have hnbr : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) ↔
        (q = endpoint ∨ q = left ∨ q = right) := by
    intro q
    refine ⟨hexact q, ?_⟩
    rintro (rfl | rfl | rfl)
    · exact hjEndpoint
    · exact hjLeft
    · exact hjRight
  rcases hendpoint with hroot | hterminal
  · -- endpoint is the root: `j ∈ K`, so `j` is also adjacent to `j₁ ∈ K`
    exfalso
    have hrootEq : endpoint = ⟨0, P.path.nonempty⟩ := Fin.ext hroot
    have hjRoot : (G.adjoinRootAt K).Adj (some j) none := by
      rw [← P.root_eq, ← hrootEq]
      exact hjEndpoint
    have hjK : j ∈ K := by simpa using hjRoot
    let first := P.firstOriginalIndex (by omega)
    obtain ⟨v, hv⟩ := P.vertex_eq_some_of_pos first (by
      simp [first, firstOriginalIndex])
    have hrootFirst : (G.adjoinRootAt K).Adj none (P.path.vertex first) := by
      have hadj : (G.adjoinRootAt K).Adj
          (P.path.vertex ⟨0, P.path.nonempty⟩) (P.path.vertex first) := by
        apply (P.path.adj_iff ⟨0, P.path.nonempty⟩ first).2
        left
        simp [first, firstOriginalIndex]
      rw [P.root_eq] at hadj
      exact hadj
    have hvK : v ∈ K := by
      rw [hv] at hrootFirst
      simpa using hrootFirst
    have hjv : j ≠ v := by
      intro hjv
      apply hjOutside
      exact ⟨first, hv.trans (congrArg some hjv.symm)⟩
    have hjFirst : (G.adjoinRootAt K).Adj (some j) (P.path.vertex first) := by
      rw [hv]
      exact hK hjK hvK hjv
    have hfirstLeft : first = left := by
      rcases hexact first hjFirst with hfe | hfl | hfr
      · have hval := congrArg Fin.val hfe
        dsimp [first, firstOriginalIndex] at hval
        omega
      · exact hfl
      · have hval := congrArg Fin.val hfr
        dsimp [first, firstOriginalIndex] at hval
        omega
    have hleftVal : left.val = 1 := by
      have hval := congrArg Fin.val hfirstLeft
      simpa [first, firstOriginalIndex] using hval.symm
    exact hnotDef left
      (P.path.singleVertexDeformation_of_inducedPathTriple
        (left := endpoint) (center := left) (right := right) hjOutside
        hel her hlr hjEndpoint hjLeft hjRight hexact
        (P.path.consecutiveTriple (by omega) (by omega)))
  · -- endpoint is the terminal
    by_cases hleftRoot : left.val = 0
    · by_cases hshort : P.path.card = 3
      · exact (hnotDef right
          (P.path.singleVertexDeformation_of_inducedPathTriple
            (left := left) (center := right) (right := endpoint) hjOutside
            hlr hel.symm her.symm hjLeft hjRight hjEndpoint
            (by
              intro q hq
              rcases hexact q hq with hqe | hql | hqr
              · exact Or.inr (Or.inr hqe)
              · exact Or.inl hql
              · exact Or.inr (Or.inl hqr))
            (P.path.consecutiveTriple (by omega) (by omega)))).elim
      · refine ⟨
          { bubble := j
            split := left
            gap := by omega
            outside := hjOutside
            adj_iff := ?_ }, rfl⟩
        intro q
        rw [hnbr q]
        constructor
        · rintro (hq | hq | hq) <;> (have := congrArg Fin.val hq; omega)
        · intro hq
          rcases hq with hq | hq | hq
          · exact Or.inr (Or.inl (Fin.ext (by omega)))
          · exact Or.inr (Or.inr (Fin.ext (by omega)))
          · exact Or.inl (Fin.ext (by omega))
    · by_cases hgap : left.val + 3 < P.path.card
      · refine ⟨
          { bubble := j
            split := left
            gap := hgap
            outside := hjOutside
            adj_iff := ?_ }, rfl⟩
        intro q
        rw [hnbr q]
        constructor
        · rintro (hq | hq | hq) <;> (have := congrArg Fin.val hq; omega)
        · intro hq
          rcases hq with hq | hq | hq
          · exact Or.inr (Or.inl (Fin.ext (by omega)))
          · exact Or.inr (Or.inr (Fin.ext (by omega)))
          · exact Or.inl (Fin.ext (by omega))
      · exact (hnotDef right
          (P.path.singleVertexDeformation_of_inducedPathTriple
            (left := left) (center := right) (right := endpoint) hjOutside
            hlr hel.symm her.symm hjLeft hjRight hjEndpoint
            (by
              intro q hq
              rcases hexact q hq with hqe | hql | hqr
              · exact Or.inr (Or.inr hqe)
              · exact Or.inl hql
              · exact Or.inr (Or.inl hqr))
            (P.path.consecutiveTriple (by omega) (by omega)))).elim

/-- Resolve an endpoint together with an unordered adjacent pair. -/
theorem exists_cliqueBubbleWand_of_endpoint_pair
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {endpoint a b : Fin P.path.card}
    (hea : endpoint ≠ a) (heb : endpoint ≠ b) (hab : a ≠ b)
    (hjEndpoint : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex endpoint))
    (hjA : (G.adjoinRootAt K).Adj (some j) (P.path.vertex a))
    (hjB : (G.adjoinRootAt K).Adj (some j) (P.path.vertex b))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = endpoint ∨ q = a ∨ q = b)
    (hendpoint : P.path.IsEndpointIndex endpoint)
    (habAdj : (G.adjoinRootAt K).Adj (P.path.vertex a) (P.path.vertex b))
    (hnotDef : ∀ i, ¬ P.path.SingleVertexDeformation (some j) i) :
    ∃ w : CliqueBubbleWand G K P, w.bubble = j := by
  rcases (P.path.adj_iff a b).1 habAdj with habOrder | hbaOrder
  · exact P.exists_cliqueBubbleWand_of_ordered_endpoint_pair hK hjOutside
      hea heb hab hjEndpoint hjA hjB hexact hendpoint habOrder hnotDef
  · exact P.exists_cliqueBubbleWand_of_ordered_endpoint_pair hK hjOutside
      heb hea hab.symm hjEndpoint hjB hjA
      (by
        intro q hq
        rcases hexact q hq with hqe | hqa | hqb
        · exact Or.inl hqe
        · exact Or.inr (Or.inr hqa)
        · exact Or.inr (Or.inl hqb))
      hendpoint hbaOrder hnotDef

/-- The external odd-support geometry of `j` relative to `P`, with neither a
terminal extension nor a Definition 10 deformation, is a bubble wand with
split index `s ≥ 0`. -/
theorem exists_cliqueBubbleWand_of_externalKrylovGeometryCase
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    (h : P.path.ExternalKrylovGeometryCase (some j))
    (hnotExt : ¬ P.path.TerminalExtensionData (some j))
    (hnotDef : ∀ i, ¬ P.path.SingleVertexDeformation (some j) i) :
    ∃ w : CliqueBubbleWand G K P, w.bubble = j := by
  rcases h with
    ⟨q, hq, hqEndpoint, hexact⟩ |
    ⟨i, hdeform⟩ |
    ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hexact, hshape⟩
  · exact (hnotExt (P.terminalExtensionData_of_uniqueOriginalEndpoint hK
      hjOutside hq hqEndpoint hexact)).elim
  · exact (hnotDef i hdeform).elim
  · rcases hshape with
      ⟨hpEndpoint, hqrAdj⟩ |
      ⟨hqEndpoint, hprAdj⟩ |
      ⟨hrEndpoint, hpqAdj⟩
    · exact P.exists_cliqueBubbleWand_of_endpoint_pair hK hjOutside
        hpq hpr hqr hp hq hr hexact hpEndpoint hqrAdj hnotDef
    · exact P.exists_cliqueBubbleWand_of_endpoint_pair hK hjOutside
        hpq.symm hqr hpr hq hp hr
        (by
          intro k hk
          rcases hexact k hk with hkp | hkq | hkr
          · exact Or.inr (Or.inl hkp)
          · exact Or.inl hkq
          · exact Or.inr (Or.inr hkr))
        hqEndpoint hprAdj hnotDef
    · exact P.exists_cliqueBubbleWand_of_endpoint_pair hK hjOutside
        hpr.symm hqr.symm hpq hr hp hq
        (by
          intro k hk
          rcases hexact k hk with hkp | hkq | hkr
          · exact Or.inr (Or.inl hkp)
          · exact Or.inr (Or.inr hkq)
          · exact Or.inl hkr)
        hrEndpoint hpqAdj hnotDef

/-- Classification of one anticommuting vertex of a clique-rooted path in a
simplicial-clique-rooted claw-free graph: the vertex `j` is the terminal vertex
of `P`, a terminal extension, a Definition 10 deformation (clone), or the bubble
of a `CliqueBubbleWand` (the root handle `s = 0` allowed).  Hence a vertex that
is none of the first three is a wand bubble. -/
theorem exists_cliqueBubbleWand_of_anticommutesWith
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {j : V} (hanti : P.path.AnticommutesWith (some j))
    (hnotTerm : P.terminalVertex ≠ some j)
    (hnotExt : ¬ P.path.TerminalExtensionData (some j))
    (hnotDef : ∀ i, ¬ P.path.SingleVertexDeformation (some j) i) :
    ∃ w : CliqueBubbleWand G K P, w.bubble = j := by
  rcases P.originalAnticommutingCase hK hclaw hanti with hterm | ⟨hout, hodd⟩
  · exact (hnotTerm hterm).elim
  · exact P.exists_cliqueBubbleWand_of_externalKrylovGeometryCase hK.isClique
      hout (hodd.toKrylovGeometry P.path hout) hnotExt hnotDef

/-- For a simplicial clique and claw-free `G`, a vertex `j` is the bubble of a
wand on `P` exactly when it anticommutes with `P` and is neither the terminal
vertex of `P`, nor a terminal extension, nor a Definition 10 clone of a path
vertex.  This is the disjoint-partition form used to split the one-step
commutator into tree, deformation and wand terms. -/
theorem exists_cliqueBubbleWand_iff
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (j : V) :
    (∃ w : CliqueBubbleWand G K P, w.bubble = j) ↔
      P.path.AnticommutesWith (some j) ∧ P.terminalVertex ≠ some j ∧
        ¬ P.path.TerminalExtensionData (some j) ∧
        ∀ i, ¬ P.path.SingleVertexDeformation (some j) i := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.anticommutesWith, w.terminalVertex_ne, w.not_terminalExtensionData,
      w.not_singleVertexDeformation⟩
  · rintro ⟨hanti, hnotTerm, hnotExt, hnotDef⟩
    exact P.exists_cliqueBubbleWand_of_anticommutesWith hK hclaw hanti
      hnotTerm hnotExt hnotDef

end RootedInducedPath

namespace PauliCliqueHamiltonianRepresentation

variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Classification bridge for the one-step Hamiltonian action: an original
vertex `j` anticommuting with the path operator of `P`, which is neither the
terminal vertex, nor a terminal extension, nor a Definition 10 deformation
(the contraction, extension and deformation branches of
`ResolvedOneTermParityCase`), is the bubble of a `CliqueBubbleWand` on `P`.
The root-hoop branches of `ResolvedOneTermParityCase` are the wands with
`s = 0` and the bubble-wand branches those with `s ≥ 1`; the wand is read off
the exact neighbour pattern of `j`, not from the carriers.

The representation `H` records the setting only; the statement is
representation-independent (`RootedInducedPath.exists_cliqueBubbleWand_of_anticommutesWith`). -/
theorem exists_cliqueBubbleWand_of_resolved
    (_H : G.PauliCliqueHamiltonianRepresentation K R A)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {j : V}
    (hanti : P.path.AnticommutesWith (some j))
    (hnotTerm : P.terminalVertex ≠ some j)
    (hnotExt : ¬ P.path.TerminalExtensionData (some j))
    (hnotDef : ∀ i, ¬ P.path.SingleVertexDeformation (some j) i) :
    ∃ w : CliqueBubbleWand G K P, w.bubble = j :=
  P.exists_cliqueBubbleWand_of_anticommutesWith hK hclaw hanti hnotTerm
    hnotExt hnotDef

end PauliCliqueHamiltonianRepresentation


/-! ### Comparison with the set-level relation `EvenHoopBubbleWandArc` -/

namespace RootedInducedPath

/-- A clique-rooted induced path is determined by its original carrier: the
set `{j*} ∪ carrier` induces a path graph, and its ordering starting at the
endpoint `j*` is unique. -/
theorem ext_of_originalCarrier_eq {Q Q' : CliqueRootedInducedPath G K}
    (h : Q.originalCarrier = Q'.originalCarrier) : Q = Q' := by
  apply ext_path
  apply IndexedInducedPath.eq_of_range_eq_of_first_eq
  · ext x
    cases x with
    | none =>
        constructor
        · intro _
          exact ⟨⟨0, Q'.path.nonempty⟩, Q'.root_eq⟩
        · intro _
          exact ⟨⟨0, Q.path.nonempty⟩, Q.root_eq⟩
    | some v =>
        have hv := Set.ext_iff.1 h v
        exact hv
  · rw [Q.root_eq, Q'.root_eq]

/-- In a clique-rooted path, an original vertex of `P` lies in `K` exactly
when it sits at index `1` (the root is adjacent only to `j₁` among the path
vertices). -/
theorem mem_iff_index_eq_one_of_vertex_eq_some
    (P : CliqueRootedInducedPath G K) {i : Fin P.path.card} {v : V}
    (h : P.path.vertex i = some v) : v ∈ K ↔ i.val = 1 := by
  have hadj := P.path.adj_iff ⟨0, P.path.nonempty⟩ i
  rw [P.root_eq, h, G.adjoinRootAt_adj_none_some K v] at hadj
  rw [hadj]
  change 0 + 1 = i.val ∨ i.val + 1 = 0 ↔ i.val = 1
  omega

end RootedInducedPath


/-- The hoop of a bubble wand with an alternating even-hole labeling has even
cardinality: the labeling's carrier has `2k` elements and is the carrier of
the indexed hole `B.hoopHole`. -/
theorem BubbleWand.even_hoopHole_card_of_labeling
    (B : BubbleWand G) {k : Nat} (C : EvenHoleLabeling G k)
    (hC : C.carrier = B.hoop) : Even B.hoopHole.card := by
  have hrange : (Set.range B.hoopHole.vertex).ncard = B.hoopHole.card := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ B.hoopHole.injective,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hA : (Set.range C.a).ncard = k := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ C.a_injective,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hB : (Set.range C.b).ncard = k := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ C.b_injective,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdisj : Disjoint (Set.range C.a) (Set.range C.b) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact C.color_disjoint i j hj.symm
  have hcarrier : C.carrier.ncard = k + k := by
    rw [EvenHoleLabeling.carrier,
      Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _),
      hA, hB]
  exact ⟨k, by rw [← hrange, B.range_hoopHole, ← hC, hcarrier]⟩

namespace EvenHoopArc

variable {P Q : CliqueRootedInducedPath G K}

/-- An extra arc with a non-root handle is an arc of the set-level relation
`EvenHoopBubbleWandArc`: delete the root from `P` and read the wand on the
original tail.  (The converse holds under claw-freeness,
`EvenHoopBubbleWandArc.evenHoopArc`.) -/
theorem evenHoopBubbleWandArc (h : EvenHoopArc G K P Q)
    (hQ : 2 ≤ Q.path.card) : EvenHoopBubbleWandArc G K P Q := by
  obtain ⟨w, rfl, hev⟩ := h
  have hs : 1 ≤ w.split.val := by
    have := hQ
    simp only [CliqueBubbleWand.handle_card] at this
    omega
  have hgap := w.gap
  let B : BubbleWand G :=
    { path := P.originalTail w.two_le_card
      bubble := w.bubble
      split := ⟨w.split.val - 1, by
        change _ < P.path.card - 1
        omega⟩
      gap := by
        change w.split.val - 1 + 3 < P.path.card - 1
        omega
      outside := by
        rintro ⟨i, hi⟩
        apply w.outside
        refine ⟨P.originalTailIndex w.two_le_card i, ?_⟩
        rw [P.path_vertex_originalTailIndex]
        exact congrArg some hi
      adj_iff := by
        intro q
        change G.Adj w.bubble (P.originalTailVertex w.two_le_card q) ↔
          q.val = w.split.val - 1 ∨ q.val = w.split.val - 1 + 1 ∨
            q.val + 1 = P.path.card - 1
        rw [← G.adjoinRootAt_adj_some_some K,
          ← P.path_vertex_originalTailIndex w.two_le_card q, w.adj_iff]
        change (q.val + 1 = w.split.val ∨ q.val + 1 = w.split.val + 1 ∨
            q.val + 1 + 1 = P.path.card) ↔ _
        have := q.isLt
        change q.val < P.path.card - 1 at this
        omega }
  have hcarrier : w.handle.originalCarrier = B.handle := by
    ext v
    rw [w.mem_handle_originalCarrier_iff v]
    constructor
    · rintro ⟨q, hqs, hq⟩
      have hq0 : q.val ≠ 0 := by
        intro h0
        have hq' : q = ⟨0, P.path.nonempty⟩ := Fin.ext h0
        rw [hq', P.root_eq] at hq
        simp at hq
      refine ⟨⟨q.val - 1, by
        change _ < P.path.card - 1
        have := q.isLt
        omega⟩, ?_, ?_⟩
      · change q.val - 1 ≤ w.split.val - 1
        omega
      · have h1 := P.path_vertex_originalTailIndex w.two_le_card
          ⟨q.val - 1, by
            have := q.isLt
            omega⟩
        have hidx : P.originalTailIndex w.two_le_card
            ⟨q.val - 1, by
              have := q.isLt
              omega⟩ = q := by
          apply Fin.ext
          change q.val - 1 + 1 = q.val
          omega
        rw [hidx, hq] at h1
        exact (Option.some.inj h1).symm
    · rintro ⟨q, hqs, hq⟩
      change q.val ≤ w.split.val - 1 at hqs
      refine ⟨P.originalTailIndex w.two_le_card q, ?_, ?_⟩
      · change q.val + 1 ≤ w.split.val
        omega
      · rw [P.path_vertex_originalTailIndex]
        exact congrArg some hq
  have hhole : Even B.hoopHole.card := by
    change Even (P.path.card - 1 - (w.split.val - 1 + 1) + 1)
    have : P.path.card - 1 - (w.split.val - 1 + 1) + 1 = w.hoopCard := by
      unfold CliqueBubbleWand.hoopCard
      omega
    rw [this]
    exact hev
  obtain ⟨k, E, hE⟩ := B.hoopHole.exists_evenHoleLabeling hhole
  exact ⟨B, P.originalCarrier_eq_range_originalTail w.two_le_card,
    hcarrier, k, E, hE.trans B.range_hoopHole⟩

end EvenHoopArc


namespace EvenHoopBubbleWandArc

variable {P Q : CliqueRootedInducedPath G K}

/-- The set-level relation `EvenHoopBubbleWandArc` never points into the root
path `{j*}`: the handle of a `BubbleWand` contains its first vertex, so its
original carrier is nonempty.  This is the defect of the repo relation that
`EvenHoopArc` repairs (`evenHoopArc_cliqueRootPath_iff`). -/
theorem ne_cliqueRootPath (h : EvenHoopBubbleWandArc G K P Q) :
    Q ≠ cliqueRootPath G K := by
  obtain ⟨B, _, htarget, _⟩ := h
  rintro rfl
  have hmem : B.path.vertex ⟨0, B.path.nonempty⟩ ∈
      (cliqueRootPath G K).originalCarrier := by
    rw [htarget]
    exact ⟨⟨0, B.path.nonempty⟩, by simp, rfl⟩
  obtain ⟨i, hi⟩ := hmem
  simp at hi

/-- Under claw-freeness of `G* = G + j*` for a clique `K`, an arc of the
set-level relation `EvenHoopBubbleWandArc` is an arc `P → Q` of
`EvenHoopArc` whose target is not the root path (the set-level relation
omits root handles by construction: `Q.originalCarrier = ∅` is impossible
there because a handle contains the first tail vertex).

Claw-freeness of `G*` is a genuine premise here.  Without it the set-level
relation can contain arcs that are not wands of `G*`: for `K = {a, j}`, the path
`P = (j*, a, p₂, p₃, p₄)` and a bubble `j` adjacent to `a, p₂, p₄` forms a
wand on the original tail `(a, p₂, p₃, p₄)` with handle `{a}` and hoop
`{p₂, p₃, p₄, j}`, yet in `G*` the vertex `j` is also adjacent to the root
`j*`, so `Γ_P(j) = {j₀, j₁, j₂, j₄}` and `j` is not a bubble of `P` (this
configuration contains a claw centred at `j`). -/
theorem evenHoopArc (hK : G.IsClique K)
    (hclaw : (G.adjoinRootAt K).IsClawFree)
    (h : EvenHoopBubbleWandArc G K P Q) :
    EvenHoopArc G K P Q ∧ 2 ≤ Q.path.card := by
  obtain ⟨B, hsource, htarget, k, C, hC⟩ := h
  have hgapB := B.gap
  have hevenB : Even B.hoopHole.card := B.even_hoopHole_card_of_labeling C hC
  -- the first tail vertex of `B` lies in `P.originalCarrier`
  have hB0mem : B.path.vertex ⟨0, B.path.nonempty⟩ ∈ P.originalCarrier := by
    rw [hsource]
    exact ⟨_, rfl⟩
  obtain ⟨i0, hi0⟩ := hB0mem
  have hi0pos : i0.val ≠ 0 := by
    intro h0
    have hq' : i0 = ⟨0, P.path.nonempty⟩ := Fin.ext h0
    rw [hq', P.root_eq] at hi0
    simp at hi0
  have hN : 2 ≤ P.path.card := by
    have := i0.isLt
    omega
  set T := P.originalTail hN with hT
  have hrangeBT : Set.range B.path.vertex = Set.range T.vertex := by
    rw [← hsource]
    exact P.originalCarrier_eq_range_originalTail hN
  -- the target `Q` has an original vertex, hence a first original vertex in `K`
  have hB0handle : B.path.vertex ⟨0, B.path.nonempty⟩ ∈ B.handle :=
    ⟨⟨0, B.path.nonempty⟩, by simp, rfl⟩
  have hB0Q : B.path.vertex ⟨0, B.path.nonempty⟩ ∈ Q.originalCarrier := by
    rw [htarget]
    exact hB0handle
  obtain ⟨iq, hiq⟩ := hB0Q
  have hiqpos : iq.val ≠ 0 := by
    intro h0
    have hq' : iq = ⟨0, Q.path.nonempty⟩ := Fin.ext h0
    rw [hq', Q.root_eq] at hiq
    simp at hiq
  have hQcard : 2 ≤ Q.path.card := by
    have := iq.isLt
    omega
  obtain ⟨v1, hv1⟩ := Q.vertex_eq_some_of_pos ⟨1, by omega⟩ (by simp)
  have hv1K : v1 ∈ K :=
    (Q.mem_iff_index_eq_one_of_vertex_eq_some hv1).2 rfl
  have hv1Q : v1 ∈ Q.originalCarrier := ⟨_, hv1⟩
  have hv1handle : v1 ∈ B.handle := by
    rw [← htarget]
    exact hv1Q
  obtain ⟨r, hrs, hrv⟩ := hv1handle
  -- `v1` is the first tail vertex of `P`, i.e. `T.vertex 0`
  have hv1P : v1 ∈ P.originalCarrier := by
    rw [hsource]
    exact ⟨r, hrv⟩
  obtain ⟨ip, hip⟩ := hv1P
  have hip1 : ip.val = 1 := (P.mem_iff_index_eq_one_of_vertex_eq_some hip).1 hv1K
  have hT0 : T.vertex ⟨0, T.nonempty⟩ = v1 := by
    have h1 := P.path_vertex_originalTailIndex hN ⟨0, by omega⟩
    have hidx : P.originalTailIndex hN ⟨0, by omega⟩ = ip := Fin.ext (by
      change 0 + 1 = ip.val
      omega)
    rw [hidx, hip] at h1
    exact (Option.some.inj h1).symm
  -- degree argument: `r = 0`, i.e. `B.path` starts at `v1`
  have hr0 : r.val = 0 := by
    by_contra hr
    have hrB : r.val + 1 < B.path.card := by
      have := r.isLt
      change r.val ≤ B.split.val at hrs
      omega
    let rl : Fin B.path.card := ⟨r.val - 1, by omega⟩
    let rr : Fin B.path.card := ⟨r.val + 1, hrB⟩
    have hladj : G.Adj (B.path.vertex rl) (B.path.vertex r) :=
      (B.path.adj_iff _ _).2 (Or.inl (by change r.val - 1 + 1 = r.val; omega))
    have hradj : G.Adj (B.path.vertex rr) (B.path.vertex r) :=
      (B.path.adj_iff _ _).2 (Or.inr rfl)
    have hlmem : B.path.vertex rl ∈ Set.range T.vertex := by
      rw [← hrangeBT]
      exact ⟨_, rfl⟩
    have hrmem : B.path.vertex rr ∈ Set.range T.vertex := by
      rw [← hrangeBT]
      exact ⟨_, rfl⟩
    obtain ⟨ml, hml⟩ := hlmem
    obtain ⟨mr, hmr⟩ := hrmem
    have hrT0 : B.path.vertex r = T.vertex ⟨0, T.nonempty⟩ := hrv.trans hT0.symm
    have hmladj : G.Adj (T.vertex ml) (T.vertex ⟨0, T.nonempty⟩) := by
      rw [hml, ← hrT0]
      exact hladj
    have hmradj : G.Adj (T.vertex mr) (T.vertex ⟨0, T.nonempty⟩) := by
      rw [hmr, ← hrT0]
      exact hradj
    have hml1 : ml.val = 1 := by
      rcases (T.adj_iff _ _).1 hmladj with h | h
      · change ml.val + 1 = 0 at h
        omega
      · change 0 + 1 = ml.val at h
        omega
    have hmr1 : mr.val = 1 := by
      rcases (T.adj_iff _ _).1 hmradj with h | h
      · change mr.val + 1 = 0 at h
        omega
      · change 0 + 1 = mr.val at h
        omega
    have hmlmr : ml = mr := Fin.ext (by omega)
    have heq : B.path.vertex rl = B.path.vertex rr := by
      rw [← hml, ← hmr, hmlmr]
    have hinj := B.path.injective heq
    have := congrArg Fin.val hinj
    change r.val - 1 = r.val + 1 at this
    omega
  have hB0T : B.path.vertex ⟨0, B.path.nonempty⟩ = T.vertex ⟨0, T.nonempty⟩ := by
    have hr : r = ⟨0, B.path.nonempty⟩ := Fin.ext hr0
    rw [← hr, hrv, hT0]
  have hcardBT : B.path.card = T.card :=
    le_antisymm
      (B.path.card_le_of_range_eq_of_first_eq T hrangeBT hB0T)
      (T.card_le_of_range_eq_of_first_eq B.path hrangeBT.symm hB0T.symm)
  have hcardT : T.card = P.path.card - 1 := rfl
  have hBT := B.path.vertex_eq_of_range_eq_of_first_eq T hrangeBT hB0T
  -- the dictionary between tail indices of `B` and path indices of `P`
  have hdict : ∀ q : Fin B.path.card,
      P.path.vertex ⟨q.val + 1, by omega⟩ = some (B.path.vertex q) := by
    intro q
    have h1 := P.path_vertex_originalTailIndex hN ⟨q.val, by omega⟩
    have h2 := hBT q.val q.isLt (by omega)
    change P.path.vertex ⟨q.val + 1, _⟩ = some (P.originalTailVertex hN ⟨q.val, _⟩) at h1
    change B.path.vertex ⟨q.val, q.isLt⟩ = P.originalTailVertex hN ⟨q.val, _⟩ at h2
    rw [h1, h2]
  have hdict' : ∀ (i : Fin P.path.card) (v : V), P.path.vertex i = some v →
      ∃ q : Fin B.path.card, B.path.vertex q = v ∧ q.val + 1 = i.val := by
    intro i v hi
    have hipos : i.val ≠ 0 := by
      intro h0
      have hq' : i = ⟨0, P.path.nonempty⟩ := Fin.ext h0
      rw [hq', P.root_eq] at hi
      simp at hi
    refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, ?_,
      by change i.val - 1 + 1 = i.val; omega⟩
    have h1 := hdict ⟨i.val - 1, by have := i.isLt; omega⟩
    have hidx : (⟨i.val - 1 + 1, by have := i.isLt; omega⟩ : Fin P.path.card) = i :=
      Fin.ext (by change i.val - 1 + 1 = i.val; omega)
    rw [hidx, hi] at h1
    exact (Option.some.inj h1).symm
  have hN5 : 5 ≤ P.path.card := by omega
  have hdict2 : ∀ (q : Fin B.path.card) (j : Fin P.path.card),
      j.val = q.val + 1 → P.path.vertex j = some (B.path.vertex q) := by
    intro q j hj
    have h1 := hdict q
    rwa [show j = ⟨q.val + 1, by omega⟩ from Fin.ext hj]
  have hnoadjRoot : ∀ i : Fin P.path.card, 2 ≤ i.val →
      ¬ (G.adjoinRootAt K).Adj none (P.path.vertex i) := by
    intro i hi h
    rcases (P.path.adj_iff ⟨0, P.path.nonempty⟩ i).1
      (by rw [P.root_eq]; exact h) with h | h
    · have h' : 0 + 1 = i.val := h
      omega
    · have h' : i.val + 1 = 0 := h
      omega
  have hnoadj : ∀ i j : Fin P.path.card, i.val + 2 ≤ j.val →
      ¬ (G.adjoinRootAt K).Adj (P.path.vertex i) (P.path.vertex j) := by
    intro i j hij h
    rcases (P.path.adj_iff _ _).1 h with h | h <;> omega
  -- the bubble is not in `K`
  have hbubK : B.bubble ∉ K := by
    intro hbK
    have hbv1 : B.bubble ≠ v1 := by
      intro h
      apply B.outside
      exact ⟨r, hrv.trans h.symm⟩
    have hadj1 : G.Adj B.bubble v1 := hK hbK hv1K hbv1
    have hB0v1 : B.path.vertex ⟨0, B.path.nonempty⟩ = v1 := by
      have hr' : r = ⟨0, B.path.nonempty⟩ := Fin.ext hr0
      rw [← hr']
      exact hrv
    have hs0 : B.split.val = 0 := by
      have h := (B.adj_iff ⟨0, B.path.nonempty⟩).1 (by
        rw [hB0v1]
        exact hadj1)
      change 0 = B.split.val ∨ 0 = B.split.val + 1 ∨ 0 + 1 = B.path.card at h
      omega
    have hl1 : 1 < B.path.card := by omega
    have hl2 : B.path.card - 1 < B.path.card := by omega
    have hP2 : P.path.vertex ⟨2, by omega⟩ = some (B.path.vertex ⟨1, hl1⟩) :=
      hdict2 ⟨1, hl1⟩ _ rfl
    have hP3 : P.path.vertex ⟨B.path.card, by omega⟩ =
        some (B.path.vertex ⟨B.path.card - 1, hl2⟩) :=
      hdict2 ⟨B.path.card - 1, hl2⟩ _ (by change B.path.card = B.path.card - 1 + 1; omega)
    have hca : (G.adjoinRootAt K).Adj (some B.bubble) none :=
      (G.adjoinRootAt_adj_some_none K B.bubble).2 hbK
    have hcb : (G.adjoinRootAt K).Adj (some B.bubble) (P.path.vertex ⟨2, by omega⟩) := by
      rw [hP2]
      change G.Adj B.bubble _
      rw [B.adj_iff]
      change 1 = B.split.val ∨ 1 = B.split.val + 1 ∨ 1 + 1 = B.path.card
      omega
    have hcc : (G.adjoinRootAt K).Adj (some B.bubble) (P.path.vertex ⟨B.path.card, by omega⟩) := by
      rw [hP3]
      change G.Adj B.bubble _
      rw [B.adj_iff]
      change B.path.card - 1 = B.split.val ∨ B.path.card - 1 = B.split.val + 1 ∨
        B.path.card - 1 + 1 = B.path.card
      omega
    have hab : (none : Option V) ≠ P.path.vertex ⟨2, by omega⟩ := by
      rw [hP2]
      simp
    have hac : (none : Option V) ≠ P.path.vertex ⟨B.path.card, by omega⟩ := by
      rw [hP3]
      simp
    have hbc : P.path.vertex ⟨2, by omega⟩ ≠ P.path.vertex ⟨B.path.card, by omega⟩ := by
      intro h
      have := congrArg Fin.val (P.path.injective h)
      change 2 = B.path.card at this
      omega
    rcases hclaw hca hcb hcc hab hac hbc with h | h | h
    · exact hnoadjRoot _ (Nat.le_refl 2) h
    · exact hnoadjRoot _ (by change 2 ≤ B.path.card; omega) h
    · exact hnoadj _ _ (by change 2 + 2 ≤ B.path.card; omega) h
  -- the wand on `P`
  let w : CliqueBubbleWand G K P :=
    { bubble := B.bubble
      split := ⟨B.split.val + 1, by omega⟩
      gap := by
        change B.split.val + 1 + 3 < P.path.card
        omega
      outside := by
        rintro ⟨i, hi⟩
        obtain ⟨q, hq, _⟩ := hdict' i B.bubble hi
        exact B.outside ⟨q, hq⟩
      adj_iff := by
        intro q
        change _ ↔ q.val = B.split.val + 1 ∨ q.val = B.split.val + 1 + 1 ∨
          q.val + 1 = P.path.card
        by_cases hq0 : q.val = 0
        · have hq' : q = ⟨0, P.path.nonempty⟩ := Fin.ext hq0
          rw [hq', P.root_eq]
          constructor
          · intro h
            exact absurd ((G.adjoinRootAt_adj_some_none K B.bubble).1 h) hbubK
          · intro h
            change 0 = B.split.val + 1 ∨ 0 = B.split.val + 1 + 1 ∨ 0 + 1 = P.path.card
              at h
            omega
        · obtain ⟨v, hv⟩ := P.vertex_eq_some_of_pos q (by omega)
          obtain ⟨q', hq'v, hq'i⟩ := hdict' q v hv
          rw [hv]
          change G.Adj B.bubble v ↔ _
          rw [← hq'v, B.adj_iff q']
          omega }
  refine ⟨⟨w, ?_, ?_⟩, hQcard⟩
  · -- the handle of `w` is `Q`
    apply RootedInducedPath.ext_of_originalCarrier_eq
    rw [htarget]
    ext v
    rw [w.mem_handle_originalCarrier_iff v]
    constructor
    · rintro ⟨q, hqs, hq⟩
      obtain ⟨q', hq'v, hq'i⟩ := hdict' q v hq
      refine ⟨q', ?_, hq'v⟩
      change q.val ≤ B.split.val + 1 at hqs
      omega
    · rintro ⟨q', hq's, hq'v⟩
      refine ⟨⟨q'.val + 1, by omega⟩, ?_, ?_⟩
      · change q'.val + 1 ≤ B.split.val + 1
        omega
      · rw [hdict q', hq'v]
  · -- the hoop is even
    change Even (P.path.card - (B.split.val + 1))
    have hcard : P.path.card - (B.split.val + 1) = B.hoopHole.card := by
      change _ = B.path.card - (B.split.val + 1) + 1
      omega
    rw [hcard]
    exact hevenB

end EvenHoopBubbleWandArc

/-- Fidelity bridge: for a clique `K` with `G* = G + j*` claw-free, the
set-level relation `EvenHoopBubbleWandArc` (which discards the root and the
order of the paths) is exactly `EvenHoopArc` restricted to targets that are
not the root path.  The arcs into the root path `{j*}` are the ones the set-level
relation omits (`evenHoopArc_cliqueRootPath_iff`). -/
theorem evenHoopBubbleWandArc_iff_evenHoopArc (hK : G.IsClique K)
    (hclaw : (G.adjoinRootAt K).IsClawFree)
    (P Q : CliqueRootedInducedPath G K) :
    EvenHoopBubbleWandArc G K P Q ↔ EvenHoopArc G K P Q ∧ 2 ≤ Q.path.card :=
  ⟨EvenHoopBubbleWandArc.evenHoopArc hK hclaw,
    fun h => h.1.evenHoopBubbleWandArc h.2⟩

/-! ### Example: a root-handle wand on the 4-cycle

The 4-cycle `0 - 1 - 2 - 3 - 0` with `K = {0, 1}`.  The rooted path
`P = (j*, 0, 3, 2)` has the bubble `1` with `Γ_P(1) = {j₀, j₁, j₃}`, so it is a
wand with split index `s = 0`: its handle is the root path `{j*}` and its hoop
is the whole 4-cycle.  The repo relation `EvenHoopBubbleWandArc` has no arc
`P → {j*}`, while `EvenHoopArc` has one. -/

namespace CliqueBubbleWand

namespace Example

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
def fourCycle : SimpleGraph (Fin 4) where
  Adj a b := (a.val + 1) % 4 = b.val ∨ (b.val + 1) % 4 = a.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- The clique `K = {0, 1}`. -/
def edgeClique : Set (Fin 4) := {0, 1}

/-- The rooted induced path `(j*, 0, 3, 2)` of `G*`. -/
def path : CliqueRootedInducedPath fourCycle edgeClique where
  path :=
    { card := 4
      nonempty := by decide
      vertex := ![none, some 0, some 3, some 2]
      injective := by decide
      adj_iff := by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [adjoinRootAt, AdjoinRootAdj, fourCycle, edgeClique] }
  root_eq := rfl

/-- The bubble `1` is a wand on `(j*, 0, 3, 2)` with split index `0`. -/
def wand : CliqueBubbleWand fourCycle edgeClique path where
  bubble := 1
  split := ⟨0, by decide⟩
  gap := by decide
  outside := by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [path] at hi
  adj_iff := by
    intro q
    fin_cases q <;>
      simp [path, adjoinRootAt, AdjoinRootAdj, fourCycle, edgeClique]

theorem wand_handle : wand.handle = cliqueRootPath fourCycle edgeClique :=
  wand.handle_eq_cliqueRootPath_iff.2 rfl

/-- The root-handle arc exists in `Λ`. -/
theorem evenHoopArc_root :
    EvenHoopArc fourCycle edgeClique path (cliqueRootPath fourCycle edgeClique) :=
  ⟨wand, wand_handle, by decide⟩

/-- It is invisible to the set-level relation `EvenHoopBubbleWandArc`. -/
theorem not_evenHoopBubbleWandArc_root :
    ¬ EvenHoopBubbleWandArc fourCycle edgeClique path
      (cliqueRootPath fourCycle edgeClique) :=
  fun h => h.ne_cliqueRootPath rfl

end Example

end CliqueBubbleWand

end SimpleGraph
