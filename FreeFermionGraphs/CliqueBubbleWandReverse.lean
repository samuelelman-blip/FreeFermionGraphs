import FreeFermionGraphs.CliqueBubbleWand
import FreeFermionGraphs.PathClosedNeighborhood

/-!
# Reversal of a bubble wand

Case (b.iv) of the proof of Theorem 3 (arXiv 2305.15625v1, L1520).  Let
`P = (j₀ = j*, j₁, ..., j_ℓ)` be a rooted induced path of `G* = G + j*` and let
`j` be the bubble of a wand on `P` with split index `s` (`Γ_P(j) = {j_s, j_{s+1}, j_ℓ}`,
`0 ≤ s < ℓ - 2`).  v1 introduces

`P* = (P ∪ {j}) ∖ {j_{s+1}}`,

"the path traversing `C` in the opposite direction to `P`", where
`C = {j_{s+1}, ..., j_ℓ, j}` is the hoop.  As an *ordered* path this is

`P* = (j₀, ..., j_s, j, j_ℓ, j_{ℓ-1}, ..., j_{s+2})`.

The handle `P_s = (j₀, ..., j_s)` is unchanged, and the hoop is traversed from
`j` through `j_ℓ` down to `j_{s+2}`.  This is the object that v1 only writes as
a set difference; here the ordering is part of the data, since the rooted
induced paths of `G*` are the vertices of the induced-path tree.

Main declarations (all for `w : CliqueBubbleWand G K P`).

* `reverseBubble`: the original vertex `j_{s+1}`, the vertex that `P*` drops;
* `reverse`: the rooted induced path `P*` (`reverse_card`: `|P*| = |P|`);
* `reverseWand`: `j_{s+1}` is the bubble of a wand on `P*` with the same split
  index (`reverseWand_split_val`), the same handle (`reverseWand_handle`), the
  same hoop size (`reverseWand_hoopCard`) and the same hoop carrier
  (`reverseWand_hoopCarrier`);
* `reverseWand_reverse`, `reverseWand_reverseBubble`: `(P*)* = P`, and the
  vertex dropped by the second reversal is the original bubble;
* `reverse_ne`: `P* ≠ P`;
* `closedNbhd_reverse`: if `G` is claw-free then `N(P*) = N(P)`.  This is not
  stated in v1.  It uses claw-freeness of `G` only (not simpliciality of `K`):
  a claw centred at the bubble `j` with leaves `y`, `j_{s+1}`, `j_ℓ`, the last
  two being non-adjacent because `ℓ ≥ s + 3`, shows `Γ[j] ⊆ N(P)`; the converse
  inclusion is the same statement for the wand on `P*` (whose bubble is
  `j_{s+1}`), together with `(P*)* = P`.

Indices: `P.path.card = ℓ + 1`, the split index is `split.val = s`, and
`s + 3 < P.path.card` is `s < ℓ - 2`.  The path `P*` has the vertex `j_q` at
index `q ≤ s`, the bubble at index `s + 1`, and `j_{ℓ + s + 2 - q}` at index
`q ≥ s + 2`, that is, `P.path.vertex (card + s + 1 - q)`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace CliqueBubbleWand

variable {G : SimpleGraph V} {K : Set V} {P : CliqueRootedInducedPath G K}

/-! ### The dropped vertex `j_{s+1}` -/

/-- The original vertex `j_{s+1}` at path index `split + 1`: the first vertex
of the hoop, which the reversed path `P*` drops (v1 L1520:
`P* = (P ∪ {j}) ∖ {j_{s+1}}`). -/
noncomputable def reverseBubble (w : CliqueBubbleWand G K P) : V :=
  w.hoopVertex ⟨0, by have := w.gap; omega⟩

/-- The path vertex at index `split + 1` is the original vertex
`reverseBubble`. -/
theorem path_vertex_split_succ (w : CliqueBubbleWand G K P)
    (q : Fin P.path.card) (hq : q.val = w.split.val + 1) :
    P.path.vertex q = some w.reverseBubble := by
  have h := w.path_vertex_hoopIndex ⟨0, by have := w.gap; omega⟩
  have hidx : w.hoopIndex ⟨0, by have := w.gap; omega⟩ = q :=
    Fin.ext (by simp [hoopIndex, hq])
  rw [hidx] at h
  exact h

/-- A path vertex equals `j_{s+1}` exactly at index `s + 1`. -/
theorem path_vertex_eq_reverseBubble_iff (w : CliqueBubbleWand G K P)
    (q : Fin P.path.card) :
    P.path.vertex q = some w.reverseBubble ↔ q.val = w.split.val + 1 := by
  have hgap := w.gap
  constructor
  · intro h
    have := w.path_vertex_split_succ ⟨w.split.val + 1, by omega⟩ rfl
    have hq := P.path.injective (h.trans this.symm)
    exact congrArg Fin.val hq
  · exact w.path_vertex_split_succ q

/-- `j_{s+1}` is a vertex of `P`. -/
theorem reverseBubble_mem_originalCarrier (w : CliqueBubbleWand G K P) :
    w.reverseBubble ∈ P.originalCarrier :=
  ⟨⟨w.split.val + 1, by have := w.gap; omega⟩,
    w.path_vertex_split_succ _ rfl⟩

/-- `j_{s+1}` is not in the handle `P_s`. -/
theorem reverseBubble_notMem_handle (w : CliqueBubbleWand G K P) :
    w.reverseBubble ∉ w.handle.originalCarrier := by
  intro h
  obtain ⟨q, hqs, hq⟩ := (w.mem_handle_originalCarrier_iff _).1 h
  have := (w.path_vertex_eq_reverseBubble_iff q).1 hq
  omega

/-- The bubble is not a vertex of `P`. -/
theorem bubble_notMem_originalCarrier (w : CliqueBubbleWand G K P) :
    w.bubble ∉ P.originalCarrier :=
  fun h => w.outside h

/-- The bubble and the dropped vertex `j_{s+1}` are adjacent in `G`. -/
theorem adj_bubble_reverseBubble (w : CliqueBubbleWand G K P) :
    G.Adj w.bubble w.reverseBubble := by
  have h := w.adj_next
  rw [w.path_vertex_split_succ _ rfl] at h
  exact h

/-! ### The reversed path `P*` -/

/-- The vertex map of `P* = (j₀, ..., j_s, j, j_ℓ, j_{ℓ-1}, ..., j_{s+2})`:
`j_q` for `q ≤ s`, the bubble `j` at index `s + 1`, and `j_{ℓ + s + 2 - q}`
(that is, `P.path.vertex (card + s + 1 - q)`) for `q ≥ s + 2`. -/
def reverseVertex (w : CliqueBubbleWand G K P)
    (q : Fin P.path.card) : Option V :=
  if h1 : q.val ≤ w.split.val then P.path.vertex q
  else if _h2 : q.val = w.split.val + 1 then some w.bubble
  else P.path.vertex ⟨P.path.card + w.split.val + 1 - q.val, by
    have := q.isLt
    omega⟩

theorem reverseVertex_of_le (w : CliqueBubbleWand G K P)
    {q : Fin P.path.card} (h : q.val ≤ w.split.val) :
    w.reverseVertex q = P.path.vertex q := by
  simp only [reverseVertex, dif_pos h]

theorem reverseVertex_split_succ (w : CliqueBubbleWand G K P)
    {q : Fin P.path.card} (h : q.val = w.split.val + 1) :
    w.reverseVertex q = some w.bubble := by
  have h1 : ¬ q.val ≤ w.split.val := by omega
  simp only [reverseVertex, dif_neg h1, dif_pos h]

theorem reverseVertex_of_gt (w : CliqueBubbleWand G K P)
    {q r : Fin P.path.card} (h : w.split.val + 2 ≤ q.val)
    (hr : r.val = P.path.card + w.split.val + 1 - q.val) :
    w.reverseVertex q = P.path.vertex r := by
  have h1 : ¬ q.val ≤ w.split.val := by omega
  have h2 : ¬ q.val = w.split.val + 1 := by omega
  simp only [reverseVertex, dif_neg h1, dif_neg h2]
  congr 1
  exact Fin.ext hr.symm

theorem reverseVertex_injective (w : CliqueBubbleWand G K P) :
    Function.Injective w.reverseVertex := by
  have hgap := w.gap
  intro p q hpq
  have hplt := p.isLt
  have hqlt := q.isLt
  have hp : p.val ≤ w.split.val ∨ p.val = w.split.val + 1 ∨
      w.split.val + 2 ≤ p.val := by omega
  have hq : q.val ≤ w.split.val ∨ q.val = w.split.val + 1 ∨
      w.split.val + 2 ≤ q.val := by omega
  have hinj := P.path.injective
  apply Fin.ext
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
  · rw [w.reverseVertex_of_le hp, w.reverseVertex_of_le hq] at hpq
    exact congrArg Fin.val (hinj hpq)
  · rw [w.reverseVertex_of_le hp, w.reverseVertex_split_succ hq] at hpq
    exact absurd ⟨p, hpq⟩ w.outside
  · rw [w.reverseVertex_of_le hp,
      w.reverseVertex_of_gt hq (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩)
        rfl] at hpq
    have := congrArg Fin.val (hinj hpq)
    simp only at this
    omega
  · rw [w.reverseVertex_split_succ hp, w.reverseVertex_of_le hq] at hpq
    exact absurd ⟨q, hpq.symm⟩ w.outside
  · omega
  · rw [w.reverseVertex_split_succ hp,
      w.reverseVertex_of_gt hq (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩)
        rfl] at hpq
    exact absurd ⟨_, hpq.symm⟩ w.outside
  · rw [w.reverseVertex_of_gt hp (r := ⟨P.path.card + w.split.val + 1 - p.val, by omega⟩)
        rfl, w.reverseVertex_of_le hq] at hpq
    have := congrArg Fin.val (hinj hpq)
    simp only at this
    omega
  · rw [w.reverseVertex_of_gt hp (r := ⟨P.path.card + w.split.val + 1 - p.val, by omega⟩)
        rfl, w.reverseVertex_split_succ hq] at hpq
    exact absurd ⟨_, hpq⟩ w.outside
  · rw [w.reverseVertex_of_gt hp (r := ⟨P.path.card + w.split.val + 1 - p.val, by omega⟩)
        rfl, w.reverseVertex_of_gt hq
        (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩) rfl] at hpq
    have := congrArg Fin.val (hinj hpq)
    simp only at this
    omega

/-- Adjacency in `G*` of the vertices of `P*` at indices `p ≤ q` is the
adjacency of consecutive indices. -/
theorem reverseVertex_adj_of_le (w : CliqueBubbleWand G K P)
    (p q : Fin P.path.card) (hpq : p.val ≤ q.val) :
    (G.adjoinRootAt K).Adj (w.reverseVertex p) (w.reverseVertex q) ↔
      p.val + 1 = q.val ∨ q.val + 1 = p.val := by
  have hgap := w.gap
  have hplt := p.isLt
  have hqlt := q.isLt
  have hp : p.val ≤ w.split.val ∨ p.val = w.split.val + 1 ∨
      w.split.val + 2 ≤ p.val := by omega
  have hq : q.val ≤ w.split.val ∨ q.val = w.split.val + 1 ∨
      w.split.val + 2 ≤ q.val := by omega
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
  · -- both in the handle
    rw [w.reverseVertex_of_le hp, w.reverseVertex_of_le hq]
    exact P.path.adj_iff p q
  · -- `p ≤ s`, `q = s + 1`: the bubble
    rw [w.reverseVertex_of_le hp, w.reverseVertex_split_succ hq, adj_comm,
      w.adj_iff p]
    omega
  · -- `p ≤ s`, `q ≥ s + 2`: no adjacency
    rw [w.reverseVertex_of_le hp,
      w.reverseVertex_of_gt hq (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩)
        rfl, P.path.adj_iff]
    simp only
    omega
  · omega
  · -- `p = q = s + 1`
    have hpq' : p = q := Fin.ext (by omega)
    subst hpq'
    rw [w.reverseVertex_split_succ hp]
    simp only [(G.adjoinRootAt K).loopless.irrefl, false_iff]
    omega
  · -- `p = s + 1`, `q ≥ s + 2`
    rw [w.reverseVertex_split_succ hp,
      w.reverseVertex_of_gt hq (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩)
        rfl, w.adj_iff]
    simp only
    omega
  · omega
  · omega
  · -- both in the mirrored hoop
    rw [w.reverseVertex_of_gt hp (r := ⟨P.path.card + w.split.val + 1 - p.val, by omega⟩)
        rfl, w.reverseVertex_of_gt hq
        (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩) rfl,
      P.path.adj_iff]
    simp only
    omega

/-- The reversed path `P* = (j₀, ..., j_s, j, j_ℓ, ..., j_{s+2})` of `G*`
(v1 L1520: `P* = (P ∪ {j}) ∖ {j_{s+1}}`, "the path traversing `C` in the
opposite direction to `P`"), as a rooted induced path with the same handle
`P_s`. -/
def reverse (w : CliqueBubbleWand G K P) : CliqueRootedInducedPath G K where
  path :=
    { card := P.path.card
      nonempty := P.path.nonempty
      vertex := w.reverseVertex
      injective := w.reverseVertex_injective
      adj_iff := by
        intro p q
        rcases le_total p.val q.val with h | h
        · exact w.reverseVertex_adj_of_le p q h
        · rw [adj_comm, w.reverseVertex_adj_of_le q p h]
          omega }
  root_eq := by
    change w.reverseVertex ⟨0, P.path.nonempty⟩ = none
    rw [w.reverseVertex_of_le (by simp)]
    exact P.root_eq

@[simp]
theorem reverse_card (w : CliqueBubbleWand G K P) :
    w.reverse.path.card = P.path.card :=
  rfl

theorem reverse_vertex_of_le (w : CliqueBubbleWand G K P)
    {q : Fin P.path.card} (h : q.val ≤ w.split.val) :
    w.reverse.path.vertex q = P.path.vertex q :=
  w.reverseVertex_of_le h

theorem reverse_vertex_split_succ (w : CliqueBubbleWand G K P)
    {q : Fin P.path.card} (h : q.val = w.split.val + 1) :
    w.reverse.path.vertex q = some w.bubble :=
  w.reverseVertex_split_succ h

theorem reverse_vertex_of_gt (w : CliqueBubbleWand G K P)
    {q r : Fin P.path.card} (h : w.split.val + 2 ≤ q.val)
    (hr : r.val = P.path.card + w.split.val + 1 - q.val) :
    w.reverse.path.vertex q = P.path.vertex r :=
  w.reverseVertex_of_gt h hr

/-- The vertices of `P*` are the bubble together with the vertices of `P`
other than `j_{s+1}`. -/
theorem mem_reverse_originalCarrier_iff (w : CliqueBubbleWand G K P) (x : V) :
    x ∈ w.reverse.originalCarrier ↔
      x = w.bubble ∨ (x ∈ P.originalCarrier ∧ x ≠ w.reverseBubble) := by
  have hgap := w.gap
  have hc : w.reverse.path.card = P.path.card := rfl
  constructor
  · rintro ⟨q, hq⟩
    have hqlt := q.isLt
    have hcases : q.val ≤ w.split.val ∨ q.val = w.split.val + 1 ∨
        w.split.val + 2 ≤ q.val := by omega
    rcases hcases with h | h | h
    · rw [w.reverse_vertex_of_le h] at hq
      refine Or.inr ⟨⟨q, hq⟩, ?_⟩
      rintro rfl
      have := (w.path_vertex_eq_reverseBubble_iff q).1 hq
      omega
    · rw [w.reverse_vertex_split_succ h] at hq
      exact Or.inl (Option.some.inj hq).symm
    · rw [w.reverse_vertex_of_gt h
        (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩) rfl] at hq
      refine Or.inr ⟨⟨_, hq⟩, ?_⟩
      rintro rfl
      have := (w.path_vertex_eq_reverseBubble_iff _).1 hq
      simp only at this
      omega
  · rintro (rfl | ⟨⟨q, hq⟩, hne⟩)
    · exact ⟨⟨w.split.val + 1, by omega⟩,
        w.reverse_vertex_split_succ rfl⟩
    · have hqlt := q.isLt
      have hqne : q.val ≠ w.split.val + 1 := by
        intro h
        apply hne
        have := w.path_vertex_split_succ q h
        exact Option.some.inj (hq.symm.trans this)
      by_cases hle : q.val ≤ w.split.val
      · exact ⟨q, by rw [w.reverse_vertex_of_le hle]; exact hq⟩
      · refine ⟨⟨P.path.card + w.split.val + 1 - q.val, by omega⟩, ?_⟩
        exact (w.reverse_vertex_of_gt
          (q := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩)
          (r := q) (by simp only; omega) (by simp only; omega)).trans hq

/-! ### The wand on `P*` -/

/-- `j_{s+1}` is the bubble of a wand on `P*`, with the same split index
(v1 L1520).  The hoop of `w` is traversed in the opposite direction. -/
noncomputable def reverseWand (w : CliqueBubbleWand G K P) :
    CliqueBubbleWand G K w.reverse where
  bubble := w.reverseBubble
  split := w.split
  gap := w.gap
  outside := by
    rintro ⟨q, hq⟩
    have hgap := w.gap
    have hqlt := q.isLt
    have hc : w.reverse.path.card = P.path.card := rfl
    have hcases : q.val ≤ w.split.val ∨ q.val = w.split.val + 1 ∨
        w.split.val + 2 ≤ q.val := by omega
    rcases hcases with h | h | h
    · rw [w.reverse_vertex_of_le h] at hq
      have := (w.path_vertex_eq_reverseBubble_iff q).1 hq
      omega
    · rw [w.reverse_vertex_split_succ h] at hq
      exact w.bubble_notMem_originalCarrier
        ⟨⟨w.split.val + 1, by omega⟩, by
          rw [w.path_vertex_split_succ _ rfl]
          exact congrArg some (Option.some.inj hq).symm⟩
    · rw [w.reverse_vertex_of_gt h
        (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩) rfl] at hq
      have := (w.path_vertex_eq_reverseBubble_iff _).1 hq
      simp only at this
      omega
  adj_iff := by
    intro q
    have hgap := w.gap
    have hqlt := q.isLt
    have hc : w.reverse.path.card = P.path.card := rfl
    have hcases : q.val ≤ w.split.val ∨ q.val = w.split.val + 1 ∨
        w.split.val + 2 ≤ q.val := by omega
    have hrb := w.path_vertex_split_succ ⟨w.split.val + 1, by omega⟩ rfl
    rcases hcases with h | h | h
    · -- `q` in the handle: `j_{s+1}` is adjacent to `j_s` only
      rw [w.reverse_vertex_of_le h, ← hrb, P.path.adj_iff]
      simp only
      omega
    · -- `q = s + 1`: the bubble
      rw [w.reverse_vertex_split_succ h]
      exact iff_of_true w.adj_bubble_reverseBubble.symm (Or.inr (Or.inl h))
    · -- `q ≥ s + 2`: `j_{s+1}` is adjacent to `j_{s+2}` (index `ℓ` of `P*`)
      rw [w.reverse_vertex_of_gt h
        (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩) rfl, ← hrb,
        P.path.adj_iff]
      simp only
      omega

@[simp]
theorem reverseWand_split_val (w : CliqueBubbleWand G K P) :
    w.reverseWand.split.val = w.split.val :=
  rfl

@[simp]
theorem reverseWand_bubble (w : CliqueBubbleWand G K P) :
    w.reverseWand.bubble = w.reverseBubble :=
  rfl

/-- The vertex of `P*` at index `s + 1` is the original bubble, so the vertex
dropped by the second reversal is the original bubble. -/
theorem reverseWand_reverseBubble (w : CliqueBubbleWand G K P) :
    w.reverseWand.reverseBubble = w.bubble := by
  have hgap := w.gap
  let q : Fin w.reverse.path.card := ⟨w.split.val + 1, by
    change w.split.val + 1 < P.path.card
    omega⟩
  have h1 := w.reverseWand.path_vertex_split_succ q rfl
  have h2 := w.reverse_vertex_split_succ (q := q) rfl
  exact Option.some.inj (h1.symm.trans h2)

/-- `(P*)* = P` (the second reversal uses the wand `reverseWand` on `P*`). -/
theorem reverseWand_reverse (w : CliqueBubbleWand G K P) :
    w.reverseWand.reverse = P := by
  have hgap := w.gap
  apply RootedInducedPath.ext_path
  refine IndexedInducedPath.ext_card_vertex rfl (heq_of_eq ?_)
  funext q
  have hqlt := q.isLt
  have hc : w.reverse.path.card = P.path.card := rfl
  have hc' : w.reverseWand.reverse.path.card = P.path.card := rfl
  have hcases : q.val ≤ w.split.val ∨ q.val = w.split.val + 1 ∨
      w.split.val + 2 ≤ q.val := by omega
  rcases hcases with h | h | h
  · change w.reverseWand.reverseVertex q = P.path.vertex q
    rw [w.reverseWand.reverseVertex_of_le h]
    exact w.reverse_vertex_of_le h
  · change w.reverseWand.reverseVertex q = P.path.vertex q
    rw [w.reverseWand.reverseVertex_split_succ h]
    exact (congrArg some (w.reverseWand_bubble)).trans
      (w.path_vertex_split_succ q h).symm
  · change w.reverseWand.reverseVertex q = P.path.vertex q
    rw [w.reverseWand.reverseVertex_of_gt h
      (r := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩) rfl]
    exact w.reverse_vertex_of_gt (q := ⟨P.path.card + w.split.val + 1 - q.val, by omega⟩)
      (r := q) (by simp only; omega) (by simp only; omega)

/-- The wand on `P*` has the same handle `P_s` (v1 L1520: the path `P*` is a
path "traversing `C` in the opposite direction", with the same handle). -/
theorem reverseWand_handle (w : CliqueBubbleWand G K P) :
    w.reverseWand.handle = w.handle := by
  apply RootedInducedPath.ext_path
  refine IndexedInducedPath.ext_card_vertex rfl (heq_of_eq ?_)
  funext q
  have hqlt : q.val < w.split.val + 1 := q.isLt
  change w.reverse.path.vertex ⟨q.val, _⟩ = P.path.vertex ⟨q.val, _⟩
  exact w.reverse_vertex_of_le (by change q.val ≤ w.split.val; omega)

/-- The wand on `P*` has the same hoop size `ℓ - s + 1`. -/
theorem reverseWand_hoopCard (w : CliqueBubbleWand G K P) :
    w.reverseWand.hoopCard = w.hoopCard :=
  rfl

/-- The wand on `P*` has the same hoop carrier `{j_{s+1}, ..., j_ℓ, j}`. -/
theorem reverseWand_hoopCarrier (w : CliqueBubbleWand G K P) :
    w.reverseWand.hoopCarrier = w.hoopCarrier := by
  have hsub : ∀ x, x ∈ w.handle.originalCarrier → x ∈ P.originalCarrier := by
    intro x hx
    obtain ⟨q, _, hq⟩ := (w.mem_handle_originalCarrier_iff x).1 hx
    exact ⟨q, hq⟩
  unfold hoopCarrier bubbleWandArcHoopCarrier
  rw [w.reverseWand_handle]
  ext x
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff,
    w.mem_reverse_originalCarrier_iff]
  change ((x = w.bubble ∨ x ∈ P.originalCarrier ∧ x ≠ w.reverseBubble) ∧
      x ∉ w.handle.originalCarrier) ∨ x = w.reverseBubble ↔
    (x ∈ P.originalCarrier ∧ x ∉ w.handle.originalCarrier) ∨ x = w.bubble
  constructor
  · rintro (⟨h | ⟨hx, _⟩, hnH⟩ | rfl)
    · exact Or.inr h
    · exact Or.inl ⟨hx, hnH⟩
    · exact Or.inl ⟨w.reverseBubble_mem_originalCarrier, w.reverseBubble_notMem_handle⟩
  · rintro (⟨hx, hnH⟩ | h)
    · by_cases hne : x = w.reverseBubble
      · exact Or.inr hne
      · exact Or.inl ⟨Or.inr ⟨hx, hne⟩, hnH⟩
    · refine Or.inl ⟨Or.inl h, fun hxH => ?_⟩
      exact w.bubble_notMem_originalCarrier (h ▸ hsub x hxH)

/-- `P* ≠ P`: the vertex at index `s + 1` is the bubble in `P*` and
`j_{s+1}` in `P`. -/
theorem reverse_ne (w : CliqueBubbleWand G K P) : w.reverse ≠ P := by
  intro h
  have hgap := w.gap
  have key : ∀ {R R' : CliqueRootedInducedPath G K}, R = R' →
      ∀ (a : Fin R.path.card) (b : Fin R'.path.card), a.val = b.val →
        R.path.vertex a = R'.path.vertex b := by
    intro R R' hR
    subst hR
    intro a b hab
    rw [Fin.ext hab]
  have h1 := key h ⟨w.split.val + 1, by change _ < P.path.card; omega⟩
    ⟨w.split.val + 1, by omega⟩ rfl
  rw [w.reverse_vertex_split_succ rfl,
    w.path_vertex_split_succ _ rfl] at h1
  exact w.outside ⟨⟨w.split.val + 1, by omega⟩, by
    rw [w.path_vertex_split_succ _ rfl]
    exact congrArg some (Option.some.inj h1).symm⟩

/-! ### The closed neighbourhood is unchanged by the reversal -/

/-- Claw-freeness of `G` forces `Γ[j] ⊆ N(P)` for the bubble `j` of a wand on
`P`: a neighbour `y` of `j` that is none of `j_{s+1}`, `j_ℓ` forms a claw at
`j` with `j_{s+1}` and `j_ℓ`, which are non-adjacent because `ℓ ≥ s + 3`; so
`y` is adjacent to `j_{s+1}` or to `j_ℓ`, hence lies in `N(P)`. -/
theorem closedNeighborhood_bubble_subset (hclaw : G.IsClawFree)
    (w : CliqueBubbleWand G K P) :
    G.closedNeighborhood w.bubble ⊆ P.closedNbhd := by
  have hgap := w.gap
  have hterm : 0 < P.terminalIndex.val := by
    simp only [RootedInducedPath.terminalIndex]
    omega
  obtain ⟨jl, hjl⟩ := P.vertex_eq_some_of_pos P.terminalIndex hterm
  have hrb := w.path_vertex_split_succ ⟨w.split.val + 1, by omega⟩ rfl
  have hb1 : G.Adj w.bubble w.reverseBubble := w.adj_bubble_reverseBubble
  have hb2 : G.Adj w.bubble jl := by
    have := w.adj_terminal
    rw [hjl] at this
    exact this
  have hne : w.reverseBubble ≠ jl := by
    intro h
    rw [h] at hrb
    have := congrArg Fin.val (P.path.injective (hrb.trans hjl.symm))
    simp only [RootedInducedPath.terminalIndex] at this
    omega
  have hnadj : ¬ G.Adj w.reverseBubble jl := by
    intro hadj
    have hadj' : (G.adjoinRootAt K).Adj (some w.reverseBubble) (some jl) := hadj
    rw [← hrb, ← hjl, P.path.adj_iff] at hadj'
    simp only [RootedInducedPath.terminalIndex] at hadj'
    omega
  intro y hy
  rcases hy with rfl | hy
  · exact P.closedNeighborhood_subset_closedNbhd w.reverseBubble_mem_originalCarrier
      (Or.inr hb1.symm)
  · by_cases hy1 : y = w.reverseBubble
    · subst hy1
      exact P.closedNeighborhood_subset_closedNbhd w.reverseBubble_mem_originalCarrier
        (Or.inl rfl)
    by_cases hy2 : y = jl
    · subst hy2
      exact P.mem_closedNbhd_of_vertex_eq P.terminalIndex hjl
    rcases hclaw hy hb1 hb2 hy1 hy2 hne with h | h | h
    · exact P.closedNeighborhood_subset_closedNbhd w.reverseBubble_mem_originalCarrier
        (Or.inr h.symm)
    · exact P.closedNeighborhood_subset_closedNbhd ⟨P.terminalIndex, hjl⟩
        (Or.inr h.symm)
    · exact (hnadj h).elim

/-- One inclusion: `N(P*) ⊆ N(P)`.  Only the bubble is new in `P*`, and
`Γ[j] ⊆ N(P)` by `closedNeighborhood_bubble_subset`. -/
theorem closedNbhd_reverse_subset (hclaw : G.IsClawFree)
    (w : CliqueBubbleWand G K P) :
    w.reverse.closedNbhd ⊆ P.closedNbhd := by
  intro x hx
  rcases hx with hxK | hx
  · exact P.subset_closedNbhd hxK
  · obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rcases (w.mem_reverse_originalCarrier_iff v).1 hv with rfl | ⟨hvP, _⟩
    · exact closedNeighborhood_bubble_subset hclaw w hxv
    · exact P.closedNeighborhood_subset_closedNbhd hvP hxv

/-- `N(P*) = N(P)` when `G` is claw-free (not stated in v1; it is the
neighbourhood invariance accompanying the reversal of case (b.iv), L1520).
The inclusion `⊆` is `closedNbhd_reverse_subset`; the converse is the same
statement for the wand `reverseWand` on `P*`, because `(P*)* = P`. -/
theorem closedNbhd_reverse (hclaw : G.IsClawFree)
    (w : CliqueBubbleWand G K P) :
    w.reverse.closedNbhd = P.closedNbhd := by
  apply Set.Subset.antisymm (closedNbhd_reverse_subset hclaw w)
  have h := closedNbhd_reverse_subset hclaw w.reverseWand
  rwa [reverseWand_reverse] at h

/-! ### An example: the four-cycle -/

namespace Example

/-- In the four-cycle example `P = (j*, 0, 3, 2)` with bubble `1` and split
index `0`, the wand reversal drops `j₁ = 0`. -/
theorem wand_reverseBubble : wand.reverseBubble = 0 := by
  have h := wand.path_vertex_split_succ ⟨1, by decide⟩ rfl
  simp [path] at h
  exact h.symm

/-- The reversed path is `P* = (j*, 1, 2, 3)`. -/
theorem wand_reverse_vertex :
    wand.reverse.path.vertex ⟨1, by decide⟩ = some 1 ∧
    wand.reverse.path.vertex ⟨2, by decide⟩ = some 2 ∧
    wand.reverse.path.vertex ⟨3, by decide⟩ = some 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact wand.reverse_vertex_split_succ rfl
  · rw [wand.reverse_vertex_of_gt (r := ⟨3, by decide⟩) (by decide) rfl]
    simp [path]
  · rw [wand.reverse_vertex_of_gt (r := ⟨2, by decide⟩) (by decide) rfl]
    simp [path]

end Example

end CliqueBubbleWand

end SimpleGraph
