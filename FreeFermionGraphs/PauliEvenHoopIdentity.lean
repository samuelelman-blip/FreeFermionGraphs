import FreeFermionGraphs.PauliWandPairing
import FreeFermionGraphs.PauliHoleOperator

/-!
# The even-hoop operator identity `h_P h_j = (-1)^{k-1} h_{P_s} h_C`

Operator content of the assembly of hole products in case (b.iv) of the proof of
Theorem 3 (arXiv 2305.15625v1, L1555-1576).  The sign is not displayed in v1; it is the
source of the sign defect in Eq. (decoratedtree) (paper issue 3).

Let `P = (j₀ = j*, j₁, ..., j_ℓ)` be a rooted induced path of `G*` and let `j` be the bubble
of a wand on `P` with split index `s` (`Γ_P(j) = {j_s, j_{s+1}, j_ℓ}`, `0 ≤ s < ℓ - 2`,
`s = 0` allowed).  The handle is `Q = P_s = (j₀, ..., j_s)` and the hoop is
`C = {j_{s+1}, ..., j_ℓ, j}`, an induced cycle on `m = ℓ - s + 1` vertices.  When the hoop is
even, `m = 2k`, we have `h_C = h_{C_a} h_{C_b}` (v1 L311-313), and

`h_P h_j = (-1)^{k-1} h_Q h_C`.

For the root handle `Q = {j*}` (`s = 0`) one has `h_Q = χ`.  Combined with the wand pairing
`h_P h_j = h_{P*} h_{j_{s+1}}` of `PauliWandPairing` (case of an even hoop) the pair `(P, P*)`
contributes `2 (-1)^{k-1} h_Q h_C`.

## Proof

The list `(j_{s+1}, ..., j_ℓ, j)` is a cyclic enumeration `c₀, ..., c_{2k-1}` of the hoop.
Collecting the even positions `c₀, c₂, ...` to the left of the odd positions `c₁, c₃, ...`
crosses exactly one adjacent pair for each of the `k - 1` later even positions `c_{2i}`
(`i ≥ 1`), namely `c_{2i-1} c_{2i}`: the induced cycle gives `c_{2i}` the neighbours `c_{2i±1}`
only, and `c_{2i+1}` stays to its right.  Hence
`h_{c₀} ⋯ h_{c_{2k-1}} = (-1)^{k-1} (∏ even)(∏ odd)`
(`PauliFrustrationRepresentation.listOperator_range_double`).  The two products are the
independent products over the two proper colour classes of the hoop; any alternating labelling
`E` with the carrier of the hoop has these as its colour classes up to a swap
(`IndexedInducedHole.exists_colour_classes`), and `h_C` is symmetric under the swap
(`holeOperator_swapColors`, `labelingOperator_comm`).

Main declarations.

* `PauliFrustrationRepresentation.listOperator_range_double`: the sign lemma for a path-like
  list of `2k` terms, in which consecutive terms anticommute and non-consecutive terms commute,
  except possibly for the first term (which may anticommute with the last one);
* `IndexedInducedHole.listOperator_ofFn_vertex_eq`: for an indexed induced hole with `2k`
  vertices the ordered product `h_{c₀} ⋯ h_{c_{2k-1}}` is
  `(-1)^{k-1} h_{even} h_{odd}`;
* `IndexedInducedHole.exists_colour_classes`: the colour classes of any alternating labelling
  with the carrier of an indexed hole are its even and odd positions;
* `CliqueBubbleWand.hoopCard_eq_two_mul`: an alternating labelling `E` of `k` pairs with the
  carrier of the hoop forces the hoop to have `2k` vertices;
* `PauliCliqueHamiltonianRepresentation.holeOperator_eq_even_mul_odd`: `h_C` is the product of
  the independent products over the even and the odd positions of the hoop;
* `PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_holeOperator`: the identity
  `h_P h_j = (-1)^{k-1} h_{P_s} h_C`;
* `PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_rootOperator_mul_holeOperator`:
  the case of a root handle, `h_P h_j = (-1)^{k-1} χ h_C`;
* `PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_add_reverse_eq_two_mul`: the
  pair `(P, P*)` contributes `2 (-1)^{k-1} h_{P_s} h_C` (and `..._root` for a root handle).

No claw-freeness, no simpliciality of `K` and no full cyclic order of `E` are used: the
carrier of `E` is the hoop, which is an induced cycle, so the colour classes of `E` are
forced.  The hoop need not be assumed even: `hoopCard_eq_two_mul` shows that the existence of
`E` makes it so.

Hand checks: on the four-cycle (`k = 2`) the sign is `-1`, proved as
`CliqueBubbleWand.Example.wand_evenHoop_identity` (`h_P h_1 = -χ h_C`, the example of
`PauliWandPairing`, root handle); on the six-cycle (`k = 3`) the formula gives `+1`.

The statements are stated for `[DecidableEq V]` only (`Fintype V` is not needed).
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-! ### The sign lemma for the even/odd collection -/

/-- The even positions `c 0, c 2, ..., c (2k - 2)`. -/
def evenList (c : ℕ → V) (k : ℕ) : List V :=
  (List.range k).map fun i => c (2 * i)

/-- The odd positions `c 1, c 3, ..., c (2k - 1)`. -/
def oddList (c : ℕ → V) (k : ℕ) : List V :=
  (List.range k).map fun i => c (2 * i + 1)

theorem evenList_succ (c : ℕ → V) (k : ℕ) :
    evenList c (k + 1) = evenList c k ++ [c (2 * k)] := by
  simp [evenList, List.range_succ]

theorem oddList_succ (c : ℕ → V) (k : ℕ) :
    oddList c (k + 1) = oddList c k ++ [c (2 * k + 1)] := by
  simp [oddList, List.range_succ]

/-- A vertex that is adjacent to none of the odd positions `c 1, ..., c (2m - 1)` has no
neighbour in `oddList c m`. -/
theorem listNeighborCount_oddList_eq_zero (G : SimpleGraph V) (c : ℕ → V) (x : V) :
    ∀ m : ℕ, (∀ a, a < m → ¬ G.Adj x (c (2 * a + 1))) →
      listNeighborCount G x (oddList c m) = 0
  | 0, _ => by simp [oddList]
  | m + 1, h => by
    rw [oddList_succ, listNeighborCount_append,
      listNeighborCount_oddList_eq_zero G c x m (fun a ha => h a (by omega)),
      listNeighborCount_singleton_of_not_adj G (h m (by omega))]

/-- The term `c (2m + 2)` has exactly one neighbour (`c (2m + 1)`) among the odd positions
`c 1, ..., c (2m + 1)`. -/
theorem listNeighborCount_oddList_eq_one (G : SimpleGraph V) (c : ℕ → V) (m : ℕ)
    (hlast : G.Adj (c (2 * (m + 1))) (c (2 * m + 1)))
    (hsep : ∀ a, a < m → ¬ G.Adj (c (2 * (m + 1))) (c (2 * a + 1))) :
    listNeighborCount G (c (2 * (m + 1))) (oddList c (m + 1)) = 1 := by
  rw [oddList_succ, listNeighborCount_append,
    listNeighborCount_oddList_eq_zero G c _ m hsep,
    listNeighborCount_singleton_of_adj G hlast]

/-- **Collecting the even positions to the left** (v1 L1555-1576, the sign of the hoop
product).  Let `c 0, ..., c (2k + 1)` be terms such that consecutive terms are adjacent in
the frustration graph and a term `c i` with `i ≥ 1` is adjacent to a later `c j` only for
`j = i + 1`.  Then
`h_{c₀} ⋯ h_{c_{2k+1}} = (-1)^k (h_{c₀} h_{c₂} ⋯ h_{c_{2k}}) (h_{c₁} h_{c₃} ⋯ h_{c_{2k+1}})`:
each `c_{2i}` with `1 ≤ i ≤ k` crosses exactly one adjacent term, `c_{2i-1}`. -/
theorem listOperator_range_double (H : G.PauliFrustrationRepresentation A) (c : ℕ → V) :
    ∀ k : ℕ,
    (∀ i, i + 1 < 2 * (k + 1) → G.Adj (c i) (c (i + 1))) →
    (∀ i j, 1 ≤ i → i < j → j < 2 * (k + 1) → G.Adj (c i) (c j) → j = i + 1) →
    H.listOperator ((List.range (2 * (k + 1))).map c) =
      (-1 : A) ^ k *
        (H.listOperator (evenList c (k + 1)) * H.listOperator (oddList c (k + 1)))
  | 0, _, _ => by
    simp [evenList, oddList, listOperator, List.range_succ]
  | k + 1, hcons, hsep => by
    have ih := listOperator_range_double H c k
      (fun i hi => hcons i (by omega))
      (fun i j h1 h2 h3 => hsep i j h1 h2 (by omega))
    have hlast : G.Adj (c (2 * (k + 1))) (c (2 * k + 1)) := by
      have := hcons (2 * k + 1) (by omega)
      have e : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [e] at this
      exact this.symm
    have hnot : ∀ a, a < k → ¬ G.Adj (c (2 * (k + 1))) (c (2 * a + 1)) := by
      intro a ha hadj
      have := hsep (2 * a + 1) (2 * (k + 1)) (by omega) (by omega) (by omega) hadj.symm
      omega
    have hcount := listNeighborCount_oddList_eq_one G c k hlast hnot
    have hcomm := H.term_mul_listOperator (c (2 * (k + 1))) (oddList c (k + 1))
    rw [hcount, pow_one, neg_one_mul] at hcomm
    have e : 2 * (k + 1 + 1) = 2 * (k + 1) + 1 + 1 := by omega
    have eT : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [e, List.range_succ, List.range_succ, List.map_append, List.map_append,
      listOperator_append, listOperator_append, ih, evenList_succ (k := k + 1),
      oddList_succ (k := k + 1), listOperator_append, listOperator_append]
    have h1 : ∀ x, H.listOperator [x] = H.term x := by
      intro x
      simp [listOperator]
    simp only [List.map_cons, List.map_nil, h1]
    have hOT : H.listOperator (oddList c (k + 1)) * H.term (c (2 * (k + 1))) =
        -(H.term (c (2 * (k + 1))) * H.listOperator (oddList c (k + 1))) := by
      rw [hcomm]; simp
    set E := H.listOperator (evenList c (k + 1))
    set O := H.listOperator (oddList c (k + 1))
    set T := H.term (c (2 * (k + 1)))
    set U := H.term (c (2 * (k + 1) + 1))
    have hre : (-1 : A) ^ k * (E * O) * T * U = (-1 : A) ^ k * (E * (O * T) * U) := by
      simp only [mul_assoc]
    rw [hre, hOT]
    simp only [mul_assoc, mul_neg, neg_mul, pow_succ, mul_one]

/-- The ordered product over a duplicate-free list of pairwise non-adjacent vertices is the
canonical independent product of the underlying finset. -/
theorem listOperator_eq_independentProduct_toFinset [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {l : List V} (hnd : l.Nodup)
    (hind : G.IsIndepSet (l.toFinset : Set V)) :
    H.listOperator l = H.independentProduct l.toFinset := by
  rw [H.independentProduct_eq_noncommProd hind, Finset.noncommProd_toFinset _ _ _ hnd]
  rfl

/-- Transport of ordered products along `some`: the product of the terms `h_{some v}` over a
list of original vertices is the product for the restricted representation. -/
theorem listOperator_map_some {K : Set V}
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) (l : List V) :
    Hp.listOperator (l.map some) = Hp.restrictSome.listOperator l := by
  unfold listOperator
  rw [List.map_map]
  rfl

end PauliFrustrationRepresentation

/-! ### Indexed holes: even and odd positions -/

namespace IndexedInducedHole

variable {G : SimpleGraph V}

/-- The vertices of an indexed hole as a function on `ℕ` (junk values beyond the cardinality). -/
def vertexNat (C : IndexedInducedHole G) (i : ℕ) : V :=
  if h : i < C.card then C.vertex ⟨i, h⟩
  else C.vertex ⟨0, by have := C.four_le_card; omega⟩

theorem vertexNat_of_lt (C : IndexedInducedHole G) {i : ℕ} (h : i < C.card) :
    C.vertexNat i = C.vertex ⟨i, h⟩ :=
  dif_pos h

theorem ofFn_vertex_eq_map_range (C : IndexedInducedHole G) :
    List.ofFn C.vertex = (List.range C.card).map C.vertexNat := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < C.card := by simpa using h1
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rw [C.vertexNat_of_lt hi]

theorem adj_vertexNat_iff (C : IndexedInducedHole G) {i j : ℕ} (hi : i < C.card)
    (hj : j < C.card) :
    G.Adj (C.vertexNat i) (C.vertexNat j) ↔
      (i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j + 1 = C.card) ∨ (j = 0 ∧ i + 1 = C.card)) := by
  rw [C.vertexNat_of_lt hi, C.vertexNat_of_lt hj, C.adj_iff]
  rfl

theorem vertexNat_injOn (C : IndexedInducedHole G) {i j : ℕ} (hi : i < C.card)
    (hj : j < C.card) (h : C.vertexNat i = C.vertexNat j) : i = j := by
  rw [C.vertexNat_of_lt hi, C.vertexNat_of_lt hj] at h
  exact congrArg Fin.val (C.injective h)

/-- The vertices at even positions `c₀, c₂, ...` of an indexed hole. -/
def evenVertices [DecidableEq V] (C : IndexedInducedHole G) : Finset V :=
  (Finset.univ.filter fun q : Fin C.card => q.val % 2 = 0).image C.vertex

/-- The vertices at odd positions `c₁, c₃, ...` of an indexed hole. -/
def oddVertices [DecidableEq V] (C : IndexedInducedHole G) : Finset V :=
  (Finset.univ.filter fun q : Fin C.card => ¬ q.val % 2 = 0).image C.vertex

theorem mem_evenVertices_iff [DecidableEq V] (C : IndexedInducedHole G) (x : V) :
    x ∈ C.evenVertices ↔ ∃ q : Fin C.card, q.val % 2 = 0 ∧ C.vertex q = x := by
  simp [evenVertices]

theorem mem_oddVertices_iff [DecidableEq V] (C : IndexedInducedHole G) (x : V) :
    x ∈ C.oddVertices ↔ ∃ q : Fin C.card, ¬ q.val % 2 = 0 ∧ C.vertex q = x := by
  simp [oddVertices]

theorem card_evenVertices_add_card_oddVertices [DecidableEq V] (C : IndexedInducedHole G) :
    C.evenVertices.card + C.oddVertices.card = C.card := by
  unfold evenVertices oddVertices
  rw [Finset.card_image_of_injective _ C.injective,
    Finset.card_image_of_injective _ C.injective,
    Finset.card_filter_add_card_filter_not]
  simp

/-- In an indexed hole with an even number of vertices, two positions of the same parity are
not adjacent. -/
theorem isIndepSet_evenVertices [DecidableEq V] (C : IndexedInducedHole G) {k : ℕ}
    (hk : C.card = 2 * k) : G.IsIndepSet (C.evenVertices : Set V) := by
  intro x hx y hy _ hadj
  rw [Finset.mem_coe, mem_evenVertices_iff] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  rw [C.adj_iff] at hadj
  unfold CyclicAdjacent at hadj
  omega

theorem isIndepSet_oddVertices [DecidableEq V] (C : IndexedInducedHole G) {k : ℕ}
    (hk : C.card = 2 * k) : G.IsIndepSet (C.oddVertices : Set V) := by
  intro x hx y hy _ hadj
  rw [Finset.mem_coe, mem_oddVertices_iff] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  rw [C.adj_iff] at hadj
  unfold CyclicAdjacent at hadj
  omega

/-- **The ordered product around an even hole** (v1 L1555-1576): for an indexed induced hole
`c₀, ..., c_{2k-1}` with `2k` vertices,
`h_{c₀} h_{c₁} ⋯ h_{c_{2k-1}} = (-1)^{k-1} h_{even} h_{odd}`,
where `h_{even}` and `h_{odd}` are the independent products over the even and odd positions. -/
theorem listOperator_ofFn_vertex_eq [DecidableEq V] {A : Type w} [Ring A]
    (H : G.PauliFrustrationRepresentation A) (C : IndexedInducedHole G) {k : ℕ}
    (hk : C.card = 2 * k) :
    H.listOperator (List.ofFn C.vertex) =
      (-1 : A) ^ (k - 1) *
        (H.independentProduct C.evenVertices * H.independentProduct C.oddVertices) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := C.four_le_card; omega⟩
  have hcons : ∀ i, i + 1 < 2 * (m + 1) → G.Adj (C.vertexNat i) (C.vertexNat (i + 1)) := by
    intro i hi
    rw [C.adj_vertexNat_iff (by omega) (by omega)]
    omega
  have hsep : ∀ i j, 1 ≤ i → i < j → j < 2 * (m + 1) →
      G.Adj (C.vertexNat i) (C.vertexNat j) → j = i + 1 := by
    intro i j h1 h2 h3 hadj
    rw [C.adj_vertexNat_iff (by omega) (by omega)] at hadj
    omega
  have key := H.listOperator_range_double C.vertexNat m hcons hsep
  rw [C.ofFn_vertex_eq_map_range, hk, key, Nat.add_sub_cancel]
  have hEven : (PauliFrustrationRepresentation.evenList C.vertexNat (m + 1)).toFinset =
      C.evenVertices := by
    ext x
    rw [List.mem_toFinset, mem_evenVertices_iff]
    simp only [PauliFrustrationRepresentation.evenList, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨2 * i, by omega⟩, by simp, (C.vertexNat_of_lt (by omega)).symm⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.val / 2, by have := q.isLt; omega, ?_⟩
      have e : 2 * (q.val / 2) = q.val := by omega
      rw [e, C.vertexNat_of_lt q.isLt]
  have hOdd : (PauliFrustrationRepresentation.oddList C.vertexNat (m + 1)).toFinset =
      C.oddVertices := by
    ext x
    rw [List.mem_toFinset, mem_oddVertices_iff]
    simp only [PauliFrustrationRepresentation.oddList, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨2 * i + 1, by omega⟩, by simp, (C.vertexNat_of_lt (by omega)).symm⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.val / 2, by have := q.isLt; omega, ?_⟩
      have e : 2 * (q.val / 2) + 1 = q.val := by omega
      rw [e, C.vertexNat_of_lt q.isLt]
  have hndE : (PauliFrustrationRepresentation.evenList C.vertexNat (m + 1)).Nodup := by
    apply List.Nodup.map_on _ (List.nodup_range)
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    have := C.vertexNat_injOn (by omega) (by omega) hxy
    omega
  have hndO : (PauliFrustrationRepresentation.oddList C.vertexNat (m + 1)).Nodup := by
    apply List.Nodup.map_on _ (List.nodup_range)
    intro x hx y hy hxy
    rw [List.mem_range] at hx hy
    have := C.vertexNat_injOn (by omega) (by omega) hxy
    omega
  have hiE := C.isIndepSet_evenVertices hk
  have hiO := C.isIndepSet_oddVertices hk
  rw [← hEven] at hiE ⊢
  rw [← hOdd] at hiO ⊢
  rw [← H.listOperator_eq_independentProduct_toFinset hndE hiE,
    ← H.listOperator_eq_independentProduct_toFinset hndO hiO]

/-! ### Colour classes of an alternating labelling of a hole -/

/-- A proper two-colouring of the vertex set of an indexed hole, with the first vertex in the
first class, colours the even positions with the first class and the odd positions with the
second class: consecutive vertices are adjacent, hence of different colour. -/
theorem colour_classes_aux (C : IndexedInducedHole G) (A B : Set V)
    (hcar : A ∪ B = Set.range C.vertex) (hAB : Disjoint A B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (h0 : C.vertex ⟨0, by have := C.four_le_card; omega⟩ ∈ A) :
    (∀ x, x ∈ A ↔ ∃ q : Fin C.card, q.val % 2 = 0 ∧ C.vertex q = x) ∧
    (∀ x, x ∈ B ↔ ∃ q : Fin C.card, ¬ q.val % 2 = 0 ∧ C.vertex q = x) := by
  have hmem : ∀ q : Fin C.card, C.vertex q ∈ A ∪ B := fun q => hcar ▸ ⟨q, rfl⟩
  have hstep : ∀ n (hn : n < C.card),
      (n % 2 = 0 → C.vertex ⟨n, hn⟩ ∈ A) ∧ (¬ n % 2 = 0 → C.vertex ⟨n, hn⟩ ∈ B) := by
    intro n
    induction n with
    | zero => intro hn; exact ⟨fun _ => h0, fun h => absurd rfl h⟩
    | succ n ih =>
      intro hn
      obtain ⟨iha, ihb⟩ := ih (by omega)
      have hadj : G.Adj (C.vertex ⟨n, by omega⟩) (C.vertex ⟨n + 1, hn⟩) :=
        (C.adj_iff _ _).2 (Or.inl rfl)
      have hc := hmem ⟨n + 1, hn⟩
      by_cases hpar : n % 2 = 0
      · have hx := iha hpar
        rcases hc with hc | hc
        · exact absurd hadj (hA _ hx _ hc)
        · exact ⟨fun h => by omega, fun _ => hc⟩
      · have hx := ihb hpar
        rcases hc with hc | hc
        · exact ⟨fun _ => hc, fun h => by omega⟩
        · exact absurd hadj (hB _ hx _ hc)
  have hdisj := Set.disjoint_left.1 hAB
  constructor
  · intro x
    constructor
    · intro hx
      have hxr : x ∈ Set.range C.vertex := hcar ▸ Or.inl hx
      obtain ⟨q, rfl⟩ := hxr
      refine ⟨q, ?_, rfl⟩
      by_contra hne
      exact hdisj hx ((hstep q.val q.isLt).2 hne)
    · rintro ⟨q, hq, rfl⟩
      exact (hstep q.val q.isLt).1 hq
  · intro x
    constructor
    · intro hx
      have hxr : x ∈ Set.range C.vertex := hcar ▸ Or.inr hx
      obtain ⟨q, rfl⟩ := hxr
      refine ⟨q, ?_, rfl⟩
      intro heq
      exact hdisj ((hstep q.val q.isLt).1 heq) hx
    · rintro ⟨q, hq, rfl⟩
      exact (hstep q.val q.isLt).2 hq

/-- **The colour classes of an alternating labelling `E` whose carrier is an indexed hole `C`
are the even and odd positions of `C`**, in one of the two orders.  (The carrier of `E` is
`2`-regular and bipartite with classes `a`, `b`; on a hole, which is connected, the proper
`2`-colouring is determined by the colour of one vertex.) -/
theorem exists_colour_classes [DecidableEq V] (C : IndexedInducedHole G) {k : ℕ}
    (E : G.EvenHoleLabeling k) (hcar : E.carrier = Set.range C.vertex) :
    (Finset.univ.image E.a = C.evenVertices ∧ Finset.univ.image E.b = C.oddVertices) ∨
    (Finset.univ.image E.a = C.oddVertices ∧ Finset.univ.image E.b = C.evenVertices) := by
  have hdis : Disjoint (Set.range E.a) (Set.range E.b) :=
    Set.disjoint_left.2 fun x ⟨i, hi⟩ ⟨j, hj⟩ => E.color_disjoint i j (hi.trans hj.symm)
  have hA : ∀ x ∈ Set.range E.a, ∀ y ∈ Set.range E.a, ¬ G.Adj x y := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact E.adj_aa i j
  have hB : ∀ x ∈ Set.range E.b, ∀ y ∈ Set.range E.b, ¬ G.Adj x y := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact E.adj_bb i j
  have hcar' : Set.range E.a ∪ Set.range E.b = Set.range C.vertex := hcar
  have h0 : C.vertex ⟨0, by have := C.four_le_card; omega⟩ ∈
      Set.range E.a ∪ Set.range E.b := hcar' ▸ ⟨_, rfl⟩
  rcases h0 with h0 | h0
  · obtain ⟨h1, h2⟩ := C.colour_classes_aux _ _ hcar' hdis hA hB h0
    left
    constructor
    · ext x
      rw [Finset.mem_image, mem_evenVertices_iff, ← h1 x]
      simp
    · ext x
      rw [Finset.mem_image, mem_oddVertices_iff, ← h2 x]
      simp
  · obtain ⟨h1, h2⟩ := C.colour_classes_aux _ _ (by rw [Set.union_comm]; exact hcar')
      hdis.symm hB hA h0
    right
    constructor
    · ext x
      rw [Finset.mem_image, mem_oddVertices_iff, ← h2 x]
      simp
    · ext x
      rw [Finset.mem_image, mem_evenVertices_iff, ← h1 x]
      simp

/-- If an alternating labelling of `k` pairs has the carrier of an indexed hole `C`, then `C`
has `2k` vertices. -/
theorem card_eq_two_mul_of_labeling [DecidableEq V] (C : IndexedInducedHole G) {k : ℕ}
    (E : G.EvenHoleLabeling k) (hcar : E.carrier = Set.range C.vertex) :
    C.card = 2 * k := by
  have hsum := C.card_evenVertices_add_card_oddVertices
  have ha : (Finset.univ.image E.a).card = k := by
    rw [Finset.card_image_of_injective _ E.a_injective]
    simp
  have hb : (Finset.univ.image E.b).card = k := by
    rw [Finset.card_image_of_injective _ E.b_injective]
    simp
  rcases C.exists_colour_classes E hcar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at ha
    rw [h2] at hb
    omega
  · rw [h1] at ha
    rw [h2] at hb
    omega

end IndexedInducedHole

/-! ### The vertex lists of a wand -/

namespace CliqueBubbleWand

variable {G : SimpleGraph V} {K : Set V} {P : CliqueRootedInducedPath G K}

/-- The vertex list of the handle `P_s` is the prefix of the vertex list of `P`. -/
theorem ofFn_handle_vertex (w : CliqueBubbleWand G K P) :
    List.ofFn w.handle.path.vertex = (List.ofFn P.path.vertex).take (w.split.val + 1) := by
  have hgap := w.gap
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, handle_card]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
    rfl

/-- The hoop list `(j_{s+1}, ..., j_ℓ, j)`, read in `G*`, is the vertex list of the hoop hole
`w.hoopHole`, mapped along `some`. -/
theorem drop_append_bubble_eq_map_ofFn (w : CliqueBubbleWand G K P) :
    (List.ofFn P.path.vertex).drop (w.split.val + 1) ++ [some w.bubble] =
      (List.ofFn w.hoopHole.vertex).map some := by
  have hhole : List.ofFn w.hoopHole.vertex = List.ofFn w.hoopPath.vertex ++ [w.bubble] := by
    have h := List.ofFn_succ' (n := w.hoopPath.card)
      (w.hoopPath.closeToHole w.hoopPath_endpointClosureData).vertex
    simp only [IndexedInducedPath.closeToHole_vertex_castSucc,
      IndexedInducedPath.closeToHole_vertex_last] at h
    unfold hoopHole
    refine h.trans ?_
    simp
  rw [w.drop_split_succ_eq_ofFn, hhole, List.map_append, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext q
  exact w.path_vertex_hoopIndex q

/-- **The hoop has `2k` vertices** if `E` is an alternating labelling with `k` pairs whose
carrier is the hoop carrier. -/
theorem hoopCard_eq_two_mul [DecidableEq V] (w : CliqueBubbleWand G K P) {k : ℕ}
    (E : G.EvenHoleLabeling k) (hE : E.carrier = w.hoopCarrier) :
    w.hoopCard = 2 * k := by
  have h := w.hoopHole.card_eq_two_mul_of_labeling E (hE.trans w.range_hoopHole.symm)
  rwa [w.hoopHole_card] at h

end CliqueBubbleWand

/-! ### The even-hoop identity -/

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- `h_C` for the alternating labelling `E` of the hoop is the product of the independent
products over the even and the odd positions of the hoop hole, for the restricted
representation. -/
theorem holeOperator_eq_even_mul_odd [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {P : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) {k : ℕ} (E : G.EvenHoleLabeling k)
    (hE : E.carrier = w.hoopCarrier) :
    H.holeOperator E =
      H.operator.restrictSome.independentProduct w.hoopHole.evenVertices *
        H.operator.restrictSome.independentProduct w.hoopHole.oddVertices := by
  have hcar : E.carrier = Set.range w.hoopHole.vertex := hE.trans w.range_hoopHole.symm
  rw [holeOperator_eq_labelingOperator]
  unfold PauliFrustrationRepresentation.labelingOperator
  rcases w.hoopHole.exists_colour_classes E hcar with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · have hcomm := H.operator.restrictSome.labelingOperator_comm E
    rw [h1, h2] at hcomm
    rw [h1, h2]
    exact hcomm

/-- **The even-hoop operator identity** (v1 L1555-1576; the sign is not displayed in v1).
Let `w` be a bubble wand on `P` with handle `Q = P_s` (the root path `{j*}` is allowed) and
bubble `j`, and let `E` be an alternating labelling of `k` pairs whose carrier is the hoop
`C = {j_{s+1}, ..., j_ℓ, j}` (so the hoop is an even hole with `2k` vertices,
`CliqueBubbleWand.hoopCard_eq_two_mul`).  Then, with `h_C = h_{C_a} h_{C_b}`,

`h_P h_j = (-1)^{k-1} h_Q h_C`.

The hoop list `(j_{s+1}, ..., j_ℓ, j)` is a cyclic enumeration of `C`; collecting the odd and the
even positions into `h_{C_a}` and `h_{C_b}` crosses one adjacent pair for each of the `k - 1`
later even positions.  Hand checks: `C₄` gives `-1`, `C₆` gives `+1`.

The statement needs no claw-freeness, no simpliciality of `K` and no full cyclic order of `E`:
the carrier is connected, so it determines the colour classes up to a swap, and `h_C` does not
depend on the swap. -/
theorem pathOperator_mul_bubble_eq_holeOperator [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {P : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) {k : ℕ} (E : G.EvenHoleLabeling k)
    (hE : E.carrier = w.hoopCarrier) :
    H.pathOperator P * H.operator.term (some w.bubble) =
      (-1 : A) ^ (k - 1) * (H.pathOperator w.handle * H.holeOperator E) := by
  have hcar : E.carrier = Set.range w.hoopHole.vertex := hE.trans w.range_hoopHole.symm
  have hcard : w.hoopHole.card = 2 * k := w.hoopHole.card_eq_two_mul_of_labeling E hcar
  have hlist := w.hoopHole.listOperator_ofFn_vertex_eq H.operator.restrictSome hcard
  have hP : H.pathOperator P =
      H.operator.listOperator ((List.ofFn P.path.vertex).take (w.split.val + 1)) *
        H.operator.listOperator ((List.ofFn P.path.vertex).drop (w.split.val + 1)) := by
    unfold pathOperator PauliFrustrationRepresentation.pathOperator
    rw [← PauliFrustrationRepresentation.listOperator_append, List.take_append_drop]
  have hhandle : H.pathOperator w.handle =
      H.operator.listOperator ((List.ofFn P.path.vertex).take (w.split.val + 1)) := by
    unfold pathOperator PauliFrustrationRepresentation.pathOperator
    rw [w.ofFn_handle_vertex]
  have hdrop : H.operator.listOperator ((List.ofFn P.path.vertex).drop (w.split.val + 1)) *
      H.operator.term (some w.bubble) =
        H.operator.listOperator ((List.ofFn w.hoopHole.vertex).map some) := by
    rw [← w.drop_append_bubble_eq_map_ofFn, PauliFrustrationRepresentation.listOperator_append]
    simp [PauliFrustrationRepresentation.listOperator]
  rw [hP, mul_assoc, hdrop, PauliFrustrationRepresentation.listOperator_map_some, hlist,
    hhandle, H.holeOperator_eq_even_mul_odd w E hE]
  exact ((Commute.neg_one_left _).pow_left (k - 1)).symm.left_comm _

/-- The root-handle case (`s = 0`, `Q = {j*}`, `h_Q = χ`): `h_P h_j = (-1)^{k-1} χ h_C`. -/
theorem pathOperator_mul_bubble_eq_rootOperator_mul_holeOperator [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {P : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) (hs : w.split.val = 0) {k : ℕ} (E : G.EvenHoleLabeling k)
    (hE : E.carrier = w.hoopCarrier) :
    H.pathOperator P * H.operator.term (some w.bubble) =
      (-1 : A) ^ (k - 1) * (H.rootOperator * H.holeOperator E) := by
  rw [H.pathOperator_mul_bubble_eq_holeOperator w E hE,
    (w.handle_eq_cliqueRootPath_iff).2 hs, H.pathOperator_cliqueRootPath]

/-- **The pair `(P, P*)` contributes `2 (-1)^{k-1} h_Q h_C`** (v1 L1576, "the contributions
from even holes add"): combining the even-hoop identity with the wand pairing
`h_P h_j = h_{P*} h_{j_{s+1}}` for even hoops (`pathOperator_mul_bubble_eq_reverse_of_even`). -/
theorem pathOperator_mul_bubble_add_reverse_eq_two_mul [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {P : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) {k : ℕ} (E : G.EvenHoleLabeling k)
    (hE : E.carrier = w.hoopCarrier) :
    H.pathOperator P * H.operator.term (some w.bubble) +
        H.pathOperator w.reverse * H.operator.term (some w.reverseBubble) =
      2 * ((-1 : A) ^ (k - 1) * (H.pathOperator w.handle * H.holeOperator E)) := by
  have heven : Even w.hoopCard := ⟨k, by rw [w.hoopCard_eq_two_mul E hE]; ring⟩
  rw [← H.pathOperator_mul_bubble_eq_reverse_of_even w heven,
    H.pathOperator_mul_bubble_eq_holeOperator w E hE, two_mul]

/-- The pair `(P, P*)` for a root handle contributes `2 (-1)^{k-1} χ h_C`. -/
theorem pathOperator_mul_bubble_add_reverse_eq_two_mul_root [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {P : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) (hs : w.split.val = 0) {k : ℕ} (E : G.EvenHoleLabeling k)
    (hE : E.carrier = w.hoopCarrier) :
    H.pathOperator P * H.operator.term (some w.bubble) +
        H.pathOperator w.reverse * H.operator.term (some w.reverseBubble) =
      2 * ((-1 : A) ^ (k - 1) * (H.rootOperator * H.holeOperator E)) := by
  rw [H.pathOperator_mul_bubble_add_reverse_eq_two_mul w E hE,
    (w.handle_eq_cliqueRootPath_iff).2 hs, H.pathOperator_cliqueRootPath]

end PauliCliqueHamiltonianRepresentation

/-! ### An example: the four-cycle -/

namespace CliqueBubbleWand

namespace Example

/-- Hand check on `C₄` (`P = (j*, 0, 3, 2)`, bubble `1`, root handle, hoop `{0, 3, 2, 1}`
with `k = 2`): `h_P h_1 = -χ h_C` in every clique-rooted Pauli representation. -/
theorem wand_evenHoop_identity {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    (H : fourCycle.PauliCliqueHamiltonianRepresentation edgeClique R A) :
    ∃ E : fourCycle.EvenHoleLabeling 2, E.carrier = wand.hoopCarrier ∧
      H.pathOperator path * H.operator.term (some 1) = -(H.rootOperator * H.holeOperator E) := by
  obtain ⟨k, E, hE⟩ := wand.hoopHole.exists_evenHoleLabeling
    (by rw [wand.hoopHole_card, wand_hoopCard]; decide)
  have hE' : E.carrier = wand.hoopCarrier := hE.trans wand.range_hoopHole
  have hk : k = 2 := by
    have := wand.hoopCard_eq_two_mul E hE'
    rw [wand_hoopCard] at this
    omega
  subst hk
  refine ⟨E, hE', ?_⟩
  have h := H.pathOperator_mul_bubble_eq_rootOperator_mul_holeOperator wand rfl E hE'
  rw [show (-1 : A) ^ (2 - 1) = -1 by norm_num, neg_one_mul] at h
  exact h

end Example

end CliqueBubbleWand

end SimpleGraph
