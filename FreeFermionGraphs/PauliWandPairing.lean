import FreeFermionGraphs.CliqueBubbleWandReverse
import Mathlib.Algebra.BigOperators.Fin

/-!
# List reversal and the wand pairing `h_P h_j = (-1)^m h_{P*} h_{j_{s+1}}`

Operator content of the closing sentence of case (b.iv) in the proof of
Theorem 3 (arXiv 2305.15625v1, L1576: "the contributions from odd holes
cancel, and the contributions from even holes add") together with the
definition of the reversed path `P*` (L1520).

Let `P = (j₀ = j*, j₁, ..., j_ℓ)` be a rooted induced path of `G*`, and let
`j` be the bubble of a wand on `P` with split index `s`
(`Γ_P(j) = {j_s, j_{s+1}, j_ℓ}`, `0 ≤ s < ℓ - 2`).  The hoop
`C = {j_{s+1}, ..., j_ℓ, j}` has `m = ℓ - s + 1` vertices (an induced `m`-cycle)
and `P* = (j₀, ..., j_s, j, j_ℓ, ..., j_{s+2})` traverses it in the opposite
direction.  Then

`h_P h_j = (-1)^m h_{P*} h_{j_{s+1}}`,

so the two terms are equal when the hoop is even and cancel when it is odd.

Main declarations.

* `PauliFrustrationRepresentation.adjacentPairCount G l`: the number of
  adjacent pairs `i < j` of a list `l`, i.e. the number of frustration edges
  inside the product `h_{l₀} h_{l₁} ⋯`;
* `PauliFrustrationRepresentation.listOperator_reverse`: reversing a product of
  terms multiplies it by `(-1)^(adjacentPairCount G l)`;
* `PauliFrustrationRepresentation.listOperator_append_mul_term_eq_reverse`: the
  list form of the pairing, `h_{pre·x·T} h_b = (-1)^c h_{pre·b·T^rev} h_x` with
  `c` the number of adjacent pairs of `x · T · b`;
* `CliqueBubbleWand.adjacentPairCount_hoop`: the hoop list has exactly
  `hoopCard` adjacent pairs, since it is an induced cycle (`m - 2` path edges
  and the two edges at the bubble);
* `CliqueBubbleWand.pathOperator_mul_term_bubble_eq_reverse`: the pairing for
  any representation of the frustration graph `G*`;
* `PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_reverse`,
  `PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_reverse_of_even`,
  `PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_add_reverse_eq_zero`:
  the pairing in the clique-rooted Hamiltonian representation, with the even
  (terms agree) and odd (terms cancel) consequences.

The statements need no claw-freeness and no simpliciality of `K`; only the
induced hoop cycle is used.  The terms are those of the frustration graph
`G*`: the bubble `j` is the original term `H.operator.term (some j)`, and
`j_{s+1}` (`CliqueBubbleWand.reverseBubble`) is an original vertex of `P`.

Indices: `P.path.card = ℓ + 1`, the split index is `w.split.val = s` and the
hoop size is `w.hoopCard = P.path.card - w.split.val = ℓ - s + 1`.

Hand check on the four-cycle (`Example.wand_pairing`): for `P = (j*, 0, 3, 2)`
with bubble `1` one has `m = 4`, `P* = (j*, 1, 2, 3)` and
`h_P h_1 = h_{P*} h_0`, in agreement with `h_P h_j = -χ h_C = h_{P*} h_{j₁}`.
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- The number of adjacent pairs `i < j` of a list: the pairs of listed
vertices joined by an edge of `G`, i.e. the number of frustration edges inside
the ordered product `h_{l₀} h_{l₁} ⋯`.  The definition is noncomputable so
public sign theorems do not carry a choice of decidable adjacency as
mathematical data. -/
noncomputable def adjacentPairCount (G : SimpleGraph V) : List V → ℕ
  | [] => 0
  | v :: l => listNeighborCount G v l + adjacentPairCount G l

@[simp]
theorem adjacentPairCount_nil (G : SimpleGraph V) : adjacentPairCount G [] = 0 :=
  rfl

@[simp]
theorem adjacentPairCount_cons (G : SimpleGraph V) (v : V) (l : List V) :
    adjacentPairCount G (v :: l) =
      listNeighborCount G v l + adjacentPairCount G l :=
  rfl

/-! ### Neighbour counts of concatenations -/

theorem listNeighborCount_append (G : SimpleGraph V) (j : V) (l₁ l₂ : List V) :
    listNeighborCount G j (l₁ ++ l₂) =
      listNeighborCount G j l₁ + listNeighborCount G j l₂ := by
  classical
  simp [listNeighborCount, List.countP_append]

theorem listNeighborCount_singleton_of_adj (G : SimpleGraph V) {j x : V}
    (h : G.Adj j x) :
    listNeighborCount G j [x] = 1 := by
  simp [listNeighborCount_cons_of_adj G [] h]

theorem listNeighborCount_singleton_of_not_adj (G : SimpleGraph V) {j x : V}
    (h : ¬ G.Adj j x) :
    listNeighborCount G j [x] = 0 := by
  simp [listNeighborCount_cons_of_not_adj G [] h]

/-- Appending one vertex adds the number of its neighbours in the list. -/
theorem adjacentPairCount_append_singleton (G : SimpleGraph V) (l : List V)
    (x : V) :
    adjacentPairCount G (l ++ [x]) =
      adjacentPairCount G l + listNeighborCount G x l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : G.Adj a x
    · have h' : G.Adj x a := h.symm
      rw [List.cons_append, adjacentPairCount_cons, listNeighborCount_append, ih,
        listNeighborCount_singleton_of_adj G h, adjacentPairCount_cons,
        listNeighborCount_cons_of_adj G l h']
      omega
    · have h' : ¬ G.Adj x a := fun hh => h hh.symm
      rw [List.cons_append, adjacentPairCount_cons, listNeighborCount_append, ih,
        listNeighborCount_singleton_of_not_adj G h, adjacentPairCount_cons,
        listNeighborCount_cons_of_not_adj G l h']
      omega

/-! ### Counting along `List.ofFn` -/

/-- The neighbour count along `List.ofFn f` is the sum of the adjacency
indicators over the index set. -/
theorem listNeighborCount_ofFn (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) :
    ∀ (k : ℕ) (f : Fin k → V),
      listNeighborCount G x (List.ofFn f) =
        ∑ i : Fin k, if G.Adj x (f i) then 1 else 0
  | 0, f => by simp
  | k + 1, f => by
    rw [List.ofFn_succ, Fin.sum_univ_succ,
      ← listNeighborCount_ofFn G x k (fun i => f i.succ)]
    by_cases h : G.Adj x (f 0)
    · rw [listNeighborCount_cons_of_adj G _ h, if_pos h]
      omega
    · rw [listNeighborCount_cons_of_not_adj G _ h, if_neg h]
      omega

/-- A path with `k` vertices, listed in order, has `k - 1` adjacent pairs. -/
theorem adjacentPairCount_ofFn_of_adj_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ (k : ℕ) (f : Fin k → V),
      (∀ i j, G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) →
      adjacentPairCount G (List.ofFn f) = k - 1
  | 0, f, _ => by simp
  | k + 1, f, h => by
    rw [List.ofFn_succ, adjacentPairCount_cons,
      adjacentPairCount_ofFn_of_adj_iff G k (fun i => f i.succ) (fun i j => by
        rw [h]; simp only [Fin.val_succ]; omega),
      listNeighborCount_ofFn]
    cases k with
    | zero => simp
    | succ k' =>
      rw [Fin.sum_univ_succ]
      have h0 : G.Adj (f 0) (f (Fin.succ 0)) := (h _ _).2 (Or.inl rfl)
      rw [if_pos h0]
      have : ∀ i : Fin k', ¬ G.Adj (f 0) (f (Fin.succ (Fin.succ i))) := by
        intro i hi
        rw [h] at hi
        simp only [Fin.val_zero, Fin.val_succ] at hi
        omega
      simp [this]
      omega

/-- A vertex adjacent exactly to the two endpoints of a listed path with
`k ≥ 2` vertices has two neighbours in the list. -/
theorem listNeighborCount_ofFn_endpoints (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k) (f : Fin k → V) (x : V)
    (h : ∀ q, G.Adj x (f q) ↔ q.val = 0 ∨ q.val + 1 = k) :
    listNeighborCount G x (List.ofFn f) = 2 := by
  rw [listNeighborCount_ofFn]
  simp only [h]
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun q : Fin k => q.val = 0 ∨ q.val + 1 = k) =
      {⟨0, by omega⟩, ⟨k - 1, by omega⟩} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [this, Finset.card_pair]
  · simp
  · intro hh
    have := congrArg Fin.val hh
    simp at this
    omega

/-! ### Reversal of an ordered product of terms -/

/-- Reversing the order of an ordered product of Pauli terms multiplies it by
`(-1)` to the number of adjacent pairs of the list: every adjacent pair
anticommutes once when its two factors are swapped, every non-adjacent pair
commutes. -/
theorem listOperator_reverse (H : G.PauliFrustrationRepresentation A)
    (l : List V) :
    H.listOperator l.reverse =
      (-1 : A) ^ adjacentPairCount G l * H.listOperator l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 : H.listOperator [a] = H.term a := by simp [listOperator]
    have h2 : H.listOperator (a :: l) = H.term a * H.listOperator l :=
      listOperator_cons H a l
    have key := H.term_mul_listOperator a l
    rw [List.reverse_cons, listOperator_append, ih, adjacentPairCount_cons, h1, h2, key]
    rcases neg_one_pow_eq_or A (listNeighborCount G a l) with h | h <;>
    rcases neg_one_pow_eq_or A (adjacentPairCount G l) with h' | h' <;>
    simp [pow_add, h, h']

/-- List form of the wand pairing.  If the term `h_b` is multiplied on the
right of `h_{pre} h_x h_T`, the hoop `x · T · b` can be traversed in the
opposite direction: `h_{pre·x·T} h_b = (-1)^c h_{pre·b·T^rev} h_x`, where `c` is
the number of adjacent pairs of the list `x · T · b`. -/
theorem listOperator_append_mul_term_eq_reverse
    (H : G.PauliFrustrationRepresentation A) (pre T : List V) (x b : V) :
    H.listOperator (pre ++ x :: T) * H.term b =
      (-1 : A) ^ adjacentPairCount G (x :: T ++ [b]) *
        (H.listOperator (pre ++ b :: T.reverse) * H.term x) := by
  have h1 : ∀ (l : List V) (y : V),
      H.listOperator l * H.term y = H.listOperator (l ++ [y]) := by
    intro l y
    rw [listOperator_append]
    simp [listOperator]
  have eL : H.listOperator (pre ++ x :: T) * H.term b =
      H.listOperator (pre ++ (x :: T ++ [b])) := by
    rw [h1, List.append_assoc]
  have eR : H.listOperator (pre ++ b :: T.reverse) * H.term x =
      H.listOperator (pre ++ (x :: T ++ [b]).reverse) := by
    rw [h1]
    congr 1
    simp
  rw [eL, eR, listOperator_append H pre (x :: T ++ [b]),
    listOperator_append H pre (x :: T ++ [b]).reverse, listOperator_reverse]
  generalize adjacentPairCount G (x :: T ++ [b]) = c
  rcases neg_one_pow_eq_or A c with h | h <;> simp [h]

end PauliFrustrationRepresentation

namespace CliqueBubbleWand

variable {G : SimpleGraph V} {K : Set V} {P : CliqueRootedInducedPath G K}

/-! ### The vertex lists of `P` and `P*` -/

/-- The vertex list of `P* = (j₀, ..., j_s, j, j_ℓ, ..., j_{s+2})` is the
handle `(j₀, ..., j_s)`, the bubble `j`, and the reversed tail
`(j_ℓ, ..., j_{s+2})` of `P`. -/
theorem ofFn_reverse_vertex (w : CliqueBubbleWand G K P) :
    List.ofFn w.reverse.path.vertex =
      (List.ofFn P.path.vertex).take (w.split.val + 1) ++
        some w.bubble ::
          ((List.ofFn P.path.vertex).drop (w.split.val + 2)).reverse := by
  have hgap := w.gap
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn]
    have hi : i < P.path.card := by
      rw [List.length_ofFn] at h1
      exact h1
    have hlen : (List.take (w.split.val + 1) (List.ofFn P.path.vertex)).length =
        w.split.val + 1 := by
      simp only [List.length_take, List.length_ofFn]
      omega
    by_cases hle : i ≤ w.split.val
    · rw [List.getElem_append_left (by omega)]
      simp only [List.getElem_take, List.getElem_ofFn]
      exact w.reverse_vertex_of_le (q := ⟨i, hi⟩) hle
    · rw [List.getElem_append_right (by omega)]
      by_cases heq : i = w.split.val + 1
      · subst heq
        simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
        exact w.reverse_vertex_split_succ rfl
      · simp only [hlen]
        rw [List.getElem_cons, dif_neg (by omega), List.getElem_reverse]
        simp only [List.getElem_drop, List.getElem_ofFn, List.length_drop,
          List.length_ofFn]
        exact w.reverse_vertex_of_gt (q := ⟨i, hi⟩) (r := ⟨_, by omega⟩)
          (by simp; omega) (by simp; omega)

/-- The vertex list of `P` from index `s + 1` on is `j_{s+1}` followed by
`j_{s+2}, ..., j_ℓ`. -/
theorem drop_split_succ (w : CliqueBubbleWand G K P) :
    (List.ofFn P.path.vertex).drop (w.split.val + 1) =
      some w.reverseBubble ::
        (List.ofFn P.path.vertex).drop (w.split.val + 2) := by
  have hgap := w.gap
  have hlt : w.split.val + 1 < (List.ofFn P.path.vertex).length := by
    simp only [List.length_ofFn]
    omega
  rw [List.drop_eq_getElem_cons hlt]
  congr 1
  rw [List.getElem_ofFn]
  exact w.path_vertex_split_succ _ rfl

/-- The vertex list of `P` from index `s + 1` on is the vertex list of the hoop
path `(j_{s+1}, ..., j_ℓ)`, read in `G*`. -/
theorem drop_split_succ_eq_ofFn (w : CliqueBubbleWand G K P) :
    (List.ofFn P.path.vertex).drop (w.split.val + 1) =
      List.ofFn (fun q : Fin (P.path.card - (w.split.val + 1)) =>
        P.path.vertex (w.hoopIndex q)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [hoopIndex]
    omega

/-! ### The hoop is an induced cycle -/

/-- The hoop list `(j_{s+1}, ..., j_ℓ, j)` has exactly `hoopCard` adjacent
pairs.  Along `(j_{s+1}, ..., j_ℓ)` the induced path has `hoopCard - 2`
adjacent pairs, and the bubble `j` is adjacent to the two endpoints `j_{s+1}`
and `j_ℓ` only (v1 Definition 11: the hoop is an `m`-cycle with `m` edges). -/
theorem adjacentPairCount_hoop (w : CliqueBubbleWand G K P) :
    PauliFrustrationRepresentation.adjacentPairCount (G.adjoinRootAt K)
      ((List.ofFn P.path.vertex).drop (w.split.val + 1) ++ [some w.bubble]) =
        w.hoopCard := by
  classical
  have hgap := w.gap
  rw [w.drop_split_succ_eq_ofFn,
    PauliFrustrationRepresentation.adjacentPairCount_append_singleton,
    PauliFrustrationRepresentation.adjacentPairCount_ofFn_of_adj_iff _ _ _
      (fun p q => by
        rw [P.path.adj_iff]
        simp only [hoopIndex]
        omega),
    PauliFrustrationRepresentation.listNeighborCount_ofFn_endpoints _
      (k := P.path.card - (w.split.val + 1)) (by omega) _ (some w.bubble)
      (fun q => by
        have hq := q.isLt
        rw [w.adj_iff]
        simp only [hoopIndex]
        omega)]
  unfold hoopCard
  omega

/-! ### The wand pairing -/

/-- The wand pairing for any representation of the frustration graph `G*`:
`h_P h_j = (-1)^m h_{P*} h_{j_{s+1}}` where `m = hoopCard` is the number of
vertices of the hoop, `j` is the bubble and `j_{s+1}` the vertex that `P*`
drops (v1 L1520, L1576). -/
theorem pathOperator_mul_term_bubble_eq_reverse {A : Type w} [Ring A]
    (w : CliqueBubbleWand G K P)
    (H : (G.adjoinRootAt K).PauliFrustrationRepresentation A) :
    H.pathOperator P.path * H.term (some w.bubble) =
      (-1 : A) ^ w.hoopCard *
        (H.pathOperator w.reverse.path * H.term (some w.reverseBubble)) := by
  have key := H.listOperator_append_mul_term_eq_reverse
    ((List.ofFn P.path.vertex).take (w.split.val + 1))
    ((List.ofFn P.path.vertex).drop (w.split.val + 2))
    (some w.reverseBubble) (some w.bubble)
  have e1 : (List.ofFn P.path.vertex).take (w.split.val + 1) ++
      some w.reverseBubble :: (List.ofFn P.path.vertex).drop (w.split.val + 2) =
        List.ofFn P.path.vertex := by
    rw [← w.drop_split_succ, List.take_append_drop]
  have e2 : PauliFrustrationRepresentation.adjacentPairCount (G.adjoinRootAt K)
      (some w.reverseBubble :: (List.ofFn P.path.vertex).drop (w.split.val + 2) ++
        [some w.bubble]) = w.hoopCard := by
    rw [← w.drop_split_succ]
    exact w.adjacentPairCount_hoop
  rw [e1, e2, ← w.ofFn_reverse_vertex] at key
  exact key

end CliqueBubbleWand

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The wand pairing (v1 L1520, L1576): for a bubble wand `w` on `P` whose hoop
has `m` vertices,
`h_P h_j = (-1)^m h_{P*} h_{j_{s+1}}`.
Here `h_j` is the Hamiltonian term of the bubble, `P*` is the reversed path
(`CliqueBubbleWand.reverse`) and `j_{s+1}` is `CliqueBubbleWand.reverseBubble`,
the original vertex that `P*` drops.  No claw-freeness is needed. -/
theorem pathOperator_mul_bubble_eq_reverse
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P) :
    H.pathOperator P * H.operator.term (some w.bubble) =
      (-1 : A) ^ w.hoopCard *
        (H.pathOperator w.reverse * H.operator.term (some w.reverseBubble)) :=
  w.pathOperator_mul_term_bubble_eq_reverse H.operator

/-- For an even hoop the two terms of the wand pairing are equal (the
contributions of even holes add, v1 L1576). -/
theorem pathOperator_mul_bubble_eq_reverse_of_even
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P)
    (heven : Even w.hoopCard) :
    H.pathOperator P * H.operator.term (some w.bubble) =
      H.pathOperator w.reverse * H.operator.term (some w.reverseBubble) := by
  rw [H.pathOperator_mul_bubble_eq_reverse w, heven.neg_one_pow, one_mul]

/-- For an odd hoop the two terms of the wand pairing cancel (the
contributions of odd holes cancel, v1 L1576). -/
theorem pathOperator_mul_bubble_add_reverse_eq_zero
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P)
    (hodd : Odd w.hoopCard) :
    H.pathOperator P * H.operator.term (some w.bubble) +
      H.pathOperator w.reverse * H.operator.term (some w.reverseBubble) = 0 := by
  rw [H.pathOperator_mul_bubble_eq_reverse w, hodd.neg_one_pow]
  simp

end PauliCliqueHamiltonianRepresentation

/-! ### An example: the four-cycle -/

namespace CliqueBubbleWand

namespace Example

/-- The hoop of the four-cycle example has `m = 4` vertices. -/
theorem wand_hoopCard : wand.hoopCard = 4 := rfl

/-- Hand check on `C₄` (`P = (j*, 0, 3, 2)`, bubble `1`, `P* = (j*, 1, 2, 3)`):
`h_P h_1 = h_{P*} h_0`, in every representation of the frustration graph of the
rooted four-cycle. -/
theorem wand_pairing {A : Type w} [Ring A]
    (H : (fourCycle.adjoinRootAt edgeClique).PauliFrustrationRepresentation A) :
    H.pathOperator path.path * H.term (some 1) =
      H.pathOperator wand.reverse.path * H.term (some 0) := by
  have h := wand.pathOperator_mul_term_bubble_eq_reverse H
  have hb : wand.bubble = 1 := rfl
  rw [wand_hoopCard, wand_reverseBubble, hb, (by decide : Even 4).neg_one_pow,
    one_mul] at h
  exact h

end Example

end CliqueBubbleWand

end SimpleGraph
