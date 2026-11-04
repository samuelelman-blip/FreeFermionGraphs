import FreeFermionGraphs.ScaledPauliRepresentation
import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.EvenHoleLabelingDeform
import FreeFermionGraphs.BubbleWandEventClassUnique

/-!
# Single-step clone identities for the hole operator

The proof of cancellation for Theorem 1(iii) (arXiv 2305.15625 v1, L1213-1233) multiplies
the hole operator `h_C = h_{C_a} h_{C_b}` (v1 L313) by the operator of an obstruction
`O`, deforming the hole one vertex at a time: "we use the fact that independent set
factors ... commute to multiply their corresponding factors" (v1 L1213-1233).  This
module proves the per-step identities behind that argument, for the alternating-label
interface `EvenHoleLabeling` of the repository.

Let `L` be an alternating labelling of an even hole, `s ≺_L a_i` (`L.CloneAt s i`; v1
Definition 10, L682) and `L' = L.deform h` the labelling obtained by replacing `a_i` by
`s`.  Then, with the scaled Pauli terms `h_j^2 = b_j^2` (v1 L232),

* forward: `h_L * (h_{a_i} * h_s) = b_{a_i}^2 * h_{L'}`;
* reverse: `h_s * h_{a_i} * h_L = b_{a_i}^2 * h_{L'}`.

The ordered pair `(h_{a_i}, h_s)` is (removed vertex, introduced vertex), matching the
order of the two factors in v1's `h_{P^(r)} = h_{P ∩ C_x} h_{P ∩ C'_y}`.  Neither
claw-freeness nor the full cyclic order of `L` is needed: only the clone axioms of
`CloneAt` and the independence of the two colour classes.

The forward identity needs that `h_{a_i}` and `h_s` commute with the `b`-class product
`h_{L_b}`: each of them has exactly two neighbours in `L_b` (`b_i` and `b_{next i}`),
so the sign `(-1)^{Δ}` of `PauliFrustrationRepresentation.term_mul_independentProduct`
is `+1`.  The reverse identity uses only the left-insertion law for independent
products.

The `b`-class versions are the same identities for `L.swapColors`, with the
colour-swap invariance `labelingOperator_swapColors`
(`b`-class clones are `a`-class clones of the swapped labelling).

## Main declarations

* `SimpleGraph.ScaledPauliFrustrationRepresentation.labelingOperator_mul_pair`: the
  forward identity (a-class).
* `SimpleGraph.ScaledPauliFrustrationRepresentation.pair_mul_labelingOperator`: the
  reverse identity (a-class).
* `SimpleGraph.ScaledPauliFrustrationRepresentation.labelingOperator_mul_pair_swapColors`
  and `pair_mul_labelingOperator_swapColors`: the corresponding `b`-class identities, for a
  clone of `b_i = L.b i` in the sense `L.swapColors.CloneAt s i`.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace HoleCloneIdentities

open EvenHoleLabeling

variable [DecidableEq V] {k : ℕ} {L : G.EvenHoleLabeling k} {s : V} {i : Fin k}

/-- The `a`-class of the deformed labelling is the original class with `a i` replaced by
the clone `s`. -/
private theorem image_a_deform (h : L.CloneAt s i) :
    Finset.univ.image (L.deform h).a =
      insert s ((Finset.univ.image L.a).erase (L.a i)) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_erase]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hq : q = i
    · subst hq
      left
      simp
    · right
      refine ⟨?_, q, ?_⟩
      · rw [deform_a_away L h hq]
        exact fun hqi => hq (L.a_injective hqi)
      · rw [deform_a_away L h hq]
  · rintro (rfl | ⟨hvi, q, rfl⟩)
    · exact ⟨i, by simp⟩
    · have hq : q ≠ i := fun hq => hvi (by rw [hq])
      exact ⟨q, deform_a_away L h hq⟩

/-- A clone is not in the `a`-class. -/
private theorem clone_not_mem_image_a (h : L.CloneAt s i) :
    s ∉ Finset.univ.image L.a := by
  intro hs
  exact h.outside (by
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact L.a_mem_carrier q)

/-- A clone is non-adjacent to every `a`-vertex other than the original. -/
private theorem clone_not_adj_erase (h : L.CloneAt s i) :
    ∀ v ∈ (Finset.univ.image L.a).erase (L.a i), ¬G.Adj s v := by
  intro v hv hsv
  obtain ⟨hvi, hvA⟩ := Finset.mem_erase.1 hv
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hvA
  rcases (h.adj_iff (L.a q) (L.a_mem_carrier q)).1 hsv with hqi | hqi
  · exact hvi hqi
  · exact L.adj_aa i q hqi

/-- The original `a i` is non-adjacent to every other `a`-vertex. -/
private theorem original_not_adj_erase :
    ∀ v ∈ (Finset.univ.image L.a).erase (L.a i), ¬G.Adj (L.a i) v := by
  intro v hv
  obtain ⟨-, hvA⟩ := Finset.mem_erase.1 hv
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hvA
  exact L.adj_aa i q

/-- `a i` has exactly two neighbours in the `b`-class. -/
private theorem card_filter_adj_original [DecidableRel G.Adj] :
    ((Finset.univ.image L.b).filter (G.Adj (L.a i))).card = 2 := by
  have hset : (Finset.univ.image L.b).filter (G.Adj (L.a i)) =
      {L.b i, L.b (L.next i)} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      rcases (L.adj_ab_iff i j).1 hadj with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨i, rfl⟩, L.adj_a_b i⟩
      · exact ⟨⟨_, rfl⟩, L.adj_a_b_next i⟩
  rw [hset, Finset.card_pair]
  exact fun h => L.next_ne i (L.b_injective h).symm

/-- A clone has the same neighbours as `a i` in the `b`-class. -/
private theorem filter_adj_clone [DecidableRel G.Adj] (h : L.CloneAt s i) :
    (Finset.univ.image L.b).filter (G.Adj s) =
      (Finset.univ.image L.b).filter (G.Adj (L.a i)) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨q, rfl⟩, hs⟩
    refine ⟨⟨q, rfl⟩, ?_⟩
    rcases (h.adj_iff (L.b q) (L.b_mem_carrier q)).1 hs with hq | hq
    · exact (L.color_disjoint i q hq.symm).elim
    · exact hq
  · rintro ⟨⟨q, rfl⟩, ha⟩
    exact ⟨⟨q, rfl⟩, (h.adj_iff (L.b q) (L.b_mem_carrier q)).2 (Or.inr ha)⟩

end HoleCloneIdentities

namespace ScaledPauliFrustrationRepresentation

variable {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
variable [DecidableEq V]

open HoleCloneIdentities

/-- A term with an even number of neighbours in an independent set commutes with the
product over that set. -/
private theorem term_commute_of_even [DecidableRel G.Adj]
    (H : G.ScaledPauliFrustrationRepresentation R A) (j : V)
    {U : Finset V} (hU : G.IsIndepSet (U : Set V)) (hev : Even (U.filter (G.Adj j)).card) :
    H.operator.term j * H.operator.independentProduct U =
      H.operator.independentProduct U * H.operator.term j := by
  have hc : G.crossCount {j} U = (U.filter (G.Adj j)).card := by
    rw [crossCount_eq_sum_card_filter, Finset.sum_singleton]
  rw [H.operator.term_mul_independentProduct j hU, hc, hev.neg_one_pow, one_mul]

/-- **Forward single-step clone identity** (v1 L1213-1233, the step `h_C h_O ∝ h_{C~}`).

If `s ≺_L a_i`, then `h_L * (h_{a_i} * h_s) = b_{a_i}^2 * h_{L'}` where `L' = L.deform h`
is `L` with `a_i` replaced by `s`.  The factor `h_{a_i}` removes the original vertex from
the `a`-class (using `h_{a_i}^2 = b_{a_i}^2`) and `h_s` introduces the clone; both commute
with `h_{L_b}` because each has exactly two neighbours in `L_b`.  No claw-freeness or full
cyclic order is needed. -/
theorem labelingOperator_mul_pair (H : G.ScaledPauliFrustrationRepresentation R A)
    {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} {i : Fin k} (h : L.CloneAt s i) :
    H.operator.labelingOperator L * (H.operator.term (L.a i) * H.operator.term s) =
      algebraMap R A (H.coupling (L.a i) ^ 2) * H.operator.labelingOperator (L.deform h) := by
  classical
  set A0 : Finset V := (Finset.univ.image L.a).erase (L.a i) with hA0
  have hai : L.a i ∉ A0 := Finset.notMem_erase _ _
  have hsA0 : s ∉ A0 := fun hs => clone_not_mem_image_a h (Finset.mem_of_mem_erase hs)
  have hA0ind : G.IsIndepSet (A0 : Set V) :=
    L.isIndepSet_image_a.mono (by
      intro v hv
      exact Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hv)))
  have hAeq : Finset.univ.image L.a = insert (L.a i) A0 := by
    rw [hA0, Finset.insert_erase (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)]
  have hAright : H.operator.independentProduct (Finset.univ.image L.a) =
      H.operator.independentProduct A0 * H.operator.term (L.a i) := by
    rw [hAeq]
    exact H.operator.independentProduct_insert_right hai hA0ind original_not_adj_erase
  have hA'right : H.operator.independentProduct (Finset.univ.image (L.deform h).a) =
      H.operator.independentProduct A0 * H.operator.term s := by
    rw [image_a_deform h]
    exact H.operator.independentProduct_insert_right hsA0 hA0ind (clone_not_adj_erase h)
  have hcomm_ai : H.operator.term (L.a i) *
      H.operator.independentProduct (Finset.univ.image L.b) =
      H.operator.independentProduct (Finset.univ.image L.b) * H.operator.term (L.a i) :=
    H.term_commute_of_even (L.a i) L.isIndepSet_image_b (by
      rw [card_filter_adj_original]; exact even_two)
  have hcomm_s : H.operator.term s *
      H.operator.independentProduct (Finset.univ.image L.b) =
      H.operator.independentProduct (Finset.univ.image L.b) * H.operator.term s :=
    H.term_commute_of_even s L.isIndepSet_image_b (by
      rw [filter_adj_clone h, card_filter_adj_original]; exact even_two)
  have hdefb : H.operator.independentProduct (Finset.univ.image (L.deform h).b) =
      H.operator.independentProduct (Finset.univ.image L.b) := rfl
  unfold PauliFrustrationRepresentation.labelingOperator
  rw [hdefb, hA'right, hAright]
  calc H.operator.independentProduct A0 * H.operator.term (L.a i) *
        H.operator.independentProduct (Finset.univ.image L.b) *
        (H.operator.term (L.a i) * H.operator.term s)
      = H.operator.independentProduct A0 *
          ((H.operator.term (L.a i) * H.operator.independentProduct (Finset.univ.image L.b)) *
            H.operator.term (L.a i)) * H.operator.term s := by
        simp only [mul_assoc]
    _ = H.operator.independentProduct A0 *
          (H.operator.independentProduct (Finset.univ.image L.b) *
            (H.operator.term (L.a i) * H.operator.term (L.a i))) * H.operator.term s := by
        rw [hcomm_ai]
        simp only [mul_assoc]
    _ = H.operator.independentProduct A0 *
          (H.operator.independentProduct (Finset.univ.image L.b) *
            algebraMap R A (H.coupling (L.a i) ^ 2)) * H.operator.term s := by
        rw [H.term_sq]
    _ = H.operator.independentProduct A0 *
          (algebraMap R A (H.coupling (L.a i) ^ 2) *
            H.operator.independentProduct (Finset.univ.image L.b)) * H.operator.term s := by
        rw [← Algebra.commutes (H.coupling (L.a i) ^ 2)
          (H.operator.independentProduct (Finset.univ.image L.b))]
    _ = algebraMap R A (H.coupling (L.a i) ^ 2) *
          (H.operator.independentProduct A0 *
            (H.operator.independentProduct (Finset.univ.image L.b) * H.operator.term s)) := by
        rw [← mul_assoc (H.operator.independentProduct A0),
          ← Algebra.commutes (H.coupling (L.a i) ^ 2) (H.operator.independentProduct A0)]
        simp only [mul_assoc]
    _ = algebraMap R A (H.coupling (L.a i) ^ 2) *
          (H.operator.independentProduct A0 * H.operator.term s *
            H.operator.independentProduct (Finset.univ.image L.b)) := by
        rw [← hcomm_s]
        simp only [mul_assoc]

/-- **Reverse single-step clone identity** (v1 L1213-1233, the step `h_O h_{C'} ∝ h_{C~'}`:
the obstruction factors multiply the hole operator from the left).

If `s ≺_L a_i`, then `h_s * h_{a_i} * h_L = b_{a_i}^2 * h_{L'}` with `L' = L.deform h`.
Only the left-insertion law and `h_{a_i}^2 = b_{a_i}^2` are used: no commutation with the
`b`-class is required. -/
theorem pair_mul_labelingOperator (H : G.ScaledPauliFrustrationRepresentation R A)
    {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} {i : Fin k} (h : L.CloneAt s i) :
    H.operator.term s * H.operator.term (L.a i) * H.operator.labelingOperator L =
      algebraMap R A (H.coupling (L.a i) ^ 2) * H.operator.labelingOperator (L.deform h) := by
  classical
  set A0 : Finset V := (Finset.univ.image L.a).erase (L.a i) with hA0
  have hai : L.a i ∉ A0 := Finset.notMem_erase _ _
  have hsA0 : s ∉ A0 := fun hs => clone_not_mem_image_a h (Finset.mem_of_mem_erase hs)
  have hA0ind : G.IsIndepSet (A0 : Set V) :=
    L.isIndepSet_image_a.mono (by
      intro v hv
      exact Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hv)))
  have hAeq : Finset.univ.image L.a = insert (L.a i) A0 := by
    rw [hA0, Finset.insert_erase (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)]
  have hAleft : H.operator.independentProduct (Finset.univ.image L.a) =
      H.operator.term (L.a i) * H.operator.independentProduct A0 := by
    rw [hAeq]
    exact H.operator.independentProduct_insert_left hai hA0ind original_not_adj_erase
  have hA'left : H.operator.independentProduct (Finset.univ.image (L.deform h).a) =
      H.operator.term s * H.operator.independentProduct A0 := by
    rw [image_a_deform h]
    exact H.operator.independentProduct_insert_left hsA0 hA0ind (clone_not_adj_erase h)
  have hdefb : H.operator.independentProduct (Finset.univ.image (L.deform h).b) =
      H.operator.independentProduct (Finset.univ.image L.b) := rfl
  unfold PauliFrustrationRepresentation.labelingOperator
  rw [hdefb, hA'left, hAleft]
  calc H.operator.term s * H.operator.term (L.a i) *
        (H.operator.term (L.a i) * H.operator.independentProduct A0 *
          H.operator.independentProduct (Finset.univ.image L.b))
      = H.operator.term s * (H.operator.term (L.a i) * H.operator.term (L.a i)) *
          H.operator.independentProduct A0 *
          H.operator.independentProduct (Finset.univ.image L.b) := by
        simp only [mul_assoc]
    _ = H.operator.term s * algebraMap R A (H.coupling (L.a i) ^ 2) *
          H.operator.independentProduct A0 *
          H.operator.independentProduct (Finset.univ.image L.b) := by
        rw [H.term_sq]
    _ = algebraMap R A (H.coupling (L.a i) ^ 2) *
          (H.operator.term s * H.operator.independentProduct A0 *
            H.operator.independentProduct (Finset.univ.image L.b)) := by
        rw [← Algebra.commutes (H.coupling (L.a i) ^ 2) (H.operator.term s)]
        simp only [mul_assoc]

/-- `b`-class version of `labelingOperator_mul_pair`: for a clone of `b_i = L.b i`, i.e.
`L.swapColors.CloneAt s i` (note `L.swapColors.a i = L.b i`),
`h_L * (h_{b_i} * h_s) = b_{b_i}^2 * h_{L'}` with `L' = L.swapColors.deform h`.
This follows from the `a`-class identity for `L.swapColors` and
`labelingOperator_swapColors`. -/
theorem labelingOperator_mul_pair_swapColors (H : G.ScaledPauliFrustrationRepresentation R A)
    {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} {i : Fin k} (h : L.swapColors.CloneAt s i) :
    H.operator.labelingOperator L * (H.operator.term (L.b i) * H.operator.term s) =
      algebraMap R A (H.coupling (L.b i) ^ 2) *
        H.operator.labelingOperator (L.swapColors.deform h) := by
  have := H.labelingOperator_mul_pair L.swapColors h
  rwa [H.operator.labelingOperator_swapColors] at this

/-- `b`-class version of `pair_mul_labelingOperator`: for a clone of `b_i = L.b i`, i.e.
`L.swapColors.CloneAt s i`,
`h_s * h_{b_i} * h_L = b_{b_i}^2 * h_{L'}` with `L' = L.swapColors.deform h`. -/
theorem pair_mul_labelingOperator_swapColors (H : G.ScaledPauliFrustrationRepresentation R A)
    {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} {i : Fin k} (h : L.swapColors.CloneAt s i) :
    H.operator.term s * H.operator.term (L.b i) * H.operator.labelingOperator L =
      algebraMap R A (H.coupling (L.b i) ^ 2) *
        H.operator.labelingOperator (L.swapColors.deform h) := by
  have := H.pair_mul_labelingOperator L.swapColors h
  rwa [H.operator.labelingOperator_swapColors] at this

end ScaledPauliFrustrationRepresentation

end SimpleGraph
