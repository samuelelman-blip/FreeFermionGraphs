import FreeFermionGraphs.PauliSetSigns
import FreeFermionGraphs.GeneralizedCycleSymmetry
import FreeFermionGraphs.EvenHoleFullCyclicOrder
import FreeFermionGraphs.EvenHoleLabelingDeform
import FreeFermionGraphs.IndexedInducedHoleEvenLabeling
import FreeFermionGraphs.BubbleWandEventClassUnique

/-!
# Operator-level Definitions 4, 14 and 15: charges, even-hole carriers and `J_{C₀}`

This module attaches operators to the combinatorial objects of manuscript
Definitions 4, 14 and 15 (arXiv 2305.15625 v1, `definition:independentsetcharges`
L516, `definion:tokenslidingcharges` L783, `definition:generalizedcyclesymmetries`
L799) over `SimpleGraph.PauliFrustrationRepresentation`.

## Even-hole carriers

v1 L313 labels an even hole `C = b₀-a₀-b₁-a₁-⋯-b_{k-1}-a_{k-1}-b₀`, with colouring
classes `C_a`, `C_b`, and sets `h_C = h_{C_a} h_{C_b}`, noting that the two factors
commute.  Here

* `IsEvenHoleCarrier G C` : `C` is the vertex set of an (indexed) even induced hole;
* a *full-cyclic labelling* is an `EvenHoleLabeling` whose `next` map is a single
  `k`-cycle (`HasFullCyclicOrder`).

The bridges between the two notions are proved in both directions
(`IndexedInducedHole.exists_fullCyclic_evenHoleLabeling`,
`EvenHoleLabeling.isEvenHoleCarrier_of_hasFullCyclicOrder`,
`EvenHoleLabeling.hasFullCyclicOrder_of_isEvenHoleCarrier`), together with

* uniqueness of the colour classes up to swapping (`colorClasses_eq_or_swap`);
* stability of the deformation closure `⟨C₀⟩` of an even-hole carrier: every member
  is again an even-hole carrier (`InEvenHoleDeformationClosure.isEvenHoleCarrier`).

## The hole operator

`labelingOperator L = h_{C_a} h_{C_b}` is the product attached to a labelling.  It is
invariant under swapping the colours (`labelingOperator_swapColors`) because the two
class products commute (every `a i` has exactly the two `b`-neighbours `b i` and
`b (next i)`, so the cross count is `2k`, even; this uses
`PauliFrustrationRepresentation.independentProduct_mul_independentProduct` from
`FreeFermionGraphs.PauliSetSigns`).  Since the colour classes of an even-hole carrier
are determined up to a swap, `labelingOperator` only depends on the carrier
(`labelingOperator_eq_of_carrier_eq`), and `evenHoleOperator C = h_C` is the carrier-level
operator.  Its fallback value `0` on carriers with no full-cyclic labelling is never
used on a carrier that is an even hole, or lies in the deformation closure of one
(`evenHoleOperator_eq`, `evenHoleOperator_eq_of_isEvenHoleCarrier`,
`exists_fullCyclic_labeling_of_mem_closure`).

## Charges

`tokenSlidingChargeOp k μ = q_{k,μ}`, `generalizedCycleSymmetryOp C₀ = J_{C₀}`;
`sum_tokenSlidingChargeOp` is `Σ_μ q_{k,μ} = Q^(k)`, and `Q^(1) = H`
(`operatorIndependentSetChargeFull_one`); `Q^(0) = I` is
`SimpleGraph.operatorIndependentSetCharge_zero`, and the component charge at `k = 0` is `I`
(`tokenSlidingChargeOp_zero`, the convention of v1 L794).

Convention: the manuscript only defines `J_{C₀}` for an even hole `C₀`; downstream
statements about `generalizedCycleSymmetryOp` should assume `G.IsEvenHoleCarrier C₀`.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- `C` is the vertex set of an even induced hole (an `IndexedInducedHole` of even
length).  v1 L313 ("An even hole is a hole with an even number of vertices"). -/
def IsEvenHoleCarrier (G : SimpleGraph V) (C : Set V) : Prop :=
  ∃ H : G.IndexedInducedHole, Even H.card ∧ Set.range H.vertex = C

/-! ### Connectedness of an indexed hole -/

/-- A predicate on vertices that is invariant along edges of an indexed hole takes the
same truth value on all its vertices (connectedness of a hole, by walking along the
cyclic order). -/
theorem IndexedInducedHole.pred_iff_of_adj (C : G.IndexedInducedHole) (P : V → Prop)
    (hP : ∀ i j : Fin C.card, G.Adj (C.vertex i) (C.vertex j) →
      (P (C.vertex i) ↔ P (C.vertex j)))
    (i j : Fin C.card) : P (C.vertex i) ↔ P (C.vertex j) := by
  have h4 := C.four_le_card
  have key : ∀ n (hn : n < C.card),
      P (C.vertex ⟨n, hn⟩) ↔ P (C.vertex ⟨0, by omega⟩) := by
    intro n
    induction n with
    | zero => intro hn; exact Iff.rfl
    | succ n ih =>
      intro hn
      have h1 := hP ⟨n, by omega⟩ ⟨n + 1, hn⟩ ((C.adj_iff _ _).2 (Or.inl rfl))
      exact h1.symm.trans (ih (by omega))
  exact (key i.1 i.2).trans (key j.1 j.2).symm

/-- A predicate invariant along the edges inside an even-hole carrier takes the same
truth value on the whole carrier. -/
theorem IsEvenHoleCarrier.pred_iff {C : Set V} (hC : G.IsEvenHoleCarrier C) (P : V → Prop)
    (hP : ∀ x ∈ C, ∀ y ∈ C, G.Adj x y → (P x ↔ P y)) :
    ∀ x ∈ C, ∀ y ∈ C, (P x ↔ P y) := by
  obtain ⟨H, _, rfl⟩ := hC
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact H.pred_iff_of_adj P (fun i j hij => hP _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij) i j

namespace EvenHoleLabeling

/-! ### Iterates of `next` -/

theorem next_injective {k : ℕ} (L : G.EvenHoleLabeling k) : Function.Injective L.next := by
  intro x y h
  rw [← L.prev_next x, ← L.prev_next y, h]

theorem nextIterate_add {k : ℕ} (L : G.EvenHoleLabeling k) (m n : ℕ) (i : Fin k) :
    L.nextIterate (m + n) i = L.nextIterate m (L.nextIterate n i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [nextIterate_succ, ih]

theorem nextIterate_injective {k : ℕ} (L : G.EvenHoleLabeling k) (m : ℕ) :
    Function.Injective (L.nextIterate m) := by
  induction m with
  | zero => intro x y h; exact h
  | succ m ih =>
    intro x y h
    exact ih (L.next_injective h)

/-! ### From a carrier equal to the range of an indexed hole to a full cyclic order -/

/-- A labelling whose carrier is the vertex set of an indexed induced hole has full
cyclic order: otherwise the `next`-orbit of an index would carry a proper union of
colour-class vertices that has no edge to the rest of the hole, contradicting
connectedness of the hole. -/
theorem hasFullCyclicOrder_of_carrier_eq_range {k : ℕ} (L : G.EvenHoleLabeling k)
    (H : G.IndexedInducedHole) (hcar : L.carrier = Set.range H.vertex) :
    L.HasFullCyclicOrder := by
  intro i n hn hnk heq
  -- the orbit of `i`
  let O : Fin k → Prop := fun j => ∃ m, L.nextIterate m i = j
  have hOnext : ∀ j, O j → O (L.next j) := by
    rintro j ⟨m, rfl⟩
    exact ⟨m + 1, rfl⟩
  have hOprev : ∀ j, O j → O (L.prev j) := by
    rintro j ⟨m, rfl⟩
    cases m with
    | zero =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine ⟨n', ?_⟩
      have h1 : L.nextIterate (n' + 1) i = i := heq
      show L.nextIterate n' i = L.prev i
      calc L.nextIterate n' i = L.prev (L.next (L.nextIterate n' i)) := (L.prev_next _).symm
        _ = L.prev i := congrArg L.prev h1
    | succ m =>
      exact ⟨m, by rw [nextIterate_succ, L.prev_next]⟩
  -- the orbit is a proper subset of `Fin k`
  have hper : ∀ q m, L.nextIterate (m + q * n) i = L.nextIterate m i := by
    intro q
    induction q with
    | zero => intro m; simp
    | succ q ih =>
      intro m
      rw [show m + (q + 1) * n = (m + q * n) + n by ring, L.nextIterate_add, heq, ih]
  have hproper : ∃ j : Fin k, ¬ O j := by
    by_contra hall'
    have hall : ∀ j, O j := fun j => by_contra fun h => hall' ⟨j, h⟩
    let f : Fin n → Fin k := fun m => L.nextIterate m.val i
    have hsurj : Function.Surjective f := by
      intro j
      obtain ⟨m, hm⟩ := hall j
      have hmn : m % n < n := Nat.mod_lt _ hn
      refine ⟨⟨m % n, hmn⟩, ?_⟩
      show L.nextIterate (m % n) i = j
      rw [← hm]
      have := hper (m / n) (m % n)
      rw [Nat.mul_comm, Nat.mod_add_div] at this
      exact this.symm
    have := Fintype.card_le_of_surjective f hsurj
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨j₀, hj₀⟩ := hproper
  -- the invariant predicate
  let P : V → Prop := fun v => ∃ j, O j ∧ (v = L.a j ∨ v = L.b j)
  have hPstep : ∀ x ∈ L.carrier, ∀ y ∈ L.carrier, G.Adj x y → P x → P y := by
    intro x hx y hy hxy hPx
    obtain ⟨j, hOj, hxj⟩ := hPx
    rcases hxj with rfl | rfl
    · rcases hy with ⟨j', rfl⟩ | ⟨j', rfl⟩
      · exact (L.adj_aa j j' hxy).elim
      · rcases (L.adj_ab_iff j j').1 hxy with rfl | rfl
        · exact ⟨_, hOj, Or.inr rfl⟩
        · exact ⟨_, hOnext _ hOj, Or.inr rfl⟩
    · rcases hy with ⟨j', rfl⟩ | ⟨j', rfl⟩
      · rcases (L.adj_ab_iff j' j).1 hxy.symm with rfl | rfl
        · exact ⟨_, hOj, Or.inl rfl⟩
        · refine ⟨L.prev (L.next j'), hOprev _ hOj, Or.inl ?_⟩
          rw [L.prev_next]
      · exact (L.adj_bb j j' hxy).elim
  have hP : ∀ x ∈ Set.range H.vertex, ∀ y ∈ Set.range H.vertex, G.Adj x y →
      (P x ↔ P y) := by
    intro x hx y hy hxy
    rw [← hcar] at hx hy
    exact ⟨hPstep x hx y hy hxy, hPstep y hy x hx hxy.symm⟩
  -- apply connectedness of the hole
  have hcon : ∀ x ∈ Set.range H.vertex, ∀ y ∈ Set.range H.vertex, (P x ↔ P y) := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact H.pred_iff_of_adj P (fun i j hij => hP _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij) p q
  have hPa : P (L.a i) := ⟨i, ⟨0, rfl⟩, Or.inl rfl⟩
  have hai : L.a i ∈ Set.range H.vertex := by rw [← hcar]; exact L.a_mem_carrier i
  have haj : L.a j₀ ∈ Set.range H.vertex := by rw [← hcar]; exact L.a_mem_carrier j₀
  obtain ⟨j, hOj, hj⟩ := (hcon _ hai _ haj).1 hPa
  rcases hj with hj | hj
  · exact hj₀ (L.a_injective hj ▸ hOj)
  · exact L.color_disjoint j₀ j hj

/-! ### From a full cyclic order to an indexed hole -/

/-- Under a full cyclic order, two iterates `next^m i`, `next^m' i` with
`m < m' ≤ k` coincide only for `m = 0`, `m' = k`. -/
theorem HasFullCyclicOrder.eq_zero_of_nextIterate_eq {k : ℕ} {L : G.EvenHoleLabeling k}
    (hL : L.HasFullCyclicOrder) (i : Fin k) {m m' : ℕ} (hmm' : m < m') (hm' : m' ≤ k)
    (h : L.nextIterate m i = L.nextIterate m' i) : m = 0 ∧ m' = k := by
  obtain ⟨d, rfl⟩ : ∃ d, m' = m + d := ⟨m' - m, by omega⟩
  rw [L.nextIterate_add] at h
  have hd : L.nextIterate d i = i := (L.nextIterate_injective m h).symm
  by_cases hdk : d < k
  · exact (hL i d (by omega) hdk hd).elim
  · omega

/-- Under a full cyclic order the `k`-th iterate of `next` is the identity. -/
theorem HasFullCyclicOrder.nextIterate_card {k : ℕ} {L : G.EvenHoleLabeling k}
    (hL : L.HasFullCyclicOrder) (i : Fin k) : L.nextIterate k i = i := by
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (k + 1) => L.nextIterate m.val i) (by simp)
  have hxy' : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hx := x.isLt
  have hy := y.isLt
  rcases Nat.lt_or_gt_of_ne hxy' with hlt | hlt
  · obtain ⟨h0, hk⟩ := hL.eq_zero_of_nextIterate_eq i hlt (by omega) hf
    rw [h0, hk] at hf
    exact hf.symm
  · obtain ⟨h0, hk⟩ := hL.eq_zero_of_nextIterate_eq i hlt (by omega) hf.symm
    rw [h0, hk] at hf
    exact hf

/-- The index reached after `j` steps of `next` from the base index `0`. -/
def walkIndex {k : ℕ} (L : G.EvenHoleLabeling k) (j : Fin k) : Fin k :=
  L.nextIterate j.val ⟨0, by have := L.two_le; omega⟩

theorem walkIndex_injective {k : ℕ} {L : G.EvenHoleLabeling k} (hL : L.HasFullCyclicOrder) :
    Function.Injective L.walkIndex := by
  intro j j' h
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (hL.eq_zero_of_nextIterate_eq _ hlt (by omega) h).2
    have := j'.isLt
    omega
  · have := (hL.eq_zero_of_nextIterate_eq _ hlt (by omega) h.symm).2
    have := j.isLt
    omega

theorem walkIndex_surjective {k : ℕ} {L : G.EvenHoleLabeling k} (hL : L.HasFullCyclicOrder) :
    Function.Surjective L.walkIndex :=
  Finite.surjective_of_injective (walkIndex_injective hL)

theorem next_walkIndex_of_lt {k : ℕ} (L : G.EvenHoleLabeling k) (j : Fin k)
    (hj : j.val + 1 < k) : L.next (L.walkIndex j) = L.walkIndex ⟨j.val + 1, hj⟩ :=
  rfl

theorem next_walkIndex_of_eq {k : ℕ} {L : G.EvenHoleLabeling k} (hL : L.HasFullCyclicOrder)
    (j : Fin k) (hj : j.val + 1 = k) :
    L.next (L.walkIndex j) = L.walkIndex ⟨0, by have := L.two_le; omega⟩ := by
  have h := hL.nextIterate_card ⟨0, by have := L.two_le; omega⟩
  show L.nextIterate (j.val + 1) _ = _
  rw [hj]
  exact h

/-- The vertex at position `p` of the walk `b₀, a₀, b₁, a₁, …` (even positions are
`b`-vertices, odd positions `a`-vertices). -/
def walkVertex {k : ℕ} (L : G.EvenHoleLabeling k) (p : Fin (2 * k)) : V :=
  if p.val % 2 = 0 then L.b (L.walkIndex ⟨p.val / 2, by have := p.isLt; omega⟩)
  else L.a (L.walkIndex ⟨p.val / 2, by have := p.isLt; omega⟩)

theorem walkVertex_adj_even_odd {k : ℕ} {L : G.EvenHoleLabeling k} (hL : L.HasFullCyclicOrder)
    {p q : Fin (2 * k)} (hp : p.val % 2 = 0) (hq : q.val % 2 = 1) :
    G.Adj (L.walkVertex p) (L.walkVertex q) ↔ CyclicAdjacent p q := by
  have hp' := p.isLt
  have hq' := q.isLt
  unfold walkVertex
  rw [if_pos hp, if_neg (by omega), G.adj_comm, L.adj_ab_iff,
    (walkIndex_injective hL).eq_iff]
  unfold CyclicAdjacent
  by_cases hlt : q.val / 2 + 1 < k
  · rw [L.next_walkIndex_of_lt _ hlt, (walkIndex_injective hL).eq_iff]
    simp only [Fin.mk.injEq]
    omega
  · have hk : q.val / 2 + 1 = k := by omega
    rw [L.next_walkIndex_of_eq hL ⟨q.val / 2, by omega⟩ hk, (walkIndex_injective hL).eq_iff]
    simp only [Fin.mk.injEq]
    omega

/-- The indexed even hole obtained by walking `b₀-a₀-b₁-a₁-⋯-b_{k-1}-a_{k-1}` around a
full-cyclic labelling (v1 L313, Eq. `evenholelabel`). -/
def walkHole {k : ℕ} (L : G.EvenHoleLabeling k) (hL : L.HasFullCyclicOrder) :
    G.IndexedInducedHole where
  card := 2 * k
  four_le_card := by have := L.two_le; omega
  vertex := L.walkVertex
  injective := by
    intro p q h
    apply Fin.ext
    have hp' := p.isLt
    have hq' := q.isLt
    unfold walkVertex at h
    by_cases hp : p.val % 2 = 0 <;> by_cases hq : q.val % 2 = 0
    · rw [if_pos hp, if_pos hq] at h
      have := congrArg Fin.val ((walkIndex_injective hL) (L.b_injective h))
      simp only at this
      omega
    · rw [if_pos hp, if_neg hq] at h
      exact (L.color_disjoint _ _ h.symm).elim
    · rw [if_neg hp, if_pos hq] at h
      exact (L.color_disjoint _ _ h).elim
    · rw [if_neg hp, if_neg hq] at h
      have := congrArg Fin.val ((walkIndex_injective hL) (L.a_injective h))
      simp only at this
      omega
  adj_iff := by
    intro p q
    have hp' := p.isLt
    have hq' := q.isLt
    by_cases hp : p.val % 2 = 0 <;> by_cases hq : q.val % 2 = 0
    · have h1 : ¬G.Adj (L.walkVertex p) (L.walkVertex q) := by
        unfold walkVertex
        rw [if_pos hp, if_pos hq]
        exact L.adj_bb _ _
      refine ⟨fun h => (h1 h).elim, fun h => ?_⟩
      unfold CyclicAdjacent at h
      omega
    · exact walkVertex_adj_even_odd hL hp (by omega)
    · rw [G.adj_comm]
      exact (walkVertex_adj_even_odd hL hq (by omega)).trans
        ⟨CyclicAdjacent.symm, CyclicAdjacent.symm⟩
    · have h1 : ¬G.Adj (L.walkVertex p) (L.walkVertex q) := by
        unfold walkVertex
        rw [if_neg hp, if_neg hq]
        exact L.adj_aa _ _
      refine ⟨fun h => (h1 h).elim, fun h => ?_⟩
      unfold CyclicAdjacent at h
      omega

/-- A full-cyclic labelling presents an even hole carrier: its carrier is the vertex set
of the walk hole `b₀-a₀-b₁-a₁-⋯`, of length `2k`.  (Converse of
`IndexedInducedHole.exists_fullCyclic_evenHoleLabeling`.) -/
theorem isEvenHoleCarrier_of_hasFullCyclicOrder {k : ℕ} (L : G.EvenHoleLabeling k)
    (hL : L.HasFullCyclicOrder) : G.IsEvenHoleCarrier L.carrier := by
  refine ⟨L.walkHole hL, even_two_mul k, ?_⟩
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    show L.walkVertex p ∈ L.carrier
    unfold walkVertex
    split_ifs
    · exact L.b_mem_carrier _
    · exact L.a_mem_carrier _
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨j, rfl⟩ := walkIndex_surjective hL i
      refine ⟨⟨2 * j.val + 1, show 2 * j.val + 1 < 2 * k by have := j.isLt; omega⟩, ?_⟩
      show L.walkVertex _ = _
      unfold walkVertex
      have h1 : ¬ (2 * j.val + 1) % 2 = 0 := by omega
      rw [if_neg h1]
      congr 2
      apply Fin.ext
      simp only
      omega
    · obtain ⟨j, rfl⟩ := walkIndex_surjective hL i
      refine ⟨⟨2 * j.val, show 2 * j.val < 2 * k by have := j.isLt; omega⟩, ?_⟩
      show L.walkVertex _ = _
      unfold walkVertex
      have h1 : (2 * j.val) % 2 = 0 := by omega
      rw [if_pos h1]
      congr 2
      apply Fin.ext
      simp only
      omega

/-- A full cyclic order is automatic for a labelling that presents an even hole carrier
(the carrier is a single connected hole, so `next` cannot split into several orbits). -/
theorem hasFullCyclicOrder_of_isEvenHoleCarrier {k : ℕ} (L : G.EvenHoleLabeling k)
    (hC : G.IsEvenHoleCarrier L.carrier) : L.HasFullCyclicOrder := by
  obtain ⟨H, _, hH⟩ := hC
  exact L.hasFullCyclicOrder_of_carrier_eq_range H hH.symm

/-- A labelling presents an even hole carrier iff it has full cyclic order. -/
theorem isEvenHoleCarrier_iff_hasFullCyclicOrder {k : ℕ} (L : G.EvenHoleLabeling k) :
    G.IsEvenHoleCarrier L.carrier ↔ L.HasFullCyclicOrder :=
  ⟨L.hasFullCyclicOrder_of_isEvenHoleCarrier, L.isEvenHoleCarrier_of_hasFullCyclicOrder⟩

/-- The two colour classes of an even-hole carrier are determined up to swapping.  If
two alternating labellings (of possibly different half-lengths, which is forced to
agree) have the same even-hole carrier, then they have the same `a`- and `b`-classes
or the roles are interchanged.  (v1 L313: "the two unique independent sets of size
`k` in `C`, the colouring classes".)  The proof is uniqueness of the two-colouring of a
connected bipartite graph, the carrier being a connected hole. -/
theorem colorClasses_eq_or_swap {k k' : ℕ} (L : G.EvenHoleLabeling k)
    (L' : G.EvenHoleLabeling k') (hC : G.IsEvenHoleCarrier L.carrier)
    (h : L.carrier = L'.carrier) :
    (Set.range L.a = Set.range L'.a ∧ Set.range L.b = Set.range L'.b) ∨
      (Set.range L.a = Set.range L'.b ∧ Set.range L.b = Set.range L'.a) := by
  have hcar : ∀ x, (x ∈ Set.range L.a ∨ x ∈ Set.range L.b) ↔
      (x ∈ Set.range L'.a ∨ x ∈ Set.range L'.b) := fun x => Set.ext_iff.mp h x
  have hdisj : ∀ x, ¬ (x ∈ Set.range L.a ∧ x ∈ Set.range L.b) := by
    rintro x ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
    exact L.color_disjoint i j hj.symm
  have hdisj' : ∀ x, ¬ (x ∈ Set.range L'.a ∧ x ∈ Set.range L'.b) := by
    rintro x ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
    exact L'.color_disjoint i j hj.symm
  -- adjacency inside the carrier switches the colour class
  have hadj : ∀ {M : Σ k, G.EvenHoleLabeling k} {x y : V},
      (x ∈ Set.range M.2.a ∨ x ∈ Set.range M.2.b) →
      (y ∈ Set.range M.2.a ∨ y ∈ Set.range M.2.b) → G.Adj x y →
      (x ∈ Set.range M.2.a ↔ y ∉ Set.range M.2.a) := by
    rintro ⟨kk, M⟩ x y hx hy hxy
    have hd : ∀ x, ¬ (x ∈ Set.range M.a ∧ x ∈ Set.range M.b) := by
      rintro x ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
      exact M.color_disjoint i j hj.symm
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, rfl⟩
      exact M.adj_aa i j hxy
    · intro hya
      rcases hx with hxa | ⟨i, rfl⟩
      · exact hxa
      · rcases hy with hya' | ⟨j, rfl⟩
        · exact (hya hya').elim
        · exact (M.adj_bb i j hxy).elim
  let P : V → Prop := fun x => x ∈ Set.range L.a ↔ x ∈ Set.range L'.a
  have hP : ∀ x ∈ L.carrier, ∀ y ∈ L.carrier, G.Adj x y → (P x ↔ P y) := by
    intro x hx y hy hxy
    have h1 := hadj (M := ⟨k, L⟩) hx hy hxy
    have h2 := hadj (M := ⟨k', L'⟩) ((hcar x).1 hx) ((hcar y).1 hy) hxy
    simp only [P]
    tauto
  have hconst := hC.pred_iff P hP
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ L.carrier := by
    obtain ⟨H, _, hH⟩ := hC
    have hmem : H.vertex ⟨0, by have := H.four_le_card; omega⟩ ∈ Set.range H.vertex :=
      Set.mem_range_self _
    exact ⟨_, hH ▸ hmem⟩
  by_cases hx₀P : P x₀
  · left
    have hall : ∀ x, x ∈ L.carrier → P x := fun x hx => (hconst x₀ hx₀ x hx).1 hx₀P
    constructor <;> ext x
    · by_cases hx : x ∈ L.carrier
      · have := hall x hx
        have := hcar x
        have := hdisj x
        simp only [P] at *
        tauto
      · have := hcar x
        have := hdisj x
        have : ¬ (x ∈ Set.range L.a ∨ x ∈ Set.range L.b) := hx
        tauto
    · by_cases hx : x ∈ L.carrier
      · have := hall x hx
        have := hcar x
        have := hdisj x
        have := hdisj' x
        simp only [P] at *
        tauto
      · have := hcar x
        have : ¬ (x ∈ Set.range L.a ∨ x ∈ Set.range L.b) := hx
        tauto
  · right
    have hall : ∀ x, x ∈ L.carrier → ¬ P x := fun x hx hPx =>
      hx₀P ((hconst x₀ hx₀ x hx).2 hPx)
    constructor <;> ext x
    · by_cases hx : x ∈ L.carrier
      · have := hall x hx
        have := hcar x
        have := hdisj x
        have := hdisj' x
        simp only [P] at *
        tauto
      · have := hcar x
        have : ¬ (x ∈ Set.range L.a ∨ x ∈ Set.range L.b) := hx
        tauto
    · by_cases hx : x ∈ L.carrier
      · have := hall x hx
        have := hcar x
        have := hdisj x
        have := hdisj' x
        simp only [P] at *
        tauto
      · have := hcar x
        have : ¬ (x ∈ Set.range L.a ∨ x ∈ Set.range L.b) := hx
        tauto

end EvenHoleLabeling

/-- Every even indexed induced hole has an alternating labelling with the same
carrier and **full cyclic order**.  (The labelling of
`IndexedInducedHole.exists_evenHoleLabeling` automatically has full cyclic order, since
its carrier is a connected hole; see `EvenHoleLabeling.hasFullCyclicOrder_of_carrier_eq_range`.) -/
theorem IndexedInducedHole.exists_fullCyclic_evenHoleLabeling (C : G.IndexedInducedHole)
    (hEven : Even C.card) :
    ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧
      L.carrier = Set.range C.vertex := by
  obtain ⟨k, L, hL⟩ := C.exists_evenHoleLabeling hEven
  exact ⟨k, L, L.hasFullCyclicOrder_of_carrier_eq_range C hL, hL⟩

/-- A set is an even hole carrier iff it is the carrier of a full-cyclic labelling. -/
theorem isEvenHoleCarrier_iff_exists_fullCyclic_labeling (C : Set V) :
    G.IsEvenHoleCarrier C ↔
      ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧ L.carrier = C := by
  constructor
  · rintro ⟨H, hEven, rfl⟩
    exact H.exists_fullCyclic_evenHoleLabeling hEven
  · rintro ⟨k, L, hL, rfl⟩
    exact L.isEvenHoleCarrier_of_hasFullCyclicOrder hL

/-- The deformation closure of an even-hole carrier consists of even-hole carriers:
a single-vertex deformation step (in either direction) of an even-hole carrier is the
passage between the carriers of two labellings that differ by `EvenHoleLabeling.deform`,
which has the same `next` iterates, hence the same full cyclic order. -/
theorem InEvenHoleDeformationClosure.isEvenHoleCarrier {C₀ C : Set V}
    (h : InEvenHoleDeformationClosure G C₀ C) (hC₀ : G.IsEvenHoleCarrier C₀) :
    G.IsEvenHoleCarrier C := by
  induction h with
  | refl => exact hC₀
  | tail _ hstep ih =>
    obtain ⟨k, L, s, i, hcl, hcase⟩ := hstep
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hL := L.hasFullCyclicOrder_of_isEvenHoleCarrier ih
      rw [← L.deform_carrier hcl]
      exact (L.deform hcl).isEvenHoleCarrier_of_hasFullCyclicOrder
        (L.hasFullCyclicOrder_deform hcl hL)
    · rw [← L.deform_carrier hcl] at ih
      have hD := (L.deform hcl).hasFullCyclicOrder_of_isEvenHoleCarrier ih
      have hL : L.HasFullCyclicOrder := fun q n hn hk => by
        rw [← L.nextIterate_deform hcl n q]
        exact hD q n hn hk
      exact L.isEvenHoleCarrier_of_hasFullCyclicOrder hL

namespace EvenHoleLabeling

/-- The `a`-class `{a i}` of a labelling is an independent set. -/
theorem isIndepSet_image_a [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) :
    G.IsIndepSet ((Finset.univ.image L.a : Finset V) : Set V) := by
  intro x hx y hy _
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact L.adj_aa i j

/-- The `b`-class `{b i}` of a labelling is an independent set. -/
theorem isIndepSet_image_b [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) :
    G.IsIndepSet ((Finset.univ.image L.b : Finset V) : Set V) := by
  intro x hx y hy _
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact L.adj_bb i j

/-- Every `a i` has exactly the two `b`-neighbours `b i` and `b (next i)`, so the
number of edges between the two colour classes is `2k`. -/
theorem crossCount_image_a_image_b [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) :
    G.crossCount (Finset.univ.image L.a) (Finset.univ.image L.b) = 2 * k := by
  classical
  rw [crossCount_eq_sum_card_filter,
    Finset.sum_image (fun i _ j _ h => L.a_injective h)]
  have h2 : ∀ i : Fin k, ((Finset.univ.image L.b).filter (G.Adj (L.a i))).card = 2 := by
    intro i
    have hset : (Finset.univ.image L.b).filter (G.Adj (L.a i)) = {L.b i, L.b (L.next i)} := by
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
  simp [h2, mul_comm]

/-- Finsets of colour-class vertices depend only on the range of the labelling map. -/
theorem image_univ_eq_of_range_eq [DecidableEq V] {k k' : ℕ} (f : Fin k → V) (g : Fin k' → V)
    (h : Set.range f = Set.range g) : Finset.univ.image f = Finset.univ.image g := by
  apply Finset.coe_injective
  simpa using h

end EvenHoleLabeling

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- The operator `h_C = h_{C_a} h_{C_b}` attached to an alternating labelling
(v1 L313: "We choose the factor ordering for the operator corresponding to `C` as
`h_C = h_{C_a} h_{C_b}`"). -/
noncomputable def labelingOperator [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {k : ℕ} (L : G.EvenHoleLabeling k) : A :=
  H.independentProduct (Finset.univ.image L.a) * H.independentProduct (Finset.univ.image L.b)

/-- The two colour-class products commute (v1 L313: "these operators commute").  Each `a i`
has exactly the two `b`-neighbours `b i`, `b (next i)`, so the cross count is `2k`, even
(`PauliFrustrationRepresentation.independentProduct_mul_independentProduct_of_even`). -/
theorem labelingOperator_comm [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {k : ℕ} (L : G.EvenHoleLabeling k) :
    H.independentProduct (Finset.univ.image L.a) * H.independentProduct (Finset.univ.image L.b) =
      H.independentProduct (Finset.univ.image L.b) *
        H.independentProduct (Finset.univ.image L.a) :=
  H.independentProduct_mul_independentProduct_of_even L.isIndepSet_image_a L.isIndepSet_image_b
    (by rw [L.crossCount_image_a_image_b]; exact even_two_mul k)

/-- Swapping the two colours does not change `h_{C_a} h_{C_b}`, since the classes commute. -/
theorem labelingOperator_swapColors [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {k : ℕ} (L : G.EvenHoleLabeling k) :
    H.labelingOperator L.swapColors = H.labelingOperator L := by
  have h1 : Finset.univ.image L.swapColors.a = Finset.univ.image L.b := rfl
  have h2 : Finset.univ.image L.swapColors.b = Finset.univ.image L.a := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨L.next j, by simp [EvenHoleLabeling.swapColors, L.prev_next]⟩
  unfold labelingOperator
  rw [h1, h2]
  exact (H.labelingOperator_comm L).symm

/-- `h_C` depends only on the carrier: two alternating labellings with the same even-hole
carrier give the same operator.  By `EvenHoleLabeling.colorClasses_eq_or_swap` their
colour classes agree or are swapped, and the two class products commute. -/
theorem labelingOperator_eq_of_carrier_eq [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {k k' : ℕ} (L : G.EvenHoleLabeling k) (L' : G.EvenHoleLabeling k')
    (hC : G.IsEvenHoleCarrier L.carrier) (h : L.carrier = L'.carrier) :
    H.labelingOperator L = H.labelingOperator L' := by
  rcases L.colorClasses_eq_or_swap L' hC h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · unfold labelingOperator
    rw [EvenHoleLabeling.image_univ_eq_of_range_eq _ _ ha,
      EvenHoleLabeling.image_univ_eq_of_range_eq _ _ hb]
  · unfold labelingOperator
    rw [EvenHoleLabeling.image_univ_eq_of_range_eq _ _ ha,
      EvenHoleLabeling.image_univ_eq_of_range_eq _ _ hb]
    exact (H.labelingOperator_comm L').symm

/-- The carrier-level operator `h_C` of an even hole (v1 L313, Def. 15 L799).

It is `h_{C_a} h_{C_b}` for a full-cyclic labelling of `C` and the (never used on
even-hole carriers, see `evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier`) fallback value
`0` otherwise.  The choice of labelling is irrelevant by
`labelingOperator_eq_of_carrier_eq`. -/
noncomputable def evenHoleOperator [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    (C : Set V) : A := by
  classical
  exact if h : ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧ L.carrier = C
    then H.labelingOperator h.choose_spec.choose else 0

/-- For every labelling presenting an even-hole carrier, `h_C` is its labelling operator;
in particular `evenHoleOperator` is not the fallback `0` there. -/
theorem evenHoleOperator_eq_of_isEvenHoleCarrier [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {k : ℕ} (L : G.EvenHoleLabeling k)
    (hC : G.IsEvenHoleCarrier L.carrier) :
    H.evenHoleOperator L.carrier = H.labelingOperator L := by
  classical
  have hex : ∃ (k' : ℕ) (L' : G.EvenHoleLabeling k'), L'.HasFullCyclicOrder ∧
      L'.carrier = L.carrier :=
    ⟨k, L, L.hasFullCyclicOrder_of_isEvenHoleCarrier hC, rfl⟩
  unfold evenHoleOperator
  rw [dif_pos hex]
  have hcar : hex.choose_spec.choose.carrier = L.carrier := hex.choose_spec.choose_spec.2
  exact H.labelingOperator_eq_of_carrier_eq _ L (by rw [hcar]; exact hC) hcar

/-- `h_C = h_{C_a} h_{C_b}` for every full-cyclic labelling `L` of `C = L.carrier`. -/
theorem evenHoleOperator_eq [DecidableEq V] (H : G.PauliFrustrationRepresentation A) {k : ℕ}
    (L : G.EvenHoleLabeling k) (hL : L.HasFullCyclicOrder) :
    H.evenHoleOperator L.carrier = H.labelingOperator L :=
  H.evenHoleOperator_eq_of_isEvenHoleCarrier L (L.isEvenHoleCarrier_of_hasFullCyclicOrder hL)

/-- The fallback value `0` of `evenHoleOperator` is only taken on sets that are not
even-hole carriers. -/
theorem evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {C : Set V} (hC : ¬ G.IsEvenHoleCarrier C) :
    H.evenHoleOperator C = 0 := by
  classical
  have hex : ¬ ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧ L.carrier = C :=
    fun h => hC ((isEvenHoleCarrier_iff_exists_fullCyclic_labeling C).2 h)
  unfold evenHoleOperator
  rw [dif_neg hex]

/-- On an even-hole carrier `evenHoleOperator` is the labelling operator of some
full-cyclic labelling of that carrier. -/
theorem exists_fullCyclic_labeling_evenHoleOperator [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧ L.carrier = C ∧
      H.evenHoleOperator C = H.labelingOperator L := by
  obtain ⟨k, L, hL, rfl⟩ := (isEvenHoleCarrier_iff_exists_fullCyclic_labeling C).1 hC
  exact ⟨k, L, hL, rfl, H.evenHoleOperator_eq L hL⟩

/-- Every even indexed induced hole `C` carries the genuine operator `h_C`: its
carrier has a full-cyclic labelling `L`, and `evenHoleOperator` of the carrier is
`labelingOperator L` (not the fallback `0`). -/
theorem exists_fullCyclic_labeling_evenHoleOperator_of_indexedInducedHole [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (C : G.IndexedInducedHole) (hEven : Even C.card) :
    ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧
      L.carrier = Set.range C.vertex ∧
      H.evenHoleOperator (Set.range C.vertex) = H.labelingOperator L := by
  obtain ⟨k, L, hL, hcar⟩ := C.exists_fullCyclic_evenHoleLabeling hEven
  refine ⟨k, L, hL, hcar, ?_⟩
  rw [← hcar]
  exact H.evenHoleOperator_eq L hL

/-- For `C₀` an even-hole carrier, every term `h_C`, `C ∈ ⟨C₀⟩`, of the generalized cycle
symmetry is the labelling operator of a full-cyclic labelling of `C` (never the fallback
`0`). -/
theorem exists_fullCyclic_labeling_of_mem_closure [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {C₀ C : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀) (h : InEvenHoleDeformationClosure G C₀ C) :
    ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧ L.carrier = C ∧
      H.evenHoleOperator C = H.labelingOperator L :=
  H.exists_fullCyclic_labeling_evenHoleOperator (h.isEvenHoleCarrier hC₀)

/-! ### Token-sliding charges and generalized cycle symmetries -/

/-- Definition 14 (v1 L783): the token-sliding charge `q_{k,μ} = Σ_{S ∈ μ} h_S` of a
component `μ ∈ Ξ_k` of the token-sliding solution graph. -/
noncomputable def tokenSlidingChargeOp [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (k : ℕ) (μ : G.TokenSlidingComponent k) : A :=
  G.tokenSlidingCharge k (fun S => H.independentProduct S.1) μ

/-- Definition 15 (v1 L799): the generalized cycle symmetry `J_{C₀} = Σ_{C ∈ ⟨C₀⟩} h_C`.
The manuscript defines it for an even hole `C₀`; theorems about it should assume
`G.IsEvenHoleCarrier C₀`. -/
noncomputable def generalizedCycleSymmetryOp [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (C₀ : Set V) : A :=
  G.generalizedCycleSymmetry C₀ H.evenHoleOperator

/-- `J_{C₀}` only depends on the deformation closure `⟨C₀⟩`. -/
theorem generalizedCycleSymmetryOp_eq_of_mem [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {C₀ C₁ : Set V}
    (h : InEvenHoleDeformationClosure G C₀ C₁) :
    H.generalizedCycleSymmetryOp C₀ = H.generalizedCycleSymmetryOp C₁ :=
  G.generalizedCycleSymmetry_eq_of_mem H.evenHoleOperator h

/-- The token-sliding charges sum to the independent-set charge:
`Σ_{μ ∈ Ξ_k} q_{k,μ} = Q^(k)` (v1 L788). -/
theorem sum_tokenSlidingChargeOp [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (k : ℕ) :
    ∑ μ ∈ G.tokenSlidingComponentFinset k, H.tokenSlidingChargeOp k μ =
      G.operatorIndependentSetChargeFull H.toOperatorModel k := by
  classical
  unfold tokenSlidingChargeOp
  rw [G.sum_tokenSlidingCharge_eq_independentSetCharge]
  unfold independentSetCharge operatorIndependentSetChargeFull operatorIndependentSetCharge
  refine (Finset.sum_subtype (G.independentFinsetsOfCardAvoid ∅ k) (fun S => ?_)
    (fun S => H.independentProduct S)).symm
  rw [mem_independentFinsetsOfCardAvoid]
  constructor
  · rintro ⟨hc, hi, -⟩
    exact ⟨hi, hc⟩
  · rintro ⟨hi, hc⟩
    exact ⟨hc, hi, by simp⟩

/-- `Q^(1) = H` (v1 Def. 4, L516): the independent sets of size one are the singletons and
`h_{{j}} = h_j`. -/
theorem operatorIndependentSetChargeFull_one [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) :
    G.operatorIndependentSetChargeFull H.toOperatorModel 1 = H.hamiltonian := by
  classical
  have hset : G.independentFinsetsOfCardAvoid ∅ 1 =
      Finset.univ.image (fun j : V => ({j} : Finset V)) := by
    ext S
    rw [mem_independentFinsetsOfCardAvoid, Finset.mem_image]
    constructor
    · rintro ⟨hc, -, -⟩
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
      exact ⟨j, Finset.mem_univ _, rfl⟩
    · rintro ⟨j, -, rfl⟩
      exact ⟨Finset.card_singleton j, by simp, by simp⟩
  unfold operatorIndependentSetChargeFull operatorIndependentSetCharge
  rw [hset, Finset.sum_image (fun x _ y _ h => by simpa using h)]
  unfold hamiltonian
  refine Finset.sum_congr rfl fun j _ => ?_
  show H.independentProduct {j} = H.term j
  have hs : G.IsIndepSet (({j} : Finset V) : Set V) := by simp
  rw [H.independentProduct_eq_noncommProd hs]
  simp

/-- The convention of v1 L794 at `k = 0`: there is a single component, with charge `I`. -/
theorem tokenSlidingChargeOp_zero [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (μ : G.TokenSlidingComponent 0) :
    H.tokenSlidingChargeOp 0 μ = 1 := by
  classical
  refine SimpleGraph.ConnectedComponent.ind (fun S₀ => ?_) μ
  have hempty : ∀ S : G.TokenConfiguration 0, S.1 = ∅ := fun S =>
    Finset.card_eq_zero.mp S.2.card_eq
  have hsub : ∀ S T : G.TokenConfiguration 0, S = T := fun S T =>
    Subtype.ext ((hempty S).trans (hempty T).symm)
  unfold tokenSlidingChargeOp tokenSlidingCharge
  rw [Finset.sum_eq_single S₀ (fun S _ hne => (hne (hsub S S₀)).elim)
    (fun h => (h (Finset.mem_univ _)).elim)]
  simp [tokenSlidingComponentMk, hempty S₀, H.independentProduct_empty]

end PauliFrustrationRepresentation

end SimpleGraph
