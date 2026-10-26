import FreeFermionGraphs.PauliPathOperator

/-!
# Sign calculus for ordered and independent products of Hamiltonian terms

This module formalises the elementary commutation bookkeeping on which the
proof of Theorem 1(i) of the manuscript (arXiv 2305.15625 v1, "Independent Set
Charges", proof at L882-892) rests.

* Eq. (`degreephase`, v1 L273): the term `h_j` and a product `h_U` over a vertex
  set `U` commute up to the sign `(-1)^(Δ_U(j))`, where `Δ_U(j)` is the number
  of neighbours of `j` in `U`.
* Eq. (`symmetricdifference`, v1 L277): the sign exponent is additive modulo two
  under symmetric difference in `U`.
* v1 L887-892: for independent sets `S, S'` one has
  `h_S h_{S'} = (-1)^{Σ_{j ∈ S} Δ_{S'}(j)} h_{S'} h_S`.

The model is `SimpleGraph.PauliFrustrationRepresentation`: arbitrary ring-valued
terms with `Adj ↔ anticommute` and non-adjacent terms commuting.  No Pauli
matrices, Hermiticity or squares are involved.

The quantity `Σ_{j ∈ S} Δ_{S'}(j)` is `SimpleGraph.crossCount G S S'`, the number
of ordered pairs `(x, y) ∈ S × S'` with `x ~ y`.  (v1 identifies it with
`|E[S ⊕ S']|` for independent `S, S'`; we record the intermediate reduction
`crossCount G S S' = crossCount G (S \ S') (S' \ S)` but do not introduce the
edge-count form.)

Beyond the statements needed for v1 Theorem 1(i) the module proves the product
factorisation `h_S h_T = (h_{S ∩ T})² h_{S \ T} h_{T \ S}` for independent
`S, T` (the factorisation used at v1 L1944-1948, in the appendix proof of the
generalized characteristic polynomial, Lemma `generalizedcharacteristicpolynomial`).
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Number of ordered pairs `(x, y) ∈ S × T` with `x ~ y` in `G`.

For independent `S, T` this is the exponent `Σ_{j ∈ S} Δ_T(j)` of v1 (proof of
Theorem 1(i), L887-891).  The definition is noncomputable so public sign
theorems do not carry a choice of decidable adjacency as data. -/
noncomputable def crossCount (G : SimpleGraph V) (S T : Finset V) : ℕ := by
  classical exact ((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card

/-- The cross count unfolds, for any decidable adjacency, to the cardinality of
the filtered product. -/
theorem crossCount_eq_card_filter [DecidableRel G.Adj] (S T : Finset V) :
    G.crossCount S T = ((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card := by
  unfold crossCount
  congr

/-- The cross count is the double sum of adjacency indicators. -/
theorem crossCount_eq_sum_sum [DecidableRel G.Adj] (S T : Finset V) :
    G.crossCount S T = ∑ s ∈ S, ∑ t ∈ T, if G.Adj s t then 1 else 0 := by
  rw [crossCount_eq_card_filter, Finset.card_filter, Finset.sum_product]

/-- The cross count, summed over the first set, of the neighbour counts in the
second set. -/
theorem crossCount_eq_sum_card_filter [DecidableRel G.Adj] (S T : Finset V) :
    G.crossCount S T = ∑ s ∈ S, (T.filter (G.Adj s)).card := by
  rw [crossCount_eq_sum_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

/-- Number of neighbours of `j` in a finset is the neighbour count over the
canonical list of its elements. -/
theorem listNeighborCount_toList_eq_card_filter [DecidableRel G.Adj]
    (j : V) (T : Finset V) :
    PauliFrustrationRepresentation.listNeighborCount G j T.toList =
      (T.filter (G.Adj j)).card := by
  classical
  unfold PauliFrustrationRepresentation.listNeighborCount
  have h := Multiset.coe_countP (G.Adj j) T.toList
  rw [Finset.coe_toList, Multiset.countP_eq_card_filter] at h
  convert h.symm
  rfl

/-- `crossCount` as the sum of `listNeighborCount`s over the canonical list of
the second set. -/
theorem crossCount_eq_sum_listNeighborCount (S T : Finset V) :
    G.crossCount S T =
      (S.toList.map fun j =>
        PauliFrustrationRepresentation.listNeighborCount G j T.toList).sum := by
  classical
  rw [Finset.sum_map_toList, crossCount_eq_sum_card_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [listNeighborCount_toList_eq_card_filter]

/-- Symmetry of the cross count (the relation `Adj` is symmetric). -/
theorem crossCount_comm (S T : Finset V) :
    G.crossCount S T = G.crossCount T S := by
  classical
  rw [crossCount_eq_sum_sum, crossCount_eq_sum_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [G.adj_comm]

/-- Exact additivity of the cross count under symmetric difference in the second
argument: the symmetric difference counts the common part twice too little. -/
theorem crossCount_symmDiff_right_add [DecidableEq V] (X Y Z : Finset V) :
    G.crossCount X (symmDiff Y Z) + 2 * G.crossCount X (Y ∩ Z) =
      G.crossCount X Y + G.crossCount X Z := by
  classical
  simp only [crossCount_eq_sum_card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- Pointwise identity for a fixed `x`, with `A = N(x) ∩ Y` and `B = N(x) ∩ Z`.
  set A := Y.filter (G.Adj x) with hA
  set B := Z.filter (G.Adj x) with hB
  have h1 : (symmDiff Y Z).filter (G.Adj x) = (A \ B) ∪ (B \ A) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_union,
      Finset.mem_sdiff, hA, hB]
    tauto
  have h2 : (Y ∩ Z).filter (G.Adj x) = A ∩ B := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter, hA, hB]
    tauto
  have hdisj : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  rw [h1, h2, Finset.card_union_of_disjoint hdisj]
  have hAB := Finset.card_sdiff_add_card_inter A B
  have hBA := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hBA
  omega

/-- Parity additivity of the cross count under symmetric difference in the
second argument (v1 Eq. `symmetricdifference`, L277, in sign-exponent form). -/
theorem crossCount_symmDiff_right_mod_two [DecidableEq V] (X Y Z : Finset V) :
    G.crossCount X (symmDiff Y Z) % 2 = (G.crossCount X Y + G.crossCount X Z) % 2 := by
  have h := G.crossCount_symmDiff_right_add X Y Z
  omega

/-- Parity additivity of the cross count under symmetric difference in the first
argument. -/
theorem crossCount_symmDiff_left_mod_two [DecidableEq V] (X Y Z : Finset V) :
    G.crossCount (symmDiff Y Z) X % 2 = (G.crossCount Y X + G.crossCount Z X) % 2 := by
  rw [crossCount_comm, crossCount_comm Y X, crossCount_comm Z X]
  exact G.crossCount_symmDiff_right_mod_two X Y Z

/-- For independent `S, T`, every edge of `S × T` joins `S \ T` to `T \ S`:
a vertex of `S ∩ T` has no neighbour in `S ∪ T`.  Hence the cross count equals
that of the symmetric-difference halves (v1 L887-889). -/
theorem crossCount_eq_sdiff_sdiff [DecidableEq V] {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V)) :
    G.crossCount S T = G.crossCount (S \ T) (T \ S) := by
  classical
  rw [crossCount_eq_card_filter, crossCount_eq_card_filter]
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hx, hy⟩, hadj⟩
    refine ⟨⟨⟨hx, fun hxT => ?_⟩, hy, fun hyS => ?_⟩, hadj⟩
    · -- `x ∈ T` and `y ∈ T` adjacent contradicts independence of `T`
      have hne : x ≠ y := hadj.ne
      exact hT (Finset.mem_coe.mpr hxT) (Finset.mem_coe.mpr hy) hne hadj
    · have hne : x ≠ y := hadj.ne
      exact hS (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hyS) hne hadj
  · rintro ⟨⟨⟨hx, _⟩, hy, _⟩, hadj⟩
    exact ⟨⟨hx, hy⟩, hadj⟩

/-- A subset of an independent finset is independent. -/
theorem IsIndepSet.finset_subset {S T : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hTS : T ⊆ S) : G.IsIndepSet (T : Set V) :=
  Set.Pairwise.mono (Finset.coe_subset.mpr hTS) hS

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- Powers of `-1` are central. -/
theorem neg_one_pow_commute (n : ℕ) (x : A) :
    Commute ((-1 : A) ^ n) x :=
  (Commute.neg_one_left x).pow_left n

/-- Product of the terms along two vertex lists commute up to the sign
`(-1)^{#{(x, y) ∈ L₁ × L₂ : x ~ y}}`, written as the sum over `L₁` of the
neighbour counts in `L₂` (v1 Eq. `degreephase`, L273, iterated over the first
factor). -/
theorem listOperator_mul_listOperator (H : G.PauliFrustrationRepresentation A)
    (L₁ L₂ : List V) :
    H.listOperator L₁ * H.listOperator L₂ =
      (-1 : A) ^ (L₁.map fun j => listNeighborCount G j L₂).sum *
        (H.listOperator L₂ * H.listOperator L₁) := by
  induction L₁ with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, pow_add]
      set a := (xs.map fun j => listNeighborCount G j L₂).sum with ha
      set b := listNeighborCount G x L₂ with hb
      calc
        H.listOperator (x :: xs) * H.listOperator L₂ =
            H.term x * (H.listOperator xs * H.listOperator L₂) := by
              rw [listOperator_cons, mul_assoc]
        _ = H.term x * ((-1 : A) ^ a *
              (H.listOperator L₂ * H.listOperator xs)) := by rw [ih]
        _ = (-1 : A) ^ a *
              (H.term x * H.listOperator L₂ * H.listOperator xs) := by
              rw [(neg_one_pow_commute a (H.term x)).symm.left_comm, mul_assoc]
        _ = (-1 : A) ^ a * ((-1 : A) ^ b *
              (H.listOperator L₂ * H.term x) * H.listOperator xs) := by
              rw [hb, H.term_mul_listOperator]
        _ = (-1 : A) ^ b * (-1 : A) ^ a *
              (H.listOperator L₂ * H.listOperator (x :: xs)) := by
              rw [listOperator_cons]
              simp only [mul_assoc]
              rw [← mul_assoc ((-1 : A) ^ a) ((-1 : A) ^ b),
                (neg_one_pow_commute a ((-1 : A) ^ b)).eq, mul_assoc]

/-- On an independent finset the canonical product is the ordered list product
along the canonical enumeration `Finset.toList`. -/
theorem independentProduct_eq_listOperator_toList
    (H : G.PauliFrustrationRepresentation A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    H.independentProduct S = H.listOperator S.toList := by
  classical
  rw [H.independentProduct_eq_noncommProd hS]
  have hcomm := H.independent_pairwise_commute hS
  have hcongr :
      S.noncommProd H.term hcomm =
        S.toList.toFinset.noncommProd H.term
          (by rw [Finset.toList_toFinset]; exact hcomm) :=
    Finset.noncommProd_congr (Finset.toList_toFinset S).symm (fun _ _ => rfl) _
  rw [hcongr, Finset.noncommProd_toFinset _ _ _ S.nodup_toList]
  rfl

/-- Moving the term `h_j` across the product `h_U` over an independent set `U`
produces the sign `(-1)^{Δ_U(j)}` (v1 Eq. `degreephase`, L273), where
`Δ_U(j) = crossCount G {j} U` is the number of neighbours of `j` in `U`. -/
theorem term_mul_independentProduct [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (j : V)
    {U : Finset V} (hU : G.IsIndepSet (U : Set V)) :
    H.term j * H.independentProduct U =
      (-1 : A) ^ G.crossCount {j} U *
        (H.independentProduct U * H.term j) := by
  rw [H.independentProduct_eq_listOperator_toList hU,
    H.term_mul_listOperator, G.crossCount_eq_sum_listNeighborCount]
  simp

/-- Two independent-set products commute up to the sign
`(-1)^{c(S,T)}`, `c(S,T) = #{(x, y) ∈ S × T : x ~ y}` (v1 proof of Theorem 1(i),
L887-891; the exponent is `Σ_{j ∈ S} Δ_T(j)`). -/
theorem independentProduct_mul_independentProduct [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V)) :
    H.independentProduct S * H.independentProduct T =
      (-1 : A) ^ G.crossCount S T *
        (H.independentProduct T * H.independentProduct S) := by
  rw [H.independentProduct_eq_listOperator_toList hS,
    H.independentProduct_eq_listOperator_toList hT,
    H.listOperator_mul_listOperator, G.crossCount_eq_sum_listNeighborCount]

/-- Even cross count: the two independent-set products commute. -/
theorem independentProduct_mul_independentProduct_of_even [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (heven : Even (G.crossCount S T)) :
    H.independentProduct S * H.independentProduct T =
      H.independentProduct T * H.independentProduct S := by
  rw [H.independentProduct_mul_independentProduct hS hT, heven.neg_one_pow, one_mul]

/-- Odd cross count: the two independent-set products anticommute (the
situation `|E[S ⊕ S']|` odd in v1 L883-892). -/
theorem independentProduct_mul_independentProduct_of_odd [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hodd : Odd (G.crossCount S T)) :
    H.independentProduct S * H.independentProduct T =
      -(H.independentProduct T * H.independentProduct S) := by
  rw [H.independentProduct_mul_independentProduct hS hT, hodd.neg_one_pow, neg_one_mul]

/-- The product over a disjoint union that is independent splits as the product
of the two products (a case of `Finset.noncommProd_union_of_disjoint`). -/
theorem independentProduct_union [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    {S T : Finset V} (hST : Disjoint S T)
    (hU : G.IsIndepSet ((S ∪ T : Finset V) : Set V)) :
    H.independentProduct (S ∪ T) =
      H.independentProduct S * H.independentProduct T := by
  have hS : G.IsIndepSet (S : Set V) :=
    IsIndepSet.finset_subset hU Finset.subset_union_left
  have hT : G.IsIndepSet (T : Set V) :=
    IsIndepSet.finset_subset hU Finset.subset_union_right
  rw [H.independentProduct_eq_noncommProd hU, H.independentProduct_eq_noncommProd hS,
    H.independentProduct_eq_noncommProd hT]
  exact Finset.noncommProd_union_of_disjoint hST H.term _

/-- The products over two disjoint finsets whose union is independent commute
(both equal the product over the union). -/
theorem independentProduct_comm_of_union [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    {S T : Finset V} (hST : Disjoint S T)
    (hU : G.IsIndepSet ((S ∪ T : Finset V) : Set V)) :
    H.independentProduct S * H.independentProduct T =
      H.independentProduct T * H.independentProduct S := by
  have hU' : G.IsIndepSet ((T ∪ S : Finset V) : Set V) := by
    rwa [Finset.union_comm]
  rw [← H.independentProduct_union hST hU, ←
    H.independentProduct_union hST.symm hU', Finset.union_comm]

/-- Factorisation of a product of two independent-set products:
`h_S h_T = (h_{S ∩ T})² h_{S \ T} h_{T \ S}` (v1 L1944-1948, the displayed
identity in the proof for the partition function; there it is justified by the
fact that the factors `h_j`, `j ∈ S ∩ T`, commute with every factor of
`h_S h_T`).  Here it follows from `h_S = h_{S ∩ T} h_{S \ T} = h_{S \ T} h_{S ∩ T}`
and `h_T = h_{S ∩ T} h_{T \ S}`. -/
theorem independentProduct_mul_eq [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V)) :
    H.independentProduct S * H.independentProduct T =
      (H.independentProduct (S ∩ T) * H.independentProduct (S ∩ T)) *
        (H.independentProduct (S \ T) * H.independentProduct (T \ S)) := by
  have hdisjS : Disjoint (S ∩ T) (S \ T) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have hdisjT : Disjoint (S ∩ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).1
  have hunS : S ∩ T ∪ S \ T = S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hunT : S ∩ T ∪ T \ S = T := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hIA : G.IsIndepSet ((S ∩ T ∪ S \ T : Finset V) : Set V) := by
    rw [hunS]; exact hS
  have hIB : G.IsIndepSet ((S ∩ T ∪ T \ S : Finset V) : Set V) := by
    rw [hunT]; exact hT
  have hS1 := H.independentProduct_union hdisjS hIA
  have hT1 := H.independentProduct_union hdisjT hIB
  have hcomm := H.independentProduct_comm_of_union hdisjS hIA
  rw [hunS] at hS1
  rw [hunT] at hT1
  rw [hS1, hT1]
  calc
    H.independentProduct (S ∩ T) * H.independentProduct (S \ T) *
        (H.independentProduct (S ∩ T) * H.independentProduct (T \ S)) =
      H.independentProduct (S ∩ T) *
        (H.independentProduct (S \ T) * H.independentProduct (S ∩ T)) *
          H.independentProduct (T \ S) := by
      simp only [mul_assoc]
    _ = H.independentProduct (S ∩ T) *
        (H.independentProduct (S ∩ T) * H.independentProduct (S \ T)) *
          H.independentProduct (T \ S) := by
      rw [← hcomm]
    _ = _ := by simp only [mul_assoc]

end PauliFrustrationRepresentation
end SimpleGraph
