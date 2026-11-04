import FreeFermionGraphs.SimplicialModeHamiltonian
import FreeFermionGraphs.CliqueChargeCliqueRecursion
import FreeFermionGraphs.IndependenceSeries
import Mathlib.Algebra.Polynomial.Eval.Algebra

/-!
# The weighted independence polynomial and `h_S² = ∏ b_j²`

Manuscript reference: arXiv 2305.15625 v1, Definition 6 (weighted independence
polynomial, L542-547)

`I_G(x) = ∑_{S ∈ 𝒮_G} x^{|S|} ∏_{j ∈ S} b_j²`,

the recursion Eq. (independencepolynomialrecursion) (L551)

`I_G(x) = I_{G∖K}(x) + x ∑_{j ∈ K} b_j² I_{G∖Γ[j]}(x)`   (`K` a clique),

and the fact `h_j² = b_j² I` (L231) in the form `h_S h_S = (∏_{j ∈ S} b_j²) I` for an
independent set `S`, which is what turns Eq. (setsymmetricrepresentation) into
Eq. (cyclesymmetries) (L568) and is used in the proof of Lemma 11 (L1977).

## Conventions

* Following the repository, the deleted graph `G ∖ W` is represented by the ambient
  vertex type together with the deleted carrier `W : Set V`; its independent sets are the
  independent finsets of `G` disjoint from `W`
  (`SimpleGraph.independentFinsetsOfCardAvoid`).  `I_{G∖W}` is
  `weightedIndependencePolynomial b W`, and `I_G` is the case `W = ∅`.
* The polynomial is real-valued, `b : V → ℝ`, as in v1.  Definition 6 sums over all
  independent sets; `weightedIndependencePolynomial` groups them by cardinality
  (`weightedIndependencePolynomial_eq_sum` shows this is Definition 6 literally).
* Nothing is assumed about `b` (in particular no nonvanishing): the recursion is a pure
  counting identity.

## Main results

* `weightedIndependencePolynomial` : `I_{G∖W}(x)` (Definition 6).
* `weightedIndependencePolynomial_eq_sum` : the sum over all independent sets.
* `weightedIndependencePolynomial_singleVertex` : the recursion for a single vertex.
* `weightedIndependencePolynomial_finsetClique`,
  `weightedIndependencePolynomial_clique` : Eq. (independencepolynomialrecursion).
* `weightedIndependencePolynomial_eval₂_eq_indepSeries` : compatibility with the existing
  power-series form `indepSeries` (the substitution `x = -X²`, with the vertex set
  `V ∖ W`).
* `PauliCliqueHamiltonianRepresentation.independentProduct_mul_self` : for an independent
  set `S`, `h_S h_S = (∏_{j ∈ S} b_j²) • 1`.
* `SimplicialModeHamiltonian.independentProduct_mul_self` : the same for the simplicial
  mode model (real couplings).
-/

open Set
open scoped BigOperators

universe u v w
variable {V : Type u}

namespace SimpleGraph

/-! ### The polynomial -/

/-- The weighted independence polynomial of `G ∖ W`, with weights `b_j²`
(v1 Definition 6, L542-547):
`I_{G∖W}(x) = ∑_{S independent, S ∩ W = ∅} x^{|S|} ∏_{j ∈ S} b_j²`.

The independent sets are grouped by their cardinality `k ≤ |V|`, which is the form in
which the charges `Q_{G∖W}^{(k)}` are indexed; `weightedIndependencePolynomial_eq_sum`
gives the sum over all independent sets.  `W = ∅` is `I_G`. -/
noncomputable def weightedIndependencePolynomial
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] (b : V → ℝ) (W : Set V) :
    Polynomial ℝ :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), ∑ S ∈ G.independentFinsetsOfCardAvoid W k,
    Polynomial.C (∏ j ∈ S, b j ^ 2) * Polynomial.X ^ k

/-- The degree-`k` part of `I_{G∖W}`: the contribution of the independent `k`-sets
avoiding `W`. -/
noncomputable def weightedIndependenceLevel
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] (b : V → ℝ) (W : Set V) (k : ℕ) :
    Polynomial ℝ :=
  ∑ S ∈ G.independentFinsetsOfCardAvoid W k,
    Polynomial.C (∏ j ∈ S, b j ^ 2) * Polynomial.X ^ k

theorem weightedIndependencePolynomial_eq_sum_level
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] (b : V → ℝ) (W : Set V) :
    G.weightedIndependencePolynomial b W =
      ∑ k ∈ Finset.range (Fintype.card V + 1), G.weightedIndependenceLevel b W k :=
  rfl

namespace WeightedIndependence

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V]

/-- There is no independent set of more than `|V|` vertices. -/
theorem independentFinsetsOfCardAvoid_eq_empty_of_lt
    {W : Set V} {k : ℕ} (hk : Fintype.card V < k) :
    G.independentFinsetsOfCardAvoid W k = ∅ := by
  ext S
  simp only [mem_independentFinsetsOfCardAvoid, Finset.notMem_empty, iff_false, not_and]
  intro hcard
  have := Finset.card_le_univ S
  omega

/-- The level sum vanishes beyond `|V|`. -/
theorem weightedIndependenceLevel_eq_zero_of_lt
    (b : V → ℝ) {W : Set V} {k : ℕ} (hk : Fintype.card V < k) :
    G.weightedIndependenceLevel b W k = 0 := by
  unfold weightedIndependenceLevel
  rw [independentFinsetsOfCardAvoid_eq_empty_of_lt hk]
  simp

/-- `I_{G∖W}` may be summed over any initial segment of degrees containing
`0, …, |V|`. -/
theorem weightedIndependencePolynomial_eq_sum_range
    (b : V → ℝ) (W : Set V) {M : ℕ} (hM : Fintype.card V + 1 ≤ M) :
    G.weightedIndependencePolynomial b W =
      ∑ k ∈ Finset.range M, G.weightedIndependenceLevel b W k := by
  rw [weightedIndependencePolynomial_eq_sum_level]
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro k hkM hk
  apply weightedIndependenceLevel_eq_zero_of_lt
  simp only [Finset.mem_range, not_lt] at hkM hk
  omega

/-- The only independent `0`-set is `∅`. -/
theorem weightedIndependenceLevel_zero (b : V → ℝ) (W : Set V) :
    G.weightedIndependenceLevel b W 0 = 1 := by
  have h : G.independentFinsetsOfCardAvoid W 0 = {∅} := by
    ext S
    simp only [mem_independentFinsetsOfCardAvoid, Finset.card_eq_zero, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      refine ⟨rfl, ?_, by simp⟩
      simp [SimpleGraph.IsIndepSet]
  unfold weightedIndependenceLevel
  rw [h]
  simp

/-- Level form of the single-vertex recursion: for `j ∉ W`,
`I^{(k+1)}_{G∖W} = I^{(k+1)}_{G∖(W∪{j})} + x b_j² I^{(k)}_{G∖(W∪Γ[j])}`. -/
theorem weightedIndependenceLevel_succ_singleVertex
    (b : V → ℝ) {W : Set V} {j : V} (hjW : j ∉ W) (k : ℕ) :
    G.weightedIndependenceLevel b W (k + 1) =
      G.weightedIndependenceLevel b (W ∪ ({j} : Set V)) (k + 1) +
        Polynomial.C (b j ^ 2) * Polynomial.X *
          G.weightedIndependenceLevel b (W ∪ G.closedNeighborhood j) k := by
  classical
  unfold weightedIndependenceLevel
  rw [independentFinsetsOfCardAvoid_eq_union_singleVertex (j := j) k,
    Finset.sum_union (independentFinsets_singleVertex_disjoint k)]
  congr 1
  rw [independentFinsetsContainingAvoid_eq_image hjW k]
  have hinj : ∀ T₁ ∈ G.independentFinsetsOfCardAvoid (W ∪ G.closedNeighborhood j) k,
      ∀ T₂ ∈ G.independentFinsetsOfCardAvoid (W ∪ G.closedNeighborhood j) k,
        insert j T₁ = insert j T₂ → T₁ = T₂ := by
    intro T₁ hT₁ T₂ hT₂ hEq
    rw [mem_independentFinsetsOfCardAvoid] at hT₁ hT₂
    exact insert_injective_on_avoids_closedNeighborhood
      (fun v hvT hvC => hT₁.2.2 v hvT (Or.inr hvC))
      (fun v hvT hvC => hT₂.2.2 v hvT (Or.inr hvC)) hEq
  rw [Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [mem_independentFinsetsOfCardAvoid] at hT
  have hjT : j ∉ T := fun hjT => hT.2.2 j hjT (Or.inr (by simp [closedNeighborhood]))
  rw [Finset.prod_insert hjT, Polynomial.C_mul, pow_succ]
  ring

end WeightedIndependence

open WeightedIndependence

/-- The single-vertex case of Eq. (independencepolynomialrecursion) (v1 L551), with a
previously deleted carrier `W`: for `j ∉ W`,
`I_{G∖W}(x) = I_{G∖(W∪{j})}(x) + x b_j² I_{G∖(W∪Γ[j])}(x)`. -/
theorem weightedIndependencePolynomial_singleVertex
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] (b : V → ℝ)
    {W : Set V} {j : V} (hjW : j ∉ W) :
    G.weightedIndependencePolynomial b W =
      G.weightedIndependencePolynomial b (W ∪ ({j} : Set V)) +
        Polynomial.C (b j ^ 2) * Polynomial.X *
          G.weightedIndependencePolynomial b (W ∪ G.closedNeighborhood j) := by
  set N := Fintype.card V
  rw [weightedIndependencePolynomial_eq_sum_range b W (M := N + 2) (by omega),
    weightedIndependencePolynomial_eq_sum_range b (W ∪ ({j} : Set V)) (M := N + 2)
      (by omega)]
  rw [G.weightedIndependencePolynomial_eq_sum_level b (W ∪ G.closedNeighborhood j)]
  rw [Finset.sum_range_succ' _ (N + 1), Finset.sum_range_succ' _ (N + 1),
    weightedIndependenceLevel_zero, weightedIndependenceLevel_zero]
  simp_rw [weightedIndependenceLevel_succ_singleVertex b hjW]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Eq. (independencepolynomialrecursion) (v1 L551) for a clique `K` of the deleted graph
`G ∖ W` (the finite-set form):
`I_{G∖W}(x) = I_{G∖(W∪K)}(x) + x ∑_{j ∈ K} b_j² I_{G∖(W∪Γ[j])}(x)`. -/
theorem weightedIndependencePolynomial_finsetClique
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] (b : V → ℝ) {W : Set V}
    (K : Finset V) (hK : G.IsClique (K : Set V)) (hKW : ∀ j ∈ K, j ∉ W) :
    G.weightedIndependencePolynomial b W =
      G.weightedIndependencePolynomial b (W ∪ (K : Set V)) +
        Polynomial.X * ∑ j ∈ K, Polynomial.C (b j ^ 2) *
          G.weightedIndependencePolynomial b (W ∪ G.closedNeighborhood j) := by
  classical
  induction K using Finset.induction_on generalizing W with
  | empty => simp
  | @insert j K hjK ih =>
      have hjW : j ∉ W := hKW j (by simp)
      have hKrest : G.IsClique (K : Set V) := by
        intro a ha b' hb hab
        exact hK (by simp [ha]) (by simp [hb]) hab
      have hRestAvoid : ∀ l ∈ K, l ∉ W ∪ ({j} : Set V) := by
        intro l hl hUnion
        rcases hUnion with hlW | hlj
        · exact hKW l (by simp [hl]) hlW
        · have hljEq : l = j := by simpa using hlj
          subst l
          exact hjK hl
      have hSingle := weightedIndependencePolynomial_singleVertex (G := G) b hjW
      have hIH := ih hKrest hRestAvoid (W := W ∪ ({j} : Set V))
      have hFinalDeletion :
          (W ∪ ({j} : Set V)) ∪ (K : Set V) =
            W ∪ ((insert j K : Finset V) : Set V) := by
        ext v
        simp [or_left_comm, or_comm]
      have hNeighborhoodDeletion :
          ∀ l ∈ K, (W ∪ ({j} : Set V)) ∪ G.closedNeighborhood l =
            W ∪ G.closedNeighborhood l := by
        intro l hl
        have hlj : l ≠ j := by
          intro h
          subst l
          exact hjK hl
        have hadj : G.Adj l j := hK (by simp [hl]) (by simp) hlj
        have hjClosed : j ∈ G.closedNeighborhood l :=
          Set.mem_insert_iff.mpr (Or.inr ((G.mem_neighborSet l j).mpr hadj))
        ext v
        constructor
        · intro hv
          rcases hv with (hvW | hvj) | hvClosed
          · exact Or.inl hvW
          · have hvEq : v = j := by simpa using hvj
            subst v
            exact Or.inr hjClosed
          · exact Or.inr hvClosed
        · intro hv
          rcases hv with hvW | hvClosed
          · exact Or.inl (Or.inl hvW)
          · exact Or.inr hvClosed
      rw [hSingle, hIH, hFinalDeletion]
      have hsum : (∑ l ∈ K, Polynomial.C (b l ^ 2) *
            G.weightedIndependencePolynomial b ((W ∪ ({j} : Set V)) ∪ G.closedNeighborhood l)) =
          ∑ l ∈ K, Polynomial.C (b l ^ 2) *
            G.weightedIndependencePolynomial b (W ∪ G.closedNeighborhood l) := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [hNeighborhoodDeletion l hl]
      rw [hsum, Finset.sum_insert hjK]
      ring

/-- Eq. (independencepolynomialrecursion) (v1 L551) for a set-valued clique `K` of `G`
(no previously deleted vertices):
`I_G(x) = I_{G∖K}(x) + x ∑_{j ∈ K} b_j² I_{G∖Γ[j]}(x)`.  The finite representative
`verticesOfSet K` is only an implementation device for the finite sum. -/
theorem weightedIndependencePolynomial_clique
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] (b : V → ℝ)
    {K : Set V} (hK : G.IsClique K) :
    G.weightedIndependencePolynomial b ∅ =
      G.weightedIndependencePolynomial b K +
        Polynomial.X * ∑ j ∈ verticesOfSet K, Polynomial.C (b j ^ 2) *
          G.weightedIndependencePolynomial b (G.closedNeighborhood j) := by
  have hVertices : (((verticesOfSet K : Finset V) : Set V)) = K := by
    ext v
    simp
  have hFiniteClique : G.IsClique (((verticesOfSet K : Finset V) : Set V)) := by
    rw [hVertices]
    exact hK
  have h := weightedIndependencePolynomial_finsetClique (G := G) b (W := (∅ : Set V))
    (verticesOfSet K) hFiniteClique (fun j _ => by simp)
  rw [hVertices] at h
  simpa using h

/-! ### Definition 6 as a sum over all independent sets -/

/-- The independent finsets of `G ∖ W`: the independent sets of `G` disjoint from the
deleted carrier `W` (the carrier `𝒮_{G∖W}` of v1 Definition 6). -/
noncomputable def independentFinsetsAvoid
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] (W : Set V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun S => G.IsIndepSet (S : Set V) ∧ ∀ v ∈ S, v ∉ W

@[simp]
theorem mem_independentFinsetsAvoid
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] {W : Set V} {S : Finset V} :
    S ∈ G.independentFinsetsAvoid W ↔ G.IsIndepSet (S : Set V) ∧ ∀ v ∈ S, v ∉ W := by
  classical
  simp [independentFinsetsAvoid]

/-- v1 Definition 6 literally: `I_{G∖W}(x) = ∑_{S ∈ 𝒮_{G∖W}} x^{|S|} ∏_{j∈S} b_j²`. -/
theorem weightedIndependencePolynomial_eq_sum
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] (b : V → ℝ) (W : Set V) :
    G.weightedIndependencePolynomial b W =
      ∑ S ∈ G.independentFinsetsAvoid W,
        Polynomial.C (∏ j ∈ S, b j ^ 2) * Polynomial.X ^ S.card := by
  classical
  unfold weightedIndependencePolynomial
  rw [← Finset.sum_fiberwise_of_maps_to (s := G.independentFinsetsAvoid W)
    (t := Finset.range (Fintype.card V + 1)) (g := Finset.card)
    (f := fun S => Polynomial.C (∏ j ∈ S, b j ^ 2) * Polynomial.X ^ S.card)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hfilter : (G.independentFinsetsAvoid W).filter (fun S => S.card = k) =
        G.independentFinsetsOfCardAvoid W k := by
      ext S
      simp only [Finset.mem_filter, mem_independentFinsetsAvoid,
        mem_independentFinsetsOfCardAvoid]
      tauto
    rw [hfilter]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [(mem_independentFinsetsOfCardAvoid.mp hS).1]
  · intro S _
    simpa [Nat.lt_succ_iff] using Finset.card_le_univ S

/-- Compatibility with the power-series form `indepSeries`: substituting `x = -X²` in
`I_{G∖W}` gives the weighted independence series of the vertex set `V ∖ W` with weights
`b_j²`.  (`indepSeries` is used by the Krylov-row closed form.) -/
theorem weightedIndependencePolynomial_eval₂_eq_indepSeries
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] (b : V → ℝ) (W : Set V)
    [DecidablePred (· ∈ W)] :
    (G.weightedIndependencePolynomial b W).eval₂ PowerSeries.C (-(PowerSeries.X ^ 2)) =
      G.indepSeries (fun v => b v ^ 2) (Finset.univ.filter fun v => v ∉ W) := by
  classical
  rw [weightedIndependencePolynomial_eq_sum, Polynomial.eval₂_finsetSum,
    indepSeries_eq_sum]
  refine Finset.sum_congr ?_ fun S _ => ?_
  · ext S
    simp only [mem_independentFinsetsAvoid, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_iff, Finset.mem_univ, true_and]
    tauto
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]

/-! ### `h_S h_S = (∏_{j∈S} b_j²) I` -/

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]

/-- For an independent set `S` of the frustration graph, the canonical product
`h_S = ∏_{j∈S} h_j` squares to the central scalar `∏_{j∈S} b_j²`: `h_S h_S = (∏ b_j²) I`.
This is the fact `h_j² = b_j² I` (v1 L231) extended to independent sets, as used in
Eq. (cyclesymmetries) (v1 L568) and in the proof of Lemma 11 (v1 L1977).  Only the Pauli
setup is needed: the factors of `h_S` commute pairwise, and each squares to `b_j² I`. -/
theorem independentProduct_mul_self
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    H.operator.restrictSome.independentProduct S *
        H.operator.restrictSome.independentProduct S =
      algebraMap R A (∏ j ∈ S, H.coupling j ^ 2) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [H.operator.restrictSome.independentProduct_empty]
      simp
  | insert j S hj ih =>
      have hsub : (S : Set V) ⊆ ((insert j S : Finset V) : Set V) := by
        intro x hx
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx))
      have hS' : G.IsIndepSet (S : Set V) := hS.mono hsub
      have hnonadj : ∀ v ∈ S, ¬G.Adj j v := by
        intro v hv hadj
        have hjmem : j ∈ ((insert j S : Finset V) : Set V) := by simp
        have hvmem : v ∈ ((insert j S : Finset V) : Set V) := by simp [hv]
        exact hS hjmem hvmem (fun h => hj (h ▸ hv)) hadj
      set M := H.operator.restrictSome with hM
      have hleft := M.independentProduct_insert_left hj hS' hnonadj
      have hright := M.independentProduct_insert_right hj hS' hnonadj
      have hterm : M.term j * M.term j = algebraMap R A (H.coupling j ^ 2) :=
        H.original_term_sq j
      calc M.independentProduct (insert j S) * M.independentProduct (insert j S)
          = (M.term j * M.independentProduct S) * (M.independentProduct S * M.term j) := by
            rw [← hleft, ← hright]
        _ = M.term j * (M.independentProduct S * M.independentProduct S) * M.term j := by
            simp only [mul_assoc]
        _ = M.term j * algebraMap R A (∏ i ∈ S, H.coupling i ^ 2) * M.term j := by
            rw [ih hS']
        _ = algebraMap R A (∏ i ∈ S, H.coupling i ^ 2) * (M.term j * M.term j) := by
            rw [← Algebra.commutes (∏ i ∈ S, H.coupling i ^ 2) (M.term j)]
            simp only [mul_assoc]
        _ = algebraMap R A (∏ i ∈ insert j S, H.coupling i ^ 2) := by
            rw [hterm, ← map_mul, Finset.prod_insert hj, mul_comm]

end PauliCliqueHamiltonianRepresentation

namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]

/-- `h_S h_S = (∏_{j∈S} b_j²) I` for an independent set `S` in the simplicial-mode model
(real couplings); see `PauliCliqueHamiltonianRepresentation.independentProduct_mul_self`. -/
theorem independentProduct_mul_self (H : G.SimplicialModeHamiltonian Ks A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    H.frustration.independentProduct S * H.frustration.independentProduct S =
      algebraMap ℝ A (∏ j ∈ S, H.coupling j ^ 2) :=
  H.toPauliCliqueHamiltonianRepresentation.independentProduct_mul_self hS

end SimplicialModeHamiltonian

end SimpleGraph
