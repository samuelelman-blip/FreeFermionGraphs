import FreeFermionGraphs.SimplicialModeHamiltonian
import FreeFermionGraphs.CliqueChargeCliqueRecursion
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

/-!
# The transfer operator `T_{G∖W}(u)` and its recursions

Manuscript (arXiv 2305.15625 v1) Definition 5 (transfer operator, L532-540):
the transfer operator is the generating function of the independent set charges,

`T_G(u) = ∑_{S ∈ 𝒮_G} (-u)^{|S|} h_S = ∑_{k=0}^{α(G)} (-u)^k Q_G^(k)`.

Here `PauliFrustrationRepresentation.transfer H W u` is the transfer operator
`T_{G∖W}(u)` of the vertex-deleted induced graph `G ∖ W`, built from the deleted
charges `Q_{G∖W}^(k)` (`PauliFrustrationRepresentation.deletedCharge`).

* `transfer` : `T_{G∖W}(u) = ∑_{k ≤ |V|} (-u)^k Q_{G∖W}^(k)`.  The sum over
  `k ≤ |V|` equals the sum over `k ≤ α(G)` of v1 because the charges vanish above
  the independence number (`transfer_eq_sum_range_of_card_lt`).
* `transfer_zero` : `T_{G∖W}(0) = 1`.
* `transfer_clique` : Eq. (transfermatrixrecursion) (v1 L550), for an arbitrary
  clique `K`, `T_G = T_{G∖K} - u ∑_{j ∈ K} h_j T_{G∖Γ[j]}`; its deleted-carrier
  form is `transfer_finsetClique`.
* `transfer_simplicial` : the generating-function form of v1 Lemma 18
  (`kjrecursion`, L1992-2018; the repository's `paperLemma17`), for a simplicial
  clique `Ks`, `T_G = T_{G∖Ks} - u ∑_{j ∈ Ks} T_{G∖K_j} h_j`.
* `transfer_adjoinRoot` : for the root-adjoined graph `G⁺`, whose extra vertex
  `none` carries the simplicial mode `χ` (v1 Definition 8, L588),
  `T_{G⁺}(u) = T_G(u) - u χ T_{G∖Ks}(u)`.

Deliberate generalisation: v1 takes the spectral parameter `u` real.  Here `u`
lies in an arbitrary commutative ring `R` acting on the operator ring `A`
(`[CommRing R] [Algebra R A]`); the exact solution later needs complex `u`.
All the results are purely algebraic: they use neither claw-freeness nor
commutation of the charges, only the recursions for the charges.
-/

open Set Finset
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- The transfer operator `T_{G∖W}(u) = ∑_k (-u)^k Q_{G∖W}^(k)` of the
vertex-deleted induced graph `G ∖ W` (v1 Definition 5, L532-540).  The sum runs
over `k ≤ |V|`; this agrees with the sum over `k ≤ α(G)` of v1 because the
charges vanish above the independence number.  The spectral parameter `u` lies
in a commutative ring `R` acting on `A` (v1: `u ∈ ℝ`). -/
noncomputable def transfer [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra R A]
    (H : G.PauliFrustrationRepresentation A) (W : Set V) (u : R) : A :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), (-u) ^ k • H.deletedCharge W k

section Transfer

variable [Fintype V] [DecidableEq V]
variable {R : Type*} [CommRing R] [Algebra R A]

/-- `Q_G^(k)` is the deleted charge with nothing deleted. -/
theorem deletedCharge_empty (H : G.PauliFrustrationRepresentation A) (k : ℕ) :
    H.deletedCharge ∅ k = H.charge k :=
  rfl

/-- `Q_{G∖W}^(0) = 1` for every deleted carrier `W`. -/
theorem deletedCharge_zero (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    H.deletedCharge W 0 = 1 :=
  operatorIndependentSetCharge_zero H.toOperatorModel W

/-- Since the charges vanish above `|V|`, the sum defining `T_{G∖W}(u)` may be
extended to any range `0 ≤ k < n` with `|V| < n`. -/
theorem transfer_eq_sum_range_of_card_lt (H : G.PauliFrustrationRepresentation A)
    (W : Set V) (u : R) {n : ℕ} (hn : Fintype.card V < n) :
    H.transfer W u = ∑ k ∈ Finset.range n, (-u) ^ k • H.deletedCharge W k := by
  unfold transfer
  refine Finset.sum_subset (Finset.range_subset_range.mpr hn) (fun k hk hk' => ?_)
  rw [Finset.mem_range] at hk hk'
  rw [H.deletedCharge_eq_zero_of_card_lt W (by omega), smul_zero]

/-- `T_{G∖W}(0) = 1`: only the `k = 0` term survives, and `Q^(0) = 1`
(v1 Definition 5, L532-540). -/
theorem transfer_zero (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    H.transfer W (0 : R) = 1 := by
  unfold transfer
  rw [Finset.sum_range_succ']
  simp [H.deletedCharge_zero W]

/-! ### The generating-function step -/

/-- Generating function of a charge recursion.  If `c (k+1) = d (k+1) + e k` for
all `k` and `c 0 = d 0`, then
`∑_{k<n+1} (-u)^k c_k = ∑_{k<n+1} (-u)^k d_k - u ∑_{k<n} (-u)^k e_k`. -/
theorem sum_range_smul_recursion (u : R) (c d e : ℕ → A) (hc0 : c 0 = d 0)
    (hrec : ∀ k, c (k + 1) = d (k + 1) + e k) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-u) ^ k • c k =
      ∑ k ∈ Finset.range (n + 1), (-u) ^ k • d k -
        u • ∑ k ∈ Finset.range n, (-u) ^ k • e k := by
  rw [Finset.sum_range_succ' (fun k => (-u) ^ k • c k),
    Finset.sum_range_succ' (fun k => (-u) ^ k • d k), Finset.smul_sum]
  have key : ∀ k ∈ Finset.range n, (-u) ^ (k + 1) • c (k + 1) =
      (-u) ^ (k + 1) • d (k + 1) - u • (-u) ^ k • e k := by
    intro k _
    have hs : (-u) ^ (k + 1) • e k = -(u • (-u) ^ k • e k) := by
      rw [pow_succ', mul_smul, neg_smul]
    rw [hrec, smul_add, hs]
    abel
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, hc0]
  simp only [pow_zero, one_smul]
  abel

/-- Transfer-operator form of a charge recursion `Q_{G∖W}^(k+1) = Q_{G∖W'}^(k+1) + E_k`
(valid for all `k`): `T_{G∖W}(u) = T_{G∖W'}(u) - u ∑_{k ≤ |V|} (-u)^k E_k`. -/
theorem transfer_eq_sub_of_charge_recursion (H : G.PauliFrustrationRepresentation A)
    {W W' : Set V} {E : ℕ → A}
    (hrec : ∀ k, H.deletedCharge W (k + 1) = H.deletedCharge W' (k + 1) + E k)
    (u : R) :
    H.transfer W u = H.transfer W' u -
      u • ∑ k ∈ Finset.range (Fintype.card V + 1), (-u) ^ k • E k := by
  have hn : Fintype.card V < Fintype.card V + 1 + 1 := by omega
  rw [H.transfer_eq_sum_range_of_card_lt W u hn,
    H.transfer_eq_sum_range_of_card_lt W' u hn]
  refine sum_range_smul_recursion u _ _ E ?_ hrec (Fintype.card V + 1)
  rw [H.deletedCharge_zero W, H.deletedCharge_zero W']

/-- Interchanging the sums over `k` and `j` with `h_j` multiplying on the left. -/
theorem sum_range_smul_sum_mul_left {ι : Type*} (u : R) (n : ℕ) (s : Finset ι)
    (a : ι → A) (q : ι → ℕ → A) :
    ∑ k ∈ Finset.range n, (-u) ^ k • ∑ j ∈ s, a j * q j k =
      ∑ j ∈ s, a j * ∑ k ∈ Finset.range n, (-u) ^ k • q j k := by
  simp only [Finset.smul_sum, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_comm

/-- Interchanging the sums over `k` and `j` with `h_j` multiplying on the right. -/
theorem sum_range_smul_sum_mul_right {ι : Type*} (u : R) (n : ℕ) (s : Finset ι)
    (a : ι → A) (q : ι → ℕ → A) :
    ∑ k ∈ Finset.range n, (-u) ^ k • ∑ j ∈ s, q j k * a j =
      ∑ j ∈ s, (∑ k ∈ Finset.range n, (-u) ^ k • q j k) * a j := by
  simp only [Finset.smul_sum, Finset.sum_mul, smul_mul_assoc]
  exact Finset.sum_comm

/-! ### Clique recursions -/

/-- Eq. (transfermatrixrecursion) (v1 L550) with an arbitrary previously deleted
carrier `W`, for a finite clique `K` disjoint from `W`:
`T_{G∖W} = T_{G∖(W∪K)} - u ∑_{j ∈ K} h_j T_{G∖(W∪Γ[j])}`.

The hypothesis `K ∩ W = ∅` is that of the charge recursion
`operatorIndependentSetCharge_finsetClique`, which it uses. -/
theorem transfer_finsetClique (H : G.PauliFrustrationRepresentation A)
    {W : Set V} (K : Finset V) (hK : G.IsClique (K : Set V))
    (hKW : ∀ j ∈ K, j ∉ W) (u : R) :
    H.transfer W u = H.transfer (W ∪ ↑K) u -
      u • ∑ j ∈ K, H.term j * H.transfer (W ∪ G.closedNeighborhood j) u := by
  have h := H.transfer_eq_sub_of_charge_recursion (W := W) (W' := W ∪ ↑K)
    (E := fun k => ∑ j ∈ K, H.term j * H.deletedCharge (W ∪ G.closedNeighborhood j) k)
    (fun k => operatorIndependentSetCharge_finsetClique H.toOperatorModel K hK hKW k) u
  rw [h, sum_range_smul_sum_mul_left]
  rfl

/-- Eq. (transfermatrixrecursion) (v1 L550), exactly as printed, for an arbitrary
clique `K ⊆ V`:
`T_G = T_{G∖K} - u ∑_{j ∈ K} h_j T_{G∖Γ[j]}`. -/
theorem transfer_clique (H : G.PauliFrustrationRepresentation A)
    {K : Set V} (hK : G.IsClique K) (u : R) :
    H.transfer ∅ u = H.transfer K u -
      u • ∑ j ∈ verticesOfSet K, H.term j * H.transfer (G.closedNeighborhood j) u := by
  have h := H.transfer_eq_sub_of_charge_recursion (W := ∅) (W' := K)
    (E := fun k => ∑ j ∈ verticesOfSet K,
      H.term j * H.deletedCharge (G.closedNeighborhood j) k)
    (fun k => operatorIndependentSetCharge_clique H.toOperatorModel hK k) u
  rw [h, sum_range_smul_sum_mul_left]
  rfl

/-- The generating-function form of v1 Lemma 18 (`kjrecursion`, L1992-2018; the
repository's `paperLemma17`): for a simplicial clique `Ks`, with
`K_j = Γ[j] ∖ (Ks ∖ {j})`,
`T_G = T_{G∖Ks} - u ∑_{j ∈ Ks} T_{G∖K_j} h_j`.

This needs only the simplicial clique, not claw-freeness. -/
theorem transfer_simplicial (H : G.PauliFrustrationRepresentation A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks) (u : R) :
    H.transfer ∅ u = H.transfer Ks u -
      u • ∑ j ∈ verticesOfSet Ks, H.transfer (G.lemma17CliqueAt Ks j) u * H.term j := by
  have h := H.transfer_eq_sub_of_charge_recursion (W := ∅) (W' := Ks)
    (E := fun k => ∑ j ∈ verticesOfSet Ks,
      H.deletedCharge (G.lemma17CliqueAt Ks j) k * H.term j)
    (fun k => H.paperLemma17 hKs k) u
  rw [h, sum_range_smul_sum_mul_right]
  rfl

/-! ### The root-adjoined graph -/

/-- For the root-adjoined graph `G⁺ = G.adjoinRootAt K`, whose extra vertex `none`
carries the simplicial mode `χ` (v1 Definition 8, L588), the transfer operator
satisfies `T_{G⁺}(u) = T_G(u) - u χ T_{G∖Ks}(u)` (Eq. (50) at the vertex `χ`,
whose closed neighbourhood is `{χ} ∪ Ks`).  Here `T_G` and `T_{G∖Ks}` are the
transfer operators of the restricted representation `Hp.restrictSome`. -/
theorem transfer_adjoinRoot {K : Set V}
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) (u : R) :
    Hp.transfer ∅ u = Hp.restrictSome.transfer ∅ u -
      u • (Hp.term none * Hp.restrictSome.transfer K u) := by
  have hn : Fintype.card (Option V) = Fintype.card V + 1 := Fintype.card_option
  have h0 : Hp.charge 0 = Hp.restrictSome.charge 0 := by
    rw [Hp.charge_zero, Hp.restrictSome.charge_zero]
  have hsum := sum_range_smul_recursion u (fun k => Hp.charge k)
    (fun k => Hp.restrictSome.charge k)
    (fun k => Hp.term none * Hp.restrictSome.deletedCharge K k) h0
    (fun k => Hp.charge_succ_adjoinRoot k) (Fintype.card V + 1)
  have hL : Hp.transfer ∅ u =
      ∑ k ∈ Finset.range (Fintype.card V + 1 + 1), (-u) ^ k • Hp.charge k := by
    unfold transfer
    rw [hn]
    rfl
  have hR : Hp.restrictSome.transfer ∅ u =
      ∑ k ∈ Finset.range (Fintype.card V + 1 + 1), (-u) ^ k • Hp.restrictSome.charge k :=
    Hp.restrictSome.transfer_eq_sum_range_of_card_lt ∅ u (by omega)
  have hK : Hp.restrictSome.transfer K u =
      ∑ k ∈ Finset.range (Fintype.card V + 1), (-u) ^ k • Hp.restrictSome.deletedCharge K k :=
    rfl
  rw [hL, hR, hK, hsum, Finset.mul_sum]
  simp only [mul_smul_comm]

end Transfer

end PauliFrustrationRepresentation
end SimpleGraph
