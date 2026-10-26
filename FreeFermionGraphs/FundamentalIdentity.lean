import FreeFermionGraphs.TransferOperator
import Mathlib.Tactic.NoncommRing

/-!
# The Fundamental Identity

Manuscript (arXiv 2305.15625 v1) Lemma 12 (`FundamentalIdentity`, L1274-1283;
proof in Appendix "Proof of Lemma 12", L1986-2056; it uses v1 Lemma 18
`kjrecursion`, L1992-2018, which is `paperLemma17` in this repository).  In the
numbering of the revised manuscript used by the repository this is "Lemma 2".

Let `Ks` be a simplicial clique of the frustration graph `G`, let `χ = σ^{j_s}`
be a simplicial mode with respect to `Ks` (v1 Definition 8, L588-595), and write
`Σ = ∑_{j ∈ Ks} h_j`.  Then, as operators,

`T_G(u) (1 + u Σ) χ T_G(-u) = Z_G(-u²) (1 - u Σ) χ`,

where `Z_G(-u²) := T_G(u) T_G(-u)` is the generalised characteristic polynomial
of v1 Definition 7 (L557), written there as an operator-valued polynomial in
`x = -u²`; here it is just the operator product `T_G(u) T_G(-u)`, with the
transfer operator `T_G(u) = ∑_k (-u)^k Q_G^(k)`
(`PauliFrustrationRepresentation.transfer`, v1 Definition 5).  The proof of the
manuscript shows first the *reduced* identity

`(1 + u Σ) χ T_G(-u) = T_G(-u) (1 - u Σ) χ`,

and the full identity follows by multiplying on the left by `T_G(u)`.  The
reduced identity is, coefficient by coefficient in `u`, the relation

`χ Q^(k+1) + Σ χ Q^(k) = (Q^(k+1) - Q^(k) Σ) χ`  for all `k ≥ 0`

(v1 display at L2027, with the index shifted by one so that no truncated
subtraction occurs; the case `k = 0` is `[H, χ] = 2 Σ χ`, see
`commutator_hamiltonian_root`).

## Provenance and deliberate deviations from v1

* v1 states Lemma 12 for an "SCF Hamiltonian" (simplicial, claw-free: the
  frustration graph is claw-free and contains a simplicial clique, v1 L319).
  The proof of v1 uses
  neither claw-freeness nor Theorem 1 (commutation of the charges): it uses only
  that `Ks` is a simplicial clique, the commutation pattern of `χ` and of the
  products `h_j χ` with the terms `h_v` (`χ` anticommutes with `h_v` exactly for
  `v ∈ Ks`), Eq. (50) of v1 on the cliques `Ks` and `K_j`, v1 Lemma 18, and the
  cancellation of the ordered double sum over pairs of distinct vertices of `Ks`.
  The statements below therefore carry **no** claw-freeness hypothesis, and no
  hypothesis `χ² = 1`, Hermiticity or reality of couplings either.  Fewer
  premises give a strictly stronger theorem, which the fidelity policy permits;
  because it is not the printed statement it is not given an unqualified
  paper-facing name (no `paperLemma2` alias).
* The setup is the root-adjoined representation `Hp` of the frustration graph
  `G⁺ = G.adjoinRootAt Ks` (`PauliFrustrationRepresentation`), with `χ` the term
  at the new vertex `none`.  No hypothesis beyond the simplicial clique
  `Ks` is used, and no field of the representation assumes a conclusion.
* v1 takes `u` real.  Here `u` lies in an arbitrary commutative ring `R` acting
  on the operator ring `A` (`[CommRing R] [Algebra R A]`), as in
  `PauliFrustrationRepresentation.transfer`.
* The index in the coefficient form is shifted by one (`k + 1` for v1's `k`),
  as in `paperLemma17`.  The operators `Q^(k)` are the charges of the restricted
  representation `Hp.restrictSome` (the terms `h_j`, `j ∈ V`).

## Main declarations

* `PauliFrustrationRepresentation.fundamentalIdentity_coeff` : the coefficient form;
* `PauliFrustrationRepresentation.fundamentalIdentity_reduced` : the reduced form;
* `PauliFrustrationRepresentation.fundamentalIdentity` : the full form.
-/

open Set Finset
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w} [Ring A]

/-! ### Commutation of an operator with a deleted charge -/

/-- An operator commuting with every term `h_v`, `v ∉ W`, commutes with every
charge `Q_{G∖W}^(k)`: each summand is a product of such terms. -/
theorem commute_deletedCharge_of_forall_commute [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {x : A} {W : Set V}
    (hx : ∀ v, v ∉ W → Commute x (H.term v)) (k : ℕ) :
    Commute x (H.deletedCharge W k) := by
  classical
  unfold deletedCharge operatorIndependentSetCharge
  refine Commute.sum_right _ _ _ (fun S hS => ?_)
  rw [mem_independentFinsetsOfCardAvoid] at hS
  obtain ⟨-, hind, havoid⟩ := hS
  show Commute x (H.independentProduct S)
  rw [H.independentProduct_eq_noncommProd hind]
  exact Finset.noncommProd_commute _ _ _ _ (fun v hv => hx v (havoid v hv))

/-- `h_j` commutes with `Q_{G∖Γ[j]}^(k)`: every independent set avoiding `Γ[j]`
consists of terms nonadjacent to `j`. -/
theorem term_commute_deletedCharge_closedNeighborhood [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (j : V) (k : ℕ) :
    Commute (H.term j) (H.deletedCharge (G.closedNeighborhood j) k) := by
  refine H.commute_deletedCharge_of_forall_commute (fun v hv => ?_) k
  exact H.commute_of_not_adj (fun hadj => hv (Or.inr hadj))

/-! ### Commutation pattern of `h_j χ` -/

section Root

variable (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)

/-- For `j ∈ Ks`, the product `h_j χ` commutes with `h_v` for every `v ∉ K_j`
(v1 L2034: "`h_j χ` only anticommutes with `h_k` if `k` is in `K_j`").
Here `K_j = Γ[j] ∖ (Ks ∖ {j})` is `G.lemma17CliqueAt Ks j`.

For `v ∈ Ks` both `χ` and `h_j` anticommute with `h_v` (the clique `Ks`); for
`v ∉ Ks` the mode `χ` commutes with `h_v` and `h_j` commutes with `h_v`
because `v ∉ Γ[j] = Ks ∪ K_j`. -/
theorem term_mul_root_commute_of_not_mem
    (hKs : G.IsSimplicialClique Ks) {j v : V} (hj : j ∈ Ks)
    (hv : v ∉ G.lemma17CliqueAt Ks j) :
    Commute (Hp.term (some j) * Hp.term none) (Hp.term (some v)) := by
  show Hp.term (some j) * Hp.term none * Hp.term (some v) =
    Hp.term (some v) * (Hp.term (some j) * Hp.term none)
  by_cases hvKs : v ∈ Ks
  · have hvj : v ≠ j := fun h => hv (by rw [h]; exact mem_lemma17CliqueAt_self hj)
    have hadj : (G.adjoinRootAt Ks).Adj (some j) (some v) :=
      hKs.isClique hj hvKs (Ne.symm hvj)
    have h1 := Hp.adj_iff_anticommute.mp hadj
    have h2 := (Hp.root_anticommute_iff v).mp hvKs
    calc Hp.term (some j) * Hp.term none * Hp.term (some v)
        = Hp.term (some j) * (Hp.term none * Hp.term (some v)) := mul_assoc _ _ _
      _ = Hp.term (some j) * (-(Hp.term (some v) * Hp.term none)) := by rw [h2]
      _ = -(Hp.term (some j) * Hp.term (some v)) * Hp.term none := by noncomm_ring
      _ = Hp.term (some v) * Hp.term (some j) * Hp.term none := by rw [h1, neg_neg]
      _ = Hp.term (some v) * (Hp.term (some j) * Hp.term none) := mul_assoc _ _ _
  · have hvΓ : v ∉ G.closedNeighborhood j := by
      rw [closedNeighborhood_eq_union_lemma17CliqueAt hKs hj]
      exact fun h => h.elim hvKs hv
    have hnadj : ¬ (G.adjoinRootAt Ks).Adj (some j) (some v) :=
      fun hadj => hvΓ (Or.inr hadj)
    have h1 := Hp.commute_of_not_adj hnadj
    have h2 := (Hp.root_commute_of_not_mem hvKs).eq
    calc Hp.term (some j) * Hp.term none * Hp.term (some v)
        = Hp.term (some j) * (Hp.term none * Hp.term (some v)) := mul_assoc _ _ _
      _ = Hp.term (some j) * (Hp.term (some v) * Hp.term none) := by rw [h2]
      _ = (Hp.term (some j) * Hp.term (some v)) * Hp.term none := (mul_assoc _ _ _).symm
      _ = (Hp.term (some v) * Hp.term (some j)) * Hp.term none := by rw [h1]
      _ = Hp.term (some v) * (Hp.term (some j) * Hp.term none) := mul_assoc _ _ _

/-- For `j ∈ Ks`, the product `h_j χ` anticommutes with `h_v` for every
`v ∈ K_j` (v1 L2034).  For `v = j` this is the anticommutation of `χ` with
`h_j`; for `v ∈ K_j ∖ Ks` it is the edge `j ~ v` of `G`, `χ` commuting with
`h_v`.  No simpliciality of `Ks` is needed here. -/
theorem term_mul_root_anticommute_of_mem
    {j v : V} (hj : j ∈ Ks)
    (hv : v ∈ G.lemma17CliqueAt Ks j) :
    Hp.term (some j) * Hp.term none * Hp.term (some v) =
      -(Hp.term (some v) * (Hp.term (some j) * Hp.term none)) := by
  by_cases hvKs : v ∈ Ks
  · have hvj : v = j := by
      by_contra hne
      exact hv.2 ⟨hvKs, hne⟩
    subst hvj
    have h2 := (Hp.root_anticommute_iff v).mp hvKs
    calc Hp.term (some v) * Hp.term none * Hp.term (some v)
        = Hp.term (some v) * (Hp.term none * Hp.term (some v)) := mul_assoc _ _ _
      _ = Hp.term (some v) * (-(Hp.term (some v) * Hp.term none)) := by rw [h2]
      _ = -(Hp.term (some v) * (Hp.term (some v) * Hp.term none)) := by noncomm_ring
  · have hvne : v ≠ j := fun h => hvKs (h ▸ hj)
    have hadj : G.Adj j v := by
      rcases hv.1 with h | h
      · exact absurd h hvne
      · exact (G.mem_neighborSet j v).mp h
    have h1 := Hp.adj_iff_anticommute.mp
      ((adjoinRootAt_adj_some_some G Ks j v).mpr hadj)
    have h2 := (Hp.root_commute_of_not_mem hvKs).eq
    calc Hp.term (some j) * Hp.term none * Hp.term (some v)
        = Hp.term (some j) * (Hp.term none * Hp.term (some v)) := mul_assoc _ _ _
      _ = Hp.term (some j) * (Hp.term (some v) * Hp.term none) := by rw [h2]
      _ = (Hp.term (some j) * Hp.term (some v)) * Hp.term none := (mul_assoc _ _ _).symm
      _ = (-(Hp.term (some v) * Hp.term (some j))) * Hp.term none := by rw [h1]
      _ = -(Hp.term (some v) * (Hp.term (some j) * Hp.term none)) := by noncomm_ring

/-! ### The three ingredients of the coefficient identity -/

variable [Fintype V] [DecidableEq V]

/-- `χ Q^(k+1) = Q^(k+1) χ - 2 ∑_{j ∈ Ks} Q_{G∖Γ[j]}^(k) h_j χ`.

Eq. (50) of v1 on the clique `Ks` (`Q^(k+1) = Q_{G∖Ks}^(k+1) + ∑_j h_j Q_{G∖Γ[j]}^(k)`);
`χ` commutes with the charges of graphs from which `Ks` is deleted, and
anticommutes with each `h_j`, `j ∈ Ks` (v1 L2029-2033). -/
theorem root_mul_charge_succ
    (hKs : G.IsSimplicialClique Ks) (k : ℕ) :
    Hp.term none * Hp.restrictSome.charge (k + 1) =
      Hp.restrictSome.charge (k + 1) * Hp.term none -
        2 * ∑ j ∈ verticesOfSet Ks,
          Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k *
            (Hp.term (some j) * Hp.term none) := by
  classical
  have h : Hp.restrictSome.charge (k + 1) =
      Hp.restrictSome.deletedCharge Ks (k + 1) +
        ∑ j ∈ verticesOfSet Ks, Hp.term (some j) *
          Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k :=
    operatorIndependentSetCharge_clique Hp.restrictSome.toOperatorModel hKs.isClique k
  have hKsc : Hp.term none * Hp.restrictSome.deletedCharge Ks (k + 1) =
      Hp.restrictSome.deletedCharge Ks (k + 1) * Hp.term none :=
    (Hp.root_commute_deletedCharge (subset_refl Ks) (k + 1)).eq
  have hterm : ∀ j ∈ verticesOfSet Ks,
      Hp.term none * (Hp.term (some j) *
          Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k) =
        Hp.term (some j) *
            Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k * Hp.term none -
          2 * (Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k *
            (Hp.term (some j) * Hp.term none)) := by
    intro j hjFin
    have hj : j ∈ Ks := mem_verticesOfSet.mp hjFin
    have hanti := (Hp.root_anticommute_iff j).mp hj
    have hPχ : Hp.term none *
        Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k =
        Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k * Hp.term none := by
      refine (Hp.root_commute_deletedCharge (W := G.closedNeighborhood j) ?_ k).eq
      rw [closedNeighborhood_eq_union_lemma17CliqueAt hKs hj]
      exact Set.subset_union_left
    have hPh : Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k *
        Hp.term (some j) = Hp.term (some j) *
          Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k :=
      (Hp.restrictSome.term_commute_deletedCharge_closedNeighborhood j k).eq.symm
    set P := Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k with hP
    set hj' := Hp.term (some j) with hhj
    set χ := Hp.term none with hχ
    calc χ * (hj' * P) = (χ * hj') * P := (mul_assoc _ _ _).symm
      _ = -(hj' * χ) * P := by rw [hanti]
      _ = -(hj' * (χ * P)) := by noncomm_ring
      _ = -(hj' * (P * χ)) := by rw [hPχ]
      _ = hj' * P * χ - 2 * (P * (hj' * χ)) := by
        have : P * (hj' * χ) = hj' * P * χ := by
          rw [← mul_assoc, hPh]
        rw [this]; noncomm_ring
  rw [h, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, hKsc,
    Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  abel

/-- For `j ∈ Ks` and every `k`,
`h_j χ Q^(k) + Q^(k) h_j χ = 2 Q_{G∖K_j}^(k) h_j χ`.

Eq. (50) of v1 on the clique `K_j` (a clique because `Ks` is simplicial,
`lemma17CliqueAt_isClique`) splits `Q^(k) = Q_{G∖K_j}^(k) + ∑_{j' ∈ K_j} h_{j'}
Q_{G∖Γ[j']}^(k-1)`.  The first summand commutes with `h_j χ`, the others
anticommute with it, because `h_j χ` anticommutes with `h_{j'}` for `j' ∈ K_j`
and commutes with the charge `Q_{G∖Γ[j']}`, `K_j ⊆ Γ[j']` (v1 L2034-2039). -/
theorem term_mul_root_anticomm_charge
    (hKs : G.IsSimplicialClique Ks) {j : V} (hj : j ∈ Ks) (k : ℕ) :
    Hp.term (some j) * Hp.term none * Hp.restrictSome.charge k +
        Hp.restrictSome.charge k * (Hp.term (some j) * Hp.term none) =
      2 * (Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) k *
        (Hp.term (some j) * Hp.term none)) := by
  classical
  have hcom : ∀ {W : Set V}, G.lemma17CliqueAt Ks j ⊆ W → ∀ m : ℕ,
      Commute (Hp.term (some j) * Hp.term none) (Hp.restrictSome.deletedCharge W m) :=
    fun hW m => Hp.restrictSome.commute_deletedCharge_of_forall_commute
      (fun v hv => Hp.term_mul_root_commute_of_not_mem hKs hj (fun h => hv (hW h))) m
  cases k with
  | zero =>
      rw [Hp.restrictSome.charge_zero, Hp.restrictSome.deletedCharge_zero]
      noncomm_ring
  | succ n =>
      have hKj : G.IsClique (G.lemma17CliqueAt Ks j) := lemma17CliqueAt_isClique hKs hj
      have h : Hp.restrictSome.charge (n + 1) =
          Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) (n + 1) +
            ∑ j' ∈ verticesOfSet (G.lemma17CliqueAt Ks j), Hp.term (some j') *
              Hp.restrictSome.deletedCharge (G.closedNeighborhood j') n :=
        operatorIndependentSetCharge_clique Hp.restrictSome.toOperatorModel hKj n
      have hmain := (hcom (subset_refl _) (n + 1)).eq
      have hsum : ∀ j' ∈ verticesOfSet (G.lemma17CliqueAt Ks j),
          Hp.term (some j) * Hp.term none *
              (Hp.term (some j') *
                Hp.restrictSome.deletedCharge (G.closedNeighborhood j') n) +
            Hp.term (some j') *
              Hp.restrictSome.deletedCharge (G.closedNeighborhood j') n *
              (Hp.term (some j) * Hp.term none) = 0 := by
        intro j' hj'Fin
        have hj' : j' ∈ G.lemma17CliqueAt Ks j := mem_verticesOfSet.mp hj'Fin
        have hanti := Hp.term_mul_root_anticommute_of_mem hj hj'
        have hsub : G.lemma17CliqueAt Ks j ⊆ G.closedNeighborhood j' := by
          intro v hv
          by_cases hvj' : v = j'
          · exact Or.inl hvj'
          · exact Or.inr ((G.mem_neighborSet j' v).mpr (hKj hj' hv (Ne.symm hvj')))
        have hQ := (hcom hsub n).eq
        set x := Hp.term (some j) * Hp.term none with hx
        set Q := Hp.restrictSome.deletedCharge (G.closedNeighborhood j') n with hQdef
        set y := Hp.term (some j') with hy
        calc x * (y * Q) + y * Q * x = (x * y) * Q + y * (Q * x) := by
              simp only [mul_assoc]
          _ = -(y * x) * Q + y * (x * Q) := by rw [hanti, hQ]
          _ = 0 := by noncomm_ring
      set x := Hp.term (some j) * Hp.term none with hx
      set QK := Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) (n + 1) with hQK
      rw [h, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      have hsum' : ∑ i ∈ verticesOfSet (G.lemma17CliqueAt Ks j),
          x * (Hp.term (some i) *
            Hp.restrictSome.deletedCharge (G.closedNeighborhood i) n) +
          ∑ i ∈ verticesOfSet (G.lemma17CliqueAt Ks j),
            Hp.term (some i) *
              Hp.restrictSome.deletedCharge (G.closedNeighborhood i) n * x = 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero hsum
      calc _ = (x * QK + QK * x) +
          (∑ i ∈ verticesOfSet (G.lemma17CliqueAt Ks j),
          x * (Hp.term (some i) *
            Hp.restrictSome.deletedCharge (G.closedNeighborhood i) n) +
          ∑ i ∈ verticesOfSet (G.lemma17CliqueAt Ks j),
            Hp.term (some i) *
              Hp.restrictSome.deletedCharge (G.closedNeighborhood i) n * x) := by abel
        _ = 2 * (QK * x) := by
            rw [hsum', add_zero, hmain]
            noncomm_ring

/-- `∑_{j ∈ Ks} (Q_{G∖K_j}^(k) - Q_{G∖Γ[j]}^(k)) h_j χ = 0`.

By v1 (D22), `Q_{G∖K_j}^(n+1) - Q_{G∖(Ks ∪ K_j)}^(n+1) = ∑_{l ∈ Ks∖{j}}
Q_{G∖(Ks ∪ K_j ∪ K_l)}^(n) h_l`, and `Γ[j] = Ks ∪ K_j`.  The resulting ordered
double sum over pairs of distinct vertices of `Ks` vanishes by
`lemma17_orderedDoubleSum_eq_zero` (v1 L2051-2053: the charge is symmetric in
`j, l` while `h_j, h_l` anticommute).  For `k = 0` every summand is zero. -/
theorem sum_lemma17Clique_sub_closedNeighborhood_mul_root
    (hKs : G.IsSimplicialClique Ks) (k : ℕ) :
    ∑ j ∈ verticesOfSet Ks,
        (Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) k -
          Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k) *
          (Hp.term (some j) * Hp.term none) = 0 := by
  classical
  cases k with
  | zero =>
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [Hp.restrictSome.deletedCharge_zero, Hp.restrictSome.deletedCharge_zero]
      simp
  | succ n =>
      set M := Hp.restrictSome.toOperatorModel with hM
      have hterm : ∀ j ∈ verticesOfSet Ks,
          (Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) (n + 1) -
            Hp.restrictSome.deletedCharge (G.closedNeighborhood j) (n + 1)) *
            (Hp.term (some j) * Hp.term none) =
          (∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
            lemma17OrderedPairContribution M Ks n (j, l)) * Hp.term none := by
        intro j hjFin
        have hj : j ∈ Ks := mem_verticesOfSet.mp hjFin
        have hD22 := lemma17_D22 M hKs hj n
        have hsub : Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) (n + 1) -
            Hp.restrictSome.deletedCharge (G.closedNeighborhood j) (n + 1) =
            ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
              G.operatorIndependentSetCharge M
                (Ks ∪ G.lemma17CliqueAt Ks j ∪ G.lemma17CliqueAt Ks l) n * M.term l := by
          rw [closedNeighborhood_eq_union_lemma17CliqueAt hKs hj]
          show G.operatorIndependentSetCharge M (G.lemma17CliqueAt Ks j) (n + 1) -
            G.operatorIndependentSetCharge M (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) = _
          rw [hD22]
          abel
        rw [hsub, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        simp only [lemma17OrderedPairContribution, mul_assoc]
        rfl
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        ← lemma17_orderedDoubleSum_eq_nested M Ks n,
        lemma17_orderedDoubleSum_eq_zero M hKs n, zero_mul]

end Root

/-! ### The coefficient form -/

/-- **Fundamental Identity, coefficient form** (v1 Lemma 12, display at
L2027, index shifted by one; repo "Lemma 2").

For a simplicial clique `Ks`, a root-adjoined representation `Hp` (the mode
`χ = Hp.term none`, the terms `h_j = Hp.term (some j)`), and `Σ = ∑_{j ∈ Ks} h_j`:

`χ Q^(k+1) + Σ χ Q^(k) = (Q^(k+1) - Q^(k) Σ) χ`  for all `k ≥ 0`,

where `Q^(k)` is the charge of the restricted representation `Hp.restrictSome`.
For `k = 0` this is `[H, χ] = 2 Σ χ` (`commutator_hamiltonian_root`).

The proof follows v1 L2029-2053 in the commutator form
`[χ, Q^(k+1)] + ∑_j {h_j χ, Q^(k)} = 0`: the first term equals
`-2 ∑_j Q_{G∖Γ[j]}^(k) h_j χ` (`root_mul_charge_succ`), the second
`2 ∑_j Q_{G∖K_j}^(k) h_j χ` (`term_mul_root_anticomm_charge`), and the two
agree by the vanishing of the ordered double sum
(`sum_lemma17Clique_sub_closedNeighborhood_mul_root`).

No claw-freeness is assumed (v1 states the lemma for SCF Hamiltonians but does not
use it), nor `χ² = 1`, Hermiticity, or reality of couplings. -/
theorem fundamentalIdentity_coeff [Fintype V] [DecidableEq V]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hKs : G.IsSimplicialClique Ks) (k : ℕ) :
    Hp.term none * Hp.restrictSome.charge (k + 1) +
        (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none *
          Hp.restrictSome.charge k =
      (Hp.restrictSome.charge (k + 1) -
          Hp.restrictSome.charge k * ∑ j ∈ verticesOfSet Ks, Hp.term (some j)) *
        Hp.term none := by
  classical
  have hA := Hp.root_mul_charge_succ hKs k
  have hB := fun j (hj : j ∈ verticesOfSet Ks) =>
    Hp.term_mul_root_anticomm_charge hKs (mem_verticesOfSet.mp hj) k
  have hC := Hp.sum_lemma17Clique_sub_closedNeighborhood_mul_root hKs k
  have hS1 : (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none *
        Hp.restrictSome.charge k =
      ∑ j ∈ verticesOfSet Ks,
        Hp.term (some j) * Hp.term none * Hp.restrictSome.charge k := by
    rw [Finset.sum_mul, Finset.sum_mul]
  have hS2 : Hp.restrictSome.charge k *
        (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none =
      ∑ j ∈ verticesOfSet Ks,
        Hp.restrictSome.charge k * (Hp.term (some j) * Hp.term none) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [mul_assoc]
  have e2 : (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none *
        Hp.restrictSome.charge k +
        Hp.restrictSome.charge k * (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) *
          Hp.term none =
      ∑ j ∈ verticesOfSet Ks,
        2 * (Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) k *
          (Hp.term (some j) * Hp.term none)) := by
    rw [hS1, hS2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hB
  have e4 : ∑ j ∈ verticesOfSet Ks,
        2 * (Hp.restrictSome.deletedCharge (G.lemma17CliqueAt Ks j) k *
          (Hp.term (some j) * Hp.term none)) -
        2 * ∑ j ∈ verticesOfSet Ks,
          Hp.restrictSome.deletedCharge (G.closedNeighborhood j) k *
            (Hp.term (some j) * Hp.term none) = 0 := by
    rw [← Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    rw [hC, mul_zero]
  rw [← sub_eq_zero, sub_mul]
  calc _ = (Hp.term none * Hp.restrictSome.charge (k + 1) -
          Hp.restrictSome.charge (k + 1) * Hp.term none) +
        ((∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none *
          Hp.restrictSome.charge k +
        Hp.restrictSome.charge k * (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) *
          Hp.term none) := by abel
    _ = 0 := by
        rw [e2, hA]
        refine Eq.trans ?_ e4
        abel

/-! ### The reduced and full forms -/

/-- Generating-function step of the Fundamental Identity: if the coefficient
relation `χ Q_{k+1} + Σ χ Q_k = (Q_{k+1} - Q_k Σ) χ` holds for all `k` and
`Q_0 = 1`, then for the truncation `T_N = ∑_{k<N} u^k Q_k`,

`(1 + uΣ) χ T_N - T_N (1 - uΣ) χ = -u^N [χ, Q_N]`.

(The right-hand side is the boundary term of the telescoping sum, and vanishes
once `Q_N = 0`.) -/
theorem reduced_partial_sum {R : Type*} [CommRing R] [Algebra R A]
    (χ S : A) (Q : ℕ → A) (hQ0 : Q 0 = 1)
    (hcoeff : ∀ k, χ * Q (k + 1) + S * χ * Q k = (Q (k + 1) - Q k * S) * χ)
    (u : R) (N : ℕ) :
    (1 + u • S) * χ * ∑ k ∈ Finset.range N, u ^ k • Q k -
        (∑ k ∈ Finset.range N, u ^ k • Q k) * ((1 - u • S) * χ) =
      -(u ^ N • (χ * Q N - Q N * χ)) := by
  induction N with
  | zero => simp [hQ0]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hN := hcoeff N
      have hexp : (1 + u • S) * χ * (∑ k ∈ Finset.range N, u ^ k • Q k + u ^ N • Q N) -
          (∑ k ∈ Finset.range N, u ^ k • Q k + u ^ N • Q N) * ((1 - u • S) * χ) =
          ((1 + u • S) * χ * ∑ k ∈ Finset.range N, u ^ k • Q k -
            (∑ k ∈ Finset.range N, u ^ k • Q k) * ((1 - u • S) * χ)) +
          u ^ N • ((χ * Q N - Q N * χ) + u • (S * χ * Q N + Q N * S * χ)) := by
        simp only [mul_add, add_mul, sub_mul, mul_sub, smul_add, smul_sub, one_mul,
          mul_smul_comm, smul_mul_assoc, mul_assoc, smul_smul]
        rw [mul_comm (u ^ N) u]
        abel
      have hE : S * χ * Q N + Q N * S * χ = -(χ * Q (N + 1) - Q (N + 1) * χ) := by
        calc S * χ * Q N + Q N * S * χ
            = (χ * Q (N + 1) + S * χ * Q N) - χ * Q (N + 1) + Q N * S * χ := by abel
          _ = (Q (N + 1) * χ - Q N * S * χ) - χ * Q (N + 1) + Q N * S * χ := by
              rw [hN, sub_mul]
          _ = -(χ * Q (N + 1) - Q (N + 1) * χ) := by abel
      rw [hexp, ih, hE, pow_succ, mul_smul, smul_neg, smul_add, smul_neg]
      abel

/-- **Fundamental Identity, reduced form** (the displayed identity at the start of
the proof of v1 Lemma 12, L2021-2023; repo "Lemma 2").

For a simplicial clique `Ks`, the mode `χ = Hp.term none` and `Σ = ∑_{j ∈ Ks} h_j`,

`(1 + uΣ) χ T_G(-u) = T_G(-u) (1 - uΣ) χ`,

where `T_G(u) = Hp.restrictSome.transfer ∅ u` is the transfer operator
(v1 Definition 5).  It is the generating function, in `u`, of the coefficient
form `fundamentalIdentity_coeff` (the sum defining `T_G` is finite, and its
top coefficient `Q^(|V|+1)` vanishes).  The spectral parameter `u` lies in an
arbitrary commutative ring `R` acting on `A` (v1: real `u`).  As for the
coefficient form, no claw-freeness, `χ² = 1`, or Hermiticity is assumed. -/
theorem fundamentalIdentity_reduced [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra R A]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hKs : G.IsSimplicialClique Ks) (u : R) :
    (1 + u • ∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none *
        Hp.restrictSome.transfer ∅ (-u) =
      Hp.restrictSome.transfer ∅ (-u) *
        ((1 - u • ∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none) := by
  have hT : Hp.restrictSome.transfer ∅ (-u) =
      ∑ k ∈ Finset.range (Fintype.card V + 1), u ^ k • Hp.restrictSome.charge k := by
    unfold transfer
    simp only [neg_neg]
    rfl
  have h := reduced_partial_sum (R := R) (Hp.term none)
    (∑ j ∈ verticesOfSet Ks, Hp.term (some j)) (fun k => Hp.restrictSome.charge k)
    Hp.restrictSome.charge_zero (fun k => Hp.fundamentalIdentity_coeff hKs k) u
    (Fintype.card V + 1)
  have hz : Hp.restrictSome.charge (Fintype.card V + 1) = 0 :=
    Hp.restrictSome.deletedCharge_eq_zero_of_card_lt ∅ (Nat.lt_succ_self _)
  simp only [hz, mul_zero, zero_mul, sub_zero, smul_zero, neg_zero] at h
  rw [hT]
  exact sub_eq_zero.mp h

/-- **Fundamental Identity** (v1 Lemma 12, L1274-1283, with `Z_G(-u²)` unfolded by
v1 Definition 7; repo "Lemma 2").

Let `Ks` be a simplicial clique of the frustration graph `G` of the Pauli
Hamiltonian `H = ∑_j h_j` (`Hp.restrictSome`), and `χ = Hp.term none` a
simplicial mode for `Ks` (v1 Definition 8), i.e. the term at the root of the
root-adjoined representation `Hp` of `G⁺ = G.adjoinRootAt Ks`.  With
`Σ = ∑_{j ∈ Ks} h_j` and `T_G(u) = Hp.restrictSome.transfer ∅ u`,

`T_G(u) (1 + uΣ) χ T_G(-u) = Z_G(-u²) (1 - uΣ) χ`.

The generalised characteristic polynomial of v1 Definition 7 is the operator
`Z_G(-u²) := T_G(u) T_G(-u)` (the polynomial `Z_G(x)` with `x = -u²`, as in
v1 Lemma 11); the statement below unfolds it as this product, so no separate
definition of `Z_G` is needed.  Its proof is `fundamentalIdentity_reduced`
multiplied on the left by `T_G(u)`.

Deliberate deviation from v1: the manuscript states the lemma for an "SCF
Hamiltonian" (claw-free frustration graph).  Its proof uses neither
claw-freeness nor Theorem 1 (commutation of the charges), so this theorem has no
such premise; it also needs no `χ² = 1`, Hermiticity or reality of couplings,
and holds for every root-adjoined frustration representation `Hp` over a ring `A`,
with spectral parameter `u` in any commutative ring `R` acting on `A`.  Fewer
premises give a stronger statement, hence it is named by its content and not
`paperLemma2`; the only hypothesis is that `Ks` is a simplicial clique, as in v1. -/
theorem fundamentalIdentity [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra R A]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hKs : G.IsSimplicialClique Ks) (u : R) :
    Hp.restrictSome.transfer ∅ u *
        ((1 + u • ∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none *
          Hp.restrictSome.transfer ∅ (-u)) =
      (Hp.restrictSome.transfer ∅ u * Hp.restrictSome.transfer ∅ (-u)) *
        ((1 - u • ∑ j ∈ verticesOfSet Ks, Hp.term (some j)) * Hp.term none) := by
  rw [Hp.fundamentalIdentity_reduced hKs u, mul_assoc]

end PauliFrustrationRepresentation
end SimpleGraph
