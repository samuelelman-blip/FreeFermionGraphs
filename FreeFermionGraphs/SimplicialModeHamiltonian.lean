import FreeFermionGraphs.Lemma17Paper
import FreeFermionGraphs.PauliCliqueHamiltonian
import FreeFermionGraphs.PauliPathOperator
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Data.Real.Star

/-!
# The root-adjoined Pauli model of the simplicial mode

Manuscript (arXiv 2305.15625 v1) Definition 8 (simplicial mode, L588-595) adds
to a Pauli Hamiltonian `H = ∑ h_j` with frustration graph `G` (Definition 1,
L224; Eq. (paulihamiltonian), L91) one further Pauli operator
`χ = σ^{j_s}` which anticommutes with the Hamiltonian terms `h_k` exactly for
`k ∈ K_s` (`⟨j_s, k⟩ = δ_{k ∈ K_s}`).  The commutation pattern of the terms
`{h_j} ∪ {χ}` is therefore the frustration graph `G⁺ = G.adjoinRootAt Ks` of
the root-adjoined model; the new vertex `none` is `j_s`.

This module develops the algebra of that model, which every later package on
the exact solution (the Fundamental Identity, the transfer-matrix recursion,
the ladder relations) uses:

* `restrictSome` : a `(G.adjoinRootAt K)`-representation restricts to a
  `G`-representation (the terms indexed by original vertices);
* `charge_one` : `Q_G^(1) = H` (v1 Definition 4 remark, L522), and
  `deletedCharge_eq_zero_of_card_lt` : `Q_{G\W}^(k) = 0` for `k > |V|`;
* charge transport `Q^{G⁺}_{G⁺ \ ({χ} ∪ W)} = Q_{G\W}` and the recursion
  `Q^{G⁺,(k+1)} = Q_G^(k+1) + χ Q_{G\Ks}^(k)` (Eq. (50) at the vertex `χ`);
* `χ` commutes with `Q_{G\W}^(k)` whenever `Ks ⊆ W`;
* `[H, χ] = 2 (∑_{j ∈ Ks} h_j) χ`;
* Hermiticity of the independent products `h_S` and of all charges
  `Q_{G\W}^(k)`, from Hermiticity of the terms;
* `b_j ≠ 0` for every coupling, derived from the setup rather than assumed
  (v1 requires `b_j ∈ ℝ \ {0}`, L91).

The results that need no `*`-structure are stated for an arbitrary
`(G.adjoinRootAt K).PauliFrustrationRepresentation A` so that they apply under
the weakest hypotheses.  Nothing here assumes simpliciality of `Ks`; that
hypothesis is supplied per theorem by later packages.

Deliberate deviations from v1: v1 requires `j_s ∉ V` and the existence of `χ`
(which may need an ancilla qubit).  Neither is encoded: `χ` is simply part of
the data, as in v1's Theorem 2 where `χ` is given.  The theorem-level
hypothesis `Ks` simplicial is not a field of the structure.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {K : Set V} {A : Type w} [Ring A]

/-! ### Restriction to the original vertices -/

/-- Restriction of a representation of the root-adjoined graph `G⁺` to the
original vertices: `term j := h_j`.  Adjacency of `some j, some k` in `G⁺` is
adjacency in `G` (`adjoinRootAt_adj_some_some`), so Definition 1 holds for
`G`. -/
def restrictSome
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) :
    G.PauliFrustrationRepresentation A where
  term j := Hp.term (some j)
  adj_iff_anticommute := by
    intro j k
    rw [← adjoinRootAt_adj_some_some G K j k]
    exact Hp.adj_iff_anticommute
  commute_of_not_adj := by
    intro j k hjk
    exact Hp.commute_of_not_adj
      (by rwa [adjoinRootAt_adj_some_some G K j k])

@[simp]
theorem restrictSome_term
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) (j : V) :
    Hp.restrictSome.term j = Hp.term (some j) :=
  rfl

/-- The Hamiltonian of the restricted representation is the sum of the terms
`h_j` over the original vertices (the root term `χ` is excluded). -/
theorem hamiltonian_restrictSome [Fintype V]
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) :
    Hp.restrictSome.hamiltonian = ∑ j : V, Hp.term (some j) :=
  rfl

/-- `χ` anticommutes with `h_j` exactly for `j ∈ K`: the manuscript relation
`⟨j_s, j⟩ = δ_{j ∈ K_s}` (Definition 8, L591). -/
theorem root_anticommute_iff
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) (j : V) :
    j ∈ K ↔
      Hp.term none * Hp.term (some j) =
        -(Hp.term (some j) * Hp.term none) := by
  rw [← adjoinRootAt_adj_none_some G K j]
  exact Hp.adj_iff_anticommute

/-- `χ` commutes with `h_j` for every `j ∉ K`. -/
theorem root_commute_of_not_mem
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A)
    {j : V} (hj : j ∉ K) :
    Commute (Hp.term none) (Hp.term (some j)) :=
  Hp.commute_of_not_adj (by rwa [adjoinRootAt_adj_none_some G K j])

/-! ### Basic facts on charges -/

/-- Reindexing `Finset.noncommProd` along an embedding of the index type. -/
theorem noncommProd_map_embedding {α γ β : Type*} [Monoid β]
    (e : α ↪ γ) (s : Finset α) (f : γ → β)
    (comm : ((s.map e : Finset γ) : Set γ).Pairwise (Function.onFun Commute f))
    (comm' : (s : Set α).Pairwise (Function.onFun Commute fun a => f (e a))) :
    (s.map e).noncommProd f comm = s.noncommProd (fun a => f (e a)) comm' := by
  simp only [Finset.noncommProd, Finset.map_val, Multiset.map_map]
  rfl

/-- Independent `1`-sets avoiding `∅` are exactly the singletons. -/
theorem independentFinsetsOfCardAvoid_one
    [Fintype V] [DecidableEq V] :
    G.independentFinsetsOfCardAvoid ∅ 1 =
      Finset.univ.map ⟨fun v : V => ({v} : Finset V), Finset.singleton_injective⟩ := by
  ext S
  simp only [mem_independentFinsetsOfCardAvoid, Finset.mem_map,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, Set.mem_empty_iff_false,
    not_false_eq_true, implies_true, and_true]
  constructor
  · rintro ⟨hcard, -⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨Finset.card_singleton a, ?_⟩
    simp

/-- Manuscript Definition 4 remark (L522): `Q_G^(1) = H`. -/
theorem charge_one [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) :
    H.charge 1 = H.hamiltonian := by
  classical
  unfold charge operatorIndependentSetChargeFull operatorIndependentSetCharge
  rw [independentFinsetsOfCardAvoid_one, Finset.sum_map]
  unfold hamiltonian
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show H.independentProduct {a} = H.term a
  rw [H.independentProduct_eq_noncommProd (by simp)]
  exact Finset.noncommProd_singleton a H.term

/-- Manuscript Definition 4 (L517-522) for the deleted charges: no
independent set has more than `|V|` vertices, so `Q_{G\W}^(k) = 0` for
`k > |V|`.  (v1 ranges over `k ≤ α(G)`; the repo has no independence number,
and the bound `|V|` is the one used downstream.) -/
theorem deletedCharge_eq_zero_of_card_lt [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (W : Set V) {k : ℕ}
    (hk : Fintype.card V < k) :
    H.deletedCharge W k = 0 := by
  classical
  unfold deletedCharge operatorIndependentSetCharge
  have hempty : G.independentFinsetsOfCardAvoid W k = ∅ := by
    ext S
    simp only [mem_independentFinsetsOfCardAvoid, Finset.notMem_empty, iff_false]
    rintro ⟨hcard, -⟩
    have := Finset.card_le_univ S
    omega
  rw [hempty, Finset.sum_empty]

/-- `Q_G^(0) = 1`. -/
theorem charge_zero [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) :
    H.charge 0 = 1 :=
  operatorIndependentSetCharge_zero H.toOperatorModel ∅

/-! ### Transport between `G⁺` and `G` -/

/-- Independent products transport along `some`: the product over the image
`some '' S` in `G⁺` is the product over `S` for the restricted
representation. -/
theorem independentProduct_map_some [DecidableEq V]
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    Hp.independentProduct (S.map Function.Embedding.some) =
      Hp.restrictSome.independentProduct S := by
  classical
  have hS' : (G.adjoinRootAt K).IsIndepSet
      ((S.map Function.Embedding.some : Finset (Option V)) : Set (Option V)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    show ¬(G.adjoinRootAt K).Adj (some a) (some b)
    rw [adjoinRootAt_adj_some_some]
    exact hS ha hb (fun h => hxy (by rw [h]))
  rw [Hp.independentProduct_eq_noncommProd hS',
    Hp.restrictSome.independentProduct_eq_noncommProd hS]
  exact noncommProd_map_embedding Function.Embedding.some S Hp.term _
    (Hp.restrictSome.independent_pairwise_commute hS)

/-- Charge transport: `Q^{G⁺}_{G⁺ \ ({χ} ∪ W)} = Q_{G \ W}`.  Deleting `χ`
together with the image of `W` from `G⁺` leaves exactly `G \ W`, and the
canonical products agree under `some`. -/
theorem deletedCharge_restrictSome [Fintype V] [DecidableEq V]
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A)
    (W : Set V) (k : ℕ) :
    Hp.deletedCharge (insert none (Option.some '' W)) k =
      Hp.restrictSome.deletedCharge W k := by
  classical
  unfold deletedCharge operatorIndependentSetCharge
  symm
  refine Finset.sum_bij (fun S _ => S.map Function.Embedding.some) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_independentFinsetsOfCardAvoid] at hS ⊢
    obtain ⟨hcard, hind, havoid⟩ := hS
    refine ⟨by rw [Finset.card_map, hcard], ?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_map] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      show ¬(G.adjoinRootAt K).Adj (some a) (some b)
      rw [adjoinRootAt_adj_some_some]
      exact hind ha hb (fun h => hxy (by rw [h]))
    · intro x hx hxW
      rw [Finset.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [Function.Embedding.some_apply] at hxW
      rcases hxW with h | ⟨b, hb, hba⟩
      · exact Option.some_ne_none _ h
      · exact havoid a ha (Option.some_injective _ hba ▸ hb)
  · intro S₁ _ S₂ _ h
    exact Finset.map_injective _ h
  · intro T hT
    rw [mem_independentFinsetsOfCardAvoid] at hT
    obtain ⟨hcard, hind, havoid⟩ := hT
    have hnone : none ∉ T := fun h => havoid none h (Set.mem_insert _ _)
    have hmap : T.eraseNone.map Function.Embedding.some = T := by
      rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hnone]
    refine ⟨T.eraseNone, ?_, hmap⟩
    rw [mem_independentFinsetsOfCardAvoid]
    refine ⟨?_, ?_, ?_⟩
    · rw [← Finset.card_map Function.Embedding.some, hmap, hcard]
    · intro a ha b hb hab
      have ha' : some a ∈ T := by
        rw [← hmap, Finset.mem_map]; exact ⟨a, ha, rfl⟩
      have hb' : some b ∈ T := by
        rw [← hmap, Finset.mem_map]; exact ⟨b, hb, rfl⟩
      rw [← adjoinRootAt_adj_some_some G K a b]
      exact hind ha' hb' (fun h => hab (Option.some_injective _ h))
    · intro a ha haW
      have ha' : some a ∈ T := by
        rw [← hmap, Finset.mem_map]; exact ⟨a, ha, rfl⟩
      exact havoid (some a) ha' (Set.mem_insert_of_mem _ ⟨a, haW, rfl⟩)
  · intro S hS
    rw [mem_independentFinsetsOfCardAvoid] at hS
    exact (independentProduct_map_some Hp hS.2.1).symm

/-- The closed neighbourhood of the root `χ` in `G⁺` is `{χ} ∪ some '' K`. -/
theorem closedNeighborhood_adjoinRootAt_none (G : SimpleGraph V) (K : Set V) :
    (G.adjoinRootAt K).closedNeighborhood none =
      insert none (Option.some '' K) := by
  ext x
  cases x with
  | none => simp [closedNeighborhood]
  | some v =>
      simp [closedNeighborhood, adjoinRootAt_adj_none_some]

/-- Manuscript Eq. (50) (v1 `chargecliquerecursion`, L529) at the vertex `χ`
of `G⁺`, where `Γ[χ] = {χ} ∪ K_s`:
`Q^{G⁺,(k+1)} = Q_G^(k+1) + χ Q_{G\K_s}^(k)`.  The two charges on the right
are those of the restricted representation, by `deletedCharge_restrictSome`. -/
theorem charge_succ_adjoinRoot [Fintype V] [DecidableEq V]
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) (k : ℕ) :
    Hp.charge (k + 1) =
      Hp.restrictSome.charge (k + 1) +
        Hp.term none * Hp.restrictSome.deletedCharge K k := by
  classical
  have h := operatorIndependentSetCharge_singleVertex
    (G := G.adjoinRootAt K) Hp.toOperatorModel
    (W := (∅ : Set (Option V))) (j := none) (by simp) k
  have e1 : ((∅ : Set (Option V)) ∪ ({none} : Set (Option V))) =
      insert none (Option.some '' (∅ : Set V)) := by
    ext x; cases x <;> simp
  have e2 : ((∅ : Set (Option V)) ∪ (G.adjoinRootAt K).closedNeighborhood none) =
      insert none (Option.some '' K) := by
    rw [Set.empty_union, closedNeighborhood_adjoinRootAt_none]
  rw [e1, e2] at h
  have h1 := deletedCharge_restrictSome Hp (∅ : Set V) (k + 1)
  have h2 := deletedCharge_restrictSome Hp K k
  calc Hp.charge (k + 1)
      = Hp.deletedCharge (insert none (Option.some '' (∅ : Set V))) (k + 1) +
        Hp.term none *
          Hp.deletedCharge (insert none (Option.some '' K)) k := h
    _ = Hp.restrictSome.charge (k + 1) +
        Hp.term none * Hp.restrictSome.deletedCharge K k := by
      rw [h1, h2]
      rfl

/-! ### Commutation with the root `χ` -/

/-- `χ` commutes with `Q_{G\W}^(k)` whenever `K_s ⊆ W`: an independent set of
`G \ W` avoids `K_s`, hence consists of terms commuting with `χ`
(v1 Definition 8, L591, together with Definition 4, L517-522). -/
theorem root_commute_deletedCharge [Fintype V] [DecidableEq V]
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A)
    {W : Set V} (hKW : K ⊆ W) (k : ℕ) :
    Commute (Hp.term none) (Hp.restrictSome.deletedCharge W k) := by
  classical
  unfold deletedCharge operatorIndependentSetCharge
  refine Commute.sum_right _ _ _ (fun S hS => ?_)
  rw [mem_independentFinsetsOfCardAvoid] at hS
  obtain ⟨-, hind, havoid⟩ := hS
  show Commute (Hp.term none) (Hp.restrictSome.independentProduct S)
  rw [Hp.restrictSome.independentProduct_eq_noncommProd hind]
  refine Finset.noncommProd_commute _ _ _ _ (fun v hv => ?_)
  exact Hp.root_commute_of_not_mem (fun hvK => havoid v hv (hKW hvK))

/-- `[H, χ] = 2 (∑_{j ∈ K_s} h_j) χ`: the Hamiltonian commutator with the
simplicial mode only sees the terms of the simplicial clique. -/
theorem commutator_hamiltonian_root [Fintype V] [DecidableEq V]
    (Hp : (G.adjoinRootAt K).PauliFrustrationRepresentation A) :
    algebraCommutator Hp.restrictSome.hamiltonian (Hp.term none) =
      2 * ((∑ j ∈ verticesOfSet K, Hp.term (some j)) * Hp.term none) := by
  classical
  rw [commutator_hamiltonian_eq_sum, Finset.sum_mul, Finset.mul_sum]
  have hv : verticesOfSet K = Finset.univ.filter (fun v => v ∈ K) := by
    ext v; simp
  rw [hv, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j ∈ K
  · have hanti := (Hp.root_anticommute_iff j).mp hj
    rw [if_pos hj]
    show Hp.term (some j) * Hp.term none - Hp.term none * Hp.term (some j) =
      2 * (Hp.term (some j) * Hp.term none)
    rw [hanti, sub_neg_eq_add, two_mul]
  · rw [if_neg hj]
    show Hp.term (some j) * Hp.term none - Hp.term none * Hp.term (some j) = 0
    rw [sub_eq_zero]
    exact (Hp.root_commute_of_not_mem hj).eq.symm

/-! ### Hermiticity -/

section Star

variable [StarRing A]

/-- If every term `h_j` is Hermitian, then so is the canonical product `h_S`
over an independent set: the factors commute pairwise, so the star of the
product (the reversed product) equals the product. -/
theorem isSelfAdjoint_independentProduct_of_terms
    (H : G.PauliFrustrationRepresentation A)
    (hH : ∀ v, IsSelfAdjoint (H.term v))
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    IsSelfAdjoint (H.independentProduct S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [H.independentProduct_empty]
      exact IsSelfAdjoint.one A
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
      have hleft := H.independentProduct_insert_left hj hS' hnonadj
      have hright := H.independentProduct_insert_right hj hS' hnonadj
      have hih := ih hS'
      show star (H.independentProduct (insert j S)) = H.independentProduct (insert j S)
      conv_lhs => rw [hleft, star_mul, hih.star_eq, (hH j).star_eq]
      exact hright.symm

/-- If every term is Hermitian, all the charges `Q_{G\W}^(k)` are Hermitian. -/
theorem isSelfAdjoint_deletedCharge_of_terms [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    (hH : ∀ v, IsSelfAdjoint (H.term v)) (W : Set V) (k : ℕ) :
    IsSelfAdjoint (H.deletedCharge W k) := by
  classical
  unfold deletedCharge operatorIndependentSetCharge
  refine Finset.sum_induction _ (fun x : A => IsSelfAdjoint x)
    (fun a b ha hb => ha.add hb) (IsSelfAdjoint.zero A) ?_
  intro S hS
  rw [mem_independentFinsetsOfCardAvoid] at hS
  exact H.isSelfAdjoint_independentProduct_of_terms hH hS.2.1

/-- If every term is Hermitian, so is the Hamiltonian. -/
theorem isSelfAdjoint_hamiltonian_of_terms [Fintype V]
    (H : G.PauliFrustrationRepresentation A)
    (hH : ∀ v, IsSelfAdjoint (H.term v)) :
    IsSelfAdjoint H.hamiltonian := by
  unfold hamiltonian
  refine Finset.sum_induction _ (fun x : A => IsSelfAdjoint x)
    (fun a b ha hb => ha.add hb) (IsSelfAdjoint.zero A) ?_
  intro j _
  exact hH j

end Star

end PauliFrustrationRepresentation

/-- The root-adjoined Pauli model of a Hamiltonian together with its
simplicial mode (v1 Definition 8, L588-595).

`operator.term (some j)` is the Hamiltonian term `h_j = b_j σ^j` with real
coupling `b_j` (`coupling j`), so `h_j² = b_j² I` (v1 L231).  The vertex `none`
of `G⁺ = G.adjoinRootAt Ks` is the new label `j_s`, and
`operator.term none = χ = σ^{j_s}` is the simplicial mode.  Adjacency in
`G⁺` is the Pauli commute/anticommute dichotomy, so `χ` anticommutes with
`h_k` exactly for `k ∈ Ks` (`⟨j_s, k⟩ = δ_{k ∈ Ks}`, L591), and the original
terms anticommute along the edges of `G` (Definition 1).

The two extra fields record the Hermiticity and the unit square of Pauli
operators, which v1 leaves implicit ("Pauli operator").  They are part of the
manuscript setup, not claims to be proved.  The facts that the couplings are
nonzero, that independent products and charges are Hermitian, and the
transport identities are theorems below, not fields.  The hypothesis that
`Ks` is a simplicial clique is passed per theorem rather than stored. -/
structure SimplicialModeHamiltonian (G : SimpleGraph V) (Ks : Set V) (A : Type w)
    [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
    extends G.PauliCliqueHamiltonianRepresentation Ks ℝ A where
  /-- Every Hamiltonian term `h_j` and the simplicial mode `χ` are Hermitian. -/
  term_selfAdjoint : ∀ v : Option V, IsSelfAdjoint (operator.term v)
  /-- The simplicial mode squares to the identity, `χ² = I`. -/
  root_sq : operator.term none * operator.term none = 1

namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]

/-- The Hamiltonian terms `h_j` as a representation of the frustration graph
`G` of `H` (Definition 1). -/
abbrev frustration (H : G.SimplicialModeHamiltonian Ks A) :
    G.PauliFrustrationRepresentation A :=
  H.operator.restrictSome

/-- The simplicial mode `χ = σ^{j_s}`. -/
abbrev root (H : G.SimplicialModeHamiltonian Ks A) : A :=
  H.operator.term none

/-- The term `h_j = b_j σ^j` squares to `b_j² I`. -/
theorem term_sq (H : G.SimplicialModeHamiltonian Ks A) (j : V) :
    H.frustration.term j * H.frustration.term j =
      algebraMap ℝ A (H.coupling j ^ 2) :=
  H.original_term_sq j

/-- Every coupling `b_j` is nonzero.  This follows from the setup: with
`j = k`, the anticommutation criterion says `h_j² ≠ -h_j²` (there are no loops
in `G⁺`), whereas `b_j = 0` would give `h_j² = 0 = -h_j²`. -/
theorem coupling_ne_zero (H : G.SimplicialModeHamiltonian Ks A) (j : V) :
    H.coupling j ≠ 0 := by
  intro h0
  have hsq := H.original_term_sq j
  rw [h0] at hsq
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, map_zero] at hsq
  have hadj : (G.adjoinRootAt Ks).Adj (some j) (some j) :=
    H.operator.adj_iff_anticommute.mpr (by rw [hsq]; simp)
  exact (G.adjoinRootAt Ks).irrefl hadj

/-- The canonical product `h_S` over an independent set `S` of the frustration
graph is Hermitian. -/
theorem isSelfAdjoint_independentProduct (H : G.SimplicialModeHamiltonian Ks A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    IsSelfAdjoint (H.frustration.independentProduct S) :=
  H.frustration.isSelfAdjoint_independentProduct_of_terms
    (fun v => H.term_selfAdjoint (some v)) hS

/-- All the charges `Q_{G\W}^(k)` are Hermitian. -/
theorem isSelfAdjoint_deletedCharge [Fintype V] [DecidableEq V]
    (H : G.SimplicialModeHamiltonian Ks A) (W : Set V) (k : ℕ) :
    IsSelfAdjoint (H.frustration.deletedCharge W k) :=
  H.frustration.isSelfAdjoint_deletedCharge_of_terms
    (fun v => H.term_selfAdjoint (some v)) W k

/-- The Hamiltonian `H = ∑ h_j` is Hermitian. -/
theorem isSelfAdjoint_hamiltonian [Fintype V]
    (H : G.SimplicialModeHamiltonian Ks A) :
    IsSelfAdjoint H.frustration.hamiltonian :=
  H.frustration.isSelfAdjoint_hamiltonian_of_terms
    (fun v => H.term_selfAdjoint (some v))

/-- The charges of the root-adjoined graph `G⁺` are Hermitian as well. -/
theorem isSelfAdjoint_operator_deletedCharge [Fintype V] [DecidableEq V]
    (H : G.SimplicialModeHamiltonian Ks A) (W : Set (Option V)) (k : ℕ) :
    IsSelfAdjoint (H.operator.deletedCharge W k) :=
  H.operator.isSelfAdjoint_deletedCharge_of_terms H.term_selfAdjoint W k

/-- The physical Hamiltonian of the underlying `PauliCliqueHamiltonianRepresentation`
is the Hamiltonian of the restricted representation. -/
theorem physicalHamiltonian_eq [Fintype V]
    (H : G.SimplicialModeHamiltonian Ks A) :
    H.physicalHamiltonian = H.frustration.hamiltonian :=
  rfl

end SimplicialModeHamiltonian

end SimpleGraph
