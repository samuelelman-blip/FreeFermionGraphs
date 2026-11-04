import FreeFermionGraphs.KrylovTreeMatrix
import FreeFermionGraphs.KrylovTreeRowBalance
import FreeFermionGraphs.KrylovBalancedStep
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Theorem 3 (Polynomial Divisibility) for even-hole-free graphs

Manuscript reference: arXiv 2305.15625v1, Theorem 3 `theorem:polynomialdivisibility`
(L1328-1336), proof L1494-1520, and Result 2 (L110-127), in the case of a
graph without even holes.  (The repo numbers some lemmas of v1 differently,
following a revised manuscript that is not available; see `docs/` and the
headers of `KrylovTreeRowBalance.lean` and `KrylovBalancedStep.lean`.)

Setting.  `G` is a finite claw-free graph, `K` a simplicial clique, and `H` a
Pauli clique Hamiltonian representation (`H.physicalHamiltonian = Σ_j t_j`,
`H.rootOperator = χ = t_{j*}`, `H.pathOperator P = h_P`).  The matrix
`T = cliqueTreeMatrix G K H.coupling` is the tree part of Eq. (decoratedtree)
(L1434-1445), indexed by the rooted induced paths of `G* = G + j*`.  When `G`
has no even hole there are no generalized cycles, `Π_𝒥 = I`, and Eq.
(decoratedtree) reduces to `T` (`eqE1WeightedAdjacency_eq_cliqueTreeMatrix`).

Main declarations.

* `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`:
  the concrete form.  In the Lean convention `[H, ·]` (without the factor `i` of
  `[iH, ·]`),
  `[H, ·]^k (χ) = Σ_P ((-2)^k (T^k)_{{j*},P}) h_P`;
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree_exists`:
  the existential form of v1's statement.  Over `ℝ`, with `ad_{iH} = [iH, ·]`,
  there exists a real matrix `M` supported on pairs of paths whose
  cardinalities have opposite parity (the weighted adjacency matrix of a
  directed bipartite graph) such that
  `ad_{iH}^k (χ) = Σ_P ((-2i)^k (M^k)_{{j*},P}) h_P`.
  The witness is `M = T`.

Proof.  By `iteratedCommutator_eq_matrixPow_sum_of_rows` (the good-row
induction of `KrylovBalancedStep.lean`) with `basis = h_·`, `source = {j*}` and
the matrix `(-2) • T`, it suffices to show that `[H, ·]` maps the row
`(-2)^n (T^n)_{{j*},·}` to the row `(-2)^{n+1} (T^{n+1})_{{j*},·}`.  The row
`(T^n)_{{j*},·}` is balanced (`cliqueTreeMatrix_pow_root_eq_of_closure`,
`cliqueTreeMatrix_pow_root_wandReverse`), so
`commutator_sum_of_isBalancedRow` gives the one-step identity.  The base case
uses `pathOperator_cliqueRootPath` (`h_{{j*}} = χ`).  For the form with
`[iH, ·]` one has `ad_{iH}^k = i^k ad_H^k`.

Fidelity.  Both theorems carry the extra premise `hfree` (no indexed induced hole
of even cardinality), which is not a hypothesis of v1 Theorem 3; this is why the
names are qualified `_of_evenHoleFree` (`docs/PAPER_FIDELITY.md`).  The other
hypotheses are the manuscript setup (`K` simplicial, `G` claw-free, `H` a
representation with `χ` anticommuting exactly with `K`); connectivity of `G`
(Result 2) is not needed.  v1 states Theorem 3 existentially with the extra
projection `Π_𝒥` onto an eigenspace of the generalized cycle symmetries `J_C`;
with no even holes there is no `J_C`, so `Π_𝒥 = I` and the projection is
absent.  The concrete form is the stronger statement: it identifies the matrix
(`T`), while the printed existential form only asserts that some real matrix
exists; the factor `(-2i)^k` of the printed form is `i^k` (from `[iH, ·] = i [H, ·]`)
times the factor `(-2)^k` of the concrete form.

The matrix-power statements need a decidable-equality instance on
`CliqueRootedInducedPath G K`; it is an instance argument (any instance works,
and `Classical.decEq` always provides one).
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}

section Concrete

variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- The row `(T^n)_{{j*},·}` of the tree matrix is balanced
(`RootedInducedPath.IsBalancedRow`): it is constant along deformation closures
and under wand reversals (v1 Lemma 16 and Eq. (pathcircle), via the closed form
of `KrylovRowClosedForm.lean`). -/
theorem isBalancedRow_cliqueTreeMatrix_pow_root [Fintype V]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R) (n : ℕ) :
    RootedInducedPath.IsBalancedRow
      (fun P : CliqueRootedInducedPath G K =>
        (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) P) := by
  classical
  refine ⟨fun P s i h => ?_, fun P w _ => ?_⟩
  · exact (cliqueTreeMatrix_pow_root_eq_of_closure hK hclaw b
      (InducedPathDeformationStep.inClosure ⟨s, i, h, rfl⟩) n).symm
  · exact (cliqueTreeMatrix_pow_root_wandReverse hK hclaw b w n).symm

/-- **Theorem 3 of v1 (Polynomial Divisibility), concrete form, for graphs
without even holes** (v1 L1328-1336, proof L1494-1520).

Let `G` be a finite claw-free graph with no even hole, `K` a simplicial clique and
`H` a Pauli clique Hamiltonian representation with couplings `b`.  Then, for
every `k`,
`[H, ·]^k (χ) = (-2)^k Σ_P (T^k)_{{j*},P} h_P`,
where `T = cliqueTreeMatrix G K b` is Eq. (decoratedtree) without generalized
cycles (`Π_𝒥 = I`).  In terms of `ad_{iH} = [iH, ·]` this is the printed
`ad_{iH}^k χ = (-2i)^k Σ_P (A^k)_{{j*},P} h_P` with `A = T`
(see `paperTheorem3_of_evenHoleFree_exists`).

The name is qualified because of the extra premise `hfree`, the absence of even
holes (`docs/PAPER_FIDELITY.md`); the other hypotheses are the manuscript
setup. -/
theorem paperTheorem3_of_evenHoleFree [Fintype V]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (H : G.PauliCliqueHamiltonianRepresentation K R A) (k : ℕ) :
    iteratedCommutator H.physicalHamiltonian k H.rootOperator =
      ∑ P : CliqueRootedInducedPath G K,
        ((-2 : R) ^ k * (cliqueTreeMatrix G K H.coupling ^ k)
          (cliqueRootPath G K) P) • H.pathOperator P := by
  set T : Matrix (CliqueRootedInducedPath G K) (CliqueRootedInducedPath G K) R :=
    cliqueTreeMatrix G K H.coupling with hT
  have hpow : ∀ n : ℕ, (((-2 : R) • T) ^ n) = (-2 : R) ^ n • T ^ n := fun n => by
    rw [smul_pow]
  have hrow : ∀ n : ℕ,
      algebraCommutator H.physicalHamiltonian
          (∑ y, (((-2 : R) • T) ^ n) (cliqueRootPath G K) y • H.pathOperator y) =
        ∑ y, (((-2 : R) • T) ^ (n + 1)) (cliqueRootPath G K) y •
          H.pathOperator y := by
    intro n
    have hbal := (isBalancedRow_cliqueTreeMatrix_pow_root hK hclaw H.coupling n).const_mul
      ((-2 : R) ^ n)
    have key := H.commutator_sum_of_isBalancedRow hK hclaw hfree _ hbal
    simp only [hpow, Matrix.smul_apply, smul_eq_mul]
    rw [key]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    congr 1
    have hstep : (T ^ (n + 1)) (cliqueRootPath G K) Q =
        ∑ P, (T ^ n) (cliqueRootPath G K) P * T P Q := by
      rw [pow_succ, Matrix.mul_apply]
    rw [hstep, pow_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hT]
    ring
  have := iteratedCommutator_eq_matrixPow_sum_of_rows H.physicalHamiltonian
    H.pathOperator ((-2 : R) • T) (cliqueRootPath G K) hrow k
  rw [H.pathOperator_cliqueRootPath] at this
  rw [this]
  simp only [hpow, Matrix.smul_apply, smul_eq_mul]

end Concrete

section ComplexScalars

variable {A : Type w} [Ring A] [Algebra ℂ A]

/-- The commutator with a complex multiple of `X` is the complex multiple of the
commutator. -/
theorem algebraCommutator_smul_left (c : ℂ) (X x : A) :
    algebraCommutator (c • X) x = c • algebraCommutator X x := by
  simp only [algebraCommutator, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The commutator is complex linear in its second argument. -/
theorem algebraCommutator_smul_right (c : ℂ) (X x : A) :
    algebraCommutator X (c • x) = c • algebraCommutator X x := by
  simp only [algebraCommutator, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- `ad_{c X}^k = c^k ad_X^k`: in particular `[iH, ·]^k = i^k [H, ·]^k`. -/
theorem iteratedCommutator_smul_left (c : ℂ) (X x : A) (k : ℕ) :
    iteratedCommutator (c • X) k x = c ^ k • iteratedCommutator X k x := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [iteratedCommutator_succ, ih, algebraCommutator_smul_left,
        algebraCommutator_smul_right, iteratedCommutator_succ, pow_succ, mul_smul,
        smul_comm]

end ComplexScalars

section Existential

variable {A : Type w} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Theorem 3 of v1 (Polynomial Divisibility), existential form, for graphs
without even holes** (v1 L1328-1336, with `Π_𝒥 = I`).

Let `G` be a finite claw-free graph with no even hole, `K` a simplicial clique and
`H` a Pauli clique Hamiltonian representation over `ℝ`.  Then there exists a real
matrix `M`, indexed by the rooted induced paths of `G* = G + j*`, which is the
weighted adjacency matrix of a directed bipartite graph (every nonzero entry
`M_{PQ}` has `|P| + |Q|` odd, so `|P| mod 2` is the bipartition), such that for all
`k`
`ad_{iH}^k (χ) = (-2i)^k Σ_P (M^k)_{{j*},P} h_P`,  with `ad_{iH} = [iH, ·]`.

The witness is the tree matrix `M = cliqueTreeMatrix G K b`
(`paperTheorem3_of_evenHoleFree` gives the concrete form with `[H, ·]`).  The
name is qualified because of the extra premise `hfree` (`docs/PAPER_FIDELITY.md`).
The projection `Π_𝒥` of v1 does not occur: without even holes there are no
generalized cycle symmetries `J_C`. -/
theorem paperTheorem3_of_evenHoleFree_exists [Fintype V]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) :
    ∃ M : Matrix (CliqueRootedInducedPath G K) (CliqueRootedInducedPath G K) ℝ,
      (∀ P Q, M P Q ≠ 0 → Odd (P.path.card + Q.path.card)) ∧
      ∀ k : ℕ, iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator =
        ∑ P, ((-2 * Complex.I) ^ k * ((M ^ k) (cliqueRootPath G K) P : ℂ)) •
          H.pathOperator P := by
  refine ⟨cliqueTreeMatrix G K H.coupling,
    fun P Q h => cliqueTreeMatrix_ne_zero_imp_odd H.coupling h, fun k => ?_⟩
  rw [iteratedCommutator_smul_left, paperTheorem3_of_evenHoleFree hK hclaw hfree H k,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  have hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x := fun r x => by
    calc r • x = r • ((1 : ℂ) • x) := by rw [one_smul]
      _ = (r • (1 : ℂ)) • x := (smul_assoc r (1 : ℂ) x).symm
      _ = (r : ℂ) • x := by rw [Complex.real_smul, mul_one]
  rw [hreal, smul_smul, mul_pow]
  push_cast
  ring_nf

end Existential

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
