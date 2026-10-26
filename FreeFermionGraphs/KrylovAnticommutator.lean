import FreeFermionGraphs.KrylovTreeMatrix
import FreeFermionGraphs.Theorem3EvenHoleFree

/-!
# Corollary 1 (the anticommutator matrix), with the corrected sign

Manuscript reference: arXiv 2305.15625v1, Corollary 12
(`corollary:modifiedanticommutationrelation`, L1341-1392; repository/revised
manuscript Corollary 1) and the printed formula of Result 2,
Eq. (`modifiedcommutationrelation`) (L117-121).  (v1 numbers all corollaries with
one global counter, so this corollary is the 12th one, and v1 Corollary 1 is the
unrelated `corollary:vertexcycleneighboring` at L671.  The repository numbers
corollaries and lemmas following a revised manuscript that is not available, in
which this is Corollary 1; the declaration names `paperCorollary1_*` use the
repository number.  Here v1 labels and line numbers are cited.)

The statement.  Let `a_k = ad_H^k χ`.  Once Theorem 3 gives
`a_k Π = (-2)^k Σ_P (T^k)_{{j*},P} h_P Π` (Lean convention `ad_H = [H, ·]`
without the factor `i` of the manuscript's `ad = [iH, ·]`), the anticommutators
of the Krylov vectors are scalars times `Π`:

`{a_j, a_k} Π = 2 (-1)^j (-2)^(j+k) (T^(j+k))_{{j*},{j*}} Π`.

Main declarations.

* `anticommutator_iteratedCommutator_of_expansion`: the abstract form.  Its
  hypotheses are the manuscript setup (`χ² = 1`, `[H, Π] = 0`, `[χ, Π] = 0`,
  `h_{{j*}} = χ`, `χ` anticommutes with `h_P` for `P ≠ {j*}`) together with the
  Krylov expansion of Theorem 3 *as data on the input side*; the conclusion is
  the anticommutator formula, which is not assumed.
* `krylovGram_symm`: the scalar `2 (-1)^j (-2)^(j+k) (T^(j+k))_{j*j*}` is
  symmetric in `(j, k)` once the odd powers vanish at the root (they do for the
  bipartite tree matrix, `cliqueTreeMatrix_pow_cliqueRootPath_eq_zero_of_odd`).
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.rootOperator_anticommute_pathOperator`:
  `χ` anticommutes with `h_P` for every rooted induced path `P ≠ {j*}`: `P_1` is
  the only vertex of `P` adjacent to `j*`.
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`:
  the instance for claw-free graphs with a simplicial clique and no even hole,
  where Theorem 3 holds with `Π = I` and `T = cliqueTreeMatrix`
  (`paperTheorem3_of_evenHoleFree`).  The even-hole-free hypothesis is not part
  of v1 Corollary 12 (repository Corollary 1), hence the qualified name
  (`docs/PAPER_FIDELITY.md`).
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree_ad`:
  the same in the manuscript convention `ad = [iH, ·]`:
  `{ad^j χ, ad^k χ} = 2 M_{jk}` with the corrected
  `M_{jk} = (-1)^j (-2i)^(j+k) (A^(j+k))_{j*j*}`.
* `krylovGramI_symm`, `krylovGramI_real`: that corrected `M` is symmetric and real
  once the odd powers vanish at the root.

Correction of v1 (sign error).  v1's proof of Corollary 12 solves the recursion
`{ad^j χ, ad^k χ} = -{ad^(j-1) χ, ad^(k+1) χ}` (L1380) as
`{ad^j χ, ad^k χ} = (-i)^j · 2 M_{0,j+k}` (L1384), then drops the factor
`(-i)^j` altogether (L1385) and concludes the printed
`M_{jk} = (-2i)^(j+k) (A^(j+k))_{j*j*}` (L1389), with the same formula in Result 2
(L119-120).  The recursion has factor `-1` per step, not `-i`, and
`M_{0,m} = (-2i)^m (A^m)_{j*j*}` (L1359), so the correct solution is

`M_{jk} = (-1)^j M_{0,j+k} = (-1)^j (-2i)^(j+k) (A^(j+k))_{j*j*}`.

The factor `(-1)^j` is missing in the printed formula.  Smallest
counterexample: `G` a single vertex `a`, `K = {a}`, `H = t_a` with
`t_a² = b²`, and `χ` anticommuting with `t_a`.  Then
`ad χ = [i t_a, χ] = -2i χ t_a`, so `(ad χ)² = (-2i)² (χ t_a)² = 4 b²` (as
`(χ t_a)² = -b²`) and `{ad χ, ad χ} = 8 b²`, that is `M_{11} = 4 b² > 0`, as
required by the positive definiteness claimed in Result 2.  The printed formula
gives `M_{11} = (-2i)² (A²)_{j*j*} = -4 b²` (`(A²)_{j*j*} = b²`), which is
negative.  The theorem `printedCorollary1_fails_single_vertex` below checks this
in `2 × 2` complex matrices (`χ = σ_x`, `H = σ_z`, `b = 1`); the
corrected formula is `paperCorollary1_of_evenHoleFree_ad`.

Not covered here: positive definiteness of `M` and the Majorana modes constructed
after the Corollary.  Both need a sector trace (v1 argues positivity with the
full trace although `M` depends on the sector), and the Majorana paragraph of v1
carries further errors (the factor `i^(j mod 2)` makes the odd modes
anti-Hermitian).  The hypothesis `χ² = 1` is a
hypothesis, not a field of `PauliCliqueHamiltonianRepresentation` (in v1
`χ = σ^{j*}` is a Pauli string).  The hypothesis `[χ, Π] = 0` corresponds to
v1's claim that `χ` commutes with the generalized cycle symmetries (Result 2),
and `[H, Π] = 0` to `[H, J_C] = 0` (Theorem 1(ii)); for graphs without even
holes `Π = I`.  For general `G` the abstract theorem is to be instantiated with
the sector expansion of a later package.
-/

open scoped BigOperators

universe u v w

/-! ### Algebraic lemmas on the commutator -/

section Algebra

variable {A : Type w} [Ring A]

/-- The commutator with `H` is a derivation of the anticommutator:
`[H, {x, y}] = {[H, x], y} + {x, [H, y]}`. -/
theorem algebraCommutator_anticommutator (H x y : A) :
    algebraCommutator H (x * y + y * x) =
      (algebraCommutator H x * y + y * algebraCommutator H x) +
        (x * algebraCommutator H y + algebraCommutator H y * x) := by
  unfold algebraCommutator
  noncomm_ring

/-- If `X Π` is a scalar multiple of `Π` and `H` commutes with `Π`, then
`[H, X] Π = 0`. -/
theorem algebraCommutator_mul_eq_zero_of_mul_eq_smul {R : Type v} [CommRing R]
    [Algebra R A] (H X Pr : A) (hHP : Commute H Pr) (s : R) (hX : X * Pr = s • Pr) :
    algebraCommutator H X * Pr = 0 := by
  have h1 : H * X * Pr = s • (H * Pr) := by
    rw [mul_assoc, hX, mul_smul_comm]
  have h2 : X * H * Pr = s • (H * Pr) := by
    rw [mul_assoc, hHP.eq, ← mul_assoc, hX, smul_mul_assoc, ← hHP.eq]
  unfold algebraCommutator
  rw [sub_mul, h1, h2, sub_self]

end Algebra

/-! ### The abstract anticommutator formula -/

section Abstract

variable {X : Type u} {R : Type v} {A : Type w}
variable [Fintype X] [DecidableEq X] [CommRing R] [Ring A] [Algebra R A]

/-- The case `j = 0` of the anticommutator formula: `{χ, a_k} Π` only sees the
coefficient of `h_{root} = χ` in the expansion of `a_k Π`. -/
theorem anticommutator_root_iteratedCommutator_of_expansion
    (H χ Pr : A) (hχ : χ * χ = 1) (hχP : Commute χ Pr)
    (h : X → A) (root : X) (hroot : h root = χ)
    (hanti : ∀ P, P ≠ root → χ * h P = -(h P * χ))
    (T : Matrix X X R)
    (hKry : ∀ n, iteratedCommutator H n χ * Pr =
      ∑ P, ((-2 : R) ^ n * (T ^ n) root P) • (h P * Pr))
    (k : ℕ) :
    (χ * iteratedCommutator H k χ + iteratedCommutator H k χ * χ) * Pr =
      ((2 : R) * (-2) ^ k * (T ^ k) root root) • Pr := by
  have hterm : ∀ P, (χ * h P + h P * χ) * Pr = if P = root then (2 : R) • Pr else 0 := by
    intro P
    by_cases hP : P = root
    · subst hP
      rw [if_pos rfl, hroot, hχ, add_mul, one_mul, two_smul]
    · rw [if_neg hP, hanti P hP, neg_add_cancel, zero_mul]
  have hP : ∀ P, χ * (h P * Pr) + (h P * Pr) * χ = (χ * h P + h P * χ) * Pr := by
    intro P
    simp only [add_mul, mul_assoc, hχP.eq]
  have hsplit : ∀ a : A, (χ * a + a * χ) * Pr = χ * (a * Pr) + (a * Pr) * χ := by
    intro a
    simp only [add_mul, mul_assoc, hχP.eq]
  rw [hsplit, hKry k, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  have hsum : ∀ P ∈ (Finset.univ : Finset X),
      χ * (((-2 : R) ^ k * (T ^ k) root P) • (h P * Pr)) +
        (((-2 : R) ^ k * (T ^ k) root P) • (h P * Pr)) * χ =
      ((-2 : R) ^ k * (T ^ k) root P) • (if P = root then (2 : R) • Pr else 0) := by
    intro P _
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hP, hterm]
  rw [Finset.sum_congr rfl hsum]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  congr 1
  ring

/-- **v1 Corollary 12 (`corollary:modifiedanticommutationrelation`, L1341-1392;
repository Corollary 1), abstract form, with the corrected sign.**

Let `a_n = [H, ·]^n χ`.  Suppose `χ² = 1`, `[H, Π] = 0`, `[χ, Π] = 0`, the root
operator `h_{root}` is `χ`, `χ` anticommutes with `h_P` for `P ≠ root`, and the
Krylov expansion `a_n Π = (-2)^n Σ_P (T^n)_{root,P} h_P Π` holds for all `n`
(Theorem 3).  Then
`{a_j, a_k} Π = 2 (-1)^j (-2)^(j+k) (T^(j+k))_{root,root} Π`.

The proof is the induction of v1 (L1351-1392): the case `j = 0` is
`anticommutator_root_iteratedCommutator_of_expansion`; the step uses that `[H, ·]`
is a derivation of the anticommutator (`algebraCommutator_anticommutator`) and
that `[H, s Π] = 0`, whence `{a_j, a_k} Π + {a_{j-1}, a_{k+1}} Π = 0`.  The factor
is therefore `(-1)^j`, not the `(-i)^j` or `1` of v1's printed solution of the
recursion (see the module docstring).  In the manuscript convention
`ad = [iH, ·]` the factor `(-2)^(j+k)` becomes `(-2i)^(j+k)`
(`paperCorollary1_of_evenHoleFree_ad`). -/
theorem anticommutator_iteratedCommutator_of_expansion
    (H χ Pr : A) (hχ : χ * χ = 1) (hHP : Commute H Pr) (hχP : Commute χ Pr)
    (h : X → A) (root : X) (hroot : h root = χ)
    (hanti : ∀ P, P ≠ root → χ * h P = -(h P * χ))
    (T : Matrix X X R)
    (hKry : ∀ n, iteratedCommutator H n χ * Pr =
      ∑ P, ((-2 : R) ^ n * (T ^ n) root P) • (h P * Pr))
    (j k : ℕ) :
    (iteratedCommutator H j χ * iteratedCommutator H k χ +
        iteratedCommutator H k χ * iteratedCommutator H j χ) * Pr =
      ((2 : R) * (-1) ^ j * (-2) ^ (j + k) * (T ^ (j + k)) root root) • Pr := by
  induction j generalizing k with
  | zero =>
      have h0 := anticommutator_root_iteratedCommutator_of_expansion H χ Pr hχ hχP h root
        hroot hanti T hKry k
      rw [iteratedCommutator_zero, h0]
      simp
  | succ j ih =>
      have hder := algebraCommutator_anticommutator H (iteratedCommutator H j χ)
        (iteratedCommutator H k χ)
      have hzero := algebraCommutator_mul_eq_zero_of_mul_eq_smul H _ Pr hHP _ (ih k)
      rw [hder, ← iteratedCommutator_succ, ← iteratedCommutator_succ, add_mul, ih (k + 1)]
        at hzero
      rw [eq_neg_of_add_eq_zero_left hzero, ← neg_smul, show j + 1 + k = j + (k + 1) by omega]
      congr 1
      ring

end Abstract

/-! ### Symmetry of the Gram scalar -/

/-- `(-1)^j = (-1)^k` when `j + k` is even. -/
private theorem neg_one_pow_eq_of_even_add {S : Type*} [CommRing S] {j k : ℕ}
    (h : Even (j + k)) : (-1 : S) ^ j = (-1) ^ k := by
  rcases Nat.even_or_odd j with hj | hj
  · have hk : Even k := by
      rw [Nat.even_iff] at hj h ⊢
      omega
    rw [hj.neg_one_pow, hk.neg_one_pow]
  · have hk : Odd k := by
      rw [Nat.odd_iff] at hj
      rw [Nat.even_iff] at h
      rw [Nat.odd_iff]
      omega
    rw [hj.neg_one_pow, hk.neg_one_pow]

/-- **Symmetry of the corrected Gram scalar** (v1 Corollary 12, repository
Corollary 1: "`M` is real symmetric", statement at L1348, proof at L1391; the
printed formula for `M_{jk}` is at L1388-1389).  If the odd powers of `T` vanish at
the root (for the bipartite clique tree matrix this is
`cliqueTreeMatrix_pow_cliqueRootPath_eq_zero_of_odd`), then
`2 (-1)^j (-2)^(j+k) (T^(j+k))_{root,root}` is symmetric in `(j, k)`: for odd
`j + k` both sides vanish, and for even `j + k` the signs `(-1)^j` and `(-1)^k`
agree. -/
theorem krylovGram_symm {X R : Type*} [Fintype X] [DecidableEq X] [CommRing R]
    (T : Matrix X X R) (root : X)
    (hpar : ∀ n, Odd n → (T ^ n) root root = 0) (j k : ℕ) :
    (2 : R) * (-1) ^ j * (-2) ^ (j + k) * (T ^ (j + k)) root root =
      (2 : R) * (-1) ^ k * (-2) ^ (j + k) * (T ^ (j + k)) root root := by
  rcases Nat.even_or_odd (j + k) with he | ho
  · rw [neg_one_pow_eq_of_even_add he]
  · rw [hpar _ ho]
    simp

/-! ### The manuscript convention `ad = [iH, ·]` -/

section Complex

variable {X : Type u}
variable [Fintype X] [DecidableEq X]

/-- The corrected Gram scalar in the manuscript convention is symmetric:
`(-1)^j (-2i)^(j+k) (A^(j+k))_{root,root} = (-1)^k (-2i)^(j+k) (A^(j+k))_{root,root}`
when the odd powers of `A` vanish at the root. -/
theorem krylovGramI_symm (A : Matrix X X ℝ) (root : X)
    (hpar : ∀ n, Odd n → (A ^ n) root root = 0) (j k : ℕ) :
    (2 : ℂ) * (-1) ^ j * (-2 * Complex.I) ^ (j + k) * (((A ^ (j + k)) root root : ℝ) : ℂ) =
      (2 : ℂ) * (-1) ^ k * (-2 * Complex.I) ^ (j + k) *
        (((A ^ (j + k)) root root : ℝ) : ℂ) := by
  rcases Nat.even_or_odd (j + k) with he | ho
  · rw [neg_one_pow_eq_of_even_add he]
  · rw [hpar _ ho]
    simp

/-- The corrected Gram scalar in the manuscript convention is real when the odd
powers of `A` vanish at the root: for odd `j + k` it is zero, and for even `j + k`
it is `2 (-1)^j (-4)^((j+k)/2) (A^(j+k))_{root,root}`, as `(-2i)^2 = -4`. -/
theorem krylovGramI_real (A : Matrix X X ℝ) (root : X)
    (hpar : ∀ n, Odd n → (A ^ n) root root = 0) (j k : ℕ) :
    ∃ r : ℝ, (2 : ℂ) * (-1) ^ j * (-2 * Complex.I) ^ (j + k) *
      (((A ^ (j + k)) root root : ℝ) : ℂ) = (r : ℂ) := by
  rcases Nat.even_or_odd (j + k) with ⟨m, hm⟩ | ho
  · refine ⟨2 * (-1) ^ j * (-4) ^ m * (A ^ (j + k)) root root, ?_⟩
    have hsq : (-2 * Complex.I) ^ 2 = -4 := by
      rw [mul_pow, Complex.I_sq]
      norm_num
    rw [hm, ← two_mul, pow_mul, hsq]
    push_cast
    ring
  · refine ⟨0, ?_⟩
    rw [hpar _ ho]
    simp

end Complex

/-! ### Root anticommutation and the even-hole-free instance -/

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {K : Set V}

namespace PauliCliqueHamiltonianRepresentation

variable {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]

/-- The root operator `χ = t_{j*}` anticommutes with `h_P` for every rooted
induced path `P ≠ {j*}` of `G* = G + j*`.

A path `P ≠ {j*}` has at least two vertices, `P_0 = j*`, and since `P` is induced
in `G*` the only path vertex adjacent to `j*` is `P_1`; so the neighbour count
of `j*` on `P` is one and `term_mul_pathOperator` gives the sign `-1`. -/
theorem rootOperator_anticommute_pathOperator
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P : CliqueRootedInducedPath G K} (hP : P ≠ cliqueRootPath G K) :
    H.rootOperator * H.pathOperator P = -(H.pathOperator P * H.rootOperator) := by
  have hcard : 2 ≤ P.path.card := by
    have h1 : ¬P.path.card = 1 := fun h =>
      hP ((RootedInducedPath.eq_cliqueRootPath_iff P).2 h)
    have h2 := P.path.nonempty
    omega
  have hroot : P.path.vertex ⟨0, P.path.nonempty⟩ = none := P.root_eq
  have hset : P.path.neighborIndexSet none = {⟨1, by omega⟩} := by
    ext i
    rw [IndexedInducedPath.mem_neighborIndexSet, Set.mem_singleton_iff]
    have hadj := P.path.adj_iff ⟨0, P.path.nonempty⟩ i
    rw [hroot] at hadj
    rw [hadj, Fin.ext_iff]
    dsimp only
    omega
  have key := H.operator.term_mul_pathOperator none P.path
  rw [hset, Set.ncard_singleton, pow_one, neg_one_mul] at key
  exact key

variable [Fintype V] [DecidableEq (CliqueRootedInducedPath G K)]

/-- **v1 Corollary 12 (anticommutator matrix; repository Corollary 1) for graphs
without even holes, with the corrected sign** (`corollary:modifiedanticommutationrelation`,
v1 L1341-1392, Result 2 Eq. (`modifiedcommutationrelation`) L117-121).

For a finite claw-free graph `G` without even holes, a simplicial clique `K`, and
a Pauli clique Hamiltonian representation `H` whose root operator `χ` squares to
`1`, in the convention `ad_H = [H, ·]`,
`{ad_H^j χ, ad_H^k χ} = 2 (-1)^j (-2)^(j+k) (T^(j+k))_{{j*},{j*}}`,
where `T = cliqueTreeMatrix G K H.coupling`.  Without even holes `Π_𝒥 = I`, so
the projection of v1 is absent.  In the manuscript convention `ad = [iH, ·]` this
is `paperCorollary1_of_evenHoleFree_ad`.

The name is qualified because of the extra premise `hfree` (no indexed induced
hole of even cardinality), which is not a hypothesis of v1 Corollary 12.  The
hypothesis `hχ : χ² = 1` is a manuscript fact (`χ` is a Pauli string) that is not
a field of the representation.  The sign `(-1)^j` is the correction of v1's
printed formula (see the module docstring for the one-vertex counterexample).
Connectivity of `G` (Result 2) is not needed. -/
theorem paperCorollary1_of_evenHoleFree
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (hχ : H.rootOperator * H.rootOperator = 1) (j k : ℕ) :
    iteratedCommutator H.physicalHamiltonian j H.rootOperator *
          iteratedCommutator H.physicalHamiltonian k H.rootOperator +
        iteratedCommutator H.physicalHamiltonian k H.rootOperator *
          iteratedCommutator H.physicalHamiltonian j H.rootOperator =
      algebraMap R A ((2 : R) * (-1) ^ j * (-2) ^ (j + k) *
        (cliqueTreeMatrix G K H.coupling ^ (j + k)) (cliqueRootPath G K)
          (cliqueRootPath G K)) := by
  have key := anticommutator_iteratedCommutator_of_expansion H.physicalHamiltonian
    H.rootOperator 1 hχ (Commute.one_right _) (Commute.one_right _) H.pathOperator
    (cliqueRootPath G K) H.pathOperator_cliqueRootPath
    (fun P hP => H.rootOperator_anticommute_pathOperator hP)
    (cliqueTreeMatrix G K H.coupling)
    (fun n => by
      rw [mul_one]
      simp only [mul_one]
      exact paperTheorem3_of_evenHoleFree hK hclaw hfree H n) j k
  rw [mul_one, ← Algebra.algebraMap_eq_smul_one] at key
  exact key

end PauliCliqueHamiltonianRepresentation

section ManuscriptConvention

variable {A : Type w} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
variable [Fintype V] [DecidableEq (CliqueRootedInducedPath G K)]

/-- **v1 Corollary 12 (repository Corollary 1) in the manuscript convention
`ad = [iH, ·]`, for graphs without even holes, with the corrected sign**
(`corollary:modifiedanticommutationrelation`, v1 L1341-1392, Result 2 Eq.
(`modifiedcommutationrelation`) L117-121).

With `A = cliqueTreeMatrix G K H.coupling` (real) and `ad = [iH, ·]`,
`{ad^j χ, ad^k χ} = 2 M_{jk}` where
`M_{jk} = (-1)^j (-2i)^(j+k) (A^(j+k))_{{j*},{j*}}`.
The printed formula of v1 lacks the factor `(-1)^j` (see the module docstring and
`printedCorollary1_fails_single_vertex`).  Reality and symmetry of `M` follow from
the vanishing of the odd powers at the root (`krylovGramI_real`, `krylovGramI_symm`,
`cliqueTreeMatrix_pow_cliqueRootPath_eq_zero_of_odd`).  The name is qualified
because of the extra premise `hfree` (no even hole) and `χ² = 1` is a hypothesis
(`PauliCliqueHamiltonianRepresentation` has no such field). -/
theorem PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree_ad
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A)
    (hχ : H.rootOperator * H.rootOperator = 1) (j k : ℕ) :
    iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
          iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
        iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
          iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator =
      ((2 : ℂ) * ((-1) ^ j * (-2 * Complex.I) ^ (j + k) *
        (((cliqueTreeMatrix G K H.coupling ^ (j + k)) (cliqueRootPath G K)
          (cliqueRootPath G K) : ℝ) : ℂ))) • (1 : A) := by
  have hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x := fun r x => by
    calc r • x = r • ((1 : ℂ) • x) := by rw [one_smul]
      _ = (r • (1 : ℂ)) • x := (smul_assoc r (1 : ℂ) x).symm
      _ = (r : ℂ) • x := by rw [Complex.real_smul, mul_one]
  have hcor := H.paperCorollary1_of_evenHoleFree hK hclaw hfree hχ j k
  rw [iteratedCommutator_smul_left, iteratedCommutator_smul_left, smul_mul_smul_comm,
    smul_mul_smul_comm, mul_comm (Complex.I ^ k) (Complex.I ^ j), ← smul_add, hcor,
    Algebra.algebraMap_eq_smul_one, hreal, smul_smul]
  congr 1
  push_cast
  rw [mul_pow, pow_add]
  ring

end ManuscriptConvention

end SimpleGraph

/-! ### The printed sign is wrong: the one-vertex counterexample -/

namespace KrylovAnticommutator

/- Data of the smallest case `G = {a}`, `K = {a}` in `2 × 2` complex matrices with
`b = 1`: the root operator `χ = σ_x`, the Hamiltonian `H = t_a = σ_z`
(`χ² = 1`, `χ t_a = -t_a χ`, `t_a² = b² = 1`) and the tree matrix `A` on the two
paths `{j*}`, `{j*, a}` (weight `1` for the extension and `b² = 1` for the
contraction). -/
namespace SingleVertex

/-- The root operator `χ = σ_x`. -/
def chi : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Hamiltonian `H = t_a = σ_z` (`b = 1`). -/
def ham : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The tree matrix `A` on the paths `{j*}`, `{j*, a}` for `b = 1`. -/
def treeMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

end SingleVertex

open SingleVertex in
/-- **v1's printed formula for `M_{11}` has the wrong sign** (v1 Corollary 12,
repository Corollary 1, L1388-1391; Result 2 L119-120).  For `G = {a}`, `K = {a}`,
`b = 1` (`χ = σ_x`, `H = σ_z`, `A` the two-path tree matrix) with `ad = [iH, ·]`:

* `χ² = 1` and `χ H = -H χ`;
* `{ad χ, ad χ} = 2 M_{11}` with the corrected `M_{11} = (-1)^1 (-2i)^2 (A²)_{00} = 4`,
  that is `{ad χ, ad χ} = 8 I`;
* the printed `M_{11} = (-2i)^2 (A²)_{00} = -4` would give `-8 I`, and `8 I ≠ -8 I`.

So the corrected formula of `paperCorollary1_of_evenHoleFree_ad` is the right one,
and the printed one contradicts the positive definiteness of `M` claimed in
Result 2. -/
theorem printedCorollary1_fails_single_vertex :
    chi * chi = 1 ∧ chi * ham = -(ham * chi) ∧
    iteratedCommutator (Complex.I • ham) 1 chi * iteratedCommutator (Complex.I • ham) 1 chi +
        iteratedCommutator (Complex.I • ham) 1 chi *
          iteratedCommutator (Complex.I • ham) 1 chi =
      ((2 : ℂ) * ((-1) ^ 1 * (-2 * Complex.I) ^ (1 + 1) * (treeMatrix ^ (1 + 1)) 0 0)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    iteratedCommutator (Complex.I • ham) 1 chi * iteratedCommutator (Complex.I • ham) 1 chi +
        iteratedCommutator (Complex.I • ham) 1 chi *
          iteratedCommutator (Complex.I • ham) 1 chi ≠
      ((2 : ℂ) * ((-2 * Complex.I) ^ (1 + 1) * (treeMatrix ^ (1 + 1)) 0 0)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hA2 : (treeMatrix ^ (1 + 1)) 0 0 = 1 := by
    rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [treeMatrix]
  have hI : (-2 * Complex.I) ^ (1 + 1) = -4 := by
    rw [pow_two]
    have := Complex.I_mul_I
    linear_combination 4 * this
  have ha : iteratedCommutator (Complex.I • ham) 1 chi =
      !![0, 2 * Complex.I; -2 * Complex.I, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [iteratedCommutator, algebraCommutator, ham, chi] <;>
      ring
  have hsum : iteratedCommutator (Complex.I • ham) 1 chi *
        iteratedCommutator (Complex.I • ham) 1 chi +
      iteratedCommutator (Complex.I • ham) 1 chi *
        iteratedCommutator (Complex.I • ham) 1 chi = (8 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [ha]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp [Complex.I_sq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [chi, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [chi, ham, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hsum, hA2, hI]
    norm_num
  · rw [hsum, hA2, hI]
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
    norm_num at this

end KrylovAnticommutator
