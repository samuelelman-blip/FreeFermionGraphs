import FreeFermionGraphs.CycleSymmetrySectors
import FreeFermionGraphs.ModeSectorPositivity

/-!
# Cross-sector relations of the incognito modes

Manuscript (arXiv 2305.15625 v1): Theorem 2 (`main.tex` L1248-1264), the statement
`[Π_J, ψ_{J',j}] = 0` for all `J`, `J'`, `j` (L1259-1263), and Lemma 14
(`LadderAnticommutationRelations`, L1306-1313, proved at L2058-2104):
`{ψ_{J,+j}, ψ_{J',-k}} = δ_{J,J'} δ_{jk} Π_J`.  In the numbering of the revised manuscript
used by the repository, v1 Lemma 14 is "Lemma 4".

This module is the second of the three pieces of the assembly of Theorem 2 (the first is
`CycleSymmetrySectors`, which produces the sectors `Π_l`; the last is the per-sector conclusions
and the assembly).  It proves the *cross-sector* half of the canonical anticommutation relations
of the incognito modes, and the commutation of the sector projections with the modes of all
sectors, for the actual sectors `Π_l` of the cycle symmetries; the within-sector relations
(`LadderAnticommutation`) are collected in the same statements.

## What is proved

The proof is the one sentence of v1 ("the cross-sector `δ_{J,J'}` is immediate"): the modes
`ψ_{l,j}^± = N_{l,j}^{-1} Π_l T(∓u_{l,j}) χ T(±u_{l,j})` of a sector `l` lie in `Π_l A Π_l`
(`ModeSector.Pi_mul_mode`), and `Π_l Π_{l'} = 0` for `l ≠ l'`.  Neither claw-freeness nor the
non-degeneracy data enter the cross-sector statements; they enter only the within-sector
relations of `LadderAnticommutation`.

* `ModeSector.Orthogonal S S'` : `Π_S Π_{S'} = 0`; it is symmetric (`Orthogonal.symm`).
* `ModeSector.Orthogonal.Pi_mul_mode`, `commute_mode`, `mode_mul_mode`, `mode_anticomm_mode`: for
  orthogonal sectors `Π_S A'_w = 0 = A'_w Π_S` (so `[Π_S, A'_w] = 0`) and `A_v A'_w = 0 = A'_w A_v`,
  for the unnormalised modes `A_v = Π T(-v) χ T(v)` at arbitrary real `v`, `w`.
* `ModeSector.Orthogonal.Pi_mul_psiPlus`, `commute_psiPlus`, `psiPlus_anticomm_psiMinus`, ...:
  the same for the normalised modes `ψ_j^± = Nondegenerate.psiPlus/psiMinus`: the four
  anticommutators `{ψ_j^±, ψ'^±_k} = 0` across orthogonal sectors, and the `†` form
  (`(ψ_j^+)† = ψ_j^-`, `Nondegenerate.star_psiPlus`).
* `ModeSector.Family.*`: for a family `S : ι → H.ModeSector` of pairwise orthogonal sectors with
  non-degeneracy data `D l`, and `ψ l j = (D l).psiPlus j`:
  `Π_l ψ_{l',j} = ψ_{l',j} Π_l = δ_{l,l'} ψ_{l',j}` (`Pi_mul_psi`, `psi_mul_Pi`,
  `commute_Pi_psi`, `commute_Pi_star_psi`);
  `{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l` (`psi_anticomm_star_psi`, with the two cases
  `psi_anticomm_star_psi_self` and `psi_anticomm_star_psi_of_ne`);
  `{ψ_{l,j}, ψ_{l',k}} = 0` (`psi_anticomm_psi`) and its adjoint `{ψ^†, ψ^†} = 0`
  (`star_psi_anticomm_star_psi`).  The Kronecker symbol is written `if l = l' ∧ HEq j k`, because
  `j : Fin (D l).r` and `k : Fin (D l').r` live in different types.
* `explicitIncognitoMode H Π z_G z_K u` : the explicit mode `N⁻¹ Π T(-u) χ T(u)`,
  `N = 4 u √(z_K(-u²) z_G'(-u²))` of v1 Definition 9 and L2097; `psiPlus_eq_explicitIncognitoMode`
  says that `Nondegenerate.psiPlus` is this expression.
* `SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute`: the same
  statements for the sectors of `CycleSymmetrySectors` (`jointModeSector`) in
  `Matrix (Fin d) (Fin d) ℂ`, in the form needed to finish Theorem 2: there are `Λ`, `Π_l`, the
  `r_l = deg z_{∅,l}` positive distinct roots `u_{l,j}` with their non-degeneracy facts, and the
  explicit modes `ψ_{l,j}`, such that for all `l, l' ∈ Λ` the commutation and the canonical
  anticommutation relations hold.

`CrossSectorRelationsExample` checks that the hypotheses of the assembled theorem are jointly
satisfiable.

## Premises

* `hJ : H.frustration.CycleSymmetriesCommute` is v1 Theorem 1(iii) (`[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0`),
  not yet formalised; it is needed only to *produce* the joint eigenprojections `Π_l`, so the
  assembled theorem carries the suffix `_of_cycleSymmetry_commute` (docs/PAPER_FIDELITY.md).
* `hND` is the non-degeneracy hypothesis of the solution, per occurring sector `l`:
  `IsCoprime z_{∅,l} z_{Ks,l}`.  For real polynomials this is equivalent to v1's tacit
  assumption that `Z_{G,J}` and `Z_{G∖Ks,J}` have no common complex root (coprimality gives no
  common root directly; the converse needs the Fundamental Theorem of Algebra, which is not
  available in this build, see `ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero`).
  v1's Theorem 2 is false without it (the `C₄` counterexample with `J = ±1`).
* The abstract statements (everything before the assembled theorem) have, besides the
  orthogonality of the sectors and the non-degeneracy data `D l` as explicit arguments, only the
  hypotheses of the cited within-sector relations (`hclaw : G.IsClawFree`,
  `hKs : G.IsSimplicialClique Ks`); the cross-sector statements need neither.

## Deviations from v1

* v1 states the cross-sector commutation `[Π_J, ψ_{J',j}] = 0` and the CAR only for
  `{ψ_{J,+j}, ψ_{J',-k}}`; the relations `{ψ_+, ψ_+} = 0` and `{ψ_-, ψ_-} = 0` and the `†`
  forms (v1's `ψ_{J,-j}` is `ψ_{J,j}^†`, never proved there) are also proved, across sectors
  as well as within one, and `Π_l ψ_{l',k} = δ_{l,l'} ψ_{l',k}` is the sharper form of the
  commutation.
* The index `l` runs over the joint-eigenvalue tuples of the family `{J_κ}` of *all* classes of
  the quotient `EvenHoleDeformationClass`; the junk coordinates are `0` (see
  `CycleSymmetrySectors`), which does not affect any statement here.
* The inner index runs over `Fin (r l)` with `r l = deg z_{∅,l}` instead of `α(G)` (they
  coincide in generic sectors; v1 does not say that `deg Z_{G,J} = α(G)` in every sector, which
  fails in the `C₄` example).
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace SimplicialModeHamiltonian

namespace ModeSector

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]

variable {H : G.SimplicialModeHamiltonian Ks A}

/-! ### Orthogonal sectors -/

/-- Two mode sectors `S`, `S'` of `H` are *orthogonal* if `Π_S Π_{S'} = 0` (the sector
projections `Π_J`, `Π_{J'}` of distinct joint eigenspaces of v1 Theorem 2). -/
def Orthogonal (S S' : H.ModeSector) : Prop :=
  S.Pi * S'.Pi = 0

namespace Orthogonal

variable {S S' : H.ModeSector}

/-- Orthogonality is symmetric, because the projections are Hermitian. -/
theorem symm (h : S.Orthogonal S') : S'.Orthogonal S := by
  have h' := congrArg star h
  rwa [star_mul, S.Pi_selfAdjoint.star_eq, S'.Pi_selfAdjoint.star_eq, star_zero] at h'

/-- `Π_{S'} Π_S = 0` (the other order). -/
theorem Pi_mul_Pi (h : S.Orthogonal S') : S'.Pi * S.Pi = 0 :=
  h.symm

/-- An element living in the sector `S'` (`Π' x = x`) is killed by `Π_S` on the left. -/
theorem Pi_mul_eq_zero (h : S.Orthogonal S') {x : A} (hx : S'.Pi * x = x) : S.Pi * x = 0 := by
  rw [← hx, ← mul_assoc, h, zero_mul]

/-- An element living in the sector `S'` (`x Π' = x`) is killed by `Π_S` on the right. -/
theorem mul_Pi_eq_zero (h : S.Orthogonal S') {x : A} (hx : x * S'.Pi = x) : x * S.Pi = 0 := by
  rw [← hx, mul_assoc, h.symm, mul_zero]

/-- The product of an element of the sector `S` (`x Π = x`) and an element of the orthogonal
sector `S'` (`Π' y = y`) is `0`. -/
theorem mul_eq_zero (h : S.Orthogonal S') {x y : A} (hx : x * S.Pi = x) (hy : S'.Pi * y = y) :
    x * y = 0 := by
  rw [← hx, ← hy]
  calc x * S.Pi * (S'.Pi * y) = x * (S.Pi * S'.Pi) * y := by simp only [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

/-- Elements of orthogonal sectors anticommute (in fact both products vanish):
`{x, y} = 0` when `Π x = x = x Π` and `Π' y = y = y Π'`. -/
theorem anticomm_eq_zero (h : S.Orthogonal S') {x y : A} (hx : S.Pi * x = x ∧ x * S.Pi = x)
    (hy : S'.Pi * y = y ∧ y * S'.Pi = y) : x * y + y * x = 0 := by
  rw [h.mul_eq_zero hx.2 hy.1, h.symm.mul_eq_zero hy.2 hx.1, add_zero]

/-- `Π_S` commutes with every element of the orthogonal sector `S'`. -/
theorem commute_of_mem (h : S.Orthogonal S') {x : A} (hy : S'.Pi * x = x ∧ x * S'.Pi = x) :
    Commute S.Pi x := by
  unfold Commute SemiconjBy
  rw [h.Pi_mul_eq_zero hy.1, h.mul_Pi_eq_zero hy.2]

/-! #### The unnormalised modes `A_v = Π T(-v) χ T(v)` -/

/-- `Π_S A'_w = 0 = A'_w Π_S` for the unnormalised mode `A'_w` of an orthogonal sector
(v1: `Π_J ψ_{J',j} = 0` for `J ≠ J'`). -/
theorem Pi_mul_mode (h : S.Orthogonal S') (w : ℝ) :
    S.Pi * S'.mode w = 0 ∧ S'.mode w * S.Pi = 0 :=
  ⟨h.Pi_mul_eq_zero (S'.Pi_mul_mode w).1, h.mul_Pi_eq_zero (S'.Pi_mul_mode w).2⟩

/-- `[Π_S, A'_w] = 0` for the mode of an orthogonal sector (both products vanish). -/
theorem commute_mode (h : S.Orthogonal S') (w : ℝ) : Commute S.Pi (S'.mode w) :=
  h.commute_of_mem (S'.Pi_mul_mode w)

/-- `A_v A'_w = 0` for modes of orthogonal sectors. -/
theorem mode_mul_mode (h : S.Orthogonal S') (v w : ℝ) : S.mode v * S'.mode w = 0 :=
  h.mul_eq_zero (S.Pi_mul_mode v).2 (S'.Pi_mul_mode w).1

/-- `{A_v, A'_w} = 0` for modes of orthogonal sectors, at arbitrary real `v`, `w`. -/
theorem mode_anticomm_mode (h : S.Orthogonal S') (v w : ℝ) :
    S.mode v * S'.mode w + S'.mode w * S.mode v = 0 :=
  h.anticomm_eq_zero (S.Pi_mul_mode v) (S'.Pi_mul_mode w)

/-! #### The normalised modes `ψ_j^±` -/

/-- `Π_S ψ'^+_k = 0 = ψ'^+_k Π_S` for the normalised raising mode of an orthogonal sector. -/
theorem Pi_mul_psiPlus (h : S.Orthogonal S') (D' : S'.Nondegenerate) (k : Fin D'.r) :
    S.Pi * D'.psiPlus k = 0 ∧ D'.psiPlus k * S.Pi = 0 :=
  ⟨h.Pi_mul_eq_zero (D'.Pi_mul_psiPlus k).1, h.mul_Pi_eq_zero (D'.Pi_mul_psiPlus k).2⟩

/-- `Π_S ψ'^-_k = 0 = ψ'^-_k Π_S` for the normalised lowering mode of an orthogonal sector. -/
theorem Pi_mul_psiMinus (h : S.Orthogonal S') (D' : S'.Nondegenerate) (k : Fin D'.r) :
    S.Pi * D'.psiMinus k = 0 ∧ D'.psiMinus k * S.Pi = 0 :=
  ⟨h.Pi_mul_eq_zero (D'.Pi_mul_psiMinus k).1, h.mul_Pi_eq_zero (D'.Pi_mul_psiMinus k).2⟩

/-- `[Π_S, ψ'^+_k] = 0` for the mode of an orthogonal sector (v1: `[Π_J, ψ_{J',j}] = 0`). -/
theorem commute_psiPlus (h : S.Orthogonal S') (D' : S'.Nondegenerate) (k : Fin D'.r) :
    Commute S.Pi (D'.psiPlus k) :=
  h.commute_of_mem (D'.Pi_mul_psiPlus k)

/-- `[Π_S, ψ'^-_k] = 0` for the mode of an orthogonal sector. -/
theorem commute_psiMinus (h : S.Orthogonal S') (D' : S'.Nondegenerate) (k : Fin D'.r) :
    Commute S.Pi (D'.psiMinus k) :=
  h.commute_of_mem (D'.Pi_mul_psiMinus k)

/-- `{ψ_j^+, ψ'^-_k} = 0` for modes of orthogonal sectors (v1 Lemma 14 with `J ≠ J'`). -/
theorem psiPlus_anticomm_psiMinus (h : S.Orthogonal S') (D : S.Nondegenerate)
    (D' : S'.Nondegenerate) (j : Fin D.r) (k : Fin D'.r) :
    D.psiPlus j * D'.psiMinus k + D'.psiMinus k * D.psiPlus j = 0 :=
  h.anticomm_eq_zero (D.Pi_mul_psiPlus j) (D'.Pi_mul_psiMinus k)

/-- `{ψ_j^+, ψ'^+_k} = 0` for modes of orthogonal sectors. -/
theorem psiPlus_anticomm_psiPlus (h : S.Orthogonal S') (D : S.Nondegenerate)
    (D' : S'.Nondegenerate) (j : Fin D.r) (k : Fin D'.r) :
    D.psiPlus j * D'.psiPlus k + D'.psiPlus k * D.psiPlus j = 0 :=
  h.anticomm_eq_zero (D.Pi_mul_psiPlus j) (D'.Pi_mul_psiPlus k)

/-- `{ψ_j^-, ψ'^-_k} = 0` for modes of orthogonal sectors. -/
theorem psiMinus_anticomm_psiMinus (h : S.Orthogonal S') (D : S.Nondegenerate)
    (D' : S'.Nondegenerate) (j : Fin D.r) (k : Fin D'.r) :
    D.psiMinus j * D'.psiMinus k + D'.psiMinus k * D.psiMinus j = 0 :=
  h.anticomm_eq_zero (D.Pi_mul_psiMinus j) (D'.Pi_mul_psiMinus k)

/-- `{ψ_j^-, ψ'^+_k} = 0` for modes of orthogonal sectors. -/
theorem psiMinus_anticomm_psiPlus (h : S.Orthogonal S') (D : S.Nondegenerate)
    (D' : S'.Nondegenerate) (j : Fin D.r) (k : Fin D'.r) :
    D.psiMinus j * D'.psiPlus k + D'.psiPlus k * D.psiMinus j = 0 :=
  h.anticomm_eq_zero (D.Pi_mul_psiMinus j) (D'.Pi_mul_psiPlus k)

/-- `{ψ_j^+, (ψ'^+_k)†} = 0` for modes of orthogonal sectors (the `†` form of
`psiPlus_anticomm_psiMinus`, `(ψ'^+_k)† = ψ'^-_k`). -/
theorem psiPlus_anticomm_star_psiPlus (h : S.Orthogonal S') (D : S.Nondegenerate)
    (D' : S'.Nondegenerate) (j : Fin D.r) (k : Fin D'.r) :
    D.psiPlus j * star (D'.psiPlus k) + star (D'.psiPlus k) * D.psiPlus j = 0 := by
  rw [D'.star_psiPlus]
  exact h.psiPlus_anticomm_psiMinus D D' j k

end Orthogonal

/-! ### Families of pairwise orthogonal sectors -/

namespace Family

variable {ι : Type*} {S : ι → H.ModeSector}

/-- **`Π_l ψ_{l',k} = δ_{l,l'} ψ_{l',k}`** (v1 Theorem 2, L1262-1263, `[Π_J, ψ_{J',j}] = 0`, in
the sharper form "both sides are `0` or `ψ`"): for a family of pairwise orthogonal sectors with
non-degeneracy data `D l`, the projection of the sector `l` multiplies the modes of the sector
`l'` to `0` if `l ≠ l'` and acts as the identity if `l = l'`. -/
theorem Pi_mul_psi (D : ∀ l, (S l).Nondegenerate)
    (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m)) (l l' : ι) (k : Fin (D l').r)
    [Decidable (l = l')] :
    (S l).Pi * (D l').psiPlus k = if l = l' then (D l').psiPlus k else 0 := by
  by_cases h : l = l'
  · subst h
    rw [if_pos rfl]
    exact ((D l).Pi_mul_psiPlus k).1
  · rw [if_neg h]
    exact ((hS l l' h).Pi_mul_psiPlus (D l') k).1

/-- **`ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`**, the other order of `Pi_mul_psi`. -/
theorem psi_mul_Pi (D : ∀ l, (S l).Nondegenerate)
    (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m)) (l l' : ι) (k : Fin (D l').r)
    [Decidable (l = l')] :
    (D l').psiPlus k * (S l).Pi = if l = l' then (D l').psiPlus k else 0 := by
  by_cases h : l = l'
  · subst h
    rw [if_pos rfl]
    exact ((D l).Pi_mul_psiPlus k).2
  · rw [if_neg h]
    exact ((hS l l' h).Pi_mul_psiPlus (D l') k).2

/-- **`[Π_l, ψ_{l',k}] = 0` for all `l`, `l'`** (v1 Theorem 2, L1262-1263). -/
theorem commute_Pi_psi (D : ∀ l, (S l).Nondegenerate)
    (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m)) (l l' : ι) (k : Fin (D l').r) :
    Commute (S l).Pi ((D l').psiPlus k) := by
  by_cases h : l = l'
  · subst h
    exact ((D l).Pi_mul_psiPlus k).1.trans ((D l).Pi_mul_psiPlus k).2.symm
  · exact (hS l l' h).commute_psiPlus (D l') k

/-- **`[Π_l, ψ_{l',k}^†] = 0` for all `l`, `l'`.** -/
theorem commute_Pi_star_psi (D : ∀ l, (S l).Nondegenerate)
    (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m)) (l l' : ι) (k : Fin (D l').r) :
    Commute (S l).Pi (star ((D l').psiPlus k)) := by
  rw [(D l').star_psiPlus]
  by_cases h : l = l'
  · subst h
    exact ((D l).Pi_mul_psiMinus k).1.trans ((D l).Pi_mul_psiMinus k).2.symm
  · exact (hS l l' h).commute_psiMinus (D l') k

/-- **`{ψ_{l,j}, ψ_{l',k}^†} = 0` for `l ≠ l'`** (v1 Lemma 14 with `J ≠ J'`,
`{ψ_{J,+j}, ψ_{J',-k}} = 0`, since `ψ_{J',-k} = ψ_{J',k}^†`). -/
theorem psi_anticomm_star_psi_of_ne (D : ∀ l, (S l).Nondegenerate)
    (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m)) {l l' : ι} (hll : l ≠ l')
    (j : Fin (D l).r) (k : Fin (D l').r) :
    (D l).psiPlus j * star ((D l').psiPlus k) + star ((D l').psiPlus k) * (D l).psiPlus j = 0 :=
  (hS l l' hll).psiPlus_anticomm_star_psiPlus (D l) (D l') j k

/-- **`{ψ_{l,j}, ψ_{l,k}^†} = δ_{jk} Π_l`** within one sector: v1 Lemma 14 in the form with
`ψ_{J,-k} = ψ_{J,k}^†` (`Nondegenerate.ladder_plus_minus` and `Nondegenerate.star_psiPlus`). -/
theorem psi_anticomm_star_psi_self (D : ∀ l, (S l).Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (l : ι) (j k : Fin (D l).r) :
    (D l).psiPlus j * star ((D l).psiPlus k) + star ((D l).psiPlus k) * (D l).psiPlus j =
      if j = k then (S l).Pi else 0 := by
  rw [(D l).star_psiPlus]
  exact (D l).ladder_plus_minus hclaw hKs j k

/-- **The canonical anticommutation relations of the incognito modes, across and within
sectors** (v1 Lemma 14, L1306-1313, `{ψ_{J,+j}, ψ_{J',-k}} = δ_{J,J'} δ_{jk} Π_J`, with
`ψ_{J',-k} = ψ_{J',k}^†`):

`{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l`.

The Kronecker symbol is `if l = l' ∧ HEq j k`, because `j : Fin (D l).r` and `k : Fin (D l').r` are
indices of different types when `l ≠ l'`.  The premises beyond the manuscript setup are the
non-degeneracy data `D l` of every sector (which v1 uses silently) and the orthogonality of the
sectors (`Π_l Π_{l'} = 0`, automatic for distinct joint eigenspaces). -/
theorem psi_anticomm_star_psi (D : ∀ l, (S l).Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m))
    (l l' : ι) (j : Fin (D l).r) (k : Fin (D l').r) [Decidable (l = l' ∧ HEq j k)] :
    (D l).psiPlus j * star ((D l').psiPlus k) + star ((D l').psiPlus k) * (D l).psiPlus j =
      if l = l' ∧ HEq j k then (S l).Pi else 0 := by
  by_cases hll : l = l'
  · subst hll
    rw [psi_anticomm_star_psi_self D hclaw hKs l j k]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, if_pos ⟨rfl, HEq.rfl⟩]
    · rw [if_neg hjk, if_neg (fun h => hjk (eq_of_heq h.2))]
  · rw [if_neg (fun h => hll h.1)]
    exact psi_anticomm_star_psi_of_ne D hS hll j k

/-- **`{ψ_{l,j}, ψ_{l',k}} = 0`** for all `l`, `l'`, `j`, `k` (not stated in v1; across sectors by
orthogonality, within a sector by `Nondegenerate.ladder_plus_plus`). -/
theorem psi_anticomm_psi (D : ∀ l, (S l).Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m))
    (l l' : ι) (j : Fin (D l).r) (k : Fin (D l').r) :
    (D l).psiPlus j * (D l').psiPlus k + (D l').psiPlus k * (D l).psiPlus j = 0 := by
  by_cases hll : l = l'
  · subst hll
    exact (D l).ladder_plus_plus hclaw hKs j k
  · exact (hS l l' hll).psiPlus_anticomm_psiPlus (D l) (D l') j k

/-- **`{ψ_{l,j}^†, ψ_{l',k}^†} = 0`**, the adjoint of `psi_anticomm_psi`. -/
theorem star_psi_anticomm_star_psi (D : ∀ l, (S l).Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hS : ∀ l m, l ≠ m → (S l).Orthogonal (S m))
    (l l' : ι) (j : Fin (D l).r) (k : Fin (D l').r) :
    star ((D l).psiPlus j) * star ((D l').psiPlus k) +
        star ((D l').psiPlus k) * star ((D l).psiPlus j) = 0 := by
  have h := congrArg star (psi_anticomm_psi D hclaw hKs hS l l' j k)
  rw [star_add, star_mul, star_mul, star_zero] at h
  rw [← h, add_comm]

end Family

end ModeSector

/-! ### The explicit modes and the assembled statement for the sectors of the cycle symmetries -/

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]

/-- **The explicit normalised incognito mode** of the sector with projection `Π`, sector
polynomials `z_G = Z_{G,J}`, `z_K = Z_{G∖Ks,J}` and spectral parameter `u` (v1 Definition 9 and
Theorem 2, L596-603, L1254-1256, with the normalisation of L2097):

`ψ = N⁻¹ Π T(-u) χ T(u)`,  `N = 4 u √(z_K(-u²) z_G'(-u²))`.

For a mode sector `S` with non-degeneracy data `D` it is `D.psiPlus j` at `u = D.u j`
(`ModeSector.Nondegenerate.psiPlus_eq_explicitIncognitoMode`). -/
noncomputable def explicitIncognitoMode (H : G.SimplicialModeHamiltonian Ks A) (Pi : A)
    (zG zK : Polynomial ℝ) (u : ℝ) : A :=
  (4 * u * Real.sqrt (zK.eval (-u ^ 2) * (Polynomial.derivative zG).eval (-u ^ 2)))⁻¹ •
    (Pi * H.frustration.transfer ∅ (-u) * H.root * H.frustration.transfer ∅ u)

namespace ModeSector.Nondegenerate

variable {H : G.SimplicialModeHamiltonian Ks A} {S : H.ModeSector}

/-- The normalised mode `ψ_j^+ = D.psiPlus j` is the explicit mode
`explicitIncognitoMode H Π z_G z_K u_j` (definitional). -/
theorem psiPlus_eq_explicitIncognitoMode (D : S.Nondegenerate) (j : Fin D.r) :
    D.psiPlus j = H.explicitIncognitoMode S.Pi S.zG S.zK (D.u j) :=
  rfl

end ModeSector.Nondegenerate

open scoped Classical in
/-- **Cross-sector relations of the incognito modes for the sectors of the cycle symmetries,
conditional on `[J, J'] = 0` and on per-sector coprimality** (v1 Theorem 2, L1248-1264, the
statements `[Π_J, ψ_{J',j}] = 0` for all `J`, `J'`, `j` and the canonical anticommutation
relations of Lemma 14 including `J ≠ J'`).

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks`, whose cycle symmetries commute (`hJ`, v1 Theorem 1(iii),
not yet formalised) and such that for every joint-eigenvalue tuple `l` of the `J_{⟨C₀⟩}` that
occurs the sector polynomials `z_{∅,l}`, `z_{Ks,l}` are coprime (`hND`; for real polynomials this
is v1's tacit "no common complex root", see the module docstring).  Then there are

* a finite set `Λ` of tuples and Hermitian idempotents `Π_l ≠ 0` (`l ∈ Λ`), pairwise orthogonal
  with `∑ Π_l = 1`, `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l` and the other properties of
  `exists_modeSectors_of_cycleSymmetry_commute` (`CycleSymmetrySectors`), every `Π_l` being the
  projection of a `ModeSector` with `z_G = z_{∅,l}`, `z_K = z_{Ks,l}`;
* in every sector `l ∈ Λ` exactly `r_l = deg z_{∅,l}` distinct positive numbers `u_{l,j}` with
  `z_{∅,l} = ∏_j (1 + x/u_{l,j}²)`, `z_{Ks,l}(-u_{l,j}²) z_{∅,l}'(-u_{l,j}²) > 0` (so that the
  normalisation is a positive real) and `Z_G(-u_{l,j}²) Π_l = 0`;
* the explicit modes `ψ_{l,j} = N_{l,j}⁻¹ Π_l T(-u_{l,j}) χ T(u_{l,j})`,
  `N_{l,j} = 4 u_{l,j} √(z_{Ks,l}(-u_{l,j}²) z_{∅,l}'(-u_{l,j}²))`
  (`explicitIncognitoMode`; v1 Definition 9 and L2097),

such that for all `l, l' ∈ Λ` and all `j`, `k`:

* `[Π_l, ψ_{l',k}] = 0`, more precisely `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`, and
  `[Π_l, ψ_{l',k}^†] = 0`;
* `{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l`  (v1 Lemma 14, `ψ_{l,-k} = ψ_{l,k}^†`);
* `{ψ_{l,j}, ψ_{l',k}} = 0` and `{ψ_{l,j}^†, ψ_{l',k}^†} = 0`.

The relations with `l ≠ l'` use only `Π_l Π_{l'} = 0` (`ModeSector.Orthogonal`); the relations
with `l = l'` are `Nondegenerate.ladder_plus_minus`, `ladder_plus_plus` of
`LadderAnticommutation`.  The Kronecker symbol is `if l = l' ∧ HEq j k`, since `j : Fin (r l)`
and `k : Fin (r l')` have different types for `l ≠ l'`.

Premises beyond the manuscript setup: `hJ` (v1 Theorem 1(iii), hence the name) and `hND` (v1's
tacit non-degeneracy; Theorem 2 is false without it, the `C₄` counterexample with `J = ±1`). -/
theorem exists_crossSectorModes_of_cycleSymmetry_commute {d : ℕ}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hJ : H.frustration.CycleSymmetriesCommute)
    (hND : ∀ l : G.EvenHoleDeformationClass → ℝ,
      ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀, G.IsEvenHoleCarrier C₀ →
          (H.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
            ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
        ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) →
      IsCoprime (G.sectorPolynomial H.coupling ∅ l) (G.sectorPolynomial H.coupling Ks l)) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ)
      (r : (G.EvenHoleDeformationClass → ℝ) → ℕ) (u : ∀ l, Fin (r l) → ℝ)
      (ψ : ∀ l, Fin (r l) → Matrix (Fin d) (Fin d) ℂ),
      -- the joint spectral projectors of the cycle symmetries
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ∀ m ∈ Λ, l ≠ m → Pi l * Pi m = 0) ∧ ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ∀ C₀, G.IsEvenHoleCarrier C₀ →
        H.frustration.generalizedCycleSymmetryOp C₀ * Pi l =
          ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) ∧
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        (∀ C₀, G.IsEvenHoleCarrier C₀ →
          Commute x (H.frustration.generalizedCycleSymmetryOp C₀)) →
          ∀ l ∈ Λ, Commute x (Pi l)) ∧
      (∀ l : G.EvenHoleDeformationClass → ℝ,
        l ∈ Λ ↔
          ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀, G.IsEvenHoleCarrier C₀ →
              (H.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
                ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
            ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0)) ∧
      (∀ l ∈ Λ, ∃ S : H.ModeSector, S.Pi = Pi l ∧
        S.zG = G.sectorPolynomial H.coupling ∅ l ∧ S.zK = G.sectorPolynomial H.coupling Ks l) ∧
      -- the roots `u_{l,j}` (non-degeneracy data)
      (∀ l ∈ Λ, r l = (G.sectorPolynomial H.coupling ∅ l).natDegree ∧ Function.Injective (u l) ∧
        (∀ j, 0 < u l j) ∧
        G.sectorPolynomial H.coupling ∅ l =
          ∏ j, (1 + Polynomial.C ((u l j)⁻¹ ^ 2) * Polynomial.X) ∧
        (∀ j, 0 < (G.sectorPolynomial H.coupling Ks l).eval (-(u l j) ^ 2) *
          (Polynomial.derivative (G.sectorPolynomial H.coupling ∅ l)).eval (-(u l j) ^ 2)) ∧
        ∀ j, H.frustration.transfer ∅ (u l j) * H.frustration.transfer ∅ (-(u l j)) * Pi l = 0) ∧
      -- the explicit modes
      (∀ l j, ψ l j = H.explicitIncognitoMode (Pi l) (G.sectorPolynomial H.coupling ∅ l)
        (G.sectorPolynomial H.coupling Ks l) (u l j)) ∧
      -- cross-sector commutation: `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ k, Commute (Pi l) (ψ l' k) ∧ Commute (Pi l) (star (ψ l' k))) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ k, Pi l * ψ l' k = (if l = l' then ψ l' k else 0) ∧
        ψ l' k * Pi l = (if l = l' then ψ l' k else 0)) ∧
      -- the canonical anticommutation relations, across and within sectors
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * star (ψ l' k) + star (ψ l' k) * ψ l j = if l = l' ∧ HEq j k then Pi l else 0) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * ψ l' k + ψ l' k * ψ l j = 0) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        star (ψ l j) * star (ψ l' k) + star (ψ l' k) * star (ψ l j) = 0) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7⟩ :=
    H.frustration.exists_jointSpectralProjections_of_cycleSymmetry_commute
      (fun j => H.term_selfAdjoint (some j)) hJ
  -- the sectors of `CycleSymmetrySectors`
  let S : Λ → H.ModeSector := fun l =>
    H.jointModeSector hclaw hKs l.1 (Pi l.1) (h1 l.1 l.2).1 (h1 l.1 l.2).2.1 (h4 l.1 l.2)
      (fun x hx => h6 x hx l.1 l.2)
  -- non-degeneracy data of every occurring sector, from coprimality
  have hD : ∀ l : Λ, ∃ D : (S l).Nondegenerate, D.r = (S l).zG.natDegree := fun l =>
    (S l).exists_nondegenerate_of_isCoprime hclaw hKs (h1 l.1 l.2).2.2
      (hND l.1 ((h7 l.1).1 l.2))
  -- the raw (non-dependent) data `r`, `u`
  have hraw : ∀ l : G.EvenHoleDeformationClass → ℝ, ∃ (r : ℕ) (u : Fin r → ℝ), l ∈ Λ →
      (r = (G.sectorPolynomial H.coupling ∅ l).natDegree ∧ Function.Injective u ∧
        (∀ j, 0 < u j) ∧
        G.sectorPolynomial H.coupling ∅ l =
          ∏ j, (1 + Polynomial.C ((u j)⁻¹ ^ 2) * Polynomial.X) ∧
        (∀ j, 0 < (G.sectorPolynomial H.coupling Ks l).eval (-(u j) ^ 2) *
          (Polynomial.derivative (G.sectorPolynomial H.coupling ∅ l)).eval (-(u j) ^ 2))) := by
    intro l
    by_cases hl : l ∈ Λ
    · obtain ⟨D, hDr⟩ := hD ⟨l, hl⟩
      exact ⟨D.r, D.u, fun _ => ⟨hDr, D.u_injective, D.u_pos, D.zG_eq, D.radicand_pos⟩⟩
    · exact ⟨0, Fin.elim0, fun h => (hl h).elim⟩
  choose r u hru using hraw
  let D : ∀ l : Λ, (S l).Nondegenerate := fun l =>
    ⟨r l.1, u l.1, (hru l.1 l.2).2.2.1, (hru l.1 l.2).2.1, (hru l.1 l.2).2.2.2.1,
      (hru l.1 l.2).2.2.2.2⟩
  have hS : ∀ l m : Λ, l ≠ m → (S l).Orthogonal (S m) := fun l m hlm =>
    h2 l.1 l.2 m.1 m.2 (fun h => hlm (Subtype.ext h))
  refine ⟨Λ, Pi, r, u, fun l k => H.explicitIncognitoMode (Pi l)
    (G.sectorPolynomial H.coupling ∅ l) (G.sectorPolynomial H.coupling Ks l) (u l k),
    h1, h2, h3, h4, h5, h6, h7, ?_, ?_, fun l j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact ⟨S ⟨l, hl⟩, rfl, rfl, rfl⟩
  · intro l hl
    obtain ⟨hr, hinj, hpos, hzG, hrad⟩ := hru l hl
    refine ⟨hr, hinj, hpos, hzG, hrad, fun j => ?_⟩
    have hroot : (S ⟨l, hl⟩).zG.eval (-(u l j) ^ 2) = 0 := (D ⟨l, hl⟩).zG_eval_root j
    have hz := (S ⟨l, hl⟩).Z_scalar (u l j)
    rw [hroot, zero_smul] at hz
    have hc : Commute (S ⟨l, hl⟩).Pi
        (H.frustration.transfer ∅ (u l j) * H.frustration.transfer ∅ (-(u l j))) :=
      ((S ⟨l, hl⟩).Pi_comm_transfer (u l j)).mul_right ((S ⟨l, hl⟩).Pi_comm_transfer (-(u l j)))
    exact hc.eq.symm.trans hz
  · intro l hl l' hl' k
    exact ⟨ModeSector.Family.commute_Pi_psi D hS ⟨l, hl⟩ ⟨l', hl'⟩ k,
      ModeSector.Family.commute_Pi_star_psi D hS ⟨l, hl⟩ ⟨l', hl'⟩ k⟩
  · intro l hl l' hl' k
    have h := ModeSector.Family.Pi_mul_psi D hS ⟨l, hl⟩ ⟨l', hl'⟩ k
    have h' := ModeSector.Family.psi_mul_Pi D hS ⟨l, hl⟩ ⟨l', hl'⟩ k
    by_cases hll : l = l'
    · subst hll
      rw [if_pos rfl]
      rw [if_pos rfl] at h h'
      exact ⟨h, h'⟩
    · have hne : (⟨l, hl⟩ : Λ) ≠ ⟨l', hl'⟩ := fun h => hll (congrArg Subtype.val h)
      rw [if_neg hll]
      rw [if_neg hne] at h h'
      exact ⟨h, h'⟩
  · intro l hl l' hl' j k
    by_cases hll : l = l'
    · subst hll
      have h := ModeSector.Family.psi_anticomm_star_psi_self D hclaw hKs ⟨l, hl⟩ j k
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos ⟨rfl, HEq.rfl⟩]
        rw [if_pos rfl] at h
        exact h
      · rw [if_neg (fun h => hjk (eq_of_heq h.2))]
        rw [if_neg hjk] at h
        exact h
    · rw [if_neg (fun h => hll h.1)]
      have hne : (⟨l, hl⟩ : Λ) ≠ ⟨l', hl'⟩ := fun h => hll (congrArg Subtype.val h)
      exact ModeSector.Family.psi_anticomm_star_psi_of_ne D hS hne j k
  · intro l hl l' hl' j k
    exact ModeSector.Family.psi_anticomm_psi D hclaw hKs hS ⟨l, hl⟩ ⟨l', hl'⟩ j k
  · intro l hl l' hl' j k
    exact ModeSector.Family.star_psi_anticomm_star_psi D hclaw hKs hS ⟨l, hl⟩ ⟨l', hl'⟩ j k

end SimplicialModeHamiltonian

end SimpleGraph
