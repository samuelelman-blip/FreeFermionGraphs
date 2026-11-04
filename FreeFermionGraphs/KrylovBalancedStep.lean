import FreeFermionGraphs.KrylovMatrixRealization
import FreeFermionGraphs.KrylovRowDecomposition
import FreeFermionGraphs.CliqueBubbleWandReverse
import FreeFermionGraphs.PauliWandPairing
import FreeFermionGraphs.PauliPathOperatorWeightedCancellation
import FreeFermionGraphs.InducedPathDeformationReverse

/-!
# The one-step identity for balanced coefficient rows, and the good-row induction

Manuscript reference: arXiv 2305.15625v1, proof of Theorem 3 (Section "Krylov
Subspaces"), the induction on `k` (L1494-1506), the cancellation of the
case (b.i) terms (L1514-1518) and the cancellation of the odd-hole terms in
case (b.iv) (L1575).  (The repo numbers some lemmas of v1 differently,
following a revised manuscript that is not available.)

In the Lean convention `[H, ·]` (without the factor `i` of `[iH, ·]`) the
exact one-row decomposition of `KrylovRowDecomposition.lean` reads, for every
rooted induced path `P` of `G* = G + j*`,

`[H, h_P] = -2 ( Σ_Q T_{PQ} h_Q + Σ_{j ∈ D(P)} h_P h_j + Σ_{j ∈ W(P)} h_P h_j )`,

where `T` is the tree matrix, `D(P)` is the set of Definition 10 clones of
vertices of `P` and `W(P)` the set of bubbles of wands on `P`.  The terms with
`j ∈ D(P)` and `j ∈ W(P)` are not in the span of the path operators of `P`'s
tree neighbours; they cancel only *between different rows*.  This file proves
the cancellation for a coefficient vector `c` that is *balanced*:

* `c(P~) = c(P)` for every single-vertex deformation `P~` of `P`
  (case (b.i), pairing `P ↔ P~`, `j ↔ P_i`, via
  `pathOperator_deformation_smul_add_eq_zero`), and
* `c(P*) = c(P)` for the reversal `P*` of every wand `w` on `P` whose hoop has
  an odd number of vertices (case (b.iv), pairing `P ↔ P*`, `j ↔ j_{s+1}`, via
  `pathOperator_mul_bubble_add_reverse_eq_zero`).

For such `c` and for a graph without even holes (so that every hoop is odd;
the hoop is an induced hole, `CliqueBubbleWand.exists_hoopHole`) one gets

`[H, Σ_P c_P h_P] = Σ_Q ( -2 Σ_P c_P T_{PQ} ) h_Q`.

The two sums over `(P, j)` with `j ∈ D(P)` (respectively `j ∈ W(P)`) are
killed by `Finset.sum_involution` on `Σ P, V`: the involution sends
`(P, j)` to `(P~, P_i)` (respectively `(P*, j_{s+1})`).  It is involutive by
`SingleVertexDeformation.deform_reverse_eq` (respectively
`CliqueBubbleWand.reverseWand_reverse`), it has no fixed point because the
vertex sets differ, and the two paired terms cancel.  The clone index `i` of a
clone `j` is unique (`SingleVertexDeformation.index_unique`: the path
neighbours of `j` are `P_{i-1}, P_i, P_{i+1}`), and the wand of a bubble is
unique (`CliqueBubbleWand.ext_of_bubble_eq`), which makes the involution
well defined.

Main declarations.

* `RootedInducedPath.IsBalancedRow`: the balance condition on `c`;
* `PauliCliqueHamiltonianRepresentation.sum_deformation_smul_eq_zero` and
  `PauliCliqueHamiltonianRepresentation.sum_wand_smul_eq_zero_of_odd`: the two
  cancellations;
* `PauliCliqueHamiltonianRepresentation.commutator_sum_of_isBalancedRow`: the
  one-step identity, for graphs without even holes;
* `iteratedCommutator_eq_matrixPow_sum_of_rows` (root namespace, companion of
  `KrylovMatrixRealization.lean`): the abstract good-row induction.  If the
  commutator maps the row `source · T^n` to the row `source · T^{n+1}` for every
  `n` then `[H, ·]^n (basis source) = Σ_y (T^n)_{source, y} basis y`.

Fidelity.  The identity needs only the manuscript setup (`K` simplicial, `G`
claw-free) plus the balance of `c`, which is an assumption on the *input*
vector and not a claim about the output; and `hfree` (no indexed induced hole
of even cardinality), whose only use is to make every wand hoop odd.  The
name `commutator_sum_of_isBalancedRow` is the premise-qualified name required
by `docs/PAPER_FIDELITY.md`.  The abstract lemma
`iteratedCommutator_eq_matrixPow_sum_of_rows` replaces
`iteratedCommutator_eq_matrixPow_sum` of `KrylovMatrixRealization.lean`, whose
row-wise premise `hstep` is false for the path basis: the term `h_P h_j` of a
clone `j` is not in the span of path operators and cancels only against the row
of the deformed path.  Here the premise is only on the rows of the powers of
`T` that are actually used.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

/-! ### The abstract good-row induction -/

/-- The abstract good-row induction (the induction on `k` of the proof of
Theorem 3, v1 L1494-1506).  Suppose that, for every `n`, the commutator with `H`
maps the row `source · T^n` (in the basis) to the row `source · T^{n+1}`.  Then
the `n`-fold commutator of the basis element at `source` is the row
`source · T^n`:
`[H, ·]^n (basis source) = Σ_y (T^n)_{source, y} basis y`.

Only the rows that are actually reached from `source` need the one-step
property; a one-step formula for every basis element (the premise of
`iteratedCommutator_eq_matrixPow_sum`) is not required. -/
theorem iteratedCommutator_eq_matrixPow_sum_of_rows
    {X R A : Type*} [Fintype X] [DecidableEq X]
    [CommRing R] [Ring A] [Algebra R A]
    (H : A) (basis : X → A) (T : Matrix X X R) (source : X)
    (hrow : ∀ n : ℕ,
      algebraCommutator H (∑ y, (T ^ n) source y • basis y) =
        ∑ y, (T ^ (n + 1)) source y • basis y)
    (n : ℕ) :
    iteratedCommutator H n (basis source) =
      ∑ y, (T ^ n) source y • basis y := by
  induction n with
  | zero => simp [Matrix.one_apply]
  | succ n ih => rw [iteratedCommutator_succ, ih, hrow n]

namespace SimpleGraph

/-! ### Uniqueness of the clone index -/

namespace IndexedInducedPath

variable {H : SimpleGraph V}

/-- A clone `s` of a path vertex determines the index: the path neighbours of `s`
are `P_{i-1}, P_i, P_{i+1}`, so two clone indices of the same vertex coincide.
(Definition 10 of v1, L682-691, for induced paths.) -/
theorem SingleVertexDeformation.index_unique
    {P : IndexedInducedPath H} {s : V} {i i' : Fin P.card}
    (h : P.SingleVertexDeformation s i) (h' : P.SingleVertexDeformation s i') :
    i = i' := by
  have key : ∀ (j : Fin P.card), P.SingleVertexDeformation s j →
      ∀ q : Fin P.card, H.Adj s (P.vertex q) ↔
        (q.val = j.val ∨ q.val + 1 = j.val ∨ j.val + 1 = q.val) := by
    intro j hj q
    rw [hj.adj_iff q, P.adj_iff j q]
    simp only [Fin.ext_iff]
    omega
  have hl := h'.internal_left
  have hr := h'.internal_right
  have hlt := i'.isLt
  have a1 := (key i h ⟨i'.val - 1, by omega⟩).1
    ((key i' h' ⟨i'.val - 1, by omega⟩).2 (Or.inr (Or.inl (by simp only; omega))))
  have a2 := (key i h ⟨i'.val + 1, hr⟩).1
    ((key i' h' ⟨i'.val + 1, hr⟩).2 (Or.inr (Or.inr rfl)))
  apply Fin.ext
  simp only at a1 a2
  omega

end IndexedInducedPath

/-! ### Balanced rows -/

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- A coefficient row `c` on the rooted induced paths of `G*` is *balanced* when

* `c(P~) = c(P)` for every single-vertex deformation `P~` of `P` (v1
  Definition 10; case (b.i) of the proof of Theorem 3), and
* `c(P*) = c(P)` for the reversal `P*` of every bubble wand on `P` whose hoop
  has an odd number of vertices (case (b.iv), v1 L1520, L1575).

This is exactly what is needed for the terms `h_P h_j` of clones and of odd-hoop
bubbles to cancel in `[H, Σ_P c_P h_P]`.  The rows `(T^n)_{{j*}, ·}` of the
tree matrix are balanced (`KrylovTreeRowBalance.lean`). -/
def IsBalancedRow {R : Type v} (c : CliqueRootedInducedPath G K → R) : Prop :=
  (∀ (P : CliqueRootedInducedPath G K) {s : Option V} {i : Fin P.path.card}
      (h : P.path.SingleVertexDeformation s i), c (P.deform h) = c P) ∧
  (∀ (P : CliqueRootedInducedPath G K) (w : CliqueBubbleWand G K P),
      Odd w.hoopCard → c w.reverse = c P)

/-- A constant multiple of a balanced row is balanced. -/
theorem IsBalancedRow.const_mul {R : Type v} [Mul R]
    {c : CliqueRootedInducedPath G K → R} (hc : IsBalancedRow c) (a : R) :
    IsBalancedRow (fun P => a * c P) :=
  ⟨fun P _ _ h => by simp only [hc.1 P h],
    fun P w hw => by simp only [hc.2 P w hw]⟩

/-- Two Definition 10 deformations of the same vertex of `P` at the same clone
give the same deformed path: the deformation index is determined by the clone. -/
theorem deform_eq_of_deformation
    (P : CliqueRootedInducedPath G K) {s : Option V} {i i' : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (h' : P.path.SingleVertexDeformation s i') :
    P.deform h = P.deform h' := by
  have hii : i = i' := h.index_unique h'
  subst hii
  rfl

/-- Deforming back along the reverse deformation recovers the path; the form
used when the clone is named by a given term `s'` equal to the replaced vertex. -/
theorem deform_deform_eq_of_vertex_eq
    (P : CliqueRootedInducedPath G K) {s : Option V} {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i) {s' : Option V}
    (hv : P.path.vertex i = s')
    (hrev : (P.deform h).path.SingleVertexDeformation s' i) :
    (P.deform h).deform hrev = P := by
  subst hv
  exact ext_path
    (IndexedInducedPath.SingleVertexDeformation.deform_reverse_eq P.path h)

/-! ### The involution on clone pairs -/

section Deformation

variable [Fintype V]

/-- The index `i` of a clone `j ∈ D(P)`. -/
noncomputable def deformationIndex (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles) : Fin P.path.card :=
  Classical.choose ((P.mem_deformationBubbles j).1 hj)

theorem deformationIndex_spec (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles) :
    P.path.SingleVertexDeformation (some j) (P.deformationIndex hj) :=
  Classical.choose_spec ((P.mem_deformationBubbles j).1 hj)

/-- The original vertex `P_i` that the clone `j ∈ D(P)` replaces. -/
noncomputable def deformationSwap (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles) : V :=
  Classical.choose (P.vertex_eq_some_of_pos (P.deformationIndex hj)
    (P.deformationIndex_spec hj).internal_left)

theorem path_vertex_deformationIndex (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles) :
    P.path.vertex (P.deformationIndex hj) = some (P.deformationSwap hj) :=
  Classical.choose_spec (P.vertex_eq_some_of_pos (P.deformationIndex hj)
    (P.deformationIndex_spec hj).internal_left)

/-- The replaced vertex `P_i` is a clone of `j` in the deformed path `P~`. -/
theorem deformationSwap_deformation (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles) :
    (P.deform (P.deformationIndex_spec hj)).path.SingleVertexDeformation
      (some (P.deformationSwap hj)) (P.deformationIndex hj) := by
  have hrev := (P.deformationIndex_spec hj).reverse P.path
  rw [P.path_vertex_deformationIndex hj] at hrev
  exact hrev

theorem deformationSwap_mem (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles) :
    P.deformationSwap hj ∈
      (P.deform (P.deformationIndex_spec hj)).deformationBubbles :=
  ((P.deform (P.deformationIndex_spec hj)).mem_deformationBubbles _).2
    ⟨_, P.deformationSwap_deformation hj⟩

/-- The swap is involutive: the clone of `P~` replacing `P_i` is `j`, and the
deformation of `P~` back is `P`. -/
theorem deformationSwap_involutive (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.deformationBubbles)
    (hj' : P.deformationSwap hj ∈
      (P.deform (P.deformationIndex_spec hj)).deformationBubbles) :
    (P.deform (P.deformationIndex_spec hj)).deform
        ((P.deform (P.deformationIndex_spec hj)).deformationIndex_spec hj') = P ∧
      (P.deform (P.deformationIndex_spec hj)).deformationSwap hj' = j := by
  set P' := P.deform (P.deformationIndex_spec hj) with hP'
  have h2 := P'.deformationIndex_spec hj'
  have hrev := P.deformationSwap_deformation hj
  have hi : P'.deformationIndex hj' = P.deformationIndex hj :=
    h2.index_unique hrev
  constructor
  · rw [P'.deform_eq_of_deformation h2 hrev]
    exact P.deform_deform_eq_of_vertex_eq (P.deformationIndex_spec hj)
      (P.path_vertex_deformationIndex hj) hrev
  · have h3 := P'.path_vertex_deformationIndex hj'
    rw [hi] at h3
    have h4 : P'.path.vertex (P.deformationIndex hj) = some j :=
      IndexedInducedPath.deform_vertex_at P.path (P.deformationIndex_spec hj)
    exact Option.some.inj (h3.symm.trans h4)

omit [Fintype V] in
/-- The deformed path differs from the original: the clone is outside `P`. -/
theorem deform_ne_self (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card} (h : P.path.SingleVertexDeformation s i) :
    P.deform h ≠ P := by
  intro heq
  apply h.outside
  have hrange := congrArg
    (fun Q : CliqueRootedInducedPath G K => Set.range Q.path.vertex) heq
  have hmem : s ∈ Set.range (P.deform h).path.vertex :=
    ⟨i, IndexedInducedPath.deform_vertex_at P.path h⟩
  rw [hrange] at hmem
  exact hmem

end Deformation

/-! ### The involution on wand pairs -/

section Wand

variable [Fintype V]

/-- The wand on `P` with bubble `j ∈ W(P)`; it is unique
(`CliqueBubbleWand.ext_of_bubble_eq`). -/
noncomputable def wandOfBubble (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.wandBubbles) : CliqueBubbleWand G K P :=
  Classical.choose ((P.mem_wandBubbles j).1 hj)

theorem wandOfBubble_bubble (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.wandBubbles) : (P.wandOfBubble hj).bubble = j :=
  Classical.choose_spec ((P.mem_wandBubbles j).1 hj)

theorem reverseBubble_mem_wandBubbles (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.wandBubbles) :
    (P.wandOfBubble hj).reverseBubble ∈ (P.wandOfBubble hj).reverse.wandBubbles :=
  ((P.wandOfBubble hj).reverse.mem_wandBubbles _).2
    ⟨(P.wandOfBubble hj).reverseWand, rfl⟩

/-- Reversal is involutive on the pairs `(P, j)`, `j ∈ W(P)`. -/
theorem wandOfBubble_involutive (P : CliqueRootedInducedPath G K) {j : V}
    (hj : j ∈ P.wandBubbles)
    (hj' : (P.wandOfBubble hj).reverseBubble ∈
      (P.wandOfBubble hj).reverse.wandBubbles) :
    ((P.wandOfBubble hj).reverse.wandOfBubble hj').reverse = P ∧
      ((P.wandOfBubble hj).reverse.wandOfBubble hj').reverseBubble = j := by
  set w := P.wandOfBubble hj with hw
  have hbub : ((w.reverse).wandOfBubble hj').bubble = w.reverseWand.bubble :=
    w.reverse.wandOfBubble_bubble hj'
  have heq : (w.reverse).wandOfBubble hj' = w.reverseWand :=
    CliqueBubbleWand.ext_of_bubble_eq _ _ hbub
  rw [heq]
  exact ⟨w.reverseWand_reverse,
    w.reverseWand_reverseBubble.trans (P.wandOfBubble_bubble hj)⟩

end Wand

end RootedInducedPath

/-! ### Wand hoops in graphs without even holes -/

namespace CliqueBubbleWand

variable {G : SimpleGraph V} {K : Set V}

/-- In a graph without even holes every wand hoop has an odd number of
vertices: the hoop is an induced hole (`CliqueBubbleWand.exists_hoopHole`). -/
theorem odd_hoopCard_of_evenHoleFree
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    {P : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P) :
    Odd w.hoopCard := by
  obtain ⟨C, _, hC⟩ := w.exists_hoopHole
  rw [← hC]
  exact Nat.not_even_iff_odd.1 (hfree C)

end CliqueBubbleWand

/-! ### The two cancellations and the one-step identity -/

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The clone terms of case (b.i) cancel in pairs for a balanced row (v1
L1514-1518): `Σ_P c_P Σ_{j ∈ D(P)} h_P h_j = 0` when `c(P~) = c(P)` for all
deformations. -/
theorem sum_deformation_smul_eq_zero [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (c : CliqueRootedInducedPath G K → R)
    (hc : RootedInducedPath.IsBalancedRow c) :
    ∑ P : CliqueRootedInducedPath G K, ∑ j ∈ P.deformationBubbles,
      c P • (H.pathOperator P * H.operator.term (some j)) = 0 := by
  rw [Finset.sum_sigma' Finset.univ
    (fun P : CliqueRootedInducedPath G K => P.deformationBubbles)
    (fun P j => c P • (H.pathOperator P * H.operator.term (some j)))]
  refine Finset.sum_involution
    (fun a ha => ⟨a.1.deform (a.1.deformationIndex_spec (Finset.mem_sigma.1 ha).2),
      a.1.deformationSwap (Finset.mem_sigma.1 ha).2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨P, j⟩ ha
    have hj : j ∈ P.deformationBubbles := (Finset.mem_sigma.1 ha).2
    have h := P.deformationIndex_spec hj
    have hv := P.path_vertex_deformationIndex hj
    have key := H.operator.pathOperator_deformation_smul_add_eq_zero P.path h
      (hc.1 P h).symm
    rw [hv] at key
    exact key
  · rintro ⟨P, j⟩ ha _ heq
    have hj : j ∈ P.deformationBubbles := (Finset.mem_sigma.1 ha).2
    have := congrArg Sigma.fst heq
    exact P.deform_ne_self (P.deformationIndex_spec hj) this
  · rintro ⟨P, j⟩ ha
    have hj : j ∈ P.deformationBubbles := (Finset.mem_sigma.1 ha).2
    exact Finset.mem_sigma.2 ⟨Finset.mem_univ _, P.deformationSwap_mem hj⟩
  · rintro ⟨P, j⟩ ha
    have hj : j ∈ P.deformationBubbles := (Finset.mem_sigma.1 ha).2
    obtain ⟨e1, e2⟩ := P.deformationSwap_involutive hj (P.deformationSwap_mem hj)
    exact Sigma.ext e1 (heq_of_eq e2)

/-- The terms of the odd-hoop wands of case (b.iv) cancel in pairs for a balanced
row (v1 L1575, "the contributions from odd holes cancel"):
`Σ_P c_P Σ_{j ∈ W(P)} h_P h_j = 0` when `c(P*) = c(P)` for the reversal of every
wand and every hoop is odd. -/
theorem sum_wand_smul_eq_zero_of_odd [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (c : CliqueRootedInducedPath G K → R)
    (hrev : ∀ (P : CliqueRootedInducedPath G K) (w : CliqueBubbleWand G K P),
      c w.reverse = c P)
    (hodd : ∀ (P : CliqueRootedInducedPath G K) (w : CliqueBubbleWand G K P),
      Odd w.hoopCard) :
    ∑ P : CliqueRootedInducedPath G K, ∑ j ∈ P.wandBubbles,
      c P • (H.pathOperator P * H.operator.term (some j)) = 0 := by
  rw [Finset.sum_sigma' Finset.univ
    (fun P : CliqueRootedInducedPath G K => P.wandBubbles)
    (fun P j => c P • (H.pathOperator P * H.operator.term (some j)))]
  refine Finset.sum_involution
    (fun a ha => ⟨(a.1.wandOfBubble (Finset.mem_sigma.1 ha).2).reverse,
      (a.1.wandOfBubble (Finset.mem_sigma.1 ha).2).reverseBubble⟩) ?_ ?_ ?_ ?_
  · rintro ⟨P, j⟩ ha
    have hj : j ∈ P.wandBubbles := (Finset.mem_sigma.1 ha).2
    set w := P.wandOfBubble hj with hw
    have hbub : w.bubble = j := P.wandOfBubble_bubble hj
    have key := H.pathOperator_mul_bubble_add_reverse_eq_zero w (hodd P w)
    rw [hbub] at key
    show c P • (H.pathOperator P * H.operator.term (some j)) +
      c w.reverse • (H.pathOperator w.reverse *
        H.operator.term (some w.reverseBubble)) = 0
    rw [hrev P w, ← smul_add, key, smul_zero]
  · rintro ⟨P, j⟩ ha _ heq
    have hj : j ∈ P.wandBubbles := (Finset.mem_sigma.1 ha).2
    have := congrArg Sigma.fst heq
    exact (P.wandOfBubble hj).reverse_ne this
  · rintro ⟨P, j⟩ ha
    have hj : j ∈ P.wandBubbles := (Finset.mem_sigma.1 ha).2
    exact Finset.mem_sigma.2 ⟨Finset.mem_univ _, P.reverseBubble_mem_wandBubbles hj⟩
  · rintro ⟨P, j⟩ ha
    have hj : j ∈ P.wandBubbles := (Finset.mem_sigma.1 ha).2
    obtain ⟨e1, e2⟩ := P.wandOfBubble_involutive hj (P.reverseBubble_mem_wandBubbles hj)
    exact Sigma.ext e1 (heq_of_eq e2)

/-- **One-step identity for balanced coefficient rows** (the induction step of
the proof of Theorem 3, v1 L1494-1520, L1575, in the convention `[H, ·]`
instead of `[iH, ·]`).

Let `G` be claw-free without even holes, `K` a simplicial clique and `c` a
balanced row.  Then
`[H, Σ_P c_P h_P] = Σ_Q ( -2 Σ_P c_P T_{PQ} ) h_Q`,
with `T = cliqueTreeMatrix G K b` the tree part of Eq. (decoratedtree).  The
exact one-row decomposition `commutator_pathOperator_decomposition` expresses
`[H, h_P]` as `-2` times the tree part plus the clone terms and the wand
terms; the latter two cancel by balance
(`sum_deformation_smul_eq_zero`, `sum_wand_smul_eq_zero_of_odd`).

Premises beyond the manuscript setup: the balance of `c`, a hypothesis on the
input row, and `hfree`, used only to make every wand hoop odd. -/
theorem commutator_sum_of_isBalancedRow [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (c : CliqueRootedInducedPath G K → R)
    (hc : RootedInducedPath.IsBalancedRow c) :
    algebraCommutator H.physicalHamiltonian (∑ P, c P • H.pathOperator P) =
      ∑ Q, ((-2 : R) * ∑ P, c P * cliqueTreeMatrix G K H.coupling P Q) •
        H.pathOperator Q := by
  -- linearity of the commutator
  have hlin : algebraCommutator H.physicalHamiltonian
      (∑ P, c P • H.pathOperator P) =
      ∑ P, c P • algebraCommutator H.physicalHamiltonian (H.pathOperator P) := by
    change commutatorLinearMap (R := R) H.physicalHamiltonian
      (∑ P, c P • H.pathOperator P) = _
    rw [map_sum]
    simp_rw [LinearMap.map_smul, commutatorLinearMap_apply]
  -- the scalar `-2`
  have hscalar : ∀ X : A, ((-1 : A) - 1) * X = (-2 : R) • X := by
    intro X
    rw [Algebra.smul_def, map_neg, map_ofNat]
    have h2 : ((-1 : A) - 1) = -2 := by rw [← neg_add', one_add_one_eq_two]
    rw [h2]
  -- the three cancellation facts
  have hdef := H.sum_deformation_smul_eq_zero c hc
  have hwand := H.sum_wand_smul_eq_zero_of_odd c
    (fun P w => hc.2 P w (CliqueBubbleWand.odd_hoopCard_of_evenHoleFree hfree w))
    (fun P w => CliqueBubbleWand.odd_hoopCard_of_evenHoleFree hfree w)
  -- the tree part
  have htree : ∑ P, c P • ∑ Q, cliqueTreeMatrix G K H.coupling P Q • H.pathOperator Q =
      ∑ Q, (∑ P, c P * cliqueTreeMatrix G K H.coupling P Q) • H.pathOperator Q := by
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hlin]
  simp_rw [H.commutator_pathOperator_decomposition hK hclaw, hscalar]
  have hsplit : ∀ P : CliqueRootedInducedPath G K,
      c P • (-2 : R) •
          ((∑ Q, cliqueTreeMatrix G K H.coupling P Q • H.pathOperator Q) +
            (∑ j ∈ P.deformationBubbles, H.pathOperator P * H.operator.term (some j)) +
            ∑ j ∈ P.wandBubbles, H.pathOperator P * H.operator.term (some j)) =
        (-2 : R) • ((c P • ∑ Q, cliqueTreeMatrix G K H.coupling P Q • H.pathOperator Q) +
          (c P • ∑ j ∈ P.deformationBubbles,
            H.pathOperator P * H.operator.term (some j)) +
          c P • ∑ j ∈ P.wandBubbles, H.pathOperator P * H.operator.term (some j)) := by
    intro P
    rw [smul_comm (c P) (-2 : R)]
    simp only [smul_add]
  simp_rw [hsplit]
  have hdef' : ∑ P : CliqueRootedInducedPath G K,
      c P • ∑ j ∈ P.deformationBubbles, H.pathOperator P * H.operator.term (some j) = 0 := by
    simpa only [Finset.smul_sum] using hdef
  have hwand' : ∑ P : CliqueRootedInducedPath G K,
      c P • ∑ j ∈ P.wandBubbles, H.pathOperator P * H.operator.term (some j) = 0 := by
    simpa only [Finset.smul_sum] using hwand
  rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, hdef', hwand',
    add_zero, add_zero, htree, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [mul_smul]

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
