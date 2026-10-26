import FreeFermionGraphs.ScaledPauliRepresentation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A concrete scaled Pauli representation of an arbitrary graph

Every graph `G` on a linearly ordered vertex type `V` with decidable adjacency has a concrete
representation of its frustration structure by "Pauli-type" operators (v1 L93, L232): on the
free module `R^{Finset V}` of functions on finite subsets of `V` (the computational basis of a
register with one qubit per vertex) let

`(T_v f)(S) = (-1)^{|S ∩ Γ_<(v)|} f(S Δ {v})`,

where `Γ_<(v)` is the set of neighbours of `v` that are smaller than `v`.  So `T_v` is the bit flip
`X_v` of qubit `v` followed by a phase string `Z` on the smaller neighbours of `v`.  Then
`T_v^2 = 1`, `T_v T_w = - T_w T_v` for adjacent `v ≠ w` (exactly one of `X_v Z_w`, `X_w Z_v` occurs)
and `T_v T_w = T_w T_v` for non-adjacent `v ≠ w`.  Scaling by invertible couplings `b_v` gives
`ScaledPauliFrustrationRepresentation G R (Module.End R (Finset V → R))` with
`h_v = b_v T_v`, `h_v^2 = b_v^2`.

The repository otherwise only constructs representations of single small graphs by hand
(explicit `4 × 4` matrices).  This module supplies a uniform construction, used to show that
the hypotheses of operator-level theorems (for instance `HoleOperatorTransport`) are satisfiable
on the non-vacuity example `Lemma12ResidualExample`.

The coefficient ring `R` is only assumed to satisfy `(2 : R) ≠ 0`, which is needed for the
*converse* direction of `adj_iff_anticommute` (a non-adjacent pair does not anticommute).

## Main declarations

* `SimpleGraph.PauliShiftModel.shift`: the operator `T_v`.
* `SimpleGraph.PauliShiftModel.shift_mul_shift_of_adj`, `shift_mul_shift_of_not_adj`,
  `shift_mul_self`: the Pauli relations.
* `SimpleGraph.PauliShiftModel.scaledRepresentation`: the scaled Pauli representation with
  an arbitrary family of invertible couplings.
-/

universe u v

namespace SimpleGraph

namespace PauliShiftModel

variable {V : Type u} [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Type v) [CommRing R]

/-- Toggle the membership of `v` in a finite set. -/
def toggle (v : V) (S : Finset V) : Finset V :=
  if v ∈ S then S.erase v else insert v S

/-- The sign `-1` if `u` is a smaller neighbour of `v` and `1` otherwise. -/
def sgnFactor (v u : V) : R :=
  if G.Adj v u ∧ u < v then -1 else 1

/-- The phase `(-1)^{|S ∩ Γ_<(v)|}` of the `Z`-string of `v` on the basis state `S`. -/
def sgn (v : V) (S : Finset V) : R :=
  ∏ u ∈ S, sgnFactor G R v u

variable {G R}

theorem mem_toggle (v x : V) (S : Finset V) :
    x ∈ toggle v S ↔ (if x = v then x ∉ S else x ∈ S) := by
  unfold toggle
  by_cases hv : v ∈ S
  · rw [if_pos hv, Finset.mem_erase]
    by_cases hx : x = v
    · subst hx
      simp [hv]
    · simp [hx]
  · rw [if_neg hv, Finset.mem_insert]
    by_cases hx : x = v
    · subst hx
      simp [hv]
    · simp [hx]

theorem toggle_toggle (v : V) (S : Finset V) : toggle v (toggle v S) = S := by
  ext x
  rw [mem_toggle, mem_toggle]
  by_cases hx : x = v <;> simp [hx]

theorem toggle_comm {v w : V} (hvw : v ≠ w) (S : Finset V) :
    toggle v (toggle w S) = toggle w (toggle v S) := by
  ext x
  rw [mem_toggle, mem_toggle, mem_toggle, mem_toggle]
  by_cases hxv : x = v
  · subst hxv
    simp [hvw]
  · by_cases hxw : x = w
    · subst hxw
      simp [hxv]
    · simp [hxv, hxw]

variable (G R) in
theorem sgnFactor_mul_self (v u : V) : sgnFactor G R v u * sgnFactor G R v u = 1 := by
  unfold sgnFactor
  split_ifs <;> simp

theorem sgn_mul_self (v : V) (S : Finset V) : sgn G R v S * sgn G R v S = 1 := by
  unfold sgn
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun u _ => sgnFactor_mul_self G R v u

theorem sgn_toggle (w v : V) (S : Finset V) :
    sgn G R w (toggle v S) = sgnFactor G R w v * sgn G R w S := by
  unfold toggle
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    have h := Finset.mul_prod_erase S (fun u => sgnFactor G R w u) hv
    unfold sgn
    rw [← h, ← mul_assoc, sgnFactor_mul_self, one_mul]
  · rw [if_neg hv]
    unfold sgn
    rw [Finset.prod_insert hv]

/-- The basis-state operator `T_v`: flip the qubit `v` and apply the phase string `Z` on the
smaller neighbours of `v`. -/
def shift (G : SimpleGraph V) [DecidableRel G.Adj] (R : Type v) [CommRing R] (v : V) :
    Module.End R (Finset V → R) where
  toFun f S := sgn G R v S * f (toggle v S)
  map_add' f g := by
    ext S
    simp [mul_add]
  map_smul' c f := by
    ext S
    simp [mul_left_comm]

theorem shift_apply (v : V) (f : Finset V → R) (S : Finset V) :
    shift G R v f S = sgn G R v S * f (toggle v S) :=
  rfl

theorem shift_mul_shift_apply (v w : V) (f : Finset V → R) (S : Finset V) :
    (shift G R v * shift G R w) f S =
      sgn G R v S * (sgnFactor G R w v * sgn G R w S) * f (toggle w (toggle v S)) := by
  rw [Module.End.mul_apply, shift_apply, shift_apply, sgn_toggle]
  ring

/-- `T_v^2 = 1`. -/
theorem shift_mul_self (v : V) : shift G R v * shift G R v = 1 := by
  ext f S
  rw [shift_mul_shift_apply, toggle_toggle]
  have h1 : sgnFactor G R v v = 1 := by
    simp [sgnFactor]
  rw [h1, one_mul, sgn_mul_self]
  simp

/-- Adjacent `T_v`, `T_w` anticommute. -/
theorem shift_mul_shift_of_adj {v w : V} (h : G.Adj v w) :
    shift G R v * shift G R w = -(shift G R w * shift G R v) := by
  ext f S
  rw [shift_mul_shift_apply]
  simp only [LinearMap.neg_apply, Pi.neg_apply]
  rw [shift_mul_shift_apply, toggle_comm h.ne.symm]
  rcases lt_or_gt_of_ne h.ne with hlt | hlt
  · have h1 : sgnFactor G R w v = -1 := by
      simp [sgnFactor, h.symm, hlt]
    have h2 : sgnFactor G R v w = 1 := by
      simp [sgnFactor, not_lt.mpr hlt.le]
    rw [h1, h2]
    ring
  · have h1 : sgnFactor G R w v = 1 := by
      simp [sgnFactor, not_lt.mpr hlt.le]
    have h2 : sgnFactor G R v w = -1 := by
      simp [sgnFactor, h, hlt]
    rw [h1, h2]
    ring

/-- Non-adjacent `T_v`, `T_w` commute. -/
theorem shift_mul_shift_of_not_adj {v w : V} (h : ¬ G.Adj v w) :
    shift G R v * shift G R w = shift G R w * shift G R v := by
  by_cases hvw : v = w
  · rw [hvw]
  · ext f S
    rw [shift_mul_shift_apply, shift_mul_shift_apply, toggle_comm (Ne.symm hvw)]
    have hwv : ¬ G.Adj w v := fun h' => h h'.symm
    have h1 : sgnFactor G R w v = 1 := by simp [sgnFactor, hwv]
    have h2 : sgnFactor G R v w = 1 := by simp [sgnFactor, h]
    rw [h1, h2]
    ring

/-- `T_v T_w` evaluated on the constant function `1` at the empty set, for non-adjacent
`v, w`: it is `1`.  This is used to separate commuting from anticommuting pairs. -/
theorem shift_mul_shift_one_empty {v w : V} (h : ¬ G.Adj v w) :
    (shift G R v * shift G R w) (fun _ => (1 : R)) ∅ = 1 := by
  rw [shift_mul_shift_apply]
  have hwv : ¬ G.Adj w v := fun h' => h h'.symm
  have h1 : sgnFactor G R w v = 1 := by simp [sgnFactor, hwv]
  simp [sgn, h1]

variable (G R) in
/-- **A concrete scaled Pauli representation of an arbitrary graph.**  The operators
`h_v = b_v T_v` on `R^{Finset V}` satisfy `h_v h_w = - h_w h_v` iff `v ~ w`, commute otherwise,
and `h_v^2 = b_v^2`, for any family of invertible couplings `b_v`, provided `2 ≠ 0` in `R`. -/
def scaledRepresentation (b : V → R) (hb : ∀ v, IsUnit (b v)) (h2 : (2 : R) ≠ 0) :
    G.ScaledPauliFrustrationRepresentation R (Module.End R (Finset V → R)) where
  operator :=
    { term := fun v => b v • shift G R v
      adj_iff_anticommute := by
        intro j k
        have hfact : (b j • shift G R j) * (b k • shift G R k) =
            (b j * b k) • (shift G R j * shift G R k) := smul_mul_smul_comm _ _ _ _
        have hfact' : (b k • shift G R k) * (b j • shift G R j) =
            (b j * b k) • (shift G R k * shift G R j) := by
          rw [smul_mul_smul_comm, mul_comm (b k) (b j)]
        rw [hfact, hfact']
        constructor
        · intro hjk
          rw [shift_mul_shift_of_adj hjk, smul_neg]
        · intro heq
          by_contra hjk
          have hcomm := shift_mul_shift_of_not_adj (R := R) hjk
          rw [hcomm] at heq
          have heq' := congrArg (fun T : Module.End R (Finset V → R) =>
            T (fun _ => (1 : R)) ∅) heq
          simp only [LinearMap.smul_apply, Pi.smul_apply, LinearMap.neg_apply, Pi.neg_apply,
            smul_eq_mul] at heq'
          have hcomm' := shift_mul_shift_one_empty (R := R) hjk
          rw [← hcomm, hcomm'] at heq'
          have hu : IsUnit (b j * b k) := (hb j).mul (hb k)
          have h2' : (b j * b k) * 2 = 0 := by linear_combination heq'
          exact h2 (hu.mul_right_eq_zero.mp h2')
      commute_of_not_adj := by
        intro j k hjk
        have hfact : (b j • shift G R j) * (b k • shift G R k) =
            (b j * b k) • (shift G R j * shift G R k) := smul_mul_smul_comm _ _ _ _
        have hfact' : (b k • shift G R k) * (b j • shift G R j) =
            (b j * b k) • (shift G R k * shift G R j) := by
          rw [smul_mul_smul_comm, mul_comm (b k) (b j)]
        rw [hfact, hfact', shift_mul_shift_of_not_adj hjk] }
  coupling := b
  coupling_isUnit := hb
  term_sq := by
    intro j
    show (b j • shift G R j) * (b j • shift G R j) = algebraMap R _ (b j ^ 2)
    rw [smul_mul_smul_comm, shift_mul_self, Algebra.algebraMap_eq_smul_one, pow_two]

end PauliShiftModel

end SimpleGraph
