import FreeFermionGraphs.BubbleWandArcEvent
import FreeFermionGraphs.GeneralizedCycleSymmetry
import FreeFermionGraphs.InducedPathFintype

/-!
# Canonical normalization of generalized-cycle arcs

Equation (E1) requires the inverses of the normalizations for all targets in
one generalized-cycle class to sum to two.  The manuscript does not select a
pointwise normalization.  Here it is chosen uniformly over the finite set of
actual bubble events in that class, and the printed sum rule is derived.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- All targets reached from `P` by an even-hoop bubble event whose canonical
event carrier belongs to the deformation closure named by `C₀`. -/
noncomputable def bubbleWandTargetsInClosure
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P : CliqueRootedInducedPath G K) (C₀ : Set V) :
    Finset (CliqueRootedInducedPath G K) := by
  classical
  exact Finset.univ.filter fun Q =>
    ∃ j : V, Nonempty (EvenHoopBubbleWandEvent G K P Q j) ∧
      InEvenHoleDeformationClosure G C₀
        (bubbleWandArcHoopCarrier P Q j)

@[simp]
theorem mem_bubbleWandTargetsInClosure
    {G : SimpleGraph V} {K : Set V} [Fintype V]
    {P Q : CliqueRootedInducedPath G K} {C₀ : Set V} :
    Q ∈ bubbleWandTargetsInClosure G K P C₀ ↔
      ∃ j : V, Nonempty (EvenHoopBubbleWandEvent G K P Q j) ∧
        InEvenHoleDeformationClosure G C₀
          (bubbleWandArcHoopCarrier P Q j) := by
  classical
  simp [bubbleWandTargetsInClosure]

/-- A retained event in the named closure makes the canonical target set
nonempty. -/
theorem bubbleWandTargetsInClosure_nonempty_of_event
    {G : SimpleGraph V} {K : Set V} [Fintype V]
    {P Q : CliqueRootedInducedPath G K} {C₀ : Set V} {j : V}
    (E : EvenHoopBubbleWandEvent G K P Q j)
    (hclosure : InEvenHoleDeformationClosure G C₀
      (bubbleWandArcHoopCarrier P Q j)) :
    (bubbleWandTargetsInClosure G K P C₀).Nonempty := by
  refine ⟨Q, mem_bubbleWandTargetsInClosure.mpr ?_⟩
  exact ⟨j, ⟨E⟩, hclosure⟩

/-- Uniform Eq. (E1) normalization for one source and one generalized-cycle
class.  The target argument is retained to match the paper's notation. -/
noncomputable def canonicalBubbleWandNormalization
    {R : Type w} [Field R]
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P _Q : CliqueRootedInducedPath G K) (C₀ : Set V) : R :=
  (bubbleWandTargetsInClosure G K P C₀).card / 2

/-- The uniform construction satisfies exactly the normalization equation
printed below Eq. (E1). -/
theorem canonicalBubbleWandNormalization_sum_inverse
    {R : Type w} [Field R] [CharZero R]
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P : CliqueRootedInducedPath G K) (C₀ : Set V)
    (hne : (bubbleWandTargetsInClosure G K P C₀).Nonempty) :
    (1 / 2 : R) *
        ∑ Q ∈ bubbleWandTargetsInClosure G K P C₀,
          (canonicalBubbleWandNormalization G K P Q C₀)⁻¹ = 1 := by
  classical
  let targets := bubbleWandTargetsInClosure G K P C₀
  have hcardNat : targets.card ≠ 0 := Finset.card_ne_zero.mpr hne
  have hcard : (targets.card : R) ≠ 0 := by
    exact_mod_cast hcardNat
  have htwo : (2 : R) ≠ 0 := by
    exact_mod_cast (by decide : (2 : Nat) ≠ 0)
  change (1 / 2 : R) *
      ∑ _Q ∈ targets, ((targets.card : R) / 2)⁻¹ = 1
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [inv_div]
  simp only [div_eq_mul_inv, one_mul]
  calc
    (2 : R)⁻¹ * ((targets.card : R) *
        (2 * (targets.card : R)⁻¹)) =
        ((2 : R)⁻¹ * 2) *
          ((targets.card : R) * (targets.card : R)⁻¹) := by
      ac_rfl
    _ = 1 := by
      rw [inv_mul_cancel₀ htwo, mul_inv_cancel₀ hcard, one_mul]

end SimpleGraph
