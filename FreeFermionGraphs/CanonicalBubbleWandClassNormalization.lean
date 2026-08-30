import FreeFermionGraphs.CanonicalBubbleWandNormalization
import FreeFermionGraphs.EvenHoleDeformationQuotient

/-!
# Canonical generalized-cycle normalization on quotient classes

The coefficient in Eq. (E1) is indexed by the deformation class `⟨C₀⟩`,
not by a chosen carrier.  This module moves both the finite target set and its
uniform normalization to the actual quotient.  It also proves that evaluating
at any representative recovers the closure-based construction exactly.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- All targets reached from `P` by an even-hoop bubble event in the specified
even-hole deformation class. -/
noncomputable def bubbleWandTargetsInClass
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G) :
    Finset (CliqueRootedInducedPath G K) := by
  classical
  exact Finset.univ.filter fun Q =>
    ∃ j : V, Nonempty (EvenHoopBubbleWandEvent G K P Q j) ∧
      G.evenHoleDeformationClassOf (bubbleWandArcHoopCarrier P Q j) = c

@[simp]
theorem mem_bubbleWandTargetsInClass
    {G : SimpleGraph V} {K : Set V} [Fintype V]
    {P Q : CliqueRootedInducedPath G K}
    {c : EvenHoleDeformationClass G} :
    Q ∈ bubbleWandTargetsInClass G K P c ↔
      ∃ j : V, Nonempty (EvenHoopBubbleWandEvent G K P Q j) ∧
        G.evenHoleDeformationClassOf
          (bubbleWandArcHoopCarrier P Q j) = c := by
  classical
  simp [bubbleWandTargetsInClass]

/-- A retained event in the named quotient class makes its canonical target
set nonempty. -/
theorem bubbleWandTargetsInClass_nonempty_of_event
    {G : SimpleGraph V} {K : Set V} [Fintype V]
    {P Q : CliqueRootedInducedPath G K}
    {c : EvenHoleDeformationClass G} {j : V}
    (E : EvenHoopBubbleWandEvent G K P Q j)
    (hclass : G.evenHoleDeformationClassOf
      (bubbleWandArcHoopCarrier P Q j) = c) :
    (bubbleWandTargetsInClass G K P c).Nonempty := by
  refine ⟨Q, mem_bubbleWandTargetsInClass.mpr ?_⟩
  exact ⟨j, ⟨E⟩, hclass⟩

/-- Choosing a representative for a quotient class recovers exactly the
earlier closure-based target set. -/
theorem bubbleWandTargetsInClass_mk
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P : CliqueRootedInducedPath G K) (C₀ : Set V) :
    bubbleWandTargetsInClass G K P
        (G.evenHoleDeformationClassOf C₀) =
      bubbleWandTargetsInClosure G K P C₀ := by
  classical
  ext Q
  rw [mem_bubbleWandTargetsInClass,
    mem_bubbleWandTargetsInClosure]
  constructor
  · rintro ⟨j, hE, hclass⟩
    exact ⟨j, hE,
      (evenHoleDeformationClassOf_eq_iff.mp hclass).symm⟩
  · rintro ⟨j, hE, hclosure⟩
    exact ⟨j, hE,
      evenHoleDeformationClassOf_eq_iff.mpr hclosure.symm⟩

/-- Uniform Eq. (E1) normalization indexed by the genuine quotient class. -/
noncomputable def canonicalBubbleWandClassNormalization
    {R : Type w} [Field R]
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P _Q : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G) : R :=
  (bubbleWandTargetsInClass G K P c).card / 2

/-- The class-indexed coefficient agrees with the closure-indexed coefficient
for every representative. -/
theorem canonicalBubbleWandClassNormalization_mk
    {R : Type w} [Field R]
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P Q : CliqueRootedInducedPath G K) (C₀ : Set V) :
    canonicalBubbleWandClassNormalization G K P Q
        (G.evenHoleDeformationClassOf C₀) =
      (canonicalBubbleWandNormalization G K P Q C₀ : R) := by
  simp only [canonicalBubbleWandClassNormalization,
    canonicalBubbleWandNormalization,
    bubbleWandTargetsInClass_mk]

/-- The quotient-level uniform construction satisfies exactly the
normalization equation printed below Eq. (E1). -/
theorem canonicalBubbleWandClassNormalization_sum_inverse
    {R : Type w} [Field R] [CharZero R]
    (G : SimpleGraph V) (K : Set V) [Fintype V]
    (P : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G)
    (hne : (bubbleWandTargetsInClass G K P c).Nonempty) :
    (1 / 2 : R) *
        ∑ Q ∈ bubbleWandTargetsInClass G K P c,
          (canonicalBubbleWandClassNormalization G K P Q c)⁻¹ = 1 := by
  classical
  let targets := bubbleWandTargetsInClass G K P c
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
