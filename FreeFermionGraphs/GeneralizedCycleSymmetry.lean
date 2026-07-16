import FreeFermionGraphs.DeformationClosureRelation
import FreeFermionGraphs.TokenSlidingCharges

/-!
# Generalized cycle symmetries

The combinatorial content of Definition 15.  As with token-sliding charges,
the operator `h_C` is represented by an arbitrary additive weight on carrier
sets; the closure sum is independent of the representative used to name the
deformation class.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- The finite set of carriers in the deformation closure `⟨C₀⟩`. -/
noncomputable def deformationClosureFinset (G : SimpleGraph V) (C₀ : Set V)
    [Fintype V] [DecidableEq V] : Finset (Set V) := by
  classical
  exact Finset.univ.filter (InEvenHoleDeformationClosure G C₀)

@[simp]
theorem mem_deformationClosureFinset {G : SimpleGraph V} {C₀ C : Set V}
    [Fintype V] [DecidableEq V] :
    C ∈ G.deformationClosureFinset C₀ ↔
      InEvenHoleDeformationClosure G C₀ C := by
  classical
  simp [deformationClosureFinset]

/-- Deformation-equivalent representatives determine the same finite
closure. -/
theorem deformationClosureFinset_eq_of_mem {G : SimpleGraph V}
    {C₀ C₁ : Set V} [Fintype V] [DecidableEq V]
    (h : InEvenHoleDeformationClosure G C₀ C₁) :
    G.deformationClosureFinset C₀ = G.deformationClosureFinset C₁ := by
  classical
  ext C
  simp only [mem_deformationClosureFinset]
  constructor
  · intro h₀C
    exact InEvenHoleDeformationClosure.trans
      (InEvenHoleDeformationClosure.symm h) h₀C
  · intro h₁C
    exact InEvenHoleDeformationClosure.trans h h₁C

/-- Definition 15, in generic additive form: sum the carrier weights over a
whole deformation closure. -/
noncomputable def generalizedCycleSymmetry (G : SimpleGraph V) (C₀ : Set V)
    [Fintype V] [DecidableEq V] {A : Type w} [AddCommMonoid A]
    (weight : Set V → A) : A :=
  (G.deformationClosureFinset C₀).sum weight

/-- A generalized cycle sum depends only on weights inside its closure. -/
theorem generalizedCycleSymmetry_congr (G : SimpleGraph V) (C₀ : Set V)
    [Fintype V] [DecidableEq V] {A : Type w} [AddCommMonoid A]
    {weight weight' : Set V → A}
    (h : ∀ C, InEvenHoleDeformationClosure G C₀ C →
      weight C = weight' C) :
    G.generalizedCycleSymmetry C₀ weight =
      G.generalizedCycleSymmetry C₀ weight' := by
  unfold generalizedCycleSymmetry
  apply Finset.sum_congr rfl
  intro C hC
  exact h C (mem_deformationClosureFinset.mp hC)

/-- The generalized cycle symmetry is independent of the chosen carrier used
to name a deformation closure. -/
theorem generalizedCycleSymmetry_eq_of_mem {G : SimpleGraph V}
    {C₀ C₁ : Set V} [Fintype V] [DecidableEq V]
    {A : Type w} [AddCommMonoid A] (weight : Set V → A)
    (h : InEvenHoleDeformationClosure G C₀ C₁) :
    G.generalizedCycleSymmetry C₀ weight =
      G.generalizedCycleSymmetry C₁ weight := by
  unfold generalizedCycleSymmetry
  rw [deformationClosureFinset_eq_of_mem h]

end SimpleGraph
