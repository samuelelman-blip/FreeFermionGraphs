import FreeFermionGraphs.OperatorCharges

/-!
# Theorem 1 (iii): expansion of `[J_{C₀}, J_{C₀'}]`

This module contains the first step of the proof of part (iii) of the Conserved Charges theorem of
the manuscript (arXiv 2305.15625 v1, `theorem:conservedcharges` (iii), L864-871; the proof of
part (iii) begins at L929): the commutator of two generalized cycle symmetries (Definition 15,
v1 L799) is expanded as a sum over pairs of deformation-closure members,
`equation:conservedcyclecommutator` (v1 L934-936),
`[J_{C₀}, J_{C₀'}] = Σ_{C ∈ ⟨C₀⟩, C' ∈ ⟨C₀'⟩} [h_C, h_{C'}]`.

* `PauliFrustrationRepresentation.commutator_generalizedCycleSymmetryOp_pair_eq_sum`: the
  expansion, over an arbitrary ring `A` and for arbitrary carriers `C₀`, `C₀'` (no claw-freeness,
  no even-hole hypothesis: it is a purely formal consequence of bilinearity of the commutator and
  of the definitions of `J_{C₀}` and `⟨C₀⟩`).  It is the analogue of
  `PauliFrustrationRepresentation.commutator_generalizedCycleSymmetryOp_eq_sum` (Theorem 1 (ii),
  `FreeFermionGraphs.TheoremOneII`) and simpler than it, since there are no indicators: both
  sums run over deformation closures.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- Expansion of the commutator of two generalized cycle symmetries as a sum over pairs of
deformation-closure members (v1 L934-936, `equation:conservedcyclecommutator`):
`[J_{C₀}, J_{C₀'}] = Σ_{(C, C') ∈ ⟨C₀⟩ × ⟨C₀'⟩} [h_C, h_{C'}]`. -/
theorem commutator_generalizedCycleSymmetryOp_pair_eq_sum [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (C₀ C₀' : Set V) :
    algebraCommutator (H.generalizedCycleSymmetryOp C₀) (H.generalizedCycleSymmetryOp C₀') =
      ∑ p ∈ G.deformationClosureFinset C₀ ×ˢ G.deformationClosureFinset C₀',
        algebraCommutator (H.evenHoleOperator p.1) (H.evenHoleOperator p.2) := by
  unfold generalizedCycleSymmetryOp generalizedCycleSymmetry algebraCommutator
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_product]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← Finset.sum_sub_distrib]

end PauliFrustrationRepresentation

end SimpleGraph
