import FreeFermionGraphs.HoleOperatorTransport
import FreeFermionGraphs.PauliShiftModel
import Mathlib.Algebra.BigOperators.Fin

/-!
# Non-vacuity of the hole-operator transport on the palindromic example of v1

`HoleOperatorTransport` proves, for a complete Definition 19 deformation `F` and a scaled Pauli
representation `H`,

* `h_C h_O = κ₁ h_{C~}` (`evenHoleOperator_mul_pairProduct`), and
* `h_O h_{C'} = κ₂ h_{C~'}` along a `ReverseRun`
  (`pairProduct_mul_evenHoleOperator_of_reverseRun`).

This module checks that these statements are not vacuous.  On the ten-vertex claw-free graph
`Lemma12ResidualExample.graph` (v1's palindromic path example, v1 L957-966, with `ℓ = 2`) there
is the genuinely two-step deformation `Lemma12ResidualExample.full` together with its reverse run
from `C' = (d_0, c_0, d_1, c_1, d_2, c_2)`.  The graph is realised by the concrete Pauli-type
operators of `PauliShiftModel`, with couplings `b_v = v + 1` over `ℚ`, so that the scalars
`κ₁ = b_0^2 b_2^2 = 9` and `κ₂ = b_5^2 b_7^2 = 2304` are non-trivial and `κ₁ κ₂ = 144^2`.

The hole operators on both sides are invertible, hence non-zero.

## Main declarations

* `HoleOperatorTransportExample.rep`: the scaled Pauli representation of the example graph.
* `HoleOperatorTransportExample.removedWeight_eq`, `introducedWeight_eq`: `κ₁ = 9`, `κ₂ = 2304`.
* `HoleOperatorTransportExample.forward_transport`, `reverse_transport`: the two identities,
  instantiated.
* `HoleOperatorTransportExample.isUnit_evenHoleOperator`, `evenHoleOperator_ne_zero`: the hole
  operators are invertible, hence non-zero.
* `HoleOperatorTransportExample.transport_nonvacuous`: everything at once.
-/

namespace SimpleGraph

namespace HoleOperatorTransportExample

open Lemma12ResidualExample FixedPairingPathFamily
open FixedPairingPathFamily.FullDefinition19Deformation

/-- The operator algebra of the example: endomorphisms of `ℚ^{Finset (Fin 10)}`. -/
abbrev Op : Type := Module.End ℚ (Finset (Fin 10) → ℚ)

theorem coupling_isUnit (v : Fin 10) : IsUnit ((v.val : ℚ) + 1) :=
  IsUnit.mk0 _ (Nat.cast_add_one_ne_zero v.val)

/-- The scaled Pauli representation of the example graph with couplings `b_v = v + 1`. -/
def rep : graph.ScaledPauliFrustrationRepresentation ℚ Op :=
  PauliShiftModel.scaledRepresentation graph ℚ (fun v => (v.val : ℚ) + 1) coupling_isUnit
    two_ne_zero

theorem coupling_eq (v : Fin 10) : rep.coupling v = (v.val : ℚ) + 1 := rfl

/-- `κ₁ = b_{a_0}^2 b_{a_1}^2 = 1^2 · 3^2 = 9` (the removed vertices are `a_0 = 0` and
`a_1 = 2`). -/
theorem removedWeight_eq : full.removedWeight rep = 9 := by
  change ∏ t : Fin 2, rep.coupling
    ((full.deformation.step t).before.vertex (full.deformation.step t).removedIndex) ^ 2 = 9
  rw [Fin.prod_univ_two]
  show rep.coupling ((full.deformation.step ⟨0, by decide⟩).before.vertex
      (full.deformation.step ⟨0, by decide⟩).removedIndex) ^ 2 *
    rep.coupling ((full.deformation.step ⟨1, by decide⟩).before.vertex
      (full.deformation.step ⟨1, by decide⟩).removedIndex) ^ 2 = 9
  have h0 : (full.deformation.step ⟨0, by decide⟩).before.vertex
      (full.deformation.step ⟨0, by decide⟩).removedIndex = 0 := rfl
  have h1 : (full.deformation.step ⟨1, by decide⟩).before.vertex
      (full.deformation.step ⟨1, by decide⟩).removedIndex = 2 := rfl
  rw [h0, h1, coupling_eq, coupling_eq]
  norm_num

/-- `κ₂ = b_{c_0}^2 b_{c_1}^2 = 6^2 · 8^2 = 2304` (the introduced vertices are
`c_0 = 5`, `c_1 = 7`). -/
theorem introducedWeight_eq : full.introducedWeight rep = 2304 := by
  change ∏ t : Fin 2, rep.coupling (full.deformation.step t).introduced ^ 2 = 2304
  rw [Fin.prod_univ_two]
  show rep.coupling (full.deformation.step ⟨0, by decide⟩).introduced ^ 2 *
    rep.coupling (full.deformation.step ⟨1, by decide⟩).introduced ^ 2 = 2304
  have h0 : (full.deformation.step ⟨0, by decide⟩).introduced = 5 := rfl
  have h1 : (full.deformation.step ⟨1, by decide⟩).introduced = 7 := rfl
  rw [h0, h1, coupling_eq, coupling_eq]
  norm_num

/-- The hole operator of every even indexed hole is invertible in the example: it is the
product of the two class products, which are invertible by `independentProduct_isUnit`. -/
theorem isUnit_evenHoleOperator (C : graph.IndexedInducedHole) (hEven : Even C.card) :
    IsUnit (rep.operator.evenHoleOperator (Set.range C.vertex)) := by
  obtain ⟨k, L, -, -, hL⟩ :=
    rep.operator.exists_fullCyclic_labeling_evenHoleOperator_of_indexedInducedHole C hEven
  rw [hL]
  unfold PauliFrustrationRepresentation.labelingOperator
  exact (rep.independentProduct_isUnit L.isIndepSet_image_a).mul
    (rep.independentProduct_isUnit L.isIndepSet_image_b)

/-- Hence the hole operators of the example are non-zero, so the transport identities are not
`0 = 0`. -/
theorem evenHoleOperator_ne_zero (C : graph.IndexedInducedHole) (hEven : Even C.card) :
    rep.operator.evenHoleOperator (Set.range C.vertex) ≠ 0 :=
  (isUnit_evenHoleOperator C hEven).ne_zero

/-- **Forward transport on the example**: `h_C h_O = 9 · h_{C~}` with
`C = (a_0, b_0, a_1, b_1)` and `C~ = (c_0, b_0, c_1, b_1)`. -/
theorem forward_transport :
    rep.operator.evenHoleOperator (Set.range full.initialHole.vertex) * full.pairProduct rep =
      algebraMap ℚ Op 9 * rep.operator.evenHoleOperator (Set.range full.terminalHole.vertex) := by
  have h := full.evenHoleOperator_mul_pairProduct rep ⟨2, rfl⟩
  rwa [removedWeight_eq] at h

/-- **Reverse transport on the example**: along the reverse run of `Lemma12ResidualExample`
from `C'`, `h_O h_{C'} = 2304 · h_{C~'}`. -/
theorem reverse_transport :
    ∃ R' : graph.IndexedInducedHole, ReverseRun full residualData.primeHole 0 R' ∧
      full.pairProduct rep * rep.operator.evenHoleOperator (Set.range holeC'.vertex) =
        algebraMap ℚ Op 2304 * rep.operator.evenHoleOperator (Set.range R'.vertex) := by
  obtain ⟨R', hrun⟩ := exists_reverseRun
  refine ⟨R', hrun, ?_⟩
  have h := full.pairProduct_mul_evenHoleOperator_of_reverseRun rep
    (P := residualData.primeHole) residualData.primeHole_even hrun
  rwa [introducedWeight_eq] at h

/-- Everything at once: both transport identities hold on the example, with non-zero
(invertible) hole operators and non-trivial scalars `κ₁ = 9`, `κ₂ = 2304`,
`κ₁ κ₂ = 144^2`. -/
theorem transport_nonvacuous :
    (full.removedWeight rep = 9 ∧ full.introducedWeight rep = 2304 ∧
      full.removedWeight rep * full.introducedWeight rep = 144 ^ 2) ∧
    IsUnit (rep.operator.evenHoleOperator (Set.range full.initialHole.vertex)) ∧
    IsUnit (rep.operator.evenHoleOperator (Set.range full.terminalHole.vertex)) ∧
    IsUnit (rep.operator.evenHoleOperator (Set.range holeC'.vertex)) ∧
    rep.operator.evenHoleOperator (Set.range full.initialHole.vertex) * full.pairProduct rep =
      algebraMap ℚ Op 9 * rep.operator.evenHoleOperator (Set.range full.terminalHole.vertex) ∧
    ∃ R' : graph.IndexedInducedHole, ReverseRun full residualData.primeHole 0 R' ∧
      full.pairProduct rep * rep.operator.evenHoleOperator (Set.range holeC'.vertex) =
        algebraMap ℚ Op 2304 * rep.operator.evenHoleOperator (Set.range R'.vertex) := by
  refine ⟨⟨removedWeight_eq, introducedWeight_eq, ?_⟩, isUnit_evenHoleOperator _ ⟨2, rfl⟩,
    isUnit_evenHoleOperator _ ⟨2, rfl⟩, isUnit_evenHoleOperator _ ⟨3, rfl⟩, forward_transport,
    reverse_transport⟩
  rw [removedWeight_eq, introducedWeight_eq]
  norm_num

end HoleOperatorTransportExample

end SimpleGraph
