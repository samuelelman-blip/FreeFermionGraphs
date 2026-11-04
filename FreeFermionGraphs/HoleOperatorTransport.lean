import FreeFermionGraphs.HoleCloneIdentities
import FreeFermionGraphs.Lemma12Residual
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Transport of the hole operator along a deformation and along its reverse run

The proof of cancellation for Theorem 1(iii) (arXiv 2305.15625 v1, "Proof of Cancellation",
L1203-1241) writes
`h_O = ∏_{r ascending} h_{P^(r)}`, with `h_{P^(r)} = h_{P^(r) ∩ C_x} h_{P^(r) ∩ C'_y}`
(v1 L1205-1212), and uses the two relations
`h_C h_O h_O h_{C'} ∝ h_{C~} h_{C~'}` ... "where all scale factors cancel upon conjugating by
`h_O^2`" (v1 L1213-1233).  The two ingredients are never stated in v1:

* `h_C h_O = κ₁ h_{C~}` (the hole operator of `C` is transported to that of the terminal
  hole `C~ = C^(m)` by right multiplication by `h_O`), and
* `h_O h_{C'} = κ₂ h_{C~'}` (the hole operator of the prime hole `C'` is transported to
  that of the end point `C~'` of the reverse run by left multiplication by `h_O`),

with the *same ordered* product `h_O` on both sides.  This module proves both for the
complete Definition 19 deformation `FullDefinition19Deformation` of the repository, with the
explicit scalars `κ₁ = ∏_t b_{k_t}^2` (removed vertices) and `κ₂ = ∏_t b_{j_t}^2`
(introduced vertices), so that `κ₁ κ₂ = ∏_t (b_{k_t} b_{j_t})^2` exactly (the scalar that v1 calls
`B^2` at L1236; the identification `h_O h_O^† = B^2 I` itself is not part of this module).
This makes precise v1's phrase "all scale factors cancel".

## Dictionary

For a deformation `F` with steps `t = 0, …, N-1` the step `t` removes the vertex
`k_t = (F.deformation.step t).before.vertex (F.deformation.step t).removedIndex` and
introduces `j_t = (F.deformation.step t).introduced`.

* `pairProduct H F = ∏_{t ascending} (h_{k_t} h_{j_t})` is v1's ordered `h_O`.  Its factor
  `h_{k_t} h_{j_t}` is the contribution of one single-vertex deformation to
  `h_{P^(r)} = h_{P^(r) ∩ C_x} h_{P^(r) ∩ C'_y}`: in v1's notation the removed vertex belongs to
  a colour class of the original hole `C` and the introduced vertex to one of `C'` (fields
  `removed_mem_original` of the Lemma 12 data and `introduced_mem_prime` of
  `FullDefinition19Deformation`); the identities below do not use this.
* `removedWeight H F = ∏_t b_{k_t}^2` and `introducedWeight H F = ∏_t b_{j_t}^2`.
* `C` is `F.initialHole`, `C~ = C^(m)` is `F.terminalHole`, `C'` is the starting hole
  `P` of a `ReverseRun F P 0 R'`, and `C~'` is its end point `R'`.

## Main declarations

* `SimpleGraph.ScaledPauliFrustrationRepresentation.evenHoleOperator_mul_pair_of_deformation`:
  one indexed step, forward: `h_C (h_k h_j) = b_k^2 h_{C'}`.
* `SimpleGraph.ScaledPauliFrustrationRepresentation.pair_mul_evenHoleOperator_of_deformation`:
  one indexed step, reverse: `(h_k h_j) h_C = b_j^2 h_{C'}` when `C` contains `j`.
* `FullDefinition19Deformation.pairProduct`, `removedWeight`, `introducedWeight`.
* `FullDefinition19Deformation.evenHoleOperator_mul_pairProduct`:
  `h_C h_O = (∏_t b_{k_t}^2) h_{C~}`.
* `FullDefinition19Deformation.pairProduct_mul_evenHoleOperator_of_reverseRun`:
  `h_O h_{C'} = (∏_t b_{j_t}^2) h_{C~'}` along a `ReverseRun`.
* `FullDefinition19Deformation.removedWeight_mul_introducedWeight`:
  `κ₁ κ₂ = ∏_t (b_{k_t} b_{j_t})^2`.
* `FullDefinition19Deformation.evenHoleOperator_mul_pairProduct_mul_pairProduct_mul_`
  `evenHoleOperator`: the combination `h_C (h_O h_O) h_{C'} = κ₁ κ₂ (h_{C~} h_{C~'})` used at
  v1 L1213-1233.

## Fidelity

Both identities are unconditional consequences of the manuscript setup (a scaled Pauli
representation `h_j^2 = b_j^2`, v1 L232) together with the structure `FullDefinition19Deformation`
(for the forward identity) and an explicit `ReverseRun` (for the reverse identity).  The
`ReverseRun` is the datum whose existence is the content of Lemma 12; the identity itself
only needs the run, not the Lemma 12 data.  Neither claw-freeness nor the full Lemma 11 data
are used: only that every step is a literal single-vertex deformation of an even hole.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace ScaledPauliFrustrationRepresentation

variable {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
variable [DecidableEq V]

/-- Indexed forward single-step identity (v1 L1213-1233, `h_C h_O ∝ h_{C~}`, one step).

If `C` is an even indexed hole and `s` is a single-vertex deformation of `C` replacing the
vertex `k = C.vertex q`, then `h_C (h_k h_s) = b_k^2 h_{C'}` with `C' = C.deform h`.  Here `h_C`
is the carrier-level hole operator `evenHoleOperator`.  The proof presents `C` by a
full-cyclic alternating labelling in which `k` is an `a`-vertex (swapping the colour names if
necessary) and applies `labelingOperator_mul_pair`. -/
theorem evenHoleOperator_mul_pair_of_deformation
    (H : G.ScaledPauliFrustrationRepresentation R A)
    (C : G.IndexedInducedHole) (hEven : Even C.card)
    {s : V} {q : Fin C.card} (h : C.SingleVertexDeformation s q) :
    H.operator.evenHoleOperator (Set.range C.vertex) *
        (H.operator.term (C.vertex q) * H.operator.term s) =
      algebraMap R A (H.coupling (C.vertex q) ^ 2) *
        H.operator.evenHoleOperator (Set.range (C.deform h).vertex) := by
  have key : ∀ {k : ℕ} (E : G.EvenHoleLabeling k) (r : Fin k),
      E.carrier = Set.range C.vertex → C.vertex q = E.a r →
      H.operator.evenHoleOperator (Set.range C.vertex) *
          (H.operator.term (C.vertex q) * H.operator.term s) =
        algebraMap R A (H.coupling (C.vertex q) ^ 2) *
          H.operator.evenHoleOperator (Set.range (C.deform h).vertex) := by
    intro k E r hcar hrem
    have hfull : E.HasFullCyclicOrder := E.hasFullCyclicOrder_of_carrier_eq_range C hcar
    obtain ⟨hc, hcar'⟩ := E.transport_indexedDeformation C h r hcar hrem
    have hfull' : (E.deform hc).HasFullCyclicOrder := E.hasFullCyclicOrder_deform hc hfull
    have h1 : H.operator.evenHoleOperator (Set.range C.vertex) =
        H.operator.labelingOperator E := by
      rw [← hcar]
      exact H.operator.evenHoleOperator_eq E hfull
    have h2 : H.operator.evenHoleOperator (Set.range (C.deform h).vertex) =
        H.operator.labelingOperator (E.deform hc) := by
      rw [← hcar']
      exact H.operator.evenHoleOperator_eq (E.deform hc) hfull'
    rw [h1, h2, hrem]
    exact H.labelingOperator_mul_pair E hc
  obtain ⟨k, E, hE⟩ := C.exists_evenHoleLabeling hEven
  have hq : C.vertex q ∈ E.carrier := by
    rw [hE]
    exact ⟨q, rfl⟩
  rcases hq with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact key E r hE hr.symm
  · exact key E.swapColors r (by rw [E.swapColors_carrier, hE]) hr.symm

/-- Indexed reverse single-step identity (v1 L1213-1233, `h_O h_{C'} ∝ h_{C~'}`, one step).

If `C` is an even indexed hole, `j = C.vertex q` is one of its vertices and `k` is a
single-vertex deformation of `C` replacing `j`, then `(h_k h_j) h_C = b_j^2 h_{C'}` with
`C' = C.deform h`.  Compare `evenHoleOperator_mul_pair_of_deformation`: the roles of the two
factors are exchanged, because in a reverse run the *introduced* vertex of the forward step is
the vertex that gets replaced. -/
theorem pair_mul_evenHoleOperator_of_deformation
    (H : G.ScaledPauliFrustrationRepresentation R A)
    (C : G.IndexedInducedHole) (hEven : Even C.card)
    {s : V} {q : Fin C.card} (h : C.SingleVertexDeformation s q) :
    H.operator.term s * H.operator.term (C.vertex q) *
        H.operator.evenHoleOperator (Set.range C.vertex) =
      algebraMap R A (H.coupling (C.vertex q) ^ 2) *
        H.operator.evenHoleOperator (Set.range (C.deform h).vertex) := by
  have key : ∀ {k : ℕ} (E : G.EvenHoleLabeling k) (r : Fin k),
      E.carrier = Set.range C.vertex → C.vertex q = E.a r →
      H.operator.term s * H.operator.term (C.vertex q) *
          H.operator.evenHoleOperator (Set.range C.vertex) =
        algebraMap R A (H.coupling (C.vertex q) ^ 2) *
          H.operator.evenHoleOperator (Set.range (C.deform h).vertex) := by
    intro k E r hcar hrem
    have hfull : E.HasFullCyclicOrder := E.hasFullCyclicOrder_of_carrier_eq_range C hcar
    obtain ⟨hc, hcar'⟩ := E.transport_indexedDeformation C h r hcar hrem
    have hfull' : (E.deform hc).HasFullCyclicOrder := E.hasFullCyclicOrder_deform hc hfull
    have h1 : H.operator.evenHoleOperator (Set.range C.vertex) =
        H.operator.labelingOperator E := by
      rw [← hcar]
      exact H.operator.evenHoleOperator_eq E hfull
    have h2 : H.operator.evenHoleOperator (Set.range (C.deform h).vertex) =
        H.operator.labelingOperator (E.deform hc) := by
      rw [← hcar']
      exact H.operator.evenHoleOperator_eq (E.deform hc) hfull'
    rw [h1, h2, hrem]
    exact H.pair_mul_labelingOperator E hc
  obtain ⟨k, E, hE⟩ := C.exists_evenHoleLabeling hEven
  have hq : C.vertex q ∈ E.carrier := by
    rw [hE]
    exact ⟨q, rfl⟩
  rcases hq with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact key E r hE hr.symm
  · exact key E.swapColors r (by rw [E.swapColors_carrier, hE]) hr.symm

end ScaledPauliFrustrationRepresentation

namespace FixedPairingPathFamily

namespace FullDefinition19Deformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
variable {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]

/-- The factor `h_{k_t} h_{j_t}` of one single-vertex replacement of `F`: the term of the
removed vertex `k_t` followed by the term of the introduced vertex `j_t`.  This is the
contribution of the step to `h_{P^(r)} = h_{P^(r) ∩ C_x} h_{P^(r) ∩ C'_y}` (v1 L1205-1212). -/
noncomputable def pairTerm (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (t : Fin F.deformation.stepCount) : A :=
  H.operator.term ((F.deformation.step t).before.vertex (F.deformation.step t).removedIndex) *
    H.operator.term (F.deformation.step t).introduced

/-- The ordered product `h_O = ∏_{t ascending} (h_{k_t} h_{j_t})` of v1 L1203-1212.  Its
rightmost pair acts first on `C'` (for a `ReverseRun`) and its leftmost pair acts first on `C`
(for the forward identity). -/
noncomputable def pairProduct (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) : A :=
  (List.ofFn fun t : Fin F.deformation.stepCount =>
    H.operator.term ((F.deformation.step t).before.vertex (F.deformation.step t).removedIndex) *
      H.operator.term (F.deformation.step t).introduced).prod

/-- The scalar `κ₁ = ∏_t b_{k_t}^2` collected from the removed vertices. -/
noncomputable def removedWeight (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) : R :=
  ∏ t : Fin F.deformation.stepCount,
    H.coupling ((F.deformation.step t).before.vertex (F.deformation.step t).removedIndex) ^ 2

/-- The scalar `κ₂ = ∏_t b_{j_t}^2` collected from the introduced vertices. -/
noncomputable def introducedWeight (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) : R :=
  ∏ t : Fin F.deformation.stepCount, H.coupling (F.deformation.step t).introduced ^ 2

theorem pairProduct_eq_ofFn_prod (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.pairProduct H = (List.ofFn (F.pairTerm H)).prod :=
  rfl

/-- The removed-vertex weight of step `t`, extended by `1` outside the range of steps. -/
noncomputable def removedWeightAt (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (t : ℕ) : R :=
  if h : t < F.deformation.stepCount then
    H.coupling ((F.deformation.step ⟨t, h⟩).before.vertex
      (F.deformation.step ⟨t, h⟩).removedIndex) ^ 2
  else 1

/-- The introduced-vertex weight of step `t`, extended by `1` outside the range of steps. -/
noncomputable def introducedWeightAt (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (t : ℕ) : R :=
  if h : t < F.deformation.stepCount then
    H.coupling (F.deformation.step ⟨t, h⟩).introduced ^ 2
  else 1

theorem removedWeight_eq_prod_range (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.removedWeight H = ∏ t ∈ Finset.range F.deformation.stepCount, F.removedWeightAt H t := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [removedWeightAt, t.isLt]

theorem introducedWeight_eq_prod_Ico (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.introducedWeight H =
      ∏ t ∈ Finset.Ico 0 F.deformation.stepCount, F.introducedWeightAt H t := by
  rw [← Finset.range_eq_Ico, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [introducedWeightAt, t.isLt]

/-- The product of the first `n` pair terms of `h_O`. -/
noncomputable def pairPrefix (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (n : ℕ) : A :=
  ((List.ofFn (F.pairTerm H)).take n).prod

/-- The product of the pair terms of `h_O` from position `n` on. -/
noncomputable def pairSuffix (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (n : ℕ) : A :=
  ((List.ofFn (F.pairTerm H)).drop n).prod

theorem pairPrefix_zero (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) : F.pairPrefix H 0 = 1 := by
  simp [pairPrefix]

theorem pairPrefix_stepCount (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.pairPrefix H F.deformation.stepCount = F.pairProduct H := by
  unfold pairPrefix pairProduct
  rw [List.take_of_length_le (by simp)]
  rfl

theorem pairPrefix_succ (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) {n : ℕ} (hn : n < F.deformation.stepCount) :
    F.pairPrefix H (n + 1) = F.pairPrefix H n * F.pairTerm H ⟨n, hn⟩ := by
  unfold pairPrefix
  rw [List.take_add_one]
  simp [hn]

theorem pairSuffix_zero (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.pairSuffix H 0 = F.pairProduct H := by
  simp [pairSuffix, pairProduct]
  rfl

theorem pairSuffix_stepCount (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.pairSuffix H F.deformation.stepCount = 1 := by
  unfold pairSuffix
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem pairSuffix_eq (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) {n : ℕ} (hn : n < F.deformation.stepCount) :
    F.pairSuffix H n = F.pairTerm H ⟨n, hn⟩ * F.pairSuffix H (n + 1) := by
  unfold pairSuffix
  rw [List.drop_eq_getElem_cons (by simpa using hn)]
  simp

/-- The identity `κ₁ κ₂ = ∏_t (b_{k_t} b_{j_t})^2`.  The right-hand side is the scalar that v1
calls `B^2` (L1236), taken over the vertices touched by the deformation: it is what makes precise
"all scale factors cancel upon conjugating by `h_O^2`" (v1 L1229). -/
theorem removedWeight_mul_introducedWeight (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) :
    F.removedWeight H * F.introducedWeight H =
      ∏ t : Fin F.deformation.stepCount,
        (H.coupling ((F.deformation.step t).before.vertex
            (F.deformation.step t).removedIndex) * H.coupling (F.deformation.step t).introduced) ^
          2 := by
  unfold removedWeight introducedWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun _ _ => ?_
  rw [mul_pow]

/-- Both transport scalars are units, because every coupling is. -/
theorem removedWeight_isUnit (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) : IsUnit (F.removedWeight H) :=
  IsUnit.prod_iff.mpr fun _ _ => (H.coupling_isUnit _).pow 2

theorem introducedWeight_isUnit (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) : IsUnit (F.introducedWeight H) :=
  IsUnit.prod_iff.mpr fun _ _ => (H.coupling_isUnit _).pow 2

section Transport

variable [DecidableEq V]

/-- Forward transport after `n + 1` steps: `h_C (h_{k_0} h_{j_0}) ⋯ (h_{k_n} h_{j_n}) =
(∏_{t ≤ n} b_{k_t}^2) h_{C^(n)}`, where `C^(n)` is the hole after step `n`.  The proof is the
induction over the steps: `carrier_chain` identifies the carrier after step `n` with the carrier
before step `n + 1`, and `evenHoleOperator` only depends on the carrier. -/
theorem evenHoleOperator_mul_pairPrefix_succ
    (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (hEven : Even F.initialHole.card) :
    ∀ (n : ℕ) (hn : n < F.deformation.stepCount),
      H.operator.evenHoleOperator (Set.range F.initialHole.vertex) * F.pairPrefix H (n + 1) =
        algebraMap R A (∏ t ∈ Finset.range (n + 1), F.removedWeightAt H t) *
          H.operator.evenHoleOperator
            (Set.range (F.deformation.step ⟨n, hn⟩).after.vertex) := by
  intro n
  induction n with
  | zero =>
      intro hn
      have hstep := H.evenHoleOperator_mul_pair_of_deformation
        (F.deformation.step ⟨0, hn⟩).before (F.even_card_before hEven 0 hn)
        (F.deformation.step ⟨0, hn⟩).deformation
      rw [F.pairPrefix_succ H hn, F.pairPrefix_zero H, one_mul]
      simpa [removedWeightAt, hn, initialHole, pairTerm,
        ConcreteDeformationStep.after] using hstep
  | succ n ih =>
      intro hn
      have hprev : n < F.deformation.stepCount := by omega
      have hchain := F.deformation.carrier_chain (i := ⟨n, hprev⟩) (j := ⟨n + 1, hn⟩) rfl
      have hstep := H.evenHoleOperator_mul_pair_of_deformation
        (F.deformation.step ⟨n + 1, hn⟩).before (F.even_card_before hEven (n + 1) hn)
        (F.deformation.step ⟨n + 1, hn⟩).deformation
      rw [F.pairPrefix_succ H hn, ← mul_assoc, ih hprev, hchain, mul_assoc]
      have hpair : F.pairTerm H ⟨n + 1, hn⟩ =
          H.operator.term ((F.deformation.step ⟨n + 1, hn⟩).before.vertex
              (F.deformation.step ⟨n + 1, hn⟩).removedIndex) *
            H.operator.term (F.deformation.step ⟨n + 1, hn⟩).introduced := rfl
      rw [hpair, hstep, ← mul_assoc, ← map_mul, Finset.prod_range_succ _ (n + 1)]
      simp [removedWeightAt, hn, ConcreteDeformationStep.after]

/-- **Forward transport of the hole operator** (v1 L1213-1233: `h_C h_O ∝ h_{C~}`).

For a complete Definition 19 deformation `F` of an even initial hole `C`,
`h_C h_O = (∏_t b_{k_t}^2) h_{C~}`, where `h_O` is the ordered product of the pairs
`h_{k_t} h_{j_t}` over the removed and introduced vertices of the steps, and `C~ = C^(m)` is the
terminal hole.  Unconditional on the manuscript setup (scaled Pauli terms `h_j^2 = b_j^2`);
no claw-freeness and no Lemma 11/12 data are used. -/
theorem evenHoleOperator_mul_pairProduct (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (hEven : Even F.initialHole.card) :
    H.operator.evenHoleOperator (Set.range F.initialHole.vertex) * F.pairProduct H =
      algebraMap R A (F.removedWeight H) *
        H.operator.evenHoleOperator (Set.range F.terminalHole.vertex) := by
  have hpos := F.nonempty
  have hlt : F.deformation.stepCount - 1 < F.deformation.stepCount := by omega
  have hN : F.deformation.stepCount - 1 + 1 = F.deformation.stepCount := by omega
  have key := F.evenHoleOperator_mul_pairPrefix_succ H hEven
    (F.deformation.stepCount - 1) hlt
  rw [hN, F.pairPrefix_stepCount H, ← F.removedWeight_eq_prod_range H] at key
  exact key

/-- Reverse transport along a reverse run: for a `ReverseRun F P n R'`,
`h_{k_n} h_{j_n} ⋯ h_{k_{N-1}} h_{j_{N-1}} h_P = (∏_{t ≥ n} b_{j_t}^2) h_{R'}`. -/
theorem pairSuffix_mul_evenHoleOperator_of_reverseRun
    (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime)
    {P R' : G.IndexedInducedHole} {n : ℕ} (hP : Even P.card)
    (hrun : ReverseRun F P n R') :
    F.pairSuffix H n * H.operator.evenHoleOperator (Set.range P.vertex) =
      algebraMap R A (∏ t ∈ Finset.Ico n F.deformation.stepCount, F.introducedWeightAt H t) *
        H.operator.evenHoleOperator (Set.range R'.vertex) := by
  induction hrun with
  | terminal =>
      simp [pairSuffix_stepCount]
  | @step n hn R tail q removedVertex deformation introduced_mem_original ih =>
      have hEven : Even R.card := (tail.inEvenHoleDeformationClosure hP).2
      have hstep := H.pair_mul_evenHoleOperator_of_deformation R hEven deformation
      rw [removedVertex] at hstep
      rw [F.pairSuffix_eq H hn, mul_assoc, ih,
        Finset.prod_eq_prod_Ico_succ_bot hn]
      have hcomm := Algebra.commutes
        (∏ t ∈ Finset.Ico (n + 1) F.deformation.stepCount, F.introducedWeightAt H t)
        (F.pairTerm H ⟨n, hn⟩)
      rw [← mul_assoc, ← hcomm, mul_assoc]
      have hpair : F.pairTerm H ⟨n, hn⟩ =
          H.operator.term ((F.deformation.step ⟨n, hn⟩).before.vertex
              (F.deformation.step ⟨n, hn⟩).removedIndex) *
            H.operator.term (F.deformation.step ⟨n, hn⟩).introduced := rfl
      rw [hpair, hstep, ← mul_assoc, ← map_mul, mul_comm]
      simp [introducedWeightAt, hn]

/-- **Reverse transport of the hole operator** (v1 L1213-1233: `h_O h_{C'} ∝ h_{C~'}`).

For a reverse run of `F` from an even hole `P` (the prime hole `C'`) to `R'` (the hole `C~'`),
`h_O h_{C'} = (∏_t b_{j_t}^2) h_{C~'}`, with the same ordered product `h_O` as in
`evenHoleOperator_mul_pairProduct`: its rightmost pair acts first on `C'`, matching the fact that
a `ReverseRun` starts from the last forward step and descends.  Together with the forward
identity this gives `κ₁ κ₂ = ∏_t (b_{k_t} b_{j_t})^2`
(`removedWeight_mul_introducedWeight`), which is how the scale factors of v1 cancel.
Unconditional given the run; the existence of the run is Lemma 12. -/
theorem pairProduct_mul_evenHoleOperator_of_reverseRun
    (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime)
    {P R' : G.IndexedInducedHole} (hP : Even P.card) (hrun : ReverseRun F P 0 R') :
    F.pairProduct H * H.operator.evenHoleOperator (Set.range P.vertex) =
      algebraMap R A (F.introducedWeight H) *
        H.operator.evenHoleOperator (Set.range R'.vertex) := by
  have key := F.pairSuffix_mul_evenHoleOperator_of_reverseRun H hP hrun
  rw [F.pairSuffix_zero H, ← F.introducedWeight_eq_prod_Ico H] at key
  exact key

/-- The combined identity behind v1's middle display (L1213-1233): for a reverse run of `F`
from the even hole `P = C'` to `R' = C~'`,
`h_C (h_O h_O) h_{C'} = κ₁ κ₂ (h_{C~} h_{C~'})`.  It is the product of the forward identity
and the reverse identity, which share the same ordered `h_O`. -/
theorem evenHoleOperator_mul_pairProduct_mul_pairProduct_mul_evenHoleOperator
    (H : G.ScaledPauliFrustrationRepresentation R A)
    (F : FullDefinition19Deformation O Cprime) (hEven : Even F.initialHole.card)
    {P R' : G.IndexedInducedHole} (hP : Even P.card) (hrun : ReverseRun F P 0 R') :
    H.operator.evenHoleOperator (Set.range F.initialHole.vertex) *
        (F.pairProduct H * F.pairProduct H) *
        H.operator.evenHoleOperator (Set.range P.vertex) =
      algebraMap R A (F.removedWeight H * F.introducedWeight H) *
        (H.operator.evenHoleOperator (Set.range F.terminalHole.vertex) *
          H.operator.evenHoleOperator (Set.range R'.vertex)) := by
  have hfwd := F.evenHoleOperator_mul_pairProduct H hEven
  have hrev := F.pairProduct_mul_evenHoleOperator_of_reverseRun H hP hrun
  calc H.operator.evenHoleOperator (Set.range F.initialHole.vertex) *
        (F.pairProduct H * F.pairProduct H) *
        H.operator.evenHoleOperator (Set.range P.vertex)
      = (H.operator.evenHoleOperator (Set.range F.initialHole.vertex) * F.pairProduct H) *
          (F.pairProduct H * H.operator.evenHoleOperator (Set.range P.vertex)) := by
        simp only [mul_assoc]
    _ = (algebraMap R A (F.removedWeight H) *
          H.operator.evenHoleOperator (Set.range F.terminalHole.vertex)) *
        (algebraMap R A (F.introducedWeight H) *
          H.operator.evenHoleOperator (Set.range R'.vertex)) := by
        rw [hfwd, hrev]
    _ = algebraMap R A (F.removedWeight H * F.introducedWeight H) *
        (H.operator.evenHoleOperator (Set.range F.terminalHole.vertex) *
          H.operator.evenHoleOperator (Set.range R'.vertex)) := by
        rw [map_mul, mul_assoc, ← mul_assoc
          (H.operator.evenHoleOperator (Set.range F.terminalHole.vertex)),
          ← Algebra.commutes (F.introducedWeight H)
            (H.operator.evenHoleOperator (Set.range F.terminalHole.vertex)),
          mul_assoc, mul_assoc]

end Transport

end FullDefinition19Deformation

end FixedPairingPathFamily

end SimpleGraph
