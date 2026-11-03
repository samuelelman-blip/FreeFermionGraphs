import FreeFermionGraphs.TheoremOneI
import FreeFermionGraphs.TheoremOneII
import FreeFermionGraphs.TheoremOneIII

/-!
# Non-vacuity of Theorem 1 (i)-(iii): an eight-vertex graph with two deformation classes

Witness that the conclusions of `paperTheorem1i`, `paperTheorem1ii` and `paperTheorem1iii` (arXiv
2305.15625 v1, `theorem:conservedcharges`, L864-873) carry content: in a three-qubit Pauli
representation of a claw-free frustration graph, the individual terms `h_C`, `h_{C'}` of the
expansion of `[J_C, J_{C'}]` anticommute, so the commutator of the terms is not zero, while the
commutator of the symmetries is.  Without such an instance, the cancellation between different
terms of the sum (the pairing of v1 L1241) could be a statement about a sum that is zero termwise.

## The instance

The graph `g8` has eight vertices, with labels `0 = b₀, 1 = a₀, 2 = b₁, 3 = a₁, 4 = d₀, 5 = c₀,
6 = d₁, 7 = c₁`, and the fifteen edges `01 12 23 03 45 56 67 47 05 15 25 04 14 26 16`
(`edges8`).  It is claw-free (`clawFree`, by `decide`).  The two 4-holes are

* `C = a₀ b₀ a₁ b₁ = {0, 1, 2, 3}` (`holeC`, `carrierC`), the cycle `0 - 1 - 2 - 3 - 0`, and
* `C' = {4, 5, 6, 7}` (`holeC'`, `carrierC'`), the cycle `4 - 5 - 6 - 7 - 4`,

and the vertex `5` is a clone (in the sense of v1 Definition 10, L682) of `1` in `C`, with
neighbours `0, 1, 2`, while `1` is a clone of `5` in `C'`, with neighbours `4, 5, 6`.  The vertex `3`
is adjacent to `C` but not to `C'`.

* **The crossing number is odd.**  `c(C, C') = 7`: the anticommutation graph has seven edges
  between `C` and `C'` (the edges `05, 15, 25, 04, 14, 26, 16`).  Consequently the terms `h_C`
  and `h_{C'}` anticommute (`terms_anticommute`: `h_C h_{C'} ≠ h_{C'} h_C`, evaluated through
  `hC_eq`, `hC'_eq` on explicit integer matrices).
* **The holes lie in different deformation classes.**  `not_same_class` shows that `C'` is not in
  the deformation closure of `C`: by v1 Lemma 4 (L736; repo `lemma9`, `openNeighborhood_eq`) holes
  of one class have the same open neighbourhood, and `3 ∈ Γ(C) ∖ Γ(C')`.  Hence `J_C ≠ J_{C'}`
  as sums over different families, and the commutation of `J_C` and `J_{C'}` is not the trivial
  case `C' ∈ ⟨C⟩`, where `[J_C, J_{C'}] = [J_C, J_C] = 0`.
* **The representation** `rep` is the `PauliFrustrationRepresentation` over `Matrix (Fin 8) (Fin 8) ℤ`
  with the terms `T j` (products of the Pauli matrices `xOp i`, `zOp i` on three qubits),
  anticommuting along the edges of `g8` and commuting along the non-edges (`T_anti`, `T_comm`,
  `T_not_anti`, each by `decide +kernel`).

## Main declarations

* `SimpleGraph.TheoremOneExample.thm1iii_content`: Theorem 1 (iii) for `C`, `C'`:
  `[J_C, J_{C'}] = 0`, the holes lie in different deformation classes, and `[h_C, h_{C'}] ≠ 0`.
* `SimpleGraph.TheoremOneExample.thm1ii_content`: Theorem 1 (ii) for `C` and the token-sliding
  component of `{5}`: `[J_C, q_{1, μ}] = 0` although `[h_C, h_{{5}}] ≠ 0`.
* `SimpleGraph.TheoremOneExample.thm1i_content`: Theorem 1 (i) for the components of `{4}` and
  `{3, 7}`: `[q_{1, μ}, q_{2, ν}] = 0` although `[h_{{4}}, h_{{3, 7}}] ≠ 0`.

## Relation to the earlier instances

The instances of `T3NonVacuity` (`SimpleGraph.T3Example.graph7`) and `T3FixedPairingExample` have
`C ⊕ T = C'` for the toggle `T` of their deformation (`fpExD_carrier_fwdEnd`), so `C'` lies in the
deformation closure of `C`, `J_C = J_{C'}`, and `[J_C, J_{C'}] = 0` is trivial there.  In `graph7`
the six 4-holes form a single deformation class.  The module `T3NonVacuity` therefore witnesses
that the existence layer (`palindromicToggles` nonempty) is inhabited, but not that Theorem 1 (iii)
has content.  The present module is the genuine witness for Theorem 1 (iii): there the pair
`(C, C')` has odd crossing number, `h_C` and `h_{C'}` anticommute, and two different classes are
involved; the cancellation of the sum in `[J_C, J_{C'}]` has to take place between the terms
`(C ⊕ T, C' ⊕ T)` of the pairing, the `T` being a toggle of an odd palindromic deformation
(`palindromicToggles`).

No `sorry`, no axiom and no `native_decide`: the finite matrix identities are checked by
`decide +kernel`.
-/

open scoped symmDiff

namespace SimpleGraph

namespace TheoremOneExample

/-! ### The graph -/

/-- The edges of the example graph `g8`, on the labels
`0 = b₀, 1 = a₀, 2 = b₁, 3 = a₁, 4 = d₀, 5 = c₀, 6 = d₁, 7 = c₁`: the 4-cycle `0 1 2 3` (the hole
`C`), the 4-cycle `4 5 6 7` (the hole `C'`), the neighbours `0, 1, 2` of the clone `5` of `1`, and
the neighbours `4, 5, 6` of the clone `1` of `5`. -/
def edges8 : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (0, 3), (4, 5), (5, 6), (6, 7), (4, 7), (0, 5), (1, 5), (2, 5), (0, 4),
    (1, 4), (2, 6), (1, 6)]

/-- The example graph: two 4-holes `C = 0 1 2 3` and `C' = 4 5 6 7` with the seven edges
`05, 15, 25, 04, 14, 26, 16` between them (so `c(C, C') = 7`). -/
def g8 : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun x y => (x.val, y.val) ∈ edges8

instance : DecidableRel g8.Adj := by
  unfold g8
  infer_instance

set_option synthInstance.maxSize 1000 in
/-- The graph `g8` is claw-free, so Theorem 1 applies to it. -/
theorem clawFree : g8.IsClawFree := by
  have h : ∀ c a b d : Fin 8, g8.Adj c a → g8.Adj c b → g8.Adj c d → a ≠ b → a ≠ d →
      b ≠ d → g8.Adj a b ∨ g8.Adj a d ∨ g8.Adj b d := by decide
  exact fun c a b d => h c a b d

/-! ### A three-qubit integer Pauli realisation -/

/-- The Pauli matrix `X` on qubit `i` of three qubits, as an integer matrix indexed by `Fin 8`
(basis states are bit strings; `X_i` flips bit `i`). -/
def xOp (i : ℕ) : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a b => if a.val = b.val ^^^ 2 ^ i then 1 else 0

/-- The Pauli matrix `Z` on qubit `i` of three qubits, as an integer matrix indexed by `Fin 8`. -/
def zOp (i : ℕ) : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.diagonal fun a => if a.val.testBit i then -1 else 1

/-- The Hamiltonian terms: Pauli strings on three qubits, one for each vertex of `g8`, with
anticommutation pattern given by the edges of `g8`. -/
def T : Fin 8 → Matrix (Fin 8) (Fin 8) ℤ
  | 0 => zOp 0
  | 1 => xOp 0
  | 2 => zOp 0 * zOp 1
  | 3 => xOp 0 * zOp 2
  | 4 => xOp 0 * zOp 0 * xOp 1 * xOp 2
  | 5 => xOp 0 * zOp 0 * zOp 1 * xOp 2
  | 6 => zOp 0 * xOp 1 * xOp 2 * zOp 2
  | 7 => zOp 1

/-- Adjacent vertices have anticommuting terms. -/
theorem T_anti : ∀ j k : Fin 8, g8.Adj j k → T j * T k = -(T k * T j) := by decide +kernel

/-- Non-adjacent vertices have commuting terms. -/
theorem T_comm : ∀ j k : Fin 8, ¬ g8.Adj j k → T j * T k = T k * T j := by decide +kernel

/-- Terms of non-adjacent vertices do not anticommute. -/
theorem T_not_anti : ∀ j k : Fin 8, ¬ g8.Adj j k → T j * T k ≠ -(T k * T j) := by
  decide +kernel

/-- The Pauli frustration representation of `g8` on three qubits with integer entries. -/
def rep : g8.PauliFrustrationRepresentation (Matrix (Fin 8) (Fin 8) ℤ) where
  term := T
  adj_iff_anticommute := by
    intro j k
    constructor
    · exact T_anti j k
    · intro h
      by_contra hn
      exact T_not_anti j k hn h
  commute_of_not_adj := fun {j k} h => T_comm j k h

/-! ### The two holes -/

/-- The 4-hole `0 - 1 - 2 - 3 - 0` of `g8`, as an indexed induced hole. -/
def holeC : g8.IndexedInducedHole where
  card := 4
  four_le_card := le_rfl
  vertex := ![0, 1, 2, 3]
  injective := by decide
  adj_iff := by unfold CyclicAdjacent; decide

/-- The 4-hole `4 - 5 - 6 - 7 - 4` of `g8`, as an indexed induced hole. -/
def holeC' : g8.IndexedInducedHole where
  card := 4
  four_le_card := le_rfl
  vertex := ![4, 5, 6, 7]
  injective := by decide
  adj_iff := by unfold CyclicAdjacent; decide

/-- The carrier `{0, 1, 2, 3}` of the first hole. -/
def C : Set (Fin 8) := {0, 1, 2, 3}

/-- The carrier `{4, 5, 6, 7}` of the second hole. -/
def C' : Set (Fin 8) := {4, 5, 6, 7}

/-- `C` is the carrier of an even hole of `g8`. -/
theorem carrierC : g8.IsEvenHoleCarrier C :=
  ⟨holeC, ⟨2, rfl⟩, by ext x; fin_cases x <;> simp [holeC, C]⟩

/-- `C'` is the carrier of an even hole of `g8`. -/
theorem carrierC' : g8.IsEvenHoleCarrier C' :=
  ⟨holeC', ⟨2, rfl⟩, by ext x; fin_cases x <;> simp [holeC', C']⟩

/-! ### Evaluation of the hole operators -/

/-- A pair of distinct non-adjacent vertices is an independent set. -/
theorem indep_pair {a b : Fin 8} (hab : a ≠ b) (h : ¬ g8.Adj a b) :
    g8.IsIndepSet ((({a, b} : Finset (Fin 8))) : Set (Fin 8)) := by
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h
  · exact fun h' => h h'.symm
  · exact absurd rfl hxy

/-- The independent product of a pair of distinct non-adjacent vertices is the product of their
terms. -/
theorem independentProduct_pair {a b : Fin 8} (hab : a ≠ b) (h : ¬ g8.Adj a b) :
    rep.independentProduct {a, b} = T a * T b := by
  have hb : rep.independentProduct {b} = T b := by
    rw [rep.independentProduct_eq_noncommProd (by simp)]
    exact Finset.noncommProd_singleton b rep.term
  rw [rep.independentProduct_insert_left (by simpa using hab) (by simp)
    (by simpa using h), hb]
  rfl

/-- The independent product of a singleton is the term of its vertex. -/
theorem indep_singleton (a : Fin 8) :
    rep.independentProduct {a} = T a := by
  rw [rep.independentProduct_eq_noncommProd (by simp)]
  exact Finset.noncommProd_singleton a rep.term

/-- The hole operator of `C`: `h_C = (T₀ T₂)(T₁ T₃)`, the product over the two colour classes
`{0, 2}` and `{1, 3}`. -/
theorem hC_eq : rep.evenHoleOperator C = T 0 * T 2 * (T 1 * T 3) := by
  have hcov : ((({0, 2} : Finset (Fin 8))) : Set (Fin 8)) ∪
      (({1, 3} : Finset (Fin 8)) : Set (Fin 8)) = C := by
    ext x; fin_cases x <;> simp [C]
  rw [(rep.evenHoleOperator_eq_of_colouring carrierC hcov (by decide)
    (indep_pair (by decide) (by decide)) (indep_pair (by decide) (by decide))).1,
    independentProduct_pair (by decide) (by decide),
    independentProduct_pair (by decide) (by decide)]

/-- The hole operator of `C'`: `h_{C'} = (T₄ T₆)(T₅ T₇)`, the product over the two colour classes
`{4, 6}` and `{5, 7}`. -/
theorem hC'_eq : rep.evenHoleOperator C' = T 4 * T 6 * (T 5 * T 7) := by
  have hcov : ((({4, 6} : Finset (Fin 8))) : Set (Fin 8)) ∪
      (({5, 7} : Finset (Fin 8)) : Set (Fin 8)) = C' := by
    ext x; fin_cases x <;> simp [C']
  rw [(rep.evenHoleOperator_eq_of_colouring carrierC' hcov (by decide)
    (indep_pair (by decide) (by decide)) (indep_pair (by decide) (by decide))).1,
    independentProduct_pair (by decide) (by decide),
    independentProduct_pair (by decide) (by decide)]

/-! ### Theorem 1 (iii): the conclusion has content -/

/-- The two holes lie in different deformation classes: the vertex `3` (`a₁`) is adjacent to `C` but
not to `C'`, whereas holes of one class have the same open neighbourhood (v1 Lemma 4, L736). -/
theorem not_same_class : ¬ InEvenHoleDeformationClosure g8 C C' := by
  intro h
  have e := h.openNeighborhood_eq clawFree
  have h3 : (3 : Fin 8) ∈ g8.openNeighborhood C := ⟨0, by simp [C], by decide⟩
  rw [e] at h3
  obtain ⟨v, hv, hadj⟩ := h3
  simp only [C', Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> revert hadj <;> decide

/-- The term `(C, C')` of the expansion of `[J_C, J_{C'}]` is not zero: `h_C` and `h_{C'}` do not
commute (they anticommute, the crossing number `c(C, C')` being `7`). -/
theorem terms_anticommute :
    rep.evenHoleOperator C * rep.evenHoleOperator C' ≠
      rep.evenHoleOperator C' * rep.evenHoleOperator C := by
  rw [hC_eq, hC'_eq]
  decide +kernel

/-- **Non-vacuity of Theorem 1 (iii)** (v1 L864-873, proof L1203-1243).  In the representation `rep`
of the claw-free graph `g8`, the generalized cycle symmetries of the 4-holes `C` and `C'` commute
(`paperTheorem1iii`), although `C'` is not in the deformation class of `C` and the terms `h_C` and
`h_{C'}` do not commute. -/
theorem thm1iii_content :
    algebraCommutator (rep.generalizedCycleSymmetryOp C) (rep.generalizedCycleSymmetryOp C') = 0 ∧
    ¬ InEvenHoleDeformationClosure g8 C C' ∧
    algebraCommutator (rep.evenHoleOperator C) (rep.evenHoleOperator C') ≠ 0 :=
  ⟨rep.paperTheorem1iii clawFree carrierC carrierC', not_same_class, by
    unfold algebraCommutator
    exact sub_ne_zero.2 terms_anticommute⟩

/-! ### Theorem 1 (ii): the conclusion has content -/

/-- The token configuration `{5}` with one token. -/
def S5 : g8.TokenConfiguration 1 := ⟨{5}, by
  refine ⟨by simp, by simp⟩⟩

/-- **Non-vacuity of Theorem 1 (ii)** (v1 L864-873, proof L908-927).  The generalized cycle
symmetry `J_C` commutes with the token-sliding charge `q_{1, μ}` of the component `μ` of the
configuration `{5}`, although `h_C` and `h_{{5}}` do not commute. -/
theorem thm1ii_content :
    algebraCommutator (rep.generalizedCycleSymmetryOp C)
        (rep.tokenSlidingChargeOp 1 (g8.tokenSlidingComponentMk 1 S5)) = 0 ∧
    algebraCommutator (rep.evenHoleOperator C) (rep.independentProduct S5.1) ≠ 0 := by
  refine ⟨rep.paperTheorem1ii clawFree carrierC 1 _, ?_⟩
  unfold algebraCommutator
  rw [hC_eq]
  show T 0 * T 2 * (T 1 * T 3) * rep.independentProduct {5} -
      rep.independentProduct {5} * (T 0 * T 2 * (T 1 * T 3)) ≠ 0
  rw [indep_singleton]
  decide +kernel

/-! ### Theorem 1 (i): the conclusion has content -/

/-- The token configuration `{4}` with one token. -/
def S4 : g8.TokenConfiguration 1 := ⟨{4}, by
  refine ⟨by simp, by simp⟩⟩

/-- The token configuration `{3, 7}` with two tokens. -/
def S37 : g8.TokenConfiguration 2 := ⟨{3, 7}, ⟨indep_pair (by decide) (by decide), by decide⟩⟩

/-- **Non-vacuity of Theorem 1 (i)** (v1 L864-873, proof L880-906).  The token-sliding charges
`q_{1, μ}` and `q_{2, ν}` of the components `μ` of `{4}` and `ν` of `{3, 7}` commute, although
`h_{{4}}` and `h_{{3, 7}}` do not commute. -/
theorem thm1i_content :
    algebraCommutator (rep.tokenSlidingChargeOp 1 (g8.tokenSlidingComponentMk 1 S4))
        (rep.tokenSlidingChargeOp 2 (g8.tokenSlidingComponentMk 2 S37)) = 0 ∧
    algebraCommutator (rep.independentProduct S4.1) (rep.independentProduct S37.1) ≠ 0 := by
  refine ⟨rep.paperTheorem1i clawFree 1 2 _ _, ?_⟩
  unfold algebraCommutator
  show rep.independentProduct {4} * rep.independentProduct {3, 7} -
      rep.independentProduct {3, 7} * rep.independentProduct {4} ≠ 0
  rw [indep_singleton, independentProduct_pair (by decide) (by decide)]
  decide +kernel

end TheoremOneExample

end SimpleGraph
