import FreeFermionGraphs.PauliSetSigns

/-!
# The pairing index `Ψ(s, s')` of two class pairs

This module defines the bilinear invariant `Ψ` used to select the palindromic deformation in the
synthesised proof of Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, subsection
"Generalized Cycle Symmetries", label `subsection:GeneralizedCycleSymmetries`, L929ff).  It has
no counterpart in v1 as a bilinear form: v1 (Definition 21,
`definition:obstructiongraphcoloringclasses`, L1016-1019, label at L1017) prescribes the source
set of the obstruction graph as the larger colouring class, i.e. by a majority vote over pairing
types.  `Ψ` is designed to compute this majority vote: package T3-10 is to prove
`Ψ = |crossed W| - |matched W|` for claw-free graphs and hole classes.  Neither that identity nor
the correspondence of matched/crossed `W` with the pairing-type colour classes of v1 is part of
this module; here `Ψ` is only defined and its algebraic properties (sign flips, symmetry,
parity) are proved.

A *class pair* is a pair `s = (s.1, s.2)` of finite vertex sets (the two colour classes of an even
hole `C = s.1 ∪ s.2`).  Its *sign function* is `χ_s = +1` on `s.1`, `-1` on `s.2` and `0`
elsewhere (`classSign`), and
`Ψ(s, s') = Σ_{x, y} χ_s(x) χ_{s'}(y) (A + 2 I)_{x y}`
(`pairingIndex`), where `A` is the adjacency matrix of `G`.

## Contents

* `SimpleGraph.classSign`: the sign function `χ_s`; `classSign_swap` (it changes sign when the
  two classes of a disjoint pair are exchanged).
* `SimpleGraph.pairingIndex`: the pairing index `Ψ(s, s')`; `pairingIndex_eq_sum_sum` rewrites it
  for any decidable adjacency.
* `SimpleGraph.pairingIndex_swap_right`: `Ψ(s, s'.swap) = -Ψ(s, s')` for a disjoint pair `s'`.
* `SimpleGraph.pairingIndex_swap_swap`: `Ψ(s.swap, s'.swap) = Ψ(s, s')` for disjoint pairs.
* `SimpleGraph.pairingIndex_comm`: `Ψ(s, s') = Ψ(s', s)` (symmetry of `A + 2 I`).
* `SimpleGraph.pairingIndex_emod_two`: `Ψ(s, s') ≡ c(s.1 ∪ s.2, s'.1 ∪ s'.2) (mod 2)`, where
  `c = SimpleGraph.crossCount`.  The term `2 I` contributes an even amount and
  `χ_s ≡ [· ∈ s.1 ∪ s.2] (mod 2)`.  The stronger statement without the disjointness hypotheses
  (which are used only for the two `swap` lemmas) is `pairingIndex_emod_two_general`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The sign function `χ_s` of a class pair `s = (s.1, s.2)`: `+1` on `s.1`, `-1` on `s.2`
(outside `s.1`) and `0` elsewhere.  For a disjoint pair the case "`v ∈ s.2` outside `s.1`" is
simply "`v ∈ s.2`". -/
def classSign [DecidableEq V] (s : Finset V × Finset V) (v : V) : ℤ :=
  if v ∈ s.1 then 1 else if v ∈ s.2 then -1 else 0

/-- The pairing index `Ψ(s, s') = Σ_{x, y} χ_s(x) χ_{s'}(y) (A + 2 I)_{x y}` of two class pairs,
where `A` is the adjacency matrix of `G`.  The definition is noncomputable so that the statements
do not carry a choice of decidable adjacency as data (compare `SimpleGraph.crossCount`). -/
noncomputable def pairingIndex (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (s s' : Finset V × Finset V) : ℤ := by
  classical
  exact ∑ x, ∑ y, classSign s x * classSign s' y *
    ((if G.Adj x y then 1 else 0) + (if x = y then 2 else 0))

section PairingIndex

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- On the first class the sign function is `+1`. -/
theorem classSign_of_mem_fst {v : V} (hv : v ∈ s.1) : classSign s v = 1 := by
  simp [classSign, hv]

/-- On the second class, outside the first, the sign function is `-1`. -/
theorem classSign_of_mem_snd {v : V} (h1 : v ∉ s.1) (h2 : v ∈ s.2) : classSign s v = -1 := by
  simp [classSign, h1, h2]

/-- Outside both classes the sign function vanishes. -/
theorem classSign_of_not_mem {v : V} (h1 : v ∉ s.1) (h2 : v ∉ s.2) : classSign s v = 0 := by
  simp [classSign, h1, h2]

/-- Exchanging the two classes of a disjoint pair negates the sign function pointwise. -/
theorem classSign_swap (hs : Disjoint s.1 s.2) (v : V) :
    classSign s.swap v = -classSign s v := by
  by_cases h1 : v ∈ s.1
  · have h2 : v ∉ s.2 := Finset.disjoint_left.mp hs h1
    simp [classSign, h1, h2]
  · by_cases h2 : v ∈ s.2
    · simp [classSign, h1, h2]
    · simp [classSign, h1, h2]

/-- The sign function vanishes exactly off the union of the two classes. -/
theorem classSign_ne_zero_iff (v : V) : classSign s v ≠ 0 ↔ v ∈ s.1 ∪ s.2 := by
  by_cases h1 : v ∈ s.1
  · simp [classSign, h1]
  · by_cases h2 : v ∈ s.2
    · simp [classSign, h1, h2]
    · simp [classSign, h1, h2]

/-- The sign function is `1` or `-1` on the union of the two classes. -/
theorem classSign_mod_two (v : V) :
    classSign s v % 2 = if v ∈ s.1 ∪ s.2 then 1 else 0 := by
  by_cases h1 : v ∈ s.1
  · simp [classSign, h1]
  · by_cases h2 : v ∈ s.2
    · simp [classSign, h1, h2]
    · simp [classSign, h1, h2]

variable [Fintype V]

/-- The pairing index unfolds, for any decidable adjacency, to the double sum defining it. -/
theorem pairingIndex_eq_sum_sum [DecidableRel G.Adj] (s s' : Finset V × Finset V) :
    G.pairingIndex s s' = ∑ x, ∑ y, classSign s x * classSign s' y *
      ((if G.Adj x y then 1 else 0) + (if x = y then 2 else 0)) := by
  unfold pairingIndex
  convert rfl

/-- Exchanging the two classes of the second (disjoint) pair negates the pairing index:
`Ψ(s, s'.swap) = -Ψ(s, s')`. -/
theorem pairingIndex_swap_right (hs' : Disjoint s'.1 s'.2) :
    G.pairingIndex s s'.swap = -G.pairingIndex s s' := by
  classical
  rw [pairingIndex_eq_sum_sum, pairingIndex_eq_sum_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [classSign_swap hs']
  ring

/-- The pairing index is symmetric: `Ψ(s, s') = Ψ(s', s)`, because `A + 2 I` is a symmetric
matrix. -/
theorem pairingIndex_comm : G.pairingIndex s s' = G.pairingIndex s' s := by
  classical
  rw [pairingIndex_eq_sum_sum, pairingIndex_eq_sum_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have hxy : (if x = y then (2 : ℤ) else 0) = if y = x then 2 else 0 := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  have hadj : (if G.Adj x y then (1 : ℤ) else 0) = if G.Adj y x then 1 else 0 := by
    simp only [G.adj_comm x y]
  rw [hxy, hadj]
  ring

/-- Exchanging the two classes of the first (disjoint) pair negates the pairing index:
`Ψ(s.swap, s') = -Ψ(s, s')`. -/
theorem pairingIndex_swap_left (hs : Disjoint s.1 s.2) :
    G.pairingIndex s.swap s' = -G.pairingIndex s s' := by
  rw [pairingIndex_comm, pairingIndex_swap_right hs, pairingIndex_comm]

/-- Exchanging the two classes of both (disjoint) pairs leaves the pairing index unchanged:
`Ψ(s.swap, s'.swap) = Ψ(s, s')`. -/
theorem pairingIndex_swap_swap (hs : Disjoint s.1 s.2) (hs' : Disjoint s'.1 s'.2) :
    G.pairingIndex s.swap s'.swap = G.pairingIndex s s' := by
  rw [pairingIndex_swap_right hs', pairingIndex_swap_left hs, neg_neg]

/-- A finite sum over a finset of integers is determined modulo `2` by the summands modulo `2`. -/
private theorem sum_emod_two_congr {ι : Type*} (S : Finset ι) (a b : ι → ℤ)
    (h : ∀ i ∈ S, a i % 2 = b i % 2) : (∑ i ∈ S, a i) % 2 = (∑ i ∈ S, b i) % 2 := by
  rw [Finset.sum_int_mod S 2 a, Finset.sum_int_mod S 2 b]
  exact congrArg (· % 2) (Finset.sum_congr rfl h)

/-- A sum over a finset as a sum over the whole fintype with a membership indicator. -/
private theorem sum_eq_sum_ite_mem (W : Finset V) (g : V → ℤ) :
    ∑ x ∈ W, g x = ∑ x, if x ∈ W then g x else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Parity of the pairing index, without disjointness assumptions:
`Ψ(s, s') ≡ c(s.1 ∪ s.2, s'.1 ∪ s'.2) (mod 2)`.  The `2 I` summand is even and
`χ_s ≡ [· ∈ s.1 ∪ s.2] (mod 2)`. -/
theorem pairingIndex_emod_two_general :
    G.pairingIndex s s' % 2 = (G.crossCount (s.1 ∪ s.2) (s'.1 ∪ s'.2) : ℤ) % 2 := by
  classical
  have hcross : (G.crossCount (s.1 ∪ s.2) (s'.1 ∪ s'.2) : ℤ) =
      ∑ x : V, ∑ y : V,
        (if x ∈ s.1 ∪ s.2 then (if y ∈ s'.1 ∪ s'.2 then (if G.Adj x y then (1 : ℤ) else 0)
          else 0) else 0) := by
    rw [crossCount_eq_sum_sum]
    push_cast
    rw [sum_eq_sum_ite_mem (s.1 ∪ s.2)]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ s.1 ∪ s.2
    · simp only [hx, if_true]
      exact sum_eq_sum_ite_mem (s'.1 ∪ s'.2) _
    · simp [hx]
  rw [pairingIndex_eq_sum_sum, hcross]
  refine sum_emod_two_congr _ _ _ fun x _ => sum_emod_two_congr _ _ _ fun y _ => ?_
  have hx := classSign_mod_two (s := s) x
  have hy := classSign_mod_two (s := s') y
  have hsplit : classSign s x * classSign s' y *
      ((if G.Adj x y then (1 : ℤ) else 0) + (if x = y then 2 else 0)) =
      classSign s x * classSign s' y * (if G.Adj x y then (1 : ℤ) else 0) +
        2 * (classSign s x * classSign s' y * (if x = y then 1 else 0)) := by
    by_cases hxy : x = y
    · simp [hxy]
      ring
    · simp [hxy]
  rw [hsplit, Int.add_mul_emod_self_left, Int.mul_emod, Int.mul_emod (classSign s x), hx, hy]
  by_cases hxU : x ∈ s.1 ∪ s.2 <;> by_cases hyU : y ∈ s'.1 ∪ s'.2 <;>
    by_cases hadj : G.Adj x y <;> simp [hxU, hyU, hadj]

/-- Parity of the pairing index: `Ψ(s, s') ≡ c(s.1 ∪ s.2, s'.1 ∪ s'.2) (mod 2)` for disjoint
class pairs.  The disjointness hypotheses are not needed
(`pairingIndex_emod_two_general`); they are kept to match the statement for the hole classes. -/
theorem pairingIndex_emod_two (_hs : Disjoint s.1 s.2) (_hs' : Disjoint s'.1 s'.2) :
    G.pairingIndex s s' % 2 = (G.crossCount (s.1 ∪ s.2) (s'.1 ∪ s'.2) : ℤ) % 2 :=
  pairingIndex_emod_two_general

end PairingIndex

end SimpleGraph
