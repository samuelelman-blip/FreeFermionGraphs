import FreeFermionGraphs.OperatorCharges

/-!
# Toggle identity for products of independent-set Pauli terms (bare representation)

This module formalises the reordering step in the proof of cancellation in the proof of
Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, L1203-1211: the reordering
`h_C h_O h_O h_C'`), which generalises the Theorem 1(i) toggle of v1 L897-899
(`PauliFrustrationRepresentation.independentProduct_toggle_add_eq_zero`).

## Contents

* `PauliFrustrationRepresentation.independentProduct_toggle_mul`: for independent sets
  `S`, `T`, `S ⊕ Q`, `T ⊕ Q` with `Q ⊆ S ⊕ T`,
  `h_{S ⊕ Q} h_{T ⊕ Q} = (-1)^{c(S ∩ Q, T ∩ Q)} h_S h_T`, where `c = crossCount`.
  The identity is a pure reordering of one multiset of Pauli terms: write
  `S ⊕ Q = (S ∖ Q) ∪ (T ∩ Q)` and `T ⊕ Q = (S ∩ Q) ∪ (T ∖ Q)` (this uses
  `Q ⊆ S ⊕ T`), factor each product with `independentProduct_union`, and swap the two
  middle blocks once with `independentProduct_mul_independentProduct`.
  It holds for an arbitrary `PauliFrustrationRepresentation` over an arbitrary ring: no
  relation `h_j² = b_j²` and no conjugation (in particular no anti-Hermitian operator
  `h_O` with `h_O h_O^† = B² I` as in the v1 text) is used.
* `PauliFrustrationRepresentation.labelingOperator_mul_toggle_raw`: the labelling-level
  form.  If the colour classes of the even-hole labellings `L₁`, `M₁` are obtained from
  those of `L`, `M` by toggling `Q₁` in the `a`-classes and `Q₂` in the `b`-classes
  (with `Q₁ ⊆ L_a ⊕ M_a`, `Q₂ ⊆ L_b ⊕ M_b`), then
  `h_{L₁} h_{M₁} = (-1)^{e} h_L h_M` for the explicit exponent
  `e = c(L₁_b, M₁_a) + c(L_b, M_a) + c(L_a ∩ Q₁, M_a ∩ Q₁) + c(L_b ∩ Q₂, M_b ∩ Q₂)`,
  with `h_L = h_{L_a} h_{L_b}` (`labelingOperator`, v1 L313).  It applies the toggle
  identity to each of the two colour-class pairs and reorders the middle factors.

v1 numbering: v1 labels the Theorem 1(iii) cancellation argument at L1203-1241.
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- Toggle identity for independent products (v1 L1203-1211, the reordering `h_C h_O h_O h_C'`;
it generalises the Theorem 1(i) toggle of v1 L897-899): if `S`, `T`, `S ⊕ Q`, `T ⊕ Q` are
independent and `Q ⊆ S ⊕ T`, then
`h_{S ⊕ Q} h_{T ⊕ Q} = (-1)^{c(S ∩ Q, T ∩ Q)} h_S h_T`.  Valid for every
`PauliFrustrationRepresentation` over every ring; no relation `h_j² = b_j²` is used. -/
theorem independentProduct_toggle_mul [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {S T Q : Finset V} (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hS' : G.IsIndepSet ((symmDiff S Q : Finset V) : Set V))
    (hT' : G.IsIndepSet ((symmDiff T Q : Finset V) : Set V))
    (hQ : Q ⊆ symmDiff S T) :
    H.independentProduct (symmDiff S Q) * H.independentProduct (symmDiff T Q) =
      (-1 : A) ^ G.crossCount (S ∩ Q) (T ∩ Q) *
        (H.independentProduct S * H.independentProduct T) := by
  have hmem : ∀ v ∈ Q, (v ∈ S ∧ v ∉ T) ∨ (v ∈ T ∧ v ∉ S) := by
    intro v hv
    have := hQ hv
    simp only [Finset.mem_symmDiff] at this
    exact this
  have hX : G.IsIndepSet ((S ∩ Q : Finset V) : Set V) :=
    IsIndepSet.finset_subset hS Finset.inter_subset_left
  have hY : G.IsIndepSet ((T ∩ Q : Finset V) : Set V) :=
    IsIndepSet.finset_subset hT Finset.inter_subset_left
  have e1 : S = (S \ Q) ∪ (S ∩ Q) := by
    ext v; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have e2 : T = (T ∩ Q) ∪ (T \ Q) := by
    ext v; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have e3 : symmDiff S Q = (S \ Q) ∪ (T ∩ Q) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · rcases hmem v h.1 with h' | h'
        · exact absurd h'.1 h.2
        · exact Or.inr ⟨h'.1, h.1⟩
    · rintro (h | h)
      · exact Or.inl h
      · rcases hmem v h.2 with h' | h'
        · exact absurd h.1 h'.2
        · exact Or.inr ⟨h.2, h'.2⟩
  have e4 : symmDiff T Q = (S ∩ Q) ∪ (T \ Q) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · rcases hmem v h.1 with h' | h'
        · exact Or.inl ⟨h'.1, h.1⟩
        · exact absurd h'.1 h.2
    · rintro (h | h)
      · rcases hmem v h.2 with h' | h'
        · exact Or.inr ⟨h.2, h'.2⟩
        · exact absurd h.1 h'.2
      · exact Or.inl h
  have d1 : Disjoint (S \ Q) (S ∩ Q) := by
    rw [Finset.disjoint_left]; intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hv').2
  have d2 : Disjoint (T ∩ Q) (T \ Q) := by
    rw [Finset.disjoint_left]; intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have d3 : Disjoint (S \ Q) (T ∩ Q) := by
    rw [Finset.disjoint_left]; intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hv').2
  have d4 : Disjoint (S ∩ Q) (T \ Q) := by
    rw [Finset.disjoint_left]; intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have hS1 : H.independentProduct S =
      H.independentProduct (S \ Q) * H.independentProduct (S ∩ Q) := by
    conv_lhs => rw [e1]
    exact H.independentProduct_union d1 (e1 ▸ hS)
  have hT1 : H.independentProduct T =
      H.independentProduct (T ∩ Q) * H.independentProduct (T \ Q) := by
    conv_lhs => rw [e2]
    exact H.independentProduct_union d2 (e2 ▸ hT)
  have hS2 : H.independentProduct (symmDiff S Q) =
      H.independentProduct (S \ Q) * H.independentProduct (T ∩ Q) := by
    conv_lhs => rw [e3]
    exact H.independentProduct_union d3 (e3 ▸ hS')
  have hT2 : H.independentProduct (symmDiff T Q) =
      H.independentProduct (S ∩ Q) * H.independentProduct (T \ Q) := by
    conv_lhs => rw [e4]
    exact H.independentProduct_union d4 (e4 ▸ hT')
  have hswap := H.independentProduct_mul_independentProduct hY hX
  rw [G.crossCount_comm (T ∩ Q) (S ∩ Q)] at hswap
  rw [hS1, hT1, hS2, hT2]
  have hc := neg_one_pow_commute (A := A) (G.crossCount (S ∩ Q) (T ∩ Q))
    (H.independentProduct (S \ Q))
  calc H.independentProduct (S \ Q) * H.independentProduct (T ∩ Q) *
        (H.independentProduct (S ∩ Q) * H.independentProduct (T \ Q))
      = H.independentProduct (S \ Q) *
          (H.independentProduct (T ∩ Q) * H.independentProduct (S ∩ Q)) *
          H.independentProduct (T \ Q) := by simp only [mul_assoc]
    _ = H.independentProduct (S \ Q) *
          ((-1 : A) ^ G.crossCount (S ∩ Q) (T ∩ Q) *
            (H.independentProduct (S ∩ Q) * H.independentProduct (T ∩ Q))) *
          H.independentProduct (T \ Q) := by rw [hswap]
    _ = (-1 : A) ^ G.crossCount (S ∩ Q) (T ∩ Q) *
          (H.independentProduct (S \ Q) * H.independentProduct (S ∩ Q) *
            (H.independentProduct (T ∩ Q) * H.independentProduct (T \ Q))) := by
          rw [← mul_assoc (H.independentProduct (S \ Q)), ← hc.eq]
          simp only [mul_assoc]

/-- Labelling-level toggle identity (bare representation).  Let `L₁`, `M₁` be even-hole
labellings whose `a`-classes are those of `L`, `M` toggled by `Q₁ ⊆ L_a ⊕ M_a` and whose
`b`-classes are those of `L`, `M` toggled by `Q₂ ⊆ L_b ⊕ M_b`.  Then, with
`h_L = h_{L_a} h_{L_b}` (v1 L313),
`h_{L₁} h_{M₁} = (-1)^e h_L h_M` where
`e = c(L₁_b, M₁_a) + c(L_b, M_a) + c(L_a ∩ Q₁, M_a ∩ Q₁) + c(L_b ∩ Q₂, M_b ∩ Q₂)`.
This is the raw form (v1 L1203-1241): the exponent is left unsimplified, and the proof is the
toggle identity `independentProduct_toggle_mul` on each colour class together with one
reordering of the middle factors on each side. -/
theorem labelingOperator_mul_toggle_raw [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {k k' : ℕ} (L L₁ : G.EvenHoleLabeling k) (M M₁ : G.EvenHoleLabeling k')
    (Q₁ Q₂ : Finset V)
    (ha : Finset.univ.image L₁.a = symmDiff (Finset.univ.image L.a) Q₁)
    (ha' : Finset.univ.image M₁.a = symmDiff (Finset.univ.image M.a) Q₁)
    (hb : Finset.univ.image L₁.b = symmDiff (Finset.univ.image L.b) Q₂)
    (hb' : Finset.univ.image M₁.b = symmDiff (Finset.univ.image M.b) Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff (Finset.univ.image L.a) (Finset.univ.image M.a))
    (hQ₂ : Q₂ ⊆ symmDiff (Finset.univ.image L.b) (Finset.univ.image M.b)) :
    H.labelingOperator L₁ * H.labelingOperator M₁ =
      (-1 : A) ^ (G.crossCount (Finset.univ.image L₁.b) (Finset.univ.image M₁.a) +
          G.crossCount (Finset.univ.image L.b) (Finset.univ.image M.a) +
          G.crossCount (Finset.univ.image L.a ∩ Q₁) (Finset.univ.image M.a ∩ Q₁) +
          G.crossCount (Finset.univ.image L.b ∩ Q₂) (Finset.univ.image M.b ∩ Q₂)) *
        (H.labelingOperator L * H.labelingOperator M) := by
  set La := Finset.univ.image L.a
  set Lb := Finset.univ.image L.b
  set Ma := Finset.univ.image M.a
  set Mb := Finset.univ.image M.b
  set L1a := Finset.univ.image L₁.a
  set L1b := Finset.univ.image L₁.b
  set M1a := Finset.univ.image M₁.a
  set M1b := Finset.univ.image M₁.b
  have iLa : G.IsIndepSet (La : Set V) := L.isIndepSet_image_a
  have iLb : G.IsIndepSet (Lb : Set V) := L.isIndepSet_image_b
  have iMa : G.IsIndepSet (Ma : Set V) := M.isIndepSet_image_a
  have iMb : G.IsIndepSet (Mb : Set V) := M.isIndepSet_image_b
  have iL1a : G.IsIndepSet (L1a : Set V) := L₁.isIndepSet_image_a
  have iL1b : G.IsIndepSet (L1b : Set V) := L₁.isIndepSet_image_b
  have iM1a : G.IsIndepSet (M1a : Set V) := M₁.isIndepSet_image_a
  have iM1b : G.IsIndepSet (M1b : Set V) := M₁.isIndepSet_image_b
  -- toggles of the two class pairs (package T3A-S1)
  have t1 : H.independentProduct L1a * H.independentProduct M1a =
      (-1 : A) ^ G.crossCount (La ∩ Q₁) (Ma ∩ Q₁) *
        (H.independentProduct La * H.independentProduct Ma) := by
    rw [ha, ha']
    exact H.independentProduct_toggle_mul iLa iMa (ha ▸ iL1a) (ha' ▸ iM1a) hQ₁
  have t2 : H.independentProduct L1b * H.independentProduct M1b =
      (-1 : A) ^ G.crossCount (Lb ∩ Q₂) (Mb ∩ Q₂) *
        (H.independentProduct Lb * H.independentProduct Mb) := by
    rw [hb, hb']
    exact H.independentProduct_toggle_mul iLb iMb (hb ▸ iL1b) (hb' ▸ iM1b) hQ₂
  have s1 := H.independentProduct_mul_independentProduct iL1b iM1a
  have s0 := H.independentProduct_mul_independentProduct iLb iMa
  have hc : ∀ (n : ℕ) (x : A), (-1 : A) ^ n * x = x * (-1 : A) ^ n :=
    fun n x => (neg_one_pow_commute n x).eq
  have hsq : ∀ n : ℕ, (-1 : A) ^ n * (-1 : A) ^ n = 1 := by
    intro n; rw [← pow_add, ← two_mul, pow_mul]; simp
  unfold labelingOperator
  -- reorder the middle factors of both sides
  have lhs : H.independentProduct L1a * H.independentProduct L1b *
      (H.independentProduct M1a * H.independentProduct M1b) =
      (-1 : A) ^ G.crossCount L1b M1a *
        ((H.independentProduct L1a * H.independentProduct M1a) *
          (H.independentProduct L1b * H.independentProduct M1b)) := by
    calc H.independentProduct L1a * H.independentProduct L1b *
          (H.independentProduct M1a * H.independentProduct M1b)
        = H.independentProduct L1a * (H.independentProduct L1b * H.independentProduct M1a) *
            H.independentProduct M1b := by simp only [mul_assoc]
      _ = H.independentProduct L1a * ((-1 : A) ^ G.crossCount L1b M1a *
            (H.independentProduct M1a * H.independentProduct L1b)) *
            H.independentProduct M1b := by rw [s1]
      _ = _ := by
            rw [← mul_assoc (H.independentProduct L1a), ← hc]
            simp only [mul_assoc]
  have rhs : H.independentProduct La * H.independentProduct Lb *
      (H.independentProduct Ma * H.independentProduct Mb) =
      (-1 : A) ^ G.crossCount Lb Ma *
        ((H.independentProduct La * H.independentProduct Ma) *
          (H.independentProduct Lb * H.independentProduct Mb)) := by
    calc H.independentProduct La * H.independentProduct Lb *
          (H.independentProduct Ma * H.independentProduct Mb)
        = H.independentProduct La * (H.independentProduct Lb * H.independentProduct Ma) *
            H.independentProduct Mb := by simp only [mul_assoc]
      _ = H.independentProduct La * ((-1 : A) ^ G.crossCount Lb Ma *
            (H.independentProduct Ma * H.independentProduct Lb)) *
            H.independentProduct Mb := by rw [s0]
      _ = _ := by
            rw [← mul_assoc (H.independentProduct La), ← hc]
            simp only [mul_assoc]
  rw [lhs, t1, t2, rhs]
  -- pure sign bookkeeping
  set a := G.crossCount L1b M1a
  set b := G.crossCount Lb Ma
  set c1 := G.crossCount (La ∩ Q₁) (Ma ∩ Q₁)
  set c2 := G.crossCount (Lb ∩ Q₂) (Mb ∩ Q₂)
  set X := H.independentProduct La * H.independentProduct Ma
  set Y := H.independentProduct Lb * H.independentProduct Mb
  have step1 : (-1 : A) ^ a * ((-1 : A) ^ c1 * X * ((-1 : A) ^ c2 * Y)) =
      (-1 : A) ^ (a + (c1 + c2)) * (X * Y) := by
    have : X * ((-1 : A) ^ c2 * Y) = (-1 : A) ^ c2 * (X * Y) := by
      rw [← mul_assoc, ← hc c2 X, mul_assoc]
    rw [mul_assoc ((-1 : A) ^ c1), this, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add,
      add_assoc]
  have step2 : (-1 : A) ^ (a + b + c1 + c2) * ((-1 : A) ^ b * (X * Y)) =
      (-1 : A) ^ (a + (c1 + c2)) * (X * Y) := by
    rw [← mul_assoc, ← pow_add]
    have e : a + b + c1 + c2 + b = (a + (c1 + c2)) + 2 * b := by ring
    rw [e, pow_add, pow_mul]
    simp
  rw [step1, step2]

end PauliFrustrationRepresentation

end SimpleGraph
