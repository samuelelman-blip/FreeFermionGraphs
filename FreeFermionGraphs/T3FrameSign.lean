import FreeFermionGraphs.T3HoleClassRun
import FreeFermionGraphs.T3ToggleProduct

/-!
# Frame sign lemma: commutation signs of hole operators under simultaneous class toggles

This module formalises the sign bookkeeping in the proof of cancellation in the proof of
Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, L1203-1241: the relations
`h_C h_{C'} = σ h_{C'} h_C` and `h_{C~} h_{C~'} = σ h_{C~'} h_{C~}`, and the three-line
reordering display L1218-1220), at the level of *hole classes* (pairs `s = (C_a, C_b)` of the two
colouring classes of an even hole, `SimpleGraph.IsHoleClasses`, v1 Eq. `equation:evenholelabel`,
L313).  The hole operator is `h_C = h_{C_a} h_{C_b}` (v1 L313).

## Main results

* `PauliFrustrationRepresentation.evenHoleOperator_holeClasses`: `h_C = h_{s.1} h_{s.2}` for the
  carrier `C = s.1 ∪ s.2` of a hole-class state `s` (v1 L313).
* `PauliFrustrationRepresentation.evenHoleOperator_mul_evenHoleOperator_holeClasses`: for hole
  classes `s`, `s'` with carriers `C`, `C'`,
  `h_C h_{C'} = (-1)^{c(C, C')} h_{C'} h_C`, where `c = crossCount` (the number of edges between
  `C` and `C'`).  This is the closed form of the sign `σ` of v1 L1203-1241.
* `PauliFrustrationRepresentation.commutator_toggle_holeClasses` (the **frame sign lemma**): let
  `s`, `s'`, `t`, `t'` be hole classes with `t.i = s.i ⊕ Q_i`, `t'.i = s'.i ⊕ Q_i` and
  `Q_i ⊆ s.i ⊕ s'.i` (`i = 1, 2`).  Then
  `[h_{carrier t}, h_{carrier t'}] = (-1)^{c(Q₁ ⊕ Q₂, C)} [h_C, h_{C'}]`.
  This is the closed-form version of v1's three-line display (L1218-1220), in which the scale
  factors of the manuscript are not needed: no relation `h_j² = b_j²`, no anticommutation
  hypothesis, no claw-freeness and no conjugation by `h_O` is used, and the result holds for any
  `PauliFrustrationRepresentation` over any ring.
* `PauliFrustrationRepresentation.evenHoleOperator_mul_toggle_holeClasses`: the product form
  `h_{carrier t} h_{carrier t'} = (-1)^{c(Q₁ ⊕ Q₂, C)} h_C h_{C'}` of the same hypotheses; the
  commutator identity is its difference with the reversed product.
* `PauliFrustrationRepresentation.independentProduct_holeClasses_mul_toggle_raw`: the raw form
  `(h_{t.1} h_{t.2})(h_{t'.1} h_{t'.2}) = (-1)^e (h_{s.1} h_{s.2})(h_{s'.1} h_{s'.2})` with the
  explicit unsimplified exponent `e`; it is the `EvenHoleLabeling` identity
  `labelingOperator_mul_toggle_raw` restated for hole classes.  (That identity needs the labellings
  of `s` and `t` to have the same length `k`; hole classes carry no such information, so the
  class-level form is proved here by the same reordering argument.)
* `SimpleGraph.IsHoleClasses.toggle_exponent_mod_two`,
  `SimpleGraph.IsHoleClasses.crossCount_toggle_mod_two` and
  `SimpleGraph.IsHoleClasses.crossCount_toggle_mod_two_symm`: the raw exponent `e` and the
  exponent `c(Q₁ ⊕ Q₂, C)` are, modulo `2`, both the cross count `c(Y, Z)` of the vertices `Y`
  leaving `s` and the vertices `Z` leaving `s'`; in particular the exponent is symmetric in `C`
  and `C'`: `c(Q₁ ⊕ Q₂, C) ≡ c(Q₁ ⊕ Q₂, C')` (mod `2`).

The mod-`2` reduction of the exponent uses only that every vertex of a hole has an even number
(namely `2` or `0`) of neighbours in each of the two colouring classes of the hole.  It is applied
to the four holes `s`, `s'`, `t`, `t'`.

v1 numbering: the cancellation argument is v1 L1203-1241 (proof of Theorem 1(iii)); v1 does not
number its sign relation, and its remark that the scale factors cancel upon conjugating by `h_O²`
is not needed here.
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Parity calculus for `crossCount` -/

/-- Additivity of the cross count modulo `2` in both arguments under symmetric difference. -/
theorem crossCount_symmDiff_symmDiff_mod_two [DecidableEq V] (X X' Y Y' : Finset V) :
    G.crossCount (symmDiff X X') (symmDiff Y Y') % 2 =
      (G.crossCount X Y + G.crossCount X Y' + G.crossCount X' Y + G.crossCount X' Y') % 2 := by
  have h1 := G.crossCount_symmDiff_left_mod_two (symmDiff Y Y') X X'
  have h2 := G.crossCount_symmDiff_right_mod_two X Y Y'
  have h3 := G.crossCount_symmDiff_right_mod_two X' Y Y'
  omega

/-- Modulo `2`, the cross count is trilinear in the form `X ⊕ (X₁ ⊕ X₂)`, `Y ⊕ (Y₁ ⊕ Y₂)`. -/
theorem crossCount_symmDiff_symmDiff₃_mod_two [DecidableEq V] (X X₁ X₂ Y Y₁ Y₂ : Finset V) :
    G.crossCount (symmDiff X (symmDiff X₁ X₂)) (symmDiff Y (symmDiff Y₁ Y₂)) % 2 =
      (G.crossCount X Y + G.crossCount X Y₁ + G.crossCount X Y₂ +
        G.crossCount X₁ Y + G.crossCount X₁ Y₁ + G.crossCount X₁ Y₂ +
        G.crossCount X₂ Y + G.crossCount X₂ Y₁ + G.crossCount X₂ Y₂) % 2 := by
  have h1 := G.crossCount_symmDiff_symmDiff_mod_two X (symmDiff X₁ X₂) Y (symmDiff Y₁ Y₂)
  have h2 := G.crossCount_symmDiff_right_mod_two X Y₁ Y₂
  have h3 := G.crossCount_symmDiff_left_mod_two Y X₁ X₂
  have h4 := G.crossCount_symmDiff_symmDiff_mod_two X₁ X₂ Y₁ Y₂
  omega

/-- Additivity of the cross count in the first argument over a disjoint union. -/
theorem crossCount_union_left [DecidableEq V] {X Y Z : Finset V} (h : Disjoint X Y) :
    G.crossCount (X ∪ Y) Z = G.crossCount X Z + G.crossCount Y Z := by
  rw [crossCount_comm, crossCount_union_right h, crossCount_comm Z X, crossCount_comm Z Y]

/-- Two subsets of an independent finset are joined by no edge. -/
theorem crossCount_eq_zero_of_isIndepSet {S X Y : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hX : X ⊆ S) (hY : Y ⊆ S) : G.crossCount X Y = 0 := by
  classical
  rw [crossCount_eq_card_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hp hadj
  have hxy := Finset.mem_product.1 hp
  exact hS (Finset.mem_coe.mpr (hX hxy.1)) (Finset.mem_coe.mpr (hY hxy.2)) hadj.ne hadj

/-! ### Even neighbour counts in a hole -/

/-- In an independent finset, a vertex of the finset has no neighbour in it. -/
theorem IsIndepSet.filter_adj_eq_empty [DecidableRel G.Adj] {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) {v : V} (hv : v ∈ S) : S.filter (G.Adj v) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro y hy hadj
  exact hS (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hy) hadj.ne hadj

section HoleClasses

variable [DecidableEq V] {s : Finset V × Finset V}

/-- Every vertex of the carrier of a hole-class state has an even number (`0` or `2`) of
neighbours in the first class. -/
theorem IsHoleClasses.card_filter_fst_mod_two [DecidableRel G.Adj] (hs : G.IsHoleClasses s)
    {v : V} (hv : v ∈ s.1 ∪ s.2) : (s.1.filter (G.Adj v)).card % 2 = 0 := by
  obtain ⟨k, L, -, h1, h2⟩ := hs
  rw [← h1, ← h2] at hv
  rw [← h1]
  have hvC : v ∈ L.carrier := by
    rw [← L.coe_image_a_union_image_b]; exact Finset.mem_coe.mpr hv
  have h2c := L.adjacencyCount_eq_two_of_mem_carrier hvC
  rw [L.adjacencyCount_carrier_eq] at h2c
  rcases Finset.mem_union.mp hv with ha | hb
  · rw [IsIndepSet.filter_adj_eq_empty L.isIndepSet_image_a ha]; rfl
  · rw [IsIndepSet.filter_adj_eq_empty L.isIndepSet_image_b hb, Finset.card_empty] at h2c
    omega

/-- Every vertex of the carrier of a hole-class state has an even number (`0` or `2`) of
neighbours in the second class. -/
theorem IsHoleClasses.card_filter_snd_mod_two [DecidableRel G.Adj] (hs : G.IsHoleClasses s)
    {v : V} (hv : v ∈ s.1 ∪ s.2) : (s.2.filter (G.Adj v)).card % 2 = 0 := by
  obtain ⟨k, L, -, h1, h2⟩ := hs
  rw [← h1, ← h2] at hv
  rw [← h2]
  have hvC : v ∈ L.carrier := by
    rw [← L.coe_image_a_union_image_b]; exact Finset.mem_coe.mpr hv
  have h2c := L.adjacencyCount_eq_two_of_mem_carrier hvC
  rw [L.adjacencyCount_carrier_eq] at h2c
  rcases Finset.mem_union.mp hv with ha | hb
  · rw [IsIndepSet.filter_adj_eq_empty L.isIndepSet_image_a ha, Finset.card_empty] at h2c
    omega
  · rw [IsIndepSet.filter_adj_eq_empty L.isIndepSet_image_b hb]; rfl

/-- A set of vertices of the carrier of a hole-class state sends an even number of edges to the
first class. -/
theorem IsHoleClasses.crossCount_fst_mod_two (hs : G.IsHoleClasses s) {X : Finset V}
    (hX : X ⊆ s.1 ∪ s.2) : G.crossCount X s.1 % 2 = 0 := by
  classical
  rw [crossCount_eq_sum_card_filter, Finset.sum_nat_mod]
  rw [Finset.sum_eq_zero fun x hx => hs.card_filter_fst_mod_two (hX hx)]
  rfl

/-- A set of vertices of the carrier of a hole-class state sends an even number of edges to the
second class. -/
theorem IsHoleClasses.crossCount_snd_mod_two (hs : G.IsHoleClasses s) {X : Finset V}
    (hX : X ⊆ s.1 ∪ s.2) : G.crossCount X s.2 % 2 = 0 := by
  classical
  rw [crossCount_eq_sum_card_filter, Finset.sum_nat_mod]
  rw [Finset.sum_eq_zero fun x hx => hs.card_filter_snd_mod_two (hX hx)]
  rfl

end HoleClasses

/-! ### Reduction of the toggle exponent modulo `2` -/

section Toggle

variable [DecidableEq V]

/-- A subset `Q` of `a ⊕ a'` is the symmetric difference (here the disjoint union) of its parts in
`a` and in `a'`. -/
theorem eq_symmDiff_inter_of_subset_symmDiff {a a' Q : Finset V} (h : Q ⊆ symmDiff a a') :
    Q = symmDiff (a ∩ Q) (a' ∩ Q) := by
  ext v
  have hv : v ∈ Q → (v ∈ a ∧ v ∉ a') ∨ (v ∈ a' ∧ v ∉ a) := fun hvQ => by
    have := h hvQ
    rwa [Finset.mem_symmDiff] at this
  simp only [Finset.mem_symmDiff, Finset.mem_inter]
  constructor
  · intro hvQ
    rcases hv hvQ with h1 | h1
    · exact Or.inl ⟨⟨h1.1, hvQ⟩, fun h2 => h1.2 h2.1⟩
    · exact Or.inr ⟨⟨h1.1, hvQ⟩, fun h2 => h1.2 h2.1⟩
  · rintro (h1 | h1)
    · exact h1.1.2
    · exact h1.1.2

/-- The part of `Q ⊆ a ⊕ a'` lying in `a'` is contained in the toggled set `a ⊕ Q`. -/
theorem inter_subset_symmDiff_of_subset_symmDiff {a a' Q : Finset V} (h : Q ⊆ symmDiff a a') :
    a' ∩ Q ⊆ symmDiff a Q := by
  intro v hv
  rw [Finset.mem_inter] at hv
  have := h hv.2
  rw [Finset.mem_symmDiff] at this ⊢
  rcases this with h1 | h1
  · exact absurd hv.1 h1.2
  · exact Or.inr ⟨hv.2, h1.2⟩

/-- Modulo `2`, the toggle exponent of the raw identity reduces to the cross count `c(Y, Z)` of the
vertices `Y = Y₁ ∪ Y₂` leaving the first hole and `Z = Z₁ ∪ Z₂` leaving the second one.  Abstract
form, with the first hole `(a, b)`, the second hole `(a', b')`, the toggled first hole
`(a ⊕ (Y₁ ⊕ Z₁), b ⊕ (Y₂ ⊕ Z₂))` and the toggled second hole
`(a' ⊕ (Y₁ ⊕ Z₁), b' ⊕ (Y₂ ⊕ Z₂))`: the four hypotheses say that `Y₁ ⊆ a`, `Z₂ ⊆ b'`,
`Z₁` (in the first class of the toggled first hole) and `Y₂` (in the second class of the toggled
second hole) send an even number of edges to the indicated class, which is the statement that a
hole sends an even number of edges from each of its vertices to each of its classes. -/
theorem toggle_exponent_aux {b a' Y₁ Y₂ Z₁ Z₂ : Finset V}
    (hY₁ : G.crossCount Y₁ b % 2 = 0) (hZ₂ : G.crossCount Z₂ a' % 2 = 0)
    (hC : G.crossCount Z₁ (symmDiff b (symmDiff Y₂ Z₂)) % 2 = 0)
    (hD : G.crossCount Y₂ (symmDiff a' (symmDiff Y₁ Z₁)) % 2 = 0)
    (hY : Disjoint Y₁ Y₂) (hZ : Disjoint Z₁ Z₂) :
    (G.crossCount (symmDiff b (symmDiff Y₂ Z₂)) (symmDiff a' (symmDiff Y₁ Z₁)) +
        G.crossCount b a' + G.crossCount Y₁ Z₁ + G.crossCount Y₂ Z₂) % 2 =
      G.crossCount (Y₁ ∪ Y₂) (Z₁ ∪ Z₂) % 2 := by
  have e := G.crossCount_symmDiff_symmDiff₃_mod_two b Y₂ Z₂ a' Y₁ Z₁
  have eC1 := G.crossCount_symmDiff_right_mod_two Z₁ b (symmDiff Y₂ Z₂)
  have eC2 := G.crossCount_symmDiff_right_mod_two Z₁ Y₂ Z₂
  have eD1 := G.crossCount_symmDiff_right_mod_two Y₂ a' (symmDiff Y₁ Z₁)
  have eD2 := G.crossCount_symmDiff_right_mod_two Y₂ Y₁ Z₁
  have u : G.crossCount (Y₁ ∪ Y₂) (Z₁ ∪ Z₂) =
      G.crossCount Y₁ Z₁ + G.crossCount Y₁ Z₂ + (G.crossCount Y₂ Z₁ + G.crossCount Y₂ Z₂) := by
    rw [crossCount_union_left hY, crossCount_union_right hZ, crossCount_union_right hZ]
  have c1 := G.crossCount_comm b Y₁
  have c2 := G.crossCount_comm b Z₁
  have c3 := G.crossCount_comm Y₂ Z₁
  have c4 := G.crossCount_comm Z₂ Z₁
  have c5 := G.crossCount_comm Z₂ Y₁
  omega

/-- Modulo `2`, the cross count of the toggle `Q₁ ⊕ Q₂` with the carrier `a ∪ b` equals the cross
count `c(Y, Z)` of the vertices leaving the first hole with those leaving the second one.
Abstract form: `Y₁, Y₂` lie in the carrier `a ∪ b`, and `Z₁, Z₂` lie in the two classes of the
toggled hole `t₁ = a ⊕ (Y₁ ⊕ Z₁)`, `t₂ = b ⊕ (Y₂ ⊕ Z₂)`. -/
theorem toggle_frame_aux {a b Y₁ Y₂ Z₁ Z₂ : Finset V}
    (hY₁a : G.crossCount Y₁ a % 2 = 0) (hY₁b : G.crossCount Y₁ b % 2 = 0)
    (hY₂a : G.crossCount Y₂ a % 2 = 0) (hY₂b : G.crossCount Y₂ b % 2 = 0)
    (h11 : G.crossCount Z₁ (symmDiff a (symmDiff Y₁ Z₁)) % 2 = 0)
    (h12 : G.crossCount Z₁ (symmDiff b (symmDiff Y₂ Z₂)) % 2 = 0)
    (h21 : G.crossCount Z₂ (symmDiff a (symmDiff Y₁ Z₁)) % 2 = 0)
    (h22 : G.crossCount Z₂ (symmDiff b (symmDiff Y₂ Z₂)) % 2 = 0)
    (hZ₁ : G.crossCount Z₁ Z₁ = 0) (hZ₂ : G.crossCount Z₂ Z₂ = 0)
    (hab : Disjoint a b) (hY : Disjoint Y₁ Y₂) (hZ : Disjoint Z₁ Z₂) :
    G.crossCount (symmDiff (symmDiff Y₁ Z₁) (symmDiff Y₂ Z₂)) (a ∪ b) % 2 =
      G.crossCount (Y₁ ∪ Y₂) (Z₁ ∪ Z₂) % 2 := by
  have l1 := G.crossCount_union_right (A := symmDiff (symmDiff Y₁ Z₁) (symmDiff Y₂ Z₂)) hab
  have l2 := G.crossCount_symmDiff_left_mod_two a (symmDiff Y₁ Z₁) (symmDiff Y₂ Z₂)
  have l3 := G.crossCount_symmDiff_left_mod_two b (symmDiff Y₁ Z₁) (symmDiff Y₂ Z₂)
  have l4 := G.crossCount_symmDiff_left_mod_two a Y₁ Z₁
  have l5 := G.crossCount_symmDiff_left_mod_two a Y₂ Z₂
  have l6 := G.crossCount_symmDiff_left_mod_two b Y₁ Z₁
  have l7 := G.crossCount_symmDiff_left_mod_two b Y₂ Z₂
  have e11 := G.crossCount_symmDiff_right_mod_two Z₁ a (symmDiff Y₁ Z₁)
  have e11' := G.crossCount_symmDiff_right_mod_two Z₁ Y₁ Z₁
  have e12 := G.crossCount_symmDiff_right_mod_two Z₁ b (symmDiff Y₂ Z₂)
  have e12' := G.crossCount_symmDiff_right_mod_two Z₁ Y₂ Z₂
  have e21 := G.crossCount_symmDiff_right_mod_two Z₂ a (symmDiff Y₁ Z₁)
  have e21' := G.crossCount_symmDiff_right_mod_two Z₂ Y₁ Z₁
  have e22 := G.crossCount_symmDiff_right_mod_two Z₂ b (symmDiff Y₂ Z₂)
  have e22' := G.crossCount_symmDiff_right_mod_two Z₂ Y₂ Z₂
  have u : G.crossCount (Y₁ ∪ Y₂) (Z₁ ∪ Z₂) =
      G.crossCount Y₁ Z₁ + G.crossCount Y₁ Z₂ + (G.crossCount Y₂ Z₁ + G.crossCount Y₂ Z₂) := by
    rw [crossCount_union_left hY, crossCount_union_right hZ, crossCount_union_right hZ]
  have c1 := G.crossCount_comm Z₁ Y₁
  have c2 := G.crossCount_comm Z₂ Y₁
  have c3 := G.crossCount_comm Z₁ Y₂
  have c4 := G.crossCount_comm Z₂ Y₂
  have c5 := G.crossCount_comm Z₁ Z₂
  have c6 := G.crossCount_comm Z₁ a
  have c7 := G.crossCount_comm Z₂ a
  have c8 := G.crossCount_comm Z₁ b
  have c9 := G.crossCount_comm Z₂ b
  omega

end Toggle

/-! ### Exponent lemmas for hole classes -/

section HoleToggle

variable [DecidableEq V] {s s' t t' : Finset V × Finset V} {Q₁ Q₂ : Finset V}

/-- The toggle exponent of the raw identity (`c(t₂, t'₁) + c(s₂, s'₁) + c(s₁ ∩ Q₁, s'₁ ∩ Q₁) +
c(s₂ ∩ Q₂, s'₂ ∩ Q₂)`, see `independentProduct_holeClasses_mul_toggle_raw`) is, modulo `2`, the
cross count `c(Y, Z)` of the vertices `Y = (s₁ ∩ Q₁) ∪ (s₂ ∩ Q₂)` leaving `s` and
`Z = (s'₁ ∩ Q₁) ∪ (s'₂ ∩ Q₂)` leaving `s'`.  The proof uses only that every vertex of one of the
four holes `s`, `s'`, `t`, `t'` has an even number of neighbours in each of its two classes. -/
theorem IsHoleClasses.toggle_exponent_mod_two (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (ht : G.IsHoleClasses t) (ht' : G.IsHoleClasses t')
    (h₁ : t.1 = symmDiff s.1 Q₁) (h₂ : t.2 = symmDiff s.2 Q₂)
    (h₁' : t'.1 = symmDiff s'.1 Q₁) (h₂' : t'.2 = symmDiff s'.2 Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff s.1 s'.1) (hQ₂ : Q₂ ⊆ symmDiff s.2 s'.2) :
    (G.crossCount t.2 t'.1 + G.crossCount s.2 s'.1 +
        G.crossCount (s.1 ∩ Q₁) (s'.1 ∩ Q₁) + G.crossCount (s.2 ∩ Q₂) (s'.2 ∩ Q₂)) % 2 =
      G.crossCount (s.1 ∩ Q₁ ∪ s.2 ∩ Q₂) (s'.1 ∩ Q₁ ∪ s'.2 ∩ Q₂) % 2 := by
  have hQ₁' := eq_symmDiff_inter_of_subset_symmDiff hQ₁
  have hQ₂' := eq_symmDiff_inter_of_subset_symmDiff hQ₂
  have ht2 : t.2 = symmDiff s.2 (symmDiff (s.2 ∩ Q₂) (s'.2 ∩ Q₂)) := by rw [h₂, ← hQ₂']
  have ht1' : t'.1 = symmDiff s'.1 (symmDiff (s.1 ∩ Q₁) (s'.1 ∩ Q₁)) := by rw [h₁', ← hQ₁']
  have hQ₁c : Q₁ ⊆ symmDiff s'.1 s.1 := by rwa [symmDiff_comm]
  have hQ₂c : Q₂ ⊆ symmDiff s'.2 s.2 := by rwa [symmDiff_comm]
  -- `Z₁ = s'₁ ∩ Q₁` lies in the first class of `t`; `Y₂ = s₂ ∩ Q₂` in the second class of `t'`
  have hZ₁ : s'.1 ∩ Q₁ ⊆ t.1 ∪ t.2 := fun v hv =>
    Finset.mem_union_left _ (by rw [h₁]; exact inter_subset_symmDiff_of_subset_symmDiff hQ₁ hv)
  have hY₂ : s.2 ∩ Q₂ ⊆ t'.1 ∪ t'.2 := fun v hv =>
    Finset.mem_union_right _ (by rw [h₂']; exact inter_subset_symmDiff_of_subset_symmDiff hQ₂c hv)
  have key := toggle_exponent_aux (b := s.2) (a' := s'.1) (Y₁ := s.1 ∩ Q₁) (Y₂ := s.2 ∩ Q₂)
    (Z₁ := s'.1 ∩ Q₁) (Z₂ := s'.2 ∩ Q₂)
    (hs.crossCount_snd_mod_two (Finset.inter_subset_left.trans Finset.subset_union_left))
    (hs'.crossCount_fst_mod_two (Finset.inter_subset_left.trans Finset.subset_union_right))
    (by rw [← ht2]; exact ht.crossCount_snd_mod_two hZ₁)
    (by rw [← ht1']; exact ht'.crossCount_fst_mod_two hY₂)
    (hs.disjoint.mono Finset.inter_subset_left Finset.inter_subset_left)
    (hs'.disjoint.mono Finset.inter_subset_left Finset.inter_subset_left)
  rw [← ht2, ← ht1'] at key
  exact key

/-- **Frame exponent, modulo `2`.**  For hole classes `s`, `s'`, `t` with `t.i = s.i ⊕ Q_i` and
`Q_i ⊆ s.i ⊕ s'.i`, the cross count of the toggle `Q₁ ⊕ Q₂` with the carrier `C = s.1 ∪ s.2` is,
modulo `2`, the cross count `c(Y, Z)` of the vertices `Y = (s₁ ∩ Q₁) ∪ (s₂ ∩ Q₂)` leaving `s` and
`Z = (s'₁ ∩ Q₁) ∪ (s'₂ ∩ Q₂)` leaving `s'`.  (Vertices of `Q₁ ∩ Q₂` lie in all four holes and
contribute evenly.) -/
theorem IsHoleClasses.crossCount_toggle_mod_two (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (ht : G.IsHoleClasses t)
    (h₁ : t.1 = symmDiff s.1 Q₁) (h₂ : t.2 = symmDiff s.2 Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff s.1 s'.1) (hQ₂ : Q₂ ⊆ symmDiff s.2 s'.2) :
    G.crossCount (symmDiff Q₁ Q₂) (s.1 ∪ s.2) % 2 =
      G.crossCount (s.1 ∩ Q₁ ∪ s.2 ∩ Q₂) (s'.1 ∩ Q₁ ∪ s'.2 ∩ Q₂) % 2 := by
  have hQ₁' := eq_symmDiff_inter_of_subset_symmDiff hQ₁
  have hQ₂' := eq_symmDiff_inter_of_subset_symmDiff hQ₂
  have e : symmDiff Q₁ Q₂ = symmDiff (symmDiff (s.1 ∩ Q₁) (s'.1 ∩ Q₁))
      (symmDiff (s.2 ∩ Q₂) (s'.2 ∩ Q₂)) := by rw [← hQ₁', ← hQ₂']
  have ht1 : t.1 = symmDiff s.1 (symmDiff (s.1 ∩ Q₁) (s'.1 ∩ Q₁)) := by rw [h₁, ← hQ₁']
  have ht2 : t.2 = symmDiff s.2 (symmDiff (s.2 ∩ Q₂) (s'.2 ∩ Q₂)) := by rw [h₂, ← hQ₂']
  have hZ₁ : s'.1 ∩ Q₁ ⊆ t.1 ∪ t.2 := fun v hv =>
    Finset.mem_union_left _ (by rw [h₁]; exact inter_subset_symmDiff_of_subset_symmDiff hQ₁ hv)
  have hZ₂ : s'.2 ∩ Q₂ ⊆ t.1 ∪ t.2 := fun v hv =>
    Finset.mem_union_right _ (by rw [h₂]; exact inter_subset_symmDiff_of_subset_symmDiff hQ₂ hv)
  have hY₁ : s.1 ∩ Q₁ ⊆ s.1 ∪ s.2 := Finset.inter_subset_left.trans Finset.subset_union_left
  have hY₂ : s.2 ∩ Q₂ ⊆ s.1 ∪ s.2 := Finset.inter_subset_left.trans Finset.subset_union_right
  rw [e]
  refine toggle_frame_aux (hs.crossCount_fst_mod_two hY₁) (hs.crossCount_snd_mod_two hY₁)
    (hs.crossCount_fst_mod_two hY₂) (hs.crossCount_snd_mod_two hY₂)
    (by rw [← ht1]; exact ht.crossCount_fst_mod_two hZ₁)
    (by rw [← ht2]; exact ht.crossCount_snd_mod_two hZ₁)
    (by rw [← ht1]; exact ht.crossCount_fst_mod_two hZ₂)
    (by rw [← ht2]; exact ht.crossCount_snd_mod_two hZ₂)
    (crossCount_eq_zero_of_isIndepSet hs'.isIndepSet_fst Finset.inter_subset_left
      Finset.inter_subset_left)
    (crossCount_eq_zero_of_isIndepSet hs'.isIndepSet_snd Finset.inter_subset_left
      Finset.inter_subset_left)
    hs.disjoint
    (hs.disjoint.mono Finset.inter_subset_left Finset.inter_subset_left)
    (hs'.disjoint.mono Finset.inter_subset_left Finset.inter_subset_left)

/-- **Symmetry of the frame exponent.**  Modulo `2`, the cross count of the toggle `Q₁ ⊕ Q₂` with
the carrier `C = s.1 ∪ s.2` equals its cross count with the carrier `C' = s'.1 ∪ s'.2`; both are
the cross count `c(Y, Z)` of `crossCount_toggle_mod_two`. -/
theorem IsHoleClasses.crossCount_toggle_mod_two_symm (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (ht : G.IsHoleClasses t) (ht' : G.IsHoleClasses t')
    (h₁ : t.1 = symmDiff s.1 Q₁) (h₂ : t.2 = symmDiff s.2 Q₂)
    (h₁' : t'.1 = symmDiff s'.1 Q₁) (h₂' : t'.2 = symmDiff s'.2 Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff s.1 s'.1) (hQ₂ : Q₂ ⊆ symmDiff s.2 s'.2) :
    G.crossCount (symmDiff Q₁ Q₂) (s.1 ∪ s.2) % 2 =
      G.crossCount (symmDiff Q₁ Q₂) (s'.1 ∪ s'.2) % 2 := by
  have hQ₁c : Q₁ ⊆ symmDiff s'.1 s.1 := by rwa [symmDiff_comm]
  have hQ₂c : Q₂ ⊆ symmDiff s'.2 s.2 := by rwa [symmDiff_comm]
  have e1 := hs.crossCount_toggle_mod_two hs' ht h₁ h₂ hQ₁ hQ₂
  have e2 := hs'.crossCount_toggle_mod_two hs ht' h₁' h₂' hQ₁c hQ₂c
  rw [e1, e2, crossCount_comm]

end HoleToggle

end SimpleGraph

/-! ### Operators -/

namespace SimpleGraph

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A] [DecidableEq V]

/-- Moving one independent-set product across a product of two others (v1 L887-891, applied
twice): `h_S (h_T h_U) = (-1)^{c(S,T) + c(S,U)} (h_T h_U) h_S`. -/
theorem independentProduct_mul_pair (H : G.PauliFrustrationRepresentation A) {S T U : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hU : G.IsIndepSet (U : Set V)) :
    H.independentProduct S * (H.independentProduct T * H.independentProduct U) =
      (-1 : A) ^ (G.crossCount S T + G.crossCount S U) *
        (H.independentProduct T * H.independentProduct U * H.independentProduct S) := by
  have h1 := H.independentProduct_mul_independentProduct hS hT
  have h2 := H.independentProduct_mul_independentProduct hS hU
  have hc := fun (n : ℕ) (x : A) => (neg_one_pow_commute n x).eq
  calc H.independentProduct S * (H.independentProduct T * H.independentProduct U)
      = (H.independentProduct S * H.independentProduct T) * H.independentProduct U :=
        (mul_assoc _ _ _).symm
    _ = ((-1 : A) ^ G.crossCount S T * (H.independentProduct T * H.independentProduct S)) *
          H.independentProduct U := by rw [h1]
    _ = (-1 : A) ^ G.crossCount S T *
          (H.independentProduct T * (H.independentProduct S * H.independentProduct U)) := by
        simp only [mul_assoc]
    _ = (-1 : A) ^ G.crossCount S T *
          (H.independentProduct T * ((-1 : A) ^ G.crossCount S U *
            (H.independentProduct U * H.independentProduct S))) := by rw [h2]
    _ = (-1 : A) ^ G.crossCount S T * ((-1 : A) ^ G.crossCount S U *
          (H.independentProduct T * (H.independentProduct U * H.independentProduct S))) := by
        rw [← mul_assoc (H.independentProduct T), ← hc, mul_assoc]
    _ = (-1 : A) ^ (G.crossCount S T + G.crossCount S U) *
          (H.independentProduct T * H.independentProduct U * H.independentProduct S) := by
        rw [pow_add, mul_assoc, mul_assoc]

/-- Moving a product of two independent-set products across another one:
`(h_{S₁} h_{S₂})(h_{T₁} h_{T₂}) = (-1)^{c(S₁,T₁) + c(S₁,T₂) + c(S₂,T₁) + c(S₂,T₂)}
(h_{T₁} h_{T₂})(h_{S₁} h_{S₂})`. -/
theorem independentProduct_pair_mul_pair (H : G.PauliFrustrationRepresentation A)
    {S₁ S₂ T₁ T₂ : Finset V} (hS₁ : G.IsIndepSet (S₁ : Set V)) (hS₂ : G.IsIndepSet (S₂ : Set V))
    (hT₁ : G.IsIndepSet (T₁ : Set V)) (hT₂ : G.IsIndepSet (T₂ : Set V)) :
    H.independentProduct S₁ * H.independentProduct S₂ *
        (H.independentProduct T₁ * H.independentProduct T₂) =
      (-1 : A) ^ (G.crossCount S₁ T₁ + G.crossCount S₁ T₂ +
          (G.crossCount S₂ T₁ + G.crossCount S₂ T₂)) *
        (H.independentProduct T₁ * H.independentProduct T₂ *
          (H.independentProduct S₁ * H.independentProduct S₂)) := by
  have h1 := H.independentProduct_mul_pair hS₁ hT₁ hT₂
  have h2 := H.independentProduct_mul_pair hS₂ hT₁ hT₂
  have hc := fun (n : ℕ) (x : A) => (neg_one_pow_commute n x).eq
  set X := H.independentProduct T₁ * H.independentProduct T₂ with hX
  calc H.independentProduct S₁ * H.independentProduct S₂ * X
      = H.independentProduct S₁ * (H.independentProduct S₂ * X) := mul_assoc _ _ _
    _ = H.independentProduct S₁ * ((-1 : A) ^ (G.crossCount S₂ T₁ + G.crossCount S₂ T₂) *
          (X * H.independentProduct S₂)) := by rw [h2]
    _ = (-1 : A) ^ (G.crossCount S₂ T₁ + G.crossCount S₂ T₂) *
          (H.independentProduct S₁ * X * H.independentProduct S₂) := by
        rw [← mul_assoc (H.independentProduct S₁), ← hc, mul_assoc]
        simp only [mul_assoc]
    _ = (-1 : A) ^ (G.crossCount S₂ T₁ + G.crossCount S₂ T₂) *
          ((-1 : A) ^ (G.crossCount S₁ T₁ + G.crossCount S₁ T₂) *
            (X * H.independentProduct S₁) * H.independentProduct S₂) := by rw [h1]
    _ = (-1 : A) ^ (G.crossCount S₁ T₁ + G.crossCount S₁ T₂ +
          (G.crossCount S₂ T₁ + G.crossCount S₂ T₂)) *
        (X * (H.independentProduct S₁ * H.independentProduct S₂)) := by
        rw [mul_assoc ((-1 : A) ^ (G.crossCount S₁ T₁ + G.crossCount S₁ T₂)),
          ← mul_assoc ((-1 : A) ^ (G.crossCount S₂ T₁ + G.crossCount S₂ T₂)),
          (neg_one_pow_commute (G.crossCount S₂ T₁ + G.crossCount S₂ T₂) _).eq]
        simp only [← pow_add, mul_assoc]

/-! ### The hole operator of a hole-class state -/

variable {s s' t t' : Finset V × Finset V} {Q₁ Q₂ : Finset V}

/-- (a) `h_C = h_{C_a} h_{C_b}` for the carrier `C = s.1 ∪ s.2` of a hole-class state `s`
(v1 L313: "We choose the factor ordering for the operator corresponding to `C` as
`h_C = h_{C_a} h_{C_b}`").  Valid for every `PauliFrustrationRepresentation` over every ring. -/
theorem evenHoleOperator_holeClasses (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) :
    H.evenHoleOperator ↑(s.1 ∪ s.2) = H.independentProduct s.1 * H.independentProduct s.2 := by
  obtain ⟨k, L, hL, h1, h2⟩ := hs
  rw [← h1, ← h2, L.coe_image_a_union_image_b, H.evenHoleOperator_eq L hL]
  rfl

/-- (b) **Commutation sign of two hole operators** (the closed form of the sign `σ` in
`h_C h_{C'} = σ h_{C'} h_C` of v1 L1203-1241): for hole classes `s`, `s'` with carriers
`C = s.1 ∪ s.2`, `C' = s'.1 ∪ s'.2`,
`h_C h_{C'} = (-1)^{c(C, C')} h_{C'} h_C`, where `c(C, C')` is the number of edges between `C`
and `C'`.  The four class products are reordered with
`independentProduct_mul_independentProduct`; no relation `h_j² = b_j²` and no claw-freeness is
used, and the ring is arbitrary. -/
theorem evenHoleOperator_mul_evenHoleOperator_holeClasses (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') :
    H.evenHoleOperator ↑(s.1 ∪ s.2) * H.evenHoleOperator ↑(s'.1 ∪ s'.2) =
      (-1 : A) ^ G.crossCount (s.1 ∪ s.2) (s'.1 ∪ s'.2) *
        (H.evenHoleOperator ↑(s'.1 ∪ s'.2) * H.evenHoleOperator ↑(s.1 ∪ s.2)) := by
  rw [H.evenHoleOperator_holeClasses hs, H.evenHoleOperator_holeClasses hs',
    H.independentProduct_pair_mul_pair hs.isIndepSet_fst hs.isIndepSet_snd
      hs'.isIndepSet_fst hs'.isIndepSet_snd,
    crossCount_union_left hs.disjoint, crossCount_union_right hs'.disjoint,
    crossCount_union_right hs'.disjoint]

/-- **Raw frame identity** (v1 L1218-1220, the reordering `h_C h_O h_O h_{C'}`, for the class
products `h_{t.1} h_{t.2}`): for hole classes `s`, `s'`, `t`, `t'` with `t.i = s.i ⊕ Q_i`,
`t'.i = s'.i ⊕ Q_i`, `Q_i ⊆ s.i ⊕ s'.i`,
`(h_{t.1} h_{t.2}) (h_{t'.1} h_{t'.2}) = (-1)^e (h_{s.1} h_{s.2}) (h_{s'.1} h_{s'.2})` with
`e = c(t.2, t'.1) + c(s.2, s'.1) + c(s.1 ∩ Q₁, s'.1 ∩ Q₁) + c(s.2 ∩ Q₂, s'.2 ∩ Q₂)`.
This is `labelingOperator_mul_toggle_raw` in terms of hole classes; the latter needs the
labellings of `s` and `t` to have the same length, which hole classes do not provide.  The
exponent is reduced modulo `2` by `IsHoleClasses.toggle_exponent_mod_two`. -/
theorem independentProduct_holeClasses_mul_toggle_raw (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (ht : G.IsHoleClasses t)
    (ht' : G.IsHoleClasses t')
    (h₁ : t.1 = symmDiff s.1 Q₁) (h₂ : t.2 = symmDiff s.2 Q₂)
    (h₁' : t'.1 = symmDiff s'.1 Q₁) (h₂' : t'.2 = symmDiff s'.2 Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff s.1 s'.1) (hQ₂ : Q₂ ⊆ symmDiff s.2 s'.2) :
    H.independentProduct t.1 * H.independentProduct t.2 *
        (H.independentProduct t'.1 * H.independentProduct t'.2) =
      (-1 : A) ^ (G.crossCount t.2 t'.1 + G.crossCount s.2 s'.1 +
          G.crossCount (s.1 ∩ Q₁) (s'.1 ∩ Q₁) + G.crossCount (s.2 ∩ Q₂) (s'.2 ∩ Q₂)) *
        (H.independentProduct s.1 * H.independentProduct s.2 *
          (H.independentProduct s'.1 * H.independentProduct s'.2)) := by
  -- toggles of the two class pairs
  have t1 : H.independentProduct t.1 * H.independentProduct t'.1 =
      (-1 : A) ^ G.crossCount (s.1 ∩ Q₁) (s'.1 ∩ Q₁) *
        (H.independentProduct s.1 * H.independentProduct s'.1) := by
    have := H.independentProduct_toggle_mul hs.isIndepSet_fst hs'.isIndepSet_fst
      (by rw [← h₁]; exact ht.isIndepSet_fst) (by rw [← h₁']; exact ht'.isIndepSet_fst) hQ₁
    rwa [← h₁, ← h₁'] at this
  have t2 : H.independentProduct t.2 * H.independentProduct t'.2 =
      (-1 : A) ^ G.crossCount (s.2 ∩ Q₂) (s'.2 ∩ Q₂) *
        (H.independentProduct s.2 * H.independentProduct s'.2) := by
    have := H.independentProduct_toggle_mul hs.isIndepSet_snd hs'.isIndepSet_snd
      (by rw [← h₂]; exact ht.isIndepSet_snd) (by rw [← h₂']; exact ht'.isIndepSet_snd) hQ₂
    rwa [← h₂, ← h₂'] at this
  have s1 := H.independentProduct_mul_independentProduct ht.isIndepSet_snd ht'.isIndepSet_fst
  have s0 := H.independentProduct_mul_independentProduct hs.isIndepSet_snd hs'.isIndepSet_fst
  have hc : ∀ (n : ℕ) (x : A), (-1 : A) ^ n * x = x * (-1 : A) ^ n :=
    fun n x => (neg_one_pow_commute n x).eq
  -- reorder the middle factors of both sides
  have lhs : H.independentProduct t.1 * H.independentProduct t.2 *
      (H.independentProduct t'.1 * H.independentProduct t'.2) =
      (-1 : A) ^ G.crossCount t.2 t'.1 *
        ((H.independentProduct t.1 * H.independentProduct t'.1) *
          (H.independentProduct t.2 * H.independentProduct t'.2)) := by
    calc H.independentProduct t.1 * H.independentProduct t.2 *
          (H.independentProduct t'.1 * H.independentProduct t'.2)
        = H.independentProduct t.1 * (H.independentProduct t.2 * H.independentProduct t'.1) *
            H.independentProduct t'.2 := by simp only [mul_assoc]
      _ = H.independentProduct t.1 * ((-1 : A) ^ G.crossCount t.2 t'.1 *
            (H.independentProduct t'.1 * H.independentProduct t.2)) *
            H.independentProduct t'.2 := by rw [s1]
      _ = _ := by
            rw [← mul_assoc (H.independentProduct t.1), ← hc]
            simp only [mul_assoc]
  have rhs : H.independentProduct s.1 * H.independentProduct s.2 *
      (H.independentProduct s'.1 * H.independentProduct s'.2) =
      (-1 : A) ^ G.crossCount s.2 s'.1 *
        ((H.independentProduct s.1 * H.independentProduct s'.1) *
          (H.independentProduct s.2 * H.independentProduct s'.2)) := by
    calc H.independentProduct s.1 * H.independentProduct s.2 *
          (H.independentProduct s'.1 * H.independentProduct s'.2)
        = H.independentProduct s.1 * (H.independentProduct s.2 * H.independentProduct s'.1) *
            H.independentProduct s'.2 := by simp only [mul_assoc]
      _ = H.independentProduct s.1 * ((-1 : A) ^ G.crossCount s.2 s'.1 *
            (H.independentProduct s'.1 * H.independentProduct s.2)) *
            H.independentProduct s'.2 := by rw [s0]
      _ = _ := by
            rw [← mul_assoc (H.independentProduct s.1), ← hc]
            simp only [mul_assoc]
  rw [lhs, t1, t2, rhs]
  -- pure sign bookkeeping
  set a := G.crossCount t.2 t'.1
  set b := G.crossCount s.2 s'.1
  set c1 := G.crossCount (s.1 ∩ Q₁) (s'.1 ∩ Q₁)
  set c2 := G.crossCount (s.2 ∩ Q₂) (s'.2 ∩ Q₂)
  set X := H.independentProduct s.1 * H.independentProduct s'.1
  set Y := H.independentProduct s.2 * H.independentProduct s'.2
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

/-- **Frame sign lemma, product form** (v1 L1218-1220, with closed-form sign): for hole classes
`s`, `s'`, `t`, `t'` with `t.i = s.i ⊕ Q_i`, `t'.i = s'.i ⊕ Q_i`, `Q_i ⊆ s.i ⊕ s'.i`,
`h_{carrier t} h_{carrier t'} = (-1)^{c(Q₁ ⊕ Q₂, C)} h_C h_{C'}` with `C = s.1 ∪ s.2`.
The exponent `e` of the raw identity `independentProduct_holeClasses_mul_toggle_raw` is congruent
to `c(Q₁ ⊕ Q₂, C)` modulo `2` (`IsHoleClasses.toggle_exponent_mod_two` and
`IsHoleClasses.crossCount_toggle_mod_two`), so the product identity itself, and not only the
commutator identity `commutator_toggle_holeClasses`, has the closed-form sign. -/
theorem evenHoleOperator_mul_toggle_holeClasses (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (ht : G.IsHoleClasses t)
    (ht' : G.IsHoleClasses t')
    (h₁ : t.1 = symmDiff s.1 Q₁) (h₂ : t.2 = symmDiff s.2 Q₂)
    (h₁' : t'.1 = symmDiff s'.1 Q₁) (h₂' : t'.2 = symmDiff s'.2 Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff s.1 s'.1) (hQ₂ : Q₂ ⊆ symmDiff s.2 s'.2) :
    H.evenHoleOperator ↑(t.1 ∪ t.2) * H.evenHoleOperator ↑(t'.1 ∪ t'.2) =
      (-1 : A) ^ G.crossCount (symmDiff Q₁ Q₂) (s.1 ∪ s.2) *
        (H.evenHoleOperator ↑(s.1 ∪ s.2) * H.evenHoleOperator ↑(s'.1 ∪ s'.2)) := by
  rw [H.evenHoleOperator_holeClasses hs, H.evenHoleOperator_holeClasses hs',
    H.evenHoleOperator_holeClasses ht, H.evenHoleOperator_holeClasses ht',
    H.independentProduct_holeClasses_mul_toggle_raw hs hs' ht ht' h₁ h₂ h₁' h₂' hQ₁ hQ₂,
    neg_one_pow_eq_pow_mod_two (R := A),
    hs.toggle_exponent_mod_two hs' ht ht' h₁ h₂ h₁' h₂' hQ₁ hQ₂,
    ← hs.crossCount_toggle_mod_two hs' ht h₁ h₂ hQ₁ hQ₂,
    ← neg_one_pow_eq_pow_mod_two (R := A)]

/-- **Frame sign lemma** (v1 L1218-1220, closed form): let `s`, `s'`, `t`, `t'` be hole classes
with `t.i = s.i ⊕ Q_i`, `t'.i = s'.i ⊕ Q_i` and `Q_i ⊆ s.i ⊕ s'.i` (`i = 1, 2`), and write
`C = s.1 ∪ s.2`, `C' = s'.1 ∪ s'.2`.  Then
`[h_{carrier t}, h_{carrier t'}] = (-1)^{c(Q₁ ⊕ Q₂, C)} [h_C, h_{C'}]`,
where `c = crossCount` and `[x, y] = x y - y x` is `algebraCommutator`.

The exponent is symmetric in `C` and `C'` modulo `2` (`IsHoleClasses.crossCount_toggle_mod_two_symm`).
The statement holds for every `PauliFrustrationRepresentation` over every ring: no anticommutation
hypothesis, no relation `h_j² = b_j²`, no claw-freeness and no conjugation by `h_O` (the scale
factors of v1 are not needed) is used.  It follows by subtracting the two product identities
`evenHoleOperator_mul_toggle_holeClasses` for `(s, s', t, t')` and `(s', s, t', t)`. -/
theorem commutator_toggle_holeClasses (H : G.PauliFrustrationRepresentation A)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (ht : G.IsHoleClasses t)
    (ht' : G.IsHoleClasses t')
    (h₁ : t.1 = symmDiff s.1 Q₁) (h₂ : t.2 = symmDiff s.2 Q₂)
    (h₁' : t'.1 = symmDiff s'.1 Q₁) (h₂' : t'.2 = symmDiff s'.2 Q₂)
    (hQ₁ : Q₁ ⊆ symmDiff s.1 s'.1) (hQ₂ : Q₂ ⊆ symmDiff s.2 s'.2) :
    algebraCommutator (H.evenHoleOperator ↑(t.1 ∪ t.2)) (H.evenHoleOperator ↑(t'.1 ∪ t'.2)) =
      (-1 : A) ^ G.crossCount (symmDiff Q₁ Q₂) (s.1 ∪ s.2) *
        algebraCommutator (H.evenHoleOperator ↑(s.1 ∪ s.2))
          (H.evenHoleOperator ↑(s'.1 ∪ s'.2)) := by
  have hQ₁c : Q₁ ⊆ symmDiff s'.1 s.1 := by rwa [symmDiff_comm]
  have hQ₂c : Q₂ ⊆ symmDiff s'.2 s.2 := by rwa [symmDiff_comm]
  have p1 := H.evenHoleOperator_mul_toggle_holeClasses hs hs' ht ht' h₁ h₂ h₁' h₂' hQ₁ hQ₂
  have p2 := H.evenHoleOperator_mul_toggle_holeClasses hs' hs ht' ht h₁' h₂' h₁ h₂ hQ₁c hQ₂c
  have hx := hs.crossCount_toggle_mod_two_symm hs' ht ht' h₁ h₂ h₁' h₂' hQ₁ hQ₂
  have hpow : (-1 : A) ^ G.crossCount (symmDiff Q₁ Q₂) (s'.1 ∪ s'.2) =
      (-1 : A) ^ G.crossCount (symmDiff Q₁ Q₂) (s.1 ∪ s.2) := by
    rw [neg_one_pow_eq_pow_mod_two (R := A) (G.crossCount (symmDiff Q₁ Q₂) (s'.1 ∪ s'.2)),
      neg_one_pow_eq_pow_mod_two (R := A) (G.crossCount (symmDiff Q₁ Q₂) (s.1 ∪ s.2)), hx]
  unfold algebraCommutator
  rw [p1, p2, hpow, mul_sub]

end PauliFrustrationRepresentation

end SimpleGraph
