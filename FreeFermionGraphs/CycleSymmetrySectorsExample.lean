import FreeFermionGraphs.CycleSymmetrySectors

/-!
# Non-vacuity of `CycleSymmetrySectors`: the 4-cycle with a simplicial mode

`CycleSymmetrySectors` turns the commuting Hermitian cycle symmetries `J_{⟨C₀⟩}` of a
simplicial-mode Hamiltonian into joint eigenprojections `Π_l` and `ModeSector`s.  This module
checks that the hypotheses are satisfiable on a model where `J` genuinely acts, i.e. is neither
`0` nor a scalar, so that there are several sectors and each `Π_l` is a proper projection.

## The model

* `G = c4`, the 4-cycle on `Fin 4` (claw-free, with the even hole `{0, 1, 2, 3}`), and the
  simplicial clique `Ks = {0, 1}` (an edge; the external neighbours `3` of `0` and `2` of `1` form
  trivial cliques).
* Three qubits, `A = Matrix (Fin 8) (Fin 8) ℂ`, with basis label `a = a₀ + 2 a₁ + 4 a₂`, and
  Pauli operators `X_i`, `Z_i` acting on bit `i` (`xOp`, `zOp`, with integer entries).  The terms are

  `h₀ = Z₀ Z₁,  h₁ = X₀ Z₁,  h₂ = Z₀,  h₃ = X₀ Z₂,  χ = X₁`

  (couplings `b_j = 1`).  Adjacent vertices of `G⁺ = G.adjoinRootAt Ks` anticommute and
  non-adjacent ones commute: `h₀ h₁`, `h₁ h₂`, `h₂ h₃`, `h₃ h₀` anticommute, `h₀ h₂`, `h₁ h₃`
  commute, and `χ = X₁` anticommutes with `h₀`, `h₁` and commutes with `h₂`, `h₃`.  Two qubits
  would not be enough for `J` to act non-trivially: the relations of `G⁺` have irreducible
  representations of dimension 4 (the Gram matrix of the anticommutation graph has rank 4 over
  `𝔽₂`), in which `J = h₀ h₂ h₁ h₃` is central, hence a scalar.  The third qubit realises the
  two inequivalent irreducible representations, `J = +1` and `J = -1`.
* The only even hole of `G` is `C = {0, 1, 2, 3}`; its deformation class is `{C}` (no vertex
  outside `C` to clone), so `J_{⟨C⟩} = h_C = h₀ h₂ h₁ h₃ = Z₂`, with eigenvalues `±1` of
  multiplicity 4.  This is the `J = ±1` splitting of the `C₄` counterexample of v1 Theorem 2.

All matrix identities are decided on the integer matrices (by kernel evaluation, `decide +kernel`)
and transported to `ℂ` by the ring homomorphism `Int.castRingHom ℂ`.

## Main declarations

* `CycleSymmetrySectorsExample.ham` : the `SimplicialModeHamiltonian` of the model.
* `c4_isClawFree`, `c4_isSimplicialClique`, `ham_cycleSymmetriesCommute` : the hypotheses of
  `exists_modeSectors_of_cycleSymmetry_commute`.
* `cycleSymmetry_eq` : `J_{⟨C⟩} = Z₂` (so `J ≠ 0`, `J ≠` scalar: `cycleSymmetry_not_scalar`).
* `exists_two_sectors` : the conclusion of `exists_modeSectors_of_cycleSymmetry_commute` holds with
  at least two sectors, each `Π_l` is neither `0` nor `1`, the eigenvalues of `J` on the sectors
  are `+1` and `-1` (both occur), and every `Π_l` is the projection of a `ModeSector` with the
  sector polynomials `z_{∅,l}`, `z_{Ks,l}`.
-/

universe u

namespace SimpleGraph

namespace CycleSymmetrySectorsExample

/-! ### The graph and the simplicial clique -/

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
def c4 : SimpleGraph (Fin 4) where
  Adj i j := CyclicAdjacent i j
  symm := ⟨fun _ _ h => CyclicAdjacent.symm h⟩
  loopless := ⟨fun i h => by
    unfold CyclicAdjacent at h
    omega⟩

instance : DecidableRel c4.Adj := fun i j => by
  show Decidable (CyclicAdjacent i j)
  unfold CyclicAdjacent
  infer_instance

/-- The simplicial clique `Ks = {0, 1}`. -/
def Ks : Set (Fin 4) := {j | j.val < 2}

set_option synthInstance.maxSize 1024 in
theorem c4_isClawFree : c4.IsClawFree := by
  have h : ∀ center a b c : Fin 4, c4.Adj center a → c4.Adj center b → c4.Adj center c →
      a ≠ b → a ≠ c → b ≠ c → c4.Adj a b ∨ c4.Adj a c ∨ c4.Adj b c := by decide
  exact fun center a b c => h center a b c

theorem c4_isSimplicialClique : c4.IsSimplicialClique Ks := by
  have h1 : ∀ x y : Fin 4, x.val < 2 → y.val < 2 → x ≠ y → c4.Adj x y := by decide
  have h2 : ∀ j x y : Fin 4, j.val < 2 → c4.Adj j x → ¬ x.val < 2 → c4.Adj j y →
      ¬ y.val < 2 → x ≠ y → c4.Adj x y := by decide
  refine ⟨fun x hx y hy hxy => h1 x y hx hy hxy, fun j hj x hx y hy hxy => ?_⟩
  exact h2 j x y hj hx.1 hx.2 hy.1 hy.2 hxy

/-! ### The Pauli matrices -/

/-- Pauli `X` on qubit `i` of three qubits: `a ↦ a ⊕ 2^i`. -/
def xOp (i : ℕ) : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun a b => if a.val = b.val ^^^ 2 ^ i then 1 else 0

/-- Pauli `Z` on qubit `i` of three qubits: the sign `(-1)^{a_i}`. -/
def zOp (i : ℕ) : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.diagonal fun a => if a.val.testBit i then -1 else 1

/-- The terms `h_j` (`j ∈ Fin 4`) and the simplicial mode `χ` (the root, `none`) with integer
entries. -/
def M : Option (Fin 4) → Matrix (Fin 8) (Fin 8) ℤ
  | some 0 => zOp 0 * zOp 1
  | some 1 => xOp 0 * zOp 1
  | some 2 => zOp 0
  | some 3 => xOp 0 * zOp 2
  | none => xOp 1

/-- Adjacency of `G⁺ = c4.adjoinRootAt Ks` as a Boolean function. -/
def adjB : Option (Fin 4) → Option (Fin 4) → Bool
  | some i, some j => decide (c4.Adj i j)
  | none, some j => decide (j.val < 2)
  | some i, none => decide (i.val < 2)
  | none, none => false

theorem M_mul_self : ∀ v, M v * M v = 1 := by decide +kernel

theorem M_transpose : ∀ v, Matrix.transpose (M v) = M v := by decide +kernel

theorem M_anticomm : ∀ j k, adjB j k = true → M j * M k = -(M k * M j) := by decide +kernel

theorem M_comm : ∀ j k, adjB j k = false → M j * M k = M k * M j := by decide +kernel

theorem M_not_anticomm : ∀ j k, adjB j k = false → M j * M k ≠ -(M k * M j) := by
  decide +kernel

/-- `h₀ h₂ h₁ h₃ = Z₂`: the cycle symmetry of the hole `{0, 1, 2, 3}`. -/
theorem M_cycle : M (some 0) * M (some 2) * (M (some 1) * M (some 3)) = zOp 2 := by
  decide +kernel

theorem adjB_iff : ∀ j k, (c4.adjoinRootAt Ks).Adj j k ↔ adjB j k = true := by
  intro j k
  rcases j with _ | j <;> rcases k with _ | k
  · simp [adjB]
  · simp [adjB, adjoinRootAt_adj_none_some, Ks]
  · simp [adjB, adjoinRootAt_adj_some_none, Ks]
  · simp [adjB]

/-- Transport from integer matrices to complex matrices. -/
def φ : Matrix (Fin 8) (Fin 8) ℤ →+* Matrix (Fin 8) (Fin 8) ℂ :=
  (Int.castRingHom ℂ).mapMatrix

theorem φ_injective : Function.Injective φ := by
  intro A B h
  have h' : A.map (Int.cast : ℤ → ℂ) = B.map (Int.cast : ℤ → ℂ) := h
  exact Matrix.map_injective Int.cast_injective h'

theorem isSelfAdjoint_φ {m : Matrix (Fin 8) (Fin 8) ℤ} (h : Matrix.transpose m = m) :
    IsSelfAdjoint (φ m) := by
  show Matrix.conjTranspose (φ m) = φ m
  ext i j
  have h' : m j i = m i j := congrFun (congrFun h i) j
  simp [Matrix.conjTranspose_apply, φ, h']

/-! ### The Hamiltonian -/

/-- The Pauli frustration representation of `G⁺` by the matrices `φ (M v)`. -/
def rep : (c4.adjoinRootAt Ks).PauliFrustrationRepresentation (Matrix (Fin 8) (Fin 8) ℂ) where
  term v := φ (M v)
  adj_iff_anticommute := by
    intro j k
    rw [← map_mul, ← map_mul, ← map_neg, φ_injective.eq_iff, adjB_iff]
    constructor
    · exact M_anticomm j k
    · intro h
      by_contra hb
      exact M_not_anticomm j k (by simpa using hb) h
  commute_of_not_adj := by
    intro j k h
    have hb : adjB j k = false := by simpa [adjB_iff] using h
    rw [← map_mul, ← map_mul, M_comm j k hb]

/-- **The model**: a simplicial-mode Hamiltonian on three qubits whose frustration graph is the
4-cycle, with simplicial clique `{0, 1}`, couplings `b_j = 1` and simplicial mode `χ = X₁`. -/
def ham : c4.SimplicialModeHamiltonian Ks (Matrix (Fin 8) (Fin 8) ℂ) where
  operator := rep
  coupling := fun _ => 1
  original_term_sq := by
    intro j
    show φ (M (some j)) * φ (M (some j)) = _
    rw [← map_mul, M_mul_self]
    simp
  term_selfAdjoint := fun v => isSelfAdjoint_φ (M_transpose v)
  root_sq := by
    show φ (M none) * φ (M none) = 1
    rw [← map_mul, M_mul_self]
    exact map_one φ

theorem ham_term (v : Option (Fin 4)) : ham.operator.term v = φ (M v) := rfl

/-! ### Even holes and the cycle symmetry -/

/-- The set of all four vertices is an even-hole carrier of the 4-cycle. -/
theorem isEvenHoleCarrier_univ : c4.IsEvenHoleCarrier Set.univ :=
  ⟨{ card := 4
     four_le_card := le_rfl
     vertex := id
     injective := Function.injective_id
     adj_iff := fun _ _ => Iff.rfl }, ⟨2, rfl⟩, by simp⟩

/-- Every even-hole carrier of the 4-cycle is the whole vertex set. -/
theorem eq_univ_of_isEvenHoleCarrier {C : Set (Fin 4)} (hC : c4.IsEvenHoleCarrier C) :
    C = Set.univ := by
  obtain ⟨H, -, rfl⟩ := hC
  have h1 : (Set.range H.vertex).ncard = H.card := ncard_range_fin_of_injective _ H.injective
  have h2 : (Set.univ : Set (Fin 4)).ncard = 4 := by simp
  have h3 := H.four_le_card
  exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by omega) (Set.toFinite _)

/-- The deformation closure of the full vertex set is itself: a deformation step needs a clone
`s` outside the carrier of a labelling. -/
theorem eq_univ_of_inClosure_univ {V : Type u} {G : SimpleGraph V} {B : Set V}
    (h : InEvenHoleDeformationClosure G Set.univ B) : B = Set.univ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    obtain ⟨k, L, s, i, hcl, ⟨hB, hC⟩ | ⟨hB, hC⟩⟩ := hstep
    · exact absurd (hB ▸ Set.mem_univ s) hcl.outside
    · exfalso
      have hmem : L.a i ∈ L.deformedCarrier s i := hB ▸ Set.mem_univ _
      rcases hmem with h | ⟨-, h⟩
      · exact hcl.outside (h ▸ L.a_mem_carrier i)
      · exact h rfl

theorem deformationClosureFinset_univ :
    c4.deformationClosureFinset Set.univ = {Set.univ} := by
  ext C
  rw [mem_deformationClosureFinset, Finset.mem_singleton]
  constructor
  · exact eq_univ_of_inClosure_univ
  · rintro rfl
    exact InEvenHoleDeformationClosure.refl _

theorem independentProduct_pair {a b : Fin 4} (hab : a ≠ b) (h : ¬ c4.Adj a b) :
    ham.frustration.independentProduct {a, b} =
      ham.frustration.term a * ham.frustration.term b := by
  have hb : ham.frustration.independentProduct {b} = ham.frustration.term b := by
    rw [ham.frustration.independentProduct_eq_noncommProd (by simp)]
    exact Finset.noncommProd_singleton b ham.frustration.term
  rw [ham.frustration.independentProduct_insert_left (by simpa using hab) (by simp)
    (by simpa using h), hb]

/-- **`J_{⟨C⟩} = Z₂`** for the unique even hole `C = {0, 1, 2, 3}` of the 4-cycle: the class
`⟨C⟩ = {C}` has the single member `C`, `h_C = h₀ h₂ h₁ h₃` for the colour classes `{0, 2}`,
`{1, 3}`, and the product of the four matrices is `Z₂`. -/
theorem cycleSymmetry_eq :
    ham.frustration.generalizedCycleSymmetryOp Set.univ = φ (zOp 2) := by
  unfold PauliFrustrationRepresentation.generalizedCycleSymmetryOp generalizedCycleSymmetry
  rw [deformationClosureFinset_univ, Finset.sum_singleton]
  have hcov : (((({0, 2} : Finset (Fin 4)) : Set (Fin 4))) ∪
      (({1, 3} : Finset (Fin 4)) : Set (Fin 4))) = Set.univ := by
    ext x
    fin_cases x <;> simp
  have hd : Disjoint ({0, 2} : Finset (Fin 4)) {1, 3} := by decide
  have ha : c4.IsIndepSet ((({0, 2} : Finset (Fin 4)) : Set (Fin 4))) := by
    have h : ∀ x y : Fin 4, x ∈ ({0, 2} : Finset (Fin 4)) → y ∈ ({0, 2} : Finset (Fin 4)) →
        x ≠ y → ¬ c4.Adj x y := by decide
    exact fun x hx y hy hxy => h x y hx hy hxy
  have hb : c4.IsIndepSet ((({1, 3} : Finset (Fin 4)) : Set (Fin 4))) := by
    have h : ∀ x y : Fin 4, x ∈ ({1, 3} : Finset (Fin 4)) → y ∈ ({1, 3} : Finset (Fin 4)) →
        x ≠ y → ¬ c4.Adj x y := by decide
    exact fun x hx y hy hxy => h x y hx hy hxy
  rw [(ham.frustration.evenHoleOperator_eq_of_colouring isEvenHoleCarrier_univ hcov hd ha hb).1,
    independentProduct_pair (by decide) (by decide),
    independentProduct_pair (by decide) (by decide)]
  show φ (M (some 0)) * φ (M (some 2)) * (φ (M (some 1)) * φ (M (some 3))) = φ (zOp 2)
  rw [← map_mul, ← map_mul, ← map_mul, M_cycle]

/-- The hypothesis `[J, J'] = 0` holds in the model: the only even-hole carrier is
`{0, 1, 2, 3}`, so there is a single hole class and a single nonzero cycle symmetry. -/
theorem ham_cycleSymmetriesCommute : ham.frustration.CycleSymmetriesCommute := by
  intro C₀ C₁ h₀ h₁
  rw [eq_univ_of_isEvenHoleCarrier h₀, eq_univ_of_isEvenHoleCarrier h₁]
  exact Commute.refl _

/-- `J_{⟨C⟩} = Z₂` is not a scalar matrix: its diagonal entries at `0` and `4` are `1` and `-1`.
Hence the joint eigenprojections of the model have at least two sectors. -/
theorem cycleSymmetry_not_scalar (c : ℂ) :
    ham.frustration.generalizedCycleSymmetryOp Set.univ ≠ c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  intro h
  rw [cycleSymmetry_eq] at h
  have h0 := congrFun (congrFun h 0) 0
  have h4 := congrFun (congrFun h 4) 4
  have e0 : (zOp 2) 0 0 = 1 := by decide
  have e4 : (zOp 2) 4 4 = -1 := by decide
  simp only [φ, RingHom.mapMatrix_apply, Matrix.map_apply, e0, e4, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0 h4
  rw [← h0] at h4
  norm_num at h4

/-- `J_{⟨C⟩}² = 1` (`Z₂² = 1`). -/
theorem cycleSymmetry_mul_self :
    ham.frustration.generalizedCycleSymmetryOp Set.univ *
      ham.frustration.generalizedCycleSymmetryOp Set.univ = 1 := by
  rw [cycleSymmetry_eq, ← map_mul]
  have : zOp 2 * zOp 2 = 1 := by decide +kernel
  rw [this]
  exact map_one φ

/-- The only hole class of the model is the class of `{0, 1, 2, 3}`. -/
theorem eq_classOf_univ_of_isEvenHoleClass {κ : c4.EvenHoleDeformationClass}
    (h : c4.IsEvenHoleClass κ) : κ = c4.evenHoleDeformationClassOf Set.univ := by
  obtain ⟨C₀, hC₀, rfl⟩ := h
  rw [eq_univ_of_isEvenHoleCarrier hC₀]

/-- **Non-vacuity of `exists_modeSectors_of_cycleSymmetry_commute`.**  For the model `ham` (a
simplicial-mode Hamiltonian on three qubits with frustration graph the 4-cycle, claw-free, with
simplicial clique `{0, 1}`, whose cycle symmetry `J = Z₂` genuinely acts), the hypotheses of the
theorem hold (`c4_isClawFree`, `c4_isSimplicialClique`, `ham_cycleSymmetriesCommute`), and its
conclusion holds with two sectors: there are sector projections `Π_l` (`l ∈ Λ`), none of them `0`
or `1`, with `∑ Π_l = 1` and `J Π_l = l(⟨C⟩) Π_l`, and the eigenvalues `l(⟨C⟩)` are `±1`, both
occurring (`J² = 1`, `J` not a scalar).  Every `Π_l` is the projection of a `ModeSector` with the
sector polynomials `z_{∅,l}`, `z_{Ks,l}`. -/
theorem exists_two_sectors :
    ∃ (Λ : Finset (c4.EvenHoleDeformationClass → ℝ))
      (Pi : (c4.EvenHoleDeformationClass → ℝ) → Matrix (Fin 8) (Fin 8) ℂ),
      2 ≤ Λ.card ∧
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0 ∧ Pi l ≠ 1) ∧
      ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
          ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1 ∨
        l (c4.evenHoleDeformationClassOf Set.univ) = -1) ∧
      (∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1) ∧
      (∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = -1) ∧
      (∀ l ∈ Λ, ∃ S : ham.ModeSector, S.Pi = Pi l ∧
        S.zG = c4.sectorPolynomial ham.coupling ∅ l ∧
        S.zK = c4.sectorPolynomial ham.coupling Ks l) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, -, -, h8⟩ :=
    ham.exists_modeSectors_of_cycleSymmetry_commute c4_isClawFree c4_isSimplicialClique
      ham_cycleSymmetriesCommute
  have h4' : ∀ l ∈ Λ, ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
      ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) • Pi l :=
    fun l hl => h4 l hl Set.univ isEvenHoleCarrier_univ
  -- the eigenvalues are `±1` since `J² = 1`
  have hpm : ∀ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1 ∨
      l (c4.evenHoleDeformationClassOf Set.univ) = -1 := by
    intro l hl
    have e : Pi l = (((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) *
        ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ)) • Pi l := by
      calc Pi l = (ham.frustration.generalizedCycleSymmetryOp Set.univ *
            ham.frustration.generalizedCycleSymmetryOp Set.univ) * Pi l := by
              rw [cycleSymmetry_mul_self, one_mul]
        _ = ham.frustration.generalizedCycleSymmetryOp Set.univ *
            (ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l) := mul_assoc _ _ _
        _ = _ := by
              rw [h4' l hl, Matrix.mul_smul, h4' l hl, smul_smul]
    have e' : (((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) *
        ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) - 1) • Pi l = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    have hcc := sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right (h1 l hl).2.2)
    have hcc' : l (c4.evenHoleDeformationClassOf Set.univ) *
        l (c4.evenHoleDeformationClassOf Set.univ) = 1 := by exact_mod_cast hcc
    exact mul_self_eq_one_iff.1 hcc'
  -- there are two distinct sectors, because `J` is not a scalar
  have hcard : 1 < Λ.card := by
    rw [Finset.one_lt_card]
    by_contra hcon
    push Not at hcon
    have hne : Λ.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at h3
      exact zero_ne_one h3
    obtain ⟨l₀, hl₀⟩ := hne
    have hsing : Λ = {l₀} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hl₀, fun x hx => hcon x hx l₀ hl₀⟩
    rw [hsing, Finset.sum_singleton] at h3
    have h := h4' l₀ hl₀
    rw [h3, mul_one] at h
    exact cycleSymmetry_not_scalar _ h
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.1 hcard
  -- distinct sectors have distinct eigenvalues: the junk coordinates vanish
  have hval : l (c4.evenHoleDeformationClassOf Set.univ) ≠
      m (c4.evenHoleDeformationClassOf Set.univ) := by
    intro heq
    apply hlm
    funext κ
    by_cases hκ : c4.IsEvenHoleClass κ
    · rw [eq_classOf_univ_of_isEvenHoleClass hκ]
      exact heq
    · rw [h5 l hl κ hκ, h5 m hm κ hκ]
  refine ⟨Λ, Pi, hcard, fun l hl => ⟨(h1 l hl).1, (h1 l hl).2.1, (h1 l hl).2.2, ?_⟩, h3, h4', hpm,
    ?_, ?_, h8⟩
  · intro hone
    obtain ⟨m', hm', hlm'⟩ := Finset.exists_mem_ne hcard l
    have := h2 l hl m' hm' (Ne.symm hlm')
    rw [hone, one_mul] at this
    exact (h1 m' hm').2.2 this
  · rcases hpm l hl with h | h
    · exact ⟨l, hl, h⟩
    · rcases hpm m hm with h' | h'
      · exact ⟨m, hm, h'⟩
      · exact absurd (h.trans h'.symm) hval
  · rcases hpm l hl with h | h
    · rcases hpm m hm with h' | h'
      · exact absurd (h.trans h'.symm) hval
      · exact ⟨m, hm, h'⟩
    · exact ⟨l, hl, h⟩

end CycleSymmetrySectorsExample

end SimpleGraph
