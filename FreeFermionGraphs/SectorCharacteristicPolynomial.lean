import FreeFermionGraphs.GeneralizedCharacteristicPolynomial
import FreeFermionGraphs.HoleSimplicialClique
import FreeFermionGraphs.HoleAttachment

/-!
# Sector form of `Z_G` and `Z_{G∖Ks}`: regrouping into `J_{⟨C₀⟩}` (v1 Lemma 11, last display)

Manuscript reference: arXiv 2305.15625 v1, the last display of the proof of Lemma 11
(`lemma:generalizedcharacteristicpolynomial`, L1979-1982), which regroups the sum over
families of even holes into a sum over sets of deformation classes with factors
`∏ J_{⟨C₀⟩}`, together with the sector restriction `Z_{G,J}(-u²) := Z_G(-u²) Π_J`
(L563-585: "reduces to an ordinary polynomial when restricted to a symmetric subspace") and its
use for `Z_{G∖Ks}` at L2088-2093.

Let `G` be claw-free, `W ∈ {∅, Ks}` with `Ks` a simplicial clique, and `H` a representation.
With `𝒦` ranging over sets of pairwise separated deformation classes of even holes avoiding `W`,
the regrouped form of `T_{G∖W}(u) T_{G∖W}(-u)` is

`Z_{G∖W}(-u²) = ∑_𝒦 (-u²)^{|∂𝒦|/2} 2^{|𝒦|} I_{G∖(W ∪ Γ[𝒦])}(-u²) ∏_{κ ∈ 𝒦} J_κ`,

where the weights depend only on the classes by Lemma 4 (`InEvenHoleDeformationClosure.
openNeighborhood_eq`) and because a deformation step preserves the size of a hole.  If `Π` is a
vector (or operator) with `J_κ Π = λ_κ Π` for every even-hole class `κ`, then
`Z_{G∖W}(-u²) Π = z_{W,λ}(-u²) Π` for the real polynomial `z_{W,λ}` obtained by replacing each
`J_κ` by `λ_κ`.

## Main declarations

* `SimpleGraph.sectorClassFamilies G W` : the sets `𝒦` of deformation classes of even-hole
  carriers avoiding `W` that are pairwise separated (weakly, v1 L313), through the representatives
  `Quotient.out`.
* `SimpleGraph.sectorPolynomial G b W lam` : the polynomial `z_{W,λ}`,
  `∑_𝒦 C(2^{|𝒦|} ∏_{κ ∈ 𝒦} λ_κ) X^{|∂𝒦|/2} I_{G∖(W ∪ Γ[𝒦])}`, with `∂𝒦` the boundary of the
  family of representatives `𝒦.image Quotient.out` and `Γ[𝒦] = ∂𝒦 ∪ N(∂𝒦)`.
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector` :
  `T_{G∖W}(u) T_{G∖W}(-u) Π = z_{W,λ}(-u²) Π` whenever `J_{⟨C₀⟩} Π = λ_{⟨C₀⟩} Π` for every
  even-hole carrier `C₀`.
* `SimpleGraph.PauliFrustrationRepresentation.sum_sectorFibre_familyOperator_mul` : the regrouping
  itself, `(∑_{𝒳 over 𝒦} ∏_{C ∈ 𝒳} h_C) Π = (∏_{κ ∈ 𝒦} λ_κ) Π`: the sum of the family operators
  over the families of class set `𝒦` is the (commuting) product of the `J_κ`, and `J_κ` is applied
  to `Π` one factor at a time.

## Proof

`generalizedCharacteristicPolynomial` writes `T(u) T(-u)` as a sum over families
`𝒳 ∈ 𝒞^{(even)}_{G∖W}`.  Each `𝒳` is sent to its set of deformation classes
(`image_mem_sectorClassFamilies`).  The class map is injective on a family
(`evenHoleDeformationClassOf_injOn_family`: two members of one class are never separated, v1
Corollary 5 and Lemma 4), so `|𝒳| = |𝒦|`, `|∂𝒳| = ∑_{κ ∈ 𝒦} |κ|` and
`Γ[∂𝒳] = ⋃_{κ ∈ 𝒦} Γ[κ]`; hence the weight of `𝒳` depends only on `𝒦`
(`evenHoleFamilies_weight_data_eq`).  The fibre over `𝒦` is built by induction on `𝒦`
(`sum_sectorFibre_insert`): adding a class `κ` adds one hole of `κ` freely, the new hole being
separated from the old ones because separation is class-invariant (weak Corollary 5,
`evenHoleInducedCompatible_iff_of_closure`).  Peeling off one class at a time, `J_κ Π = λ_κ Π`
is applied from the right, one factor at a time (so no commutation of the `J_κ` is needed here).

## Deviations from the work package

* The package writes `H.operator.restrictSome.cycleSymmetry C₀`; the repository name of
  `J_{⟨C₀⟩}` is `generalizedCycleSymmetryOp`.
* The helper predicate `ClosureAvoids G W` (the deformation closure of a carrier avoiding `W`
  avoids `W`) packages the one place where `W = Ks` matters; it holds for `W = ∅` trivially and for
  a simplicial clique by `InEvenHoleDeformationClosure.disjoint_of_isSimplicialClique`
  (B11 (c)).
* The hypothesis `hPi` ranges over genuine even-hole carriers only, so the junk classes of
  `EvenHoleDeformationClass` (every non-hole is its own singleton class) never enter.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Class-level families and the polynomial `z_{W,λ}` -/

open scoped Classical in
/-- The sets `𝒦` of deformation classes of even holes avoiding `W` whose representatives
(`Quotient.out`) are pairwise separated in the weak sense of v1 L313
(`EvenHoleInducedCompatible`).  By weak Corollary 5 the condition does not depend on the chosen
representatives; two distinct classes only need to be separated, and a single class is never
separated from itself, so each class occurs once.  Only classes of genuine even-hole carriers
are allowed. -/
noncomputable def sectorClassFamilies (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (W : Set V) : Finset (Finset G.EvenHoleDeformationClass) :=
  Finset.univ.filter fun K =>
    (∀ κ ∈ K, G.IsEvenHoleCarrier κ.out ∧ Disjoint κ.out W) ∧
      (K : Set G.EvenHoleDeformationClass).Pairwise
        (fun κ κ' => G.EvenHoleInducedCompatible κ.out κ'.out)

/-- Membership in `sectorClassFamilies`. -/
theorem mem_sectorClassFamilies [Fintype V] [DecidableEq V] {W : Set V}
    {K : Finset G.EvenHoleDeformationClass} :
    K ∈ G.sectorClassFamilies W ↔
      (∀ κ ∈ K, G.IsEvenHoleCarrier κ.out ∧ Disjoint κ.out W) ∧
        (K : Set G.EvenHoleDeformationClass).Pairwise
          (fun κ κ' => G.EvenHoleInducedCompatible κ.out κ'.out) := by
  classical
  simp [sectorClassFamilies]

/-- **The sector polynomial `z_{W,λ}`** (v1 L1981 with `J_κ` replaced by the eigenvalue `λ_κ`,
L563-585): for couplings `b` and class eigenvalues `lam`,

`z_{W,λ}(x) = ∑_{𝒦 ∈ sectorClassFamilies G W}
  2^{|𝒦|} (∏_{κ ∈ 𝒦} λ_κ) x^{|∂𝒦|/2} I_{G∖(W ∪ Γ[𝒦])}(x)`,

where `∂𝒦 = ⋃_{κ ∈ 𝒦} κ.out` is the boundary of the family of representatives and
`Γ[𝒦] = ∂𝒦 ∪ N(∂𝒦)`.  The weights depend only on the classes
(`evenHoleFamilies_weight_data_eq`).  Indexing by sets of classes avoids the over-count `∏_κ |κ|`
that replacing each `h_C` by `λ_{⟨C⟩}` in the sum over hole families would produce. -/
noncomputable def sectorPolynomial (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (b : V → ℝ) (W : Set V) (lam : G.EvenHoleDeformationClass → ℝ) : Polynomial ℝ :=
  ∑ K ∈ G.sectorClassFamilies W,
    Polynomial.C (2 ^ K.card * ∏ κ ∈ K, lam κ) *
      Polynomial.X ^ ((G.familyBoundary (K.image Quotient.out)).ncard / 2) *
      G.weightedIndependencePolynomial b
        (W ∪ G.familyBoundary (K.image Quotient.out) ∪
          G.openNeighborhood (G.familyBoundary (K.image Quotient.out)))

/-- The families of `𝒞^{(even)}_{G∖W}` whose set of deformation classes is `K`: the fibre of the
class map over `K`. -/
noncomputable def sectorFibre (G : SimpleGraph V) [Fintype V] [DecidableEq V] (W : Set V)
    (K : Finset G.EvenHoleDeformationClass) : Finset (Finset (Set V)) := by
  classical exact (G.evenHoleFamilies W).filter fun X => X.image G.evenHoleDeformationClassOf = K

open scoped Classical in
/-- Membership in `sectorFibre`. -/
theorem mem_sectorFibre [Fintype V] [DecidableEq V] {W : Set V}
    {K : Finset G.EvenHoleDeformationClass} {X : Finset (Set V)} :
    X ∈ G.sectorFibre W K ↔
      X ∈ G.evenHoleFamilies W ∧ X.image G.evenHoleDeformationClassOf = K := by
  classical
  simp [sectorFibre]

/-! ### Deformation classes and their representatives -/

/-- The class of the representative of a class is the class. -/
theorem evenHoleDeformationClassOf_out (κ : G.EvenHoleDeformationClass) :
    G.evenHoleDeformationClassOf κ.out = κ :=
  Quotient.out_eq κ

/-- `C` lies in the deformation closure of the representative of `κ` exactly when `C` has class
`κ`. -/
theorem inEvenHoleDeformationClosure_out_iff {κ : G.EvenHoleDeformationClass} {C : Set V} :
    InEvenHoleDeformationClosure G κ.out C ↔ G.evenHoleDeformationClassOf C = κ := by
  rw [← evenHoleDeformationClassOf_eq_iff, evenHoleDeformationClassOf_out, eq_comm]

/-- A set lies in the deformation closure of the representative of its class. -/
theorem inEvenHoleDeformationClosure_classOf_out (C : Set V) :
    InEvenHoleDeformationClosure G (G.evenHoleDeformationClassOf C).out C :=
  inEvenHoleDeformationClosure_out_iff.2 rfl

/-! ### Avoiding the deleted carrier -/

/-- The deformation closure of a carrier avoiding `W` avoids `W`.  This is automatic for
`W = ∅` and holds for a simplicial clique (`closureAvoids_of_isSimplicialClique`, B11 (c)). -/
def ClosureAvoids (G : SimpleGraph V) (W : Set V) : Prop :=
  ∀ ⦃A B : Set V⦄, InEvenHoleDeformationClosure G A B → Disjoint A W → Disjoint B W

/-- Nothing is deleted: every closure avoids `∅`. -/
theorem closureAvoids_empty : G.ClosureAvoids ∅ := fun _ _ _ _ => Set.disjoint_empty _

/-- The deformation closure of a carrier avoiding a simplicial clique avoids it. -/
theorem closureAvoids_of_isSimplicialClique {Ks : Set V} (hKs : G.IsSimplicialClique Ks) :
    G.ClosureAvoids Ks :=
  fun _ _ hclo hA => hclo.disjoint_of_isSimplicialClique hKs hA

/-- `W = ∅`, or `W` a simplicial clique. -/
theorem closureAvoids_of_cases {Ks W : Set V}
    (hW : W = ∅ ∨ (W = Ks ∧ G.IsSimplicialClique Ks)) : G.ClosureAvoids W := by
  rcases hW with rfl | ⟨rfl, hKs⟩
  · exact closureAvoids_empty
  · exact closureAvoids_of_isSimplicialClique hKs

/-! ### The class map on a family of separated holes -/

/-- Two members of a family of separated even holes of the same deformation class coincide
(two holes of one class are never separated, Lemma 4). -/
theorem evenHoleDeformationClassOf_injOn_family (hclaw : G.IsClawFree) {X : Finset (Set V)}
    (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) :
    Set.InjOn G.evenHoleDeformationClassOf (X : Set (Set V)) := by
  intro C hC C' hC' h
  by_contra hne
  exact (evenHoleDeformationClassOf_eq_iff.1 h).not_evenHoleInducedCompatible hclaw
    (hX1 C (Finset.mem_coe.1 hC)) (hX2 hC hC' hne)

section Finite

open scoped Classical

variable [Fintype V] [DecidableEq V]

/-- The set of classes of a family `𝒳 ∈ 𝒞^{(even)}_{G∖W}` is in `sectorClassFamilies`. -/
theorem image_mem_sectorClassFamilies (hclaw : G.IsClawFree) {W : Set V}
    (hav : G.ClosureAvoids W) {X : Finset (Set V)} (hX : X ∈ G.evenHoleFamilies W) :
    X.image G.evenHoleDeformationClassOf ∈ G.sectorClassFamilies W := by
  rw [mem_evenHoleFamilies] at hX
  obtain ⟨hX1, hX2⟩ := hX
  rw [mem_sectorClassFamilies]
  refine ⟨?_, ?_⟩
  · intro κ hκ
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hκ
    have hout := inEvenHoleDeformationClosure_classOf_out (G := G) C
    exact ⟨hout.symm.isEvenHoleCarrier (hX1 C hC).1, hav hout.symm (hX1 C hC).2⟩
  · intro κ hκ κ' hκ' hne
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hκ)
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hκ')
    have hCC' : C ≠ C' := fun h => hne (h ▸ rfl)
    exact (evenHoleInducedCompatible_iff_of_closure
      (inEvenHoleDeformationClosure_classOf_out (G := G) C).symm
      (inEvenHoleDeformationClosure_classOf_out (G := G) C').symm hclaw
      (hX1 C hC).1 (hX1 C' hC').1).1 (hX2 (Finset.mem_coe.2 hC) (Finset.mem_coe.2 hC') hCC')

/-- The family of representatives of a set of classes in `sectorClassFamilies` is a family of
`𝒞^{(even)}_{G∖W}`, with the given set of classes. -/
theorem image_out_mem_evenHoleFamilies {W : Set V} {K : Finset G.EvenHoleDeformationClass}
    (hK : K ∈ G.sectorClassFamilies W) :
    K.image Quotient.out ∈ G.evenHoleFamilies W := by
  rw [mem_sectorClassFamilies] at hK
  rw [mem_evenHoleFamilies]
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.1 hC
    exact hK.1 κ hκ
  · intro C hC C' hC' hne
    obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC)
    obtain ⟨κ', hκ', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC')
    exact hK.2 (Finset.mem_coe.2 hκ) (Finset.mem_coe.2 hκ') (fun h => hne (h ▸ rfl))

omit [Fintype V] [DecidableEq V] in
/-- The classes of the representatives of `K` are `K`. -/
theorem image_classOf_image_out (K : Finset G.EvenHoleDeformationClass) :
    (K.image Quotient.out).image G.evenHoleDeformationClassOf = K := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := K)]
  exact Finset.image_congr fun κ _ => evenHoleDeformationClassOf_out κ

/-! ### The weight depends only on the set of classes -/

omit [Fintype V] [DecidableEq V] in
/-- `Γ[∂𝒳] = ⋃_{κ ∈ 𝒦} N(κ)`: the open neighbourhood of the boundary of a family only depends on
the set of classes of the family (Lemma 4, `InEvenHoleDeformationClosure.openNeighborhood_eq`). -/
theorem openNeighborhood_familyBoundary_eq_iUnion_out (hclaw : G.IsClawFree) (X : Finset (Set V)) :
    G.openNeighborhood (G.familyBoundary X) =
      ⋃ κ ∈ X.image G.evenHoleDeformationClassOf, G.openNeighborhood κ.out := by
  have key : ∀ C : Set V,
      G.openNeighborhood (G.evenHoleDeformationClassOf C).out = G.openNeighborhood C :=
    fun C => (inEvenHoleDeformationClosure_classOf_out (G := G) C).openNeighborhood_eq hclaw
  rw [Finset.set_biUnion_finset_image]
  ext t
  simp only [mem_openNeighborhood, familyBoundary, Set.mem_iUnion, key, exists_prop]
  constructor
  · rintro ⟨v, ⟨C, hC, hvC⟩, hadj⟩
    exact ⟨C, hC, v, hvC, hadj⟩
  · rintro ⟨C, hC, v, hvC, hadj⟩
    exact ⟨v, ⟨C, hC, hvC⟩, hadj⟩

omit [Fintype V] [DecidableEq V] in
/-- For a family of even-hole carriers, `∂𝒳 ⊆ N(∂𝒳)`, so `Γ[∂𝒳] = N(∂𝒳)`. -/
theorem familyBoundary_union_openNeighborhood {X : Finset (Set V)}
    (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C) :
    G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X) =
      G.openNeighborhood (G.familyBoundary X) := by
  refine Set.union_eq_self_of_subset_left fun v hv => ?_
  obtain ⟨C, hC, hvC⟩ := mem_familyBoundary.1 hv
  obtain ⟨w, hw, hadj⟩ := (hX1 C hC).subset_openNeighborhood hvC
  exact ⟨w, mem_familyBoundary.2 ⟨C, hC, hw⟩, hadj⟩

/-- `|∂𝒳| = ∑_{κ ∈ 𝒦} |κ|` for a family of separated even holes with set of classes `𝒦`
(the holes of one class have the same size, and the holes of a family are disjoint). -/
theorem familyBoundary_ncard_eq_sum_out_ncard (hclaw : G.IsClawFree) {X : Finset (Set V)}
    (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) :
    (G.familyBoundary X).ncard =
      ∑ κ ∈ X.image G.evenHoleDeformationClassOf, (κ.out).ncard := by
  rw [ncard_familyBoundary]
  have hbu : G.familyBoundaryFinset X = X.biUnion holeCarrierFinset := by
    ext v
    simp [mem_familyBoundaryFinset]
  rw [hbu, Finset.card_biUnion, Finset.sum_image
    (fun C hC C' hC' h => evenHoleDeformationClassOf_injOn_family hclaw hX1 hX2 hC hC' h)]
  · refine Finset.sum_congr rfl fun C hC => ?_
    have h1 : C.ncard = (holeCarrierFinset C).card := by
      conv_lhs => rw [← coe_holeCarrierFinset C]
      exact Set.ncard_coe_finset _
    rw [← h1]
    exact (inEvenHoleDeformationClosure_classOf_out (G := G) C).ncard_eq.symm
  · intro C hC C' hC' hne
    refine Finset.disjoint_left.2 fun v hv hv' => ?_
    exact Set.disjoint_left.1 (hX2 hC hC' hne).1 (mem_holeCarrierFinset.1 hv)
      (mem_holeCarrierFinset.1 hv')

/-- **The weight of a family only depends on its set of deformation classes.**  Two families of
`𝒞^{(even)}_{G∖W}` with the same set of classes have the same number of holes, the same number
of boundary vertices, and the same `W ∪ Γ[∂𝒳]` (v1 L1977: "`|C|` is constant on a class and
`Γ[∂𝒳]` only depends on classes by Lemma 4"). -/
theorem evenHoleFamilies_weight_data_eq (hclaw : G.IsClawFree) {W : Set V} {X X' : Finset (Set V)}
    (hX : X ∈ G.evenHoleFamilies W) (hX' : X' ∈ G.evenHoleFamilies W)
    (h : X.image G.evenHoleDeformationClassOf = X'.image G.evenHoleDeformationClassOf) :
    X.card = X'.card ∧ (G.familyBoundary X).ncard = (G.familyBoundary X').ncard ∧
      W ∪ G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X) =
        W ∪ G.familyBoundary X' ∪ G.openNeighborhood (G.familyBoundary X') := by
  rw [mem_evenHoleFamilies] at hX hX'
  have hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C := fun C hC => (hX.1 C hC).1
  have hX1' : ∀ C ∈ X', G.IsEvenHoleCarrier C := fun C hC => (hX'.1 C hC).1
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.card_image_of_injOn (evenHoleDeformationClassOf_injOn_family hclaw hX1 hX.2),
      h, Finset.card_image_of_injOn (evenHoleDeformationClassOf_injOn_family hclaw hX1' hX'.2)]
  · rw [familyBoundary_ncard_eq_sum_out_ncard hclaw hX1 hX.2,
      familyBoundary_ncard_eq_sum_out_ncard hclaw hX1' hX'.2, h]
  · rw [Set.union_assoc, Set.union_assoc, familyBoundary_union_openNeighborhood hX1,
      familyBoundary_union_openNeighborhood hX1',
      openNeighborhood_familyBoundary_eq_iUnion_out hclaw,
      openNeighborhood_familyBoundary_eq_iUnion_out hclaw, h]

/-! ### The fibre over a set of classes -/

/-- Adding a hole of class `κ` to a family of class set `K'` (with `κ ∉ K'`, and `insert κ K'`
a valid set of classes) gives a family of class set `insert κ K'`, in which the new hole is not
yet present. -/
theorem insert_mem_sectorFibre (hclaw : G.IsClawFree) {W : Set V} (hav : G.ClosureAvoids W)
    {κ : G.EvenHoleDeformationClass} {K' : Finset G.EvenHoleDeformationClass} (hκ : κ ∉ K')
    (hK : insert κ K' ∈ G.sectorClassFamilies W) {C : Set V} {X' : Finset (Set V)}
    (hC : InEvenHoleDeformationClosure G κ.out C) (hX' : X' ∈ G.sectorFibre W K') :
    C ∉ X' ∧ insert C X' ∈ G.sectorFibre W (insert κ K') := by
  rw [mem_sectorFibre, mem_evenHoleFamilies] at hX'
  obtain ⟨⟨hX1, hX2⟩, hXK⟩ := hX'
  rw [mem_sectorClassFamilies] at hK
  have hCκ : G.evenHoleDeformationClassOf C = κ := inEvenHoleDeformationClosure_out_iff.1 hC
  have hκ0 := hK.1 κ (Finset.mem_insert_self _ _)
  have hCh : G.IsEvenHoleCarrier C := hC.isEvenHoleCarrier hκ0.1
  have hCW : Disjoint C W := hav hC hκ0.2
  have hCX : C ∉ X' := by
    intro hCX
    apply hκ
    rw [← hXK, ← hCκ]
    exact Finset.mem_image_of_mem _ hCX
  refine ⟨hCX, ?_⟩
  rw [mem_sectorFibre, mem_evenHoleFamilies]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro C' hC'
    rcases Finset.mem_insert.1 hC' with rfl | hC'
    · exact ⟨hCh, hCW⟩
    · exact hX1 C' hC'
  · rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hX2, fun C' hC' hne => ?_⟩
    have hC'X : C' ∈ X' := Finset.mem_coe.1 hC'
    have hκ' : G.evenHoleDeformationClassOf C' ∈ K' := by
      rw [← hXK]
      exact Finset.mem_image_of_mem _ hC'X
    have hneκ : κ ≠ G.evenHoleDeformationClassOf C' := fun h => hκ (h ▸ hκ')
    have hcompat : G.EvenHoleInducedCompatible κ.out (G.evenHoleDeformationClassOf C').out :=
      hK.2 (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hκ')) hneκ
    have hAc : G.IsEvenHoleCarrier κ.out := hκ0.1
    have hBc : G.IsEvenHoleCarrier (G.evenHoleDeformationClassOf C').out :=
      (hK.1 _ (Finset.mem_insert_of_mem hκ')).1
    have h := (evenHoleInducedCompatible_iff_of_closure hC
      (inEvenHoleDeformationClosure_classOf_out (G := G) C') hclaw hAc hBc).1 hcompat
    exact ⟨h, evenHoleInducedCompatible_comm.1 h⟩
  · rw [Finset.image_insert, hCκ, hXK]

/-- **Fibre decomposition.**  The families whose set of classes is `insert κ K'` are exactly the
families `insert C X'` with `C` a hole of class `κ` and `X'` a family of class set `K'`, each
occurring once; so a sum over the fibre over `insert κ K'` is the iterated sum over
`C ∈ ⟨κ.out⟩` and over the fibre over `K'`. -/
theorem sum_sectorFibre_insert {M : Type*} [AddCommMonoid M] (hclaw : G.IsClawFree) {W : Set V}
    (hav : G.ClosureAvoids W) {κ : G.EvenHoleDeformationClass}
    {K' : Finset G.EvenHoleDeformationClass} (hκ : κ ∉ K')
    (hK : insert κ K' ∈ G.sectorClassFamilies W) (f : Finset (Set V) → M) :
    ∑ X ∈ G.sectorFibre W (insert κ K'), f X =
      ∑ C ∈ G.deformationClosureFinset κ.out, ∑ X' ∈ G.sectorFibre W K', f (insert C X') := by
  rw [← Finset.sum_product' (f := fun C X' => f (insert C X'))]
  symm
  refine Finset.sum_bij (fun p _ => insert p.1 p.2) ?_ ?_ ?_ ?_
  · rintro ⟨C, X'⟩ hp
    rw [Finset.mem_product, mem_deformationClosureFinset] at hp
    exact (insert_mem_sectorFibre hclaw hav hκ hK hp.1 hp.2).2
  · rintro ⟨C₁, X₁⟩ hp₁ ⟨C₂, X₂⟩ hp₂ h
    rw [Finset.mem_product, mem_deformationClosureFinset] at hp₁ hp₂
    obtain ⟨hn₁, -⟩ := insert_mem_sectorFibre hclaw hav hκ hK hp₁.1 hp₁.2
    obtain ⟨hn₂, -⟩ := insert_mem_sectorFibre hclaw hav hκ hK hp₂.1 hp₂.2
    dsimp only at h hn₁ hn₂
    have hC : C₁ = C₂ := by
      have hmem : C₁ ∈ insert C₂ X₂ := h ▸ Finset.mem_insert_self _ _
      rcases Finset.mem_insert.1 hmem with h' | h'
      · exact h'
      · exfalso
        have hc₁ := inEvenHoleDeformationClosure_out_iff.1 hp₁.1
        have hX₂ := (mem_sectorFibre.1 hp₂.2).2
        apply hκ
        rw [← hX₂, ← hc₁]
        exact Finset.mem_image_of_mem _ h'
    subst hC
    have hX : X₁ = X₂ := by
      rw [← Finset.erase_insert hn₁, h, Finset.erase_insert hn₂]
    rw [hX]
  · intro X hX
    rw [mem_sectorFibre] at hX
    obtain ⟨hXf, hXK⟩ := hX
    have hXf' := mem_evenHoleFamilies.1 hXf
    have hκX : κ ∈ X.image G.evenHoleDeformationClassOf := by
      rw [hXK]
      exact Finset.mem_insert_self _ _
    obtain ⟨C, hCX, hCκ⟩ := Finset.mem_image.1 hκX
    have hinj := evenHoleDeformationClassOf_injOn_family hclaw (fun C hC => (hXf'.1 C hC).1) hXf'.2
    refine ⟨(C, X.erase C), ?_, ?_⟩
    · rw [Finset.mem_product, mem_deformationClosureFinset]
      refine ⟨inEvenHoleDeformationClosure_out_iff.2 hCκ, ?_⟩
      rw [mem_sectorFibre, mem_evenHoleFamilies]
      refine ⟨⟨fun C' hC' => hXf'.1 C' (Finset.mem_of_mem_erase hC'),
        hXf'.2.mono (by intro x hx; exact Finset.mem_coe.2 (Finset.mem_of_mem_erase hx))⟩, ?_⟩
      ext κ'
      rw [Finset.mem_image]
      constructor
      · rintro ⟨C', hC', rfl⟩
        have hC'X := Finset.mem_of_mem_erase hC'
        have hmem : G.evenHoleDeformationClassOf C' ∈ insert κ K' := by
          rw [← hXK]
          exact Finset.mem_image_of_mem _ hC'X
        rcases Finset.mem_insert.1 hmem with h | h
        · exact absurd (hinj (Finset.mem_coe.2 hC'X) (Finset.mem_coe.2 hCX) (h.trans hCκ.symm))
            (Finset.ne_of_mem_erase hC')
        · exact h
      · intro hκ'
        have hmem : κ' ∈ X.image G.evenHoleDeformationClassOf := by
          rw [hXK]
          exact Finset.mem_insert_of_mem hκ'
        obtain ⟨C', hC'X, rfl⟩ := Finset.mem_image.1 hmem
        refine ⟨C', Finset.mem_erase.2 ⟨?_, hC'X⟩, rfl⟩
        rintro rfl
        exact hκ (hCκ ▸ hκ')
    · exact Finset.insert_erase hCX
  · intro p hp
    rfl

end Finite

end SimpleGraph

namespace SimpleGraph

namespace PauliFrustrationRepresentation

open scoped Classical

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- **The regrouping of v1 L1981.**  Let `Π` satisfy `J_{⟨C₀⟩} Π = λ_{⟨C₀⟩} Π` for every even-hole
carrier `C₀`.  Then for every set `𝒦` of pairwise separated deformation classes avoiding `W`,

`(∑_{𝒳 : families with class set 𝒦} ∏_{C ∈ 𝒳} h_C) Π = (∏_{κ ∈ 𝒦} λ_κ) Π`.

The sum over the fibre is the product `∏_{κ ∈ 𝒦} J_κ` (`sum_sectorFibre_insert`); acting on `Π`
from the right, each factor `J_κ` is replaced by `λ_κ`. -/
theorem sum_sectorFibre_familyOperator_mul [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra R A]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {W : Set V}
    (hav : G.ClosureAvoids W) (Pi : A) (lam : G.EvenHoleDeformationClass → R)
    (hPi : ∀ C₀, G.IsEvenHoleCarrier C₀ →
      H.generalizedCycleSymmetryOp C₀ * Pi = lam (G.evenHoleDeformationClassOf C₀) • Pi) :
    ∀ K ∈ G.sectorClassFamilies W,
      (∑ X ∈ G.sectorFibre W K, H.familyOperator X) * Pi = (∏ κ ∈ K, lam κ) • Pi := by
  intro K
  induction K using Finset.induction_on with
  | empty =>
    intro _
    have hfib : G.sectorFibre W ∅ = {∅} := by
      ext X
      rw [mem_sectorFibre, Finset.mem_singleton, Finset.image_eq_empty]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨empty_mem_evenHoleFamilies W, rfl⟩
    rw [hfib, Finset.sum_singleton, H.familyOperator_empty, one_mul, Finset.prod_empty, one_smul]
  | insert κ K' hκ ih =>
    intro hK
    have hK' : K' ∈ G.sectorClassFamilies W := by
      rw [mem_sectorClassFamilies] at hK ⊢
      exact ⟨fun κ' h => hK.1 κ' (Finset.mem_insert_of_mem h),
        hK.2.mono (by simp)⟩
    have hκ0 := (mem_sectorClassFamilies.1 hK).1 κ (Finset.mem_insert_self _ _)
    rw [sum_sectorFibre_insert hclaw hav hκ hK, Finset.prod_insert hκ]
    have hstep : ∀ C ∈ G.deformationClosureFinset κ.out,
        ∑ X' ∈ G.sectorFibre W K', H.familyOperator (insert C X') =
          H.evenHoleOperator C * ∑ X' ∈ G.sectorFibre W K', H.familyOperator X' := by
      intro C hC
      rw [mem_deformationClosureFinset] at hC
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun X' hX' => ?_
      obtain ⟨hCX, hins⟩ := insert_mem_sectorFibre hclaw hav hκ hK hC hX'
      exact H.familyOperator_insert hCX (mem_evenHoleFamilies.1 (mem_sectorFibre.1 hins).1).2
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, mul_assoc, ih hK']
    have hJ : ∑ C ∈ G.deformationClosureFinset κ.out, H.evenHoleOperator C =
        H.generalizedCycleSymmetryOp κ.out := rfl
    rw [hJ, mul_smul_comm, hPi κ.out hκ0.1, evenHoleDeformationClassOf_out, smul_smul, mul_comm]

end PauliFrustrationRepresentation

end SimpleGraph

namespace SimpleGraph

namespace PauliCliqueHamiltonianRepresentation

open scoped Classical

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w} [Ring A] [Algebra ℝ A]

/-- **Sector form of `Z_{G∖W}` (v1 L1979-1982 with L563-585).**  Let `G` be claw-free, `H` a
Hamiltonian representation of it, `W = ∅` or `W = Ks` a simplicial clique, and `Π` an element of
the operator algebra with `J_{⟨C₀⟩} Π = λ_{⟨C₀⟩} Π` for every even-hole carrier `C₀`, where
`J_{⟨C₀⟩} = ∑_{C ∈ ⟨C₀⟩} h_C` (`generalizedCycleSymmetryOp`) and `λ` is a function on deformation
classes.  Then

`Z_{G∖W}(-u²) Π = T_{G∖W}(u) T_{G∖W}(-u) Π = z_{W,λ}(-u²) Π`,

where `z_{W,λ} = sectorPolynomial G H.coupling W λ` is the real polynomial obtained from
`Z_{G∖W}(-u²) = ∑_𝒦 (-u²)^{|∂𝒦|/2} 2^{|𝒦|} I_{G∖(W ∪ Γ[𝒦])}(-u²) ∏_{κ ∈ 𝒦} J_κ` by replacing
each `J_κ` with `λ_κ`.  The hypothesis ranges over genuine even-hole carriers only (the quotient
`EvenHoleDeformationClass` also contains junk classes of non-holes, which never occur in
`z_{W,λ}`); `hW` is used only through the fact that the deformation closure of a hole avoiding
`W` avoids `W`.  `Π = 0` is allowed (the statement is then trivial). -/
theorem transfer_mul_transfer_neg_mul_sector [Fintype V] [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation Ks ℝ A) (hclaw : G.IsClawFree) {W : Set V}
    (hW : W = ∅ ∨ (W = Ks ∧ G.IsSimplicialClique Ks)) (Pi : A)
    (lam : G.EvenHoleDeformationClass → ℝ)
    (hPi : ∀ C₀, G.IsEvenHoleCarrier C₀ →
      H.operator.restrictSome.generalizedCycleSymmetryOp C₀ * Pi =
        lam (G.evenHoleDeformationClassOf C₀) • Pi) (u : ℝ) :
    H.operator.restrictSome.transfer W u * H.operator.restrictSome.transfer W (-u) * Pi =
      (G.sectorPolynomial H.coupling W lam).eval (-u ^ 2) • Pi := by
  have hav := closureAvoids_of_cases hW
  rw [H.generalizedCharacteristicPolynomial hclaw W u, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := G.evenHoleFamilies W)
    (t := G.sectorClassFamilies W) (g := fun X => X.image G.evenHoleDeformationClassOf)
    (fun X hX => image_mem_sectorClassFamilies hclaw hav hX)]
  rw [sectorPolynomial, Polynomial.eval_finsetSum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun K hK => ?_
  have hY := image_out_mem_evenHoleFamilies hK
  have hYK := image_classOf_image_out (G := G) K
  have hcardY : (K.image (Quotient.out : G.EvenHoleDeformationClass → Set V)).card = K.card :=
    Finset.card_image_of_injective _ Quotient.out_injective
  have hfib : (G.evenHoleFamilies W).filter
      (fun X => X.image G.evenHoleDeformationClassOf = K) = G.sectorFibre W K := by
    ext X
    rw [Finset.mem_filter, mem_sectorFibre]
  rw [hfib]
  have hS := H.operator.restrictSome.sum_sectorFibre_familyOperator_mul hclaw hav Pi lam hPi K hK
  set c : ℝ := (-u ^ 2) ^ ((G.familyBoundary (K.image Quotient.out)).ncard / 2) * 2 ^ K.card *
    Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
      (W ∪ G.familyBoundary (K.image Quotient.out) ∪
        G.openNeighborhood (G.familyBoundary (K.image Quotient.out)))) with hc
  have hterm : ∀ X ∈ G.sectorFibre W K,
      (((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
        Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
          (W ∪ G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
          H.operator.restrictSome.familyOperator X) * Pi =
        c • (H.operator.restrictSome.familyOperator X * Pi) := by
    intro X hX
    rw [mem_sectorFibre] at hX
    obtain ⟨h1, h2, h3⟩ := evenHoleFamilies_weight_data_eq hclaw hX.1 hY (hX.2.trans hYK.symm)
    rw [smul_mul_assoc, h1, h2, h3, hcardY]
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.sum_mul, hS, smul_smul]
  congr 1
  rw [hc]
  simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
