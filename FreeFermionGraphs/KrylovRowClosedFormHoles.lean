import FreeFermionGraphs.KrylovRowClosedForm
import FreeFermionGraphs.HoleAttachment
import FreeFermionGraphs.HoleSimplicialClique
import FreeFermionGraphs.EvenHoleOperators
import FreeFermionGraphs.CliqueHoppingMatrix
import FreeFermionGraphs.CliqueBubbleWandReverse

/-!
# Closed form of the Krylov rows of `A_λ`: the sector polynomial with hole terms

Manuscript reference: arXiv 2305.15625v1, Lemma `generalizedcharacteristicpolynomial` (statement
L1266-1271), the cycle-symmetry form Eq. (cyclesymmetries) of `Z_G` (L560-580), the proof of
Theorem 3, case (b.iv) with Eq. (pathcircle) (L1520-1576), and Eq. (decoratedtree)
(L1434-1445).  The identity proved here is not stated in v1.  It is the closed form behind the
polynomial divisibility of Theorem 3 (L1328-1336) for graphs *with* even holes, and the extension
of `KrylovRowClosedForm.lean` (even-hole-free tree matrix) to the corrected matrix
`A_λ = cliqueHoppingMatrix G K b lam` of `CliqueHoppingMatrix.lean`, with the hoop arcs.

## The statement

Let `G` be a finite claw-free graph, `K` a simplicial clique, `b : V → R` (`R` a field), and
`lam` an arbitrary assignment of a number `λ_c` to every deformation class `c` of even holes
(on a sector, `λ_c` is the eigenvalue of the generalized cycle symmetry `J_c`).  For a rooted
induced path `Q` of `G* = G + j*`, with `|Q|` its number of vertices (root included) and
`N(Q) = K ∪ ⋃_{i ≥ 1} Γ[j_i]`,

`(∑_n X^n (A_λ^n)_{{j*},Q}) · Z_V = X^{|Q|-1} · Z_{V ∖ N(Q)}`    in `R⟦X⟧`,

where `Z_U = sectorIndepSeries G b² lam U` is the sector reduction of the generalized
characteristic polynomial of `G[U]` at `x = -X²`:

`Z_U = ∑_𝒳 ∏_{C ∈ 𝒳} (2 (-X²)^{|C|/2} λ_{⟨C⟩} / |⟨C⟩|) · I_{U ∖ Γ[𝒳]}(-X²)`,

the sum over the families `𝒳` of pairwise compatible (v1 L313) even holes inside `U`.  For a
single class `c` this is `Z_U = I_U + 2 (-1)^k λ_c X^{2k} I_{U ∖ Γ[c]}` when the holes of `c` lie
in `U`, and `Z_U = I_U` when none does (`sectorIndepSeries_of_single_class_of_all`,
`_of_none`); for no even hole at all `Z_U = I_U` and the identity is
`krylovRow_mul_indepSeries` (`krylovRow_mul_sectorIndepSeries_of_evenHoleFree`).

## What the sector series is (multi-class)

v1's `Z_G = ∑_𝒳 (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖Γ[𝒳]} ∏_{C ∈ 𝒳} h_C` sums over families `𝒳` of
pairwise compatible even holes.  Two holes of one deformation class are never compatible
(`not_evenHoleInducedCompatible_of_mem_closure`), and compatibility depends only on the classes
(`evenHoleInducedCompatible_iff_of_closure`, the weak form of v1 Corollary 5, L749-751).  So the
families with class set `{c_1, …, c_m}` are the choices of one hole in each class, and
`∑ ∏ h_{C_i} = ∏ J_{c_i}`; on a sector `J_c ↦ λ_c`.  Equivalently one gives each hole of `c` the
weight `λ_c/|c|`, since the `|c|` holes of a class have the same `Γ[·]` (v1 Lemma 4,
`evenholeneighbor`, L736-739; repo `lemma9` / `InEvenHoleDeformationClosure.openNeighborhood_eq`),
the same size, and `∑_{C ∈ c} λ_c/|c| = λ_c`: this is the per-hole reading used in the
definition of `sectorIndepSeries`.

*Scope of the sector reading.*  The per-hole series is the sector reduction of v1's `Z_{G[U]}`
(`J_c ↦ λ_c`) only (i) for sets `U` that contain all or none of the holes of each class, and
(ii) when `|c|` is invertible in `R` (e.g. `[CharZero R]`).  For other `U` it is only a
bookkeeping series with per-hole weights `λ_c/|c|` and differs from the class-level polynomial.
The two sets `V` and `V ∖ N(Q)` of the theorem satisfy (i)
(`subset_compl_closedNbhd_iff_of_closure`: the holes of a class lie all inside or all outside
`V ∖ N(Q)`), so for them the series is the class-level quantity
`∑_{compatible class families} ∏_c 2(-X²)^{k_c} λ_c · I_{U ∖ Γ[·]}`.  As for (ii), the identity
`krylovRow_mul_sectorIndepSeries` itself holds over every field, but when `char R` divides some
`|c|` Lean's `λ_c/|c|` is `0`, so `sectorHoleWeight` and the hoop entries of
`cliqueHoppingMatrix` both vanish for that class and the series is no longer the sector
reduction of v1's `Z`.
(The identification with v1's operator `Z_{G∖W}` restricted to `Π_J` is the sector form of
v1 Lemma 11 (`generalizedcharacteristicpolynomial`, L1266-1271),
`SectorCharacteristicPolynomial.lean`; it is not used or proved here.)

## Main declarations

* `holeFamilies G U`, `holeSeries G ω w U`: the compatible families of even holes inside `U` and
  the series `∑_𝒳 (∏_{C ∈ 𝒳} ω_C) I_{U ∖ Γ[𝒳]}` for an arbitrary hole weight `ω`;
  `holeSeries_split`: the clique recursion `Z_U = Z_{U∖D} - X² ∑_{y ∈ D} w_y Z_{U∖Γ[y]} +
  ∑_{C ∩ D ≠ ∅} ω_C Z_{U∖Γ[C]}` for every clique `D ⊆ U` (no claw-freeness needed): the
  analogue of `indepSeries_clique_split` with the hole terms of the holes that meet `D`.
* `sectorHoleWeight`, `sectorIndepSeries`: the sector series (the interface of the work package).
* `RootedInducedPath.holeAttached_iff`: a hole is attached to `Q` (`HoleAttachment.lean`) iff it
  lies in `V ∖ N(P)` (`P` the parent of `Q`) and contains a child of `Q`.  Hence the holes that
  meet the clique `C(Q)` of children in the clique recursion are exactly the holes attached to
  `Q`: `holesMeeting_eq_attachedHoles`.
* `CliqueBubbleWand.closedNbhd_eq_handle_union`: `N(P) = N(Q) ∪ Γ[C]` for a wand `w` on `P` with
  handle `Q` and even hoop `C`.
* `sum_holeEvents`: the wand events with handle `Q` are twice the attached holes, class by class
  (the fibrewise form of `card_evenHoopEvents`).
* `holeRowTarget_tree_column`, `holeRowTarget_hoop_column`, `sectorRowTarget_column`: the column
  recursion `r_Q = [Q = {j*}] Z_V + X ∑_P (A_λ)_{PQ} r_P` for `r_Q = X^{|Q|-1} Z_{V∖N(Q)}`.
* `krylovRow_mul_sectorIndepSeries`: the closed form (every number of classes).
* `krylovRow_mul_indepSeries_single_class`: the explicit single-class form.
* `sectorRow_pow_eq_of_closedNbhd_eq` and its instances (deformations, wand reversals, sources
  of one handle and one hoop class): the rows of `A_λ` are balanced; this is v1 Lemma 16
  (`deformationclosurepathsrelation`) and Eq. (pathcircle) for the corrected matrix, for any
  number of hole classes.

## Proof

As in `KrylovRowClosedForm.lean`, avoid matrix inverses and show that `r_Q` solves the column
recursion `r_Q = [Q = {j*}] Z_V + X ∑_P (A_λ)_{PQ} r_P`, whose solution is unique.

* *Tree part.*  The sources `P` of the tree matrix are the parent of `Q` and the children
  `Q + x`, `x ∈ D := C(Q)`.  With `U = V ∖ N(P)`, `N(Q) = N(P) ⊔ D` and `N(Q+x) = N(P) ∪ Γ[x]`
  the tree part of the recursion is the clique recursion `holeSeries_split` for `U` and `D`
  *except* for the term `X^{|Q|-1} ∑_{C meets D} ω_C Z_{U∖Γ[C]}` of the holes that meet the
  clique `D` (`holeRowTarget_tree_column`).  Compatible holes cannot both meet a clique, so
  the families meeting `D` are `{C} ∪ 𝒳'` with `𝒳'` a family inside `U ∖ Γ[C]`.
* *Hoop part.*  The sources of the arcs `P → Q` of `A_λ - T` are the wand sources with handle `Q`;
  a wand on `P` has `|P| = |Q| - 1 + |C|` and `N(P) = N(Q) ∪ Γ[C]`
  (`CliqueBubbleWand.closedNbhd_eq_handle_union`), the entry is `(-1)^{k-1} λ_c/|c|` per event
  and there are two events for each attached hole `C` (`sum_holeEvents`, from
  `card_evenHoopEvents` and the class-invariance of `Γ[C]` and `|C|`).  Since `X (-1)^{k-1}
  X^{|Q|+2k-2} = -X^{|Q|-1} (-X²)^k`, the hoop part is exactly `-X^{|Q|-1} ∑_{C attached} ω_C
  Z_{U ∖ Γ[C]}` (`holeRowTarget_hoop_column`), which cancels the defect of the tree part.
  A hole meets `D = C(Q)` and lies in `V ∖ N(P)` iff it is attached to `Q`
  (`RootedInducedPath.holeAttached_iff`; claw-freeness of `G*` at the terminal vertex).

## Fidelity

Nothing here is a certificate or a structure field, and no claim that is supposed to be proved
is assumed: every statement is a theorem about the manuscript setup (a finite claw-free `G`, a
simplicial clique `K`) with the free data `b` and `lam`.  The matrix is the corrected matrix of
`CliqueHoppingMatrix.lean` (root-handle arcs, sign `(-1)^{k-1}`, per-event normalisation `1/|c|`;
see its docstring for why the printed Eq. (decoratedtree) is not usable).  The theorems help
prove Theorem 3 of v1 case (b.iv) (through Eq. (pathcircle) and the Lemma
`deformationclosurepathsrelation`) for graphs with even holes; the operator statement itself
(`ad^k χ · Π = ∑_P (-2i)^k (A_λ^k)_{{j*},P} h_P Π`) is not touched here.

## Deviations from the work package

* `sectorIndepSeries` is defined here (the package states it as an interface); the definition is
  the per-hole one above, so that the statement is a theorem for *every* number of classes.  The
  single-class case, which the package expected to prove if the general one were out of reach, is
  a corollary (`krylovRow_mul_indepSeries_single_class`).
* `[CharZero R]` is not needed for `krylovRow_mul_sectorIndepSeries` (it is needed only for the
  cancellation `n_U / |c| = 1` in the single-class closed form of `Z`).  The identity holds over
  every field, but the reading of `Z` as v1's sector-reduced polynomial needs `|c|` to be
  invertible in `R` (see "Scope of the sector reading" above).
* The theorem is not in v1, so its name carries no `paper` prefix; its hypotheses are exactly the
  manuscript setup (finite, claw-free `G`, simplicial clique `K`).  `lam` is arbitrary: no
  property of the sector (the eigenvalue relations of `Π_J`) enters, the identity is
  combinatorial.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

section HoleSeries

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w} [CommRing R]

/-- The families `𝒳` of pairwise compatible even holes inside `U`: finite sets of even-hole
carriers `C ⊆ U` such that `G[C ∪ C']` is the disjoint union of `G[C]` and `G[C']` for
distinct `C, C' ∈ 𝒳` (`EvenHoleInducedCompatible`, v1 L313).  This is `𝒞^{(even)}_{G[U]}` of
v1 (L313-317). -/
noncomputable def holeFamilies (G : SimpleGraph V) (U : Finset V) :
    Finset (Finset (Set V)) :=
  Finset.univ.filter fun F : Finset (Set V) =>
    (∀ C ∈ F, G.IsEvenHoleCarrier C ∧ C ⊆ (U : Set V)) ∧
      (F : Set (Set V)).Pairwise G.EvenHoleInducedCompatible

omit [DecidableEq V] in
theorem mem_holeFamilies {U : Finset V} {F : Finset (Set V)} :
    F ∈ G.holeFamilies U ↔ (∀ C ∈ F, G.IsEvenHoleCarrier C ∧ C ⊆ (U : Set V)) ∧
      (F : Set (Set V)).Pairwise G.EvenHoleInducedCompatible := by
  simp [holeFamilies]

/-- The part `U ∖ Γ[𝒳]` of `U` outside the closed neighbourhoods `Γ[C] = openNeighborhood C` of
the holes of the family `𝒳 = F` (for an even hole `C ⊆ openNeighborhood C`, so
`openNeighborhood C` is the closed neighbourhood). -/
noncomputable def holeFamilyRest (G : SimpleGraph V) (U : Finset V) (F : Finset (Set V)) :
    Finset V :=
  U.filter fun v => ∀ C ∈ F, v ∉ G.openNeighborhood C

omit [DecidableEq V] in
theorem mem_holeFamilyRest {U : Finset V} {F : Finset (Set V)} {v : V} :
    v ∈ G.holeFamilyRest U F ↔ v ∈ U ∧ ∀ C ∈ F, v ∉ G.openNeighborhood C := by
  simp [holeFamilyRest]

/-- The hole-weighted independence series
`∑_{𝒳 ∈ holeFamilies G U} (∏_{C ∈ 𝒳} ω_C) · I_{U ∖ Γ[𝒳]}(-X²)` with the independence series
`I` of `indepSeries` for the weights `w`.  The weight `ω` of a single hole is arbitrary here;
`sectorIndepSeries` takes the sector weight `sectorHoleWeight`. -/
noncomputable def holeSeries (G : SimpleGraph V) (ω : Set V → PowerSeries R) (w : V → R)
    (U : Finset V) : PowerSeries R :=
  ∑ F ∈ G.holeFamilies U, (∏ C ∈ F, ω C) * indepSeries G w (G.holeFamilyRest U F)

/-- The even holes inside `U` meeting `D`. -/
noncomputable def holesMeeting (G : SimpleGraph V) (U D : Finset V) : Finset (Set V) :=
  Finset.univ.filter fun C => G.IsEvenHoleCarrier C ∧ C ⊆ (U : Set V) ∧ ∃ d ∈ D, d ∈ C

omit [DecidableEq V] in
theorem mem_holesMeeting {U D : Finset V} {C : Set V} :
    C ∈ G.holesMeeting U D ↔ G.IsEvenHoleCarrier C ∧ C ⊆ (U : Set V) ∧ ∃ d ∈ D, d ∈ C := by
  simp [holesMeeting]

omit [Fintype V] [DecidableEq V] in
/-- For an even hole `C`, a vertex `y` lies in `Γ[C] = openNeighborhood C` iff some vertex of `C`
lies in the closed neighbourhood `Γ[y]` of `y` (`C ⊆ openNeighborhood C`). -/
theorem IsEvenHoleCarrier.mem_openNeighborhood_iff {C : Set V} (hC : G.IsEvenHoleCarrier C)
    {y : V} : y ∈ G.openNeighborhood C ↔ ∃ v ∈ C, v ∈ G.closedNeighborhood y := by
  constructor
  · rintro ⟨v, hv, hyv⟩
    exact ⟨v, hv, Or.inr ((G.mem_neighborSet _ _).2 hyv)⟩
  · rintro ⟨v, hv, hvy⟩
    rcases hvy with rfl | hvy
    · exact hC.subset_openNeighborhood hv
    · exact ⟨v, hv, (G.mem_neighborSet _ _).1 hvy⟩

theorem holeFamilies_filter_not_mem (U D : Finset V) :
    G.holeFamilies (U.filter fun v => v ∉ D) =
      (G.holeFamilies U).filter fun F => ∀ C ∈ F, ∀ d ∈ D, d ∉ C := by
  ext F
  simp only [mem_holeFamilies, Finset.mem_filter, Set.subset_def, Finset.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun C hC => ⟨(h1 C hC).1, fun v hv => ((h1 C hC).2 v hv).1⟩,
      h2⟩, fun C hC d hd hdC => ?_⟩
    exact ((h1 C hC).2 d hdC).2 hd
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun C hC => ⟨(h1 C hC).1, fun v hv => ?_⟩, h2⟩
    exact ⟨(h1 C hC).2 v hv, fun hvD => h3 C hC v hvD hv⟩

omit [DecidableEq V] in
theorem holeFamilies_filter_not_closedNeighborhood (U : Finset V) (y : V) :
    G.holeFamilies (U.filter fun v => v ∉ G.closedNeighborhood y) =
      (G.holeFamilies U).filter fun F => ∀ C ∈ F, y ∉ G.openNeighborhood C := by
  ext F
  simp only [mem_holeFamilies, Finset.mem_filter, Set.subset_def, Finset.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun C hC => ⟨(h1 C hC).1, fun v hv => ((h1 C hC).2 v hv).1⟩,
      h2⟩, fun C hC hy => ?_⟩
    obtain ⟨v, hv, hvy⟩ := ((h1 C hC).1.mem_openNeighborhood_iff).1 hy
    exact ((h1 C hC).2 v hv).2 hvy
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun C hC => ⟨(h1 C hC).1, fun v hv => ?_⟩, h2⟩
    refine ⟨(h1 C hC).2 v hv, fun hvy => h3 C hC ?_⟩
    exact ((h1 C hC).1.mem_openNeighborhood_iff).2 ⟨v, hv, hvy⟩


omit [DecidableEq V] in
theorem holeFamilyRest_filter (U : Finset V) (F : Finset (Set V)) (p : V → Prop)
    [DecidablePred p] :
    (G.holeFamilyRest U F).filter p = G.holeFamilyRest (U.filter p) F := by
  ext v
  simp only [mem_holeFamilyRest, Finset.mem_filter]
  tauto

/-- One clique-splitting step of `I` along `D` for the part of `U` outside `Γ[F]`. -/
theorem indepSeries_holeFamilyRest_split (w : V → R) {D U : Finset V}
    (hD : G.IsClique (D : Set V)) (hDU : D ⊆ U) (F : Finset (Set V)) :
    indepSeries G w (G.holeFamilyRest U F) =
      indepSeries G w (G.holeFamilyRest (U.filter fun v => v ∉ D) F) -
        PowerSeries.X ^ 2 * ∑ y ∈ D.filter (fun y => ∀ C ∈ F, y ∉ G.openNeighborhood C),
          PowerSeries.C (w y) * indepSeries G w
            (G.holeFamilyRest (U.filter fun v => v ∉ G.closedNeighborhood y) F) := by
  have hDF : G.IsClique ((D.filter (fun y => ∀ C ∈ F, y ∉ G.openNeighborhood C) : Finset V) :
      Set V) := hD.subset (by
    intro x hx
    exact (Finset.mem_filter.1 hx).1)
  have hsub : D.filter (fun y => ∀ C ∈ F, y ∉ G.openNeighborhood C) ⊆
      G.holeFamilyRest U F := by
    intro y hy
    obtain ⟨hyD, hyF⟩ := Finset.mem_filter.1 hy
    exact mem_holeFamilyRest.2 ⟨hDU hyD, hyF⟩
  have h := indepSeries_clique_split G w hDF hsub
  have e1 : (G.holeFamilyRest U F).filter
      (fun v => v ∉ D.filter (fun y => ∀ C ∈ F, y ∉ G.openNeighborhood C)) =
        G.holeFamilyRest (U.filter fun v => v ∉ D) F := by
    ext v
    simp only [mem_holeFamilyRest, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hvU, hvF⟩, hvn⟩
      exact ⟨⟨hvU, fun hvD => hvn ⟨hvD, hvF⟩⟩, hvF⟩
    · rintro ⟨⟨hvU, hvD⟩, hvF⟩
      exact ⟨⟨hvU, hvF⟩, fun hh => hvD hh.1⟩
  have e2 : ∀ y : V, (G.holeFamilyRest U F).filter
      (fun v => v ∉ G.closedNeighborhood y) =
        G.holeFamilyRest (U.filter fun v => v ∉ G.closedNeighborhood y) F :=
    fun y => holeFamilyRest_filter U F _
  rw [h, e1]
  simp only [e2]


omit [DecidableEq V] in
/-- The families through a fixed hole `C ⊆ U` are `C` together with a family of holes
inside `U ∖ Γ[C]`. -/
theorem sum_holeFamilies_mem (ω : Set V → PowerSeries R) (w : V → R) {U : Finset V}
    {C : Set V} (hC : G.IsEvenHoleCarrier C) (hCU : C ⊆ (U : Set V)) :
    ∑ F ∈ (G.holeFamilies U).filter (fun F => C ∈ F),
        (∏ C' ∈ F, ω C') * indepSeries G w (G.holeFamilyRest U F) =
      ω C * G.holeSeries ω w (U.filter fun v => v ∉ G.openNeighborhood C) := by
  unfold holeSeries
  rw [Finset.mul_sum]
  refine Finset.sum_bij' (fun F _ => F.erase C) (fun F' _ => insert C F') ?_ ?_ ?_ ?_ ?_
  · intro F hF
    obtain ⟨hF1, hCF⟩ := Finset.mem_filter.1 hF
    obtain ⟨h1, h2⟩ := mem_holeFamilies.1 hF1
    refine mem_holeFamilies.2 ⟨fun C' hC' => ?_, ?_⟩
    · obtain ⟨hne, hC'F⟩ := Finset.mem_erase.1 hC'
      refine ⟨(h1 C' hC'F).1, fun v hv => ?_⟩
      have hcomp : G.EvenHoleInducedCompatible C' C := h2 hC'F hCF hne
      have hdisj := (evenHoleInducedCompatible_iff_disjoint_openNeighborhood_of_isEvenHoleCarrier
        hC).1 hcomp
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨(h1 C' hC'F).2 hv, fun hvN => Set.disjoint_left.1 hdisj hv hvN⟩)
    · intro a ha b hb hab
      exact h2 (Finset.mem_erase.1 ha).2 (Finset.mem_erase.1 hb).2 hab
  · intro F' hF'
    obtain ⟨h1, h2⟩ := mem_holeFamilies.1 hF'
    have hCF' : C ∉ F' := by
      intro hCF'
      obtain ⟨x, hx⟩ := hC.nonempty
      have := (h1 C hCF').2 hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at this
      exact this.2 (hC.subset_openNeighborhood hx)
    refine Finset.mem_filter.2 ⟨mem_holeFamilies.2 ⟨fun C' hC' => ?_, ?_⟩,
      Finset.mem_insert_self _ _⟩
    · rcases Finset.mem_insert.1 hC' with rfl | hC'
      · exact ⟨hC, hCU⟩
      · refine ⟨(h1 C' hC').1, fun v hv => ?_⟩
        have := (h1 C' hC').2 hv
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at this
        exact this.1
    · have hcompat : ∀ C' ∈ F', G.EvenHoleInducedCompatible C C' := by
        intro C' hC'
        have := (h1 C' hC').2
        have hdisj : Disjoint C' (G.openNeighborhood C) := by
          refine Set.disjoint_left.2 fun v hv hvN => ?_
          have := this hv
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at this
          exact this.2 hvN
        exact evenHoleInducedCompatible_comm.1
          ((evenHoleInducedCompatible_iff_disjoint_openNeighborhood_of_isEvenHoleCarrier
            hC).2 hdisj)
      intro a ha b hb hab
      rw [Finset.coe_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hcompat b hb
      · exact evenHoleInducedCompatible_comm.1 (hcompat a ha)
      · exact h2 ha hb hab
  · intro F hF
    exact Finset.insert_erase (Finset.mem_filter.1 hF).2
  · intro F' hF'
    obtain ⟨h1, h2⟩ := mem_holeFamilies.1 hF'
    have hCF' : C ∉ F' := by
      intro hCF'
      obtain ⟨x, hx⟩ := hC.nonempty
      have := (h1 C hCF').2 hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at this
      exact this.2 (hC.subset_openNeighborhood hx)
    exact Finset.erase_insert hCF'
  · intro F hF
    obtain ⟨hF1, hCF⟩ := Finset.mem_filter.1 hF
    have hprod : ∏ C' ∈ F, ω C' = ω C * ∏ C' ∈ F.erase C, ω C' :=
      (Finset.mul_prod_erase F ω hCF).symm
    have hrest : G.holeFamilyRest U F =
        G.holeFamilyRest (U.filter fun v => v ∉ G.openNeighborhood C) (F.erase C) := by
      ext v
      simp only [mem_holeFamilyRest, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hvU, hv⟩
        exact ⟨⟨hvU, hv C hCF⟩, fun C' hC' => hv C' hC'.2⟩
      · rintro ⟨⟨hvU, hvC⟩, hv⟩
        refine ⟨hvU, fun C' hC' => ?_⟩
        by_cases hCC : C' = C
        · exact hCC ▸ hvC
        · exact hv C' ⟨hCC, hC'⟩
    rw [hprod, hrest]
    ring


omit [Fintype V] in
/-- Two holes of a family that meet a clique `D` coincide (compatible holes cannot both
meet a clique). -/
theorem eq_of_mem_of_meets_clique {D : Finset V} (hD : G.IsClique (D : Set V))
    {F : Finset (Set V)} (hF : (F : Set (Set V)).Pairwise G.EvenHoleInducedCompatible)
    {C₀ C₁ : Set V} (h₀ : C₀ ∈ F) (h₁ : C₁ ∈ F) {d₀ d₁ : V} (hd₀ : d₀ ∈ D) (hd₁ : d₁ ∈ D)
    (hc₀ : d₀ ∈ C₀) (hc₁ : d₁ ∈ C₁) : C₀ = C₁ := by
  by_contra hne
  obtain ⟨hdisj, hnadj⟩ := hF h₀ h₁ hne
  by_cases hd : d₀ = d₁
  · subst hd
    exact Set.disjoint_left.1 hdisj hc₀ hc₁
  · exact hnadj hc₀ hc₁ (hD hd₀ hd₁ hd)

/-- The families avoiding `D`: the terms of `Z_U` that split along `D`. -/
theorem holeSeries_part0 (ω : Set V → PowerSeries R) (w : V → R) {D U : Finset V}
    (hD : G.IsClique (D : Set V)) (hDU : D ⊆ U) :
    ∑ F ∈ (G.holeFamilies U).filter (fun F => ∀ C ∈ F, ∀ d ∈ D, d ∉ C),
        (∏ C ∈ F, ω C) * indepSeries G w (G.holeFamilyRest U F) =
      G.holeSeries ω w (U.filter fun v => v ∉ D) -
        PowerSeries.X ^ 2 * ∑ y ∈ D, PowerSeries.C (w y) *
          G.holeSeries ω w (U.filter fun v => v ∉ G.closedNeighborhood y) := by
  have h1 : ∀ F ∈ (G.holeFamilies U).filter (fun F => ∀ C ∈ F, ∀ d ∈ D, d ∉ C),
      (∏ C ∈ F, ω C) * indepSeries G w (G.holeFamilyRest U F) =
        (∏ C ∈ F, ω C) * indepSeries G w (G.holeFamilyRest (U.filter fun v => v ∉ D) F) -
          PowerSeries.X ^ 2 * ∑ y ∈ D.filter (fun y => ∀ C ∈ F, y ∉ G.openNeighborhood C),
            (∏ C ∈ F, ω C) * (PowerSeries.C (w y) * indepSeries G w
              (G.holeFamilyRest (U.filter fun v => v ∉ G.closedNeighborhood y) F)) := by
    intro F _
    rw [indepSeries_holeFamilyRest_split w hD hDU F, mul_sub]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · unfold holeSeries
    rw [holeFamilies_filter_not_mem]
  · congr 1
    set S := (G.holeFamilies U).filter (fun F => ∀ C ∈ F, ∀ d ∈ D, d ∉ C) with hS
    rw [Finset.sum_congr rfl (fun F _ => Finset.sum_filter _ _), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [← Finset.sum_filter]
    have hfam : S.filter (fun F => ∀ C ∈ F, y ∉ G.openNeighborhood C) =
        G.holeFamilies (U.filter fun v => v ∉ G.closedNeighborhood y) := by
      rw [holeFamilies_filter_not_closedNeighborhood, hS, Finset.filter_filter]
      apply Finset.filter_congr
      intro F hF
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun C hC d hd hdC => ?_, h⟩
        by_cases hdy : d = y
        · exact h C hC (hdy ▸ ((mem_holeFamilies.1 hF).1 C hC).1.subset_openNeighborhood hdC)
        · have hadj : G.Adj y d := hD hy hd (Ne.symm hdy)
          exact h C hC ⟨d, hdC, hadj⟩
    rw [hfam]
    unfold holeSeries
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun F _ => by ring)


/-- The families meeting `D`: they are indexed by the unique hole meeting `D`. -/
theorem holeSeries_part1 (ω : Set V → PowerSeries R) (w : V → R) {D U : Finset V}
    (hD : G.IsClique (D : Set V)) :
    ∑ F ∈ (G.holeFamilies U).filter (fun F => ¬ ∀ C ∈ F, ∀ d ∈ D, d ∉ C),
        (∏ C ∈ F, ω C) * indepSeries G w (G.holeFamilyRest U F) =
      ∑ C ∈ G.holesMeeting U D, ω C *
        G.holeSeries ω w (U.filter fun v => v ∉ G.openNeighborhood C) := by
  set T : Finset (Set V) → PowerSeries R :=
    fun F => (∏ C ∈ F, ω C) * indepSeries G w (G.holeFamilyRest U F) with hT
  have hterm : ∀ C ∈ G.holesMeeting U D,
      ω C * G.holeSeries ω w (U.filter fun v => v ∉ G.openNeighborhood C) =
        ∑ F ∈ G.holeFamilies U, if C ∈ F then T F else 0 := by
    intro C hC
    obtain ⟨hC1, hC2, -⟩ := mem_holesMeeting.1 hC
    rw [← sum_holeFamilies_mem ω w hC1 hC2, Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun F hF => ?_)
  obtain ⟨h1, h2⟩ := mem_holeFamilies.1 hF
  by_cases hav : ∀ C ∈ F, ∀ d ∈ D, d ∉ C
  · rw [if_neg (not_not.2 hav)]
    refine (Finset.sum_eq_zero fun C hC => ?_).symm
    obtain ⟨-, -, d, hdD, hdC⟩ := mem_holesMeeting.1 hC
    rw [if_neg]
    intro hCF
    exact hav C hCF d hdD hdC
  · rw [if_pos hav]
    push Not at hav
    obtain ⟨C₀, hC₀F, d₀, hd₀D, hd₀C⟩ := hav
    have hC₀ : C₀ ∈ G.holesMeeting U D :=
      mem_holesMeeting.2 ⟨(h1 C₀ hC₀F).1, (h1 C₀ hC₀F).2, d₀, hd₀D, hd₀C⟩
    rw [Finset.sum_eq_single C₀]
    · rw [if_pos hC₀F]
    · intro C hC hne
      rw [if_neg]
      intro hCF
      obtain ⟨-, -, d, hdD, hdC⟩ := mem_holesMeeting.1 hC
      exact hne (eq_of_mem_of_meets_clique hD h2 hCF hC₀F hdD hd₀D hdC hd₀C)
    · intro h
      exact absurd hC₀ h

/-- **Clique splitting for the hole-weighted independence series.**  For a clique `D ⊆ U`,

`Z_U = Z_{U∖D} - X² ∑_{y ∈ D} w_y Z_{U∖Γ[y]} + ∑_{C} ω_C Z_{U∖Γ[C]}`,

the last sum over the even holes `C ⊆ U` meeting `D`.  For `ω = 0` this is
`indepSeries_clique_split`. -/
theorem holeSeries_split (ω : Set V → PowerSeries R) (w : V → R) {D U : Finset V}
    (hD : G.IsClique (D : Set V)) (hDU : D ⊆ U) :
    G.holeSeries ω w U = G.holeSeries ω w (U.filter fun v => v ∉ D) -
      PowerSeries.X ^ 2 * ∑ y ∈ D, PowerSeries.C (w y) *
        G.holeSeries ω w (U.filter fun v => v ∉ G.closedNeighborhood y) +
      ∑ C ∈ G.holesMeeting U D, ω C *
        G.holeSeries ω w (U.filter fun v => v ∉ G.openNeighborhood C) := by
  rw [← holeSeries_part0 ω w hD hDU, ← holeSeries_part1 ω w hD (U := U)]
  unfold holeSeries
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end HoleSeries


/-- A hole is triangle-free. -/
theorem IsEvenHoleCarrier.not_triangle {C : Set V} (hC : G.IsEvenHoleCarrier C) {a b c : V}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : G.Adj a b) (h2 : G.Adj a c) (h3 : G.Adj b c) : False := by
  obtain ⟨H, -, rfl⟩ := hC
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨l, rfl⟩ := hc
  have hij := (H.adj_iff i j).1 h1
  have hil := (H.adj_iff i l).1 h2
  have hjl := (H.adj_iff j l).1 h3
  have hne1 : i.val ≠ j.val := fun h => hab (by rw [Fin.ext h])
  have hne2 : i.val ≠ l.val := fun h => hac (by rw [Fin.ext h])
  have hne3 : j.val ≠ l.val := fun h => hbc (by rw [Fin.ext h])
  have hi := i.isLt
  have hj := j.isLt
  have hl := l.isLt
  have h4 := H.four_le_card
  unfold CyclicAdjacent at hij hil hjl
  omega

namespace RootedInducedPath

/-- A hole whose vertices avoid the path `Q` and the neighbours of its earlier vertices,
and which has a vertex `d` adjacent to the terminal vertex of `Q`, is attached to `Q`
(the neighbours of the terminal in the hole are exactly two adjacent vertices).  Claw-freeness
of `G*` at the terminal, with the predecessor and two hole neighbours as leaves, makes the
neighbours pairwise adjacent, hence at most two; claw-freeness of `G` at `d` produces a
second one.  For the root path the simplicial clique `K` meets the hole in `0` or `2`
vertices. -/
theorem holeAttached_of_meets (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C : Set V} (hC : G.IsEvenHoleCarrier C)
    (h1 : ∀ v ∈ C, some v ∉ Set.range Q.path.vertex)
    (h2 : ∀ p : Fin Q.path.card, p.val + 1 < Q.path.card → ∀ v ∈ C,
      ¬ (G.adjoinRootAt K).Adj (Q.path.vertex p) (some v))
    {d : V} (hdC : d ∈ C) (hd : (G.adjoinRootAt K).Adj Q.terminalVertex (some d)) :
    Q.HoleAttached C := by
  refine ⟨h1, h2, ?_⟩
  by_cases hc1 : Q.path.card = 1
  · have hQ := (eq_cliqueRootPath_iff Q).2 hc1
    subst hQ
    have hdK : d ∈ K := hd
    have hn := hK.ncard_inter_evenHoleCarrier hC
    have hn2 : (K ∩ C).ncard = 2 := by
      rcases hn with h | h
      · exfalso
        have hfin : (K ∩ C).Finite := hC.finite.subset Set.inter_subset_right
        have := (Set.ncard_eq_zero hfin).1 h
        exact (this ▸ (show d ∈ K ∩ C from ⟨hdK, hdC⟩) : d ∈ (∅ : Set V))
      · exact h
    obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.1 hn2
    have hx : x ∈ K ∩ C := hset ▸ Set.mem_insert _ _
    have hy : y ∈ K ∩ C := hset ▸ Set.mem_insert_of_mem _ rfl
    refine ⟨x, y, hx.2, hy.2, hK.isClique hx.1 hy.1 hxy, fun v hv => ?_⟩
    rw [terminalVertex_cliqueRootPath]
    change v ∈ K ↔ _
    constructor
    · intro hvK
      have : v ∈ K ∩ C := ⟨hvK, hv⟩
      rw [hset] at this
      exact this
    · rintro (rfl | rfl)
      · exact hx.1
      · exact hy.1
  · have hcard : 2 ≤ Q.path.card := by
      have := Q.path.nonempty
      omega
    obtain ⟨q, hq⟩ := Q.vertex_eq_some_of_pos ⟨Q.path.card - 1, by omega⟩ (by
      show 0 < Q.path.card - 1
      omega)
    have hqt : Q.terminalVertex = some q := hq
    set π : Option V := Q.path.vertex ⟨Q.path.card - 2, by omega⟩ with hπ
    have hπq : (G.adjoinRootAt K).Adj π (some q) := by
      rw [← hq]
      exact (Q.path.adj_iff _ _).2 (Or.inl (by simp only; omega))
    have hπC : ∀ v ∈ C, ¬ (G.adjoinRootAt K).Adj π (some v) :=
      h2 ⟨Q.path.card - 2, by omega⟩ (by simp only; omega)
    have hπne : ∀ v ∈ C, π ≠ some v := by
      intro v hv hπv
      exact h1 v hv ⟨_, hπv⟩
    have hqC : ∀ v ∈ C, q ≠ v := by
      intro v hv hqv
      exact h1 v hv ⟨⟨Q.path.card - 1, by omega⟩, by rw [hq, hqv]⟩
    rw [hqt] at hd
    have hqd : G.Adj q d := hd
    have hdq : G.Adj d q := hqd.symm
    have hclaw' := hK.isClawFree_adjoinRootAt hclaw
    -- the neighbours of `q` in `C` are pairwise adjacent
    have hpair : ∀ u ∈ C, ∀ v ∈ C, G.Adj q u → G.Adj q v → u ≠ v → G.Adj u v := by
      intro u hu v hv hqu hqv huv
      rcases hclaw' (center := some q) hπq.symm
          (show (G.adjoinRootAt K).Adj (some q) (some u) from hqu)
          (show (G.adjoinRootAt K).Adj (some q) (some v) from hqv) (hπne u hu) (hπne v hv)
          (fun h => huv (Option.some.inj h)) with h | h | h
      · exact absurd h (hπC u hu)
      · exact absurd h (hπC v hv)
      · exact h
    -- a second neighbour
    have hC0 := hC
    obtain ⟨H, -, hHC⟩ := hC
    obtain ⟨i, hi⟩ : d ∈ Set.range H.vertex := hHC ▸ hdC
    obtain ⟨u, v, huv, hiu, hiv, hnuv⟩ := H.exists_two_nonadjacent_neighbors i
    have hu : H.vertex u ∈ C := hHC ▸ ⟨u, rfl⟩
    have hv : H.vertex v ∈ C := hHC ▸ ⟨v, rfl⟩
    rw [hi] at hiu hiv
    have hexists : ∃ e ∈ C, G.Adj q e ∧ G.Adj d e := by
      rcases hclaw (center := d) hdq hiu hiv (hqC _ hu) (hqC _ hv)
          (fun h => huv (H.injective h)) with h | h | h
      · exact ⟨_, hu, h, hiu⟩
      · exact ⟨_, hv, h, hiv⟩
      · exact absurd h hnuv
    obtain ⟨e, heC, hqe, hde⟩ := hexists
    refine ⟨d, e, hdC, heC, hde, fun w hw => ?_⟩
    rw [hqt]
    constructor
    · intro hqw
      by_contra hcon
      push Not at hcon
      have hdw : G.Adj d w := hpair d hdC w hw hqd hqw (Ne.symm hcon.1)
      have hew : G.Adj e w := hpair e heC w hw hqe hqw (Ne.symm hcon.2)
      exact hC0.not_triangle hdC heC hw hde.ne hcon.1.symm hcon.2.symm hde hdw hew
    · rintro (rfl | rfl)
      · exact hqd
      · exact hqe


/-- The vertices `v` with `v ∉ N(Q)` or `v ∈ C(Q)`: `V ∖ N(P)` for the parent `P` of `Q`
(`columnDomain_eq_of_parent`), and all of `V` for the root path. -/
def columnDomain (Q : CliqueRootedInducedPath G K) : Set V :=
  {v | v ∉ Q.closedNbhd ∨ v ∈ Q.childCandidates}

theorem columnDomain_eq_of_parent {P Q : CliqueRootedInducedPath G K}
    (hPQ : P.IsOneVertexExtension Q) {q : V} (hq : Q.terminalVertex = some q) :
    Q.columnDomain = {v | v ∉ P.closedNbhd} := by
  obtain ⟨hN, hdisj⟩ := closedNbhd_eq_parent_union hPQ hq
  ext v
  simp only [columnDomain, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · intro hv
      exact h (hN ▸ Or.inl hv)
    · exact Set.disjoint_right.1 hdisj h
  · intro h
    by_cases hv : v ∈ Q.childCandidates
    · exact Or.inr hv
    · exact Or.inl (by
        rw [hN]
        rintro (h' | h')
        · exact h h'
        · exact hv h')

theorem columnDomain_cliqueRootPath :
    (cliqueRootPath G K).columnDomain = Set.univ := by
  ext v
  simp only [columnDomain, Set.mem_univ, iff_true, Set.mem_setOf_eq]
  rw [closedNbhd_cliqueRootPath, childCandidates_cliqueRootPath]
  exact (em (v ∈ K)).symm

/-- **Attachment criterion.**  An even hole `C` is attached to the rooted path `Q` iff it lies
in the column domain `V ∖ N(P)` of `Q` (`P` the parent of `Q`) and contains a child `d ∈ C(Q)`
of `Q`. -/
theorem holeAttached_iff (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (Q : CliqueRootedInducedPath G K) {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    Q.HoleAttached C ↔ C ⊆ Q.columnDomain ∧ ∃ d ∈ Q.childCandidates, d ∈ C := by
  by_cases hc1 : Q.path.card = 1
  · have hQ := (eq_cliqueRootPath_iff Q).2 hc1
    subst hQ
    rw [columnDomain_cliqueRootPath, childCandidates_cliqueRootPath]
    constructor
    · rintro ⟨-, -, x, y, hx, hy, hxy, hiff⟩
      refine ⟨Set.subset_univ _, x, ?_, hx⟩
      have := (hiff x hx).2 (Or.inl rfl)
      exact this
    · rintro ⟨-, d, hdK, hdC⟩
      refine holeAttached_of_meets hK hclaw hC ?_ ?_ hdC hdK
      · rintro v - ⟨i, hi⟩
        simp [cliqueRootPath] at hi
      · intro p hp
        exfalso
        have := p.isLt
        simp only [cliqueRootPath_card] at hp this
        omega
  · have hcard : 2 ≤ Q.path.card := by
      have := Q.path.nonempty
      omega
    obtain ⟨P, hPQ⟩ := exists_isOneVertexExtension_of_two_le Q hcard
    obtain ⟨q, hq⟩ := Q.vertex_eq_some_of_pos ⟨Q.path.card - 1, by omega⟩ (by
      show 0 < Q.path.card - 1
      omega)
    have hqt : Q.terminalVertex = some q := hq
    have hPcard := hPQ.card_eq
    rw [columnDomain_eq_of_parent hPQ hqt, childCandidates_eq_of_parent hPQ hqt]
    constructor
    · rintro ⟨h1, h2, x, y, hx, hy, hxy, hiff⟩
      have hdom : C ⊆ {v | v ∉ P.closedNbhd} := by
        intro v hv hvN
        rcases hvN with hvK | hvU
        · have := h2 ⟨0, by omega⟩ (by simp only; omega) v hv
          rw [show Q.path.vertex ⟨0, by omega⟩ = none from Q.root_eq] at this
          exact this hvK
        · obtain ⟨p, ⟨i, hi⟩, hvp⟩ := Set.mem_iUnion₂.1 hvU
          have hiQ : Q.path.vertex ⟨i.val, by omega⟩ = some p := by
            rw [hPQ.vertex_of_lt (j := ⟨i.val, by omega⟩) i.isLt]
            exact hi
          rcases hvp with rfl | hvp
          · exact h1 v hv ⟨_, hiQ⟩
          · refine h2 ⟨i.val, by omega⟩ (by simp only; omega) v hv ?_
            rw [hiQ]
            exact (G.mem_neighborSet _ _).1 hvp
      refine ⟨hdom, x, ⟨?_, hdom hx⟩, hx⟩
      have := (hiff x hx).2 (Or.inl rfl)
      rw [hqt] at this
      exact (G.mem_neighborSet _ _).2 this
    · rintro ⟨hdom, d, ⟨hdq, -⟩, hdC⟩
      refine holeAttached_of_meets hK hclaw hC ?_ ?_ hdC ?_
      · rintro v hv ⟨i, hi⟩
        by_cases hip : i.val < P.path.card
        · rw [hPQ.vertex_of_lt (j := i) hip] at hi
          exact hdom hv (P.mem_closedNbhd_of_vertex_eq _ hi)
        · have hiq : i = ⟨Q.path.card - 1, by omega⟩ :=
            Fin.ext (by have := i.isLt; simp only; omega)
          rw [hiq, hq] at hi
          have hvq : q = v := Option.some.inj hi
          exact hdom hv (hvq ▸ hPQ.mem_closedNbhd_terminal hqt)
      · intro p hp v hv hadj
        have hpP : p.val < P.path.card := by omega
        rw [hPQ.vertex_of_lt (j := p) hpP] at hadj
        exact hdom hv (P.mem_closedNbhd_of_adj ⟨p.val, hpP⟩ hadj)
      · rw [hqt]
        exact (G.mem_neighborSet _ _).1 hdq

end RootedInducedPath


namespace CliqueBubbleWand

variable {P : CliqueRootedInducedPath G K}

/-- The hoop carrier of a wand with an even hoop is an even-hole carrier. -/
theorem isEvenHoleCarrier_hoopCarrier (w : CliqueBubbleWand G K P) (he : Even w.hoopCard) :
    G.IsEvenHoleCarrier w.hoopCarrier :=
  ⟨w.hoopHole, by rw [w.hoopHole_card]; exact he, w.range_hoopHole⟩

/-- **The closed neighbourhood of the source of a wand.**  In a claw-free graph,
`N(P) = N(P_s) ∪ Γ[C]` for a wand `w` on `P` with handle `P_s` and an even hoop `C`:
the vertices of `P` outside the handle lie in the hoop, and `Γ[j] ⊆ N(P)` for the bubble
(`closedNeighborhood_bubble_subset`). -/
theorem closedNbhd_eq_handle_union (hclaw : G.IsClawFree) (w : CliqueBubbleWand G K P)
    (he : Even w.hoopCard) :
    P.closedNbhd = w.handle.closedNbhd ∪ G.openNeighborhood w.hoopCarrier := by
  have hC := w.isEvenHoleCarrier_hoopCarrier he
  have hhoop : ∀ v, v ∈ w.hoopCarrier ↔
      (v ∈ P.originalCarrier ∧ v ∉ w.handle.originalCarrier) ∨ v = w.bubble := by
    intro v
    rw [w.hoopCarrier_eq]
    exact Iff.rfl
  ext x
  constructor
  · rintro (hxK | hx)
    · exact Or.inl (Or.inl hxK)
    · obtain ⟨v, hvP, hxv⟩ := Set.mem_iUnion₂.1 hx
      by_cases hvh : v ∈ w.handle.originalCarrier
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨v, hvh, hxv⟩))
      · refine Or.inr ?_
        have hvC : v ∈ w.hoopCarrier := (hhoop v).2 (Or.inl ⟨hvP, hvh⟩)
        rcases hxv with rfl | hxv
        · exact hC.subset_openNeighborhood hvC
        · exact ⟨v, hvC, ((G.mem_neighborSet _ _).1 hxv).symm⟩
  · rintro (hx | ⟨v, hvC, hxv⟩)
    · rcases hx with hxK | hx
      · exact Or.inl hxK
      · obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.1 hx
        exact P.closedNeighborhood_subset_closedNbhd (w.handle_originalCarrier_subset hv) hxv
    · rcases (hhoop v).1 hvC with ⟨hvP, -⟩ | rfl
      · exact P.closedNeighborhood_subset_closedNbhd hvP (Or.inr ((G.mem_neighborSet _ _).2 hxv.symm))
      · exact closedNeighborhood_bubble_subset hclaw w (Or.inr ((G.mem_neighborSet _ _).2 hxv.symm))

/-- The number of original vertices: `|P| = |Q| + 2k - 1` for a wand with handle `Q` and an
even hoop with `2k` vertices (`P.path.card` counts the root). -/
theorem path_card_eq (w : CliqueBubbleWand G K P) :
    P.path.card = w.handle.path.card - 1 + w.hoopCard := by
  have := w.gap
  simp only [handle_card, hoopCard]
  omega


end CliqueBubbleWand

/-! ### Wand events and attached holes, summed -/

section Events

open Classical

variable [Fintype V] [DecidableEq V]

/-- The wand events `(P, j)` with handle `Q` and an even hoop. -/
noncomputable def holeEvents (G : SimpleGraph V) (K : Set V) (Q : CliqueRootedInducedPath G K) :
    Finset (CliqueRootedInducedPath G K × V) :=
  Finset.univ.filter fun e => ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
    Even w.hoopCard

/-- The even holes attached to `Q`. -/
noncomputable def attachedHoles (G : SimpleGraph V) (K : Set V)
    (Q : CliqueRootedInducedPath G K) : Finset (Set V) :=
  Finset.univ.filter fun C => G.IsEvenHoleCarrier C ∧ Q.HoleAttached C

omit [DecidableEq V] in
theorem mem_attachedHoles {Q : CliqueRootedInducedPath G K} {C : Set V} :
    C ∈ attachedHoles G K Q ↔ G.IsEvenHoleCarrier C ∧ Q.HoleAttached C := by
  simp [attachedHoles]

/-- **The events of a handle are twice the attached holes.**  For a function `h` of the hoop
carrier that is constant on deformation classes of even holes,
`∑_{events (P, j) with handle Q} h(C_{P,j}) = 2 ∑_{holes C attached to Q} h(C)`.
This is the fibrewise form (summed class by class) of `card_evenHoopEvents`. -/
theorem sum_holeEvents {M : Type*} [AddCommMonoid M] (Q : CliqueRootedInducedPath G K)
    (h : Set V → M)
    (hinv : ∀ C C' : Set V, G.IsEvenHoleCarrier C →
      G.evenHoleDeformationClassOf C = G.evenHoleDeformationClassOf C' → h C = h C') :
    ∑ e ∈ holeEvents G K Q, h (bubbleWandArcHoopCarrier e.1 Q e.2) =
      2 • ∑ C ∈ attachedHoles G K Q, h C := by
  haveI : Fintype (EvenHoleDeformationClass G) := Fintype.ofFinite _
  set φ : CliqueRootedInducedPath G K × V → Set V :=
    fun e => bubbleWandArcHoopCarrier e.1 Q e.2 with hφ
  rw [← Finset.sum_fiberwise (holeEvents G K Q) (fun e => G.evenHoleDeformationClassOf (φ e)),
    ← Finset.sum_fiberwise (attachedHoles G K Q) (fun C => G.evenHoleDeformationClassOf C),
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  -- the fibre of events over the class `c` and the card statement of C14
  have hcard := card_evenHoopEvents Q c
  have hEv : (holeEvents G K Q).filter (fun e => G.evenHoleDeformationClassOf (φ e) = c) =
      Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c := by
    ext e
    simp only [holeEvents, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨w, hb, hh, hev⟩, hc⟩
      refine ⟨w, hb, hh, hev, ?_⟩
      rw [← hc, hφ]
      simp only
      rw [bubbleWandArcHoopCarrier_eq_hoopCarrier w hb hh]
    · rintro ⟨w, hb, hh, hev, hc⟩
      refine ⟨⟨w, hb, hh, hev⟩, ?_⟩
      rw [← hc, hφ]
      simp only
      rw [bubbleWandArcHoopCarrier_eq_hoopCarrier w hb hh]
  have hHs : (attachedHoles G K Q).filter (fun C => G.evenHoleDeformationClassOf C = c) =
      Finset.univ.filter fun C : Set V => G.IsEvenHoleCarrier C ∧
        G.evenHoleDeformationClassOf C = c ∧ Q.HoleAttached C := by
    ext C
    simp only [attachedHoles, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [← hEv, ← hHs] at hcard
  by_cases hne : ((attachedHoles G K Q).filter
      (fun C => G.evenHoleDeformationClassOf C = c)).Nonempty
  · obtain ⟨C₀, hC₀⟩ := hne
    obtain ⟨hC₀mem, hC₀c⟩ := Finset.mem_filter.1 hC₀
    have h1 : ∀ e ∈ (holeEvents G K Q).filter
        (fun e => G.evenHoleDeformationClassOf (φ e) = c), h (φ e) = h C₀ := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
      obtain ⟨w, hb, hh, hev⟩ := (Finset.mem_filter.1 he1).2
      have hcar : φ e = w.hoopCarrier := bubbleWandArcHoopCarrier_eq_hoopCarrier w hb hh
      rw [hcar] at he2 ⊢
      exact hinv _ _ (w.isEvenHoleCarrier_hoopCarrier hev) (he2.trans hC₀c.symm)
    have h2 : ∀ C ∈ (attachedHoles G K Q).filter
        (fun C => G.evenHoleDeformationClassOf C = c), h C = h C₀ := by
      intro C hC
      obtain ⟨hC1, hC2⟩ := Finset.mem_filter.1 hC
      exact hinv _ _ (mem_attachedHoles.1 hC1).1 (hC2.trans hC₀c.symm)
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
      hcard, mul_nsmul, smul_comm]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hcard ⊢
    simp only [Finset.card_empty, mul_zero, Finset.card_eq_zero] at hcard
    rw [hcard]
    simp

end Events



/-! ### The column recursion for the hole-weighted row target -/

section Column

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w}

/-- The children `C(Q)` of a rooted path as a finset. -/
noncomputable def holeColumnChildren (Q : CliqueRootedInducedPath G K) : Finset V :=
  Finset.univ.filter fun x => x ∈ Q.childCandidates

/-- The column domain `V ∖ N(P)` (`P` the parent of `Q`; `V` for the root) as a finset. -/
noncomputable def holeColumnDomain (Q : CliqueRootedInducedPath G K) : Finset V :=
  Finset.univ.filter fun x => x ∈ Q.columnDomain

omit [DecidableEq V] in
theorem mem_holeColumnChildren {Q : CliqueRootedInducedPath G K} {x : V} :
    x ∈ holeColumnChildren Q ↔ x ∈ Q.childCandidates := by
  simp [holeColumnChildren]

omit [DecidableEq V] in
theorem mem_holeColumnDomain {Q : CliqueRootedInducedPath G K} {x : V} :
    x ∈ holeColumnDomain Q ↔ x ∈ Q.columnDomain := by
  simp [holeColumnDomain]

omit [DecidableEq V] in
theorem sum_children_subtype {S : Type*} [AddCommMonoid S]
    (Q : CliqueRootedInducedPath G K) (F : V → S) :
    ∑ x : Q.childCandidates, F x = ∑ x ∈ holeColumnChildren Q, F x :=
  (Finset.sum_subtype (holeColumnChildren Q) (p := fun x => x ∈ Q.childCandidates)
    (fun _ => mem_holeColumnChildren) F).symm

/-- The row target `r_Q = X^{|Q|-1} Z_{V ∖ N(Q)}` with the hole-weighted series
`Z = holeSeries ω b²`. -/
noncomputable def holeRowTarget [CommRing R] (G : SimpleGraph V) (K : Set V)
    (ω : Set V → PowerSeries R) (b : V → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries R :=
  PowerSeries.X ^ (Q.path.card - 1) *
    G.holeSeries ω (fun v => b v ^ 2) (Finset.univ.filter fun v => v ∉ Q.closedNbhd)

/-- The hole correction of the column `Q`: `∑_C ω_C Z_{D(Q) ∖ Γ[C]}` over the even holes `C`
inside the column domain that contain a child of `Q`. -/
noncomputable def holeColumnDefect [CommRing R] (G : SimpleGraph V) (K : Set V)
    (ω : Set V → PowerSeries R) (b : V → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries R :=
  ∑ C ∈ G.holesMeeting (holeColumnDomain Q) (holeColumnChildren Q), ω C *
    G.holeSeries ω (fun v => b v ^ 2)
      ((holeColumnDomain Q).filter fun v => v ∉ G.openNeighborhood C)

/-- **Column recursion of the tree part.**  For the hole-weighted series `Z`,
`r_Q = [Q = {j*}] Z_V + X ∑_P T_{PQ} r_P - X^{|Q|-1} · (hole correction)`.
Without holes (`ω = 0`) the correction vanishes and this is `krylovRowTarget_column`. -/
theorem holeRowTarget_tree_column [CommRing R] [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (ω : Set V → PowerSeries R)
    (b : V → R) (Q : CliqueRootedInducedPath G K) :
    holeRowTarget G K ω b Q =
      (if Q = cliqueRootPath G K then
          G.holeSeries ω (fun v => b v ^ 2) Finset.univ else 0) +
        PowerSeries.X * ∑ P : CliqueRootedInducedPath G K,
          PowerSeries.C (cliqueTreeMatrix G K b P Q) * holeRowTarget G K ω b P -
        PowerSeries.X ^ (Q.path.card - 1) * holeColumnDefect G K ω b Q := by
  rw [sum_cliqueTreeMatrix_column PowerSeries.C b Q]
  by_cases hroot : Q = cliqueRootPath G K
  · subst hroot
    rw [if_pos rfl]
    have hpar : ∑ P : CliqueRootedInducedPath G K,
        (if P.IsOneVertexExtension (cliqueRootPath G K) then
          holeRowTarget G K ω b P else 0) = 0 :=
      Finset.sum_eq_zero fun P _ =>
        if_neg (RootedInducedPath.not_isOneVertexExtension_cliqueRootPath P)
    rw [hpar, zero_add]
    have hterm : ∀ x : (cliqueRootPath G K).childCandidates,
        PowerSeries.C (b x ^ 2) *
            holeRowTarget G K ω b ((cliqueRootPath G K).appendTerminal x.2) =
          PowerSeries.C (b x ^ 2) * (PowerSeries.X *
            G.holeSeries ω (fun v => b v ^ 2)
              (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x))) := by
      intro x
      unfold holeRowTarget
      rw [closedNbhd_appendTerminal_cliqueRootPath hK.isClique x.2]
      have hc : ((cliqueRootPath G K).appendTerminal x.2).path.card - 1 = 1 := rfl
      rw [hc, pow_one]
    rw [Finset.sum_congr rfl (fun x _ => hterm x),
      sum_children_subtype (cliqueRootPath G K) (fun x => PowerSeries.C (b x ^ 2) *
        (PowerSeries.X * G.holeSeries ω (fun v => b v ^ 2)
          (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x))))]
    have hD : G.IsClique (holeColumnChildren (cliqueRootPath G K) : Set V) := by
      have := RootedInducedPath.childCandidates_isClique hK hclaw (cliqueRootPath G K)
      convert this using 1
      ext x
      simp [mem_holeColumnChildren]
    have hU : holeColumnDomain (cliqueRootPath G K) = Finset.univ := by
      ext x
      simp [mem_holeColumnDomain, RootedInducedPath.columnDomain_cliqueRootPath]
    have hsplit := holeSeries_split ω (fun v => b v ^ 2) hD
      (Finset.subset_univ (holeColumnChildren (cliqueRootPath G K)))
    have hUD : Finset.univ.filter (fun v => v ∉ holeColumnChildren (cliqueRootPath G K)) =
        Finset.univ.filter (fun v => v ∉ (cliqueRootPath G K).closedNbhd) := by
      ext v
      simp [mem_holeColumnChildren, childCandidates_cliqueRootPath,
        RootedInducedPath.closedNbhd_cliqueRootPath]
    have hS : ∑ x ∈ holeColumnChildren (cliqueRootPath G K), PowerSeries.C (b x ^ 2) *
        (PowerSeries.X * G.holeSeries ω (fun v => b v ^ 2)
          (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x))) =
        PowerSeries.X * ∑ x ∈ holeColumnChildren (cliqueRootPath G K),
          PowerSeries.C (b x ^ 2) * G.holeSeries ω (fun v => b v ^ 2)
            (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hS]
    unfold holeColumnDefect
    rw [hU]
    rw [hUD] at hsplit
    unfold holeRowTarget
    simp only [cliqueRootPath_card, Nat.sub_self, pow_zero, one_mul]
    linear_combination (-1 : PowerSeries R) * hsplit
  · have h2 : 2 ≤ Q.path.card := by
      have h1 : Q.path.card ≠ 1 := fun h =>
        hroot ((RootedInducedPath.eq_cliqueRootPath_iff Q).2 h)
      have := Q.path.nonempty
      omega
    obtain ⟨P0, hP0⟩ := RootedInducedPath.exists_isOneVertexExtension_of_two_le Q h2
    obtain ⟨q, hq⟩ := Q.vertex_eq_some_of_pos ⟨Q.path.card - 1, by omega⟩
      (by simp only; omega)
    have hqt : Q.terminalVertex = some q := hq
    rw [if_neg hroot, zero_add]
    have hpar : ∑ P : CliqueRootedInducedPath G K,
        (if P.IsOneVertexExtension Q then holeRowTarget G K ω b P else 0) =
          holeRowTarget G K ω b P0 := by
      rw [Finset.sum_eq_single P0]
      · exact if_pos hP0
      · intro P _ hP
        exact if_neg fun h => hP (h.eq_of_right hP0)
      · intro h
        exact absurd (Finset.mem_univ P0) h
    rw [hpar]
    obtain ⟨hNQ, hdisj⟩ := RootedInducedPath.closedNbhd_eq_parent_union hP0 hqt
    obtain ⟨m, hm⟩ : ∃ m, Q.path.card = m + 2 := ⟨Q.path.card - 2, by omega⟩
    have hP0card : P0.path.card = m + 1 := by
      have := hP0.card_eq
      omega
    have hU : holeColumnDomain Q = Finset.univ.filter (fun v => v ∉ P0.closedNbhd) := by
      ext v
      simp [mem_holeColumnDomain, RootedInducedPath.columnDomain_eq_of_parent hP0 hqt]
    have hterm : ∀ x : Q.childCandidates,
        PowerSeries.C (b x ^ 2) * holeRowTarget G K ω b (Q.appendTerminal x.2) =
          PowerSeries.C (b x ^ 2) * (PowerSeries.X ^ (m + 2) *
            G.holeSeries ω (fun v => b v ^ 2)
              ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
                (fun v => v ∉ G.closedNeighborhood x))) := by
      intro x
      unfold holeRowTarget
      rw [RootedInducedPath.closedNbhd_appendTerminal hK hclaw hP0 hqt x.2]
      have hc : (Q.appendTerminal x.2).path.card - 1 = m + 2 := by
        change Q.path.card + 1 - 1 = m + 2
        omega
      rw [hc]
      congr 3
      ext v
      simp [not_or]
    rw [Finset.sum_congr rfl (fun x _ => hterm x),
      sum_children_subtype Q (fun x => PowerSeries.C (b x ^ 2) * (PowerSeries.X ^ (m + 2) *
        G.holeSeries ω (fun v => b v ^ 2)
          ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
            (fun v => v ∉ G.closedNeighborhood x))))]
    have hD : G.IsClique (holeColumnChildren Q : Set V) := by
      have := RootedInducedPath.childCandidates_isClique hK hclaw Q
      convert this using 1
      ext x
      simp [mem_holeColumnChildren]
    have hDU : holeColumnChildren Q ⊆ holeColumnDomain Q := by
      intro x hx
      rw [mem_holeColumnDomain]
      exact Or.inr (mem_holeColumnChildren.1 hx)
    have hsplit := holeSeries_split ω (fun v => b v ^ 2) hD hDU
    have hUD : (holeColumnDomain Q).filter (fun v => v ∉ holeColumnChildren Q) =
        Finset.univ.filter (fun v => v ∉ Q.closedNbhd) := by
      rw [hU]
      ext v
      simp [mem_holeColumnChildren, hNQ, not_or]
    have hSx : ∀ y ∈ holeColumnChildren Q,
        (holeColumnDomain Q).filter (fun v => v ∉ G.closedNeighborhood y) =
          (Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
            (fun v => v ∉ G.closedNeighborhood y) := by
      intro y _
      rw [hU]
    rw [hUD, Finset.sum_congr rfl (fun y hy => by rw [hSx y hy])] at hsplit
    have hS : ∑ x ∈ holeColumnChildren Q, PowerSeries.C (b x ^ 2) *
        (PowerSeries.X ^ (m + 2) * G.holeSeries ω (fun v => b v ^ 2)
          ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
            (fun v => v ∉ G.closedNeighborhood x))) =
        PowerSeries.X ^ (m + 2) * ∑ x ∈ holeColumnChildren Q, PowerSeries.C (b x ^ 2) *
          G.holeSeries ω (fun v => b v ^ 2)
            ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
              (fun v => v ∉ G.closedNeighborhood x)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hS]
    unfold holeRowTarget
    rw [hm, hP0card]
    have e1 : m + 2 - 1 = m + 1 := rfl
    have e2 : m + 1 - 1 = m := rfl
    rw [e1, e2]
    unfold holeColumnDefect
    rw [hU] at hsplit ⊢
    linear_combination (-(PowerSeries.X : PowerSeries R) ^ (m + 1)) * hsplit

end Column

/-! ### The sector series and the hoop part of the column recursion -/

section Sector

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]

/-- The sector value of one hole: `2 (-X²)^{|C|/2} λ_{⟨C⟩} / |⟨C⟩|`.  A hole of the class
`c` enters `Z` through the class eigenvalue `λ_c` of `J_c = ∑_{C ∈ c} h_C` shared equally by
the `|c|` holes of the class.  This is the sector value of `h_C` only when `|c|` is invertible in
`R` (e.g. `[CharZero R]`); if `char R` divides `|c|` then `λ_c/|c| = 0` in Lean. -/
noncomputable def sectorHoleWeight (G : SimpleGraph V) (lam : EvenHoleDeformationClass G → R)
    (C : Set V) : PowerSeries R :=
  PowerSeries.C (2 * lam (G.evenHoleDeformationClassOf C) /
      (evenHoleClassSize (G.evenHoleDeformationClassOf C) : R)) *
    (-(PowerSeries.X ^ 2)) ^ (C.ncard / 2)

/-- **The sector independence series** `Z_U`:

`Z_U = ∑_{𝒳} ∏_{C ∈ 𝒳} (2 (-X²)^{|C|/2} λ_{⟨C⟩}/|⟨C⟩|) · I_{U ∖ Γ[𝒳]}(-X²)`,

the sum over the families `𝒳` of pairwise compatible even holes inside `U` (in the sense of v1
L313), `I` the weighted independence series with weights `w`.

*Relation to v1.*  `Z_U` is the sector reduction (`J_c ↦ λ_c`) of the generalized characteristic
polynomial `Z_{G[U]}` of v1 Lemma 11 (`generalizedcharacteristicpolynomial`, L1266-1271) only
when `U` contains all or none of the holes of each deformation class (this is the case for `V`
and for `V ∖ N(Q)`, `subset_compl_closedNbhd_iff_of_closure`) and when `|⟨C⟩|` is invertible in
`R` (e.g. `[CharZero R]`; if `char R` divides `|c|` the weight `λ_c/|c|` is `0` in Lean).  For
other `U` it is only a bookkeeping series with the per-hole weights `λ_c/|c|`, which differs
from the class-level polynomial.  See the module docstring. -/
noncomputable def sectorIndepSeries (G : SimpleGraph V) (w : V → R)
    (lam : EvenHoleDeformationClass G → R) (U : Finset V) : PowerSeries R :=
  G.holeSeries (sectorHoleWeight G lam) w U


/-- The weight `(-1)^{k-1} λ_c / |c|` of one wand event with hoop carrier `C` (`|C| = 2k`,
`c = ⟨C⟩`): the summand of `cliqueHoppingMatrix`. -/
noncomputable def hoopEventWeight (G : SimpleGraph V) (lam : EvenHoleDeformationClass G → R)
    (C : Set V) : R :=
  (-1 : R) ^ (C.ncard / 2 - 1) * lam (G.evenHoleDeformationClassOf C) /
    (evenHoleClassSize (G.evenHoleDeformationClassOf C) : R)

/-- The hoop part of the entry `A_λ(P, Q) - T(P, Q)`, as a sum over the bubbles. -/
theorem cliqueHoppingMatrix_sub_tree (b : V → R) (lam : EvenHoleDeformationClass G → R)
    (P Q : CliqueRootedInducedPath G K) :
    cliqueHoppingMatrix G K b lam P Q - cliqueTreeMatrix G K b P Q =
      ∑ j : V, if ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧
          Even w.hoopCard then
        hoopEventWeight G lam (bubbleWandArcHoopCarrier P Q j) else 0 := by
  unfold cliqueHoppingMatrix hoopEventWeight
  rw [add_sub_cancel_left]

/-- The hoop part of a column, summed against `f`, is a sum over the wand events. -/
theorem sum_hoopEntry_mul {S : Type*} [CommRing S] (φ : R →+* S) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K)
    (f : CliqueRootedInducedPath G K → S) :
    ∑ P : CliqueRootedInducedPath G K,
        φ (cliqueHoppingMatrix G K b lam P Q - cliqueTreeMatrix G K b P Q) * f P =
      ∑ e ∈ holeEvents G K Q,
        φ (hoopEventWeight G lam (bubbleWandArcHoopCarrier e.1 Q e.2)) * f e.1 := by
  simp only [cliqueHoppingMatrix_sub_tree, map_sum, Finset.sum_mul]
  rw [← Fintype.sum_prod_type' (fun (P : CliqueRootedInducedPath G K) (j : V) =>
    φ (if ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧ Even w.hoopCard then
        hoopEventWeight G lam (bubbleWandArcHoopCarrier P Q j) else 0) * f P)]
  unfold holeEvents
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs <;> simp

end Sector

/-! ### The hoop part of the column recursion -/

section HoopColumn

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]

omit [DecidableEq V] in
/-- The target of a wand source in terms of the handle and the hoop: `|P| - 1 = |Q| - 1 +
(|C| - 1)` and `N(P) = N(Q) ∪ Γ[C]`. -/
theorem holeRowTarget_of_wand (hclaw : G.IsClawFree) (ω : Set V → PowerSeries R) (b : V → R)
    {P Q : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P) (hh : w.handle = Q)
    (he : Even w.hoopCard) :
    holeRowTarget G K ω b P =
      PowerSeries.X ^ (Q.path.card - 1 + (w.hoopCarrier.ncard - 1)) *
        G.holeSeries ω (fun v => b v ^ 2)
          ((Finset.univ.filter fun v => v ∉ Q.closedNbhd).filter
            fun v => v ∉ G.openNeighborhood w.hoopCarrier) := by
  unfold holeRowTarget
  have hcard := w.path_card_eq
  rw [hh] at hcard
  have hn := w.hoopCarrier_ncard
  have h4 := w.four_le_hoopCard
  have hexp : P.path.card - 1 = Q.path.card - 1 + (w.hoopCarrier.ncard - 1) := by omega
  rw [hexp]
  congr 2
  rw [w.closedNbhd_eq_handle_union hclaw he, hh]
  ext v
  simp [not_or]

/-- The ingredients of one hoop term: the term of a hole `C` in the sum over wand events. -/
noncomputable def hoopColumnTerm (G : SimpleGraph V) (K : Set V) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K) (C : Set V) :
    PowerSeries R :=
  PowerSeries.C (hoopEventWeight G lam C) *
    (PowerSeries.X ^ (Q.path.card - 1 + (C.ncard - 1)) *
      G.holeSeries (sectorHoleWeight G lam) (fun v => b v ^ 2)
        ((Finset.univ.filter fun v => v ∉ Q.closedNbhd).filter
          fun v => v ∉ G.openNeighborhood C))

theorem hoopColumnTerm_invariant (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K)
    (C C' : Set V) (hcl : G.evenHoleDeformationClassOf C = G.evenHoleDeformationClassOf C') :
    hoopColumnTerm G K b lam Q C = hoopColumnTerm G K b lam Q C' := by
  have hclo : InEvenHoleDeformationClosure G C C' := evenHoleDeformationClassOf_eq_iff.1 hcl
  have hn : C.ncard = C'.ncard := hclo.ncard_eq
  have hN : G.openNeighborhood C = G.openNeighborhood C' := hclo.openNeighborhood_eq hclaw
  unfold hoopColumnTerm hoopEventWeight
  rw [hcl, hn, hN]


omit [DecidableEq V] in
theorem holesMeeting_eq_attachedHoles (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (Q : CliqueRootedInducedPath G K) :
    G.holesMeeting (holeColumnDomain Q) (holeColumnChildren Q) = attachedHoles G K Q := by
  ext C
  rw [mem_holesMeeting, mem_attachedHoles]
  constructor
  · rintro ⟨hC, hsub, d, hd, hdC⟩
    refine ⟨hC, (RootedInducedPath.holeAttached_iff hK hclaw Q hC).2
      ⟨fun v hv => mem_holeColumnDomain.1 (Finset.mem_coe.1 (hsub hv)), d,
        mem_holeColumnChildren.1 hd, hdC⟩⟩
  · rintro ⟨hC, hA⟩
    obtain ⟨hsub, d, hd, hdC⟩ := (RootedInducedPath.holeAttached_iff hK hclaw Q hC).1 hA
    exact ⟨hC, fun v hv => Finset.mem_coe.2 (mem_holeColumnDomain.2 (hsub hv)), d,
      mem_holeColumnChildren.2 hd, hdC⟩

omit [Fintype V] in
/-- The children of `Q` lie in `Γ[C]` for every hole `C` attached to `Q`: `C(Q)` is a clique
meeting `C`. -/
theorem childCandidates_subset_openNeighborhood (hK : G.IsSimplicialClique K)
    (hclaw : G.IsClawFree) {Q : CliqueRootedInducedPath G K} {C : Set V}
    (hC : G.IsEvenHoleCarrier C) (hA : Q.HoleAttached C) :
    Q.childCandidates ⊆ G.openNeighborhood C := by
  obtain ⟨-, d, hd, hdC⟩ := (RootedInducedPath.holeAttached_iff hK hclaw Q hC).1 hA
  intro v hv
  by_cases hvd : v = d
  · exact hC.subset_openNeighborhood (hvd ▸ hdC)
  · exact ⟨d, hdC, RootedInducedPath.childCandidates_isClique hK hclaw Q hv hd hvd⟩

theorem holeColumnDomain_filter_eq (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C : Set V} (hC : G.IsEvenHoleCarrier C)
    (hA : Q.HoleAttached C) :
    (holeColumnDomain Q).filter (fun v => v ∉ G.openNeighborhood C) =
      (Finset.univ.filter fun v => v ∉ Q.closedNbhd).filter
        fun v => v ∉ G.openNeighborhood C := by
  have hsub := childCandidates_subset_openNeighborhood hK hclaw hC hA
  ext v
  simp only [Finset.mem_filter, mem_holeColumnDomain, Finset.mem_univ, true_and,
    RootedInducedPath.columnDomain, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h | h, hv⟩
    · exact ⟨h, hv⟩
    · exact absurd (hsub h) hv
  · rintro ⟨h, hv⟩
    exact ⟨Or.inl h, hv⟩

/-- **The hoop part of the column recursion.**  For the sector series `Z`,
`X ∑_P (A_λ - T)_{PQ} r_P = - X^{|Q|-1} · (hole correction of the column `Q`)`: the sum over
the wand sources of the handle `Q` is twice the sum over the holes attached to `Q`
(`sum_holeEvents`), each with the weight `(-1)^{k-1} λ_c / |c|` and the target
`r_P = X^{|Q|+2k-2} Z_{V ∖ (N(Q) ∪ Γ[C])}`. -/
theorem holeRowTarget_hoop_column (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (b : V → R) (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries.X * ∑ P : CliqueRootedInducedPath G K,
        PowerSeries.C (cliqueHoppingMatrix G K b lam P Q - cliqueTreeMatrix G K b P Q) *
          holeRowTarget G K (sectorHoleWeight G lam) b P =
      -(PowerSeries.X ^ (Q.path.card - 1) *
        holeColumnDefect G K (sectorHoleWeight G lam) b Q) := by
  rw [sum_hoopEntry_mul PowerSeries.C b lam Q]
  have h1 : ∀ e ∈ holeEvents G K Q,
      PowerSeries.C (hoopEventWeight G lam (bubbleWandArcHoopCarrier e.1 Q e.2)) *
        holeRowTarget G K (sectorHoleWeight G lam) b e.1 =
      hoopColumnTerm G K b lam Q (bubbleWandArcHoopCarrier e.1 Q e.2) := by
    intro e he
    obtain ⟨w, hb, hh, hev⟩ := (Finset.mem_filter.1 he).2
    have hcar := bubbleWandArcHoopCarrier_eq_hoopCarrier w hb hh
    rw [hcar, holeRowTarget_of_wand hclaw _ b w hh hev]
    rfl
  rw [Finset.sum_congr rfl h1, sum_holeEvents Q (hoopColumnTerm G K b lam Q)
    (fun C C' _ hcl => hoopColumnTerm_invariant hclaw b lam Q C C' hcl)]
  unfold holeColumnDefect
  rw [holesMeeting_eq_attachedHoles hK hclaw Q, Finset.smul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun C hC => ?_)
  obtain ⟨hCh, hA⟩ := mem_attachedHoles.1 hC
  rw [holeColumnDomain_filter_eq hK hclaw hCh hA]
  obtain ⟨r, hr⟩ := hCh.even_ncard
  have h4 := hCh.four_le_ncard
  obtain ⟨k, hk⟩ : ∃ k, C.ncard = 2 * (k + 1) := ⟨r - 1, by omega⟩
  have e1 : C.ncard / 2 = k + 1 := by omega
  have e2 : C.ncard - 1 = 2 * k + 1 := by omega
  unfold hoopColumnTerm hoopEventWeight sectorHoleWeight
  rw [e1, e2, Nat.add_sub_cancel, mul_div_assoc, mul_div_assoc (2 : R)]
  simp only [map_mul, map_pow, map_neg, map_one, map_ofNat]
  rw [two_nsmul]
  ring

end HoopColumn

/-! ### The closed form -/

section Main

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]

/-- Column recursion for the powers of an arbitrary matrix: the row series
`s_Q = ∑_n X^n (M^n)_{r₀ Q}` satisfies `s_Q = [Q = r₀] + X ∑_P M_{PQ} s_P`. -/
theorem rowSeries_column {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (r₀ Q : ι) :
    PowerSeries.mk (fun n => (M ^ n) r₀ Q) =
      (if Q = r₀ then 1 else 0) +
        PowerSeries.X * ∑ P : ι, PowerSeries.C (M P Q) *
          PowerSeries.mk (fun n => (M ^ n) r₀ P) := by
  ext n
  cases n with
  | zero =>
      by_cases h : Q = r₀
      · subst h
        simp
      · simp [h, Ne.symm h]
  | succ n =>
      have h0 : PowerSeries.coeff (n + 1) (if Q = r₀ then (1 : PowerSeries R) else 0) = 0 := by
        split_ifs <;> simp
      rw [PowerSeries.coeff_mk, map_add, h0, zero_add, PowerSeries.coeff_succ_X_mul,
        map_sum, pow_succ, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]

/-- **Column recursion of the sector row target** `r_Q = X^{|Q|-1} Z_{V ∖ N(Q)}` for the matrix
`A_λ`:  `r_Q = [Q = {j*}] Z_V + X ∑_P (A_λ)_{PQ} r_P`. -/
theorem sectorRowTarget_column [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K) :
    holeRowTarget G K (sectorHoleWeight G lam) b Q =
      (if Q = cliqueRootPath G K then
          sectorIndepSeries G (fun v => b v ^ 2) lam Finset.univ else 0) +
        PowerSeries.X * ∑ P : CliqueRootedInducedPath G K,
          PowerSeries.C (cliqueHoppingMatrix G K b lam P Q) *
            holeRowTarget G K (sectorHoleWeight G lam) b P := by
  have ht := holeRowTarget_tree_column hK hclaw (sectorHoleWeight G lam) b Q
  have hh := holeRowTarget_hoop_column hK hclaw b lam Q
  have hsplit : ∀ P : CliqueRootedInducedPath G K,
      PowerSeries.C (cliqueHoppingMatrix G K b lam P Q) *
          holeRowTarget G K (sectorHoleWeight G lam) b P =
        PowerSeries.C (cliqueTreeMatrix G K b P Q) *
            holeRowTarget G K (sectorHoleWeight G lam) b P +
          PowerSeries.C (cliqueHoppingMatrix G K b lam P Q - cliqueTreeMatrix G K b P Q) *
            holeRowTarget G K (sectorHoleWeight G lam) b P := by
    intro P
    rw [← add_mul, ← map_add, add_sub_cancel]
  rw [Finset.sum_congr rfl (fun P _ => hsplit P), Finset.sum_add_distrib]
  unfold sectorIndepSeries
  linear_combination ht - hh

/-- **Closed form of the Krylov rows of `A_λ`** (sector polynomial, general case; not stated in
v1).  Let `G` be finite and claw-free, `K` a simplicial clique, `b : V → R`, and
`lam` any assignment of eigenvalues to the deformation classes of even holes.  Then, for
every rooted induced path `Q` of `G*`, in `R⟦X⟧`

`(∑_n X^n (A_λ^n)_{{j*},Q}) · Z_V = X^{|Q|-1} · Z_{V ∖ N(Q)}`,

where `A_λ = cliqueHoppingMatrix G K b lam` is the corrected matrix of Eq. (decoratedtree),
`Z_U = sectorIndepSeries G b² lam U` is the sector series of `G[U]`, and `N(Q)` the closed
neighbourhood of `Q`.  Without even holes `Z = I` and this is `krylovRow_mul_indepSeries`.
`R` is any field; `CharZero` is not needed for the identity.  `Z_V` and `Z_{V ∖ N(Q)}` are the
sector reductions of v1's `Z` (`J_c ↦ λ_c`) because `V` and `V ∖ N(Q)` contain all or none of the
holes of each class, provided `|c|` is invertible in `R` (e.g. `[CharZero R]`); when `char R`
divides some `|c|`, `λ_c/|c| = 0` in Lean, so `A_λ` has no hoop arcs for that class and `Z` has
no hole terms for it, and the identity is no longer the sector reduction of v1's `Z`. -/
theorem krylovRow_mul_sectorIndepSeries [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries.mk (fun n => ((cliqueHoppingMatrix G K b lam) ^ n) (cliqueRootPath G K) Q) *
        sectorIndepSeries G (fun v => b v ^ 2) lam Finset.univ =
      PowerSeries.X ^ (Q.path.card - 1) *
        sectorIndepSeries G (fun v => b v ^ 2) lam
          (Finset.univ.filter (fun v => v ∉ Q.closedNbhd)) := by
  set Z := sectorIndepSeries G (fun v => b v ^ 2) lam Finset.univ with hZ
  have key := eq_of_column_recursion (cliqueHoppingMatrix G K b lam)
    (fun Q => if Q = cliqueRootPath G K then Z else 0)
    (fun P => PowerSeries.mk (fun n =>
      ((cliqueHoppingMatrix G K b lam) ^ n) (cliqueRootPath G K) P) * Z)
    (holeRowTarget G K (sectorHoleWeight G lam) b)
    (by
      intro Q
      have h1 := rowSeries_column (cliqueHoppingMatrix G K b lam) (cliqueRootPath G K) Q
      have hite : (if Q = cliqueRootPath G K then (1 : PowerSeries R) else 0) * Z =
          if Q = cliqueRootPath G K then Z else 0 := by
        split_ifs <;> simp
      rw [h1, add_mul, hite, mul_assoc, Finset.sum_mul]
      congr 2
      refine Finset.sum_congr rfl fun P _ => ?_
      ring)
    (sectorRowTarget_column hK hclaw b lam)
  exact congrFun key Q

end Main

/-! ### The single-class case -/

section SingleClass

open Classical

variable [Fintype V] [DecidableEq V]

/-- The even holes inside `U`. -/
noncomputable def holesIn (G : SimpleGraph V) (U : Finset V) : Finset (Set V) :=
  Finset.univ.filter fun C => G.IsEvenHoleCarrier C ∧ C ⊆ (U : Set V)

omit [DecidableEq V] in
theorem mem_holesIn {U : Finset V} {C : Set V} :
    C ∈ G.holesIn U ↔ G.IsEvenHoleCarrier C ∧ C ⊆ (U : Set V) := by
  simp [holesIn]

omit [DecidableEq V] in
/-- If all even holes of `G` form one deformation class, the compatible families are the empty
family and the singletons: two holes of one class are never compatible. -/
theorem holeFamilies_of_single_class (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀)
    (hsingle : ∀ C, G.IsEvenHoleCarrier C → InEvenHoleDeformationClosure G C₀ C)
    (U : Finset V) :
    G.holeFamilies U = insert ∅ ((G.holesIn U).image fun C => ({C} : Finset (Set V))) := by
  ext F
  rw [mem_holeFamilies, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hF : F = ∅
    · exact Or.inl hF
    · right
      obtain ⟨C, hC⟩ := Finset.nonempty_iff_ne_empty.2 hF
      refine ⟨C, mem_holesIn.2 (h1 C hC), ?_⟩
      ext C'
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        exact hC
      · intro hC'
        by_contra hne
        exact not_evenHoleInducedCompatible_of_mem_closure hC₀ hclaw (hsingle C (h1 C hC).1)
          (hsingle C' (h1 C' hC').1) (h2 hC hC' (Ne.symm hne))
  · rintro (rfl | ⟨C, hC, rfl⟩)
    · exact ⟨fun C hC => absurd hC (Finset.notMem_empty C), by simp⟩
    · obtain ⟨hC1, hC2⟩ := mem_holesIn.1 hC
      refine ⟨fun C' hC' => ?_, by simp⟩
      rw [Finset.mem_singleton] at hC'
      subst hC'
      exact ⟨hC1, hC2⟩

variable {R : Type w} [CommRing R]

omit [DecidableEq V] in
/-- With a single class of holes, `Z_U = I_U + ∑_{C ⊆ U} ω_C I_{U ∖ Γ[C]}`: the compatible
families of holes are `∅` and the singletons. -/
theorem holeSeries_of_single_class (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀)
    (hsingle : ∀ C, G.IsEvenHoleCarrier C → InEvenHoleDeformationClosure G C₀ C)
    (ω : Set V → PowerSeries R) (w : V → R) (U : Finset V) :
    G.holeSeries ω w U = indepSeries G w U +
      ∑ C ∈ G.holesIn U, ω C * indepSeries G w (U.filter fun v => v ∉ G.openNeighborhood C) := by
  unfold holeSeries
  rw [holeFamilies_of_single_class hclaw hC₀ hsingle U, Finset.sum_insert, Finset.sum_image]
  · have h1 : G.holeFamilyRest U ∅ = U := by
      ext v
      simp [mem_holeFamilyRest]
    rw [h1, Finset.prod_empty, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [Finset.prod_singleton]
    congr 2
    ext v
    simp [mem_holeFamilyRest]
  · intro C _ C' _ h
    exact Finset.singleton_injective h
  · simp


omit [Fintype V] [DecidableEq V] in
/-- A hole lies outside `N(Q)` iff it avoids `K` and no vertex of `Q` is in `Γ[C]`. -/
theorem subset_compl_closedNbhd_iff {Q : CliqueRootedInducedPath G K} {C : Set V}
    (hC : G.IsEvenHoleCarrier C) :
    C ⊆ {v | v ∉ Q.closedNbhd} ↔
      Disjoint C K ∧ ∀ p ∈ Q.originalCarrier, p ∉ G.openNeighborhood C := by
  constructor
  · intro h
    refine ⟨Set.disjoint_left.2 fun v hv hvK => h hv (Q.subset_closedNbhd hvK), ?_⟩
    rintro p hp ⟨v, hv, hpv⟩
    exact h hv (Q.closedNeighborhood_subset_closedNbhd hp
      (Or.inr ((G.mem_neighborSet _ _).2 hpv)))
  · rintro ⟨hK', hp⟩ v hv hvN
    rcases hvN with hvK | hvU
    · exact Set.disjoint_left.1 hK' hv hvK
    · obtain ⟨p, hpQ, hvp⟩ := Set.mem_iUnion₂.1 hvU
      refine hp p hpQ ?_
      rcases hvp with rfl | hvp
      · exact hC.subset_openNeighborhood hv
      · exact ⟨v, hv, ((G.mem_neighborSet _ _).1 hvp)⟩

omit [Fintype V] [DecidableEq V] in
/-- **All or none.**  For a path `Q`, the holes of one deformation class are either all
inside `V ∖ N(Q)` or all outside: `Γ[C]` and the property `C ∩ K = ∅` are constant on a class
(v1 Lemma 4, `evenholeneighbor`, L736-739; repo `lemma9` /
`InEvenHoleDeformationClosure.openNeighborhood_eq`; and `disjoint_simplicial`). -/
theorem subset_compl_closedNbhd_iff_of_closure (hK : G.IsSimplicialClique K)
    (hclaw : G.IsClawFree) (Q : CliqueRootedInducedPath G K) {C C' : Set V}
    (hC : G.IsEvenHoleCarrier C) (hclo : InEvenHoleDeformationClosure G C C') :
    C ⊆ {v | v ∉ Q.closedNbhd} ↔ C' ⊆ {v | v ∉ Q.closedNbhd} := by
  have hC' : G.IsEvenHoleCarrier C' := hclo.isEvenHoleCarrier hC
  rw [subset_compl_closedNbhd_iff hC, subset_compl_closedNbhd_iff hC',
    ← hclo.openNeighborhood_eq hclaw]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hclo.disjoint_of_isSimplicialClique hK h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hclo.symm.disjoint_of_isSimplicialClique hK h1, h2⟩

variable {R : Type w} [Field R]

/-- **The sector series with a single class of holes.**  If all even holes of `G` lie in the
deformation class of `C₀`, then for every `U`

`Z_U = I_U + n_U · (2 λ_c (-X²)^k / |c|) · I_{U ∖ Γ[c]}`,

with `n_U` the number of holes inside `U`, `c = ⟨C₀⟩`, `2k = |C₀|` and `Γ[c] = Γ[C₀]`. -/
theorem sectorIndepSeries_of_single_class (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀)
    (hsingle : ∀ C, G.IsEvenHoleCarrier C → InEvenHoleDeformationClosure G C₀ C)
    (w : V → R) (lam : EvenHoleDeformationClass G → R) (U : Finset V) :
    sectorIndepSeries G w lam U = indepSeries G w U +
      ((G.holesIn U).card : PowerSeries R) * (sectorHoleWeight G lam C₀ *
        indepSeries G w (U.filter fun v => v ∉ G.openNeighborhood C₀)) := by
  unfold sectorIndepSeries
  rw [holeSeries_of_single_class hclaw hC₀ hsingle]
  congr 1
  have hterm : ∀ C ∈ G.holesIn U, sectorHoleWeight G lam C *
      indepSeries G w (U.filter fun v => v ∉ G.openNeighborhood C) =
      sectorHoleWeight G lam C₀ *
        indepSeries G w (U.filter fun v => v ∉ G.openNeighborhood C₀) := by
    intro C hC
    have hclo := hsingle C (mem_holesIn.1 hC).1
    have hcl : G.evenHoleDeformationClassOf C = G.evenHoleDeformationClassOf C₀ :=
      (evenHoleDeformationClassOf_eq_iff.2 hclo).symm
    unfold sectorHoleWeight
    rw [hcl, hclo.ncard_eq.symm, hclo.openNeighborhood_eq hclaw]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-- If every even hole lies inside `U` (for example `U = V`), the sector series with a single
class is `Z_U = I_U + 2 λ_c (-X²)^k I_{U ∖ Γ[c]}`, i.e. `I_U + 2 (-1)^k λ_c X^{2k} I_{U ∖ Γ[c]}`:
`n_U = |c|` cancels the normalisation `1/|c|` of the hole weights. -/
theorem sectorIndepSeries_of_single_class_of_all [CharZero R] (hclaw : G.IsClawFree)
    {C₀ : Set V} (hC₀ : G.IsEvenHoleCarrier C₀)
    (hsingle : ∀ C, G.IsEvenHoleCarrier C → InEvenHoleDeformationClosure G C₀ C)
    (w : V → R) (lam : EvenHoleDeformationClass G → R) {U : Finset V}
    (hall : ∀ C, G.IsEvenHoleCarrier C → C ⊆ (U : Set V)) :
    sectorIndepSeries G w lam U = indepSeries G w U +
      PowerSeries.C (2 * lam (G.evenHoleDeformationClassOf C₀)) *
        (-(PowerSeries.X ^ 2)) ^ (C₀.ncard / 2) *
          indepSeries G w (U.filter fun v => v ∉ G.openNeighborhood C₀) := by
  rw [sectorIndepSeries_of_single_class hclaw hC₀ hsingle]
  have hholes : G.holesIn U = G.deformationClosureFinset C₀ := by
    ext C
    rw [mem_holesIn, mem_deformationClosureFinset]
    exact ⟨fun h => hsingle C h.1, fun h => ⟨h.isEvenHoleCarrier hC₀, hall C (h.isEvenHoleCarrier hC₀)⟩⟩
  rw [hholes, ← evenHoleClassSize_classOf]
  have hs : (evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R) ≠ 0 :=
    Nat.cast_ne_zero.2 (evenHoleClassSize_pos _).ne'
  unfold sectorHoleWeight
  congr 1
  have : ((evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : ℕ) : PowerSeries R) =
      PowerSeries.C (evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R) := by simp
  rw [this, ← mul_assoc, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hs]

/-- If no even hole lies inside `U`, then `Z_U = I_U`. -/
theorem sectorIndepSeries_of_single_class_of_none (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀)
    (hsingle : ∀ C, G.IsEvenHoleCarrier C → InEvenHoleDeformationClosure G C₀ C)
    (w : V → R) (lam : EvenHoleDeformationClass G → R) {U : Finset V}
    (hnone : ∀ C, G.IsEvenHoleCarrier C → ¬ C ⊆ (U : Set V)) :
    sectorIndepSeries G w lam U = indepSeries G w U := by
  rw [sectorIndepSeries_of_single_class hclaw hC₀ hsingle]
  have : G.holesIn U = ∅ := by
    ext C
    simp only [mem_holesIn, Finset.notMem_empty, iff_false, not_and]
    exact hnone C
  rw [this]
  simp

end SingleClass

/-! ### Corollaries -/

section Corollaries

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]

/-- **Single-class closed form.**  If all even holes of `G` form one deformation class
`c = ⟨C₀⟩` (`|C₀| = 2k`), then for every rooted path `Q` of `G*`

`(∑_n X^n (A_λ^n)_{{j*},Q}) · (I_V + 2 λ_c (-X²)^k I_{V ∖ Γ[c]})
   = X^{|Q|-1} · (I_{V ∖ N(Q)} + [c ⊆ V ∖ N(Q)] · 2 λ_c (-X²)^k I_{V ∖ N(Q) ∖ Γ[c]})`,

where `[c ⊆ V ∖ N(Q)]` is `1` if the holes of `c` lie in `V ∖ N(Q)` (equivalently one of them
does, `subset_compl_closedNbhd_iff_of_closure`) and `0` otherwise, and `(-X²)^k = (-1)^k X^{2k}`.
This is the formula `Z_U = I_U + 2 (-1)^k λ X^{2k} I_{U ∖ Γ[c]}` (when the holes of `c` lie in `U`;
`Z_U = I_U` otherwise) of the work package. -/
theorem krylovRow_mul_indepSeries_single_class [CharZero R]
    [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀)
    (hsingle : ∀ C, G.IsEvenHoleCarrier C → InEvenHoleDeformationClosure G C₀ C)
    (b : V → R) (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries.mk (fun n => ((cliqueHoppingMatrix G K b lam) ^ n) (cliqueRootPath G K) Q) *
        (indepSeries G (fun v => b v ^ 2) Finset.univ +
          PowerSeries.C (2 * lam (G.evenHoleDeformationClassOf C₀)) *
            (-(PowerSeries.X ^ 2)) ^ (C₀.ncard / 2) *
              indepSeries G (fun v => b v ^ 2)
                (Finset.univ.filter fun v => v ∉ G.openNeighborhood C₀)) =
      PowerSeries.X ^ (Q.path.card - 1) *
        (indepSeries G (fun v => b v ^ 2) (Finset.univ.filter fun v => v ∉ Q.closedNbhd) +
          if C₀ ⊆ {v | v ∉ Q.closedNbhd} then
            PowerSeries.C (2 * lam (G.evenHoleDeformationClassOf C₀)) *
              (-(PowerSeries.X ^ 2)) ^ (C₀.ncard / 2) *
                indepSeries G (fun v => b v ^ 2)
                  ((Finset.univ.filter fun v => v ∉ Q.closedNbhd).filter
                    fun v => v ∉ G.openNeighborhood C₀)
          else 0) := by
  have key := krylovRow_mul_sectorIndepSeries hK hclaw b lam Q
  rw [sectorIndepSeries_of_single_class_of_all hclaw hC₀ hsingle _ lam
    (U := Finset.univ) (fun C _ => by simp)] at key
  by_cases h : C₀ ⊆ {v | v ∉ Q.closedNbhd}
  · rw [sectorIndepSeries_of_single_class_of_all hclaw hC₀ hsingle _ lam
      (U := Finset.univ.filter fun v => v ∉ Q.closedNbhd) (fun C hC => by
        intro v hv
        have := (subset_compl_closedNbhd_iff_of_closure hK hclaw Q hC₀ (hsingle C hC)).1 h hv
        simpa using this)] at key
    rw [if_pos h]
    exact key
  · rw [sectorIndepSeries_of_single_class_of_none hclaw hC₀ hsingle _ lam
      (U := Finset.univ.filter fun v => v ∉ Q.closedNbhd) (fun C hC hsub => h (by
        refine (subset_compl_closedNbhd_iff_of_closure hK hclaw Q hC (hsingle C hC).symm).1 ?_
        intro v hv
        have := hsub hv
        simpa using this))] at key
    rw [if_neg h, add_zero]
    exact key

/-- Without even holes there are no compatible families but `∅`, and `Z_U = I_U`. -/
theorem sectorIndepSeries_of_evenHoleFree (hfree : ∀ C : G.IndexedInducedHole, ¬Even C.card)
    (w : V → R) (lam : EvenHoleDeformationClass G → R) (U : Finset V) :
    sectorIndepSeries G w lam U = indepSeries G w U := by
  have hfam : G.holeFamilies U = {∅} := by
    ext F
    rw [mem_holeFamilies, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩
      refine Finset.eq_empty_of_forall_notMem fun C hC => ?_
      obtain ⟨H, hH, -⟩ := (h1 C hC).1
      exact hfree H hH
    · rintro rfl
      exact ⟨fun C hC => absurd hC (Finset.notMem_empty C), by simp⟩
  unfold sectorIndepSeries holeSeries
  rw [hfam, Finset.sum_singleton, Finset.prod_empty, one_mul]
  congr 1
  ext v
  simp [mem_holeFamilyRest]

/-- Consistency with the even-hole-free closed form: for graphs without even holes,
`krylovRow_mul_sectorIndepSeries` is `krylovRow_mul_indepSeries` for the tree matrix. -/
theorem krylovRow_mul_sectorIndepSeries_of_evenHoleFree
    [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬Even C.card) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries.mk (fun n => ((cliqueTreeMatrix G K b) ^ n) (cliqueRootPath G K) Q) *
        indepSeries G (fun v => b v ^ 2) Finset.univ =
      PowerSeries.X ^ (Q.path.card - 1) *
        indepSeries G (fun v => b v ^ 2) (Finset.univ.filter fun v => v ∉ Q.closedNbhd) := by
  have key := krylovRow_mul_sectorIndepSeries hK hclaw b lam Q
  rwa [cliqueHoppingMatrix_of_evenHoleFree hfree, sectorIndepSeries_of_evenHoleFree hfree,
    sectorIndepSeries_of_evenHoleFree hfree] at key

end Corollaries

/-! ### Balanced rows of `A_λ` -/

section Balance

open Classical

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]
  [DecidableEq (CliqueRootedInducedPath G K)]

/-- The constant coefficient of the sector series is `1`: every nonempty family of holes
carries a factor `(-X²)^k` with `k ≥ 2`. -/
theorem constantCoeff_sectorIndepSeries (G : SimpleGraph V) (w : V → R)
    (lam : EvenHoleDeformationClass G → R) (U : Finset V) :
    PowerSeries.constantCoeff (sectorIndepSeries G w lam U) = 1 := by
  unfold sectorIndepSeries holeSeries
  rw [map_sum]
  have hempty : (∅ : Finset (Set V)) ∈ G.holeFamilies U := by
    rw [mem_holeFamilies]
    exact ⟨fun C hC => absurd hC (Finset.notMem_empty C), by simp⟩
  rw [Finset.sum_eq_single (∅ : Finset (Set V))]
  · have h1 : G.holeFamilyRest U ∅ = U := by
      ext v
      simp [mem_holeFamilyRest]
    rw [h1, Finset.prod_empty, one_mul, constantCoeff_indepSeries]
  · intro F hF hne
    obtain ⟨C, hC⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨hCh, -⟩ := (mem_holeFamilies.1 hF).1 C hC
    have h4 := hCh.four_le_ncard
    rw [map_mul, map_prod, Finset.prod_eq_zero hC, zero_mul]
    unfold sectorHoleWeight
    have hk : C.ncard / 2 ≠ 0 := by omega
    simp [hk]
  · intro h
    exact absurd hempty h


/-- The sector series is a unit of `R⟦X⟧`. -/
theorem isUnit_sectorIndepSeries (G : SimpleGraph V) (w : V → R)
    (lam : EvenHoleDeformationClass G → R) (U : Finset V) :
    IsUnit (sectorIndepSeries G w lam U) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_sectorIndepSeries]
  exact isUnit_one

/-- **Balanced rows of `A_λ`.**  If two rooted induced paths `P`, `Q` of `G*` have the same
number of vertices and the same closed neighbourhood, then `(A_λ^n)_{{j*},P} = (A_λ^n)_{{j*},Q}`
for every `n`: by `krylovRow_mul_sectorIndepSeries` the row series times the unit `Z_V` is
`X^{|P|-1} Z_{V ∖ N(P)}`, which depends only on `|P|` and `N(P)`. -/
theorem sectorRow_pow_eq_of_closedNbhd_eq
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) {P Q : CliqueRootedInducedPath G K}
    (hcard : P.path.card = Q.path.card) (hN : P.closedNbhd = Q.closedNbhd) (n : ℕ) :
    (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) P =
      (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) Q := by
  have hP := krylovRow_mul_sectorIndepSeries hK hclaw b lam P
  have hQ := krylovRow_mul_sectorIndepSeries hK hclaw b lam Q
  rw [hcard, hN, ← hQ] at hP
  have hser := (isUnit_sectorIndepSeries G (fun v => b v ^ 2) lam
    (Finset.univ : Finset V)).mul_left_inj.1 hP
  have hn := congrArg (PowerSeries.coeff n) hser
  simpa only [PowerSeries.coeff_mk] using hn

/-- Balanced rows of `A_λ` on a deformation closure of rooted paths (v1 Lemma 16, label
`deformationclosurepathsrelation`, L1457-1464), for the matrix `A_λ`, any number of hole
classes. -/
theorem sectorRow_pow_eq_of_closure
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) {P P' : CliqueRootedInducedPath G K}
    (h : InInducedPathDeformationClosure (G.adjoinRootAt K) P.path P'.path) (n : ℕ) :
    (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) P =
      (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) P' :=
  sectorRow_pow_eq_of_closedNbhd_eq hK hclaw b lam
    h.card_eq.symm (RootedInducedPath.closedNbhd_eq_of_closure hK hclaw h).symm n

/-- Balanced rows of `A_λ` under a bubble-wand reversal (v1 Eq. (pathcircle), L1520-1523),
for the full matrix `A_λ` with hoop arcs (the tree part is
`cliqueTreeMatrix_pow_root_wandReverse`). -/
theorem sectorRow_pow_wandReverse
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) {P : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) (n : ℕ) :
    (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) P =
      (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) w.reverse :=
  sectorRow_pow_eq_of_closedNbhd_eq hK hclaw b lam
    w.reverse_card.symm (w.closedNbhd_reverse hclaw).symm n

/-- Balanced rows of `A_λ` across the sources of one handle and one hoop class: two wand
sources `P`, `P'` with the same handle and even hoops in the same deformation class have the
same size (`|P| = |Q| - 1 + |C|`) and the same closed neighbourhood
(`N(P) = N(Q) ∪ Γ[C]`, `Γ[C]` constant on a class), hence equal rows. -/
theorem sectorRow_pow_eq_of_sameHandle
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) {P P' : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) (w' : CliqueBubbleWand G K P') (hh : w.handle = w'.handle)
    (he : Even w.hoopCard) (he' : Even w'.hoopCard)
    (hcl : G.evenHoleDeformationClassOf w.hoopCarrier =
      G.evenHoleDeformationClassOf w'.hoopCarrier) (n : ℕ) :
    (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) P =
      (cliqueHoppingMatrix G K b lam ^ n) (cliqueRootPath G K) P' := by
  have hclo : InEvenHoleDeformationClosure G w.hoopCarrier w'.hoopCarrier :=
    evenHoleDeformationClassOf_eq_iff.1 hcl
  have hn : w.hoopCarrier.ncard = w'.hoopCarrier.ncard := hclo.ncard_eq
  have hcard : P.path.card = P'.path.card := by
    have h1 := w.path_card_eq
    have h2 := w'.path_card_eq
    have h3 := w.hoopCarrier_ncard
    have h4 := w'.hoopCarrier_ncard
    rw [hh] at h1
    omega
  refine sectorRow_pow_eq_of_closedNbhd_eq hK hclaw b lam hcard ?_ n
  rw [w.closedNbhd_eq_handle_union hclaw he, w'.closedNbhd_eq_handle_union hclaw he', hh,
    hclo.openNeighborhood_eq hclaw]

end Balance

/-! ### A worked instance: the four-cycle

`G = C₄` with the edge clique `K = {0, 1}` (`CliqueBubbleWand.Example`): the single even hole is
the whole vertex set, so the single-class closed form applies and the hypotheses of the general
theorems are satisfiable. -/

namespace SectorExample

open CliqueBubbleWand.Example HoleAttachmentExample

/-- The only even hole of the four-cycle is the whole vertex set. -/
theorem fourCycle_hole_eq_univ {C : Set (Fin 4)} (hC : fourCycle.IsEvenHoleCarrier C) :
    C = Set.univ := by
  by_contra h
  obtain ⟨x, hx⟩ : ∃ x, x ∉ C := by
    by_contra h'
    push Not at h'
    exact h (Set.eq_univ_of_forall h')
  have h4 := hC.four_le_ncard
  have hsub : C ⊆ ({x}ᶜ : Set (Fin 4)) := fun y hy hyx =>
    hx (by rw [Set.mem_singleton_iff.1 hyx] at hy; exact hy)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_compl, Set.ncard_singleton] at this
  simp at this
  omega

open Classical in
/-- The sector series of `C₄` has the hole term `2 λ X⁴` (`k = 2`, `Γ[c] = V`,
`I_∅ = 1`): `Z_V = I_V + 2 λ_c X⁴`. -/
theorem fourCycle_sectorIndepSeries {R : Type} [Field R] [CharZero R] (w : Fin 4 → R)
    (lam : EvenHoleDeformationClass fourCycle → R) :
    sectorIndepSeries fourCycle w lam Finset.univ =
      indepSeries fourCycle w Finset.univ +
        PowerSeries.C (2 * lam (fourCycle.evenHoleDeformationClassOf Set.univ)) *
          PowerSeries.X ^ 4 := by
  rw [sectorIndepSeries_of_single_class_of_all fourCycle_isClawFree fourCycle_isEvenHoleCarrier
    (fun C hC => by rw [fourCycle_hole_eq_univ hC]; exact InEvenHoleDeformationClosure.refl _)
    w lam (U := Finset.univ) (fun C _ => by simp)]
  have h1 : (Finset.univ.filter fun v : Fin 4 => v ∉ fourCycle.openNeighborhood Set.univ) = ∅ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_not]
    obtain ⟨u, hu, huv⟩ : ∃ u, u ∈ (Set.univ : Set (Fin 4)) ∧ fourCycle.Adj v u := by
      fin_cases v
      · exact ⟨1, trivial, by decide⟩
      · exact ⟨0, trivial, by decide⟩
      · exact ⟨1, trivial, by decide⟩
      · exact ⟨0, trivial, by decide⟩
    exact ⟨u, hu, huv⟩
  have h2 : (Set.univ : Set (Fin 4)).ncard / 2 = 2 := by
    rw [Set.ncard_univ]
    simp
  rw [h1, indepSeries_empty, h2]
  ring

open Classical in
-- The instantiation of `krylovRow_mul_indepSeries_single_class` for `C₄` (all hypotheses are
-- satisfied by `C₄` with the edge clique `{0, 1}`, whose only even hole is the whole vertex set).
example {R : Type} [Field R] [CharZero R] (b : Fin 4 → R)
    (lam : EvenHoleDeformationClass fourCycle → R)
    (Q : CliqueRootedInducedPath fourCycle edgeClique) :=
  krylovRow_mul_indepSeries_single_class (G := fourCycle) (K := edgeClique)
    fourCycle_isSimplicialClique fourCycle_isClawFree fourCycle_isEvenHoleCarrier
    (fun C hC => by rw [fourCycle_hole_eq_univ hC]; exact InEvenHoleDeformationClosure.refl _)
    b lam Q

end SectorExample

end SimpleGraph
