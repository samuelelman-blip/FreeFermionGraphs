import FreeFermionGraphs.CliqueChargePartition
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Weighted independence series and the clique-splitting identity

Manuscript reference: arXiv 2305.15625 v1, Definition `independencepolynomial`
(weighted independence polynomial, lines 542-547) together with the remark that
`I_G` satisfies the clique recursion, Eq. `independencepolynomialrecursion`
(line 548):

`I_G(x) = I_{G \ K}(x) + x ∑_{j ∈ K} b_j² I_{G \ Γ[j]}(x)`.

For a finite vertex set `U` of a graph `G` and weights `w : V → R` (the
manuscript later specializes to `w = b²`), `indepSeries G w U` is the formal
power series obtained from the weighted independence polynomial of the induced
subgraph `G[U]` by substituting `x = -X²`:

`I_U = ∑_{S ⊆ U independent} (∏_{v ∈ S} w_v) (-X²)^{|S|}  ∈ R⟦X⟧`.

The weights are arbitrary here, so nothing beyond the manuscript setup is
assumed.  We prove that the constant coefficient is `1` (hence `I_U` is a unit
of `R⟦X⟧`) and the scalar analogue of the operator clique recursion
`operatorIndependentSetCharge_finsetClique`: for a clique `D ⊆ U`,

`I_U = I_{U \ D} - X² ∑_{y ∈ D} w_y I_{U \ Γ[y]}`,

which is Eq. `independencepolynomialrecursion` at `x = -X²`.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u} {R : Type w} [CommRing R]

namespace SimpleGraph

/-- The weighted independence series of the induced subgraph `G[U]`:
`∑_{S ⊆ U independent} (∏_{v ∈ S} w_v) (-X²)^{|S|}`.  This is the manuscript
weighted independence polynomial `I_{G[U]}(x)` (v1 Definition
`independencepolynomial`, lines 542-547) at `x = -X²`, with weights `w`
(the manuscript uses `w = b²`). -/
noncomputable def indepSeries (G : SimpleGraph V) (w : V → R) (U : Finset V) :
    PowerSeries R := by
  classical
  exact ∑ S ∈ U.powerset.filter (fun S : Finset V => G.IsIndepSet (S : Set V)),
    PowerSeries.C (∏ v ∈ S, w v) * (-(PowerSeries.X ^ 2)) ^ S.card

/-- Unfolding of `indepSeries` for an arbitrary decidability instance on the
independence predicate. -/
theorem indepSeries_eq_sum (G : SimpleGraph V) (w : V → R) (U : Finset V)
    [DecidablePred (fun S : Finset V => G.IsIndepSet (S : Set V))] :
    indepSeries G w U =
      ∑ S ∈ U.powerset.filter (fun S : Finset V => G.IsIndepSet (S : Set V)),
        PowerSeries.C (∏ v ∈ S, w v) * (-(PowerSeries.X ^ 2)) ^ S.card := by
  classical
  unfold indepSeries
  congr

/-- The constant coefficient of `I_U` is `1`: only the empty independent set
contributes to the constant term. -/
theorem constantCoeff_indepSeries (G : SimpleGraph V) (w : V → R) (U : Finset V) :
    PowerSeries.constantCoeff (indepSeries G w U) = 1 := by
  classical
  rw [indepSeries_eq_sum, map_sum]
  rw [Finset.sum_eq_single (∅ : Finset V)]
  · simp
  · intro S _ hS
    have hcard : S.card ≠ 0 := by
      intro h
      exact hS (Finset.card_eq_zero.mp h)
    simp [hcard]
  · intro h
    exfalso
    apply h
    simp [SimpleGraph.IsIndepSet]

/-- The weighted independence series is a unit of `R⟦X⟧` (its constant
coefficient is `1`). -/
theorem isUnit_indepSeries (G : SimpleGraph V) (w : V → R) (U : Finset V) :
    IsUnit (indepSeries G w U) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_indepSeries]
  exact isUnit_one

/-- The series of the empty vertex set is `1`. -/
@[simp] theorem indepSeries_empty (G : SimpleGraph V) (w : V → R) :
    indepSeries G w ∅ = 1 := by
  classical
  rw [indepSeries_eq_sum]
  have hI : G.IsIndepSet ((∅ : Finset V) : Set V) := by
    simp [SimpleGraph.IsIndepSet]
  rw [Finset.powerset_empty, Finset.filter_singleton, if_pos hI]
  simp

open Classical in
/-- The part of `I_U` coming from independent sets avoiding a vertex `y ∈ U`
is `I_{U \ {y}}`. -/
theorem sum_indep_not_mem [DecidableEq V] (G : SimpleGraph V) (w : V → R)
    (U : Finset V) (y : V) :
    ∑ S ∈ (U.powerset.filter (fun S : Finset V => G.IsIndepSet (S : Set V))).filter
          (fun S => y ∉ S),
        PowerSeries.C (∏ v ∈ S, w v) * (-(PowerSeries.X ^ 2)) ^ S.card =
      indepSeries G w (U.erase y) := by
  rw [indepSeries_eq_sum]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hSU, hI⟩, hy⟩
    refine ⟨fun v hv => ?_, hI⟩
    exact Finset.mem_erase.mpr ⟨fun h => hy (h ▸ hv), hSU hv⟩
  · rintro ⟨hSU, hI⟩
    refine ⟨⟨fun v hv => Finset.mem_of_mem_erase (hSU hv), hI⟩, fun hy => ?_⟩
    exact (Finset.mem_erase.mp (hSU hy)).1 rfl

open Classical in
/-- The part of `I_U` coming from independent sets containing a vertex
`y ∈ U` is `-X² · w_y · I_{U \ Γ[y]}`. -/
theorem sum_indep_mem [DecidableEq V] (G : SimpleGraph V) (w : V → R)
    {U : Finset V} {y : V} (hy : y ∈ U) :
    ∑ S ∈ (U.powerset.filter (fun S : Finset V => G.IsIndepSet (S : Set V))).filter
          (fun S => y ∈ S),
        PowerSeries.C (∏ v ∈ S, w v) * (-(PowerSeries.X ^ 2)) ^ S.card =
      -(PowerSeries.X ^ 2 * (PowerSeries.C (w y) *
        indepSeries G w (U.filter (fun v => v ∉ G.closedNeighborhood y)))) := by
  rw [indepSeries_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun S => S.erase y) (fun T => insert y T) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    obtain ⟨⟨hSU, hI⟩, hyS⟩ := hS
    refine ⟨fun v hv => ?_, isIndepSet_erase hI⟩
    have hv' := Finset.mem_erase.mp hv
    exact Finset.mem_filter.mpr
      ⟨hSU hv'.2, erase_avoids_closedNeighborhood hI hyS v hv⟩
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    obtain ⟨hTU, hI⟩ := hT
    have havoid : ∀ v ∈ T, v ∉ G.closedNeighborhood y := fun v hv =>
      (Finset.mem_filter.mp (hTU hv)).2
    refine ⟨⟨fun v hv => ?_, isIndepSet_insert_of_avoids_closedNeighborhood hI havoid⟩,
      Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.mp hv with rfl | hvT
    · exact hy
    · exact (Finset.mem_filter.mp (hTU hvT)).1
  · intro S hS
    simp only [Finset.mem_filter] at hS
    exact Finset.insert_erase hS.2
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    refine Finset.erase_insert fun hyT => ?_
    exact (Finset.mem_filter.mp (hT.1 hyT)).2 (Set.mem_insert _ _)
  · intro S hS
    simp only [Finset.mem_filter] at hS
    have hyS : y ∈ S := hS.2
    have hprod : ∏ v ∈ S, w v = w y * ∏ v ∈ S.erase y, w v :=
      (Finset.mul_prod_erase S w hyS).symm
    have hcard : S.card = (S.erase y).card + 1 := by
      rw [Finset.card_erase_of_mem hyS]
      have : 0 < S.card := Finset.card_pos.mpr ⟨y, hyS⟩
      omega
    rw [hprod, hcard, map_mul, pow_succ]
    ring

open Classical in
/-- Single-vertex form of the clique recursion: for `y ∈ U`,
`I_U = I_{U \ {y}} - X² w_y I_{U \ Γ[y]}`. -/
theorem indepSeries_single_split [DecidableEq V] (G : SimpleGraph V) (w : V → R)
    {U : Finset V} {y : V} (hy : y ∈ U) :
    indepSeries G w U = indepSeries G w (U.erase y) -
      PowerSeries.X ^ 2 * (PowerSeries.C (w y) *
        indepSeries G w (U.filter (fun v => v ∉ G.closedNeighborhood y))) := by
  rw [← sum_indep_not_mem G w U y, sub_eq_add_neg, ← sum_indep_mem G w hy, add_comm,
    indepSeries_eq_sum]
  exact (Finset.sum_filter_add_sum_filter_not _ (fun S => y ∈ S) _).symm

open Classical in
/-- Clique-splitting identity for the weighted independence series: for a
clique `D ⊆ U`,

`I_U = I_{U \ D} - X² ∑_{y ∈ D} w_y I_{U \ Γ[y]}`.

This is the manuscript recursion
`I_G(x) = I_{G \ K}(x) + x ∑_{j ∈ K} b_j² I_{G \ Γ[j]}(x)` (v1 Eq.
`independencepolynomialrecursion`, line 548) at `x = -X²` with `w = b²`, and
the scalar analogue of `operatorIndependentSetCharge_finsetClique`. -/
theorem indepSeries_clique_split [DecidableEq V] (G : SimpleGraph V) (w : V → R)
    {D U : Finset V} (hD : G.IsClique (D : Set V)) (hDU : D ⊆ U) :
    indepSeries G w U = indepSeries G w (U.filter (fun v => v ∉ D)) -
      PowerSeries.X ^ 2 * ∑ y ∈ D, PowerSeries.C (w y) *
        indepSeries G w (U.filter (fun v => v ∉ G.closedNeighborhood y)) := by
  induction D using Finset.induction_on generalizing U with
  | empty =>
      simp
  | @insert j D hjD ih =>
      have hDclique : G.IsClique (D : Set V) := by
        intro a ha b hb hab
        exact hD (by simp [ha]) (by simp [hb]) hab
      have hjU : j ∈ U := hDU (Finset.mem_insert_self _ _)
      have hDU' : D ⊆ U.erase j := by
        intro v hv
        refine Finset.mem_erase.mpr ⟨?_, hDU (Finset.mem_insert_of_mem hv)⟩
        rintro rfl
        exact hjD hv
      have hIH := ih hDclique hDU'
      rw [indepSeries_single_split G w hjU, hIH, Finset.sum_insert hjD]
      -- identify the vertex-set arguments
      have h1 : (U.erase j).filter (fun v => v ∉ D) =
          U.filter (fun v => v ∉ insert j D) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert]
        tauto
      have h2 : ∀ y ∈ D, (U.erase j).filter (fun v => v ∉ G.closedNeighborhood y) =
          U.filter (fun v => v ∉ G.closedNeighborhood y) := by
        intro y hy
        have hjy : j ≠ y := fun h => hjD (h ▸ hy)
        have hadj : G.Adj y j :=
          hD (by simp [hy]) (by simp) hjy.symm
        have hjmem : j ∈ G.closedNeighborhood y :=
          Set.mem_insert_iff.mpr (Or.inr ((G.mem_neighborSet y j).mpr hadj))
        ext v
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hv⟩, hn⟩
          exact ⟨hv, hn⟩
        · rintro ⟨hv, hn⟩
          refine ⟨⟨?_, hv⟩, hn⟩
          rintro rfl
          exact hn hjmem
      rw [h1, Finset.sum_congr rfl (fun y hy => by rw [h2 y hy])]
      ring

end SimpleGraph
