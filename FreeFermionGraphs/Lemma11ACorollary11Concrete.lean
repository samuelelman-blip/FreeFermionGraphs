import FreeFermionGraphs.Lemma11AOriginalHole
import FreeFermionGraphs.Corollary11

/-!
# Concrete Corollary 11 geometry

The lemmas here derive the local path-neighbour alternatives used in
Corollary 11 from the completed Lemma 11(a) path-block calculation.  No
no-shared-witness conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- A `b`-vertex of an alternating hole cannot have three distinct
neighbours in the same hole. -/
theorem not_three_distinct_carrier_neighbors_of_b
    {k : Nat} (C : EvenHoleLabeling G k) (q : Fin k)
    {x y z : V}
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) (hz : z ∈ C.carrier)
    (hqx : G.Adj (C.b q) x)
    (hqy : G.Adj (C.b q) y)
    (hqz : G.Adj (C.b q) z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  have locate (w : V) (hw : w ∈ C.carrier)
      (hqw : G.Adj (C.b q) w) :
      ∃ i : Fin k, w = C.a i ∧ (i = q ∨ i = C.prev q) := by
    rcases hw with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine ⟨i, hi.symm, ?_⟩
      have hadj : G.Adj (C.a i) (C.b q) := by
        rw [hi]
        exact hqw.symm
      rcases (C.adj_ab_iff i q).mp hadj with hqi | hqnext
      · exact Or.inl hqi.symm
      · right
        rw [hqnext, C.prev_next]
    · have hbb : G.Adj (C.b q) (C.b i) := by
        rw [hi]
        exact hqw
      exact (C.adj_bb q i hbb).elim
  obtain ⟨ix, hxeq, hix⟩ := locate x hx hqx
  obtain ⟨iy, hyeq, hiy⟩ := locate y hy hqy
  obtain ⟨iz, hzeq, hiz⟩ := locate z hz hqz
  have hixy : ix ≠ iy := by
    intro h
    apply hxy
    rw [hxeq, hyeq, h]
  have hixz : ix ≠ iz := by
    intro h
    apply hxz
    rw [hxeq, hzeq, h]
  have hiyz : iy ≠ iz := by
    intro h
    apply hyz
    rw [hyeq, hzeq, h]
  rcases hix with hix | hix <;>
    rcases hiy with hiy | hiy <;>
    rcases hiz with hiz | hiz
  all_goals subst_vars
  all_goals simp_all

end EvenHoleLabeling

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- An anticommuting Definition 20 vertex has one or two introduced
neighbours on its active path. -/
theorem introducedNeighborCount_eq_one_or_two
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hanti : D.path.AnticommutesWith u) :
    D.introducedNeighborCount u D.deformation.stepCount = 1 ∨
      D.introducedNeighborCount u D.deformation.stepCount = 2 := by
  have hui : u ∈
      (D.deformation.step
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huPrime : u ∈ Cprime :=
    ((D.deformation.step
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩).mem_dependentSet.mp hui).1
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have huOutside :=
    F.anticommuting_not_mem_path huPrime hlocal.1 hanti
  have hbalance := D.anticommuting_neighborCount_balance
    F.neighborhood.pathOrder F.path_card_eq hclaw huOutside hanti
    (F.terminalAnticommutingNonadjacency huPrime huOutside hanti)
    (D.removedIntroducedRemovedExtension_of_fullDefinition19
      F hclaw huPrime)
  have hsum := D.pathNeighborCount_eq_introduced_add_removed
    F.neighborhood.pathOrder F.path_card_eq u
  have hcases := D.path.anticommutesWith_count_eq_one_or_three
    hclaw huOutside hanti
  rcases hcases with hone | hthree <;> omega

/-- In the one-introduced-neighbour case, a dependent vertex belongs to
the first step.  Lemma 7 makes its unique path neighbour an endpoint, and
the terminal nonedge selects the initial endpoint. -/
theorem dependentStep_eq_zero_of_introducedNeighborCount_eq_one
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hanti : D.path.AnticommutesWith u)
    (hone : D.introducedNeighborCount u D.deformation.stepCount = 1) :
    s = 0 := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huPrime : u ∈ Cprime :=
    ((D.deformation.step i).mem_dependentSet.mp hui).1
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have huOutside :=
    F.anticommuting_not_mem_path huPrime hlocal.1 hanti
  have hbalance := D.anticommuting_neighborCount_balance
    F.neighborhood.pathOrder F.path_card_eq hclaw huOutside hanti
    (F.terminalAnticommutingNonadjacency huPrime huOutside hanti)
    (D.removedIntroducedRemovedExtension_of_fullDefinition19
      F hclaw huPrime)
  have hsum := D.pathNeighborCount_eq_introduced_add_removed
    F.neighborhood.pathOrder F.path_card_eq u
  have htotal : (D.path.neighborIndexSet u).ncard = 1 := by omega
  have huIntroduced : G.Adj u (D.deformation.step i).introduced :=
    ((D.deformation.step i).mem_dependentSet.mp hui).2.1
  have huPathIntroduced :
      G.Adj u
        (D.path.vertex (F.neighborhood.pathOrder.introducedPathIndex i)) := by
    rw [F.neighborhood.pathOrder.introduced_eq i]
    exact huIntroduced
  have hendpoint :
      D.path.IsEndpointIndex
        (F.neighborhood.pathOrder.introducedPathIndex i) := by
    rcases D.path.lemma7 hclaw huOutside with
        hzero | honeCase | htwo | hthree | hfour
    · omega
    · exact honeCase.2 _ huPathIntroduced
    · omega
    · omega
    · omega
  have hfirst :
      (F.neighborhood.pathOrder.introducedPathIndex i).val = 0 := by
    rcases hendpoint with hfirst | hlast
    · exact hfirst
    · exact (F.terminalAnticommutingNonadjacency
        huPrime huOutside hanti _ hlast huPathIntroduced).elim
  have hindex := F.neighborhood.pathOrder.introduced_index_val i
  have hiVal : i.val = s := rfl
  omega

/-- Two introduced neighbours can be selected as two distinct prime-hole
vertices of `C'_c`, both lying on the active path. -/
theorem exists_two_distinct_introducedNeighbors
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    {u : V}
    (htwo : D.introducedNeighborCount u D.deformation.stepCount = 2) :
    ∃ i j : Fin D.deformation.stepCount,
      i ≠ j ∧
      G.Adj u (D.deformation.step i).introduced ∧
      G.Adj u (D.deformation.step j).introduced ∧
      (D.deformation.step i).introduced ∈ Cprime ∧
      (D.deformation.step j).introduced ∈ Cprime ∧
      (D.deformation.step i).introduced ∈ O.Cc ∧
      (D.deformation.step j).introduced ∈ O.Cc ∧
      (D.deformation.step i).introduced ∈ Set.range D.path.vertex ∧
      (D.deformation.step j).introduced ∈ Set.range D.path.vertex := by
  rw [D.introducedNeighborCount_eq_ncard] at htwo
  obtain ⟨i, j, hij, hset⟩ := Set.ncard_eq_two.mp htwo
  have hi : i ∈ D.introducedNeighborStepSet u := by
    rw [hset]
    simp
  have hj : j ∈ D.introducedNeighborStepSet u := by
    rw [hset]
    simp
  refine ⟨i, j, hij, hi, hj,
    F.neighborhood.primeHole.introduced_mem i,
    F.neighborhood.primeHole.introduced_mem j,
    (F.neighborhood.mechanical.stepGeometry i).base.introduced_cc,
    (F.neighborhood.mechanical.stepGeometry j).base.introduced_cc, ?_, ?_⟩
  · refine ⟨F.neighborhood.pathOrder.introducedPathIndex i, ?_⟩
    exact F.neighborhood.pathOrder.introduced_eq i
  · refine ⟨F.neighborhood.pathOrder.introducedPathIndex j, ?_⟩
    exact F.neighborhood.pathOrder.introduced_eq j

/-- The first introduced endpoint has exactly one `C_a` neighbour in its
active path component, namely the first removed vertex. -/
theorem firstIntroduced_unique_ca_neighbor
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    {w : V}
    (hwCa : w ∈ O.Ca)
    (hjw : G.Adj
      (D.deformation.step D.firstIndex).introduced w) :
    w = (D.deformation.step D.firstIndex).before.vertex
      (D.deformation.step D.firstIndex).removedIndex := by
  let first := D.firstIndex
  have hgeom := F.neighborhood.mechanical.stepGeometry first
  have hpathAc : Set.range D.path.vertex ∈ O.acPaths := by
    rw [← D.activePath_eq first]
    exact hgeom.base.activePath_ac
  have hjPath :
      (D.deformation.step first).introduced ∈ Set.range D.path.vertex := by
    refine ⟨F.neighborhood.pathOrder.introducedPathIndex first, ?_⟩
    exact F.neighborhood.pathOrder.introduced_eq first
  obtain ⟨Q, hQ, hjQ, hwQ⟩ :=
    hgeom.base.edgeCoverage hgeom.base.introduced_cc hwCa hjw
  have hpathQ : Set.range D.path.vertex = Q :=
    O.eq_of_mem_acPaths hpathAc hQ hjPath hjQ
  have hwPath : w ∈ Set.range D.path.vertex := by
    rw [hpathQ]
    exact hwQ
  obtain ⟨q, hq⟩ := hwPath
  have hadjPath :
      G.Adj
        (D.path.vertex
          (F.neighborhood.pathOrder.introducedPathIndex first))
        (D.path.vertex q) := by
    rw [F.neighborhood.pathOrder.introduced_eq first, hq]
    exact hjw
  have hqval : q.val = 1 := by
    have hadj := (D.path.adj_iff
      (F.neighborhood.pathOrder.introducedPathIndex first) q).mp hadjPath
    have hfirstVal :
        (F.neighborhood.pathOrder.introducedPathIndex first).val = 0 := by
      simpa [first, ConcretePathDeformation.firstIndex] using
        F.neighborhood.pathOrder.introduced_index_val first
    omega
  have hqRemoved :
      q = F.neighborhood.pathOrder.removedPathIndex first := by
    apply Fin.ext
    rw [F.neighborhood.pathOrder.removed_index_val]
    dsimp [first, ConcretePathDeformation.firstIndex]
    omega
  calc
    w = D.path.vertex q := hq.symm
    _ = D.path.vertex
        (F.neighborhood.pathOrder.removedPathIndex first) := by rw [hqRemoved]
    _ = (D.deformation.step first).before.vertex
        (D.deformation.step first).removedIndex :=
      F.neighborhood.pathOrder.removed_eq first

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
