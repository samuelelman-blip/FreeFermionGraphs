import FreeFermionGraphs.Lemma11BConcreteSeparation

/-!
# Lemma 11(b): concrete terminal path containment

A dependent vertex outside the current hole has the persistent common-hole
neighbor supplied by the single-vertex deformation argument.  In an
`(a,c)` step, class independence places the dependent vertex in `C'ḓ`
and the common neighbor in `C_b`.  Since `bdPaths` are the connected
components on that pairing side, their edge lies in one such component.

This discharges the terminal path-containment field used by Lemma 11(b).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The hole-color and component data needed in addition to
`ACStepGeometry` for the common-neighbor argument. -/
structure ACHoleStepGeometry
    {Cprime : Set V}
    (O : FixedPairingPathFamily G)
    (S : ConcreteDeformationStep O Cprime) : Prop where
  base : O.ACStepGeometry S
  removed_ca :
    S.before.vertex S.removedIndex ∈ O.Ca
  prime_subset :
    Cprime ⊆ O.Cc ∪ O.Cd
  before_subset :
    Set.range S.before.vertex ⊆ O.Ca ∪ O.Cb
  ca_independent :
    IsIndependentClass G O.Ca
  bdEdgeCoverage :
    O.CoversBDEdges

/-- A concrete dependent vertex lies in the prime class paired with
`C_b`. -/
theorem ConcreteDeformationStep.dependent_mem_cd
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACHoleStepGeometry S)
    {u : V} (hu : u ∈ S.dependentSet) :
    u ∈ O.Cd := by
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet S).1 hu
  rcases hgeom.prime_subset hmem.1 with huCc | huCd
  · exact (S.dependent_not_mem_cc hgeom.base hu huCc).elim
  · exact huCd

/-- The persistent common-hole neighbor of a dependent vertex lies in
`C_b`: it belongs to the old hole, hence to `Cₐ ∪ C_b`, and adjacency
to the removed `Cₐ` vertex excludes `Cₐ`. -/
theorem ConcreteDeformationStep.dependent_commonNeighbor_mem_cb
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACHoleStepGeometry S)
    (hclaw : G.IsClawFree)
    {u : V} (hu : u ∈ S.dependentSet)
    (huOutsideHole :
      u ∉ Set.insert S.introduced (Set.range S.before.vertex)) :
    ∃ v ∈ Set.range S.before.vertex,
      G.Adj u v ∧
        G.Adj S.introduced v ∧
        G.Adj (S.before.vertex S.removedIndex) v ∧
        v ∈ O.Cb := by
  have huDependent :
      u ∈ G.dependentSubset Cprime S.introduced
        (S.before.vertex S.removedIndex) := by
    exact hu
  obtain ⟨v, hvBefore, huv, hintroducedv, hremovedv⟩ :=
    dependentSubset_has_common_hole_neighbor
      S.deformation hclaw huDependent huOutsideHole
  have hvCb : v ∈ O.Cb := by
    rcases hgeom.before_subset hvBefore with hvCa | hvCb
    · exact (hgeom.ca_independent
        hgeom.removed_ca hvCa hremovedv).elim
    · exact hvCb
  exact ⟨v, hvBefore, huv, hintroducedv, hremovedv, hvCb⟩

/-- Path containment for a concrete dependent vertex.  This is stronger
than the terminal-only field required by `Lemma11BNeighborhoodData`. -/
theorem ConcreteDeformationStep.dependent_mem_path
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACHoleStepGeometry S)
    (hclaw : G.IsClawFree)
    {u : V} (hu : u ∈ S.dependentSet)
    (huOutsideHole :
      u ∉ Set.insert S.introduced (Set.range S.before.vertex)) :
    ∃ Q : Set V, Q ∈ O.paths ∧ u ∈ Q := by
  have huCd : u ∈ O.Cd :=
    S.dependent_mem_cd hgeom hu
  obtain ⟨v, _hvBefore, huv, _hintroducedv,
      _hremovedv, hvCb⟩ :=
    S.dependent_commonNeighbor_mem_cb
      hgeom hclaw hu huOutsideHole
  obtain ⟨Q, hQ, huQ, _hvQ⟩ :=
    hgeom.bdEdgeCoverage huCd hvCb huv
  exact ⟨Q, Or.inr hQ, huQ⟩

/-- Sequence-level discharge of the path-containment obligation. -/
theorem ConcreteDeformation.dependent_mem_path
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (D : ConcreteDeformation O Cprime)
    (hclaw : G.IsClawFree)
    (hgeom : ∀ i : Fin D.stepCount,
      O.ACHoleStepGeometry (D.step i))
    (houtsideHole : ∀ (i : Fin D.stepCount) ⦃u : V⦄,
      u ∈ D.dependentAt i →
      u ∉ Set.insert (D.step i).introduced
        (Set.range (D.step i).before.vertex)) :
    ∀ (i : Fin D.stepCount) ⦃u : V⦄,
      u ∈ D.dependentAt i →
      ∃ Q : Set V, Q ∈ O.paths ∧ u ∈ Q := by
  intro i u hu
  exact (D.step i).dependent_mem_path
    (hgeom i) hclaw hu (houtsideHole i hu)

end FixedPairingPathFamily

end SimpleGraph
