import FreeFermionGraphs.Lemma11Pairing
import FreeFermionGraphs.Lemma11CommonNeighbor
import FreeFermionGraphs.Lemma11BTerminalContainment
import FreeFermionGraphs.FixedPairingPathDeformation
import FreeFermionGraphs.Lemma11APathBlock

/-!
# Lemma 11(a.i): concrete pairing preservation

For an `(a,c)` Definition 19 step, the existing concrete geometry already
places a dependent vertex in `C'_d` and its persistent common hole neighbour
in `C_b`.  Consequently they have the same fixed pairing type.  This module
packages that direct conclusion without assuming an independent four-colour
certificate for the common neighbour.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The common neighbour supplied by a concrete `(a,c)` dependent step
survives the replacement and has the same fixed pairing type as the active
deformation. -/
theorem ConcreteDeformationStep.lemma11ai_same_pairing_of_acHoleGeometry
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime)
    (hgeom : O.ACHoleStepGeometry S)
    (hclaw : G.IsClawFree)
    {u : V} (hu : u ∈ S.dependentSet)
    (huOutsideHole :
      u ∉ Set.insert S.introduced (Set.range S.before.vertex)) :
    ∃ v,
      v ∈ Set.range S.before.vertex ∧
        v ∈ Set.range S.after.vertex ∧
        G.Adj u v ∧
        G.Adj S.introduced v ∧
        G.Adj (S.before.vertex S.removedIndex) v ∧
        O.HasPairingType .ac u v := by
  obtain ⟨v, hvBefore, huv, hintroducedv, hremovedv, hvCb⟩ :=
    S.dependent_commonNeighbor_mem_cb hgeom hclaw hu huOutsideHole
  have hvAfter : v ∈ Set.range S.after.vertex :=
    S.deformation.mem_range_deform_of_mem_range_of_adj_original
      hvBefore hremovedv
  have huCd : u ∈ O.Cd := S.dependent_mem_cd hgeom hu
  have htyped : O.HasPairingType .ac u v :=
    O.hasPairingType_of_mem_b .ac hvCb (by simpa using huCd)
  exact ⟨v, hvBefore, hvAfter, huv, hintroducedv, hremovedv, htyped⟩

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Lemma 11(a.i) for any dependent vertex in a concrete Definition 19
path block.  The mechanical data provides the step geometry and the required
externality condition. -/
theorem lemma11ai_same_pairing_of_mechanicalData
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V} (hu : u ∈ D.dependentAt s) :
    ∃ v,
      v ∈ Set.range
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex ∧
        v ∈ Set.range
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).after.vertex ∧
        G.Adj u v ∧
        G.Adj
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced v ∧
        G.Adj
          ((D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex
              (D.deformation.step
                ⟨s, D.index_lt_of_mem_dependentAt hu⟩).removedIndex) v ∧
        O.HasPairingType .ac u v := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ (D.deformation.step i).dependentSet := by
    exact D.mem_step_dependentSet_of_mem_dependentAt hu
  simpa [i] using
    (D.deformation.step i).lemma11ai_same_pairing_of_acHoleGeometry
      (M.stepGeometry i) hclaw hui (M.outsideHole i hui)

/-- The concrete pairing part of Lemma 11(a.i) is available from the same
full Definition 19 local package used by the path-block equivalence. -/
theorem lemma11ai_same_pairing_of_fullDefinition19
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V} (hu : u ∈ D.dependentAt s) :
    ∃ v,
      v ∈ Set.range
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex ∧
        v ∈ Set.range
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).after.vertex ∧
        G.Adj u v ∧
        G.Adj
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced v ∧
        G.Adj
          ((D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex
              (D.deformation.step
                ⟨s, D.index_lt_of_mem_dependentAt hu⟩).removedIndex) v ∧
        O.HasPairingType .ac u v := by
  exact D.lemma11ai_same_pairing_of_mechanicalData
    F.neighborhood.mechanical hclaw hu

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
