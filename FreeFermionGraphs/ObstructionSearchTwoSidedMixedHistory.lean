import FreeFermionGraphs.ObstructionSearchTwoSidedContextAudit

/-!
# Mixed-side Definition 19 path-block histories

Definition 19 permits one fixed-pairing deformation to use both component
families `C_a ⊕ C'_c` and `C_b ⊕ C'_d`.  The carrier sequence of holes and
paths is independent of that side choice, while the full local Lemma 11 data
must be interpreted in the family selected separately for each block.

This module introduces that missing history layer.  A single carrier-level
`PathBlockHistory` records the literal ordered deformation, and every block has
its own `DeformationSide` together with full Definition 19 data after
reorientation to that side.  No obstruction-search execution is constructed
here, and no conclusion of Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- A carrier-linked Definition 19 history whose blocks may independently use
 either component side of one fixed-pairing family. -/
structure MixedSidePathBlockHistory where
  carrier : PathBlockHistory (O := O) (Cprime := Cprime)
  side : Nat → DeformationSide
  localData : ∀ r : Nat,
    ((carrier.block r).reorient (side r)).FullDefinition19Lemma11AData

namespace MixedSidePathBlockHistory

/-- The `r`th carrier block interpreted in its manuscript side. -/
def orientedBlock
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) :
    ConcretePathDeformation ((H.side r).family O) Cprime :=
  (H.carrier.block r).reorient (H.side r)

@[simp] theorem orientedBlock_path
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) :
    (H.orientedBlock r).path = (H.carrier.block r).path := rfl

/-- Definition 20 dependent sets are unchanged by the side presentation. -/
theorem orientedBlock_dependentAt
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r s : Nat) :
    (H.orientedBlock r).dependentAt s =
      (H.carrier.block r).dependentAt s := by
  simpa [orientedBlock] using
    ((H.carrier.block r).reorient_dependentAt (H.side r) s)

/-- The literal carrier links remain those of the underlying mixed sequence. -/
theorem carrier_chain
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) :
    Set.range (H.carrier.block r).finalHole.vertex =
      Set.range (H.carrier.block (r + 1)).initialHole.vertex :=
  H.carrier.chain r

/-- Convert membership in the `acPaths` family of an oriented presentation to
 membership in the selected component family of the original presentation. -/
private theorem selectedSide_and_mem_of_mem_oriented_ac
    (side : DeformationSide)
    {Q : Set V}
    (hQ : Q ∈ (side.family O).acPaths) :
    (side = .ac ∧ Q ∈ O.acPaths) ∨
      (side = .bd ∧ Q ∈ O.bdPaths) := by
  cases side with
  | ac =>
      left
      exact ⟨rfl, by simpa [DeformationSide.family] using hQ⟩
  | bd =>
      right
      exact ⟨rfl, by
        simpa [DeformationSide.family, swapSides] using hQ⟩

/-- Every block of a mixed history belongs to the component family selected by
 its own side tag. -/
theorem path_mem_selectedSide
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) :
    (H.side r = .ac ∧
        Set.range (H.carrier.block r).path.vertex ∈ O.acPaths) ∨
      (H.side r = .bd ∧
        Set.range (H.carrier.block r).path.vertex ∈ O.bdPaths) := by
  have hactive :
      Set.range
          (((H.carrier.block r).reorient (H.side r)).path.vertex) ∈
        ((H.side r).family O).acPaths := by
    rw [← ((H.carrier.block r).reorient (H.side r)).activePath_eq
      ((H.carrier.block r).reorient (H.side r)).firstIndex]
    exact
      (((H.localData r).neighborhood.mechanical.stepGeometry
        ((H.carrier.block r).reorient (H.side r)).firstIndex).base.activePath_ac)
  have hcarrier :
      Set.range (H.carrier.block r).path.vertex ∈
        ((H.side r).family O).acPaths := by
    simpa using hactive
  exact selectedSide_and_mem_of_mem_oriented_ac (H.side r) hcarrier

end MixedSidePathBlockHistory

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
