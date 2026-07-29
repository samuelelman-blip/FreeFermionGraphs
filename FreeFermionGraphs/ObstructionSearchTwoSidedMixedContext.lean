import FreeFermionGraphs.ObstructionSearchTwoSidedMixedParity

/-!
# Positive mixed-side Lemma 11 history data

A nonempty Definition 19 history has one literal sequence of hole carriers, but
its individual path blocks may use either component side of the fixed pairing.
The current path block also has its own side.

This module packages that positive-history data without forcing all blocks into
one oriented family.  It retains exactly the distinctness, carrier-link, and
Corollary 10 endpoint-uniqueness fields used by the existing finite-history
Lemma 11(a) proof.  No obstruction-search execution is constructed, and no
conclusion of Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- Positive Definition 19 history data in which the current block and every
prior block may independently use either manuscript component side.

The carrier blocks remain in the unswapped family `O`; only their local Lemma 11
presentations are reoriented. -/
structure MixedSideFullDefinition19Lemma11AHistoryData
    (D : ConcretePathDeformation O Cprime) where
  currentSide : DeformationSide
  current : (D.reorient currentSide).FullDefinition19Lemma11AData
  history : MixedSidePathBlockHistory (O := O) (Cprime := Cprime)
  priorCount : Nat
  priorCount_pos : 0 < priorCount
  final_before_current :
    Set.range (history.carrier.block (priorCount - 1)).finalHole.vertex =
      Set.range D.initialHole.vertex
  priorPath_ne_current : ∀ r : Nat, r < priorCount →
    Set.range (history.carrier.block r).path.vertex ≠
      Set.range D.path.vertex
  priorPath_pairwise : ∀ r q : Nat,
    r < priorCount → q < priorCount → r ≠ q →
      Set.range (history.carrier.block r).path.vertex ≠
        Set.range (history.carrier.block q).path.vertex
  earlierFirstIntroduced_uniquePath : ∀ r : Nat, r < priorCount →
    O.IsUniqueContainingPath
      ((history.carrier.block r).deformation.step
        (history.carrier.block r).firstIndex).introduced
      (Set.range (history.carrier.block r).path.vertex)

namespace MixedSideFullDefinition19Lemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}

/-- The current carrier block interpreted in its selected manuscript side. -/
def orientedCurrent
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData) :
    ConcretePathDeformation (X.currentSide.family O) Cprime :=
  D.reorient X.currentSide

@[simp] theorem orientedCurrent_path
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData) :
    X.orientedCurrent.path = D.path := rfl

/-- Definition 20 dependent sets of the current block are unaffected by its
side presentation. -/
theorem orientedCurrent_dependentAt
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (s : Nat) :
    X.orientedCurrent.dependentAt s = D.dependentAt s := by
  simpa [orientedCurrent] using D.reorient_dependentAt X.currentSide s

/-- The original hole before the positive mixed history. -/
def originalHole
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData) :
    IndexedInducedHole G :=
  (X.history.carrier.block 0).initialHole

/-- Every prior carrier path belongs to the full fixed-pairing path family,
independently of its local side tag. -/
theorem prior_path_mem_family
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (r : Nat) :
    Set.range (X.history.carrier.block r).path.vertex ∈ O.paths := by
  have hside := X.history.path_mem_selectedSide r
  change Set.range (X.history.carrier.block r).path.vertex ∈
    O.acPaths ∪ O.bdPaths
  rcases hside with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

end MixedSideFullDefinition19Lemma11AHistoryData

namespace FullDefinition19Lemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}

/-- The old homogeneous `ac` positive history embeds into the mixed-side
interface.  This is a compatibility map only; the literal obstruction-search
construction must eventually produce genuinely mixed side tags where needed. -/
def toMixedSide
    (X : D.FullDefinition19Lemma11AHistoryData) :
    D.MixedSideFullDefinition19Lemma11AHistoryData where
  currentSide := .ac
  current := X.current
  history :=
    { carrier := X.history
      side := fun _ => .ac
      localData := fun r => X.prior r }
  priorCount := X.priorCount
  priorCount_pos := X.priorCount_pos
  final_before_current := X.final_before_current
  priorPath_ne_current := X.priorPath_ne_current
  priorPath_pairwise := X.priorPath_pairwise
  earlierFirstIntroduced_uniquePath := X.earlierFirstIntroduced_uniquePath

@[simp] theorem toMixedSide_currentSide
    (X : D.FullDefinition19Lemma11AHistoryData) :
    X.toMixedSide.currentSide = .ac := rfl

@[simp] theorem toMixedSide_priorCount
    (X : D.FullDefinition19Lemma11AHistoryData) :
    X.toMixedSide.priorCount = X.priorCount := rfl

@[simp] theorem toMixedSide_carrier
    (X : D.FullDefinition19Lemma11AHistoryData) :
    X.toMixedSide.history.carrier = X.history := rfl

end FullDefinition19Lemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
