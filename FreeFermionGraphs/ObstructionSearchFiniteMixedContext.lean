import FreeFermionGraphs.ObstructionSearchFiniteMixedFirstCommon
import FreeFermionGraphs.ObstructionSearchFiniteMixedPrefix

/-!
# Uniform contexts for finite mixed-side search blocks

Every block of a literal finite trace is either the first block or has the
strictly bounded prefix preceding its index.  This module packages that exact
split without extending a finite execution to an artificial `Nat`-indexed
tail.

The first constructor stores only the selected side, local Definition 19 data,
and equality of its initial carrier with the fixed original hole.  The later
constructor stores the already constructed `Fin priorCount` history.  No
conclusion of Lemma 11, Corollary 11, or Lemma 14 is a field.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The finite zero-or-positive history context of one mixed-side path block. -/
inductive FiniteMixedSideLemma11AContext
    (D : ConcretePathDeformation O Cprime)
    (originalHole : IndexedInducedHole G) where
  | first
      (side : DeformationSide)
      (current : (D.reorient side).FullDefinition19Lemma11AData)
      (initial_eq_original :
        Set.range D.initialHole.vertex = Set.range originalHole.vertex)
  | later
      (history : FiniteMixedSideLemma11AHistoryData D originalHole)

namespace FiniteMixedSideLemma11AContext

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- The component side selected for the represented block. -/
def side
    (X : FiniteMixedSideLemma11AContext D originalHole) :
    DeformationSide :=
  match X with
  | .first side _ _ => side
  | .later H => H.currentSide

/-- The local Definition 19 data for the represented oriented block. -/
def currentData
    (X : FiniteMixedSideLemma11AContext D originalHole) :
    (D.reorient X.side).FullDefinition19Lemma11AData :=
  match X with
  | .first _ current _ => current
  | .later H => H.current

end FiniteMixedSideLemma11AContext

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Recover the exact zero-or-positive finite history context at trace index
`i`. -/
def contextAt
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    FiniteMixedSideLemma11AContext (X.block i) originalHole :=
  if hi : i.val = 0 then
    .first (X.side i) (X.localData i) (by
      have hindex : i = X.firstIndex := by
        apply Fin.ext
        exact hi
      rw [hindex]
      exact X.originalHole_eq)
  else
    .later (X.finiteHistoryAt i (Nat.pos_of_ne_zero hi))

@[simp] theorem contextAt_side
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    (X.contextAt i).side = X.side i := by
  unfold contextAt
  split <;> rfl

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
