import FreeFermionGraphs.ObstructionSearchTwoSidedMixedLemma11AComplete

/-!
# Uniform Lemma 11(a) contexts for mixed-side histories

A path block in a Definition 19 deformation is either the first block or is
preceded by a positive history.  The preceding blocks may independently use
the `ac` or `bd` component side of the fixed pairing.

This module packages those two cases in one context and exposes the numerical
part of Lemma 11(a.ii) with the manuscript's original hole.  It does not
construct the context from an obstruction-search execution and does not assume
any conclusion of Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- A current Definition 19 path block together with either no earlier block or
an explicitly mixed-side positive history. -/
inductive MixedSideLemma11AHistoryContext
    (D : ConcretePathDeformation O Cprime) where
  | first (side : DeformationSide)
      (current : (D.reorient side).FullDefinition19Lemma11AData)
  | later (data : D.MixedSideFullDefinition19Lemma11AHistoryData)

namespace MixedSideLemma11AHistoryContext

variable {D : ConcretePathDeformation O Cprime}

/-- The manuscript component side used by the current block. -/
def currentSide
    (X : D.MixedSideLemma11AHistoryContext) : DeformationSide :=
  match X with
  | .first side _ => side
  | .later H => H.currentSide

/-- The local Definition 19 data of the current block in its selected side. -/
def currentData
    (X : D.MixedSideLemma11AHistoryContext) :
    (D.reorient X.currentSide).FullDefinition19Lemma11AData := by
  cases X with
  | first side F => exact F
  | later H => exact H.current

/-- The original hole before the first block represented by the context. -/
def originalHole
    (X : D.MixedSideLemma11AHistoryContext) : IndexedInducedHole G :=
  match X with
  | .first _ _ => D.initialHole
  | .later H => H.originalHole

private theorem degree_step_of_reorient
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (u : V)
    (hstep :
      (D.reorient side).finalHole.externalDegree u =
        (D.reorient side).initialHole.externalDegree u + 1) :
    D.finalHole.externalDegree u =
      D.initialHole.externalDegree u + 1 := by
  cases side <;> exact hstep

/-- The numerical clause of Lemma 11(a.ii), uniformly for the first-block and
positive mixed-side-history cases. -/
theorem lemma11aii_degree_iff
    (X : D.MixedSideLemma11AHistoryContext)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      X.originalHole.externalDegree u = 3 := by
  cases X with
  | first side F =>
      have huOriented : u ∈ (D.reorient side).dependentAt s := by
        rw [D.reorient_dependentAt side s]
        exact hu
      have hantiOriented :
          (D.reorient side).path.AnticommutesWith u := by
        simpa using hanti
      have hlocal :=
        ((D.reorient side).lemma11a_membership_iff_ne_first_and_degree
          F hclaw huPrime hantiOriented).mp ⟨s, huOriented⟩
      have hstep :
          D.finalHole.externalDegree u =
            D.initialHole.externalDegree u + 1 :=
        degree_step_of_reorient D side u hlocal.2
      change D.finalHole.externalDegree u = 4 ↔
        D.initialHole.externalDegree u = 3
      omega
  | later H =>
      simpa [originalHole] using
        H.lemma11aii_degree_iff_of_mixedSideHistory
          hclaw hu huPrime hanti

end MixedSideLemma11AHistoryContext

namespace Lemma11AHistoryContext

variable {D : ConcretePathDeformation O Cprime}

/-- Every existing homogeneous history context embeds into the mixed-side
context as the `.ac` special case. -/
def toMixedSide
    (X : D.Lemma11AHistoryContext) :
    D.MixedSideLemma11AHistoryContext :=
  match X with
  | .first F => .first .ac F
  | .later H => .later H.toMixedSide

@[simp] theorem toMixedSide_originalHole
    (X : D.Lemma11AHistoryContext) :
    X.toMixedSide.originalHole = X.originalHole := by
  cases X <;> rfl

end Lemma11AHistoryContext

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
