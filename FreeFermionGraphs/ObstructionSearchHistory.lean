import FreeFermionGraphs.ObstructionSearch
import FreeFermionGraphs.Lemma11ACorollary11History

/-!
# Concrete history geometry for the obstruction search

The initialized obstruction searches start at the same original even hole.
Every path in a nonempty search output is therefore accompanied by either
the first-block Lemma 11 data or a finite earlier Definition 19 history.

This module turns those two cases into a uniform certificate.  In
particular, it derives the Corollary 11 no-shared-witness conclusion for two
distinct search paths from their concrete Lemma 11 histories.  This is the
graph-theoretic input used by the first-common-path argument in the proof of
Lemma 14(iii); no path-owner or path-disjointness conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace Lemma11AHistoryContext

variable {D : ConcretePathDeformation O Cprime}

/-- The common original hole represented by a Lemma 11 history context is
even, in both the zero-history and positive-history cases. -/
theorem originalHole_even
    (X : D.Lemma11AHistoryContext) :
    Even X.originalHole.card := by
  cases X with
  | first F =>
      simpa [Lemma11AHistoryContext.originalHole] using
        F.neighborhood.alternating.initialHole_even
  | later H =>
      simpa [Lemma11AHistoryContext.originalHole] using
        (H.prior 0).neighborhood.alternating.initialHole_even

/-- The original hole of either kind of Lemma 11 history lies in the two
original coloring classes of the fixed-pairing family. -/
theorem originalHole_carrier_subset
    (X : D.Lemma11AHistoryContext) :
    Set.range X.originalHole.vertex ⊆ O.Ca ∪ O.Cb := by
  cases X with
  | first F =>
      intro v hv
      apply
        (F.neighborhood.mechanical.stepGeometry D.firstIndex).before_subset
      simpa [Lemma11AHistoryContext.originalHole,
        ConcretePathDeformation.initialHole] using hv
  | later H =>
      intro v hv
      apply
        ((H.prior 0).neighborhood.mechanical.stepGeometry
          (H.history.block 0).firstIndex).before_subset
      simpa [Lemma11AHistoryContext.originalHole,
        ConcretePathDeformation.initialHole] using hv

/-- The base-step common neighbor of the current path block transports to
the original hole represented by its history context. -/
theorem baseCommonNeighborOn_originalHole
    (X : D.Lemma11AHistoryContext)
    (hclaw : G.IsClawFree) :
    O.BaseCommonNeighborOn D X.originalHole := by
  cases X with
  | first F =>
      intro u hu
      obtain ⟨v, hvInitial, _hvFinal, huv, hjv, hkv, hvCb,
          _hvNotPrime⟩ :=
        D.lemma11ai_commonNeighbor_currentBlock F hclaw hu
      refine ⟨v, ?_, huv, ?_, ?_, hvCb⟩
      · simpa [Lemma11AHistoryContext.originalHole] using hvInitial
      · simpa [ConcretePathDeformation.firstIndex] using hjv
      · simpa [ConcretePathDeformation.firstIndex] using hkv
  | later H =>
      simpa [Lemma11AHistoryContext.originalHole] using
        D.currentBaseCommonNeighborOn H hclaw

end Lemma11AHistoryContext

end ConcretePathDeformation

/-- A path occurring in an obstruction-search output together with the
concrete Definition 19 block and finite Lemma 11 history that produced it.

`originalHole_eq` says that all such histories are rooted at the same
initialized hole.  `prior_output_mem` records the literal execution provenance
of the prior blocks in a positive history: they are earlier paths of the same
search output, not independent auxiliary deformations.  These are
carrier-sensitive data from the actual search trace, not path-disjointness or
ownership conclusions. -/
structure SearchPathHistoryWitness
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G)
    (P : Set V) where
  block : ConcretePathDeformation O Cprime
  context : block.Lemma11AHistoryContext
  path_eq : Set.range block.path.vertex = P
  output_mem : P ∈ S.paths
  prior_output_mem :
    ∀ (H : block.FullDefinition19Lemma11AHistoryData),
      context = .later H →
      ∀ r : Nat, r < H.priorCount →
        Set.range (H.history.block r).path.vertex ∈ S.paths
  originalHole_eq : context.originalHole = originalHole

namespace SearchPathHistoryWitness

/-- Two distinct output paths rooted at one original hole cannot possess a
shared dependent vertex that anticommutes with both path operators.

This is Corollary 11 with its common-neighbor, even-hole, and carrier
hypotheses derived uniformly from the two concrete Lemma 11 histories. -/
theorem noSharedDependentAnticommutingWitness
    {S T : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : SearchPathHistoryWitness S originalHole P)
    (B : SearchPathHistoryWitness T originalHole Q)
    (hclaw : G.IsClawFree)
    (hne : P ≠ Q) :
    ¬SharedDependentAnticommutingWitness
      A.block.path B.block.path
      A.block.dependentAt B.block.dependentAt := by
  have hEven : Even originalHole.card := by
    rw [← A.originalHole_eq]
    exact A.context.originalHole_even
  have hcarrier :
      Set.range originalHole.vertex ⊆ O.Ca ∪ O.Cb := by
    rw [← A.originalHole_eq]
    exact A.context.originalHole_carrier_subset
  have hpathNe :
      Set.range A.block.path.vertex ≠
        Set.range B.block.path.vertex := by
    intro hEq
    apply hne
    rw [← A.path_eq, ← B.path_eq]
    exact hEq
  have hcommonA :
      O.BaseCommonNeighborOn A.block originalHole := by
    exact (congrArg
      (fun H : IndexedInducedHole G =>
        O.BaseCommonNeighborOn A.block H)
      A.originalHole_eq).mp
      (A.context.baseCommonNeighborOn_originalHole hclaw)
  have hcommonB :
      O.BaseCommonNeighborOn B.block originalHole := by
    exact (congrArg
      (fun H : IndexedInducedHole G =>
        O.BaseCommonNeighborOn B.block H)
      B.originalHole_eq).mp
      (B.context.baseCommonNeighborOn_originalHole hclaw)
  exact noSharedDependentAnticommutingWitness_of_concreteBlocks
    A.block B.block A.context.currentData B.context.currentData
    originalHole hclaw hEven hcarrier hpathNe hcommonA hcommonB

end SearchPathHistoryWitness

/-- Concrete path-history data for every path in one obstruction-search
output.  This is the object consumed by the forthcoming first-common-path
induction for Lemma 14(iii). -/
structure SearchHistoryData
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G) where
  witness : ∀ {P : Set V}, P ∈ S.paths →
    SearchPathHistoryWitness S originalHole P

end FixedPairingPathFamily

end SimpleGraph
