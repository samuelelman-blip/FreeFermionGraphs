import FreeFermionGraphs.Lemma11AFullDefinition19HistoryComplete
import FreeFermionGraphs.Lemma11AThreeNeighborClone

/-!
# Exact finite-history form of Lemma 11(a)

This module combines the first-block and positive-history cases.  In
particular, it does not assume that a clone centre lies in `C_a`, and it
covers the manuscript's `r = 0` case directly.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Finite Definition 19 history preceding a current path block.  The
`first` constructor is the previously missing zero-history case. -/
inductive Lemma11AHistoryContext
    (D : ConcretePathDeformation O Cprime) where
  | first (current : D.FullDefinition19Lemma11AData)
  | later (data : D.FullDefinition19Lemma11AHistoryData)

namespace Lemma11AHistoryContext

variable {D : ConcretePathDeformation O Cprime}

/-- The local Definition 19 data for the current block. -/
def currentData (X : D.Lemma11AHistoryContext) :
    D.FullDefinition19Lemma11AData :=
  match X with
  | .first F => F
  | .later H => H.current

/-- The paper's original hole before any path block in the finite history. -/
def originalHole (X : D.Lemma11AHistoryContext) : IndexedInducedHole G :=
  match X with
  | .first _ => D.initialHole
  | .later H => (H.history.block 0).initialHole

end Lemma11AHistoryContext

/-- Lemma 11(a.ii) when the current path is the first Definition 19 block. -/
theorem lemma11aii_of_firstBlock
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      D.initialHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad D.initialHole u := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have hdegree :
      D.finalHole.externalDegree u = 4 ↔
        D.initialHole.externalDegree u = 3 := by
    omega
  constructor
  · intro hfour
    have hthree := hdegree.mp hfour
    have huOutside : u ∉ Set.range D.initialHole.vertex := by
      rintro ⟨q, rfl⟩
      have htwo := D.initialHole.externalDegree_vertex_eq_two q
      omega
    obtain ⟨q, hclone⟩ :=
      D.initialHole.exists_singleVertexDeformation_of_externalDegree_eq_three
        hclaw huOutside hthree
    have hqCa :=
      D.lemma11aii_cloneCenter_mem_ca_of_firstBlock
        F hclaw hu hclone
    have hui : u ∈
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependentSet :=
      D.mem_step_dependentSet_of_mem_dependentAt hu
    have huCd : u ∈ O.Cd :=
      (D.deformation.step
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependent_mem_cd
          (F.neighborhood.mechanical.stepGeometry
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩) hui
    exact ⟨hthree,
      O.hasTypedClone_opposite .ac D.initialHole
        hclone hqCa (by simpa using huCd)⟩
  · rintro ⟨hthree, _hclone⟩
    exact hdegree.mpr hthree

/-- Lemma 11(a.ii) through a nonempty finite prefix, with the original
clone's `C_a` color derived rather than supplied as a premise. -/
theorem lemma11aii_exact_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      (X.history.block 0).initialHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad
          (X.history.block 0).initialHole u := by
  have hdegree :=
    D.lemma11aii_degree_iff_of_fullDefinition19History
      X hclaw hu huPrime hanti
  constructor
  · intro hfour
    have hthree := hdegree.mp hfour
    have huOutside :
        u ∉ Set.range (X.history.block 0).initialHole.vertex := by
      rintro ⟨q, rfl⟩
      have htwo :=
        (X.history.block 0).initialHole.externalDegree_vertex_eq_two q
      omega
    obtain ⟨q, hclone⟩ :=
      IndexedInducedHole.exists_singleVertexDeformation_of_externalDegree_eq_three
        (X.history.block 0).initialHole hclaw huOutside hthree
    have hqCa :=
      D.lemma11aii_cloneCenter_mem_ca_of_fullDefinition19History
        X hclaw hu hclone
    have hui : u ∈
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependentSet :=
      D.mem_step_dependentSet_of_mem_dependentAt hu
    have huCd : u ∈ O.Cd :=
      (D.deformation.step
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependent_mem_cd
          (X.current.neighborhood.mechanical.stepGeometry
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩) hui
    exact ⟨hthree,
      O.hasTypedClone_opposite .ac
        (X.history.block 0).initialHole
        hclone hqCa (by simpa using huCd)⟩
  · rintro ⟨hthree, _hclone⟩
    exact hdegree.mpr hthree

/-- Exact statement of all three clauses of Lemma 11(a), uniformly over
zero or more earlier Definition 19 path blocks. -/
theorem lemma11a_of_historyContext
    (D : ConcretePathDeformation O Cprime)
    (X : D.Lemma11AHistoryContext)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    ((∃ s : Nat, u ∈ D.dependentAt s) ↔
      u ≠ (D.deformation.step D.firstIndex).introduced ∧
        D.finalHole.externalDegree u =
          D.initialHole.externalDegree u + 1) ∧
    (∀ (s : Nat), u ∈ D.dependentAt s →
      ∀ q : Fin D.finalHole.card,
        D.finalHole.externalDegree u = 3 →
        D.finalHole.SingleVertexDeformation u q →
          D.finalHole.vertex q ∈
              Set.range X.originalHole.vertex ∧
            O.HasPairingType .ac u (D.finalHole.vertex q)) ∧
    (∀ (s : Nat), u ∈ D.dependentAt s →
      (D.finalHole.externalDegree u = 4 ↔
        X.originalHole.externalDegree u = 3 ∧
          O.HasTypedClone .ad X.originalHole u)) := by
  refine ⟨D.lemma11a_membership_iff_ne_first_and_degree
    X.currentData hclaw huPrime hanti, ?_, ?_⟩
  · intro s hu q hthree hclone
    cases X with
    | first F =>
        exact D.lemma11ai_of_firstBlock
          F hclaw hu huPrime hanti hthree hclone
    | later H =>
        exact D.lemma11ai_of_fullDefinition19History
          H hclaw hu huPrime hanti hthree hclone
  · intro s hu
    cases X with
    | first F =>
        exact D.lemma11aii_of_firstBlock
          F hclaw hu huPrime hanti
    | later H =>
        exact D.lemma11aii_exact_of_fullDefinition19History
          H hclaw hu huPrime hanti

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
