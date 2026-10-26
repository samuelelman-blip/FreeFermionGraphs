import FreeFermionGraphs.Lemma12VacuityAudit
import FreeFermionGraphs.Lemma11BEvenness
import FreeFermionGraphs.Lemma11BInPathTwoNeighbors
import FreeFermionGraphs.Lemma11BRemovedVertex
import FreeFermionGraphs.EvenHoleIndexedDeformation
import FreeFermionGraphs.IndexedInducedHoleEvenLabeling
import FreeFermionGraphs.BubbleWandEventClassUnique
import FreeFermionGraphs.DeformationClosureRelation

/-!
# Lemma 12 on satisfiable data: the residual-neighbour endpoint alternative

This module repairs the interface of repository Lemma 12 (v1 Lemma 7,
`solutioncriterion`, v1 L1122; appendix proof v1 L1757-1800) and exports the
carrier of its reverse run.

## The defect that is fixed

`Lemma12Definition19Data` (`Lemma12ReverseClone.lean`) demands, in the endpoint
alternative of `endpoint_or_continuation`, that *every* neighbour `v ∈ C'` of the
removed vertex `k` of a step lies on the active path.  `Lemma12VacuityAudit.lean`
proves that this makes the data uninhabited on every claw-free graph
(`lemma12Data_false_of_clawFree`) and incompatible with the criterion
`F.dependentUnion ⊆ C^(m)` on every graph (`lemma12_data_inconsistent`), so
`FullDefinition19Deformation.lemma12` is vacuous as stated.

In v1 the endpoint statement is weaker.  In the palindromic example
(v1 L957-966) the last removed vertex `a_{ℓ-1}` has two neighbours `d_{ℓ-1}`,
`d_ℓ` of `C'` which are adjacent to the introduced vertex `c_{ℓ-1}` and are not
on the path `P`.  What v1 uses (appendix proof of Lemma 7, v1 L1795) is only that a
neighbour `v ∈ C'` of `k` that is *not adjacent to the introduced vertex `j`* (and
is not `j` itself) would contradict `k` being an endpoint of its path.  The relevant
v1 statements are Corollary 6 (`corollary:pathuniqueendpoints`, v1 L1040) and
Corollary 1 (`corollary:vertexcycleneighboring`, v1 L671), which the appendix proof
invokes at v1 L1795.

## What is proved

* `Lemma12ResidualData F`: the structure `Lemma12Definition19Data` with the endpoint
  alternative restricted to residual neighbours,
  `∀ v ∈ C', k ~ v → v ≠ j → ¬ j ~ v → v ∈ activePath`.  All other fields are
  unchanged.  `Lemma12Definition19Data.toResidualData` converts old data into new
  data (the restriction only weakens the hypothesis).
* `exists_reverse_deformation_of_residualEndpoint`: the endpoint step of the
  reverse induction on the new alternative; it is exactly what
  `exists_reverse_deformation_of_residual_impossible` consumes.
* `lemma12_of_residualData`: Lemma 12 for `Lemma12ResidualData` (the build
  induction of `FullDefinition19Deformation.lemma12`, ported).
* `lemma12_carrier_of_residualData`, `lemma12_carrier_even_of_residualData`:
  the reverse run ends at a hole `R` (this is `C~'` of v1 L966, L1203-1241) of
  even length with carrier `C' ⊕ (C ⊕ C^(m))`, and `R ∈ ⟨C'⟩`.  Closure
  memberships independent of the criterion and of any data:
  `ReverseRun.inEvenHoleDeformationClosure` and
  `inEvenHoleDeformationClosure_terminal` (`C^(m) ∈ ⟨C⟩`).
* `Lemma12ResidualExample`: **non-vacuity**.  On a 10-vertex claw-free graph
  realising v1's palindromic path example (v1 L957-966) with `ℓ = 2`
  (a 4-hole `C = (a_0, b_0, a_1, b_1)`, a 6-hole
  `C' = (d_0, c_0, d_1, c_1, d_2, c_2)`, the path `P = c_0 ◇ a_0 ◇ c_1 ◇ a_1` and the
  clones `c_0 ≺_C a_0`, `c_1 ≺_{C^(0,1)} a_1`, with
  `Γ_{C'}(a_0) = d_0 ◇ c_0 ◇ d_1 ◇ c_1` and `Γ_{C'}(a_1) = d_1 ◇ c_1 ◇ d_2`) there are a
  complete Definition 19 deformation `F` with two single-vertex steps, data
  `L : Lemma12ResidualData F`, `G.IsClawFree`, and the criterion
  `F.dependentUnion ⊆ C^(m)`, all at once.  The data uses the continuation
  alternative at step `0` and the residual endpoint alternative at the last step.  Hence
  `lemma12_of_residualData` and `lemma12_carrier_of_residualData` are applied to a
  genuinely inhabited situation (`Lemma12ResidualExample.exists_reverseRun`,
  `Lemma12ResidualExample.reverse_carrier`: the end point of the reverse run is
  `C~' = C' ⊕ P = (d_0, a_0, d_1, a_1, d_2, c_2)`).  On the same `F` the *old* data does
  not exist (`Lemma12ResidualExample.not_nonempty_lemma12Definition19Data`, from
  `Lemma12VacuityAudit.lean`).  The example also satisfies the manuscript's standing
  hypothesis that `h_C` and `h_{C'}` anticommute (v1 L936), in the form that the number of
  edges between `C` and `C'` is odd (`Lemma12ResidualExample.crossEdges_odd`), and
  `W = {c_0}` (`Lemma12ResidualExample.anticommutingVertices_iff`).  In this example every dependent set `U^(r,s)` is empty, so the
  criterion holds trivially, exactly as in v1's palindromic path.

## Fidelity

`Lemma12ResidualData` is a supplied certificate (the path-specific geometry of
Definition 19 is not derived from `(C, C', W)` here), so every theorem consuming it
carries the suffix `_of_residualData`.  The identification of `C~` with
`C ⊕ ∂O` in the text of v1 (L966) is not used: it equals `C^(m)` only when the paths
of the family are pairwise vertex disjoint, while v1 Corollary 8 (`vertextwopathcomponents`,
v1 L1053) allows two path components to share a vertex.  The statements below speak
about the terminal hole `C^(m)` itself.

Correspondence with v1: `C` is `F.initialHole`, `C^(m)` is `F.terminalHole`,
`C'` is `Cprime = range L.primeHole.vertex`, and `C~'` is the end point of the
reverse run.

The other fields of `Lemma12ResidualData` (`removed_mem_original`,
`activePath_subset_boundary`, and the continuation alternative) are unchanged from
`Lemma12Definition19Data`.  They record path geometry of Definition 19 (v1 L978:
`k_{s-1}^{(r)} ∈ C_j`; `P^{(r)} ⊆ ∂O`; consecutive alternating pairs on one path) and are
supplied here as data.  None of them is the conclusion of Lemma 12 (the reverse run),
and all of them hold in the example below.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

open scoped symmDiff

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A single-vertex deformation of an even indexed hole is a deformation step
between even-hole carriers in the sense of `EvenHoleDeformationStep`
(v1 Definitions 10 and 12).

The proof picks an alternating labelling with the same carrier; if the removed
vertex is in the `b` class, the colour names are swapped first so that it
becomes an `a`-vertex, as required by `EvenHoleLabeling.CloneAt`. -/
theorem evenHoleDeformationStep_deform
    (R : IndexedInducedHole G) (hEven : Even R.card)
    {s : V} {q : Fin R.card} (h : R.SingleVertexDeformation s q) :
    EvenHoleDeformationStep G (Set.range R.vertex)
      (Set.range (R.deform h).vertex) := by
  obtain ⟨k, E, hE⟩ := R.exists_evenHoleLabeling hEven
  have hq : R.vertex q ∈ E.carrier := by
    rw [hE]
    exact ⟨q, rfl⟩
  rcases hq with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨hc, hcar⟩ :=
      E.transport_indexedDeformation R h r hE hr.symm
    refine ⟨k, E, s, r, hc, Or.inl ⟨hE.symm, ?_⟩⟩
    rw [← hcar, E.deform_carrier hc]
  · have hE' : E.swapColors.carrier = Set.range R.vertex := by
      rw [E.swapColors_carrier, hE]
    obtain ⟨hc, hcar⟩ :=
      E.swapColors.transport_indexedDeformation R h r hE' hr.symm
    refine ⟨k, E.swapColors, s, r, hc, Or.inl ⟨hE'.symm, ?_⟩⟩
    rw [← hcar, E.swapColors.deform_carrier hc]

end IndexedInducedHole

namespace FixedPairingPathFamily

namespace FullDefinition19Deformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The data used by Lemma 12 with the corrected endpoint alternative (v1 Lemma 7,
`solutioncriterion`, v1 L1122; appendix L1757-1800).

This is `Lemma12Definition19Data` with exactly one field changed.  In
`endpoint_or_continuation` the endpoint alternative only concerns *residual*
neighbours: a neighbour `v ∈ C'` of the removed vertex `k` with `v ≠ j` and
`v` not adjacent to the introduced vertex `j` lies on the active path.  The old
alternative also required this for neighbours of `k` which are adjacent to `j`; for
such vertices it contradicts the palindromic example of v1 (L957-966) and, on
claw-free graphs, the other fields (`lemma12Data_false_of_clawFree`).

This structure is a supplied certificate; theorems consuming it are named
`_of_residualData`. -/
structure Lemma12ResidualData
    (F : FullDefinition19Deformation O Cprime) where
  primeHole : IndexedInducedHole G
  primeHole_carrier : Set.range primeHole.vertex = Cprime
  primeHole_even : Even primeHole.card
  removed_mem_original :
    ∀ i : Fin F.deformation.stepCount,
      (F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex ∈
        Set.range F.initialHole.vertex
  activePath_subset_boundary :
    ∀ i : Fin F.deformation.stepCount,
      Set.range (F.deformation.step i).activePath.vertex ⊆ F.boundary
  endpoint_or_continuation :
    ∀ i : Fin F.deformation.stepCount,
      (∀ {v : V}, v ∈ Cprime →
        G.Adj
          ((F.deformation.step i).before.vertex
            (F.deformation.step i).removedIndex) v →
        v ≠ (F.deformation.step i).introduced →
        ¬G.Adj (F.deformation.step i).introduced v →
        v ∈ Set.range (F.deformation.step i).activePath.vertex) ∨
      Nonempty (Lemma12Continuation F i)

/-- Old Lemma 12 data gives residual data: the residual endpoint alternative is
a restriction of the old one. -/
def Lemma12Definition19Data.toResidualData
    {F : FullDefinition19Deformation O Cprime}
    (L : Lemma12Definition19Data F) : Lemma12ResidualData F where
  primeHole := L.primeHole
  primeHole_carrier := L.primeHole_carrier
  primeHole_even := L.primeHole_even
  removed_mem_original := L.removed_mem_original
  activePath_subset_boundary := L.activePath_subset_boundary
  endpoint_or_continuation := fun i =>
    (L.endpoint_or_continuation i).imp
      (fun hend _v hv hkv _hvj _hjv => hend hv hkv) id

/-- Endpoint case of the reverse step, residual form.  A residual prime
neighbour of the removed vertex is on the active path by the new endpoint
alternative; the active path is part of `∂O`, whereas Lemma 13 puts the same vertex
outside `∂O`.  Compare `exists_reverse_deformation_of_endpoint`, whose hypothesis is
the unrestricted endpoint alternative; together with the other fields of
`Lemma12Definition19Data` that alternative cannot hold on a claw-free graph
(`lemma12Data_false_of_clawFree`). -/
theorem exists_reverse_deformation_of_residualEndpoint
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12ResidualData F)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    (i : Fin F.deformation.stepCount)
    (R : IndexedInducedHole G)
    (hsymm :
      Set.range R.vertex ∆
          Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex)
    (hendpoint : ∀ {v : V}, v ∈ Cprime →
      G.Adj
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) v →
      v ≠ (F.deformation.step i).introduced →
      ¬G.Adj (F.deformation.step i).introduced v →
      v ∈ Set.range (F.deformation.step i).activePath.vertex) :
    ∃ q : Fin R.card,
      R.vertex q = (F.deformation.step i).introduced ∧
      R.SingleVertexDeformation
        ((F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex) q := by
  apply F.exists_reverse_deformation_of_residual_impossible
    hcriterion i R hsymm
  intro v hvR hkv hvj hjv
  obtain ⟨hvPrime, _hvNotTerminal, hvNotBoundary, _hvNotForward⟩ :=
    F.residual_reverse_neighbor
      hcriterion i R hsymm hvR hkv hvj hjv
  exact hvNotBoundary
    (L.activePath_subset_boundary i (hendpoint hvPrime hkv hvj hjv))

/-- Lemma 12 (repository numbering; v1 Lemma 7, `solutioncriterion`, v1 L1122,
appendix proof L1757-1800) on residual data.

If every Definition 20 dependent vertex belongs to the terminal hole, the
complete fixed-pairing deformation `F` has a reverse run from the prime hole
`C'` by vertices of the original hole.  The proof is the build induction of
`FullDefinition19Deformation.lemma12`: at every step the reverse hole and the
forward after-hole differ by the constant set `C' ⊕ C^(m)` (v1 L1787-1789); the
local clone step is the endpoint case (`exists_reverse_deformation_of_residualEndpoint`)
or the five-neighbour contradiction of the continuation case
(`exists_reverse_deformation_of_continuation`).

Conditional on the supplied certificate `L`, and the criterion `hcriterion`. -/
theorem lemma12_of_residualData
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12ResidualData F)
    (hclaw : G.IsClawFree)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex) :
    ∃ finalHole : IndexedInducedHole G,
      ReverseRun F L.primeHole 0 finalHole := by
  have build : ∀ (n : Nat) (hn : n ≤ F.deformation.stepCount),
      ∃ R : IndexedInducedHole G,
        ReverseRun F L.primeHole n R ∧
        Even R.card ∧
        (n = 0 ∨
          ∃ i : Fin F.deformation.stepCount,
            i.val + 1 = n ∧
            Set.range R.vertex ∆
                Set.range (F.deformation.step i).after.vertex =
              Cprime ∆ Set.range F.terminalHole.vertex) := by
    intro n hn
    induction hn using Nat.decreasingInduction with
    | self =>
        refine ⟨L.primeHole, ReverseRun.terminal, L.primeHole_even, ?_⟩
        right
        refine ⟨F.lastIndex, ?_, ?_⟩
        · simp [lastIndex]
          have hpos := F.nonempty
          omega
        · rw [L.primeHole_carrier]
          rfl
    | of_succ k hk ih =>
        obtain ⟨Rnext, hrun, hEven, hstage⟩ := ih
        let i : Fin F.deformation.stepCount := ⟨k, hk⟩
        have hsymm :
            Set.range Rnext.vertex ∆
                Set.range (F.deformation.step i).after.vertex =
              Cprime ∆ Set.range F.terminalHole.vertex := by
          rcases hstage with hkZero | ⟨previous, hprevious, hpreviousSymm⟩
          · omega
          · have hEq : previous = i := by
              apply Fin.ext
              change previous.val = k
              omega
            rw [hEq] at hpreviousSymm
            exact hpreviousSymm
        have hreverse : ∃ q : Fin Rnext.card,
            Rnext.vertex q = (F.deformation.step i).introduced ∧
            Rnext.SingleVertexDeformation
              ((F.deformation.step i).before.vertex
                (F.deformation.step i).removedIndex) q := by
          rcases L.endpoint_or_continuation i with hendpoint | hcontinuation
          · exact F.exists_reverse_deformation_of_residualEndpoint
              L hcriterion i Rnext hsymm hendpoint
          · let K : Lemma12Continuation F i :=
              Classical.choice hcontinuation
            have hconsecutive : k + 1 = K.next.val := by
              simpa [i] using K.consecutive
            have hkNext : k + 1 < F.deformation.stepCount := by
              have hnextLt := K.next.isLt
              omega
            obtain ⟨Rtail, qnext, hqnext, hnext, hRnext, tail⟩ :=
              hrun.exists_head_of_lt hkNext
            subst Rnext
            let nextIndex : Fin F.deformation.stepCount :=
              ⟨k + 1, hkNext⟩
            have hnextEq : nextIndex = K.next := by
              apply Fin.ext
              simpa [nextIndex] using hconsecutive
            exact F.exists_reverse_deformation_of_continuation
              hclaw hcriterion i K nextIndex hnextEq Rtail qnext
              (by simpa [nextIndex] using hqnext)
              (by simpa [nextIndex] using hnext)
              (by simpa using hEven)
              (by simpa [nextIndex] using hsymm)
        obtain ⟨q, hq, hdeform⟩ := hreverse
        let Rcurrent : IndexedInducedHole G := Rnext.deform hdeform
        have hrunCurrent : ReverseRun F L.primeHole k Rcurrent := by
          exact ReverseRun.step hk hrun q hq hdeform
            (L.removed_mem_original i)
        have hEvenCurrent : Even Rcurrent.card := by
          simpa [Rcurrent] using hEven
        have hnewBefore :
            Set.range Rcurrent.vertex ∆
                Set.range (F.deformation.step i).before.vertex =
              Cprime ∆ Set.range F.terminalHole.vertex := by
          let S := F.deformation.step i
          let j : V := S.introduced
          let removed : V := S.before.vertex S.removedIndex
          have hforwardReverse :
              S.after.SingleVertexDeformation removed S.removedIndex :=
            S.deformation.reverse
          have hcenter : S.after.vertex S.removedIndex = j := by
            simp [ConcreteDeformationStep.after, j]
          have hbeforeSwap :
              Set.range S.before.vertex =
                Set.insert removed
                  (Set.range S.after.vertex \ {j}) := by
            calc
              Set.range S.before.vertex =
                  Set.range (S.after.deform hforwardReverse).vertex :=
                S.deformation.reverse_deform_range_eq.symm
              _ = Set.insert removed
                    (Set.range S.after.vertex \
                      {S.after.vertex S.removedIndex}) :=
                S.after.deform_range_eq hforwardReverse
              _ = Set.insert removed
                    (Set.range S.after.vertex \ {j}) := by rw [hcenter]
          calc
            Set.range Rcurrent.vertex ∆ Set.range S.before.vertex =
                Set.insert removed (Set.range Rnext.vertex \ {j}) ∆
                  Set.insert removed (Set.range S.after.vertex \ {j}) := by
              rw [Rnext.deform_range_eq hdeform, hq, hbeforeSwap]
            _ = Set.range Rnext.vertex ∆ Set.range S.after.vertex :=
              symmDiff_same_swap
                (by exact ⟨q, hq⟩)
                hdeform.outside
                S.introduced_mem_after
                S.removed_not_mem_after
            _ = Cprime ∆ Set.range F.terminalHole.vertex := by
              simpa [S] using hsymm
        refine ⟨Rcurrent, hrunCurrent, hEvenCurrent, ?_⟩
        by_cases hkZero : k = 0
        · exact Or.inl hkZero
        · right
          let previous : Fin F.deformation.stepCount :=
            ⟨k - 1, by omega⟩
          refine ⟨previous, by simp [previous]; omega, ?_⟩
          have hchain :
              Set.range (F.deformation.step previous).after.vertex =
                Set.range (F.deformation.step i).before.vertex :=
            F.deformation.carrier_chain (i := previous) (j := i) (by
              simp [previous, i]
              omega)
          rw [hchain]
          exact hnewBefore
  obtain ⟨R, hrun, _hEven, _hstage⟩ := build 0 (Nat.zero_le _)
  exact ⟨R, hrun⟩

/-- The original `lemma12` is a corollary of `lemma12_of_residualData` (through
`Lemma12Definition19Data.toResidualData`); the converse is false, since the old data
is uninhabited on the example of this module (`Lemma12ResidualExample`). -/
theorem lemma12_via_residualData
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12Definition19Data F)
    (hclaw : G.IsClawFree)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex) :
    ∃ finalHole : IndexedInducedHole G,
      ReverseRun F L.primeHole 0 finalHole :=
  F.lemma12_of_residualData L.toResidualData hclaw hcriterion

/-- A reverse run from an even hole stays in the deformation closure of the
starting carrier, and every hole along it has even length.  (v1 L966, L1203:
`C~' ∈ ⟨C'⟩`.)  No Lemma 12 data or criterion is used: only that each reverse
step is a literal single-vertex deformation. -/
theorem ReverseRun.inEvenHoleDeformationClosure
    {F : FullDefinition19Deformation O Cprime}
    {P R : G.IndexedInducedHole} {n : ℕ}
    (h : ReverseRun F P n R) (hP : Even P.card) :
    InEvenHoleDeformationClosure G (Set.range P.vertex)
        (Set.range R.vertex) ∧
      Even R.card := by
  induction h with
  | terminal => exact ⟨InEvenHoleDeformationClosure.refl _, hP⟩
  | step hn tail q removedVertex deformation introduced_mem_original ih =>
      obtain ⟨hclosure, hEven⟩ := ih
      exact ⟨hclosure.tail
        (IndexedInducedHole.evenHoleDeformationStep_deform _ hEven
          deformation), hEven⟩

/-- Along a complete forward deformation from an even initial hole, every
hole before a step has even length. -/
theorem even_card_before
    (F : FullDefinition19Deformation O Cprime)
    (hEven : Even F.initialHole.card) :
    ∀ (n : ℕ) (hn : n < F.deformation.stepCount),
      Even (F.deformation.step ⟨n, hn⟩).before.card := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact hEven
  | succ n ih =>
      intro hn
      have hprev : n < F.deformation.stepCount := by omega
      have hchain := F.deformation.carrier_chain
        (i := ⟨n, hprev⟩) (j := ⟨n + 1, hn⟩) rfl
      have hcard :=
        IndexedInducedHole.card_eq_of_range_eq _ _ hchain
      rw [← hcard]
      exact ih hprev

/-- Every hole `(step n).after` of a complete forward deformation from an
even initial hole is in the deformation closure of the initial carrier. -/
theorem inEvenHoleDeformationClosure_after
    (F : FullDefinition19Deformation O Cprime)
    (hEven : Even F.initialHole.card) :
    ∀ (n : ℕ) (hn : n < F.deformation.stepCount),
      InEvenHoleDeformationClosure G (Set.range F.initialHole.vertex)
        (Set.range (F.deformation.step ⟨n, hn⟩).after.vertex) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact (InEvenHoleDeformationClosure.refl _).tail
        (IndexedInducedHole.evenHoleDeformationStep_deform _
          (F.even_card_before hEven 0 hn)
          (F.deformation.step ⟨0, hn⟩).deformation)
  | succ n ih =>
      intro hn
      have hprev : n < F.deformation.stepCount := by omega
      have hchain := F.deformation.carrier_chain
        (i := ⟨n, hprev⟩) (j := ⟨n + 1, hn⟩) rfl
      have hclosure := ih hprev
      rw [hchain] at hclosure
      exact hclosure.tail
        (IndexedInducedHole.evenHoleDeformationStep_deform _
          (F.even_card_before hEven (n + 1) hn)
          (F.deformation.step ⟨n + 1, hn⟩).deformation)

/-- A complete forward deformation from an even initial hole ends in the
deformation closure of the initial carrier: `C^(m) ∈ ⟨C⟩` (v1 L966,
L1203).  No Lemma 12 data or criterion is used. -/
theorem inEvenHoleDeformationClosure_terminal
    (F : FullDefinition19Deformation O Cprime)
    (hEven : Even F.initialHole.card) :
    InEvenHoleDeformationClosure G (Set.range F.initialHole.vertex)
      (Set.range F.terminalHole.vertex) :=
  F.inEvenHoleDeformationClosure_after hEven _
    (by
      have hpos := F.nonempty
      omega)

/-- The constant symmetric difference along a reverse run (v1 appendix
L1787-1789: `C'^(r,s) ⊕ C^(r,s) = C' ⊕ C^(m)`).

Let `R` be the hole reached after traversing the steps `n, n+1, …` in reverse,
starting from a hole `P` with carrier `C'`.  Then `R ⊕ (step i).after` equals
`C' ⊕ C^(m)` for `i = n - 1`, and `R ⊕ (step i).before` equals it for
`i = n`.  The proof only uses the local swap performed by each reverse step. -/
theorem ReverseRun.symmDiff_invariant
    {F : FullDefinition19Deformation O Cprime}
    {P R : G.IndexedInducedHole} {n : ℕ}
    (h : ReverseRun F P n R) (hP : Set.range P.vertex = Cprime) :
    (∀ i : Fin F.deformation.stepCount, i.val + 1 = n →
      Set.range R.vertex ∆ Set.range (F.deformation.step i).after.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex) ∧
    (∀ i : Fin F.deformation.stepCount, i.val = n →
      Set.range R.vertex ∆ Set.range (F.deformation.step i).before.vertex =
        Cprime ∆ Set.range F.terminalHole.vertex) := by
  induction h with
  | terminal =>
      refine ⟨?_, ?_⟩
      · intro i hi
        have hlast : i = F.lastIndex := by
          apply Fin.ext
          have hpos := F.nonempty
          simp only [lastIndex]
          omega
        subst hlast
        rw [hP]
        rfl
      · intro i hi
        exact absurd hi (Nat.ne_of_lt i.isLt)
  | @step n hn R' tail q removedVertex deformation introduced_mem_original ih =>
      obtain ⟨ihAfter, _⟩ := ih
      let S := F.deformation.step ⟨n, hn⟩
      have hsymm :
          Set.range R'.vertex ∆ Set.range S.after.vertex =
            Cprime ∆ Set.range F.terminalHole.vertex :=
        ihAfter ⟨n, hn⟩ rfl
      have hbefore :
          Set.range (R'.deform deformation).vertex ∆
              Set.range S.before.vertex =
            Cprime ∆ Set.range F.terminalHole.vertex := by
        let j : V := S.introduced
        let removed : V := S.before.vertex S.removedIndex
        have hforwardReverse :
            S.after.SingleVertexDeformation removed S.removedIndex :=
          S.deformation.reverse
        have hcenter : S.after.vertex S.removedIndex = j := by
          simp [ConcreteDeformationStep.after, j]
        have hbeforeSwap :
            Set.range S.before.vertex =
              Set.insert removed (Set.range S.after.vertex \ {j}) := by
          calc
            Set.range S.before.vertex =
                Set.range (S.after.deform hforwardReverse).vertex :=
              S.deformation.reverse_deform_range_eq.symm
            _ = Set.insert removed
                  (Set.range S.after.vertex \
                    {S.after.vertex S.removedIndex}) :=
              S.after.deform_range_eq hforwardReverse
            _ = Set.insert removed
                  (Set.range S.after.vertex \ {j}) := by rw [hcenter]
        calc
          Set.range (R'.deform deformation).vertex ∆
              Set.range S.before.vertex =
              Set.insert removed (Set.range R'.vertex \ {j}) ∆
                Set.insert removed (Set.range S.after.vertex \ {j}) := by
            rw [R'.deform_range_eq deformation, removedVertex, hbeforeSwap]
          _ = Set.range R'.vertex ∆ Set.range S.after.vertex :=
            symmDiff_same_swap
              (by exact ⟨q, removedVertex⟩)
              deformation.outside
              S.introduced_mem_after
              S.removed_not_mem_after
          _ = Cprime ∆ Set.range F.terminalHole.vertex := hsymm
      refine ⟨?_, ?_⟩
      · intro i hi
        have hchain := F.deformation.carrier_chain
          (i := i) (j := ⟨n, hn⟩) hi
        rw [hchain]
        exact hbefore
      · intro i hi
        have hEq : i = ⟨n, hn⟩ := Fin.ext hi
        subst hEq
        exact hbefore

/-- Lemma 12, carrier form with even length (v1 `solutioncriterion`, v1 L1122;
appendix v1 L1787-1789; used at v1 L966 and L1203-1241).

Under the Lemma 12 hypotheses the reverse run from the prime hole `C'` ends at a
hole `R` (this is `C~'`) of even length with carrier `C' ⊕ (C ⊕ C^(m))`, and
`R ∈ ⟨C'⟩`.  Here `C = F.initialHole` and `C^(m) = F.terminalHole`.

Conditional on the supplied certificate `L` and on Lemma 12's own criterion. -/
theorem lemma12_carrier_even_of_residualData
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12ResidualData F)
    (hclaw : G.IsClawFree)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex) :
    ∃ R : G.IndexedInducedHole,
      ReverseRun F L.primeHole 0 R ∧ Even R.card ∧
      Set.range R.vertex =
        symmDiff Cprime
          (symmDiff (Set.range F.initialHole.vertex)
            (Set.range F.terminalHole.vertex)) ∧
      InEvenHoleDeformationClosure G Cprime (Set.range R.vertex) := by
  obtain ⟨R, hrun⟩ := F.lemma12_of_residualData L hclaw hcriterion
  obtain ⟨hclosure, hEven⟩ :=
    hrun.inEvenHoleDeformationClosure L.primeHole_even
  rw [L.primeHole_carrier] at hclosure
  refine ⟨R, hrun, hEven, ?_, hclosure⟩
  have h0 :=
    (hrun.symmDiff_invariant L.primeHole_carrier).2 ⟨0, F.nonempty⟩ rfl
  have h0' : Set.range R.vertex ∆ Set.range F.initialHole.vertex =
      Cprime ∆ Set.range F.terminalHole.vertex := h0
  ext v
  have hv := congrArg (fun A : Set V => v ∈ A) h0'
  simp only [Set.mem_symmDiff, eq_iff_iff] at hv ⊢
  tauto

/-- Lemma 12, carrier form (v1 `solutioncriterion`, v1 L1122; appendix v1
L1787-1789; used at v1 L966 and L1203-1241): the reverse run ends at `C~'` with
carrier `C' ⊕ (C ⊕ C^(m))` and `C~' ∈ ⟨C'⟩`.  Conditional on the supplied
certificate `L` and on the criterion. -/
theorem lemma12_carrier_of_residualData
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12ResidualData F)
    (hclaw : G.IsClawFree)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex) :
    ∃ R : G.IndexedInducedHole,
      ReverseRun F L.primeHole 0 R ∧
      Set.range R.vertex =
        symmDiff Cprime
          (symmDiff (Set.range F.initialHole.vertex)
            (Set.range F.terminalHole.vertex)) ∧
      InEvenHoleDeformationClosure G Cprime (Set.range R.vertex) := by
  obtain ⟨R, hrun, _hEven, hcarrier, hclosure⟩ :=
    F.lemma12_carrier_even_of_residualData L hclaw hcriterion
  exact ⟨R, hrun, hcarrier, hclosure⟩

end FullDefinition19Deformation

end FixedPairingPathFamily

/-! ### Non-vacuity: the palindromic path example of v1 with `ℓ = 2`

The graph has ten vertices, numbered as follows.

* `C = (a_0, b_0, a_1, b_1) = (0, 1, 2, 3)`, a 4-hole.
* `C' = (d_0, c_0, d_1, c_1, d_2, c_2) = (4, 5, 6, 7, 8, 9)`, a 6-hole.
* `P = c_0 ◇ a_0 ◇ c_1 ◇ a_1 = (5, 0, 7, 2)`, a component of `G[C_a ⊕ C'_c]`.
* Step `0`: `c_0 ≺_C a_0`, so `c_0` is adjacent to `a_0, b_0, b_1`.
* Step `1`: `c_1 ≺_{C^(0,1)} a_1` in `C^(0,1) = (c_0, b_0, a_1, b_1)`, so `c_1` is adjacent
  to `a_1, b_0, b_1` and not to `c_0`.
* Palindromic endpoint (v1 L957-966): `Γ_{C'}(a_0) = d_0 ◇ c_0 ◇ d_1 ◇ c_1` and
  `Γ_{C'}(a_1) = d_1 ◇ c_1 ◇ d_2`, so the removed vertex `a_1` of the last step has
  the `C'`-neighbours `d_1`, `d_2` that are *not* on `P` (and are both adjacent to `c_1`).
* The remaining adjacencies `b_0 ~ d_1, d_2` and `b_1 ~ d_0, d_1` are one of four choices
  (exhaustive search over the eight undetermined pairs between `{b_0, b_1}` and
  `{d_0, d_1, d_2, c_2}`) that make the graph claw-free.  This choice also makes the
  number of edges between `C` and `C'` odd (fifteen), i.e. `h_C` and `h_{C'}` anticommute,
  and `W = {c_0}`.  All Lean statements below are checked by kernel evaluation.

The last step has `a_1 ∉ C'` with `C'`-neighbours `d_1`, `d_2` off the path, so the
unrestricted endpoint alternative of `Lemma12Definition19Data` fails; the residual
alternative holds because both are adjacent to `c_1`. -/

namespace Lemma12ResidualExample

open FixedPairingPathFamily FixedPairingPathFamily.FullDefinition19Deformation

/-- The edges of the example graph, in the numbering described above: the two holes,
the clone and path edges, and the palindromic endpoint adjacencies. -/
def edgeList : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(0,3),
   (4,5),(5,6),(6,7),(7,8),(8,9),(4,9),
   (0,5),(1,5),(3,5),
   (1,7),(2,7),(3,7),
   (0,7),
   (0,4),(0,6),
   (2,6),(2,8),
   (1,6),(1,8),(3,4),(3,6)]

/-- The ten-vertex example graph. -/
def graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun x y : Fin 10 => (x.val, y.val) ∈ edgeList)

instance : DecidableRel graph.Adj := fun x y => by unfold graph; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The example graph is claw-free. -/
theorem clawFree : graph.IsClawFree := by
  have h : ∀ center a b c : Fin 10, graph.Adj center a → graph.Adj center b →
      graph.Adj center c → a ≠ b → a ≠ c → b ≠ c →
      graph.Adj a b ∨ graph.Adj a c ∨ graph.Adj b c := by
    decide +kernel
  exact fun center a b c => h center a b c

/-- The original hole `C = (a_0, b_0, a_1, b_1) = (0, 1, 2, 3)`. -/
def holeC : IndexedInducedHole graph where
  card := 4
  four_le_card := le_rfl
  vertex := fun i => ⟨i.val, by have := i.isLt; omega⟩
  injective := by decide +kernel
  adj_iff := by
    unfold CyclicAdjacent
    decide +kernel

/-- The prime hole `C' = (d_0, c_0, d_1, c_1, d_2, c_2) = (4, 5, 6, 7, 8, 9)`. -/
def holeC' : IndexedInducedHole graph where
  card := 6
  four_le_card := by decide
  vertex := fun i => ⟨i.val + 4, by have := i.isLt; omega⟩
  injective := by decide +kernel
  adj_iff := by
    unfold CyclicAdjacent
    decide +kernel

/-- The deformation path `P = c_0 ◇ a_0 ◇ c_1 ◇ a_1 = (5, 0, 7, 2)`. -/
def path : IndexedInducedPath graph where
  card := 4
  nonempty := by decide
  vertex := ![5, 0, 7, 2]
  injective := by decide +kernel
  adj_iff := by decide +kernel

/-- The carrier of the prime hole. -/
def primeCarrier : Set (Fin 10) := Set.range holeC'.vertex

/-- The fixed-pairing path family with the single `(a, c)` path `P`. -/
def family : FixedPairingPathFamily graph where
  Ca := {0, 2}
  Cb := {1, 3}
  Cc := {5, 7, 9}
  Cd := {4, 6, 8}
  acPaths := {Set.range path.vertex}
  bdPaths := ∅
  ac_pairwise := Set.pairwise_singleton _ _
  bd_pairwise := Set.pairwise_empty _
  ac_subset := by
    rintro P rfl
    rintro _ ⟨i, rfl⟩
    have h : ∀ i : Fin path.card, path.vertex i = 5 ∨ path.vertex i = 0 ∨
        path.vertex i = 7 ∨ path.vertex i = 2 := by decide +kernel
    rcases h i with h | h | h | h <;> simp [h]
  bd_subset := by
    intro P hP
    exact absurd hP (Set.notMem_empty P)
  ac_induced := by
    rintro P rfl
    exact ⟨path, rfl⟩
  bd_induced := by
    intro P hP
    exact absurd hP (Set.notMem_empty P)

/-- Step `0`: `c_0 = 5` is a clone of `a_0 = 0` in `C`. -/
theorem singleVertexDeformation₀ :
    holeC.SingleVertexDeformation (5 : Fin 10) (⟨0, by decide⟩ : Fin holeC.card) where
  outside := by
    have h : ∀ i : Fin holeC.card, holeC.vertex i ≠ 5 := by decide +kernel
    rintro ⟨i, hi⟩
    exact h i hi
  adj_iff := by decide +kernel

/-- The first concrete step: replace `a_0` by `c_0` in `C`. -/
def step₀ : ConcreteDeformationStep family primeCarrier where
  before := holeC
  introduced := 5
  removedIndex := ⟨0, by decide⟩
  deformation := singleVertexDeformation₀
  activePath := path
  activePath_mem := Or.inl rfl
  introduced_mem_activePath := ⟨⟨0, by decide⟩, rfl⟩
  removed_mem_activePath := ⟨⟨1, by decide⟩, rfl⟩

/-- Step `1`: `c_1 = 7` is a clone of `a_1 = 2` in `C^(0,1) = (c_0, b_0, a_1, b_1)`. -/
theorem singleVertexDeformation₁ :
    step₀.after.SingleVertexDeformation (7 : Fin 10)
      (⟨2, by decide⟩ : Fin step₀.after.card) where
  outside := by
    have h : ∀ i : Fin step₀.after.card, step₀.after.vertex i ≠ 7 := by decide +kernel
    rintro ⟨i, hi⟩
    exact h i hi
  adj_iff := by decide +kernel

/-- The second concrete step: replace `a_1` by `c_1` in `C^(0,1)`. -/
def step₁ : ConcreteDeformationStep family primeCarrier where
  before := step₀.after
  introduced := 7
  removedIndex := ⟨2, by decide⟩
  deformation := singleVertexDeformation₁
  activePath := path
  activePath_mem := Or.inl rfl
  introduced_mem_activePath := ⟨⟨2, by decide⟩, rfl⟩
  removed_mem_activePath := ⟨⟨3, by decide⟩, rfl⟩

/-- The two-step deformation of `C` along `P`. -/
def deformation : ConcreteDeformation family primeCarrier where
  stepCount := 2
  step := ![step₀, step₁]
  carrier_chain := by
    intro i j h
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    change i + 1 = j at h
    have hi' : i = 0 := by change i < 2 at hi; change j < 2 at hj; omega
    have hj' : j = 1 := by omega
    subst hi' hj'
    rfl

/-- The complete Definition 19 deformation of the example. -/
def full : FullDefinition19Deformation family primeCarrier where
  deformation := deformation
  nonempty := by decide
  introduced_mem_prime := by
    intro i
    obtain ⟨i, hi⟩ := i
    have : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases this with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl⟩
  removedPrime_hasSuccessor := by
    intro i h
    exfalso
    have hne : ∀ q : Fin holeC'.card, holeC'.vertex q ≠ (0 : Fin 10) ∧
        holeC'.vertex q ≠ (2 : Fin 10) := by decide +kernel
    obtain ⟨q, hq⟩ := h
    obtain ⟨i, hi⟩ := i
    have : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases this with rfl | rfl
    · exact (hne q).1 hq
    · exact (hne q).2 hq

/-- The continuation datum from step `0` to step `1`. -/
def continuation : Lemma12Continuation full ⟨0, by decide⟩ where
  next := ⟨1, by decide⟩
  consecutive := rfl
  samePath := rfl
  removed_adj_nextIntroduced := by decide +kernel
  introduced_ne_nextIntroduced := by decide +kernel
  introduced_ne_nextRemoved := by decide +kernel
  introduced_not_adj_nextIntroduced := by decide +kernel
  introduced_not_adj_nextRemoved := by decide +kernel

/-- The residual Lemma 12 data of the example.  Step `0` uses the continuation
alternative; step `1` (the last) uses the residual endpoint alternative: the
`C'`-neighbours `d_1`, `d_2` of `a_1` which are off the path are both adjacent to
`c_1`. -/
def residualData : Lemma12ResidualData full where
  primeHole := holeC'
  primeHole_carrier := rfl
  primeHole_even := ⟨3, rfl⟩
  removed_mem_original := by
    intro i
    obtain ⟨i, hi⟩ := i
    have : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases this with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl⟩
  activePath_subset_boundary := by
    intro i
    have hp : (full.deformation.step i).activePath = path := by
      obtain ⟨i, hi⟩ := i
      have : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
      rcases this with rfl | rfl <;> rfl
    rw [hp]
    rintro _ ⟨q, rfl⟩
    have h : ∀ q : Fin path.card, path.vertex q = 5 ∨ path.vertex q = 0 ∨
        path.vertex q = 7 ∨ path.vertex q = 2 := by decide +kernel
    have h0 : (full.deformation.step ⟨0, by decide⟩).introduced = 5 := rfl
    have h0' : (full.deformation.step ⟨0, by decide⟩).before.vertex
        (full.deformation.step ⟨0, by decide⟩).removedIndex = 0 := rfl
    have h1 : (full.deformation.step ⟨1, by decide⟩).introduced = 7 := rfl
    have h1' : (full.deformation.step ⟨1, by decide⟩).before.vertex
        (full.deformation.step ⟨1, by decide⟩).removedIndex = 2 := rfl
    rcases h q with h | h | h | h
    · exact ⟨⟨0, by decide⟩, Or.inl (h.trans h0.symm)⟩
    · exact ⟨⟨0, by decide⟩, Or.inr (h.trans h0'.symm)⟩
    · exact ⟨⟨1, by decide⟩, Or.inl (h.trans h1.symm)⟩
    · exact ⟨⟨1, by decide⟩, Or.inr (h.trans h1'.symm)⟩
  endpoint_or_continuation := by
    intro i
    obtain ⟨i, hi⟩ := i
    have : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases this with rfl | rfl
    · exact Or.inr ⟨continuation⟩
    · left
      intro v hv hkv hvj hjv
      exfalso
      obtain ⟨q, rfl⟩ := hv
      have h : ∀ q : Fin holeC'.card, graph.Adj 2 (holeC'.vertex q) →
          holeC'.vertex q ≠ 7 → ¬graph.Adj 7 (holeC'.vertex q) → False := by
        decide +kernel
      exact h q hkv hvj hjv

/-- The criterion of Lemma 12 holds in the example: every dependent set is empty. -/
theorem criterion : full.dependentUnion ⊆ Set.range full.terminalHole.vertex := by
  rintro u ⟨i, hu⟩
  exfalso
  obtain ⟨⟨q, rfl⟩, hadj, hne, hnadj⟩ := hu
  obtain ⟨i, hi⟩ := i
  have : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  rcases this with rfl | rfl
  · have h : ∀ q : Fin holeC'.card, graph.Adj (holeC'.vertex q) 5 →
        holeC'.vertex q ≠ 0 → graph.Adj (holeC'.vertex q) 0 := by
      decide +kernel
    exact hnadj (h q hadj hne)
  · have h : ∀ q : Fin holeC'.card, graph.Adj (holeC'.vertex q) 7 →
        holeC'.vertex q ≠ 2 → graph.Adj (holeC'.vertex q) 2 := by
      decide +kernel
    exact hnadj (h q hadj hne)

/-- Lemma 12 (`lemma12_of_residualData`) applied to the example. -/
theorem exists_reverseRun :
    ∃ R : IndexedInducedHole graph, ReverseRun full residualData.primeHole 0 R :=
  full.lemma12_of_residualData residualData clawFree criterion

/-- On the same deformation the unrestricted Lemma 12 data does not exist
(`lemma12Data_false_of_clawFree`): the residual alternative is what makes the
hypotheses of Lemma 12 satisfiable. -/
theorem not_nonempty_lemma12Definition19Data :
    ¬ Nonempty (Lemma12Definition19Data full) :=
  not_nonempty_lemma12Data_of_clawFree full clawFree

/-- The reverse run of the example ends at `C~' = C' ⊕ P = (d_0, a_0, d_1, a_1, d_2, c_2)`,
with carrier `{a_0, a_1, d_0, d_1, d_2, c_2} = {0, 2, 4, 6, 8, 9}`
(`lemma12_carrier_of_residualData`). -/
theorem reverse_carrier :
    ∃ R : IndexedInducedHole graph, ReverseRun full residualData.primeHole 0 R ∧
      Set.range R.vertex = {0, 2, 4, 6, 8, 9} := by
  obtain ⟨R, hrun, hcar, _⟩ :=
    full.lemma12_carrier_of_residualData residualData clawFree criterion
  refine ⟨R, hrun, ?_⟩
  rw [hcar]
  ext v
  have hC : ∀ v : Fin 10, (v ∈ Set.range full.initialHole.vertex ↔ v.val < 4) := by
    simp only [Set.mem_range]
    decide +kernel
  have hT : ∀ v : Fin 10, (v ∈ Set.range full.terminalHole.vertex ↔
      (v = 5 ∨ v = 1 ∨ v = 7 ∨ v = 3)) := by
    simp only [Set.mem_range]
    decide +kernel
  have hP : ∀ v : Fin 10, (v ∈ primeCarrier ↔ 4 ≤ v.val) := by
    simp only [primeCarrier, Set.mem_range]
    decide +kernel
  have key : ∀ v : Fin 10,
      (v ∈ symmDiff primeCarrier (symmDiff (Set.range full.initialHole.vertex)
        (Set.range full.terminalHole.vertex))) ↔ v ∈ ({0, 2, 4, 6, 8, 9} : Set (Fin 10)) := by
    intro v
    simp only [Set.mem_symmDiff, Set.mem_insert_iff, Set.mem_singleton_iff, hC, hT, hP]
    revert v
    decide +kernel
  exact key v

/-- The number of edges between `C = {0, 1, 2, 3}` and `C' = {4, ..., 9}` is odd, so that
`h_C` and `h_{C'}` anticommute for any Pauli representation of the frustration graph
(the standing assumption of v1 L936). -/
theorem crossEdges_odd :
    ((((Finset.univ.filter fun x : Fin 10 => x.val < 4) ×ˢ
        (Finset.univ.filter fun x : Fin 10 => 4 ≤ x.val)).filter
          fun p => graph.Adj p.1 p.2).card) % 2 = 1 := by
  decide +kernel

/-- The vertices of `C'` whose term anticommutes with `h_C`, i.e. with an odd number of
neighbours in `C`, form the set `W = {c_0}` of v1 L1006: `|W| = 1` is odd, as v1
requires (L1013). -/
theorem anticommutingVertices_iff :
    ∀ v : Fin 10, 4 ≤ v.val →
      (((Finset.univ.filter fun x : Fin 10 => x.val < 4 ∧ graph.Adj v x).card % 2 = 1) ↔
        v = 5) := by
  decide +kernel

end Lemma12ResidualExample

/-- Non-vacuity of Lemma 12 on residual data: there are a claw-free graph, a
fixed-pairing path family, a complete Definition 19 deformation `F` with
`L : Lemma12ResidualData F` and the criterion `F.dependentUnion ⊆ C^(m)`, such that
the original `Lemma12Definition19Data` does not exist for `F`. -/
theorem exists_lemma12ResidualData_with_criterion :
    ∃ (G : SimpleGraph (Fin 10)) (O : FixedPairingPathFamily G) (Cprime : Set (Fin 10))
      (F : FixedPairingPathFamily.FullDefinition19Deformation O Cprime)
      (_L : FixedPairingPathFamily.FullDefinition19Deformation.Lemma12ResidualData F),
      G.IsClawFree ∧ F.dependentUnion ⊆ Set.range F.terminalHole.vertex ∧
        ¬ Nonempty
          (FixedPairingPathFamily.FullDefinition19Deformation.Lemma12Definition19Data F) :=
  ⟨Lemma12ResidualExample.graph, Lemma12ResidualExample.family,
    Lemma12ResidualExample.primeCarrier, Lemma12ResidualExample.full,
    Lemma12ResidualExample.residualData, Lemma12ResidualExample.clawFree,
    Lemma12ResidualExample.criterion,
    Lemma12ResidualExample.not_nonempty_lemma12Definition19Data⟩

end SimpleGraph
