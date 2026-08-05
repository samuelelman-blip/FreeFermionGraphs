import FreeFermionGraphs.ObstructionSearchFiniteMixedTrace
import FreeFermionGraphs.Lemma11BFullDefinition19
import FreeFermionGraphs.Lemma12Palindromic

/-!
# Unobstructed finite deformations and Lemma 16

The manuscript calls a fixed-pairing deformation unobstructed when no vertex
outside its terminal hole is both dependent on a path block and
anticommuting with that block's path operator. Lemma 16 proves that a
commuting dependent vertex outside the terminal hole would, by Lemma 11(b),
produce an earlier anticommuting dependent vertex in the same fixed-pairing
component. Corollaries 9 and 10 then force that earlier witness to remain
outside the terminal hole, contradicting unobstructedness.

This module formalises that argument in two layers. The definition of
unobstructedness and the reduction from the Corollaries 9--10 transport step
to the Lemma 12 criterion are exact. The theorem
`paperLemma16_of_terminalPathTransport` keeps the still-unconstructed global
path-occurrence transport as an explicit premise in its name. It is therefore
not yet the unqualified paper theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

namespace FiniteMixedSideSearchTrace

/-- Manuscript unobstructedness for one finite fixed-pairing deformation.

A dependent vertex outside the terminal hole may not anticommute with the
path block at which it is selected. -/
def IsUnobstructed
    (X : FiniteMixedSideSearchTrace S originalHole) : Prop :=
  ∀ (i : Fin X.blockCount) ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ (X.block i).dependentAt s →
    u ∉ Set.range X.flattened.terminalHole.vertex →
      ¬(X.block i).path.AnticommutesWith u

/-- The remaining global path-occurrence step in the printed proof of Lemma
16.

Lemma 11(b) supplies `u'`, `P`, and all premises after `outside`. The
manuscript then uses Corollaries 9 and 10, together with the later occurrence
of `P`, to prove that `u'` is also outside the terminal hole. This structure
isolates precisely that transport statement. It contains neither the Lemma 12
criterion nor a reverse run. -/
structure Lemma16TerminalPathTransportData
    (X : FiniteMixedSideSearchTrace S originalHole) : Prop where
  earlierWitness_outside :
    ∀ (i : Fin X.blockCount) ⦃s : Nat⦄ ⦃u : V⦄
      ⦃s' : Nat⦄ ⦃u' : V⦄ ⦃P : Set V⦄,
      u ∈ (X.block i).dependentAt s →
      u ∉ Set.range X.flattened.terminalHole.vertex →
      s' < s →
      u' ∈ ((X.block i).reorient (X.side i)).dependentAt s' →
      ((X.block i).reorient (X.side i)).path.AnticommutesWith u' →
      ((X.side i).family O).IsUniqueContainingBDPath u' P →
      u ∈ P →
        u' ∉ Set.range X.flattened.terminalHole.vertex

/-- Lemma 11(b), followed by the explicit terminal path-transport premise,
produces the outside anticommuting witness used in the first sentence of the
proof of Lemma 16. -/
theorem outsideAnticommutingWitness_of_terminalPathTransport
    (X : FiniteMixedSideSearchTrace S originalHole)
    (T : X.Lemma16TerminalPathTransportData)
    (hclaw : G.IsClawFree)
    (i : Fin X.blockCount) ⦃s : Nat⦄ ⦃u : V⦄
    (hu : u ∈ (X.block i).dependentAt s)
    (huOutside : u ∉ Set.range X.flattened.terminalHole.vertex)
    (hcomm : ¬(X.block i).path.AnticommutesWith u) :
    ∃ s' : Nat, ∃ u' : V,
      s' < s ∧
      u' ∈ (X.block i).dependentAt s' ∧
      (X.block i).path.AnticommutesWith u' ∧
      u' ∉ Set.range X.flattened.terminalHole.vertex := by
  let D := (X.block i).reorient (X.side i)
  have huOriented : u ∈ D.dependentAt s := by
    rw [(X.block i).reorient_dependentAt (X.side i) s]
    exact hu
  have hcommOriented : ¬D.path.AnticommutesWith u := by
    simpa [D] using hcomm
  obtain ⟨_hdegree, s', u', P, hs', hu', hanti', hunique, huP⟩ :=
    D.lemma11b_of_fullDefinition19NeighborhoodData
      (X.localData i).neighborhood hclaw huOriented hcommOriented
  have hu'Carrier : u' ∈ (X.block i).dependentAt s' := by
    rw [← (X.block i).reorient_dependentAt (X.side i) s']
    exact hu'
  have hantiCarrier : (X.block i).path.AnticommutesWith u' := by
    simpa [D] using hanti'
  have hu'Outside :
      u' ∉ Set.range X.flattened.terminalHole.vertex :=
    T.earlierWitness_outside i hu huOutside hs' hu' hanti' hunique huP
  exact ⟨s', u', hs', hu'Carrier, hantiCarrier, hu'Outside⟩

/-- Every flattened Definition 20 dependent vertex belongs to a unique
finite path block occurrence represented by the trace. -/
theorem exists_block_dependentAt_of_mem_dependentUnion
    (X : FiniteMixedSideSearchTrace S originalHole)
    {u : V} (hu : u ∈ X.flattened.dependentUnion) :
    ∃ (i : Fin X.blockCount) (s : Nat),
      u ∈ (X.block i).dependentAt s := by
  obtain ⟨k, hk⟩ := X.flattened.mem_dependentUnion_iff.mp hu
  obtain ⟨i, t, hit⟩ := X.stepIndex_surjective k
  have hstep :
      u ∈ (X.block i).deformation.step t |>.dependentSet := by
    rw [← X.step_eq i t, hit]
    exact hk
  refine ⟨i, t.val, ?_⟩
  simpa [ConcretePathDeformation.dependentAt, t.isLt] using hstep

/-- The core implication of Lemma 16. Unobstructedness rules out every
terminal-external dependent vertex once the Corollaries 9--10 transport step
has been supplied. -/
theorem dependentUnion_subset_terminal_of_unobstructed
    (X : FiniteMixedSideSearchTrace S originalHole)
    (T : X.Lemma16TerminalPathTransportData)
    (hclaw : G.IsClawFree)
    (hunobstructed : X.IsUnobstructed) :
    X.flattened.dependentUnion ⊆
      Set.range X.flattened.terminalHole.vertex := by
  intro u hu
  by_contra huOutside
  obtain ⟨i, s, huBlock⟩ :=
    X.exists_block_dependentAt_of_mem_dependentUnion hu
  have hcomm : ¬(X.block i).path.AnticommutesWith u :=
    hunobstructed i huBlock huOutside
  obtain ⟨s', u', _hs', hu', hanti', hu'Outside⟩ :=
    X.outsideAnticommutingWitness_of_terminalPathTransport
      T hclaw i huBlock huOutside hcomm
  exact (hunobstructed i hu' hu'Outside) hanti'

/-- Exact conclusion asserted by manuscript Lemma 16 once the deformation is
represented by a finite block trace and the prime-hole data for Lemma 12 are
fixed. -/
def PaperLemma16Conclusion
    (X : FiniteMixedSideSearchTrace S originalHole)
    (L : X.flattened.Lemma12Definition19Data) : Prop :=
  X.flattened.dependentUnion ⊆
      Set.range X.flattened.terminalHole.vertex ∧
    ∃ finalHole : IndexedInducedHole G,
      FullDefinition19Deformation.ReverseRun
        X.flattened L.primeHole 0 finalHole

/-- Conditional paper-facing bridge for Lemma 16.

The theorem proves both the criterion `U ⊆ C^(m)` and the palindromic reverse
run. Its name records the remaining Corollaries 9--10 occurrence-transport
premise. Once `Lemma16TerminalPathTransportData` and
`Lemma12Definition19Data` are constructed from the literal ordered Definition
19 trace, this bridge can be replaced by the unqualified `paperLemma16`.
-/
theorem paperLemma16_of_terminalPathTransport
    (X : FiniteMixedSideSearchTrace S originalHole)
    (L : X.flattened.Lemma12Definition19Data)
    (T : X.Lemma16TerminalPathTransportData)
    (hclaw : G.IsClawFree)
    (hunobstructed : X.IsUnobstructed) :
    X.PaperLemma16Conclusion L := by
  have hcriterion :=
    X.dependentUnion_subset_terminal_of_unobstructed
      T hclaw hunobstructed
  refine ⟨hcriterion, ?_⟩
  exact X.flattened.lemma12 L hclaw hcriterion

end FiniteMixedSideSearchTrace

end ConcretePathDeformation
end FixedPairingPathFamily
end SimpleGraph
