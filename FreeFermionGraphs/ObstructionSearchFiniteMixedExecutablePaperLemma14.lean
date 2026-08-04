import FreeFermionGraphs.ObstructionSearchFiniteMixedStepTerminalEvent

/-!
# Conditional Lemma 14 bridge from generated finite obstruction-search data

This module packages the strongest currently available finite Lemma 14 route.
Terminal-path parity is derived from local stepwise alternation of the
manuscript path `j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`; no explicit global coordinate partition
is stored. Target commutation is derived from the positive terminal clone,
finite Lemma 11(a), Corollary 11, and parity through the later execution
suffix. Commuting blocks then preserve degree parity, and Lemma 7 forces the
odd terminal degree to remain three. Clone-to-flank adjacency is derived from
the adjacent canonical stopping link. The unequal-centre branch accepts only a
bounded trace carrying an `IsGenerated` derivation from the finite start and
hop constructors.

The route no longer assumes step-by-step `TargetBalanced`, an explicit `j`/`k`
coordinate enumeration, or target commutation. It still does not construct all
stopping and propagation inputs from the literal Definition 19/20 search. The
terminal event supplies local colour alternation, the positive terminal clone,
and the adjacent canonical stopping link. The propagation datum still supplies
a generated trace whose constructors receive the local avoidance and adjacency
facts.

The theorem below is therefore deliberately conditional and must not be named
`paperLemma14` until those remaining inputs are derived from the literal
obstruction-search execution.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Generated terminal and propagation data sufficient for the current
conditional Lemma 14 bridge.

This structure retains only these unresolved provenance inputs:

- the literal Definition 20 fact that initialized vertices lie in `Cprime`;
- local terminal-path colour alternation and endpoint/target membership;
- the positive terminal clone and adjacent canonical stopping link;
- an `IsGenerated` unequal-centre trace whose constructor inputs include the
  local avoidance and adjacency facts used by the manuscript propagation.
-/
structure InitializationFiniteMixedSideExecutableLemma14Data
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  prime : I.InitializationPrimeVertexData
  terminal : InitializationFiniteMixedSideStepTerminalEvent T
  propagation : ∀ hclaw : G.IsClawFree,
    let terminalData :=
      terminal.toLabelledOperationalTerminalData prime hclaw
    let D := terminalData.toOperationalTerminalData.toTerminalTetherData
    FiniteMixedSideDistinctCenterGeneratedPropagationData T D hclaw

namespace InitializationFiniteMixedSideExecutableLemma14Data

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Conditional bridge to the exact four-part conclusion of manuscript
Lemma 14.

The theorem name records the additional generated-data premise. An
unqualified `paperLemma14` may be introduced only after this data is
constructed from the initialized finite obstruction search and claw-freeness.
-/
theorem paperLemma14_of_executableData
    (L : InitializationFiniteMixedSideExecutableLemma14Data T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I := by
  let terminalData :=
    L.terminal.toLabelledOperationalTerminalData L.prime hclaw
  let D := terminalData.toOperationalTerminalData.toTerminalTetherData
  have hgenerated :
      FiniteMixedSideDistinctCenterGeneratedPropagationData T D hclaw := by
    simpa [terminalData, D] using L.propagation hclaw
  exact D.paperLemma14_of_distinctCenterConsequences hclaw
    hgenerated.toTraceData.toDistinctCenterConsequences

end InitializationFiniteMixedSideExecutableLemma14Data

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
