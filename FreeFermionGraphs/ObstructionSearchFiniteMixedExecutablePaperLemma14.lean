import FreeFermionGraphs.ObstructionSearchFiniteMixedTargetCommutation

/-!
# Conditional Lemma 14 bridge from generated finite obstruction-search data

This module packages the strongest currently available finite Lemma 14 route.
Terminal-path parity is derived from the manuscript coordinate form
`j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`. Positive terminal degree three is now derived from the
manuscript's assertion that the common target commutes with every actual path
component: commuting blocks preserve degree parity, all intermediate holes are
even, and Lemma 7 forces the odd degree to remain three. Clone-to-flank
adjacency is derived from the adjacent tether-link coordinate. The
unequal-centre branch accepts only a bounded trace carrying an `IsGenerated`
derivation from the finite start and hop constructors.

The route no longer assumes the stronger step-by-step `TargetBalanced`
certificate. It still does not construct all terminal and propagation inputs
from `InitializationFiniteMixedSideTerminalCoreData` alone. In particular, the
terminal event still supplies the coordinate presentation, path commutation,
and adjacent tether links, while the propagation datum supplies a generated
trace whose constructor inputs include the required avoidance and adjacency
facts.

The theorem below is therefore deliberately conditional and must not be named
`paperLemma14` until those remaining inputs are derived from the literal
Definition 19/20 obstruction-search execution.
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

This structure is not yet an output constructed from
`InitializationFiniteMixedSideTerminalCoreData`. Its fields retain the
remaining provenance boundary:

- literal terminal coordinates and stopping-link data;
- commutation of the target with every actual path in each incoming execution;
- an `IsGenerated` unequal-centre trace whose constructor inputs include the
  local avoidance and adjacency facts used by the manuscript propagation.
-/
structure InitializationFiniteMixedSideExecutableLemma14Data
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  terminal : InitializationFiniteMixedSideCommutingTerminalEvent T
  propagation : ∀ hclaw : G.IsClawFree,
    let terminalData := terminal.toLabelledOperationalTerminalData hclaw
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
  let terminalData := L.terminal.toLabelledOperationalTerminalData hclaw
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
