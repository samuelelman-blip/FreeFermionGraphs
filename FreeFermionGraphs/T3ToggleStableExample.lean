import FreeFermionGraphs.T3ToggleStable
import FreeFermionGraphs.T3FixedPairingExample

/-!
# Toggle stability on the seven-vertex example

Non-vacuity of `SimpleGraph.FPDeformation.toggle_stable`: the palindromic two-block deformation
`fpExD` of the claw-free seven-vertex graph `fpExG` (`FreeFermionGraphs.T3FixedPairingExample`) is
odd, and toggle stability applied to `D = D' = fpExD` gives a palindromic odd deformation of the
toggled pair `(fpExD.fwdEnd, fpExD.bwdEnd) = (fpExS', fpExS)` with the same toggle
`{1, 2, 3, 4, 5, 6}`.
-/

namespace SimpleGraph

/-- Toggle stability for the seven-vertex example: there is a palindromic odd deformation of the
toggled pair of hole-class states with the toggle of `fpExD`. -/
theorem fpExD_toggle_stable :
    ∃ D'' : fpExG.FPDeformation fpExD.fwdEnd fpExD.bwdEnd,
      D''.Palindromic ∧ D''.toggle = fpExD.toggle ∧ D''.IsOdd := by
  obtain ⟨D'', h1, h2, h3⟩ := FPDeformation.toggle_stable fpExG_clawFree fpExS_isHoleClasses
    fpExS'_isHoleClasses fpExD fpExD fpExD_palindromic fpExD_palindromic
  exact ⟨D'', h1, h2, h3.2 fpExD_isOdd⟩

end SimpleGraph
