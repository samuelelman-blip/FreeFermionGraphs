import FreeFermionGraphs.T3TogglesInvariant

/-!
# The pairing involution on pairs of holes

This module closes the final pairing of the proof of Theorem 1(iii) of the manuscript
(arXiv 2305.15625 v1, L1203-1241).  v1 cancels the terms `[h_C, h_{C'}]` and
`[h_{C ⊕ T}, h_{C' ⊕ T}]` against each other "by fixing a deformation to cancel terms pairwise"
(L1237-1241) and does not argue that the resulting assignment is an involution without fixed points
on the set of pairs `(C, C')`.  We make the assignment into a function of the pair of carriers and
prove that it has these properties.

The construction is the (iii) analogue of `chosenUntethered` and `cycleChargeToggle` of
`TheoremOneII` (v1 L925-927, the pairing of the proof of Theorem 1(ii)): the candidate set
`K*(C, C')` (`SimpleGraph.palindromicToggles`) depends on the carriers alone and is stable under the
toggles it contains (`SimpleGraph.palindromicToggles_toggle`), so a choice function applied to the
set `K*(C, C')` picks the same element at the toggled pair.

## Main definitions

* `SimpleGraph.chosenPalToggle G C C'`: a fixed element of `K*(C, C')`, chosen as a function of the
  set `K*(C, C')` alone (`∅` when `K*(C, C')` is empty).
* `SimpleGraph.holePairToggle G p`: the pairing `(C, C') ↦ (C ⊕ T, C' ⊕ T)` with
  `T = chosenPalToggle C C'` when `K*(C, C')` is nonempty, and the identity otherwise.

## Main results

* `SimpleGraph.holePairToggle_involutive`: `holePairToggle` is an involution.
* `SimpleGraph.holePairToggle_ne`: if `K*(C, C')` is nonempty, `holePairToggle` moves `(C, C')`.
* `SimpleGraph.holePairToggle_mem_closure`: `holePairToggle` preserves `⟨C₀⟩ × ⟨C₀'⟩`, the product
  of the even-hole deformation closures (v1 Definition 12, L700).
* `SimpleGraph.PauliFrustrationRepresentation.commutator_holePairToggle`: on a pair with `K*(C, C')`
  nonempty, `[h, h']` of the toggled pair is the negative of `[h_C, h_{C'}]`, so the toggled pair
  cancels the pair (v1 L1237-1241, now as a pairing of terms).

## Notes

* The hypothesis `G.IsClawFree` is part of the manuscript setup of Theorem 1 and is carried so that
  the statements have the same shape as `cycleChargeToggle_involutive`; the proofs use it only
  through `palindromicToggles_toggle` and `palindromicToggles_toggle_data`, which do not use it
  either.
* No hypothesis beyond the manuscript setup is assumed.  In particular, nothing is assumed about
  the non-emptiness of `K*(C, C')`: on pairs with `K*(C, C')` empty the pairing is the identity,
  exactly as `cycleChargeToggle` is the identity where `𝒫(C, S)` is empty.
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- **A fixed element of `K*(C, C')`**, chosen as a function of the set `K*(C, C')` alone (and `∅`
when `K*(C, C')` is empty).  This is the "fixed deformation by which corresponding terms are
paired" of v1 L1237-1241, made into a function of the pair of carriers `(C, C')`; the analogue of
`chosenUntethered` (v1 L925-927). -/
noncomputable def chosenPalToggle (G : SimpleGraph V) [Fintype V] [DecidableEq V] (C C' : Set V) :
    Finset V :=
  if h : (G.palindromicToggles C C').Nonempty then h.choose else ∅

/-- **The pairing of the final step of Theorem 1(iii)** (v1 L1237-1241; see the module
documentation).  If `K*(C, C')` is nonempty, toggle the chosen element `T` in both carriers,
`(C, C') ↦ (C ⊕ T, C' ⊕ T)`; otherwise do nothing.  The analogue of `cycleChargeToggle`. -/
noncomputable def holePairToggle (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (p : Set V × Set V) : Set V × Set V :=
  if (G.palindromicToggles p.1 p.2).Nonempty then
    (symmDiff p.1 ↑(G.chosenPalToggle p.1 p.2), symmDiff p.2 ↑(G.chosenPalToggle p.1 p.2))
  else p

section Pairing

variable [Fintype V] [DecidableEq V]

/-- The chosen toggle lies in `K*(C, C')` whenever that set is nonempty. -/
theorem chosenPalToggle_mem {C C' : Set V} (h : (G.palindromicToggles C C').Nonempty) :
    G.chosenPalToggle C C' ∈ G.palindromicToggles C C' := by
  unfold chosenPalToggle
  rw [dif_pos h]
  exact h.choose_spec

/-- The chosen toggle only depends on the set `K*(C, C')`. -/
theorem chosenPalToggle_congr {C₁ C₁' C₂ C₂' : Set V}
    (h : G.palindromicToggles C₁ C₁' = G.palindromicToggles C₂ C₂') :
    G.chosenPalToggle C₁ C₁' = G.chosenPalToggle C₂ C₂' := by
  unfold chosenPalToggle
  simp only [h]

/-- **Stability of the chosen toggle.**  The chosen toggle of `(C, C')` is the chosen toggle of the
toggled pair `(C ⊕ T, C' ⊕ T)`, `T ∈ K*(C, C')`: this is `palindromicToggles_toggle` (v1
L1237-1241: the toggled pair is paired by the same deformation). -/
theorem chosenPalToggle_toggle (hclaw : G.IsClawFree) {C C' : Set V} {T : Finset V}
    (hT : T ∈ G.palindromicToggles C C') :
    G.chosenPalToggle (symmDiff C ↑T) (symmDiff C' ↑T) = G.chosenPalToggle C C' :=
  chosenPalToggle_congr (palindromicToggles_toggle hclaw hT)

/-- On a pair with `K*(C, C')` nonempty, `holePairToggle` toggles the chosen element in both
carriers. -/
theorem holePairToggle_of_nonempty {p : Set V × Set V}
    (h : (G.palindromicToggles p.1 p.2).Nonempty) :
    ((G.holePairToggle p).1 = symmDiff p.1 ↑(G.chosenPalToggle p.1 p.2)) ∧
      ((G.holePairToggle p).2 = symmDiff p.2 ↑(G.chosenPalToggle p.1 p.2)) := by
  unfold holePairToggle
  rw [if_pos h]
  exact ⟨rfl, rfl⟩

/-- On a pair with `K*(C, C')` empty, `holePairToggle` is the identity. -/
theorem holePairToggle_of_not_nonempty {p : Set V × Set V}
    (h : ¬ (G.palindromicToggles p.1 p.2).Nonempty) : G.holePairToggle p = p := by
  unfold holePairToggle
  rw [if_neg h]

/-- **The pairing is an involution** (the closing of v1 L1237-1241: the final pairing of the terms
is well defined).  The toggled pair has the same set `K*` (`palindromicToggles_toggle`), hence the
same chosen toggle, and `T ⊕ T = ∅`. -/
theorem holePairToggle_involutive (hclaw : G.IsClawFree) (p : Set V × Set V) :
    G.holePairToggle (G.holePairToggle p) = p := by
  by_cases h : (G.palindromicToggles p.1 p.2).Nonempty
  · obtain ⟨h1, h2⟩ := holePairToggle_of_nonempty h
    have hT : G.chosenPalToggle p.1 p.2 ∈ G.palindromicToggles p.1 p.2 := chosenPalToggle_mem h
    have hP : G.palindromicToggles (G.holePairToggle p).1 (G.holePairToggle p).2 =
        G.palindromicToggles p.1 p.2 := by
      rw [h1, h2]
      exact palindromicToggles_toggle hclaw hT
    have hne : (G.palindromicToggles (G.holePairToggle p).1 (G.holePairToggle p).2).Nonempty := by
      rw [hP]
      exact h
    have hchosen : G.chosenPalToggle (G.holePairToggle p).1 (G.holePairToggle p).2 =
        G.chosenPalToggle p.1 p.2 := by
      rw [h1, h2]
      exact chosenPalToggle_toggle hclaw hT
    obtain ⟨h3, h4⟩ := holePairToggle_of_nonempty hne
    refine Prod.ext ?_ ?_
    · rw [h3, hchosen, h1]
      exact symmDiff_symmDiff_cancel_right _ _
    · rw [h4, hchosen, h2]
      exact symmDiff_symmDiff_cancel_right _ _
  · rw [holePairToggle_of_not_nonempty h, holePairToggle_of_not_nonempty h]

/-- **The pairing has no fixed point where `K*(C, C')` is nonempty.**  The chosen toggle is
nonempty (`palindromicToggles_toggle_data`: `c(T, C)` is odd), and `C ⊕ T = C` would force
`T = ∅`. -/
theorem holePairToggle_ne (hclaw : G.IsClawFree) {p : Set V × Set V}
    (h : (G.palindromicToggles p.1 p.2).Nonempty) : G.holePairToggle p ≠ p := by
  intro heq
  obtain ⟨h1, -⟩ := holePairToggle_of_nonempty h
  have hne : (G.chosenPalToggle p.1 p.2).Nonempty :=
    (palindromicToggles_toggle_data hclaw (chosenPalToggle_mem h)).2.2
  have hfix : symmDiff p.1 ↑(G.chosenPalToggle p.1 p.2) = p.1 := by
    rw [← h1, heq]
  rw [symmDiff_eq_left] at hfix
  exact hne.ne_empty (by simpa using hfix)

/-- **The pairing preserves `⟨C₀⟩ × ⟨C₀'⟩`.**  If `C` lies in the even-hole deformation closure of
`C₀` and `C'` in that of `C₀'`, so do the two carriers of the toggled pair: `C ⊕ T` is in the
closure of `C` (`palindromicToggles_toggle_data`) and the closure is transitive
(`InEvenHoleDeformationClosure.trans`). -/
theorem holePairToggle_mem_closure (hclaw : G.IsClawFree) {C₀ C₀' : Set V} {p : Set V × Set V}
    (h1 : InEvenHoleDeformationClosure G C₀ p.1) (h2 : InEvenHoleDeformationClosure G C₀' p.2) :
    InEvenHoleDeformationClosure G C₀ (G.holePairToggle p).1 ∧
      InEvenHoleDeformationClosure G C₀' (G.holePairToggle p).2 := by
  by_cases h : (G.palindromicToggles p.1 p.2).Nonempty
  · obtain ⟨e1, e2⟩ := holePairToggle_of_nonempty h
    obtain ⟨d1, d2, -⟩ := palindromicToggles_toggle_data hclaw (chosenPalToggle_mem h)
    rw [e1, e2]
    exact ⟨InEvenHoleDeformationClosure.trans h1 d1, InEvenHoleDeformationClosure.trans h2 d2⟩
  · rw [holePairToggle_of_not_nonempty h]
    exact ⟨h1, h2⟩

end Pairing

namespace PauliFrustrationRepresentation

variable [Fintype V] [DecidableEq V] {A : Type w} [Ring A]

/-- **The toggled pair cancels the pair** (v1 L1237-1241, as a pairing of terms).  For every
`PauliFrustrationRepresentation` `H` of a claw-free `G` over every ring `A` and every pair of
carriers `(C, C')` with `K*(C, C')` nonempty, the commutator of the hole operators of
`holePairToggle (C, C')` is the negative of that of `(C, C')`.  It is
`commutator_palindromicToggle` for the chosen toggle. -/
theorem commutator_holePairToggle (H : G.PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) {p : Set V × Set V}
    (h : (G.palindromicToggles p.1 p.2).Nonempty) :
    algebraCommutator (H.evenHoleOperator (G.holePairToggle p).1)
        (H.evenHoleOperator (G.holePairToggle p).2) =
      -algebraCommutator (H.evenHoleOperator p.1) (H.evenHoleOperator p.2) := by
  obtain ⟨e1, e2⟩ := holePairToggle_of_nonempty h
  rw [e1, e2]
  exact commutator_palindromicToggle H hclaw (chosenPalToggle_mem h)

end PauliFrustrationRepresentation

end SimpleGraph
