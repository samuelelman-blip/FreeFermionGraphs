import FreeFermionGraphs.T3SeparatorComponent
import FreeFermionGraphs.T3FixedPairingExample

/-!
# The separator lemma on the seven-vertex example

Non-vacuity of `SimpleGraph.OddBlock.separators_sameComponent`: in the claw-free seven-vertex graph
`fpExG` of `FreeFermionGraphs.T3FixedPairingExample`, the side-1 block `j₀ - v - j₁ - k₁`
(`fpExBlockP`, word `[(j₀, v), (j₁, k₁)]`, a block of the hole classes
`fpExS = ({v, k₁}, {b, b₂})`, `fpExS' = ({j₀, j₁}, {y, v})`) runs from `fpExS`, has balanced
`W'`-content `(m', x') = (0, 0)`, and has the two distinct separators `v` and `y` in `fpExS'.2`.
The lemma puts them in one component of `G[fpExS.2 ⊕ fpExS'.2]`.
-/

namespace SimpleGraph

/-- The word of the side-1 block of the example. -/
theorem fpExBlockP_word : fpExBlockP.word = [(4, 0), (5, 1)] := by
  decide

/-- The side-1 block runs from the start state: `v ← j₀`, then `k₁ ← j₁`. -/
theorem fpExBlockP_runsFrom : fpExBlockP.RunsFrom fpExS := by
  refine ⟨({4, 5}, {2, 3}), ?_⟩
  rw [fpExBlockP_word]
  unfold fpExS
  refine ClassRun.cons (s' := ({4, 1}, {2, 3})) (fpEx_stepA _ _ _ _ _ (by decide)) ?_
  refine ClassRun.cons (s' := ({4, 5}, {2, 3})) (fpEx_stepA _ _ _ _ _ (by decide)) ?_
  exact ClassRun.nil _

/-- The separators of the side-1 block in `fpExS'.2 = {y, v}` are `v = 0` and `y = 6`. -/
theorem fpExBlockP_separators : fpExBlockP.separators fpExS'.2 = {0, 6} := by
  ext v
  rw [OddBlock.mem_separators, OddBlock.IsSeparator, fpExBlockP_word]
  revert v
  decide

/-- No vertex of the side-1 block is a matched clone in `C'`: `m' = 0`. -/
theorem fpExBlockP_matchedW :
    (fpExBlockP.support ∩ fpExG.matchedW fpExS' fpExS).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun w hw => ?_)
  obtain ⟨hws, hwm⟩ := Finset.mem_inter.1 hw
  rw [mem_matchedW] at hwm
  simp only [fpEx_isCloneIn_coe_iff] at hwm
  clear hw
  revert w
  decide

/-- No vertex of the side-1 block is a crossed clone in `C'`: `x' = 0`. -/
theorem fpExBlockP_crossedW :
    (fpExBlockP.support ∩ fpExG.crossedW fpExS' fpExS).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun w hw => ?_)
  obtain ⟨hws, hwm⟩ := Finset.mem_inter.1 hw
  rw [mem_crossedW] at hwm
  simp only [fpEx_isCloneIn_coe_iff] at hwm
  clear hw
  revert w
  decide

/-- The separator lemma on the example: the two distinct separators `v` and `y` of the side-1
block lie in one component of `G[{b, b₂} ⊕ {y, v}]`. -/
theorem fpEx_separators_sameComponent :
    (6 : Fin 7) ∈ fpExG.inducedComponentSet ↑(symmDiff fpExS.2 fpExS'.2) 0 :=
  fpExBlockP.separators_sameComponent fpExG_clawFree fpExS_isHoleClasses fpExS'_isHoleClasses
    fpExBlockP_runsFrom (Or.inl ⟨fpExBlockP_matchedW, fpExBlockP_crossedW⟩)
    (by rw [fpExBlockP_separators]; decide) (by rw [fpExBlockP_separators]; decide)

/-- Non-vacuity: the hypotheses of the separator lemma are satisfiable with two distinct
separators. -/
theorem exists_separators_two :
    ∃ (G : SimpleGraph (Fin 7)) (_ : G.IsClawFree) (s s' : Finset (Fin 7) × Finset (Fin 7))
      (_ : G.IsHoleClasses s) (_ : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1)
      (_ : Q.RunsFrom s), (Q.separators s'.2).card = 2 :=
  ⟨fpExG, fpExG_clawFree, fpExS, fpExS', fpExS_isHoleClasses, fpExS'_isHoleClasses, fpExBlockP,
    fpExBlockP_runsFrom, by rw [fpExBlockP_separators]; decide⟩

end SimpleGraph
