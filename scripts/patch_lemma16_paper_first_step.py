from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16Paper.lean")
text = path.read_text()

text = text.replace(
    "rw [X.step_eq i s, X.block i |>.activePath_eq s] at hx",
    "rw [X.step_eq i s, (X.block i).activePath_eq s] at hx",
    1,
)

old = '''/-- Every flattened removed vertex belongs to the fixed original hole. -/
theorem removed_mem_original
    (Y : X.PaperLemma16Trace) :
    ∀ k : Fin X.flattened.deformation.stepCount,
      (X.flattened.deformation.step k).before.vertex
          (X.flattened.deformation.step k).removedIndex ∈
        Set.range X.flattened.initialHole.vertex := by
  intro k
  obtain ⟨i, s, his⟩ := X.stepIndex_surjective k
  subst k
  have hraw := X.removed_mem_original i s
  have hinitial :
      Set.range X.flattened.initialHole.vertex =
        Set.range originalHole.vertex := by
    calc
      Set.range X.flattened.initialHole.vertex =
          Set.range (X.block X.firstIndex).initialHole.vertex := by
        rw [FullDefinition19Deformation.initialHole]
        have hfirst := X.stepIndex_surjective
          (⟨0, X.flattened.nonempty⟩ :
            Fin X.flattened.deformation.stepCount)
        obtain ⟨j, t, hjt⟩ := hfirst
        have hzero : (X.stepIndex j t).val = 0 := by simpa [hjt]
        have hj : j = X.firstIndex := by
          apply Fin.ext
          by_contra hne
          have hpos : 0 < j.val := by omega
          have horder := X.stepIndex_order X.firstIndex j
            (X.block X.firstIndex).firstIndex t (Or.inl hpos)
          have hfirstNonneg :=
            (X.stepIndex X.firstIndex
              (X.block X.firstIndex).firstIndex).isLt
          omega
        subst j
        have ht : t = (X.block X.firstIndex).firstIndex := by
          apply Fin.ext
          by_contra hne
          have htpos : 0 < t.val := by
            have htLt := t.isLt
            dsimp [ConcretePathDeformation.firstIndex]
            omega
          have horder := X.stepIndex_order X.firstIndex X.firstIndex
            (X.block X.firstIndex).firstIndex t
            (Or.inr ⟨rfl, htpos⟩)
          omega
        subst t
        rw [X.step_eq]
        rfl
      _ = Set.range originalHole.vertex := X.originalHole_eq
  rw [hinitial]
  have hstep := X.step_eq i s
  simpa only [hstep] using hraw
'''

new = '''/-- The first local replacement in the first path block. -/
def firstLocalStepIndex
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Fin (X.block X.firstIndex).deformation.stepCount :=
  (X.block X.firstIndex).firstIndex

/-- The first local replacement is the first flattened replacement. -/
theorem stepIndex_first_eq
    (X : FiniteMixedSideSearchTrace S originalHole) :
    X.stepIndex X.firstIndex X.firstLocalStepIndex =
      ⟨0, X.flattened.nonempty⟩ := by
  obtain ⟨i, s, his⟩ :=
    X.stepIndex_surjective
      (⟨0, X.flattened.nonempty⟩ :
        Fin X.flattened.deformation.stepCount)
  have hiVal : i.val = 0 := by
    by_contra hi
    have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
    have horder := X.stepIndex_order X.firstIndex i
      X.firstLocalStepIndex s (Or.inl (by
        simpa [FiniteMixedSideSearchTrace.firstIndex] using hiPos))
    rw [his] at horder
    omega
  have hiEq : i = X.firstIndex := by
    apply Fin.ext
    simpa [FiniteMixedSideSearchTrace.firstIndex] using hiVal
  subst i
  have hsVal : s.val = 0 := by
    by_contra hs
    have hsPos : 0 < s.val := Nat.pos_of_ne_zero hs
    have horder := X.stepIndex_order X.firstIndex X.firstIndex
      X.firstLocalStepIndex s (Or.inr ⟨rfl, by
        simpa [firstLocalStepIndex,
          ConcretePathDeformation.firstIndex] using hsPos⟩)
    rw [his] at horder
    omega
  have hsEq : s = X.firstLocalStepIndex := by
    apply Fin.ext
    simpa [firstLocalStepIndex,
      ConcretePathDeformation.firstIndex] using hsVal
  subst s
  exact his

/-- The first flattened hole is the initial hole of the first literal block. -/
theorem initialHole_range_eq_firstBlock_initialHole
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Set.range X.flattened.initialHole.vertex =
      Set.range (X.block X.firstIndex).initialHole.vertex := by
  change
    Set.range
        (X.flattened.deformation.step
          (⟨0, X.flattened.nonempty⟩ :
            Fin X.flattened.deformation.stepCount)).before.vertex =
      Set.range
        ((X.block X.firstIndex).deformation.step
          X.firstLocalStepIndex).before.vertex
  rw [← X.stepIndex_first_eq]
  rw [X.step_eq]

/-- Every flattened removed vertex belongs to the fixed original hole. -/
theorem removed_mem_original
    (Y : X.PaperLemma16Trace) :
    ∀ k : Fin X.flattened.deformation.stepCount,
      (X.flattened.deformation.step k).before.vertex
          (X.flattened.deformation.step k).removedIndex ∈
        Set.range X.flattened.initialHole.vertex := by
  intro k
  obtain ⟨i, s, his⟩ := X.stepIndex_surjective k
  subst k
  rw [X.initialHole_range_eq_firstBlock_initialHole,
    X.originalHole_eq]
  have hstep := X.step_eq i s
  simpa only [hstep] using X.removed_mem_original i s
'''

if old not in text:
    raise SystemExit("Could not find the removed_mem_original block; refusing a partial patch")

path.write_text(text.replace(old, new, 1))
print(f"Patched {path}")
