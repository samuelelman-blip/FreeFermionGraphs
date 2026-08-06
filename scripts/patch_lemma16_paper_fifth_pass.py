from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16Paper.lean")
text = path.read_text()

old_hi = '''    have horder := X.stepIndex_order X.firstIndex i
      (firstLocalStepIndex X) s (Or.inl (by
        simpa [FiniteMixedSideSearchTrace.firstIndex] using hiPos))
    rw [his] at horder
    omega
'''
new_hi = '''    have horder := X.stepIndex_order X.firstIndex i
      (firstLocalStepIndex X) s (Or.inl (by
        simpa [FiniteMixedSideSearchTrace.firstIndex] using hiPos))
    rw [his] at horder
    exact (Nat.not_lt_zero _ horder).elim
'''
if old_hi not in text:
    raise SystemExit("Could not find first-block minimality contradiction")
text = text.replace(old_hi, new_hi, 1)

old_hs = '''    have horder := X.stepIndex_order X.firstIndex X.firstIndex
      (firstLocalStepIndex X) s (Or.inr ⟨rfl, by
        simpa [firstLocalStepIndex,
          ConcretePathDeformation.firstIndex] using hsPos⟩)
    rw [his] at horder
    omega
'''
new_hs = '''    have horder := X.stepIndex_order X.firstIndex X.firstIndex
      (firstLocalStepIndex X) s (Or.inr ⟨rfl, by
        simpa [firstLocalStepIndex,
          ConcretePathDeformation.firstIndex] using hsPos⟩)
    rw [his] at horder
    exact (Nat.not_lt_zero _ horder).elim
'''
if old_hs not in text:
    raise SystemExit("Could not find first-local-step minimality contradiction")
text = text.replace(old_hs, new_hs, 1)

old_removed = '''  rw [initialHole_range_eq_firstBlock_initialHole X]
  have hOriginal :
      Set.range (X.block X.firstIndex).initialHole.vertex =
        Set.range originalHole.vertex := by
    simpa [FiniteMixedSideSearchTrace.firstIndex] using X.originalHole_eq
  rw [hOriginal]
  have hremovedEq :
'''
new_removed = '''  rw [initialHole_range_eq_firstBlock_initialHole X]
  have hremovedEq :
'''
if old_removed not in text:
    raise SystemExit("Could not find original-hole normalization block")
text = text.replace(old_removed, new_removed, 1)

old_tail = '''  rw [hremovedEq]
  exact X.removed_mem_original i s
'''
new_tail = '''  rw [hremovedEq]
  simpa [FiniteMixedSideSearchTrace.firstIndex, X.originalHole_eq] using
    X.removed_mem_original i s
'''
if old_tail not in text:
    raise SystemExit("Could not find removed-membership tail")
text = text.replace(old_tail, new_tail, 1)

path.write_text(text)
print(f"Patched {path}")
