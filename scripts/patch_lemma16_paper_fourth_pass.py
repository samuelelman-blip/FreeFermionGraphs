from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16Paper.lean")
text = path.read_text()

# The previous namespace qualification pass produced applications such as
# `X.stepIndex ... firstLocalStepIndex X`; parenthesize the helper value.
text = text.replace("firstLocalStepIndex X", "(firstLocalStepIndex X)")

old_removed = '''  rw [initialHole_range_eq_firstBlock_initialHole X,
    X.originalHole_eq]
  have hremovedEq :
      (X.flattened.deformation.step (X.stepIndex i s)).before.vertex
          (X.flattened.deformation.step (X.stepIndex i s)).removedIndex =
        ((X.block i).deformation.step s).before.vertex
          ((X.block i).deformation.step s).removedIndex :=
    congrArg
      (fun z : ConcreteDeformationStep O Cprime =>
        z.before.vertex z.removedIndex)
      (X.step_eq i s)
  rw [hremovedEq]
  exact X.removed_mem_original i s
'''

new_removed = '''  rw [initialHole_range_eq_firstBlock_initialHole X]
  have hOriginal :
      Set.range (X.block X.firstIndex).initialHole.vertex =
        Set.range originalHole.vertex := by
    simpa [FiniteMixedSideSearchTrace.firstIndex] using X.originalHole_eq
  rw [hOriginal]
  have hremovedEq :
      (X.flattened.deformation.step (X.stepIndex i s)).before.vertex
          (X.flattened.deformation.step (X.stepIndex i s)).removedIndex =
        ((X.block i).deformation.step s).before.vertex
          ((X.block i).deformation.step s).removedIndex :=
    congrArg
      (fun z : ConcreteDeformationStep O Cprime =>
        z.before.vertex z.removedIndex)
      (X.step_eq i s)
  rw [hremovedEq]
  exact X.removed_mem_original i s
'''

if old_removed not in text:
    raise SystemExit("Could not find the third-pass removed_mem_original block; refusing a partial patch")

text = text.replace(old_removed, new_removed, 1)
path.write_text(text)
print(f"Patched {path}")
