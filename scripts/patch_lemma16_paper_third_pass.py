from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16Paper.lean")
text = path.read_text()

# These helpers are declared inside the PaperLemma16Trace namespace, so they
# are not projections from the trace object X.
text = text.replace("X.firstLocalStepIndex", "firstLocalStepIndex X")
text = text.replace("X.stepIndex_first_eq", "stepIndex_first_eq X")
text = text.replace(
    "X.initialHole_range_eq_firstBlock_initialHole",
    "initialHole_range_eq_firstBlock_initialHole X",
)

old_removed = '''  rw [initialHole_range_eq_firstBlock_initialHole X,
    X.originalHole_eq]
  have hstep := X.step_eq i s
  simpa only [hstep] using X.removed_mem_original i s
'''
new_removed = '''  rw [initialHole_range_eq_firstBlock_initialHole X,
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
if old_removed not in text:
    raise SystemExit("Could not find removed_mem_original tail; refusing a partial patch")
text = text.replace(old_removed, new_removed, 1)

old_endpoint = '''    have hrawAdj :
        G.Adj
          (((X.block i).deformation.step (X.block i).lastIndex).before.vertex
            ((X.block i).deformation.step
              (X.block i).lastIndex).removedIndex) v := by
      rw [← hsLast]
      simpa only [X.step_eq i s] using hadj
'''
new_endpoint = '''    have hrawAdj :
        G.Adj
          (((X.block i).deformation.step (X.block i).lastIndex).before.vertex
            ((X.block i).deformation.step
              (X.block i).lastIndex).removedIndex) v := by
      rw [← hsLast]
      rw [X.step_eq i s] at hadj
      exact hadj
'''
if old_endpoint not in text:
    raise SystemExit("Could not find terminal endpoint transport; refusing a partial patch")
text = text.replace(old_endpoint, new_endpoint, 1)

old_final = '''  refine ⟨hcriterion, ?_⟩
  simpa [L] using X.flattened.lemma12 L hclaw hcriterion
'''
new_final = '''  refine ⟨hcriterion, ?_⟩
  have hrun := X.flattened.lemma12 L hclaw hcriterion
  simpa [L, toLemma12Definition19Data] using hrun
'''
if old_final not in text:
    raise SystemExit("Could not find final Lemma 12 invocation; refusing a partial patch")
text = text.replace(old_final, new_final, 1)

path.write_text(text)
print(f"Patched {path}")
