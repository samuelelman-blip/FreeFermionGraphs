from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16Paper.lean")
text = path.read_text()

replacements = []

replacements.append((
'''      G.Adj
        ((X.block i).deformation.step (X.block i).lastIndex).before.vertex
          ((X.block i).deformation.step
            (X.block i).lastIndex).removedIndex
        v →''',
'''      G.Adj
        (((X.block i).deformation.step (X.block i).lastIndex).before.vertex
          ((X.block i).deformation.step
            (X.block i).lastIndex).removedIndex)
        v →''',
"terminal endpoint field application",
))

replacements.append((
'''    cases hside : X.side i <;>
      simpa [D, qD, s, hside,
        FiniteMixedSideSearchTrace.orientedBlock,
        ConcretePathDeformation.reorient,
        ConcreteDeformation.reorient,
        ConcreteDeformationStep.reorient] using hD''',
'''    have hOriented :
        (X.block i).path.vertex q =
          (((X.block i).reorient (X.side i)).deformation.step s).introduced := by
      simpa [D, qD, s, FiniteMixedSideSearchTrace.orientedBlock] using hD
    calc
      (X.block i).path.vertex q =
          (((X.block i).reorient (X.side i)).deformation.step s).introduced :=
        hOriented
      _ = ((X.block i).deformation.step s).introduced :=
        (X.block i).reorient_step_introduced (X.side i) s''',
"introduced coordinate transport",
))

replacements.append((
'''    cases hside : X.side i <;>
      simpa [D, qD, s, hside,
        FiniteMixedSideSearchTrace.orientedBlock,
        ConcretePathDeformation.reorient,
        ConcreteDeformation.reorient,
        ConcreteDeformationStep.reorient] using hD''',
'''    have hOriented :
        (X.block i).path.vertex q =
          (((X.block i).reorient (X.side i)).deformation.step s).before.vertex
            (((X.block i).reorient (X.side i)).deformation.step s).removedIndex := by
      simpa [D, qD, s, FiniteMixedSideSearchTrace.orientedBlock] using hD
    calc
      (X.block i).path.vertex q =
          (((X.block i).reorient (X.side i)).deformation.step s).before.vertex
            (((X.block i).reorient (X.side i)).deformation.step s).removedIndex :=
        hOriented
      _ = ((X.block i).deformation.step s).before.vertex
          ((X.block i).deformation.step s).removedIndex :=
        reorient_step_removedVertex_eq (X.block i) (X.side i) s''',
"removed coordinate transport",
))

replacements.append((
'''    simpa only [X.step_eq i s, X.step_eq i t] using hpath''',
'''    rw [X.step_eq i s, X.step_eq i t]
    exact hpath''',
"flattened adjacent continuation",
))

replacements.append((
'''      simpa only [X.step_eq i s, X.step_eq i t] using heq''',
'''      rw [X.step_eq i s, X.step_eq i t] at heq
      exact heq''',
"introduced equality transport",
))

replacements.append((
'''      simpa only [X.step_eq i s, X.step_eq i t] using heq''',
'''      rw [X.step_eq i s, X.step_eq i t] at heq
      exact heq''',
"introduced-removed equality transport",
))

replacements.append((
'''      simpa only [X.step_eq i s, X.step_eq i t] using hadj''',
'''      rw [X.step_eq i s, X.step_eq i t] at hadj
      exact hadj''',
"introduced adjacency transport",
))

replacements.append((
'''      simpa only [X.step_eq i s, X.step_eq i t] using hadj''',
'''      rw [X.step_eq i s, X.step_eq i t] at hadj
      exact hadj''',
"introduced-removed adjacency transport",
))

replacements.append((
'''    have hrawAdj :
        G.Adj
          ((X.block i).deformation.step (X.block i).lastIndex).before.vertex
            ((X.block i).deformation.step
              (X.block i).lastIndex).removedIndex v := by''',
'''    have hrawAdj :
        G.Adj
          (((X.block i).deformation.step (X.block i).lastIndex).before.vertex
            ((X.block i).deformation.step
              (X.block i).lastIndex).removedIndex) v := by''',
"terminal endpoint local application",
))

for old, new, label in replacements:
    if old not in text:
        raise SystemExit(f"Could not find {label}; refusing a partial patch")
    text = text.replace(old, new, 1)

path.write_text(text)
print(f"Patched {path}")
