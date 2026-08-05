from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16OccurrenceTransport.lean")
text = path.read_text()

old = '''  have heqD :
      (((X.block i).reorient (X.side i)).deformation.step sD).introduced =
        (((X.block i).reorient (X.side i)).deformation.step tD).before.vertex
          (((X.block i).reorient (X.side i)).deformation.step tD).removedIndex := by
    simpa [sD, tD] using heq
'''

new = '''  have heqD :
      (((X.block i).reorient (X.side i)).deformation.step sD).introduced =
        (((X.block i).reorient (X.side i)).deformation.step tD).before.vertex
          (((X.block i).reorient (X.side i)).deformation.step tD).removedIndex := by
    calc
      (((X.block i).reorient (X.side i)).deformation.step sD).introduced =
          ((X.block i).deformation.step s).introduced := by
        simpa [sD] using
          ((X.block i).deformation.step s).reorient_introduced (X.side i)
      _ = ((X.block i).deformation.step t).before.vertex
          ((X.block i).deformation.step t).removedIndex := heq
      _ = (((X.block i).reorient (X.side i)).deformation.step tD).before.vertex
          (((X.block i).reorient (X.side i)).deformation.step tD).removedIndex := by
        symm
        simpa [tD] using
          ((X.block i).deformation.step t).reorient_removedVertex (X.side i)
'''

if old not in text:
    raise SystemExit("Could not find the expected heqD block; refusing a partial patch")

path.write_text(text.replace(old, new, 1))
print(f"Patched {path}")
