from pathlib import Path

path = Path("FreeFermionGraphs/Lemma16OccurrenceTransport.lean")
text = path.read_text()

old_helpers = '''/-- The introduced vertex of a raw trace step lies on that block's path. -/
theorem introduced_mem_path
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (s : Fin (X.block i).deformation.stepCount) :
    ((X.block i).deformation.step s).introduced ∈
      Set.range (X.block i).path.vertex := by
  let D := X.orientedBlock i
  let sD : Fin D.deformation.stepCount :=
    ⟨s.val, by
      simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using s.isLt⟩
  have hmem :
      (D.deformation.step sD).introduced ∈ Set.range D.path.vertex :=
    ⟨(X.localData i).neighborhood.pathOrder.introducedPathIndex sD,
      (X.localData i).neighborhood.pathOrder.introduced_eq sD⟩
  simpa [D, sD, FiniteMixedSideSearchTrace.orientedBlock] using hmem

/-- The removed vertex of a raw trace step lies on that block's path. -/
theorem removed_mem_path
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (s : Fin (X.block i).deformation.stepCount) :
    ((X.block i).deformation.step s).before.vertex
        ((X.block i).deformation.step s).removedIndex ∈
      Set.range (X.block i).path.vertex := by
  let D := X.orientedBlock i
  let sD : Fin D.deformation.stepCount :=
    ⟨s.val, by
      simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using s.isLt⟩
  have hmem :
      (D.deformation.step sD).before.vertex
          (D.deformation.step sD).removedIndex ∈
        Set.range D.path.vertex :=
    ⟨(X.localData i).neighborhood.pathOrder.removedPathIndex sD,
      (X.localData i).neighborhood.pathOrder.removed_eq sD⟩
  simpa [D, sD, FiniteMixedSideSearchTrace.orientedBlock] using hmem
'''

new_helpers = '''/-- The introduced vertex of a raw trace step lies on that block's path. -/
theorem introduced_mem_path
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (s : Fin (X.block i).deformation.stepCount) :
    ((X.block i).deformation.step s).introduced ∈
      Set.range (X.block i).path.vertex := by
  rw [← (X.block i).activePath_eq s]
  exact ((X.block i).deformation.step s).introduced_mem_activePath

/-- The removed vertex of a raw trace step lies on that block's path. -/
theorem removed_mem_path
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (s : Fin (X.block i).deformation.stepCount) :
    ((X.block i).deformation.step s).before.vertex
        ((X.block i).deformation.step s).removedIndex ∈
      Set.range (X.block i).path.vertex := by
  rw [← (X.block i).activePath_eq s]
  exact ((X.block i).deformation.step s).removed_mem_activePath
'''

old_distinct = '''theorem introduced_ne_removed
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (s t : Fin (X.block i).deformation.stepCount) :
    ((X.block i).deformation.step s).introduced ≠
      ((X.block i).deformation.step t).before.vertex
        ((X.block i).deformation.step t).removedIndex := by
  let D := X.orientedBlock i
  let sD : Fin D.deformation.stepCount :=
    ⟨s.val, by
      simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using s.isLt⟩
  let tD : Fin D.deformation.stepCount :=
    ⟨t.val, by
      simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using t.isLt⟩
  intro heq
  apply D.introducedPathIndex_ne_removedPathIndex
    (X.localData i).neighborhood.pathOrder sD tD
  apply D.path.injective
  rw [(X.localData i).neighborhood.pathOrder.introduced_eq sD,
    (X.localData i).neighborhood.pathOrder.removed_eq tD]
  simpa [D, sD, tD, FiniteMixedSideSearchTrace.orientedBlock] using heq
'''

new_distinct = '''theorem introduced_ne_removed
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (s t : Fin (X.block i).deformation.stepCount) :
    ((X.block i).deformation.step s).introduced ≠
      ((X.block i).deformation.step t).before.vertex
        ((X.block i).deformation.step t).removedIndex := by
  let sD : Fin ((X.block i).reorient (X.side i)).deformation.stepCount :=
    ⟨s.val, by simpa using s.isLt⟩
  let tD : Fin ((X.block i).reorient (X.side i)).deformation.stepCount :=
    ⟨t.val, by simpa using t.isLt⟩
  intro heq
  have heqD :
      (((X.block i).reorient (X.side i)).deformation.step sD).introduced =
        (((X.block i).reorient (X.side i)).deformation.step tD).before.vertex
          (((X.block i).reorient (X.side i)).deformation.step tD).removedIndex := by
    simpa [sD, tD] using heq
  apply ((X.block i).reorient (X.side i)).introducedPathIndex_ne_removedPathIndex
    (X.localData i).neighborhood.pathOrder sD tD
  apply ((X.block i).reorient (X.side i)).path.injective
  calc
    ((X.block i).reorient (X.side i)).path.vertex
        ((X.localData i).neighborhood.pathOrder.introducedPathIndex sD) =
        (((X.block i).reorient (X.side i)).deformation.step sD).introduced :=
      (X.localData i).neighborhood.pathOrder.introduced_eq sD
    _ = (((X.block i).reorient (X.side i)).deformation.step tD).before.vertex
          (((X.block i).reorient (X.side i)).deformation.step tD).removedIndex := heqD
    _ = ((X.block i).reorient (X.side i)).path.vertex
        ((X.localData i).neighborhood.pathOrder.removedPathIndex tD) :=
      ((X.localData i).neighborhood.pathOrder.removed_eq tD).symm
'''

for old, new, label in [
    (old_helpers, new_helpers, "raw path membership helpers"),
    (old_distinct, new_distinct, "introduced/removed coordinate separation"),
]:
    if old not in text:
        raise SystemExit(f"Could not find {label}; refusing a partial patch")
    text = text.replace(old, new, 1)

path.write_text(text)
print(f"Patched {path}")
