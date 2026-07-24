import FreeFermionGraphs.ObstructionSearchHistoryOrientationAudit

/-!
# Two-sided obstruction-search history interface

The manuscript's fixed-pairing deformation may use path components on either
`C_a ∪ C'_c` or `C_b ∪ C'_d`.  The existing `SearchPathHistoryWitness` stores
only the first orientation because its local Definition 19 data is phrased in
`ACHoleStepGeometry`.

A `bd` block has exactly the same local form after exchanging
`C_a ↔ C_b`, `C'_c ↔ C'_d`, and `acPaths ↔ bdPaths`.  This module records that
side exchange and introduces a history witness whose concrete Lemma 11 block
is interpreted in the corresponding oriented family.

No claim is made here that the initialized `OS` execution already constructs
this new interface.  That execution-level construction is the next provenance
step.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

/-- Exchange the two original-hole colors, the two prime-hole colors, and the
two path-component families.  A manuscript `bd` block for `O` is an `ac` block
for `O.swapSides`. -/
def swapSides (O : FixedPairingPathFamily G) : FixedPairingPathFamily G where
  Ca := O.Cb
  Cb := O.Ca
  Cc := O.Cd
  Cd := O.Cc
  acPaths := O.bdPaths
  bdPaths := O.acPaths
  ac_pairwise := O.bd_pairwise
  bd_pairwise := O.ac_pairwise
  ac_subset := by
    intro P hP
    exact O.bd_subset P hP
  bd_subset := by
    intro P hP
    exact O.ac_subset P hP
  ac_induced := O.bd_induced
  bd_induced := O.ac_induced

@[simp] theorem swapSides_ca (O : FixedPairingPathFamily G) :
    O.swapSides.Ca = O.Cb := rfl

@[simp] theorem swapSides_cb (O : FixedPairingPathFamily G) :
    O.swapSides.Cb = O.Ca := rfl

@[simp] theorem swapSides_cc (O : FixedPairingPathFamily G) :
    O.swapSides.Cc = O.Cd := rfl

@[simp] theorem swapSides_cd (O : FixedPairingPathFamily G) :
    O.swapSides.Cd = O.Cc := rfl

@[simp] theorem swapSides_acPaths (O : FixedPairingPathFamily G) :
    O.swapSides.acPaths = O.bdPaths := rfl

@[simp] theorem swapSides_bdPaths (O : FixedPairingPathFamily G) :
    O.swapSides.bdPaths = O.acPaths := rfl

/-- Swapping sides preserves the untyped union of path components. -/
@[simp] theorem swapSides_paths (O : FixedPairingPathFamily G) :
    O.swapSides.paths = O.paths := by
  simp [FixedPairingPathFamily.paths, swapSides, Set.union_comm]

/-- The orientation of one Definition 19 path block. -/
inductive DeformationSide where
  | ac
  | bd
deriving DecidableEq, Repr

namespace DeformationSide

/-- The family in which a block of the selected manuscript side is presented
as an `ac` block. -/
def family (side : DeformationSide) (O : FixedPairingPathFamily G) :
    FixedPairingPathFamily G :=
  match side with
  | .ac => O
  | .bd => O.swapSides

@[simp] theorem family_ac (O : FixedPairingPathFamily G) :
    DeformationSide.ac.family O = O := rfl

@[simp] theorem family_bd (O : FixedPairingPathFamily G) :
    DeformationSide.bd.family O = O.swapSides := rfl

end DeformationSide

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A paper-faithful history witness for one output path.

The selected side determines the family in which the existing concrete Lemma
11 block is interpreted.  For `.bd`, exchanging the color and component labels
turns the manuscript `bd` block into the already formalized `ac` local form. -/
structure TwoSidedSearchPathHistoryWitness
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G)
    (P : Set V) where
  side : DeformationSide
  block : ConcretePathDeformation (side.family O) Cprime
  context : block.Lemma11AHistoryContext
  path_eq : Set.range block.path.vertex = P
  output_mem : P ∈ S.paths
  prior_output_mem :
    ∀ (H : block.FullDefinition19Lemma11AHistoryData),
      context = .later H →
      ∀ r : Nat, r < H.priorCount →
        Set.range (H.history.block r).path.vertex ∈ S.paths
  originalHole_eq : context.originalHole = originalHole

namespace TwoSidedSearchPathHistoryWitness

/-- The oriented local geometry puts the represented path in the selected
component family of the original, unswapped data. -/
theorem path_mem_selectedSide
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P) :
    match A.side with
    | .ac => P ∈ O.acPaths
    | .bd => P ∈ O.bdPaths := by
  have hactive :
      Set.range
          (A.block.deformation.step A.block.firstIndex).activePath.vertex ∈
        (A.side.family O).acPaths :=
    (A.context.currentData.neighborhood.mechanical.stepGeometry
      A.block.firstIndex).base.activePath_ac
  rw [A.block.activePath_eq A.block.firstIndex] at hactive
  rw [A.path_eq] at hactive
  cases A.side <;> simpa [DeformationSide.family, swapSides] using hactive

/-- Forgetting the side recovers membership in the full fixed-pairing path
family. -/
theorem path_mem_family
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P) :
    P ∈ O.paths := by
  change P ∈ O.acPaths ∪ O.bdPaths
  cases hside : A.side with
  | ac =>
      left
      simpa [hside] using A.path_mem_selectedSide
  | bd =>
      right
      simpa [hside] using A.path_mem_selectedSide

end TwoSidedSearchPathHistoryWitness

namespace SearchPathHistoryWitness

/-- Every existing one-sided history witness embeds as the `ac` case of the
new interface. -/
def toTwoSided
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : SearchPathHistoryWitness S originalHole P) :
    TwoSidedSearchPathHistoryWitness S originalHole P where
  side := .ac
  block := A.block
  context := A.context
  path_eq := A.path_eq
  output_mem := A.output_mem
  prior_output_mem := A.prior_output_mem
  originalHole_eq := A.originalHole_eq

end SearchPathHistoryWitness

/-- Two-sided concrete path-history data for every output path of one search. -/
structure TwoSidedSearchHistoryData
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G) where
  witness : ∀ {P : Set V}, P ∈ S.paths →
    TwoSidedSearchPathHistoryWitness S originalHole P

namespace SearchHistoryData

/-- The existing one-sided interface embeds into the two-sided interface while
preserving every execution-provenance field. -/
def toTwoSided
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    (H : SearchHistoryData S originalHole) :
    TwoSidedSearchHistoryData S originalHole where
  witness := fun hP => (H.witness hP).toTwoSided

end SearchHistoryData

namespace TwoSidedSearchHistoryData

/-- Every represented output path carries an explicit manuscript side and
belongs to the corresponding component family. -/
theorem exists_side
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    (H : TwoSidedSearchHistoryData S originalHole)
    {P : Set V} (hP : P ∈ S.paths) :
    ∃ side : DeformationSide,
      match side with
      | .ac => P ∈ O.acPaths
      | .bd => P ∈ O.bdPaths := by
  let A := H.witness hP
  exact ⟨A.side, A.path_mem_selectedSide⟩

end TwoSidedSearchHistoryData

end FixedPairingPathFamily

end SimpleGraph
