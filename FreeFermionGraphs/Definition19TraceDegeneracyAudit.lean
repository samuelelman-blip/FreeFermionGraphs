import FreeFermionGraphs.Lemma16OccurrenceTransport
import FreeFermionGraphs.ObstructionSearchFiniteMixedPersistence
import FreeFermionGraphs.ObstructionSearchTwoSidedMixedPersistence

/-!
# Definition 19 traces: a machine-checked degeneracy audit

This module is an audit of the repository's Definition 19 interfaces, not a paper theorem.  It
proves that `FullDefinition19NeighborhoodData` and `FiniteMixedSideSearchTrace` (through its
`localData`) can only describe single-step, single-block deformations, that the three
multi-block Lemma 11 history types are empty, and draws the consequences for the repository's
Lemmas 11, 14, 15 and 16 as stated on these types.

## The paper setting (v1, arXiv 2305.15625v1)

Definition 19 (v1 L978-1013) runs a finite sequence of path blocks
`P^(r) = j_0^(r) ◇ k_0^(r) ◇ ... ◇ j_{ℓ_r-1}^(r) ◇ k_{ℓ_r-1}^(r)`, each a component of
`G[C_j ⊕ C'_{σ(j)}]`, labelled so that `j_{s-1}^(r) ∈ C'_{σ(j)} ∖ C_j` (introduced vertex)
and `k_{s-1}^(r) ∈ C_j ∖ C'_{σ(j)}` (removed vertex), v1 L980.  The holes of the run are (v1
L982-986) `C^(r,s) = C ⊕ (⊕_{g<r} P^(g)) ⊕ P^(r)_{2s-1}`, with `C^(r,0) = C^(r-1)` and
`C^(-1) = C`; so the hole before the first step of the first block is `C` itself, and
`C = C_a ∪ C_b`.

Two facts of v1 are used here, and no others.

* The removed vertices `k` lie in `C_j ⊆ C` (v1 L980).
* `j_0^(r) ∉ C`, and `j_0^(r)` lies in exactly one path component of the deformation (v1
  Corollary `pathuniqueendpoints`, L1040-1047; the proof at L1045 shows `j_0^(r) ∉ C`).

Hence `j_0^(0)`, the vertex introduced by the very first step of the run, is never removed: it
is not in `C`, hence not a removed vertex `k ∈ C_j`, and no later path contains it.  It therefore
lies in every hole `C^(r,s)` with `(r, s) ≠ (0, 0)`, although it is not in `C_a ∪ C_b ⊆ C`.
(Only the specific vertex `j_0^(r)` of each block is guaranteed to lie outside `C`.  The other
introduced vertices `j_{s-1}^(r)` are only known to lie in `C'_{σ(j)} ∖ C_j`: v1 Corollary
`vertextwopathcomponents`, L1053-1062, allows a vertex to be introduced by one block and removed
by another block of the opposite side, so that it lies in `C ∩ C'`.  The palindromic example,
v1 subsection L945-966, records the same dichotomy at L955: every introduced `c^(j)` lies
outside `C`, while the `a_j` may lie in `C ∩ C'`.)

## The defect

`ACHoleStepGeometry` (`Lemma11BTerminalContainment.lean:27-41`) has the field
`before_subset : Set.range S.before.vertex ⊆ O.Ca ∪ O.Cb`,
i.e. the hole *before* a step consists of vertices of the *original* colour classes
`C_a ∪ C_b` of `C`.  `ConcretePathDeformation.MechanicalData.stepGeometry` demands an
`ACHoleStepGeometry` for **every** step of a block, and
`FiniteMixedSideSearchTrace.localData` demands a `FullDefinition19Lemma11AData` (whose
`neighborhood : FullDefinition19NeighborhoodData` contains `mechanical`) for **every** block.
In v1 the field is a fact only at the first step of the first block, where the hole is `C`.  At
every other step it is false, because the hole before it contains `j_0^(0) ∉ C`: that hole is
`C^(0,s)` with `s ≥ 1`, or `C^(r,s)` with `r ≥ 1`.

What v1 does give for a later hole is only `C^(r,s) ⊆ C ∪ C'`.  No colour-class containment
can simply replace `before_subset`: for the mixed-side runs that `FiniteMixedSideSearchTrace`
describes, an earlier `bd`-block removes `b`-vertices and introduces vertices of `C'_d ∖ C_b`, so
the `b`-class of a later hole can contain vertices outside `C_b`; in general it is only
contained in `C_b ∪ C'_d`.

## What is proved

The mechanism: the first step introduces `j = c_0`, which is adjacent to the removed
`a_0 ∈ C_a` and to its `b`-neighbour `b_0 ∈ C_b`; as `C_a` and `C_b` are independent
(`ColorClassesIndependent`, a field of `FullDefinition19NeighborhoodData`), `j ∉ C_a ∪ C_b`
(`firstIntroduced_not_mem_ca_cb`).  But `j` belongs to every later hole of the block, and to
the first hole of every later block, so `before_subset` at that later step places `j` in
`C_a ∪ C_b`: contradiction.

* `FullDefinition19NeighborhoodData.firstIntroduced_not_mem_ca_cb`,
  `.stepCount_le_one`, `.stepCount_eq_one`: a block with integrated neighbourhood data has
  exactly one step.
* `FiniteMixedSideSearchTrace.blockCount_eq_one`, `.block_stepCount_eq_one`,
  `.flattened_stepCount_eq_one`: a finite mixed-side trace has exactly one block, with exactly
  one step, so the flattened deformation has a single step `ℓ = 1`.
* `FiniteMixedSideSearchTrace.range_path_eq_pair`: the path of such a block is the pair
  `{introduced, removed}`.
* `FiniteMixedSideSearchTrace.dependentAt_eq_empty_of_isUnobstructed` and
  `.isUnobstructed_iff_dependentUnion_eq_empty`: on every trace, `IsUnobstructed` is
  equivalent to `U = ∅`.
* `FullDefinition19Lemma11AHistoryData.isEmpty`, `FiniteMixedSideLemma11AHistoryData.isEmpty`,
  `MixedSideFullDefinition19Lemma11AHistoryData.isEmpty`: the positive-history types of
  Lemma 11 (a.ii) (`priorCount_pos : 0 < priorCount`) are uninhabited.  The current block's
  `before_subset` at its first step, whose hole is `C^(r-1)` with `r ≥ 1`, places the first
  introduced vertex `j_0^(0)` of block `0` in `C_a ∪ C_b`, contradicting
  `firstIntroduced_not_mem_ca_cb`.
* helpers: `ConcreteDeformationStep.dependent_not_mem_after` (a dependent vertex is outside
  the hole after its step) and `FiniteMixedSideSearchTrace.pathVertex_eq_introduced_or_removed`.

## Consumers of `before_subset`

All sites are in `FreeFermionGraphs/`.  They fall into three groups, according to which hole
the field is read on.

(1) Reads at a step other than the first step of the first block.  v1 gives nothing here (the
hole contains `j_0^(0) ∉ C`):

* `Lemma11BTerminalContainment.lean:81` (`dependent_commonNeighbor_mem_cb`, for the step `S`),
* `Lemma11BOrdinaryPathDescent.lean:174` (step `previous`),
* `Lemma11BExceptionalPathDescent.lean:291` and `:300` (step `previous`),
* `Lemma11BOutsideOrdinaryPredecessor.lean:183` and `:189` (step `previous`),
* `Lemma11BOutsideOrdinaryCommonB.lean:111` and `:117` (step `previous`),
* `Lemma11BConsecutiveFourCommonNeighbor.lean:133` (step `i`),
* `Lemma11BOrdinaryPersistentNeighbors.lean:567` (step `earlier`),
* `Lemma11BFinalHoleColors.lean:140` (step `D.lastIndex`).

(2) Reads at `firstIndex` of a generic block `D`.  They are consistent with v1 only if `D` is
the first block, and nothing in the signature enforces this:

* `Lemma11AOriginalHole.lean:92` (`dependent_not_mem_initialHole_of_anticommutes`).  This one
  is consumed at the *current* block of a history with `priorCount_pos : 0 < priorCount`:
  `Lemma11AFullDefinition19HistoryComplete.lean:65`
  (`FullDefinition19Lemma11AHistoryData`, `Lemma11AFullDefinition19History.lean:39`),
  `ObstructionSearchFiniteMixedLemma11A.lean:162` (`FiniteMixedSideLemma11AHistoryData`,
  `ObstructionSearchFiniteMixedPrefix.lean:39`) and
  `ObstructionSearchTwoSidedMixedLemma11AComplete.lean:160`
  (`MixedSideFullDefinition19Lemma11AHistoryData`,
  `ObstructionSearchTwoSidedMixedContext.lean:36`), and again inside
  `Lemma11AOriginalHole.lean:486` (`lemma11ai_cloneCenter_ne_currentIntroduced`, consumed through
  `lemma11ai_cloneCenter_is_commonNeighbor` by `lemma11ai_of_fullDefinition19History`).  The
  hole read there is `C^(r-1)` with `r ≥ 1`, which contains `j_0^(0) ∉ C`: v1 does not support
  it.  This is why the three history types are empty (see `isEmpty` above) and the statements
  built on them are vacuous.
* `Lemma11AOriginalHole.lean:321` (`lemma11aii_cloneCenter_mem_ca_of_firstBlock`, used by
  `Lemma11AExact.lean:82`), `ObstructionSearchHistory.lean:58` and
  `ObstructionSearchFiniteMixedCrossCorollary11.lean:162` (the `first` cases of the history
  contexts): consistent with v1 when `D` really is block `0`, i.e. in the zero-history case.

(3) Reads at `firstIndex` of block `0` of a history (the hole is `C`): consistent with v1,
`Lemma11AOriginalHole.lean:370`, `ObstructionSearchHistory.lean:65`,
`Lemma11ACorollary11History.lean:103`, `ObstructionSearchFiniteMixedCorollary11.lean:141`,
`ObstructionSearchFiniteMixedCrossCorollary11.lean:184`,
`ObstructionSearchFiniteMixedLemma11AExact.lean:84`,
`ObstructionSearchTwoSidedMixedCorollary11.lean:135`,
`ObstructionSearchTwoSidedMixedOriginalCarrier.lean:85`.  These sit in the `later` cases, that
is, in statements about histories of the (empty) types above.

The same field read at `firstIndex` of a block `i ≠ 0` would again be false in v1; this is
exactly how `blockCount_eq_one` and the three `isEmpty` theorems are proved.

## Consequences

Every theorem of the repository that consumes `FullDefinition19NeighborhoodData` or
`FullDefinition19Lemma11AData` for a trace (and every `FiniteMixedSideSearchTrace`) is, as
stated, a statement about a single-step deformation with a single block, and every theorem
that consumes one of the three positive-history types is vacuous:

* Lemma 11 (v1 Lemma 6, `lemma11b_of_fullDefinition19NeighborhoodData` and its
  `ObstructionSearchFiniteMixed*` / `Lemma11A*` consequences) covers one step, where the
  statement is nearly trivial.  The versions "through a nonempty finite prefix of earlier
  blocks", which take `X : D.FullDefinition19Lemma11AHistoryData` or the finite-mixed /
  two-sided-mixed variants, have an uninhabited hypothesis; the `later` constructors of the
  `Lemma11AHistoryContext`-style types cannot be built.  They are not merely single-step: they
  say nothing.
* Lemma 14 (v1 Lemma 8): a `FiniteMixedSideSearchTrace` produced by the search has one block;
  an honest multi-block run of Definition 19 cannot be put in this type.
* Lemma 15 (v1 Lemma 9) is used on histories built from such traces and inherits the restriction.
* Lemma 16 (v1 Lemma 10): by `isUnobstructed_iff_dependentUnion_eq_empty` the hypothesis
  `IsUnobstructed` already says `U = ∅`, and the criterion `U ⊆ C^(m)` is then trivial.

These are not claims about the paper: v1's Definition 19 and Lemmas 6, 8-10 concern arbitrary
`ℓ_r` and arbitrarily many blocks.  The defect lies in the interface field `before_subset`.  The
minimal repair is to assert it only for the first step of the first block (hole `C`) and to
derive the colour information needed at later holes `C^(r,s)` from the Definition 19 history;
it cannot be repaired by restricting to the `b`-vertices, since for mixed-side runs the
`b`-class of a later hole can contain vertices of `C'_d ∖ C_b`.  No existing declaration is
changed here.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

/-- A dependent vertex of a step is outside the hole after that step: it is adjacent to the
introduced vertex, so it cannot be the introduced vertex, and the clone condition makes a
before-hole vertex adjacent to the introduced vertex only if it is the removed vertex or
adjacent to it. -/
theorem ConcreteDeformationStep.dependent_not_mem_after
    {O : FixedPairingPathFamily G} {Cprime : Set V}
    (S : ConcreteDeformationStep O Cprime) {u : V} (hu : u ∈ S.dependentSet) :
    u ∉ Set.range S.after.vertex := by
  obtain ⟨_, hadj, hne, hnadj⟩ := (ConcreteDeformationStep.mem_dependentSet S).1 hu
  have hafter : Set.range S.after.vertex =
      Set.insert S.introduced
        (Set.range S.before.vertex \ {S.before.vertex S.removedIndex}) :=
    S.before.deform_range_eq S.deformation
  rw [hafter]
  intro h
  rcases h with h | ⟨⟨q, hq⟩, _⟩
  · subst h
    exact G.loopless.irrefl _ hadj
  · rcases (S.deformation.adj_iff q).1 (hq ▸ hadj.symm) with hqr | hqr
    · exact hne (hq.symm.trans (congrArg S.before.vertex hqr))
    · exact hnadj (hq ▸ hqr).symm

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

private theorem reorient_step_removedVertex_eq
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (i : Fin D.deformation.stepCount) :
    ((D.reorient side).deformation.step i).before.vertex
        ((D.reorient side).deformation.step i).removedIndex =
      (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex := by
  cases side <;> rfl

/-- Swapping the two sides of the fixed-pairing family does not change the union
`C_a ∪ C_b` of the colour classes of `C`. -/
private theorem family_union_eq (side : DeformationSide) :
    (side.family O).Ca ∪ (side.family O).Cb = O.Ca ∪ O.Cb := by
  cases side with
  | ac => rfl
  | bd => exact Set.union_comm _ _

namespace FullDefinition19NeighborhoodData

variable {D : ConcretePathDeformation O Cprime}

/-- The vertex introduced by the first step of a block with integrated neighbourhood data lies
in neither of the original colour classes `C_a`, `C_b`.

This uses `ACHoleStepGeometry.before_subset` at the first step of the block, together with
independence of `C_a`, `C_b`: the introduced vertex `j = c_0` is adjacent to the removed
`a_0 ∈ C_a` and to its `b`-neighbour `b_0 ∈ C_b`.  In v1 the field read at the first step is a
fact only when the block is block `0`, whose hole is `C`; for a block `r ≥ 1` the hole before
its first step is `C^(r-1)`, which contains `j_0^(0) ∉ C`, so the field is itself not a v1 fact
there.  The conclusion `j_0^(r) ∉ C_a ∪ C_b` does hold in v1 for every block `r`, by
Corollary `pathuniqueendpoints` (L1040-1047: `j_0^(r) ∉ C`). -/
theorem firstIntroduced_not_mem_ca_cb
    (F : D.FullDefinition19NeighborhoodData) :
    (D.deformation.step D.firstIndex).introduced ∉ O.Ca ∪ O.Cb := by
  let i := D.firstIndex
  let L := F.alternating
  let C := L.labeling i
  let r := L.removedAIndex i
  have hcl : C.CloneAt (D.deformation.step i).introduced r := L.cloneAt i
  have hk : C.a r ∈ O.Ca := by
    have h := (F.mechanical.stepGeometry i).removed_ca
    rwa [L.removed_eq i] at h
  have hbBefore :
      C.b r ∈ Set.range (D.deformation.step i).before.vertex := by
    rw [← L.carrier_eq i]
    exact C.b_mem_carrier r
  have hbCb : C.b r ∈ O.Cb := by
    rcases (F.mechanical.stepGeometry i).before_subset hbBefore with hb | hb
    · exact absurd (C.adj_a_b r) (F.colorClassesIndependent.ca hk hb)
    · exact hb
  rintro (hj | hj)
  · exact F.colorClassesIndependent.ca hj hk hcl.adj_original
  · exact F.colorClassesIndependent.cb hj hbCb hcl.adj_b

/-- A block with integrated neighbourhood data has at most one step: the introduced vertex of
step `0` belongs to the hole before step `1`, which `before_subset` places in `C_a ∪ C_b`.
In v1 this hole `C^(r,1)` contains the introduced vertex `j_0^(r) ∉ C` (Corollary
`pathuniqueendpoints`, L1040-1047), so the field `before_subset` is not a v1 fact at a step
`s ≥ 1`. -/
theorem stepCount_le_one
    (F : D.FullDefinition19NeighborhoodData) :
    D.deformation.stepCount ≤ 1 := by
  by_contra h
  have h2 : 1 < D.deformation.stepCount := by omega
  let i1 : Fin D.deformation.stepCount := ⟨1, h2⟩
  apply F.firstIntroduced_not_mem_ca_cb
  have hchain :=
    D.deformation.carrier_chain (i := D.firstIndex) (j := i1) (by
      simp [firstIndex, i1])
  have hmem :
      (D.deformation.step D.firstIndex).introduced ∈
        Set.range (D.deformation.step i1).before.vertex := by
    rw [← hchain]
    exact (D.deformation.step D.firstIndex).introduced_mem_after
  exact (F.mechanical.stepGeometry i1).before_subset hmem

/-- A block with integrated neighbourhood data has exactly one step. -/
theorem stepCount_eq_one
    (F : D.FullDefinition19NeighborhoodData) :
    D.deformation.stepCount = 1 :=
  le_antisymm F.stepCount_le_one D.nonempty

end FullDefinition19NeighborhoodData

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- A finite mixed-side trace has exactly one block: the first hole of a second block contains
the vertex introduced by the first block, which cannot lie in `C_a ∪ C_b`.  (In v1 the hole
`C^(0)` after the first block contains the vertex `j_0^(0) ∉ C`, by Corollary
`pathuniqueendpoints`, L1040-1047.) -/
theorem blockCount_eq_one
    (X : FiniteMixedSideSearchTrace S originalHole) :
    X.blockCount = 1 := by
  by_contra h
  have h2 : 1 < X.blockCount := by
    have := X.blockCount_pos
    omega
  let i0 : Fin X.blockCount := X.firstIndex
  let i1 : Fin X.blockCount := ⟨1, h2⟩
  let A0 := X.orientedBlock i0
  let A1 := X.orientedBlock i1
  have F0 : A0.FullDefinition19NeighborhoodData := (X.localData i0).neighborhood
  have hcount : A0.deformation.stepCount = 1 := F0.stepCount_eq_one
  have hfirst : A0.firstIndex = A0.lastIndex := by
    apply Fin.ext
    simp [ConcretePathDeformation.firstIndex, ConcretePathDeformation.lastIndex, hcount]
  have hjFinal :
      (A0.deformation.step A0.firstIndex).introduced ∈
        Set.range (X.block i0).finalHole.vertex := by
    rw [← ConcretePathDeformation.reorient_finalHole_range (X.block i0) (X.side i0)]
    rw [hfirst]
    exact (A0.deformation.step A0.lastIndex).introduced_mem_after
  have hchain := X.chain (i := i0) (j := i1) (by simp [i0, i1, firstIndex])
  have hjInitial :
      (A0.deformation.step A0.firstIndex).introduced ∈
        Set.range (A1.deformation.step A1.firstIndex).before.vertex := by
    have h1 : (A0.deformation.step A0.firstIndex).introduced ∈
        Set.range (X.block i1).initialHole.vertex := by
      rw [← hchain]
      exact hjFinal
    have h2 : (A0.deformation.step A0.firstIndex).introduced ∈
        Set.range A1.initialHole.vertex := by
      rw [show Set.range A1.initialHole.vertex = Set.range (X.block i1).initialHole.vertex from
        ConcretePathDeformation.reorient_initialHole_range (X.block i1) (X.side i1)]
      exact h1
    exact h2
  have hcol1 :=
    ((X.localData i1).neighborhood.mechanical.stepGeometry
      A1.firstIndex).before_subset hjInitial
  rw [family_union_eq] at hcol1
  apply F0.firstIntroduced_not_mem_ca_cb
  rw [family_union_eq]
  exact hcol1

/-- Every block of a finite mixed-side trace has exactly one step. -/
theorem block_stepCount_eq_one
    (X : FiniteMixedSideSearchTrace S originalHole) (i : Fin X.blockCount) :
    (X.block i).deformation.stepCount = 1 :=
  ((X.localData i).neighborhood.stepCount_eq_one :
    (X.orientedBlock i).deformation.stepCount = 1)

/-- The flattened deformation of a finite mixed-side trace has exactly one step.  Hence every
interface built on `FiniteMixedSideSearchTrace` only ever concerns single-step deformations,
for which `ℓ = 1` and the criterion `U ⊆ C^(m)` is equivalent to `U = ∅`. -/
theorem flattened_stepCount_eq_one
    (X : FiniteMixedSideSearchTrace S originalHole) :
    X.flattened.deformation.stepCount = 1 := by
  have hb := X.blockCount_eq_one
  apply le_antisymm _ X.flattened.nonempty
  by_contra h
  have h2 : 1 < X.flattened.deformation.stepCount := by omega
  obtain ⟨i, s, hs⟩ := X.stepIndex_surjective ⟨0, X.flattened.nonempty⟩
  obtain ⟨i', s', hs'⟩ := X.stepIndex_surjective ⟨1, h2⟩
  have hi : i = i' := by
    apply Fin.ext
    have := i.isLt
    have := i'.isLt
    omega
  subst hi
  have hss : s = s' := by
    apply Fin.ext
    have h1 := X.block_stepCount_eq_one i
    have := s.isLt
    have := s'.isLt
    omega
  subst hss
  have := congrArg Fin.val (hs.symm.trans hs')
  simp at this

/-- Every vertex of a trace path is one of the introduced or removed coordinates of that same
block. -/
theorem pathVertex_eq_introduced_or_removed
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    (q : Fin (X.block i).path.card) :
    (∃ s : Fin (X.block i).deformation.stepCount,
      (X.block i).path.vertex q =
        ((X.block i).deformation.step s).introduced) ∨
    (∃ s : Fin (X.block i).deformation.stepCount,
      (X.block i).path.vertex q =
        ((X.block i).deformation.step s).before.vertex
          ((X.block i).deformation.step s).removedIndex) := by
  let D := X.orientedBlock i
  let qD : Fin D.path.card :=
    ⟨q.val, by
      simp [D, FiniteMixedSideSearchTrace.orientedBlock]⟩
  rcases D.pathIndex_introduced_or_removed
      (X.localData i).neighborhood.pathOrder
      (X.localData i).path_card_eq qD with hintroduced | hremoved
  · obtain ⟨sD, hq⟩ := hintroduced
    let s : Fin (X.block i).deformation.stepCount :=
      ⟨sD.val, by
        simp [D, FiniteMixedSideSearchTrace.orientedBlock]⟩
    left
    refine ⟨s, ?_⟩
    have hD :
        D.path.vertex qD = (D.deformation.step sD).introduced := by
      rw [hq]
      exact (X.localData i).neighborhood.pathOrder.introduced_eq sD
    have hOriented :
        (X.block i).path.vertex q =
          (((X.block i).reorient (X.side i)).deformation.step s).introduced := by
      simpa [D, qD, s, FiniteMixedSideSearchTrace.orientedBlock] using hD
    calc
      (X.block i).path.vertex q =
          (((X.block i).reorient (X.side i)).deformation.step s).introduced :=
        hOriented
      _ = ((X.block i).deformation.step s).introduced :=
        (X.block i).reorient_step_introduced (X.side i) s
  · obtain ⟨sD, hq⟩ := hremoved
    let s : Fin (X.block i).deformation.stepCount :=
      ⟨sD.val, by
        simp [D, FiniteMixedSideSearchTrace.orientedBlock]⟩
    right
    refine ⟨s, ?_⟩
    have hD :
        D.path.vertex qD =
          (D.deformation.step sD).before.vertex
            (D.deformation.step sD).removedIndex := by
      rw [hq]
      exact (X.localData i).neighborhood.pathOrder.removed_eq sD
    have hOriented :
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
        reorient_step_removedVertex_eq (X.block i) (X.side i) s

/-- The path of a single-step block is the pair of the introduced and the removed vertex. -/
theorem range_path_eq_pair
    (X : FiniteMixedSideSearchTrace S originalHole) (i : Fin X.blockCount)
    (s0 : Fin (X.block i).deformation.stepCount) :
    Set.range (X.block i).path.vertex =
      {((X.block i).deformation.step s0).introduced,
        ((X.block i).deformation.step s0).before.vertex
          ((X.block i).deformation.step s0).removedIndex} := by
  have hcount := X.block_stepCount_eq_one i
  have hall : ∀ t : Fin (X.block i).deformation.stepCount, t = s0 := by
    intro t
    apply Fin.ext
    have := t.isLt
    have := s0.isLt
    omega
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    rcases X.pathVertex_eq_introduced_or_removed i q with
      ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [hall t] at ht
      exact Or.inl ht
    · rw [hall t] at ht
      exact Or.inr ht
  · rintro (rfl | rfl)
    · exact X.introduced_mem_path i s0
    · exact X.removed_mem_path i s0

/-- On a finite mixed-side trace, unobstructedness forces every dependent set to be empty.  By
`flattened_stepCount_eq_one` the trace has a single step `c_0 ≺ a_0` along `P = c_0 ◇ a_0`; a
dependent vertex `u` is adjacent to `c_0` and not to `a_0`, so it anticommutes with `P`, and by
`dependent_not_mem_after` it is outside the terminal hole. -/
theorem dependentAt_eq_empty_of_isUnobstructed
    (X : FiniteMixedSideSearchTrace S originalHole) (hunobstructed : X.IsUnobstructed)
    (i : Fin X.blockCount) (s : Nat) :
    (X.block i).dependentAt s = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hu
  have hs : s < (X.block i).deformation.stepCount :=
    (X.block i).index_lt_of_mem_dependentAt hu
  let s0 : Fin (X.block i).deformation.stepCount := ⟨s, hs⟩
  have huStep : u ∈ ((X.block i).deformation.step s0).dependentSet :=
    (X.block i).mem_step_dependentSet_of_mem_dependentAt hu
  have hcount := X.block_stepCount_eq_one i
  have hblocks := X.blockCount_eq_one
  have hTerminal : u ∉ Set.range X.flattened.terminalHole.vertex := by
    obtain ⟨i', s', his'⟩ := X.stepIndex_surjective X.flattened.lastIndex
    have hi' : i' = i := by
      apply Fin.ext
      have := i.isLt
      have := i'.isLt
      omega
    subst hi'
    have hs' : s' = s0 := by
      apply Fin.ext
      have := s'.isLt
      have := s0.isLt
      omega
    rw [hs'] at his'
    have hterm : X.flattened.terminalHole =
        ((X.block i').deformation.step s0).after := by
      show (X.flattened.deformation.step X.flattened.lastIndex).after = _
      rw [← his', X.step_eq]
    rw [hterm]
    exact ((X.block i').deformation.step s0).dependent_not_mem_after huStep
  have hanti : (X.block i).path.AnticommutesWith u := by
    obtain ⟨_, hadj, _, hnadj⟩ := (ConcreteDeformationStep.mem_dependentSet _).1 huStep
    unfold IndexedInducedPath.AnticommutesWith AnticommutesWithSet adjacencyCount
    have hset : G.adjacentIn u (Set.range (X.block i).path.vertex) =
        {((X.block i).deformation.step s0).introduced} := by
      rw [X.range_path_eq_pair i s0]
      ext v
      simp only [adjacentIn, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hv | hv, hadjv⟩
        · exact hv
        · exact absurd (hv ▸ hadjv) hnadj
      · rintro rfl
        exact ⟨Or.inl rfl, hadj⟩
    rw [hset, Set.ncard_singleton]
  exact hunobstructed i hu hTerminal hanti

/-- A finite mixed-side trace is unobstructed exactly when `U = ∅`.  Hence the hypothesis
`IsUnobstructed` of Lemma 16 (v1 Lemma 10) already says `U = ∅` on every trace of the
repository's `FiniteMixedSideSearchTrace` type, and the criterion `U ⊆ C^(m)` it is meant to
yield is trivial there. -/
theorem isUnobstructed_iff_dependentUnion_eq_empty
    (X : FiniteMixedSideSearchTrace S originalHole) :
    X.IsUnobstructed ↔ X.flattened.dependentUnion = ∅ := by
  constructor
  · intro h
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hu
    obtain ⟨i, s, hus⟩ := X.exists_block_dependentAt_of_mem_dependentUnion hu
    rw [X.dependentAt_eq_empty_of_isUnobstructed h i s] at hus
    exact hus
  · intro h i s u hu _
    exfalso
    have hs : s < (X.block i).deformation.stepCount :=
      (X.block i).index_lt_of_mem_dependentAt hu
    have huStep := (X.block i).mem_step_dependentSet_of_mem_dependentAt hu
    have hmem : u ∈ X.flattened.dependentUnion := by
      rw [FullDefinition19Deformation.mem_dependentUnion_iff]
      refine ⟨X.stepIndex i ⟨s, hs⟩, ?_⟩
      rw [X.step_eq i ⟨s, hs⟩]
      exact huStep
    rw [h] at hmem
    exact hmem

end FiniteMixedSideSearchTrace

/-- The first introduced vertex of a block with integrated neighbourhood data, presented through
a side reorientation `A.reorient side`, lies outside the original colour classes `C_a ∪ C_b` of
the unoriented family. -/
private theorem reorient_firstIntroduced_not_mem_ca_cb
    (A : ConcretePathDeformation O Cprime) (side : DeformationSide)
    (F : (A.reorient side).FullDefinition19NeighborhoodData) :
    (A.deformation.step A.firstIndex).introduced ∉ O.Ca ∪ O.Cb := by
  have h := F.firstIntroduced_not_mem_ca_cb
  rw [family_union_eq] at h
  cases side <;> exact h

/-- The positive Lemma 11 history of `FullDefinition19Lemma11AHistoryData` (a nonempty finite
prefix of earlier Definition 19 blocks, `priorCount_pos : 0 < priorCount`) is uninhabited.

The first introduced vertex `j_0^(0)` of block `0` is never removed (v1 Corollary
`pathuniqueendpoints`, L1040-1047) and so belongs to the initial hole of the current block, which
`before_subset` at the current first step places in `C_a ∪ C_b`; this contradicts
`firstIntroduced_not_mem_ca_cb`.  Every repository theorem with a hypothesis
`X : D.FullDefinition19Lemma11AHistoryData` (the "through a nonempty finite prefix" Lemma 11
statements) is therefore vacuous.  The defect is the interface field `before_subset`, not the
paper: in v1 the hole before the first step of block `r ≥ 1` is `C^(r-1)`, which contains
`j_0^(0) ∉ C`. -/
theorem FullDefinition19Lemma11AHistoryData.isEmpty
    (D : ConcretePathDeformation O Cprime) :
    IsEmpty D.FullDefinition19Lemma11AHistoryData :=
  ⟨fun X => by
    have hmem := D.earlierFirstIntroduced_mem_currentInitial X X.priorCount_pos
    have hcol :=
      (X.current.neighborhood.mechanical.stepGeometry D.firstIndex).before_subset
        (by simpa [ConcretePathDeformation.initialHole] using hmem)
    exact (X.prior 0).neighborhood.firstIntroduced_not_mem_ca_cb hcol⟩

/-- The positive finite mixed-side Lemma 11 history `FiniteMixedSideLemma11AHistoryData`
(`priorCount_pos : 0 < priorCount`) is uninhabited, by the argument of
`FullDefinition19Lemma11AHistoryData.isEmpty`, applied after identifying the colour-class union
`C_a ∪ C_b` of the oriented current and prior blocks with that of `O`. -/
theorem FiniteMixedSideLemma11AHistoryData.isEmpty
    (D : ConcretePathDeformation O Cprime) (originalHole : IndexedInducedHole G) :
    IsEmpty (D.FiniteMixedSideLemma11AHistoryData originalHole) :=
  ⟨fun H => by
    let r0 : Fin H.priorCount := ⟨0, H.priorCount_pos⟩
    have hmem := H.earlierFirstIntroduced_mem_currentInitial r0
    have hmemOriented :
        ((H.priorBlock r0).deformation.step (H.priorBlock r0).firstIndex).introduced ∈
          Set.range (D.reorient H.currentSide).initialHole.vertex := by
      rw [reorient_initialHole_range]
      exact hmem
    have hbefore :
        ((H.priorBlock r0).deformation.step (H.priorBlock r0).firstIndex).introduced ∈
          Set.range ((D.reorient H.currentSide).deformation.step
            (D.reorient H.currentSide).firstIndex).before.vertex := by
      simpa [ConcretePathDeformation.initialHole] using hmemOriented
    have hcol :=
      (H.current.neighborhood.mechanical.stepGeometry
        (D.reorient H.currentSide).firstIndex).before_subset hbefore
    rw [family_union_eq] at hcol
    exact reorient_firstIntroduced_not_mem_ca_cb (H.priorBlock r0) (H.priorSide r0)
      (H.priorData r0).neighborhood hcol⟩

/-- The positive two-sided mixed Lemma 11 history `MixedSideFullDefinition19Lemma11AHistoryData`
(`priorCount_pos : 0 < priorCount`) is uninhabited, by the argument of
`FullDefinition19Lemma11AHistoryData.isEmpty`, applied after identifying the colour-class union
`C_a ∪ C_b` of the oriented current and prior blocks with that of `O`. -/
theorem MixedSideFullDefinition19Lemma11AHistoryData.isEmpty
    (D : ConcretePathDeformation O Cprime) :
    IsEmpty D.MixedSideFullDefinition19Lemma11AHistoryData :=
  ⟨fun X => by
    have hmem :=
      D.earlierFirstIntroduced_mem_currentInitial_of_mixedSideHistory X X.priorCount_pos
    have hmemOriented :
        ((X.history.carrier.block 0).deformation.step
            (X.history.carrier.block 0).firstIndex).introduced ∈
          Set.range (D.reorient X.currentSide).initialHole.vertex := by
      rw [reorient_initialHole_range]
      exact hmem
    have hbefore :
        ((X.history.carrier.block 0).deformation.step
            (X.history.carrier.block 0).firstIndex).introduced ∈
          Set.range ((D.reorient X.currentSide).deformation.step
            (D.reorient X.currentSide).firstIndex).before.vertex := by
      simpa [ConcretePathDeformation.initialHole] using hmemOriented
    have hcol :=
      (X.current.neighborhood.mechanical.stepGeometry
        (D.reorient X.currentSide).firstIndex).before_subset hbefore
    rw [family_union_eq] at hcol
    exact reorient_firstIntroduced_not_mem_ca_cb (X.history.carrier.block 0)
      (X.history.side 0) (X.history.localData 0).neighborhood hcol⟩

end ConcretePathDeformation
end FixedPairingPathFamily
end SimpleGraph
