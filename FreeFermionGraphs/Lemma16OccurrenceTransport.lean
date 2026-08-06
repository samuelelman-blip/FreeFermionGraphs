import FreeFermionGraphs.Lemma16Unobstructed
import FreeFermionGraphs.Lemma11APathBlock

/-!
# Occurrence-level path transport for Lemma 16

This module formalises the Corollaries 9--10 occurrence argument in the
proof of manuscript Lemma 16.  The argument is carried out on the literal
finite block trace.  No terminal-external anticommuting witness is supplied
as data.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace FullDefinition19Deformation

/-- If a vertex is absent immediately after step `i` but belongs to the
terminal hole, some later step introduces it. -/
theorem exists_later_introduced_of_not_mem_after_of_mem_terminal
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    {x : V}
    (hxAfter : x ∉ Set.range (F.deformation.step i).after.vertex)
    (hxTerminal : x ∈ Set.range F.terminalHole.vertex) :
    ∃ j : Fin F.deformation.stepCount,
      i.val < j.val ∧ x = (F.deformation.step j).introduced := by
  by_contra hnone
  push Not at hnone
  have habsent : ∀ (n : Nat) (hn : n < F.deformation.stepCount),
      i.val ≤ n →
      x ∉ Set.range (F.deformation.step ⟨n, hn⟩).after.vertex := by
    intro n hn hin
    induction n, hin using Nat.le_induction with
    | base =>
        simpa using hxAfter
    | succ n hin ih =>
        have hnPrev : n < F.deformation.stepCount := by omega
        let previous : Fin F.deformation.stepCount := ⟨n, hnPrev⟩
        let current : Fin F.deformation.stepCount := ⟨n + 1, hn⟩
        intro hxCurrent
        have hxNeIntroduced :
            x ≠ (F.deformation.step current).introduced := by
          exact hnone current (by
            dsimp [current]
            omega)
        have hxBefore :
            x ∈ Set.range (F.deformation.step current).before.vertex :=
          (F.deformation.step current).mem_before_of_mem_after_of_ne_introduced
            (by simpa [current] using hxCurrent) hxNeIntroduced
        have hchain :
            Set.range (F.deformation.step previous).after.vertex =
              Set.range (F.deformation.step current).before.vertex :=
          F.deformation.carrier_chain (i := previous) (j := current) (by
            simp [previous, current])
        have hxPrevious :
            x ∈ Set.range (F.deformation.step previous).after.vertex := by
          rw [hchain]
          exact hxBefore
        exact ih hnPrev (by simpa [previous] using hxPrevious)
  have hpos : 0 < F.deformation.stepCount := F.nonempty
  have hlast : F.deformation.stepCount - 1 < F.deformation.stepCount := by
    omega
  have hiLt : i.val < F.deformation.stepCount := i.isLt
  have hiLast : i.val ≤ F.deformation.stepCount - 1 := by
    omega
  exact (habsent (F.deformation.stepCount - 1) hlast hiLast)
    (by simpa [terminalHole, lastIndex] using hxTerminal)

end FullDefinition19Deformation

namespace ConcretePathDeformation
namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Every trace path belongs to the untyped path family of any oriented
presentation of the same fixed pairing. -/
theorem path_mem_oriented_family
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i j : Fin X.blockCount) :
    Set.range (X.block j).path.vertex ∈
      ((X.side i).family O).paths := by
  cases hside : X.side i with
  | ac =>
      simpa [hside, DeformationSide.family] using X.path_mem_family j
  | bd =>
      simpa [hside, DeformationSide.family] using X.path_mem_family j

/-- A block belongs to the `acPaths` family after it is reoriented by its
own side tag. -/
theorem path_mem_own_oriented_ac
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    Set.range (X.block i).path.vertex ∈
      ((X.side i).family O).acPaths := by
  rcases X.path_mem_selectedSide i with hi | hi
  · simpa [hi.1, DeformationSide.family] using hi.2
  · simpa [hi.1, DeformationSide.family, swapSides] using hi.2

/-- A block on the opposite side belongs to `bdPaths` in the current
block's oriented family. -/
theorem path_mem_opposite_oriented_bd
    (X : FiniteMixedSideSearchTrace S originalHole)
    {i g : Fin X.blockCount}
    (hside : X.side g ≠ X.side i) :
    Set.range (X.block g).path.vertex ∈
      ((X.side i).family O).bdPaths := by
  rcases X.path_mem_selectedSide g with hg | hg
  · cases hi : X.side i <;>
      simp_all [DeformationSide.family, swapSides]
  · cases hi : X.side i <;>
      simp_all [DeformationSide.family, swapSides]

/-- A later global flattened step cannot be carried by an earlier block. -/
theorem not_block_lt_of_stepIndex_lt
    (X : FiniteMixedSideSearchTrace S originalHole)
    {i j : Fin X.blockCount}
    {s : Fin (X.block i).deformation.stepCount}
    {t : Fin (X.block j).deformation.stepCount}
    (hstep : (X.stepIndex i s).val < (X.stepIndex j t).val) :
    ¬j.val < i.val := by
  intro hji
  have hreverse := X.stepIndex_order j i t s (Or.inl hji)
  omega

/-- The introduced vertex of a raw trace step lies on that block's path. -/
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

/-- Introduced and removed coordinates of one trace block name distinct
vertices. -/
theorem introduced_ne_removed
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
    cases hside : X.side i <;>
      simpa [sD, tD, hside, FiniteMixedSideSearchTrace.orientedBlock,
        ConcretePathDeformation.reorient,
        ConcreteDeformation.reorient,
        ConcreteDeformationStep.reorient] using heq
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

/-- A dependent vertex outside one block's active path has exact colouring
in that block's oriented family. -/
theorem dependent_exactlyOne_in_oriented_family
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount)
    {s : Nat} {u : V}
    (hu : u ∈ (X.block i).dependentAt s)
    (huOutside : u ∉ Set.range (X.block i).path.vertex) :
    ExactlyOneOfFour u
      ((X.side i).family O).Ca
      ((X.side i).family O).Cb
      ((X.side i).family O).Cc
      ((X.side i).family O).Cd := by
  let D := X.orientedBlock i
  have huD : u ∈ D.dependentAt s := by
    change u ∈ ((X.block i).reorient (X.side i)).dependentAt s
    rw [(X.block i).reorient_dependentAt (X.side i) s]
    exact hu
  have huOutsideD : u ∉ Set.range D.path.vertex := by
    simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using huOutside
  exact (X.localData i).neighborhood.mechanical.dependent_exactlyOne_of_outside
    (X.localData i).neighborhood.overlapColoring huD huOutsideD

/-- If an exact-coloured vertex lies on a later trace path and on the unique
`bd` component produced by Lemma 11(b), then that later path is the same
`bd` component. -/
theorem laterPath_eq_uniqueBDPath
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i g : Fin X.blockCount)
    {u : V} {P : Set V}
    (hexact : ExactlyOneOfFour u
      ((X.side i).family O).Ca
      ((X.side i).family O).Cb
      ((X.side i).family O).Cc
      ((X.side i).family O).Cd)
    (hunique : ((X.side i).family O).IsUniqueContainingBDPath u P)
    (huLater : u ∈ Set.range (X.block g).path.vertex) :
    Set.range (X.block g).path.vertex = P := by
  have hnotBoth := hexact.not_mem_ac_and_bd
  have hsideNe : X.side g ≠ X.side i := by
    intro hEq
    have hLaterAC :
        Set.range (X.block g).path.vertex ∈
          ((X.side i).family O).acPaths := by
      have hown := X.path_mem_own_oriented_ac g
      simpa [hEq] using hown
    have huAC :
        u ∈ ((X.side i).family O).Ca ∪
          ((X.side i).family O).Cc :=
      ((X.side i).family O).ac_subset _ hLaterAC huLater
    have huBD :
        u ∈ ((X.side i).family O).Cb ∪
          ((X.side i).family O).Cd :=
      ((X.side i).family O).bd_subset P hunique.1 hunique.2.1
    exact hnotBoth ⟨huAC, huBD⟩
  have hLaterBD :
      Set.range (X.block g).path.vertex ∈
        ((X.side i).family O).bdPaths :=
    X.path_mem_opposite_oriented_bd hsideNe
  exact hunique.2.2 hLaterBD huLater

/-- In the family opposite to block `i`, a current dependent vertex is in
`C'_c` and not in `C_a`. -/
theorem dependent_mem_cc_not_ca_of_opposite_side
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i g : Fin X.blockCount)
    (hside : X.side g ≠ X.side i)
    {s : Nat} {u : V}
    (hu : u ∈ (X.block i).dependentAt s) :
    u ∈ ((X.side g).family O).Cc ∧
      u ∉ ((X.side g).family O).Ca := by
  let D := X.orientedBlock i
  have huD : u ∈ D.dependentAt s := by
    change u ∈ ((X.block i).reorient (X.side i)).dependentAt s
    rw [(X.block i).reorient_dependentAt (X.side i) s]
    exact hu
  have huCd : u ∈ ((X.side i).family O).Cd :=
    (X.localData i).neighborhood.mechanical.dependent_mem_cd huD
  have huPrime : u ∈ Cprime := by
    have hstep := D.mem_step_dependentSet_of_mem_dependentAt huD
    exact ((ConcreteDeformationStep.mem_dependentSet _).1 hstep).1
  have huNotCb : u ∉ ((X.side i).family O).Cb := by
    exact (PrimeCarrierOverlapColored.not_mem_cb_cc_of_mem_cd
      (X.localData i).neighborhood.overlapColoring huPrime huCd).1
  cases hi : X.side i <;>
    cases hg : X.side g <;>
    simp_all [DeformationSide.family, D]

/-- A vertex lying on an opposite-side path and satisfying the current
Definition 20 condition occurs there as an introduced, rather than removed,
path coordinate. -/
theorem exists_introduced_of_mem_opposite_path
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i g : Fin X.blockCount)
    (hside : X.side g ≠ X.side i)
    {s : Nat} {u : V}
    (hu : u ∈ (X.block i).dependentAt s)
    (huPath : u ∈ Set.range (X.block g).path.vertex) :
    ∃ t : Fin (X.block g).deformation.stepCount,
      ((X.block g).deformation.step t).introduced = u := by
  let Dg := X.orientedBlock g
  obtain ⟨q, hqu⟩ : ∃ q : Fin Dg.path.card, Dg.path.vertex q = u := by
    simpa [Dg, FiniteMixedSideSearchTrace.orientedBlock] using huPath
  obtain ⟨_huCc, huNotCa⟩ :=
    X.dependent_mem_cc_not_ca_of_opposite_side i g hside hu
  rcases Dg.pathIndex_introduced_or_removed
      (X.localData g).neighborhood.pathOrder
      (X.localData g).path_card_eq q with hintroduced | hremoved
  · obtain ⟨t, hq⟩ := hintroduced
    have hpath := (X.localData g).neighborhood.pathOrder.introduced_eq t
    have hDg : (Dg.deformation.step t).introduced = u := by
      calc
        (Dg.deformation.step t).introduced =
            Dg.path.vertex
              ((X.localData g).neighborhood.pathOrder.introducedPathIndex t) :=
          hpath.symm
        _ = Dg.path.vertex q := by rw [hq]
        _ = u := hqu
    let traw : Fin (X.block g).deformation.stepCount :=
      ⟨t.val, by
        simpa [Dg, FiniteMixedSideSearchTrace.orientedBlock] using t.isLt⟩
    refine ⟨traw, ?_⟩
    simpa [Dg, traw, FiniteMixedSideSearchTrace.orientedBlock] using hDg
  · obtain ⟨t, hq⟩ := hremoved
    have hpath := (X.localData g).neighborhood.pathOrder.removed_eq t
    have hremovedCa :
        ((Dg.deformation.step t).before.vertex
          (Dg.deformation.step t).removedIndex) ∈
            ((X.side g).family O).Ca :=
      ((X.localData g).neighborhood.mechanical.stepGeometry t).removed_ca
    have huEq :
        u = (Dg.deformation.step t).before.vertex
          (Dg.deformation.step t).removedIndex := by
      calc
        u = Dg.path.vertex q := hqu.symm
        _ = Dg.path.vertex
              ((X.localData g).neighborhood.pathOrder.removedPathIndex t) := by
            rw [hq]
        _ = (Dg.deformation.step t).before.vertex
              (Dg.deformation.step t).removedIndex := hpath
    have huCa : u ∈ ((X.side g).family O).Ca := by
      rw [huEq]
      exact hremovedCa
    exact (huNotCa huCa).elim

/-- The Corollaries 9--10 occurrence argument from Lemma 16: the earlier
anticommuting witness supplied by Lemma 11(b) cannot reappear in the terminal
hole. -/
theorem earlierWitness_not_mem_terminal
    (X : FiniteMixedSideSearchTrace S originalHole)
    (hclaw : G.IsClawFree)
    (i : Fin X.blockCount) {s : Nat} {u : V}
    (hu : u ∈ (X.block i).dependentAt s)
    (huOutsideTerminal :
      u ∉ Set.range X.flattened.terminalHole.vertex)
    {s' : Nat} {u' : V} {P : Set V}
    (hs' : s' < s)
    (hu' : u' ∈ (X.orientedBlock i).dependentAt s')
    (hanti' : (X.orientedBlock i).path.AnticommutesWith u')
    (hunique : ((X.side i).family O).IsUniqueContainingBDPath u' P)
    (huP : u ∈ P) :
    u' ∉ Set.range X.flattened.terminalHole.vertex := by
  let D := X.orientedBlock i
  have hu'Oriented : u' ∈ D.dependentAt s' := by simpa [D] using hu'
  have hu'Prime : u' ∈ Cprime := by
    have hstep := D.mem_step_dependentSet_of_mem_dependentAt hu'Oriented
    exact ((ConcreteDeformationStep.mem_dependentSet _).1 hstep).1
  have hmembership :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      (X.localData i) hclaw hu'Prime hanti').mp
      ⟨s', hu'Oriented⟩
  have hu'OutsidePath : u' ∉ Set.range D.path.vertex :=
    (X.localData i).anticommuting_not_mem_path
      hu'Prime hmembership.1 hanti'
  have hu'NotFinal : u' ∉ Set.range D.finalHole.vertex :=
    (X.localData i).neighborhood.mechanical.dependent_not_mem_finalHole_of_outside
      (X.localData i).neighborhood.overlapColoring
      hu'Oriented hu'OutsidePath
  have hu'NotFinalRaw :
      u' ∉ Set.range (X.block i).finalHole.vertex := by
    simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using hu'NotFinal
  intro hu'Terminal
  let si : Fin (X.block i).deformation.stepCount := (X.block i).lastIndex
  let ki : Fin X.flattened.deformation.stepCount := X.stepIndex i si
  have hu'NotAfter :
      u' ∉ Set.range (X.flattened.deformation.step ki).after.vertex := by
    rw [X.step_eq i si]
    simpa [si, ConcretePathDeformation.finalHole] using hu'NotFinalRaw
  obtain ⟨kLater, _hik, hkIntro⟩ :=
    X.flattened.exists_later_introduced_of_not_mem_after_of_mem_terminal
      ki hu'NotAfter hu'Terminal
  obtain ⟨g, t, hgt⟩ := X.stepIndex_surjective kLater
  have hu'Intro : ((X.block g).deformation.step t).introduced = u' := by
    have hstep := X.step_eq g t
    rw [hgt] at hstep
    calc
      ((X.block g).deformation.step t).introduced =
          (X.flattened.deformation.step kLater).introduced :=
        (congrArg ConcreteDeformationStep.introduced hstep).symm
      _ = u' := hkIntro.symm
  have hnotGLtI : ¬g.val < i.val := by
    intro hgi
    have hreverse := X.stepIndex_order g i t si (Or.inl hgi)
    rw [hgt] at hreverse
    exact (by omega)
  have hgne : g ≠ i := by
    intro hEq
    subst g
    have hu'RawPath : u' ∈ Set.range (X.block i).path.vertex := by
      rw [← hu'Intro]
      exact X.introduced_mem_path i t
    apply hu'OutsidePath
    simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using hu'RawPath
  have hig : i.val < g.val := by
    have hneVal : g.val ≠ i.val := by
      intro hval
      exact hgne (Fin.ext hval)
    omega
  have hu'PathG : u' ∈ Set.range (X.block g).path.vertex := by
    rw [← hu'Intro]
    exact X.introduced_mem_path g t
  have hexactU' : ExactlyOneOfFour u'
      ((X.side i).family O).Ca ((X.side i).family O).Cb
      ((X.side i).family O).Cc ((X.side i).family O).Cd := by
    have hu'Raw : u' ∈ (X.block i).dependentAt s' := by
      rw [← (X.block i).reorient_dependentAt (X.side i) s']
      exact hu'Oriented
    have hu'OutsideRaw : u' ∉ Set.range (X.block i).path.vertex := by
      simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using hu'OutsidePath
    exact X.dependent_exactlyOne_in_oriented_family i hu'Raw hu'OutsideRaw
  have hPathG : Set.range (X.block g).path.vertex = P :=
    X.laterPath_eq_uniqueBDPath i g hexactU' hunique hu'PathG
  have huPathG : u ∈ Set.range (X.block g).path.vertex := by
    rw [hPathG]
    exact huP
  have hsideNe : X.side g ≠ X.side i := by
    intro hside
    have hGAC : P ∈ ((X.side i).family O).acPaths := by
      rw [← hPathG]
      have hown := X.path_mem_own_oriented_ac g
      simpa [hside] using hown
    have huAC :=
      ((X.side i).family O).ac_subset P hGAC hunique.2.1
    have huBD :=
      ((X.side i).family O).bd_subset P hunique.1 hunique.2.1
    exact hexactU'.not_mem_ac_and_bd ⟨huAC, huBD⟩
  obtain ⟨tg, huIntroG⟩ :=
    X.exists_introduced_of_mem_opposite_path i g hsideNe hu huPathG
  let kg : Fin X.flattened.deformation.stepCount := X.stepIndex g tg
  have huIntroGlobal :
      (X.flattened.deformation.step kg).introduced = u := by
    have hstep := X.step_eq g tg
    calc
      (X.flattened.deformation.step kg).introduced =
          ((X.block g).deformation.step tg).introduced := by
        simpa [kg] using congrArg ConcreteDeformationStep.introduced hstep
      _ = u := huIntroG
  have huNotTerminalGlobal :
      (X.flattened.deformation.step kg).introduced ∉
        Set.range X.flattened.terminalHole.vertex := by
    simpa [huIntroGlobal] using huOutsideTerminal
  obtain ⟨kRemove, _hgk, hkRemove⟩ :=
    X.flattened.exists_later_removed_of_introduced_not_mem_terminal
      kg huNotTerminalGlobal
  obtain ⟨h, r, hhr⟩ := X.stepIndex_surjective kRemove
  have huRemovedH :
      ((X.block h).deformation.step r).before.vertex
          ((X.block h).deformation.step r).removedIndex = u := by
    have hstep := X.step_eq h r
    rw [hhr] at hstep
    have hremoved := congrArg
      (fun z : ConcreteDeformationStep O Cprime =>
        z.before.vertex z.removedIndex) hstep
    calc
      ((X.block h).deformation.step r).before.vertex
          ((X.block h).deformation.step r).removedIndex =
          (X.flattened.deformation.step kRemove).before.vertex
            (X.flattened.deformation.step kRemove).removedIndex :=
        hremoved.symm
      _ = (X.flattened.deformation.step kg).introduced := hkRemove.symm
      _ = u := huIntroGlobal
  have hnotHLtG : ¬h.val < g.val := by
    intro hhg
    have hreverse := X.stepIndex_order h g r tg (Or.inl hhg)
    rw [hhr] at hreverse
    exact (by omega)
  have hhne : h ≠ g := by
    intro hEq
    subst h
    exact (X.introduced_ne_removed g tg r)
      (huIntroG.trans huRemovedH.symm)
  have hgh : g.val < h.val := by
    have hneVal : h.val ≠ g.val := by
      intro hval
      exact hhne (Fin.ext hval)
    omega
  have huPathH : u ∈ Set.range (X.block h).path.vertex := by
    rw [← huRemovedH]
    exact X.removed_mem_path h r
  by_cases huCurrentPath : u ∈ Set.range (X.block i).path.vertex
  · have hiNeG : i ≠ g := by
      intro hEq
      have hval := congrArg Fin.val hEq
      omega
    have hiNeH : i ≠ h := by
      intro hEq
      have hval := congrArg Fin.val hEq
      omega
    have hgNeH : g ≠ h := by
      intro hEq
      have hval := congrArg Fin.val hEq
      omega
    have hthree := O.atMostTwoContainingPaths u
      (P := Set.range (X.block i).path.vertex)
      (Q := Set.range (X.block g).path.vertex)
      (R := Set.range (X.block h).path.vertex)
      ⟨X.path_mem_family i, huCurrentPath⟩
      ⟨X.path_mem_family g, huPathG⟩
      ⟨X.path_mem_family h, huPathH⟩
    rcases hthree with hEq | hEq | hEq
    · exact X.path_pairwise hiNeG hEq
    · exact X.path_pairwise hiNeH hEq
    · exact X.path_pairwise hgNeH hEq
  · have hexactU := X.dependent_exactlyOne_in_oriented_family
      i hu huCurrentPath
    have huniqueU :=
      FixedPairingPathFamily.atMostOneContainingPath_of_exactlyOne
        ((X.side i).family O) hexactU
    have hEq := huniqueU
      ⟨X.path_mem_oriented_family i g, huPathG⟩
      ⟨X.path_mem_oriented_family i h, huPathH⟩
    have hgNeH : g ≠ h := by
      intro hEqIndex
      have hval := congrArg Fin.val hEqIndex
      omega
    exact X.path_pairwise hgNeH hEq

/-- The terminal occurrence transport required by the conditional Lemma 16
bridge is a theorem of the finite trace. -/
theorem terminalPathTransportData
    (X : FiniteMixedSideSearchTrace S originalHole)
    (hclaw : G.IsClawFree) :
    X.Lemma16TerminalPathTransportData where
  earlierWitness_outside := by
    intro i s u s' u' P hu huOutside hs' hu' hanti' hunique huP
    exact X.earlierWitness_not_mem_terminal hclaw i hu huOutside
      hs' hu' hanti' hunique huP

end FiniteMixedSideSearchTrace
end ConcretePathDeformation
end FixedPairingPathFamily
end SimpleGraph
