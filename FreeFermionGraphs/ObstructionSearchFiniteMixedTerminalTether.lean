import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalDegreeThreeReduction

/-!
# Literal terminal tether data for finite mixed-side executions

A tethered obstruction search reaches the common target from one end of an
alternating terminal path.  Operationally, the target has degree three in the
positive final execution hole.  Its staged clone centre is adjacent to the
same-side terminal-path vertex two steps toward the incoming endpoint.

For two distinct incoming searches the endpoint slots are opposite.  If their
staged clone centres coincide, the two one-sided tether facts combine into the
common-centre neighborhood used by the manuscript's immediate claw argument.
The unequal-centre propagation remains a separate obligation.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Literal one-sided tether information for an actual incoming obstruction
arc.  The selected slot determines which same-side path flank is supplied by
this search. -/
structure FiniteMixedSideIncomingTerminalTether
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) : Prop where
  targetIndex : Fin (T.terminalPath target).card
  target_eq : (T.terminalPath target).vertex targetIndex = (target : V)
  targetIndex_even : Even targetIndex.val
  pathCard_odd : Odd (T.terminalPath target).card
  positive_finalDegree_three :
    ∀ hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount,
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.externalDegree (target : V) = 3
  clone_adj_flank :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      ∀ q : Fin (T.terminalPath target).card,
        match T.currentSlot source target with
        | .first =>
            q.val + 2 = targetIndex.val →
              G.Adj X.center (T.terminalPath target).vertex q
        | .last =>
            targetIndex.val + 2 = q.val →
              G.Adj X.center (T.terminalPath target).vertex q

/-- Literal tether data for every actual obstruction arc of the initialized
finite execution. -/
structure FiniteMixedSideInitializationTerminalTetherData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  tether : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingTerminalTether T source target incoming

namespace FiniteMixedSideInitializationTerminalTetherData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- The operational tether definition supplies the exact positive final-hole
degree required by the staged clone construction. -/
theorem positive_finalDegree_three
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target)
    (_hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V))
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 :=
  (D.tether incoming).positive_finalDegree_three hpos

/-- Tether data therefore constructs all staged final-hole clone witnesses,
including the empty-execution branch already handled by the stopping rule. -/
noncomputable def toInteriorTerminalCloneData
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideInitializationInteriorTerminalCloneData T :=
  T.interiorTerminalCloneData_of_positive_finalDegree_three
    hclaw D.positive_finalDegree_three

/-- The target index selected by two tether witnesses for the same terminal
path is identical. -/
theorem targetIndex_eq
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    {source source' target : I.Node}
    {incoming : I.graph.Arc source target}
    {incoming' : I.graph.Arc source' target} :
    (D.tether incoming).targetIndex = (D.tether incoming').targetIndex := by
  apply (T.terminalPath target).injective
  exact (D.tether incoming).target_eq.trans
    (D.tether incoming').target_eq.symm

/-- Equal staged clone centres combine the two one-sided tether facts into the
paper's common-centre terminal neighborhood. -/
theorem sameCloneTerminalNeighborhood_of_center_eq
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target)
    (left : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (right : FiniteMixedSideIncomingTerminalCloneWitness
      T source' target incoming')
    (hcenter : left.center = right.center) :
    Nonempty
      ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) := by
  let L := D.tether incoming
  let R := D.tether incoming'
  have hslots :
      T.currentSlot source target ≠ T.currentSlot source' target :=
    T.currentSlot_ne_of_twoIncoming hclaw hne incoming incoming'
  have hindex : L.targetIndex = R.targetIndex := D.targetIndex_eq
  cases hs : T.currentSlot source target <;>
    cases hs' : T.currentSlot source' target
  · exact (hslots (hs.trans hs'.symm)).elim
  · exact ⟨
      { targetIndex := L.targetIndex
        target_eq := L.target_eq
        targetIndex_even := L.targetIndex_even
        pathCard_odd := L.pathCard_odd
        cloneCenter := left.center
        clone_adj_target := left.target_adj_center.symm
        clone_adj_previous := by
          intro q hq
          have h := L.clone_adj_flank left q
          simpa [hs] using h hq
        clone_adj_next := by
          intro q hq
          have h := R.clone_adj_flank right q
          have hq' : R.targetIndex.val + 2 = q.val := by
            simpa [hindex] using hq
          have hadj : G.Adj right.center (T.terminalPath target).vertex q := by
            simpa [hs'] using h hq'
          simpa [hcenter] using hadj }⟩
  · exact ⟨
      { targetIndex := L.targetIndex
        target_eq := L.target_eq
        targetIndex_even := L.targetIndex_even
        pathCard_odd := L.pathCard_odd
        cloneCenter := left.center
        clone_adj_target := left.target_adj_center.symm
        clone_adj_previous := by
          intro q hq
          have h := R.clone_adj_flank right q
          have hq' : q.val + 2 = R.targetIndex.val := by
            simpa [hindex] using hq
          have hadj : G.Adj right.center (T.terminalPath target).vertex q := by
            simpa [hs'] using h hq'
          simpa [hcenter] using hadj
        clone_adj_next := by
          intro q hq
          have h := L.clone_adj_flank left q
          simpa [hs] using h hq }⟩
  · exact (hslots (hs.trans hs'.symm)).elim

/-- The only remaining pairwise branch after literal tether data is the
unequal-centre propagation. -/
structure DistinctCenterConsequences
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree) : Prop where
  propagate :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target)
      (hsource :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V))
      (hsource' :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source' target) ≠ (target : V)),
      let C := D.toInteriorTerminalCloneData hclaw
      let left := C.witnessOfInterior incoming hsource
      let right := C.witnessOfInterior incoming' hsource'
      left.center ≠ right.center →
        (Nonempty
            (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
              T source target incoming) ∨
          Nonempty
            (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
              T source' target incoming'))

/-- Literal tether data plus the genuine unequal-centre propagation constructs
the complete staged clone-comparison analysis. -/
noncomputable def toTerminalCloneComparisonAnalysis
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree)
    (A : D.DistinctCenterConsequences hclaw) :
    FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis T where
  terminalGeometry := by
    classical
    intro source source' target hne incoming incoming' hsource hsource'
    let C := D.toInteriorTerminalCloneData hclaw
    let left := C.witnessOfInterior incoming hsource
    let right := C.witnessOfInterior incoming' hsource'
    refine ⟨left, right, ?_, ?_⟩
    · intro hcenter
      exact D.sameCloneTerminalNeighborhood_of_center_eq
        hclaw hne incoming incoming' left right hcenter
    · intro hcenter
      exact A.propagate hne incoming incoming' hsource hsource' hcenter

/-- Exact paper-facing Lemma 14 once the literal unequal-centre propagation is
constructed.  No same-clone certificate or degree-three premise remains. -/
theorem paperLemma14_of_distinctCenterConsequences
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree)
    (A : D.DistinctCenterConsequences hclaw) :
    PaperLemma14Conclusion I :=
  T.paperLemma14_of_terminalCloneComparisonAnalysis
    (D.toTerminalCloneComparisonAnalysis hclaw A) hclaw

end FiniteMixedSideInitializationTerminalTetherData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
