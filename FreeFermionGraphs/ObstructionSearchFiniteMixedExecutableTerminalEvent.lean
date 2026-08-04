import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalAlternatingLabels

/-!
# Executable terminal events for finite obstruction searches

The terminal branch of Definition 19/20 selects an odd alternating component,
a target on its endpoint colour side, and a tether centre on the adjacent
opposite-side path vertex.  This file records those raw coordinates rather
than the parity, degree, or flank-adjacency conclusions used by Lemma 14.

The derived interface proves:

* evenness of the target coordinate and odd terminal-path cardinality;
* positive final-hole degree three from the literal clone relation; and
* adjacency of the staged clone centre to the same-side two-step flank.

No conclusion of Lemma 14 is stored in the event data.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A literal clone of a hole vertex has exactly three neighbours on the hole:
the cloned vertex and its two cycle neighbours. -/
theorem SingleVertexDeformation.externalDegree_eq_three
    {C : IndexedInducedHole G} {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) :
    C.externalDegree s = 3 := by
  classical
  obtain ⟨p, q, hpq, hip, hiq, hpqNonadj⟩ :=
    C.exists_two_nonadjacent_neighbors i
  have hipIndex : i ≠ p := by
    intro hipEq
    subst p
    exact G.loopless.irrefl (C.vertex i) hip
  have hiqIndex : i ≠ q := by
    intro hiqEq
    subst q
    exact G.loopless.irrefl (C.vertex i) hiq
  have hset : C.neighborIndexSet s = ({i, p, q} : Set (Fin C.card)) := by
    ext k
    constructor
    · intro hsk
      have hcases := (h.adj_iff k).1 hsk
      rcases hcases with rfl | hik
      · simp
      · rcases C.adjacent_index_eq_of_two_distinct_neighbors
          hpq hip hiq hik with rfl | rfl <;> simp
    · intro hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl
      · exact h.adj_clone
      · exact h.adj_of_clone_adj hip
      · exact h.adj_of_clone_adj hiq
  unfold externalDegree
  rw [hset]
  simp [hipIndex, hiqIndex, hpq]

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Raw odd-alternating coordinates for the terminal component selected by the
obstruction search.  The two coordinate families partition the indexed path;
only their parity and the target/last-endpoint coordinates are retained. -/
structure FiniteMixedSideTerminalComponentExecution
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (target : I.Node) where
  sameCount : Nat
  otherCount : Nat
  sameIndex : Fin sameCount → Fin (T.terminalPath target).card
  otherIndex : Fin otherCount → Fin (T.terminalPath target).card
  index_partition :
    ∀ q : Fin (T.terminalPath target).card,
      (∃ i : Fin sameCount, q = sameIndex i) ∨
        (∃ i : Fin otherCount, q = otherIndex i)
  sameIndex_even : ∀ i : Fin sameCount, Even (sameIndex i).val
  otherIndex_odd : ∀ i : Fin otherCount, Odd (otherIndex i).val
  targetCoordinate : Fin sameCount
  target_eq :
    (T.terminalPath target).vertex (sameIndex targetCoordinate) =
      (target : V)
  lastCoordinate : Fin sameCount
  last_eq :
    sameIndex lastCoordinate =
      (T.terminalPath target).obstructionEndpointIndex .last

namespace FiniteMixedSideTerminalComponentExecution

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target : I.Node}

/-- The path-side selected by the raw even coordinates. -/
def sameSide
    (C : FiniteMixedSideTerminalComponentExecution T target) : Set V :=
  Set.range (fun i : Fin C.sameCount =>
    (T.terminalPath target).vertex (C.sameIndex i))

/-- Raw coordinate partitioning proves that a path index is on the selected
terminal side exactly when its value is even. -/
theorem index_even_iff_mem_sameSide
    (C : FiniteMixedSideTerminalComponentExecution T target)
    (q : Fin (T.terminalPath target).card) :
    Even q.val ↔ (T.terminalPath target).vertex q ∈ C.sameSide := by
  constructor
  · intro hqEven
    rcases C.index_partition q with ⟨i, rfl⟩ | ⟨i, hi⟩
    · exact ⟨i, rfl⟩
    · obtain ⟨a, ha⟩ := hqEven
      obtain ⟨b, hb⟩ := C.otherIndex_odd i
      have hval := congrArg Fin.val hi
      omega
  · rintro ⟨i, hi⟩
    have hindex : q = C.sameIndex i :=
      (T.terminalPath target).injective hi.symm
    rw [hindex]
    exact C.sameIndex_even i

/-- The selected obstruction target is on the even terminal side. -/
theorem target_mem_sameSide
    (C : FiniteMixedSideTerminalComponentExecution T target) :
    (target : V) ∈ C.sameSide :=
  ⟨C.targetCoordinate, C.target_eq⟩

/-- The last endpoint is on the same even terminal side. -/
theorem lastEndpoint_mem_sameSide
    (C : FiniteMixedSideTerminalComponentExecution T target) :
    (T.terminalPath target).obstructionEndpoint .last ∈ C.sameSide := by
  refine ⟨C.lastCoordinate, ?_⟩
  change
    (T.terminalPath target).vertex (C.sameIndex C.lastCoordinate) =
      (T.terminalPath target).vertex
        ((T.terminalPath target).obstructionEndpointIndex .last)
  exact congrArg (T.terminalPath target).vertex C.last_eq

/-- The raw target coordinate is the canonical nearest-target coordinate. -/
theorem targetIndex_eq_canonical
    (C : FiniteMixedSideTerminalComponentExecution T target)
    {source : I.Node}
    (incoming : I.graph.Arc source target) :
    C.sameIndex C.targetCoordinate = T.terminalTargetIndex incoming := by
  apply (T.terminalPath target).injective
  exact C.target_eq.trans
    (T.terminalTargetIndex_target_eq incoming).symm

/-- Convert raw terminal coordinates to the alternating-label interface. -/
def toAlternatingLabelData
    (C : ∀ target : I.Node,
      FiniteMixedSideTerminalComponentExecution T target) :
    FiniteMixedSideTerminalAlternatingLabelData T where
  sameSide := fun target => (C target).sameSide
  index_even_iff_mem_sameSide := by
    intro target q
    exact (C target).index_even_iff_mem_sameSide q
  target_mem_sameSide := by
    intro source target incoming
    exact (C target).target_mem_sameSide
  lastEndpoint_mem_sameSide := by
    intro source target incoming
    exact (C target).lastEndpoint_mem_sameSide

end FiniteMixedSideTerminalComponentExecution

/-- Raw one-sided terminal stopping event.  A positive execution supplies the
literal final-hole clone relation.  The tether link is the adjacent path index
between the target and the endpoint-side same-colour flank. -/
structure FiniteMixedSideIncomingTerminalStopExecution
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (C : FiniteMixedSideTerminalComponentExecution T target)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  positive_target_clone :
    ∀ hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount,
      ∃ i : Fin
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).manuscriptFinalHole.card,
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).manuscriptFinalHole.SingleVertexDeformation
            (target : V) i
  linkIndex :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      Fin (T.terminalPath target).card
  link_center_eq :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      (T.terminalPath target).vertex (linkIndex X) = X.center
  link_toward_target :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      match T.currentSlot source target with
      | .first =>
          (linkIndex X).val + 1 = (C.sameIndex C.targetCoordinate).val
      | .last =>
          (C.sameIndex C.targetCoordinate).val + 1 = (linkIndex X).val

namespace FiniteMixedSideIncomingTerminalStopExecution

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {C : FiniteMixedSideTerminalComponentExecution T target}

/-- The raw clone relation gives the positive terminal-hole degree-three fact. -/
theorem positive_finalDegree_three
    (E : FiniteMixedSideIncomingTerminalStopExecution
      T C source target incoming)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 := by
  obtain ⟨i, hi⟩ := E.positive_target_clone hpos
  exact hi.externalDegree_eq_three

/-- The raw tether link lies between the target and the same-side two-step
flank, hence the staged clone centre is adjacent to that flank. -/
theorem clone_adj_flank
    (E : FiniteMixedSideIncomingTerminalStopExecution
      T C source target incoming)
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (q : Fin (T.terminalPath target).card) :
    match T.currentSlot source target with
    | .first =>
        q.val + 2 = (C.sameIndex C.targetCoordinate).val →
          G.Adj X.center ((T.terminalPath target).vertex q)
    | .last =>
        (C.sameIndex C.targetCoordinate).val + 2 = q.val →
          G.Adj X.center ((T.terminalPath target).vertex q) := by
  let r := E.linkIndex X
  have hcenter := E.link_center_eq X
  cases hs : T.currentSlot source target with
  | first =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : r.val + 1 = (C.sameIndex C.targetCoordinate).val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      right
      omega
  | last =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : (C.sameIndex C.targetCoordinate).val + 1 = r.val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      left
      omega

/-- Convert one raw terminal stop to the operational tether interface. -/
def toOperationalTether
    (E : FiniteMixedSideIncomingTerminalStopExecution
      T C source target incoming) :
    FiniteMixedSideIncomingOperationalTether T source target incoming where
  positive_finalDegree_three := E.positive_finalDegree_three
  clone_adj_flank := by
    intro X q
    have hindex := C.targetIndex_eq_canonical incoming
    simpa [hindex] using E.clone_adj_flank X q

end FiniteMixedSideIncomingTerminalStopExecution

/-- Terminal events emitted by the completed initialized obstruction-search
executions.  The component coordinates and each incoming stopping event are
raw Definition 19/20 data; the Lemma 14 terminal facts are derived below. -/
structure InitializationFiniteMixedSideExecutableTerminalEvent
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  component : ∀ target : I.Node,
    FiniteMixedSideTerminalComponentExecution T target
  stop : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingTerminalStopExecution
        T (component target) source target incoming

namespace InitializationFiniteMixedSideExecutableTerminalEvent

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- All arithmetic and one-sided tether conclusions are derived from the raw
terminal events. -/
def toLabelledOperationalTerminalData
    (E : InitializationFiniteMixedSideExecutableTerminalEvent T) :
    FiniteMixedSideInitializationLabelledOperationalTerminalData T where
  labels :=
    FiniteMixedSideTerminalComponentExecution.toAlternatingLabelData E.component
  tether := fun {source target} incoming =>
    (E.stop (source := source) (target := target) incoming).toOperationalTether

end InitializationFiniteMixedSideExecutableTerminalEvent

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
