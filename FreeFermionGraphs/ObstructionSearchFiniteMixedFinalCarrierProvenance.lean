import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalContainment

/-!
# Carrier provenance for finite mixed-side final holes

A single replacement adds only its introduced vertex.  Therefore every vertex
of the final hole of one path block either belonged to the block's initial hole
or lies on that block's active path.  Iterating over the actual finite block
sequence shows that every vertex of the manuscript terminal hole either came
from the initialized original hole or lies on an appended execution path.

For an obstruction target, both alternatives are impossible: the initializer
clone certificate puts it outside the original hole, and the stopping rule
excludes it from every appended path.  Hence the target is outside each
positive final execution hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Every vertex of a deformed hole is either an old carrier vertex or the
single introduced vertex. -/
theorem mem_range_or_eq_introduced_of_mem_range_deform
    (C : IndexedInducedHole G)
    {introduced x : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hx : x ∈ Set.range (C.deform h).vertex) :
    x ∈ Set.range C.vertex ∨ x = introduced := by
  obtain ⟨q, hq⟩ := hx
  by_cases hqi : q = i
  · right
    subst q
    simpa using hq.symm
  · left
    refine ⟨q, ?_⟩
    have haway := C.deform_vertex_away h hqi
    exact haway.symm.trans hq

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcreteDeformationStep

/-- Step-level carrier provenance. -/
theorem mem_before_or_eq_introduced_of_mem_after
    (S : ConcreteDeformationStep O Cprime)
    {x : V}
    (hx : x ∈ Set.range S.after.vertex) :
    x ∈ Set.range S.before.vertex ∨ x = S.introduced := by
  simpa [ConcreteDeformationStep.after] using
    S.before.mem_range_or_eq_introduced_of_mem_range_deform
      S.deformation hx

end ConcreteDeformationStep

namespace ConcretePathDeformation

/-- Every vertex surviving through the first `n+1` steps of one path block
came from the block's initial hole or lies on the common active path. -/
theorem mem_initialHole_or_mem_path_of_mem_stepAfter
    (D : ConcretePathDeformation O Cprime)
    {x : V} (n : Nat) (hn : n < D.deformation.stepCount)
    (hx : x ∈ Set.range (D.deformation.step ⟨n, hn⟩).after.vertex) :
    x ∈ Set.range D.initialHole.vertex ∨
      x ∈ Set.range D.path.vertex := by
  induction n with
  | zero =>
      rcases (D.deformation.step ⟨0, hn⟩).
          mem_before_or_eq_introduced_of_mem_after hx with hbefore | hintroduced
      · exact Or.inl (by simpa [ConcretePathDeformation.initialHole,
          ConcretePathDeformation.firstIndex] using hbefore)
      · right
        rw [hintroduced]
        rw [← D.activePath_eq ⟨0, hn⟩]
        exact (D.deformation.step ⟨0, hn⟩).introduced_mem_activePath
  | succ n ih =>
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      rcases (D.deformation.step current).
          mem_before_or_eq_introduced_of_mem_after (by simpa [current] using hx) with
        hbefore | hintroduced
      · have hnPrev : n < D.deformation.stepCount := by omega
        let previous : Fin D.deformation.stepCount := ⟨n, hnPrev⟩
        have hchain :
            Set.range (D.deformation.step previous).after.vertex =
              Set.range (D.deformation.step current).before.vertex :=
          D.deformation.carrier_chain (by simp [previous, current])
        have hxPrevious :
            x ∈ Set.range (D.deformation.step previous).after.vertex := by
          rw [hchain]
          exact hbefore
        exact ih hnPrev hxPrevious
      · right
        rw [hintroduced]
        rw [← D.activePath_eq current]
        exact (D.deformation.step current).introduced_mem_activePath

/-- Every vertex in the final hole of one complete path block came from its
initial hole or lies on the block path. -/
theorem mem_initialHole_or_mem_path_of_mem_finalHole
    (D : ConcretePathDeformation O Cprime)
    {x : V}
    (hx : x ∈ Set.range D.finalHole.vertex) :
    x ∈ Set.range D.initialHole.vertex ∨
      x ∈ Set.range D.path.vertex := by
  simpa [ConcretePathDeformation.finalHole,
    ConcretePathDeformation.lastIndex] using
    D.mem_initialHole_or_mem_path_of_mem_stepAfter
      (D.deformation.stepCount - 1) (by omega) hx

end ConcretePathDeformation

namespace ObstructionSearchInitialization

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}
  {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideOrderedOSExecution

/-- Carrier provenance through the first `n+1` actual finite path blocks. -/
theorem mem_originalHole_or_mem_path_through
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    {x : V} (n : Nat) (hn : n < X.blockCount)
    (hx : x ∈ Set.range (X.block ⟨n, hn⟩).finalHole.vertex) :
    x ∈ Set.range originalHole.vertex ∨
      ∃ q : Fin X.blockCount,
        q.val ≤ n ∧ x ∈ X.path q := by
  induction n with
  | zero =>
      rcases (X.block ⟨0, hn⟩).
          mem_initialHole_or_mem_path_of_mem_finalHole hx with
        hinitial | hpath
      · left
        have hctx :=
          (X.localData ⟨0, hn⟩).neighborhood
        have hfirst :
            Set.range (X.block ⟨0, hn⟩).initialHole.vertex =
              Set.range originalHole.vertex := by
          have h :=
            (ConcretePathDeformation.FiniteMixedSideLemma11AContext.first
              (X.side ⟨0, hn⟩) (X.localData ⟨0, hn⟩) rfl).originalHole
          simpa using h
        rw [← hfirst]
        exact hinitial
      · exact Or.inr ⟨⟨0, hn⟩, by omega, hpath⟩
  | succ n ih =>
      let current : Fin X.blockCount := ⟨n + 1, hn⟩
      rcases (X.block current).
          mem_initialHole_or_mem_path_of_mem_finalHole (by simpa [current] using hx) with
        hinitial | hpath
      · have hnPrev : n < X.blockCount := by omega
        let previous : Fin X.blockCount := ⟨n, hnPrev⟩
        have hchain :
            Set.range (X.block previous).finalHole.vertex =
              Set.range (X.block current).initialHole.vertex := by
          let C :=
            (ConcretePathDeformation.FiniteMixedSideLemma11AContext.later
              ((X.localData current).toFiniteHistory
                (fun r => X.block (X.priorIndex current r))
                (fun r => X.side (X.priorIndex current r))
                (fun r => X.localData (X.priorIndex current r))
                (by intro r q hrq; exact False.elim (by omega))
                (by intro r; exact False.elim (by omega))
                rfl rfl))
          exact False.elim (by omega)
        have hxPrevious :
            x ∈ Set.range (X.block previous).finalHole.vertex := by
          rw [hchain]
          exact hinitial
        rcases ih hnPrev hxPrevious with horiginal | ⟨q, hqle, hxq⟩
        · exact Or.inl horiginal
        · exact Or.inr ⟨q, by omega, hxq⟩
      · exact Or.inr ⟨current, by omega, hpath⟩

end FiniteMixedSideOrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
