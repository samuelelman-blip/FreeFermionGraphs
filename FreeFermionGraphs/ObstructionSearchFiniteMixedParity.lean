import FreeFermionGraphs.ObstructionSearchFiniteMixedPrefix

/-!
# Parity transport on bounded mixed-side histories

The parity argument in Lemma 11(a.ii) uses only the finite prefix of path
blocks preceding the current block.  This module proves that transport
directly on `FiniteMixedSideLemma11AHistoryData`, whose prior blocks are
indexed by `Fin priorCount`.

No total `Nat` history is constructed, and no conclusion of Lemma 11 or
Lemma 14 is stored as an assumption.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem parity_of_reoriented_commutes
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (A.reorient side).FullDefinition19Lemma11AData)
    (u : V)
    (hcomm : A.path.CommutesWith u) :
    A.finalHole.externalDegree u % 2 =
      A.initialHole.externalDegree u % 2 := by
  have hcommOriented : (A.reorient side).path.CommutesWith u := by
    simpa using hcomm
  have hparity :=
    (A.reorient side).finalDegree_mod_two_eq_initial_of_commutes
      F.neighborhood.pathOrder F.path_card_eq u hcommOriented
  cases side <;> exact hparity

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- A prior carrier block in the component side selected by Definition 19. -/
def orientedPrior
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) :
    ConcretePathDeformation ((H.priorSide r).family O) Cprime :=
  (H.priorBlock r).reorient (H.priorSide r)

@[simp] theorem orientedPrior_path
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) :
    (H.orientedPrior r).path = (H.priorBlock r).path :=
  rfl

/-- Reorientation does not change path commutation. -/
@[simp] theorem orientedPrior_commutesWith_iff
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) (u : V) :
    (H.orientedPrior r).path.CommutesWith u ↔
      (H.priorBlock r).path.CommutesWith u := by
  rfl

/-- Reorientation does not change path anticommutation. -/
@[simp] theorem orientedPrior_anticommutesWith_iff
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) (u : V) :
    (H.orientedPrior r).path.AnticommutesWith u ↔
      (H.priorBlock r).path.AnticommutesWith u := by
  rfl

/-- If the oriented prior block does not anticommute with `u`, the literal
carrier path commutes with `u`. -/
theorem prior_commutes_of_not_oriented_anticommutes
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) (u : V)
    (hnot : ¬(H.orientedPrior r).path.AnticommutesWith u) :
    (H.priorBlock r).path.CommutesWith u := by
  rcases (H.priorBlock r).path.commutesWith_or_anticommutesWith u with
      hcomm | hanti
  · exact hcomm
  · exact (hnot (by simpa using hanti)).elim

/-- A bounded prefix of commuting prior blocks preserves external-degree
parity from the first initial hole to the final hole of block `n`. -/
theorem finalDegree_mod_two_eq_initial_of_commutes_through
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (u : V) (n : Nat) (hn : n < H.priorCount)
    (hcomm : ∀ r : Fin H.priorCount, r.val ≤ n →
      (H.priorBlock r).path.CommutesWith u) :
    (H.priorBlock ⟨n, hn⟩).finalHole.externalDegree u % 2 =
      (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.externalDegree u % 2 := by
  induction n with
  | zero =>
      let current : Fin H.priorCount := ⟨0, hn⟩
      have hdata := H.priorData current
      simpa [current] using
        parity_of_reoriented_commutes
          (H.priorBlock current) (H.priorSide current) hdata u
          (hcomm current (by simp [current]))
  | succ n ih =>
      have hnPrevious : n < H.priorCount := by omega
      let previous : Fin H.priorCount := ⟨n, hnPrevious⟩
      let current : Fin H.priorCount := ⟨n + 1, hn⟩
      have hdata := H.priorData current
      have hcurrent :=
        parity_of_reoriented_commutes
          (H.priorBlock current) (H.priorSide current) hdata u
          (hcomm current (by simp [current]))
      have hmiddle :
          (H.priorBlock previous).finalHole.externalDegree u =
            (H.priorBlock current).initialHole.externalDegree u :=
        (H.priorBlock previous).finalHole.externalDegree_eq_of_range_eq
          (H.priorBlock current).initialHole
          (H.priorChain (r := previous) (q := current) (by
            simp [previous, current]))
      have hprevious :
          (H.priorBlock previous).finalHole.externalDegree u % 2 =
            (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.externalDegree u % 2 := by
        apply ih hnPrevious
        intro r hr
        exact hcomm r (by omega)
      calc
        (H.priorBlock ⟨n + 1, hn⟩).finalHole.externalDegree u % 2 =
            (H.priorBlock current).initialHole.externalDegree u % 2 := by
              simpa [current] using hcurrent
        _ = (H.priorBlock previous).finalHole.externalDegree u % 2 := by
              rw [hmiddle]
        _ = (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.externalDegree u % 2 :=
              hprevious

/-- The same bounded parity transport, stated using absence of
anticommutation in each side-oriented block. -/
theorem finalDegree_mod_two_eq_initial_of_no_oriented_anticommuting_through
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (u : V) (n : Nat) (hn : n < H.priorCount)
    (hnotAnti : ∀ r : Fin H.priorCount, r.val ≤ n →
      ¬(H.orientedPrior r).path.AnticommutesWith u) :
    (H.priorBlock ⟨n, hn⟩).finalHole.externalDegree u % 2 =
      (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.externalDegree u % 2 := by
  apply H.finalDegree_mod_two_eq_initial_of_commutes_through u n hn
  intro r hr
  exact H.prior_commutes_of_not_oriented_anticommutes
    r u (hnotAnti r hr)

/-- The final carrier of a nonempty bounded prior history has the same degree
parity as the manuscript original hole whenever no prior path anticommutes
with `u`. -/
theorem lastFinalDegree_mod_two_eq_original_of_no_oriented_anticommuting
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (u : V)
    (hnotAnti : ∀ r : Fin H.priorCount,
      ¬(H.orientedPrior r).path.AnticommutesWith u) :
    (H.priorBlock H.lastIndex).finalHole.externalDegree u % 2 =
      originalHole.externalDegree u % 2 := by
  have hparity :=
    H.finalDegree_mod_two_eq_initial_of_no_oriented_anticommuting_through
      u H.lastIndex.val H.lastIndex.isLt (fun r _ => hnotAnti r)
  have hinitial :
      (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.externalDegree u =
        originalHole.externalDegree u :=
    (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.externalDegree_eq_of_range_eq
      originalHole H.firstInitial_eq_original
  rw [hinitial] at hparity
  simpa using hparity

end FiniteMixedSideLemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
