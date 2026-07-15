import FreeFermionGraphs.FiveNeighbors

/-!
# Exact cardinality-five neighboring relation

This module packages the cardinality-five result in the exact form used by
Lemma 7: an induced path cannot have five distinct external neighbors, and
five distinct external neighbors of an induced hole force that hole to have
exactly five vertices.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- One of the twelve cyclic orderings of five labelled vertices is present.
The ten arguments are the possible edges `pq`, `pr`, `ps`, `pt`, `qr`,
`qs`, `qt`, `rs`, `rt`, and `st`. -/
def FiveCycleEdges
    (pq pr ps pt qr qs qt rs rt st : Prop) : Prop :=
  (pq ∧ qr ∧ rs ∧ st ∧ pt) ∨
    (pq ∧ qr ∧ rt ∧ st ∧ ps) ∨
    (pq ∧ qs ∧ rs ∧ rt ∧ pt) ∨
    (pq ∧ qs ∧ st ∧ rt ∧ pr) ∨
    (pq ∧ qt ∧ rt ∧ rs ∧ ps) ∨
    (pq ∧ qt ∧ st ∧ rs ∧ pr) ∨
    (pr ∧ qr ∧ qt ∧ st ∧ ps) ∨
    (pr ∧ rt ∧ qt ∧ qs ∧ ps) ∨
    (pr ∧ qr ∧ qs ∧ st ∧ pt) ∨
    (pr ∧ rs ∧ qs ∧ qt ∧ pt) ∨
    (ps ∧ qs ∧ qr ∧ rt ∧ pt) ∨
    (ps ∧ rs ∧ qr ∧ qt ∧ pt)

/-- A degree-two graph on five labelled vertices contains a cycle through
all five vertices. -/
set_option maxHeartbeats 2000000 in
theorem FiveNeighborCycleCase.cycle_edges
    {pq pr ps pt qr qs qt rs rt st : Prop}
    (h : FiveNeighborCycleCase pq pr ps pt qr qs qt rs rt st) :
    FiveCycleEdges pq pr ps pt qr qs qt rs rt st := by
  simp only [FiveNeighborCycleCase, ExactlyTwoOfFour, FiveCycleEdges] at *
  tauto

/-- Five distinct vertices of an indexed induced path cannot form a cycle. -/
theorem IndexedInducedPath.not_five_cycle
    (P : IndexedInducedPath G) {a b c d e : Fin P.card}
    (hab : G.Adj (P.vertex a) (P.vertex b))
    (hbc : G.Adj (P.vertex b) (P.vertex c))
    (hcd : G.Adj (P.vertex c) (P.vertex d))
    (hde : G.Adj (P.vertex d) (P.vertex e))
    (hae : G.Adj (P.vertex a) (P.vertex e)) : False := by
  have hab' := (P.adj_iff a b).1 hab
  have hbc' := (P.adj_iff b c).1 hbc
  have hcd' := (P.adj_iff c d).1 hcd
  have hde' := (P.adj_iff d e).1 hde
  have hae' := (P.adj_iff a e).1 hae
  rcases hab' with hab' | hab' <;>
    rcases hbc' with hbc' | hbc' <;>
    rcases hcd' with hcd' | hcd' <;>
    rcases hde' with hde' | hde' <;>
    rcases hae' with hae' | hae' <;> omega

/-- An indexed induced hole containing a cycle through five distinct indexed
vertices has exactly five vertices. -/
theorem IndexedInducedHole.five_cycle_forces_card_eq_five
    (C : IndexedInducedHole G) {a b c d e : Fin C.card}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hab_adj : G.Adj (C.vertex a) (C.vertex b))
    (hbc_adj : G.Adj (C.vertex b) (C.vertex c))
    (hcd_adj : G.Adj (C.vertex c) (C.vertex d))
    (hde_adj : G.Adj (C.vertex d) (C.vertex e))
    (hae_adj : G.Adj (C.vertex a) (C.vertex e)) :
    C.card = 5 := by
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hacv : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hadv : a.val ≠ d.val := fun h => had (Fin.ext h)
  have haev : a.val ≠ e.val := fun h => hae (Fin.ext h)
  have hbcv : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  have hbdv : b.val ≠ d.val := fun h => hbd (Fin.ext h)
  have hbev : b.val ≠ e.val := fun h => hbe (Fin.ext h)
  have hcdv : c.val ≠ d.val := fun h => hcd (Fin.ext h)
  have hcev : c.val ≠ e.val := fun h => hce (Fin.ext h)
  have hdev : d.val ≠ e.val := fun h => hde (Fin.ext h)
  have hcard : 4 ≤ C.card := C.four_le_card
  have ha : a.val < C.card := a.isLt
  have hb : b.val < C.card := b.isLt
  have hc : c.val < C.card := c.isLt
  have hd : d.val < C.card := d.isLt
  have he : e.val < C.card := e.isLt
  have hab' := (C.adj_iff a b).1 hab_adj
  have hbc' := (C.adj_iff b c).1 hbc_adj
  have hcd' := (C.adj_iff c d).1 hcd_adj
  have hde' := (C.adj_iff d e).1 hde_adj
  have hae' := (C.adj_iff a e).1 hae_adj
  unfold CyclicAdjacent at hab' hbc' hcd' hde' hae'
  rcases hab' with hab' | hab' | hab' | hab' <;>
    rcases hbc' with hbc' | hbc' | hbc' | hbc' <;>
    rcases hcd' with hcd' | hcd' | hcd' | hcd' <;>
    rcases hde' with hde' | hde' | hde' | hde' <;>
    rcases hae' with hae' | hae' | hae' | hae' <;> omega

/-- Exact path consequence of case (b.ii) in Lemma 7: five distinct
external neighbors of an induced path are impossible. -/
theorem IndexedInducedPath.not_five_external_neighbors
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {p q r s t : Fin P.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpt : p ≠ t)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqt : q ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hjp : G.Adj j (P.vertex p)) (hjq : G.Adj j (P.vertex q))
    (hjr : G.Adj j (P.vertex r)) (hjs : G.Adj j (P.vertex s))
    (hjt : G.Adj j (P.vertex t)) : False := by
  have hcycle := P.five_external_neighbors_induce_cycle hclaw hjP
    hpq hpr hps hpt hqr hqs hqt hrs hrt hst hjp hjq hjr hjs hjt
  rcases hcycle.cycle_edges with
      ⟨hpq', hqr', hrs', hst', hpt'⟩ |
      ⟨hpq', hqr', hrt', hst', hps'⟩ |
      ⟨hpq', hqs', hrs', hrt', hpt'⟩ |
      ⟨hpq', hqs', hst', hrt', hpr'⟩ |
      ⟨hpq', hqt', hrt', hrs', hps'⟩ |
      ⟨hpq', hqt', hst', hrs', hpr'⟩ |
      ⟨hpr', hqr', hqt', hst', hps'⟩ |
      ⟨hpr', hrt', hqt', hqs', hps'⟩ |
      ⟨hpr', hqr', hqs', hst', hpt'⟩ |
      ⟨hpr', hrs', hqs', hqt', hpt'⟩ |
      ⟨hps', hqs', hqr', hrt', hpt'⟩ |
      ⟨hps', hrs', hqr', hqt', hpt'⟩
  · exact P.not_five_cycle hpq' hqr' hrs' hst' hpt'
  · exact P.not_five_cycle hpq' hqr' hrt' hst'.symm hps'
  · exact P.not_five_cycle hpq' hqs' hrs'.symm hrt' hpt'
  · exact P.not_five_cycle hpq' hqs' hst' hrt'.symm hpr'
  · exact P.not_five_cycle hpq' hqt' hrt'.symm hrs' hps'
  · exact P.not_five_cycle hpq' hqt' hst'.symm hrs'.symm hpr'
  · exact P.not_five_cycle hpr' hqr'.symm hqt' hst'.symm hps'
  · exact P.not_five_cycle hpr' hrt' hqt'.symm hqs' hps'
  · exact P.not_five_cycle hpr' hqr'.symm hqs' hst' hpt'
  · exact P.not_five_cycle hpr' hrs' hqs'.symm hqt' hpt'
  · exact P.not_five_cycle hps' hqs'.symm hqr' hrt' hpt'
  · exact P.not_five_cycle hps' hrs'.symm hqr'.symm hqt' hpt'

/-- Exact hole consequence of case (b.ii) in Lemma 7: if an external vertex
has five distinct neighbors on an induced hole, the hole has length five. -/
theorem IndexedInducedHole.five_external_neighbors_force_card_five
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) {p q r s t : Fin C.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpt : p ≠ t)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqt : q ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hjp : G.Adj j (C.vertex p)) (hjq : G.Adj j (C.vertex q))
    (hjr : G.Adj j (C.vertex r)) (hjs : G.Adj j (C.vertex s))
    (hjt : G.Adj j (C.vertex t)) :
    C.card = 5 := by
  have hcycle := C.five_external_neighbors_induce_cycle hclaw hjC
    hpq hpr hps hpt hqr hqs hqt hrs hrt hst hjp hjq hjr hjs hjt
  rcases hcycle.cycle_edges with
      ⟨hpq', hqr', hrs', hst', hpt'⟩ |
      ⟨hpq', hqr', hrt', hst', hps'⟩ |
      ⟨hpq', hqs', hrs', hrt', hpt'⟩ |
      ⟨hpq', hqs', hst', hrt', hpr'⟩ |
      ⟨hpq', hqt', hrt', hrs', hps'⟩ |
      ⟨hpq', hqt', hst', hrs', hpr'⟩ |
      ⟨hpr', hqr', hqt', hst', hps'⟩ |
      ⟨hpr', hrt', hqt', hqs', hps'⟩ |
      ⟨hpr', hqr', hqs', hst', hpt'⟩ |
      ⟨hpr', hrs', hqs', hqt', hpt'⟩ |
      ⟨hps', hqs', hqr', hrt', hpt'⟩ |
      ⟨hps', hrs', hqr', hqt', hpt'⟩
  · exact C.five_cycle_forces_card_eq_five
      hpq hpr hps hpt hqr hqs hqt hrs hrt hst
      hpq' hqr' hrs' hst' hpt'
  · exact C.five_cycle_forces_card_eq_five
      hpq hpr hpt hps hqr hqt hqs hrt hrs hst.symm
      hpq' hqr' hrt' hst'.symm hps'
  · exact C.five_cycle_forces_card_eq_five
      hpq hps hpr hpt hqs hqr hqt hrs.symm hst hrt
      hpq' hqs' hrs'.symm hrt' hpt'
  · exact C.five_cycle_forces_card_eq_five
      hpq hps hpt hpr hqs hqt hqr hst hrs.symm hrt.symm
      hpq' hqs' hst' hrt'.symm hpr'
  · exact C.five_cycle_forces_card_eq_five
      hpq hpt hpr hps hqt hqr hqs hrt.symm hst.symm hrs
      hpq' hqt' hrt'.symm hrs' hps'
  · exact C.five_cycle_forces_card_eq_five
      hpq hpt hps hpr hqt hqs hqr hst.symm hrt.symm hrs.symm
      hpq' hqt' hst'.symm hrs'.symm hpr'
  · exact C.five_cycle_forces_card_eq_five
      hpr hpq hpt hps hqr.symm hrt hrs hqt hqs hst.symm
      hpr' hqr'.symm hqt' hst'.symm hps'
  · exact C.five_cycle_forces_card_eq_five
      hpr hpt hpq hps hrt hqr.symm hrs hqt.symm hst.symm hqs
      hpr' hrt' hqt'.symm hqs' hps'
  · exact C.five_cycle_forces_card_eq_five
      hpr hpq hps hpt hqr.symm hrs hrt hqs hqt hst
      hpr' hqr'.symm hqs' hst' hpt'
  · exact C.five_cycle_forces_card_eq_five
      hpr hps hpq hpt hrs hqr.symm hrt hqs.symm hst hqt
      hpr' hrs' hqs'.symm hqt' hpt'
  · exact C.five_cycle_forces_card_eq_five
      hps hpq hpr hpt hqs.symm hrs.symm hst hqr hqt hrt
      hps' hqs'.symm hqr' hrt' hpt'
  · exact C.five_cycle_forces_card_eq_five
      hps hpr hpq hpt hrs.symm hqs.symm hst hqr.symm hrt hqt
      hps' hrs'.symm hqr'.symm hqt' hpt'

end SimpleGraph
