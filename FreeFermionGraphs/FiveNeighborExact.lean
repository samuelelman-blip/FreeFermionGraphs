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

/-- Swapping the first two inputs preserves `ExactlyOneOfThree`. -/
theorem ExactlyOneOfThree.swap12 {x y z : Prop}
    (h : ExactlyOneOfThree x y z) : ExactlyOneOfThree y x z := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact Or.inr (Or.inl ⟨hy, hx, hz⟩)
  · exact Or.inl ⟨hy, hx, hz⟩
  · exact Or.inr (Or.inr ⟨hy, hx, hz⟩)

/-- Swapping the last two inputs preserves `ExactlyOneOfThree`. -/
theorem ExactlyOneOfThree.swap23 {x y z : Prop}
    (h : ExactlyOneOfThree x y z) : ExactlyOneOfThree x z y := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact Or.inl ⟨hx, hz, hy⟩
  · exact Or.inr (Or.inr ⟨hx, hz, hy⟩)
  · exact Or.inr (Or.inl ⟨hx, hz, hy⟩)

/-- Swapping the first two inputs preserves `ExactlyTwoOfThree`. -/
theorem ExactlyTwoOfThree.swap12 {x y z : Prop}
    (h : ExactlyTwoOfThree x y z) : ExactlyTwoOfThree y x z := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact Or.inl ⟨hy, hx, hz⟩
  · exact Or.inr (Or.inr ⟨hy, hx, hz⟩)
  · exact Or.inr (Or.inl ⟨hy, hx, hz⟩)

/-- Swapping the last two inputs preserves `ExactlyTwoOfThree`. -/
theorem ExactlyTwoOfThree.swap23 {x y z : Prop}
    (h : ExactlyTwoOfThree x y z) : ExactlyTwoOfThree x z y := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact Or.inr (Or.inl ⟨hx, hz, hy⟩)
  · exact Or.inl ⟨hx, hz, hy⟩
  · exact Or.inr (Or.inr ⟨hx, hz, hy⟩)

/-- If the first of four propositions is true and exactly two are true,
exactly one of the remaining three is true. -/
theorem ExactlyTwoOfFour.tail_exactlyOne {w x y z : Prop}
    (h : ExactlyTwoOfFour w x y z) (hw : w) :
    ExactlyOneOfThree x y z := by
  rcases h with ⟨_, hx, hy, hz⟩ | ⟨_, hx, hy, hz⟩ |
    ⟨_, hx, hy, hz⟩ | ⟨hnw, _, _, _⟩ |
    ⟨hnw, _, _, _⟩ | ⟨hnw, _, _, _⟩
  · exact Or.inl ⟨hx, hy, hz⟩
  · exact Or.inr (Or.inl ⟨hx, hy, hz⟩)
  · exact Or.inr (Or.inr ⟨hx, hy, hz⟩)
  · exact (hnw hw).elim
  · exact (hnw hw).elim
  · exact (hnw hw).elim

/-- If the first of four propositions is false and exactly two are true,
exactly two of the remaining three are true. -/
theorem ExactlyTwoOfFour.tail_exactlyTwo {w x y z : Prop}
    (h : ExactlyTwoOfFour w x y z) (hw : ¬w) :
    ExactlyTwoOfThree x y z := by
  rcases h with ⟨hw', _, _, _⟩ | ⟨hw', _, _, _⟩ |
    ⟨hw', _, _, _⟩ | ⟨_, hx, hy, hz⟩ |
    ⟨_, hx, hy, hz⟩ | ⟨_, hx, hy, hz⟩
  · exact (hw hw').elim
  · exact (hw hw').elim
  · exact (hw hw').elim
  · exact Or.inl ⟨hx, hy, hz⟩
  · exact Or.inr (Or.inl ⟨hx, hy, hz⟩)
  · exact Or.inr (Or.inr ⟨hx, hy, hz⟩)

/-- If the first two of four vertices have residual degree one and the last
two have residual degree two, the four vertices form one of the two paths
joining the first pair through the last pair. -/
theorem five_cycle_extension
    {ab ac ad bc bd cd : Prop}
    (ha : ExactlyOneOfThree ab ac ad)
    (hb : ExactlyOneOfThree ab bc bd)
    (hc : ExactlyTwoOfThree ac bc cd)
    (hd : ExactlyTwoOfThree ad bd cd) :
    (ac ∧ cd ∧ bd) ∨ (ad ∧ cd ∧ bc) := by
  rcases ha with ⟨hab, hnac, hnad⟩ |
      ⟨hnab, hac, hnad⟩ | ⟨hnab, hnac, had⟩ <;>
    rcases hb with ⟨hab', hnbc, hnbd⟩ |
      ⟨hnab', hbc, hnbd⟩ | ⟨hnab', hnbc, hbd⟩ <;>
    simp_all [ExactlyTwoOfThree]

/-- A degree-two graph on five labelled vertices contains a cycle through
all five vertices. -/
theorem FiveNeighborCycleCase.cycle_edges
    {pq pr ps pt qr qs qt rs rt st : Prop}
    (h : FiveNeighborCycleCase pq pr ps pt qr qs qt rs rt st) :
    FiveCycleEdges pq pr ps pt qr qs qt rs rt st := by
  rcases h with ⟨hp, hq, hr, hs, ht⟩
  rcases hp with ⟨hpq, hpr, hnps, hnpt⟩ |
      ⟨hpq, hnpr, hps, hnpt⟩ |
      ⟨hpq, hnpr, hnps, hpt⟩ |
      ⟨hnpq, hpr, hps, hnpt⟩ |
      ⟨hnpq, hpr, hnps, hpt⟩ |
      ⟨hnpq, hnpr, hps, hpt⟩
  · have hq' := hq.tail_exactlyOne hpq
    have hr' := hr.tail_exactlyOne hpr
    have hs' := hs.tail_exactlyTwo hnps
    have ht' := ht.tail_exactlyTwo hnpt
    rcases five_cycle_extension hq' hr' hs' ht' with
      ⟨hqs, hst, hrt⟩ | ⟨hqt, hst, hrs⟩ <;>
      unfold FiveCycleEdges <;> aesop
  · have hq' := (hq.tail_exactlyOne hpq).swap12
    have hs' := hs.tail_exactlyOne hps
    have hr' := hr.tail_exactlyTwo hnpr
    have ht' := (ht.tail_exactlyTwo hnpt).swap23
    rcases five_cycle_extension hq' hs' hr' ht' with
      ⟨hqr, hrt, hst⟩ | ⟨hqt, hrt, hrs⟩ <;>
      unfold FiveCycleEdges <;> aesop
  · have hq' := (hq.tail_exactlyOne hpq).swap23.swap12
    have ht' := ht.tail_exactlyOne hpt
    have hr' := (hr.tail_exactlyTwo hnpr).swap23
    have hs' := (hs.tail_exactlyTwo hnps).swap23
    rcases five_cycle_extension hq' ht' hr' hs' with
      ⟨hqr, hrs, hst⟩ | ⟨hqs, hrs, hrt⟩ <;>
      unfold FiveCycleEdges <;> aesop
  · have hr' := (hr.tail_exactlyOne hpr).swap12
    have hs' := (hs.tail_exactlyOne hps).swap12
    have hq' := hq.tail_exactlyTwo hnpq
    have ht' := (ht.tail_exactlyTwo hnpt).swap12.swap23
    rcases five_cycle_extension hr' hs' hq' ht' with
      ⟨hqr, hqt, hst⟩ | ⟨hrt, hqt, hqs⟩ <;>
      unfold FiveCycleEdges <;> aesop
  · have hr' := (hr.tail_exactlyOne hpr).swap23.swap12
    have ht' := (ht.tail_exactlyOne hpt).swap12
    have hq' := (hq.tail_exactlyTwo hnpq).swap23
    have hs' := (hs.tail_exactlyTwo hnps).swap12.swap23
    rcases five_cycle_extension hr' ht' hq' hs' with
      ⟨hqr, hqs, hst⟩ | ⟨hrs, hqs, hqt⟩ <;>
      unfold FiveCycleEdges <;> aesop
  · have hs' := (hs.tail_exactlyOne hps).swap23.swap12
    have ht' := (ht.tail_exactlyOne hpt).swap23.swap12
    have hq' := (hq.tail_exactlyTwo hnpq).swap12.swap23
    have hr' := (hr.tail_exactlyTwo hnpr).swap12.swap23
    rcases five_cycle_extension hs' ht' hq' hr' with
      ⟨hqs, hqr, hrt⟩ | ⟨hrs, hqr, hqt⟩ <;>
      unfold FiveCycleEdges <;> aesop

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
