import FreeFermionGraphs.SetDeformationPath
import FreeFermionGraphs.DeformationClosureRelation
import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.PauliSetSigns
import FreeFermionGraphs.HoleChargeSigns

/-!
# Toggling a cycle and an independent set along an untethered deformation path

This module formalises the cancellation step in the proof of Theorem 1 (ii) of the manuscript
(arXiv 2305.15625 v1, "Generalized Cycle Symmetries and Independent Set Charges", proof at
L908-927): given an *untethered* deformation path `P` of a labelled even hole `C` along an
independent set `S` (`SimpleGraph.EvenHoleLabeling.SetDeformationPath`, Fig.
`deformationsequence`), put `C~ = C ⊕ P` and `S~ = S ⊕ P`.  Write `K = P ∩ C_a`
(the replaced vertices `a_{i_j}`) and `J = P ∩ S` (the deforming vertices `s_j`).

* `SetDeformationPath.final_carrier_eq` (v1 L913: "`C~ = C ⊕ P`", "`C~ ∈ ⟨C₀⟩`"): the carrier
  of the final labelling of the run is `C ⊕ P`; it lies in the deformation closure `⟨C⟩` of `C`
  and the final labelling again has full cyclic order.  The three statements
  `final_carrier_eq_symmDiff`, `inEvenHoleDeformationClosure_final` and
  `hasFullCyclicOrder_final` are proved separately and need no untetheredness and no
  claw-freeness.
* `SetDeformationPath.toggle_configuration` (v1 L913 "`S~ ∈ μ`", via the token-sliding argument
  of the proof of Theorem 1 (i), L895): `S ⊕ P` is independent, has the same size as `S`, and is
  obtained from `S` by token slides (`S ↔_TS S ⊕ P`).  This is the odd-component toggle
  `card_and_tokenSlideReachable_symmDiff` applied to the independent sets `S` and `C_a`,
  because an untethered `P` is a component of `G[S ⊕ C_a]` with `2ℓ - 1` edges
  (`odd_crossCount_support`).
* `SetDeformationPath.toggle_add_eq_zero` (v1 L922-925): `h_C h_S + h_{C~} h_{S~} = 0` and
  `h_S h_C + h_{S~} h_{C~} = 0`, in every `PauliFrustrationRepresentation`.  Here
  `h_C = h_{C_a} h_{C_b}` is `PauliFrustrationRepresentation.labelingOperator`.  With
  `h_{C_a} = h_{C_a ∖ K} h_K`, `h_{C~} = h_{C_a ∖ K} h_J h_{C_b}`, `h_S = h_J h_{S ∖ P}` and
  `h_{S~} = h_K h_{S ∖ P}` the two sums are `h_{C_a ∖ K}(h_K h_J + h_J h_K) h_{C_b} h_{S ∖ P}`
  and `h_{S ∖ P} h_{C_a ∖ K}(h_J h_K + h_K h_J) h_{C_b}` respectively, which vanish because
  `c(J, K) = 2ℓ - 1` is odd.  The `C_b`-class commutes with `h_J` and `h_K` (every `s_j` and
  every `a_{i_j}` has exactly two `C_b`-neighbours, so the cross counts are `2ℓ`).  The
  vertices of `S ∖ P` and of `C_a ∖ K` commute with `h_J` and `h_K` because `P` is a
  component of `G[S ⊕ C_a]` (no cross edges leave it) and `S`, `C_a` are independent.

## Relation to the informal text of the manuscript

* v1 (L922-925) treats only the sum `h_C h_S + h_{C~} h_{S~}`: after using the anticommutation
  of `h_C` and `h_S` (L913-920) to turn both commutators into twice a product, it factorises
  the sum as `h_{C∖P}(h_{C∩P} h_{S∩P} + h_{S∩P} h_{C∩P}) h_{S∖P}`, which is correct.  Here both
  `h_C h_S + h_{C~} h_{S~} = 0` and the mirror sum `h_S h_C + h_{S~} h_{C~} = 0` are proved, so
  that `[h_C, h_S] + [h_{C~}, h_{S~}] = 0` follows without assuming the anticommutation.  In the
  mirror sum `h_{S∖P}` naturally stands to the *left* of `h_{C_a∖K}`; moving `h_{S∖P}` across
  `h_{C∖P} = h_{C_a∖K} h_{C_b}` costs a sign `(-1)^{c(S∖P, C_a∖K) + c(S∖P, C_b)}`, the same in
  both summands, so the proof tracks the order of the factors explicitly.  This is a
  strengthening of the paper's statement, not a correction of it.
* v1 uses `C ∩ P` for the `a`-vertices of the path and calls it a colouring class of `P`;
  `C ∩ P = C_a ∩ P = K` holds because the deforming vertices `s_j` lie outside `C`.
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- If no vertex of `X` is adjacent to a vertex of `Y`, the cross count vanishes. -/
theorem crossCount_eq_zero_of_not_adj {X Y : Finset V}
    (h : ∀ x ∈ X, ∀ y ∈ Y, ¬G.Adj x y) : G.crossCount X Y = 0 := by
  classical
  rw [crossCount_eq_card_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hp
  have := Finset.mem_product.1 hp
  exact h x this.1 y this.2

namespace EvenHoleLabeling

/-! ### The final labelling of a run -/

section Runs

variable {S : Set V} {k : ℕ} {L L' : G.EvenHoleLabeling k} {ps : List (V × Fin k)}

/-- A run of single-vertex deformations leads to a carrier in the deformation closure
`⟨C⟩` of the original carrier (a composite of `EvenHoleDeformationStep`s, each given by
`deform_carrier`). -/
theorem DeformsAlongAt.inEvenHoleDeformationClosure (hrun : L.DeformsAlongAt S ps L') :
    InEvenHoleDeformationClosure G L.carrier L'.carrier := by
  induction hrun with
  | nil L => exact InEvenHoleDeformationClosure.refl _
  | @cons L L' s i rest hs h _ ih =>
      refine InEvenHoleDeformationClosure.trans
        (EvenHoleDeformationStep.inClosure ?_) ih
      exact ⟨k, L, s, i, h, Or.inl ⟨rfl, L.deform_carrier h⟩⟩

/-- A run of single-vertex deformations preserves the full cyclic order. -/
theorem DeformsAlongAt.hasFullCyclicOrder (hrun : L.DeformsAlongAt S ps L')
    (hL : L.HasFullCyclicOrder) : L'.HasFullCyclicOrder := by
  induction hrun with
  | nil L => exact hL
  | @cons L L' s i rest hs h _ ih => exact ih (L.hasFullCyclicOrder_deform h hL)

end Runs

namespace SetDeformationPath

section Sets

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- The deforming vertices `J = {s_j} = P ∩ S` of a deformation path. -/
def cloneSet [DecidableEq V] (P : L.SetDeformationPath S) : Finset V :=
  Finset.univ.image P.s

/-- The replaced vertices `K = {a_{i_j}} = P ∩ C_a` of a deformation path. -/
def replacedSet [DecidableEq V] (P : L.SetDeformationPath S) : Finset V :=
  Finset.univ.image fun j => L.a (P.idx j)

theorem mem_cloneSet [DecidableEq V] (P : L.SetDeformationPath S) {v : V} :
    v ∈ P.cloneSet ↔ ∃ j, P.s j = v := by
  simp [cloneSet]

theorem mem_replacedSet [DecidableEq V] (P : L.SetDeformationPath S) {v : V} :
    v ∈ P.replacedSet ↔ ∃ j, L.a (P.idx j) = v := by
  simp [replacedSet]

theorem support_eq_union [DecidableEq V] (P : L.SetDeformationPath S) :
    P.support = P.cloneSet ∪ P.replacedSet := rfl

theorem cloneSet_subset [DecidableEq V] (P : L.SetDeformationPath S) : P.cloneSet ⊆ S := by
  intro v hv
  obtain ⟨j, rfl⟩ := P.mem_cloneSet.1 hv
  exact P.s_mem j

theorem replacedSet_subset [DecidableEq V] (P : L.SetDeformationPath S) :
    P.replacedSet ⊆ Finset.univ.image L.a := by
  intro v hv
  obtain ⟨j, rfl⟩ := P.mem_replacedSet.1 hv
  exact Finset.mem_image.2 ⟨P.idx j, Finset.mem_univ _, rfl⟩

/-- A deforming vertex `s_j` lies outside the carrier of the original hole. -/
private theorem s_not_mem_carrier [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (j : Fin P.len) : P.s j ∉ L.carrier := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · exact P.s_not_mem_image_a hS j (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
  · obtain ⟨M, hM, hMb⟩ := P.exists_clone j
    exact hM.ne_b_vertex q (by rw [hMb q]; exact hq.symm)

theorem cloneSet_disjoint_image_a [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : Disjoint P.cloneSet (Finset.univ.image L.a) := by
  rw [Finset.disjoint_left]
  intro v hv hva
  obtain ⟨j, rfl⟩ := P.mem_cloneSet.1 hv
  exact P.s_not_mem_image_a hS j hva

theorem cloneSet_disjoint_image_b [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : Disjoint P.cloneSet (Finset.univ.image L.b) := by
  rw [Finset.disjoint_left]
  intro v hv hvb
  obtain ⟨j, rfl⟩ := P.mem_cloneSet.1 hv
  obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hvb
  exact P.s_not_mem_carrier hS j (hq ▸ L.b_mem_carrier q)

/-- `P ∩ S` is the set `J = {s_j}` of deforming vertices (the `a_{i_j}` are not in `S`). -/
theorem inter_support_eq_cloneSet [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : S ∩ P.support = P.cloneSet := by
  ext x
  simp only [Finset.mem_inter, mem_support_iff, mem_cloneSet]
  constructor
  · rintro ⟨hxS, j, hj | hj⟩
    · exact ⟨j, hj⟩
    · exact (P.a_idx_not_mem hS j (hj ▸ hxS)).elim
  · rintro ⟨j, rfl⟩
    exact ⟨P.s_mem j, j, Or.inl rfl⟩

/-- `P ∩ C_a` is the set `K = {a_{i_j}}` of replaced vertices (the `s_j` are not in `C_a`). -/
theorem image_a_inter_support_eq_replacedSet [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) :
    Finset.univ.image L.a ∩ P.support = P.replacedSet := by
  ext x
  simp only [Finset.mem_inter, mem_support_iff, mem_replacedSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨q, hq⟩ , j, hj | hj⟩
    · exact (P.s_not_mem_image_a hS j
        (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hj ▸ hq⟩)).elim
    · exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨P.idx j, rfl⟩, j, Or.inr rfl⟩

/-- `S ⊕ P = K ∪ (S ∖ P)`: toggling the path replaces the deforming vertices `s_j` by the
vertices `a_{i_j}` (v1 L913 and L895: `S~` is obtained from `S` by sliding `s_j` to
`a_{i_j}`). -/
theorem symmDiff_support_eq [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) :
    symmDiff S P.support = P.replacedSet ∪ (S \ P.support) := by
  have hJ := P.inter_support_eq_cloneSet hS
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (h | ⟨hvP, hvS⟩)
    · exact Or.inr h
    · left
      rcases P.mem_support_iff.1 hvP with ⟨j, hj | hj⟩
      · exact (hvS (hj ▸ P.s_mem j)).elim
      · exact P.mem_replacedSet.2 ⟨j, hj⟩
  · rintro (h | h)
    · obtain ⟨j, rfl⟩ := P.mem_replacedSet.1 h
      exact Or.inr ⟨P.a_idx_mem_support j, P.a_idx_not_mem hS j⟩
    · exact Or.inl h

/-- `S = J ∪ (S ∖ P)`. -/
theorem eq_cloneSet_union_sdiff [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : S = P.cloneSet ∪ (S \ P.support) := by
  have hJ := P.inter_support_eq_cloneSet hS
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hv
    by_cases hvP : v ∈ P.support
    · left
      rw [← hJ]
      exact Finset.mem_inter.2 ⟨hv, hvP⟩
    · exact Or.inr ⟨hv, hvP⟩
  · rintro (h | h)
    · exact P.cloneSet_subset h
    · exact h.1

/-- The `a`-class of the final labelling is `(C_a ∖ K) ∪ J`. -/
theorem final_image_a [DecidableEq V] (P : L.SetDeformationPath S) :
    Finset.univ.image P.final.a =
      (Finset.univ.image L.a \ P.replacedSet) ∪ P.cloneSet := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff,
    mem_replacedSet, mem_cloneSet]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hq : ∃ j, P.idx j = q
    · obtain ⟨j, rfl⟩ := hq
      exact Or.inr ⟨j, (P.final_a_idx j).symm⟩
    · push Not at hq
      left
      refine ⟨⟨q, (P.final_a_of_forall_ne hq).symm⟩, ?_⟩
      rintro ⟨j, hj⟩
      rw [P.final_a_of_forall_ne hq] at hj
      exact hq j (L.a_injective hj)
  · rintro (⟨⟨q, rfl⟩, hK⟩ | ⟨j, rfl⟩)
    · refine ⟨q, ?_⟩
      apply P.final_a_of_forall_ne
      intro j hj
      exact hK ⟨j, by rw [hj]⟩
    · exact ⟨P.idx j, P.final_a_idx j⟩

/-- The `b`-class of the final labelling is that of `L`. -/
theorem final_image_b [DecidableEq V] (P : L.SetDeformationPath S) :
    Finset.univ.image P.final.b = Finset.univ.image L.b := by
  have : P.final.b = L.b := funext P.final_b
  rw [this]

end Sets

/-! ### (a) The final carrier -/

section FinalCarrier

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- **The carrier of the final labelling is `C ⊕ P`** (v1 L913, `C~ = C ⊕ P`).  It holds for
every deformation path (tethered or not); it uses only that `S` is independent, so that the
deforming vertices `s_j` lie outside `C`. -/
theorem final_carrier_eq_symmDiff [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) :
    P.final.carrier = symmDiff L.carrier ↑P.support := by
  have hfin : P.final.carrier =
      ((Finset.univ.image P.final.a ∪ Finset.univ.image P.final.b : Finset V) : Set V) :=
    P.final.coe_image_a_union_image_b.symm
  have hL : L.carrier =
      ((Finset.univ.image L.a ∪ Finset.univ.image L.b : Finset V) : Set V) :=
    L.coe_image_a_union_image_b.symm
  rw [hfin, hL, ← Finset.coe_symmDiff]
  congr 1
  rw [P.final_image_a, P.final_image_b]
  have hJa := P.cloneSet_disjoint_image_a hS
  have hJb := P.cloneSet_disjoint_image_b hS
  have hKa := P.replacedSet_subset
  have hab := L.disjoint_image_a_image_b
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, support_eq_union]
  have h1 : ∀ v, v ∈ P.cloneSet → v ∉ Finset.univ.image L.a := fun v hv => by
    exact Finset.disjoint_left.1 hJa hv
  have h2 : ∀ v, v ∈ P.cloneSet → v ∉ Finset.univ.image L.b := fun v hv => by
    exact Finset.disjoint_left.1 hJb hv
  have h3 : ∀ v, v ∈ Finset.univ.image L.a → v ∉ Finset.univ.image L.b := fun v hv => by
    exact Finset.disjoint_left.1 hab hv
  have h4 : ∀ v, v ∈ P.replacedSet → v ∈ Finset.univ.image L.a := fun v hv => hKa hv
  have h1v := h1 v
  have h2v := h2 v
  have h3v := h3 v
  have h4v := h4 v
  tauto

/-- The carrier of the final labelling of a run lies in the deformation closure `⟨C⟩`. -/
theorem inEvenHoleDeformationClosure_final (P : L.SetDeformationPath S) :
    InEvenHoleDeformationClosure G L.carrier P.final.carrier :=
  P.run.inEvenHoleDeformationClosure

/-- The final labelling of a run has full cyclic order if `L` has. -/
theorem hasFullCyclicOrder_final (hL : L.HasFullCyclicOrder) (P : L.SetDeformationPath S) :
    P.final.HasFullCyclicOrder :=
  P.run.hasFullCyclicOrder hL

/-- **Part (a) of the toggle lemma** (v1 L913: "`C~ = C ⊕ P`", "`C~ ∈ ⟨C₀⟩`").  For a
deformation path `P` of the full-cyclic labelling `L` along an independent set `S`, the
carrier of the final labelling is `C ⊕ P`, it lies in the deformation closure of `C`, and the
final labelling again has full cyclic order (so `C ⊕ P` is an even hole).

The hypotheses `hclaw` and `hP` are not needed for these conclusions (they hold for tethered
paths as well); they are kept so that the statement has the same shape as
`toggle_configuration` and `toggle_add_eq_zero`. -/
theorem final_carrier_eq [DecidableEq V] (_hclaw : G.IsClawFree) {L : G.EvenHoleLabeling k}
    (hL : L.HasFullCyclicOrder) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) (_hP : P.Untethered) :
    P.final.carrier = symmDiff L.carrier ↑P.support ∧
      InEvenHoleDeformationClosure G L.carrier P.final.carrier ∧ P.final.HasFullCyclicOrder :=
  ⟨P.final_carrier_eq_symmDiff hS, P.inEvenHoleDeformationClosure_final,
    P.hasFullCyclicOrder_final hL⟩

end FinalCarrier

/-! ### (b) The toggled independent set -/

section ToggledSet

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- **Part (b) of the toggle lemma** (v1 L913, "`S~ ∈ μ`"; L895 for the mechanism).
If `P` is an untethered deformation path of `L` along the independent set `S`, then
`S ⊕ P` is independent, has the same size as `S`, and is reached from `S` by token slides.

Indeed an untethered `P` is a component of `G[S ⊕ C_a]` (`Untethered`), and it has `2ℓ - 1`
edges between `S ∩ P` and `C_a ∩ P` (`odd_crossCount_support`), so this is
`card_and_tokenSlideReachable_symmDiff` for the independent sets `S` and `C_a`.  The
hypothesis `hL` is not needed. -/
theorem toggle_configuration [DecidableEq V] (hclaw : G.IsClawFree) {k : ℕ}
    {L : G.EvenHoleLabeling k} (_hL : L.HasFullCyclicOrder) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) (hP : P.Untethered) :
    G.IsIndepSet ↑(symmDiff S P.support) ∧ (symmDiff S P.support).card = S.card ∧
      G.TokenSlideReachable ↑S ↑(symmDiff S P.support) := by
  have hSa := L.isIndepSet_image_a
  obtain ⟨hcard, hreach⟩ :=
    card_and_tokenSlideReachable_symmDiff hclaw hS hSa hP (P.odd_crossCount_support hclaw hS)
  exact ⟨isIndepSet_symmDiff_of_isInducedComponent hS hSa hP, hcard, hreach⟩

end ToggledSet

/-! ### (c) Cancellation of `h_C h_S` against `h_{C~} h_{S~}` -/

section Cancellation

variable {k : ℕ} {L : G.EvenHoleLabeling k} {S : Finset V}

/-- A clone `s ≺_M a_i` has exactly two neighbours `b_i`, `b_{next i}` in the `b`-class. -/
theorem _root_.SimpleGraph.EvenHoleLabeling.CloneAt.card_filter_image_b [DecidableEq V]
    [DecidableRel G.Adj] {M : G.EvenHoleLabeling k} {s : V} {i : Fin k} (h : M.CloneAt s i) :
    ((Finset.univ.image M.b).filter (G.Adj s)).card = 2 := by
  have hset : (Finset.univ.image M.b).filter (G.Adj s) = {M.b i, M.b (M.next i)} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      rcases (h.adj_iff (M.b j) (M.b_mem_carrier j)).1 hadj with he | ha
      · exact (M.color_disjoint i j he.symm).elim
      · rcases (M.adj_ab_iff i j).1 ha with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨i, rfl⟩, h.adj_b⟩
      · exact ⟨⟨_, rfl⟩, h.adj_b_next⟩
  rw [hset, Finset.card_pair]
  exact fun e => M.next_ne i (M.b_injective e).symm

/-- The vertex `a_i` has exactly two neighbours `b_i`, `b_{next i}` in the `b`-class. -/
theorem _root_.SimpleGraph.EvenHoleLabeling.card_filter_image_b_a [DecidableEq V]
    [DecidableRel G.Adj] (M : G.EvenHoleLabeling k) (i : Fin k) :
    ((Finset.univ.image M.b).filter (G.Adj (M.a i))).card = 2 := by
  have hset : (Finset.univ.image M.b).filter (G.Adj (M.a i)) = {M.b i, M.b (M.next i)} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      rcases (M.adj_ab_iff i j).1 hadj with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨i, rfl⟩, M.adj_a_b i⟩
      · exact ⟨⟨_, rfl⟩, M.adj_a_b_next i⟩
  rw [hset, Finset.card_pair]
  exact fun e => M.next_ne i (M.b_injective e).symm

/-- Every deforming vertex `s_j` has exactly two neighbours in the `b`-class of `C`
(it is a clone of `a_{i_j}` in an intermediate hole with the same `b`-vertices), so the
number of edges between `C_b` and `J = P ∩ S` is `2ℓ`, in particular even. -/
theorem even_crossCount_image_b_cloneSet [DecidableEq V] (P : L.SetDeformationPath S) :
    Even (G.crossCount (Finset.univ.image L.b) P.cloneSet) := by
  classical
  have hcard : ∀ s ∈ P.cloneSet, ((Finset.univ.image L.b).filter (G.Adj s)).card = 2 := by
    intro s hs
    obtain ⟨j, rfl⟩ := P.mem_cloneSet.1 hs
    obtain ⟨M, hM, hMb⟩ := P.exists_clone j
    have : M.b = L.b := funext hMb
    rw [← this]
    exact hM.card_filter_image_b
  rw [crossCount_comm, crossCount_eq_sum_card_filter, Finset.sum_congr rfl hcard,
    Finset.sum_const, smul_eq_mul]
  exact ⟨P.cloneSet.card, by ring⟩

/-- Every replaced vertex `a_{i_j}` has exactly two neighbours in the `b`-class of `C`, so the
number of edges between `C_b` and `K = P ∩ C_a` is `2ℓ`, in particular even. -/
theorem even_crossCount_image_b_replacedSet [DecidableEq V] (P : L.SetDeformationPath S) :
    Even (G.crossCount (Finset.univ.image L.b) P.replacedSet) := by
  classical
  have hcard : ∀ s ∈ P.replacedSet, ((Finset.univ.image L.b).filter (G.Adj s)).card = 2 := by
    intro s hs
    obtain ⟨j, rfl⟩ := P.mem_replacedSet.1 hs
    exact L.card_filter_image_b_a (P.idx j)
  rw [crossCount_comm, crossCount_eq_sum_card_filter, Finset.sum_congr rfl hcard,
    Finset.sum_const, smul_eq_mul]
  exact ⟨P.replacedSet.card, by ring⟩

/-- A vertex of `S ⊕ C_a` adjacent to the path of an untethered deformation path lies on it
(`P` is a component of `G[S ⊕ C_a]`). -/
theorem mem_support_of_adj [DecidableEq V] {P : L.SetDeformationPath S} (hP : P.Untethered)
    {x y : V} (hy : y ∈ P.support) (hx : x ∈ symmDiff S (Finset.univ.image L.a))
    (hadj : G.Adj y x) : x ∈ P.support :=
  Finset.mem_coe.1 (hP.2.2 (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hx) hadj)

/-- No vertex of `S ∖ P` is adjacent to a vertex of `J = P ∩ S` (independence of `S`). -/
theorem crossCount_sdiff_cloneSet [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : G.crossCount (S \ P.support) P.cloneSet = 0 := by
  refine crossCount_eq_zero_of_not_adj fun x hx y hy hadj => ?_
  exact hS (Finset.mem_coe.2 (Finset.mem_sdiff.1 hx).1)
    (Finset.mem_coe.2 (P.cloneSet_subset hy)) hadj.ne hadj

/-- No vertex of `S ∖ P` is adjacent to a vertex of `K = P ∩ C_a`, because `P` is a component
of `G[S ⊕ C_a]` and `C_a` is independent. -/
theorem crossCount_sdiff_replacedSet [DecidableEq V]
    {P : L.SetDeformationPath S} (hP : P.Untethered) :
    G.crossCount (S \ P.support) P.replacedSet = 0 := by
  refine crossCount_eq_zero_of_not_adj fun x hx y hy hadj => ?_
  obtain ⟨hxS, hxP⟩ := Finset.mem_sdiff.1 hx
  by_cases hxA : x ∈ Finset.univ.image L.a
  · exact L.isIndepSet_image_a (Finset.mem_coe.2 hxA)
      (Finset.mem_coe.2 (P.replacedSet_subset hy)) hadj.ne hadj
  · refine hxP (mem_support_of_adj hP ?_ ?_ hadj.symm)
    · rw [support_eq_union]
      exact Finset.mem_union_right _ hy
    · exact Finset.mem_symmDiff.2 (Or.inl ⟨hxS, hxA⟩)

/-- No vertex of `C_a ∖ K` is adjacent to a vertex of `J = P ∩ S`, because `P` is a component
of `G[S ⊕ C_a]` and `S` is independent. -/
theorem crossCount_sdiff_image_a_cloneSet [DecidableEq V] (hS : G.IsIndepSet (S : Set V))
    {P : L.SetDeformationPath S} (hP : P.Untethered) :
    G.crossCount (Finset.univ.image L.a \ P.replacedSet) P.cloneSet = 0 := by
  refine crossCount_eq_zero_of_not_adj fun x hx y hy hadj => ?_
  obtain ⟨hxA, hxK⟩ := Finset.mem_sdiff.1 hx
  by_cases hxS : x ∈ S
  · exact hS (Finset.mem_coe.2 hxS) (Finset.mem_coe.2 (P.cloneSet_subset hy)) hadj.ne hadj
  · have hxP : x ∈ P.support :=
      mem_support_of_adj hP (by rw [support_eq_union]; exact Finset.mem_union_left _ hy)
        (Finset.mem_symmDiff.2 (Or.inr ⟨hxA, hxS⟩)) hadj.symm
    apply hxK
    rw [← P.image_a_inter_support_eq_replacedSet hS]
    exact Finset.mem_inter.2 ⟨hxA, hxP⟩

/-- The two sides of the path, `J = P ∩ S` and `K = P ∩ C_a`, are joined by `2ℓ - 1` edges, an
odd number (v1 L926: "`S ∩ P` and `C ∩ P` are the colouring classes of a path of odd
length"). -/
theorem odd_crossCount_replacedSet_cloneSet [DecidableEq V] (hclaw : G.IsClawFree)
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) :
    Odd (G.crossCount P.replacedSet P.cloneSet) := by
  have h := P.odd_crossCount_support hclaw hS
  rw [P.inter_support_eq_cloneSet hS, P.image_a_inter_support_eq_replacedSet hS] at h
  rwa [crossCount_comm] at h

/-- The purely algebraic identity behind the cancellation: `a = h_J`, `k = h_K` anticommute,
and `z = h_{C_b}` commutes with both, while `x = h_{S ∖ P}` and `y = h_{C_a ∖ K}` commute with
both as well. -/
theorem toggle_algebra {A : Type w} [Ring A] (x y z a k : A)
    (hza : z * a = a * z) (hzk : z * k = k * z)
    (hxa : x * a = a * x) (hxk : x * k = k * x)
    (hya : y * a = a * y) (hyk : y * k = k * y)
    (hka : k * a = -(a * k)) :
    y * k * z * (a * x) + y * a * z * (k * x) = 0 ∧
      a * x * (y * k * z) + k * x * (y * a * z) = 0 := by
  constructor
  · have e1 : y * k * z * (a * x) = y * (k * a) * z * x := by
      calc y * k * z * (a * x) = y * k * (z * a) * x := by simp only [mul_assoc]
        _ = y * k * (a * z) * x := by rw [hza]
        _ = y * (k * a) * z * x := by simp only [mul_assoc]
    have e2 : y * a * z * (k * x) = y * (a * k) * z * x := by
      calc y * a * z * (k * x) = y * a * (z * k) * x := by simp only [mul_assoc]
        _ = y * a * (k * z) * x := by rw [hzk]
        _ = y * (a * k) * z * x := by simp only [mul_assoc]
    rw [e1, e2, hka]
    simp
  · have e1 : a * x * (y * k * z) = x * y * (a * k) * z := by
      calc a * x * (y * k * z) = (a * x) * y * k * z := by simp only [mul_assoc]
        _ = (x * a) * y * k * z := by rw [← hxa]
        _ = x * (a * y) * k * z := by simp only [mul_assoc]
        _ = x * (y * a) * k * z := by rw [← hya]
        _ = x * y * (a * k) * z := by simp only [mul_assoc]
    have e2 : k * x * (y * a * z) = x * y * (k * a) * z := by
      calc k * x * (y * a * z) = (k * x) * y * a * z := by simp only [mul_assoc]
        _ = (x * k) * y * a * z := by rw [← hxk]
        _ = x * (k * y) * a * z := by simp only [mul_assoc]
        _ = x * (y * k) * a * z := by rw [← hyk]
        _ = x * y * (k * a) * z := by simp only [mul_assoc]
    rw [e1, e2, hka]
    simp

/-- **Part (c) of the toggle lemma: cancellation** (v1 L922-925).  For an untethered
deformation path `P` of the full-cyclic labelling `L` along the independent set `S`, with
`C~ = C ⊕ P` (the final labelling) and `S~ = S ⊕ P`,
`h_C h_S + h_{C~} h_{S~} = 0` and `h_S h_C + h_{S~} h_{C~} = 0`,
where `h_C = h_{C_a} h_{C_b}` is `labelingOperator`.

With `K = P ∩ C_a`, `J = P ∩ S`: `h_C = h_{C_a ∖ K} h_K h_{C_b}`,
`h_{C~} = h_{C_a ∖ K} h_J h_{C_b}`, `h_S = h_J h_{S ∖ P}`, `h_{S~} = h_K h_{S ∖ P}`.  The first
sum is `h_{C_a ∖ K}(h_K h_J + h_J h_K) h_{C_b} h_{S ∖ P}` and the second is
`h_{S ∖ P} h_{C_a ∖ K}(h_J h_K + h_K h_J) h_{C_b}`, both zero since `h_J`, `h_K` anticommute
(`c(J, K) = 2ℓ - 1` is odd) and commute with the other factors.  The hypothesis `hL` is not
needed. -/
theorem toggle_add_eq_zero [DecidableEq V] {A : Type w} [Ring A]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {k : ℕ}
    {L : G.EvenHoleLabeling k} (_hL : L.HasFullCyclicOrder) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S) (hP : P.Untethered) :
    H.labelingOperator L * H.independentProduct S +
        H.labelingOperator P.final * H.independentProduct (symmDiff S P.support) = 0 ∧
      H.independentProduct S * H.labelingOperator L +
        H.independentProduct (symmDiff S P.support) * H.labelingOperator P.final = 0 := by
  have hSa := L.isIndepSet_image_a
  have hSb := L.isIndepSet_image_b
  have hJ : G.IsIndepSet (P.cloneSet : Set V) := hS.finset_subset P.cloneSet_subset
  have hK : G.IsIndepSet (P.replacedSet : Set V) := hSa.finset_subset P.replacedSet_subset
  have hX : G.IsIndepSet ((S \ P.support : Finset V) : Set V) :=
    hS.finset_subset Finset.sdiff_subset
  have hY : G.IsIndepSet ((Finset.univ.image L.a \ P.replacedSet : Finset V) : Set V) :=
    hSa.finset_subset Finset.sdiff_subset
  have hStil : G.IsIndepSet ((symmDiff S P.support : Finset V) : Set V) := by
    have := isIndepSet_symmDiff_of_isInducedComponent hS hSa hP
    exact this
  -- decompositions of the four products
  have e1 : H.independentProduct (Finset.univ.image L.a) =
      H.independentProduct (Finset.univ.image L.a \ P.replacedSet) *
        H.independentProduct P.replacedSet := by
    have h := H.independentProduct_union (S := Finset.univ.image L.a \ P.replacedSet)
      (T := P.replacedSet) Finset.sdiff_disjoint
      (by rwa [Finset.sdiff_union_of_subset P.replacedSet_subset])
    rwa [Finset.sdiff_union_of_subset P.replacedSet_subset] at h
  have e2 : H.independentProduct (Finset.univ.image P.final.a) =
      H.independentProduct (Finset.univ.image L.a \ P.replacedSet) *
        H.independentProduct P.cloneSet := by
    have hdisj : Disjoint (Finset.univ.image L.a \ P.replacedSet) P.cloneSet :=
      (P.cloneSet_disjoint_image_a hS).symm.mono_left Finset.sdiff_subset
    have hind : G.IsIndepSet
        (((Finset.univ.image L.a \ P.replacedSet) ∪ P.cloneSet : Finset V) : Set V) := by
      rw [← P.final_image_a]
      exact P.final.isIndepSet_image_a
    rw [P.final_image_a]
    exact H.independentProduct_union hdisj hind
  have e3 : H.independentProduct S =
      H.independentProduct P.cloneSet * H.independentProduct (S \ P.support) := by
    have hdisj : Disjoint P.cloneSet (S \ P.support) := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      exact (Finset.mem_sdiff.1 hv').2 (by rw [support_eq_union]; exact Finset.mem_union_left _ hv)
    have h := H.independentProduct_union hdisj
      (by rw [← P.eq_cloneSet_union_sdiff hS]; exact hS)
    rwa [← P.eq_cloneSet_union_sdiff hS] at h
  have e4 : H.independentProduct (symmDiff S P.support) =
      H.independentProduct P.replacedSet * H.independentProduct (S \ P.support) := by
    have hdisj : Disjoint P.replacedSet (S \ P.support) := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      exact (Finset.mem_sdiff.1 hv').2
        (by rw [support_eq_union]; exact Finset.mem_union_right _ hv)
    rw [P.symmDiff_support_eq hS]
    refine H.independentProduct_union hdisj ?_
    rw [← P.symmDiff_support_eq hS]
    exact hStil
  have hC : H.labelingOperator L =
      H.independentProduct (Finset.univ.image L.a \ P.replacedSet) *
        H.independentProduct P.replacedSet * H.independentProduct (Finset.univ.image L.b) := by
    unfold PauliFrustrationRepresentation.labelingOperator
    rw [e1]
  have hC' : H.labelingOperator P.final =
      H.independentProduct (Finset.univ.image L.a \ P.replacedSet) *
        H.independentProduct P.cloneSet * H.independentProduct (Finset.univ.image L.b) := by
    unfold PauliFrustrationRepresentation.labelingOperator
    rw [e2, P.final_image_b]
  -- commutation relations
  have hza : H.independentProduct (Finset.univ.image L.b) * H.independentProduct P.cloneSet =
      H.independentProduct P.cloneSet * H.independentProduct (Finset.univ.image L.b) :=
    H.independentProduct_mul_independentProduct_of_even hSb hJ
      (even_crossCount_image_b_cloneSet P)
  have hzk : H.independentProduct (Finset.univ.image L.b) * H.independentProduct P.replacedSet =
      H.independentProduct P.replacedSet * H.independentProduct (Finset.univ.image L.b) :=
    H.independentProduct_mul_independentProduct_of_even hSb hK
      (even_crossCount_image_b_replacedSet P)
  have hxa : H.independentProduct (S \ P.support) * H.independentProduct P.cloneSet =
      H.independentProduct P.cloneSet * H.independentProduct (S \ P.support) :=
    H.independentProduct_mul_independentProduct_of_even hX hJ
      (by rw [crossCount_sdiff_cloneSet hS P]; exact ⟨0, rfl⟩)
  have hxk : H.independentProduct (S \ P.support) * H.independentProduct P.replacedSet =
      H.independentProduct P.replacedSet * H.independentProduct (S \ P.support) :=
    H.independentProduct_mul_independentProduct_of_even hX hK
      (by rw [crossCount_sdiff_replacedSet hP]; exact ⟨0, rfl⟩)
  have hya : H.independentProduct (Finset.univ.image L.a \ P.replacedSet) *
        H.independentProduct P.cloneSet =
      H.independentProduct P.cloneSet *
        H.independentProduct (Finset.univ.image L.a \ P.replacedSet) :=
    H.independentProduct_mul_independentProduct_of_even hY hJ
      (by rw [crossCount_sdiff_image_a_cloneSet hS hP]; exact ⟨0, rfl⟩)
  have hyk : H.independentProduct (Finset.univ.image L.a \ P.replacedSet) *
        H.independentProduct P.replacedSet =
      H.independentProduct P.replacedSet *
        H.independentProduct (Finset.univ.image L.a \ P.replacedSet) :=
    H.independentProduct_mul_independentProduct_of_even hY hK
      (by
        rw [crossCount_eq_zero_of_not_adj]
        · exact ⟨0, rfl⟩
        · intro x hx y hy hadj
          exact L.isIndepSet_image_a (Finset.mem_coe.2 (Finset.mem_sdiff.1 hx).1)
            (Finset.mem_coe.2 (P.replacedSet_subset hy)) hadj.ne hadj)
  have hka : H.independentProduct P.replacedSet * H.independentProduct P.cloneSet =
      -(H.independentProduct P.cloneSet * H.independentProduct P.replacedSet) :=
    H.independentProduct_mul_independentProduct_of_odd hK hJ
      (P.odd_crossCount_replacedSet_cloneSet hclaw hS)
  rw [hC, hC', e3, e4]
  exact toggle_algebra _ _ _ _ _ hza hzk hxa hxk hya hyk hka

end Cancellation

end SetDeformationPath

end EvenHoleLabeling

end SimpleGraph
