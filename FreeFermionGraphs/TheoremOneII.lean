import FreeFermionGraphs.SetDeformationTether
import FreeFermionGraphs.ToggleCycleCharge
import FreeFermionGraphs.TheoremOneI

/-!
# Theorem 1 (ii): `[J_{C₀}, q_{s,μ}] = 0`, and the conservation of `J_{C₀}`

This module proves part (ii) of the Conserved Charges theorem of the manuscript
(arXiv 2305.15625 v1, `theorem:conservedcharges` (ii), L864-871, proof L904-927), together with the
corresponding part of its last sentence ("in particular, these operators are conserved charges of
the Hamiltonian"), for the generalized cycle symmetries.

* `PauliFrustrationRepresentation.paperTheorem1ii`: for a Hamiltonian representation `H` of a
  claw-free (finite) frustration graph `G`, an even hole `C₀`, `s : ℕ` and `μ ∈ Ξ_s`,
  `[J_{C₀}, q_{s,μ}] = 0`.  The only hypotheses are the setup of the manuscript (the representation
  `H`, finiteness of `V`), claw-freeness, and `C₀` being an even hole (v1 defines `J_{C₀}` only for
  even holes).  The ring `A` is arbitrary, so the statement is more general than v1's (Pauli
  strings), and no invertibility of `2` is used: the cancellation is a pairing of terms, not a
  division.
* `PauliFrustrationRepresentation.hamiltonian_commute_generalizedCycleSymmetryOp`: `[H, J_{C₀}] = 0`
  (`s = 1`, `Q^(1) = H`).
* `SimpleGraph.untetheredSupports` and `SimpleGraph.untetheredSupports_toggle`: the set `𝒫(C, S)` of
  supports of untethered runs of `(C, S)`, over all full-cyclic labellings of `C` (both colour
  classes), is stable under the toggle: `𝒫(C ⊕ Q, S ⊕ Q) = 𝒫(C, S)` for `Q ∈ 𝒫(C, S)`.

## The proof, and what v1 leaves open

v1 expands `[J_{C₀}, q_{s,μ}] = Σ_{C ∈ ⟨C₀⟩, S ∈ μ} [h_C, h_S]` (L904).  If `h_C` and `h_S`
anticommute there is an untethered deformation path `P` of `C` along `S`
(`EvenHoleLabeling.exists_untethered_of_odd`, from the tether involution of
`FreeFermionGraphs.SetDeformationTether`), and with `C~ = C ⊕ P`, `S~ = S ⊕ P` one has
`h_C h_S + h_{C~} h_{S~} = 0` and the mirror identity
(`EvenHoleLabeling.SetDeformationPath.toggle_add_eq_zero`, from
`FreeFermionGraphs.ToggleCycleCharge`).  v1 concludes (L926-927) "for a collection of terms related
by a fixed set of untethered paths, we fix a path by which corresponding terms are paired".  For
this to cancel the sum, the chosen path of `(C~, S~)` must be the same path `P` again, i.e. the set
of untethered paths must not change under the toggle.  v1 does not argue this.  Here:

* `𝒫(C, S)` consists of the supports of untethered runs along both colour classes of `C`, i.e. of
  the runs of every full-cyclic labelling of `C` (`mem_untetheredSupports`).  An untethered run of
  the `a`-class and one of the `b`-class are both candidates: an anticommuting vertex of `S` is a
  clone of an `a`-vertex or of a `b`-vertex.
* *Same class* (`EvenHoleLabeling.SetDeformationPath.exists_toggle_path_same_class`): another
  untethered component `P'` of `G[S ⊕ C_a]` is disjoint from `P`, and `(S ⊕ P) ⊕ C~_a = S ⊕ C_a`
  (`symmDiff_symmDiff_final_image_a`), so `P'` is again an untethered path of the toggled hole.
* *The path itself*, read from the other end (`exists_reverse_untethered`): `P` is untethered for
  `(C~, S~)`, starting from `a_{i_{ℓ-1}}`, a clone of `s_{ℓ-1}` in `C~`, and replacing
  `s_{ℓ-1}, …, s_0` by `a_{i_{ℓ-1}}, …, a_{i_0}`.
* *Cross class*, the claim v1 does not make (`exists_toggle_path_other_class`): an untethered run
  `P'` of the `b`-class never contains a deforming vertex `s_j` of `P`
  (`cloneSet_disjoint_support_of_other_class`: `s_j ∈ P'` forces `s_{j-1} ∈ P'` through a common
  `b`-neighbour, hence `s_0 ∈ P'`, but `s_0` has one neighbour in `C_a` and every vertex of `P' ∩ S`
  has two), and the toggle only exchanges the twins `s_j`, `a_{i_j}`, which have the same neighbours
  in `C_b`; so `P'` is again a component of `G[(S ⊕ P) ⊕ C_b]`
  (`isInducedComponent_symmDiff_toggle`) and an untethered path of the colour-swapped toggled hole.

All new runs are built with `EvenHoleLabeling.SetDeformationPath.exists_support_eq_of_conditions`,
the form of `exists_deformsAlongAt_of_conditions` that produces a `SetDeformationPath` from
adjacency conditions alone.  With `chosenUntethered` (a choice function applied to the finite set
`𝒫(C, S)`) the toggle `cycleChargeToggle` is a fixed-point-free involution on the pairs `(C, S)`
with `𝒫(C, S) ≠ ∅`, and `Finset.sum_involution` finishes the proof.  Pairs with `𝒫(C, S) = ∅`
have `|A(C, S)|` even (`exists_untethered_of_odd`), so `h_C` and `h_S` commute
(`labelingOperator_mul_independentProduct`) and the term is zero.

## Remarks

* The hypothesis `hC : G.IsEvenHoleCarrier C` of `untetheredSupports_toggle` is redundant: an
  element of `𝒫(C, S)` already presents `C` as the carrier of a full-cyclic labelling.  The
  general form is `untetheredSupports_toggle_of_mem`.
* v1 numbering: v1 Lemma 3 is repo Lemma 8 (`CloneAt.lemma8`), used through the existence of runs
  (`CloneAt.exists_setDeformationPath`); v1 Corollary 1 is repo Corollary 2.
-/

open scoped symmDiff BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

namespace SetDeformationPath

/-! ### Building a deformation path from adjacency conditions -/

section FromConditions

variable [DecidableEq V] {S : Finset V} {k : ℕ}

/-- **A deformation path from adjacency conditions.**  Let `x₀, …, x_{ℓ-1}` be vertices of the
independent set `S` and `r₀, …, r_{ℓ-1}` distinct indices of the labelling `M` such that every
`x_m` lies outside `M`, has the `b`-neighbours of `a_{r_m}` and is adjacent to `a_{r_m}`, the only
`a`-vertices of `M` adjacent to `x_m` are among the `a_{r_{m'}}`, an earlier `x_m` is not adjacent
to a later `a_{r_{m'}}`, and `x_{m+1} ~ a_{r_m}`.  Then there is a deformation path of `M` along `S`
with support `{x_m} ∪ {a_{r_m}}`.  (Carrier-level description of a path; it is the form of
`exists_deformsAlongAt_of_conditions` that produces a `SetDeformationPath`.) -/
theorem exists_support_eq_of_conditions (hS : G.IsIndepSet (S : Set V)) (M : G.EvenHoleLabeling k)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (x : Fin ℓ → V) (r : Fin ℓ → Fin k)
    (hx : Function.Injective x) (hr : Function.Injective r) (hxS : ∀ m, x m ∈ S)
    (hout : ∀ m, x m ∉ M.carrier)
    (hb : ∀ m q, G.Adj (x m) (M.b q) ↔ G.Adj (M.a (r m)) (M.b q))
    (hadj : ∀ m, G.Adj (x m) (M.a (r m)))
    (ha : ∀ m q, G.Adj (x m) (M.a q) → ∃ m', r m' = q)
    (hpw : ∀ m m' : Fin ℓ, m < m' → ¬G.Adj (x m) (M.a (r m')))
    (hlink : ∀ m m' : Fin ℓ, m.val + 1 = m'.val → G.Adj (x m') (M.a (r m))) :
    ∃ P : M.SetDeformationPath S,
      P.support = Finset.univ.image x ∪ Finset.univ.image (fun m => M.a (r m)) := by
  obtain ⟨final, hrun⟩ := exists_deformsAlongAt_of_conditions (S := (↑S : Set V)) hS
    (List.ofFn fun m : Fin ℓ => (x m, r m)) M
    (by
      intro p hp
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      exact Finset.mem_coe.2 (hxS m))
    (by simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.2 hx)
    (by simpa [List.map_ofFn, Function.comp_def] using List.nodup_ofFn.2 hr)
    (by
      intro p hp
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      exact hout m)
    (by
      intro p hp q
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      exact hb m q)
    (by
      intro p hp
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      exact hadj m)
    (by
      intro p hp q hq
      obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hp
      obtain ⟨m', hm'⟩ := ha m q hq
      exact List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨m', rfl⟩, hm'⟩)
    (by
      rw [List.pairwise_ofFn]
      exact fun m m' hmm' => hpw m m' hmm')
  exact ⟨{ len := ℓ, len_pos := hℓ, s := x, idx := r, s_mem := hxS, s_injective := hx,
            idx_injective := hr, final := final, run := hrun, link := fun j j' h => hlink j j' h },
    rfl⟩

end FromConditions

/-! ### Local facts about the vertices of a deformation path -/

section Local

variable [DecidableEq V] {S : Finset V} {k : ℕ} {L : G.EvenHoleLabeling k}

omit [DecidableEq V] in
/-- `s_j` and `a_{i_j}` have the same neighbours in the `b`-class of `L`: `b_{i_j}` and
`b_{next i_j}`. -/
theorem adj_s_iff_adj_a_b (P : L.SetDeformationPath S) (j : Fin P.len) (q : Fin k) :
    G.Adj (P.s j) (L.b q) ↔ G.Adj (L.a (P.idx j)) (L.b q) := by
  rw [P.adj_s_b_iff j q, L.adj_ab_iff]

omit [DecidableEq V] in
/-- The same as `adj_s_iff_adj_a_b` for an arbitrary vertex of the `b`-class. -/
theorem adj_s_iff_adj_a_of_mem_range_b (P : L.SetDeformationPath S) (j : Fin P.len) {y : V}
    (hy : y ∈ Set.range L.b) : G.Adj (P.s j) y ↔ G.Adj (L.a (P.idx j)) y := by
  obtain ⟨q, rfl⟩ := hy
  exact P.adj_s_iff_adj_a_b j q

/-- **Toggling an untethered path leaves `S ⊕ C_a` unchanged**: the `a`-class of the final
labelling is `(C_a ∖ K) ∪ J` and `S ⊕ P = (S ∖ J) ∪ K`, so
`(S ⊕ P) ⊕ C~_a = S ⊕ C_a`. -/
theorem symmDiff_symmDiff_final_image_a (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) :
    symmDiff (symmDiff S P.support) (Finset.univ.image P.final.a) =
      symmDiff S (Finset.univ.image L.a) := by
  have hJS : ∀ v, v ∈ P.cloneSet → v ∈ S := fun v hv => P.cloneSet_subset hv
  have hJA : ∀ v, v ∈ P.cloneSet → v ∉ Finset.univ.image L.a := fun v hv =>
    Finset.disjoint_left.1 (P.cloneSet_disjoint_image_a hS) hv
  have hKA : ∀ v, v ∈ P.replacedSet → v ∈ Finset.univ.image L.a := fun v hv =>
    P.replacedSet_subset hv
  have hKS : ∀ v, v ∈ P.replacedSet → v ∉ S := fun v hv => by
    obtain ⟨j, rfl⟩ := P.mem_replacedSet.1 hv
    exact P.a_idx_not_mem hS j
  ext v
  have h1 := hJS v
  have h2 := hJA v
  have h3 := hKA v
  have h4 := hKS v
  simp only [Finset.mem_symmDiff, P.final_image_a, Finset.mem_union, Finset.mem_sdiff,
    support_eq_union]
  tauto

end Local

/-! ### The reverse run of an untethered path in the toggled pair -/

section Reverse

variable [DecidableEq V] {S : Finset V} {k : ℕ} {L : G.EvenHoleLabeling k}

/-- **The reverse run.**  If `P` is an untethered deformation path of `L` along the independent set
`S`, then in the toggled pair `(C ⊕ P, S ⊕ P)` (final labelling `P.final`, set `S ⊕ P`) the same
vertex set `P` is again an untethered deformation path: starting from `a_{i_{ℓ-1}}`, a clone of
`s_{ℓ-1}` in `C ⊕ P`, one replaces `s_{ℓ-1}, …, s_0` by `a_{i_{ℓ-1}}, …, a_{i_0}` (v1 L913 and the
remark "`P` itself is untethered for the toggled pair, read from `a_{ℓ-1}`" of the proof of
Theorem 1 (ii); v1 does not discuss it).

The run is built by `exists_support_eq_of_conditions`: the vertex `a_{i_j}` has the `b`-neighbours
of `s_j` (`adj_s_iff_adj_a_b`), is adjacent to `s_j`, to no other `a`-vertex of the final hole
(the only `a`-vertices adjacent to a vertex of `S ⊕ P` are the `s_m`), and `a_{i_j} ≁ s_{j'}` for
`j' < j` (`adj_s_a_iff`). -/
theorem exists_reverse_untethered (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (hP : P.Untethered)
    (hS' : G.IsIndepSet ((symmDiff S P.support : Finset V) : Set V)) :
    ∃ P'' : P.final.SetDeformationPath (symmDiff S P.support),
      P''.Untethered ∧ P''.support = P.support := by
  have hsupp : Finset.univ.image (fun m : Fin P.len => L.a (P.idx (Fin.rev m))) ∪
      Finset.univ.image (fun m : Fin P.len => P.final.a (P.idx (Fin.rev m))) = P.support := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      P.final_a_idx, P.mem_support_iff]
    constructor
    · rintro (⟨m, rfl⟩ | ⟨m, rfl⟩)
      · exact ⟨Fin.rev m, Or.inr rfl⟩
      · exact ⟨Fin.rev m, Or.inl rfl⟩
    · rintro ⟨j, rfl | rfl⟩
      · exact Or.inr ⟨Fin.rev j, by rw [Fin.rev_rev]⟩
      · exact Or.inl ⟨Fin.rev j, by rw [Fin.rev_rev]⟩
  obtain ⟨P'', hP''⟩ := exists_support_eq_of_conditions (S := symmDiff S P.support) hS'
    P.final P.len_pos (fun m => L.a (P.idx (Fin.rev m))) (fun m => P.idx (Fin.rev m))
    (fun m m' h => Fin.rev_injective (P.idx_injective (L.a_injective h)))
    (fun m m' h => Fin.rev_injective (P.idx_injective h))
    (fun m => (Finset.mem_symmDiff).2 (Or.inr ⟨P.a_idx_mem_support _, P.a_idx_not_mem hS _⟩))
    (fun m => by
      rw [P.final_carrier_eq_symmDiff hS]
      rintro (⟨-, h⟩ | ⟨h, h'⟩)
      · exact h (Finset.mem_coe.2 (P.a_idx_mem_support _))
      · exact h' (L.a_mem_carrier _))
    (fun m q => by
      rw [P.final_a_idx, P.final_b, ← P.adj_s_iff_adj_a_b _ q])
    (fun m => by
      rw [P.final_a_idx]
      exact (P.adj_a_idx _).symm)
    (fun m q hq => by
      by_cases hqi : ∃ j, P.idx j = q
      · obtain ⟨j, rfl⟩ := hqi
        exact ⟨Fin.rev j, by simp⟩
      · push Not at hqi
        rw [P.final_a_of_forall_ne hqi] at hq
        exact (L.adj_aa _ _ hq).elim)
    (fun m m' hmm' => by
      rw [P.final_a_idx]
      intro hadj
      have h := (P.adj_s_a_iff hclaw hS (Fin.rev m') (Fin.rev m)).1 hadj.symm
      have h1 : Fin.rev m' < Fin.rev m := Fin.rev_lt_rev.2 hmm'
      have h2 : (Fin.rev m').val < (Fin.rev m).val := h1
      omega)
    (fun m m' hmm' => by
      rw [P.final_a_idx]
      refine (P.link (Fin.rev m') (Fin.rev m) ?_).symm
      have h1 := m.isLt
      have h2 := m'.isLt
      simp only [Fin.val_rev]
      omega)
  refine ⟨P'', ?_, by rw [hP'', hsupp]⟩
  unfold Untethered
  rw [hP'', hsupp, P.symmDiff_symmDiff_final_image_a hS]
  exact hP

end Reverse

/-! ### Transporting an untethered path to the toggled pair -/

section Transport

variable [DecidableEq V] {S : Finset V} {k k' : ℕ}

/-- **Transport of a path to another hole.**  Let `P'` be a deformation path of `L'` along `S`
and let `M` be a hole and `S'` an independent set such that the vertices `s'_m` of `P'` lie in `S'`
and outside `M`, have the `b`-neighbours of `a'_{i'_m}` among the `b`-vertices of `M`, the
`a'_{i'_m}` are `a`-vertices of `M`, and the only `a`-vertices of `M` adjacent to some `s'_m` are
among the `a'_{i'_m}`.  Then `M` has a deformation path along `S'` with the same support as `P'`.
This is `exists_support_eq_of_conditions` for the data of `P'`. -/
theorem exists_transport {L' : G.EvenHoleLabeling k'} {S' : Finset V}
    (hS' : G.IsIndepSet (S' : Set V)) (P' : L'.SetDeformationPath S) (M : G.EvenHoleLabeling k)
    (h3 : ∀ m, P'.s m ∈ S') (h4 : ∀ m, P'.s m ∉ M.carrier)
    (h5 : ∀ m q, G.Adj (P'.s m) (M.b q) ↔ G.Adj (L'.a (P'.idx m)) (M.b q))
    (h7 : ∀ m, L'.a (P'.idx m) ∈ Set.range M.a)
    (h8 : ∀ m q, G.Adj (P'.s m) (M.a q) → ∃ m', M.a q = L'.a (P'.idx m')) :
    ∃ P'' : M.SetDeformationPath S', P''.support = P'.support := by
  choose r hr using h7
  have hinj : Function.Injective r := by
    intro m m' h
    have : L'.a (P'.idx m) = L'.a (P'.idx m') := by rw [← hr m, ← hr m', h]
    exact P'.idx_injective (L'.a_injective this)
  obtain ⟨P'', hP''⟩ := exists_support_eq_of_conditions (S := S') hS' M P'.len_pos P'.s r
    P'.s_injective hinj h3 h4
    (fun m q => by rw [hr m]; exact h5 m q)
    (fun m => by rw [hr m]; exact P'.adj_a_idx m)
    (fun m q hq => by
      obtain ⟨m', h⟩ := h8 m q hq
      exact ⟨m', M.a_injective (by rw [hr m']; exact h.symm)⟩)
    (fun m m' hmm' => by rw [hr m']; exact P'.not_adj_of_lt hmm')
    (fun m m' hmm' => by rw [hr m]; exact P'.link m m' hmm')
  refine ⟨P'', ?_⟩
  rw [hP'']
  unfold support
  congr 2
  funext m
  exact hr m

/-- **A path of the other colour class avoids the deforming vertices.**  Let `P` be a deformation
path of `L` along `S` and let `P'` be an untethered deformation path along `S` of a labelling `L'`
of the same carrier whose `a`-class is the `b`-class of `L`.  Then no deforming vertex `s_j` of `P`
lies on `P'`.

Indeed `s_{j-1}` and `s_j` share a `b`-neighbour (claw-freeness at `a_{i_{j-1}}`, whose neighbours
are `b_{i_{j-1}}`, `b_{next i_{j-1}}`, `s_{j-1}` and `s_j`), so `s_j ∈ P'` forces `s_{j-1} ∈ P'`
because `P'` is a component of `G[S ⊕ C_b]`; hence `s_0 ∈ P'`.  But `s_0` is a clone of an
`a`-vertex of `L`, with exactly one neighbour in `C_a`, while every vertex of `P'` in `S`
has two neighbours (`b'_{i'}`, `b'_{next i'}`) in the `b`-class of `L'`, which is `C_a`. -/
theorem cloneSet_disjoint_support_of_other_class (hclaw : G.IsClawFree)
    (hS : G.IsIndepSet (S : Set V)) {L : G.EvenHoleLabeling k} (P : L.SetDeformationPath S)
    {L' : G.EvenHoleLabeling k'} (P' : L'.SetDeformationPath S) (hcar : L.carrier = L'.carrier)
    (ha : Set.range L.a = Set.range L'.b)
    (hP' : G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.b)) ↑P'.support) :
    ∀ v ∈ P.cloneSet, v ∉ P'.support := by
  have step : ∀ j j' : Fin P.len, j.val + 1 = j'.val → P.s j' ∈ P'.support →
      P.s j ∈ P'.support := by
    intro j j' hjj' hj'
    have hlink := P.link j j' hjj'
    have hne1 : P.s j' ≠ L.b (P.idx j) := fun h =>
      P.s_not_mem_label_carrier hS j' (h ▸ L.b_mem_carrier _)
    have hne2 : P.s j' ≠ L.b (L.next (P.idx j)) := fun h =>
      P.s_not_mem_label_carrier hS j' (h ▸ L.b_mem_carrier _)
    have hne3 : L.b (P.idx j) ≠ L.b (L.next (P.idx j)) := fun h =>
      L.next_ne _ (L.b_injective h).symm
    have hcl := hclaw (center := L.a (P.idx j)) (a := P.s j') (b := L.b (P.idx j))
      (c := L.b (L.next (P.idx j))) hlink.symm (L.adj_a_b _) (L.adj_a_b_next _) hne1 hne2 hne3
    obtain ⟨q, hq, hadj⟩ : ∃ q, (q = P.idx j ∨ q = L.next (P.idx j)) ∧
        G.Adj (P.s j') (L.b q) := by
      rcases hcl with h | h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
      · exact (L.adj_bb _ _ h).elim
    have hsj : G.Adj (P.s j) (L.b q) := (P.adj_s_b_iff j q).2 hq
    have hybS : L.b q ∉ S := fun h =>
      hS (Finset.mem_coe.2 (P.s_mem j')) (Finset.mem_coe.2 h) hadj.ne hadj
    have hyU : L.b q ∈ (↑(symmDiff S (Finset.univ.image L.b)) : Set V) :=
      Finset.mem_coe.2 (Finset.mem_symmDiff.2
        (Or.inr ⟨Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hybS⟩))
    have hyQ : L.b q ∈ P'.support :=
      Finset.mem_coe.1 (hP'.2.2 (Finset.mem_coe.2 hj') hyU hadj)
    have hsU : P.s j ∈ (↑(symmDiff S (Finset.univ.image L.b)) : Set V) :=
      Finset.mem_coe.2 (Finset.mem_symmDiff.2
        (Or.inl ⟨P.s_mem j, Finset.disjoint_left.1 (P.cloneSet_disjoint_image_b hS)
          (P.mem_cloneSet.2 ⟨j, rfl⟩)⟩))
    exact Finset.mem_coe.1 (hP'.2.2 (Finset.mem_coe.2 hyQ) hsU hsj.symm)
  have chain : ∀ (n : ℕ) (hn : n < P.len), P.s ⟨n, hn⟩ ∈ P'.support →
      P.s P.first ∈ P'.support := by
    intro n
    induction n with
    | zero => exact fun hn h => h
    | succ n ih => exact fun hn h => ih (by omega) (step ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl h)
  intro v hv hvP'
  obtain ⟨j, rfl⟩ := P.mem_cloneSet.1 hv
  have h0 : P.s P.first ∈ P'.support := chain j.val j.isLt hvP'
  obtain ⟨m, hm | hm⟩ := P'.mem_support_iff.1 h0
  · have hn1 : G.Adj (P'.s m) (L'.b (P'.idx m)) := (P'.adj_s_b_iff m _).2 (Or.inl rfl)
    have hn2 : G.Adj (P'.s m) (L'.b (L'.next (P'.idx m))) := (P'.adj_s_b_iff m _).2 (Or.inr rfl)
    rw [hm] at hn1 hn2
    obtain ⟨p1, hp1⟩ : L'.b (P'.idx m) ∈ Set.range L.a := ha ▸ ⟨_, rfl⟩
    obtain ⟨p2, hp2⟩ : L'.b (L'.next (P'.idx m)) ∈ Set.range L.a := ha ▸ ⟨_, rfl⟩
    have c1 := (P.cloneAt_first_step.adj_a_iff_index p1).1 (hp1 ▸ hn1)
    have c2 := (P.cloneAt_first_step.adj_a_iff_index p2).1 (hp2 ▸ hn2)
    have : L'.b (P'.idx m) = L'.b (L'.next (P'.idx m)) := by
      rw [← hp1, ← hp2, c1, c2]
    exact L'.next_ne _ (L'.b_injective this).symm
  · exact P.s_not_mem_label_carrier hS P.first (hcar ▸ hm ▸ L'.a_mem_carrier _)

/-- **The components of `G[S ⊕ C_b]` not meeting `J` survive the toggle.**  If `P` is an untethered
path of `L` along `S` and `Q'` is a component of `G[S ⊕ C_b]` containing no deforming vertex
`s_j`, then `Q'` is also a component of `G[(S ⊕ P) ⊕ C_b]` (the `b`-class is unchanged by the
toggle, `S ⊕ P = (S ∖ J) ∪ K`).  A vertex of `Q'` adjacent to some `a_{i_j} ∈ K` would be
adjacent to `s_j` (if it is a `b`-vertex: the twins `s_j`, `a_{i_j}` have the same `b`-neighbours),
or would lie on `P` (if it is in `S`: `P` is a component of `G[S ⊕ C_a]`). -/
theorem isInducedComponent_symmDiff_toggle (hS : G.IsIndepSet (S : Set V))
    {L : G.EvenHoleLabeling k} (P : L.SetDeformationPath S) (hP : P.Untethered) {Q' : Finset V}
    (hQ' : G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.b)) ↑Q')
    (hdisj : ∀ v ∈ P.cloneSet, v ∉ Q') :
    G.IsInducedComponent ↑(symmDiff (symmDiff S P.support) (Finset.univ.image L.b)) ↑Q' := by
  have hJS : ∀ v, v ∈ P.cloneSet → v ∈ S := fun v hv => P.cloneSet_subset hv
  have hJB : ∀ v, v ∈ P.cloneSet → v ∉ Finset.univ.image L.b := fun v hv =>
    Finset.disjoint_left.1 (P.cloneSet_disjoint_image_b hS) hv
  have hKS : ∀ v, v ∈ P.replacedSet → v ∉ S := fun v hv => by
    obtain ⟨j, rfl⟩ := P.mem_replacedSet.1 hv
    exact P.a_idx_not_mem hS j
  have hKB : ∀ v, v ∈ P.replacedSet → v ∉ Finset.univ.image L.b := fun v hv =>
    Finset.disjoint_left.1 L.disjoint_image_a_image_b (P.replacedSet_subset hv)
  have hmem : ∀ v, v ∉ P.cloneSet → v ∉ P.replacedSet →
      (v ∈ symmDiff (symmDiff S P.support) (Finset.univ.image L.b) ↔
        v ∈ symmDiff S (Finset.univ.image L.b)) := by
    intro v hvJ hvK
    simp only [Finset.mem_symmDiff, support_eq_union, Finset.mem_union]
    tauto
  have hQW : ∀ x ∈ Q', x ∈ symmDiff S (Finset.univ.image L.b) := fun x hx =>
    Finset.mem_coe.1 (hQ'.1 (Finset.mem_coe.2 hx))
  have hQK : ∀ x ∈ Q', x ∉ P.replacedSet := by
    intro x hx hxK
    have h := Finset.mem_symmDiff.1 (hQW x hx)
    have h1 := hKS x hxK
    have h2 := hKB x hxK
    tauto
  refine ⟨fun x hx => ?_, hQ'.2.1, fun x y hx hy hxy => ?_⟩
  · have hxQ : x ∈ Q' := Finset.mem_coe.1 hx
    exact Finset.mem_coe.2 ((hmem x (hdisj x · hxQ |>.elim) (hQK x hxQ)).2 (hQW x hxQ))
  · have hxQ : x ∈ Q' := Finset.mem_coe.1 hx
    have hyW' : y ∈ symmDiff (symmDiff S P.support) (Finset.univ.image L.b) :=
      Finset.mem_coe.1 hy
    by_cases hyK : y ∈ P.replacedSet
    · exfalso
      obtain ⟨j, hj⟩ := P.mem_replacedSet.1 hyK
      rcases Finset.mem_symmDiff.1 (hQW x hxQ) with ⟨hxS, hxB⟩ | ⟨hxB, hxS⟩
      · -- `x ∈ S` adjacent to `a_{i_j}`: `x` lies on `P`
        have hxA : x ∉ Finset.univ.image L.a := by
          intro hxA
          exact L.isIndepSet_image_a (Finset.mem_coe.2 hxA)
            (Finset.mem_coe.2 (hj ▸ Finset.mem_image.2 ⟨P.idx j, Finset.mem_univ _, rfl⟩))
            hxy.ne hxy
        have hxU : x ∈ (↑(symmDiff S (Finset.univ.image L.a)) : Set V) :=
          Finset.mem_coe.2 (Finset.mem_symmDiff.2 (Or.inl ⟨hxS, hxA⟩))
        have hyP : y ∈ (↑P.support : Set V) :=
          Finset.mem_coe.2 (by rw [support_eq_union]; exact Finset.mem_union_right _ hyK)
        have hxP : x ∈ P.support := Finset.mem_coe.1 (hP.2.2 hyP hxU hxy.symm)
        have : x ∈ P.cloneSet := by
          rw [← P.inter_support_eq_cloneSet hS]
          exact Finset.mem_inter.2 ⟨hxS, hxP⟩
        exact hdisj x this hxQ
      · -- `x` is a `b`-vertex adjacent to `a_{i_j}`, hence adjacent to `s_j`
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hxB
        have hq := (L.adj_ab_iff (P.idx j) q).1 (hj ▸ hxy.symm)
        have hsj : G.Adj (P.s j) (L.b q) := (P.adj_s_b_iff j q).2 hq
        have hsU : P.s j ∈ (↑(symmDiff S (Finset.univ.image L.b)) : Set V) :=
          Finset.mem_coe.2 (Finset.mem_symmDiff.2
            (Or.inl ⟨P.s_mem j, hJB _ (P.mem_cloneSet.2 ⟨j, rfl⟩)⟩))
        exact hdisj _ (P.mem_cloneSet.2 ⟨j, rfl⟩)
          (Finset.mem_coe.1 (hQ'.2.2 hx hsU hsj.symm))
    · have hyJ : y ∉ P.cloneSet := by
        intro hyJ
        have h := Finset.mem_symmDiff.1 hyW'
        have h1 := hJS y hyJ
        have h2 := hJB y hyJ
        simp only [Finset.mem_symmDiff, support_eq_union, Finset.mem_union] at h
        tauto
      exact Finset.mem_coe.2 (Finset.mem_coe.1 (hQ'.2.2 hx
        (Finset.mem_coe.2 ((hmem y hyJ hyK).1 hyW')) hxy) : y ∈ Q')

/-- **A path of the same colour class survives the toggle.**  Let `P` be an untethered path of `L`
along `S` and `P'` another untethered path along `S` of a labelling `L'` of the same carrier with
the same colour classes, with `P'.support ≠ P.support`.  Then the toggled hole `P.final` has an
untethered deformation path along `S ⊕ P` with the same support as `P'`: distinct components of
`G[S ⊕ C_a]` are disjoint, `P'` has no neighbour on `P`, and `S ⊕ P ⊕ C~_a = S ⊕ C_a`
(`symmDiff_symmDiff_final_image_a`), so the neighbourhoods of the vertices of `P'` are the same in
`C` and in `C ⊕ P`. -/
theorem exists_toggle_path_same_class (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    {L : G.EvenHoleLabeling k} (P : L.SetDeformationPath S) (hP : P.Untethered)
    {L' : G.EvenHoleLabeling k'} (P' : L'.SetDeformationPath S) (hP' : P'.Untethered)
    (hcar : L.carrier = L'.carrier) (ha : Set.range L.a = Set.range L'.a)
    (hb : Set.range L.b = Set.range L'.b) (hne : P'.support ≠ P.support)
    (hS' : G.IsIndepSet ((symmDiff S P.support : Finset V) : Set V)) :
    ∃ P'' : P.final.SetDeformationPath (symmDiff S P.support),
      P''.Untethered ∧ P''.support = P'.support := by
  have hAA : Finset.univ.image L'.a = Finset.univ.image L.a :=
    (image_univ_eq_of_range_eq _ _ ha).symm
  have hP'U : G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.a)) ↑P'.support := by
    have h := hP'
    unfold Untethered at h
    rwa [hAA] at h
  have hdisj : Disjoint P.support P'.support :=
    Finset.disjoint_coe.1 (disjoint_of_isInducedComponent_of_ne hP hP'U
      (fun h => hne (Finset.coe_injective h).symm))
  have hsupp : ∀ m, P'.s m ∉ P.support := fun m h =>
    Finset.disjoint_left.1 hdisj h (P'.s_mem_support m)
  have hKP : ∀ m, L'.a (P'.idx m) ∉ P.support := fun m h =>
    Finset.disjoint_left.1 hdisj h (P'.a_idx_mem_support m)
  obtain ⟨P'', hP''⟩ := exists_transport hS' P' P.final
    (fun m => Finset.mem_symmDiff.2 (Or.inl ⟨P'.s_mem m, hsupp m⟩))
    (fun m => by
      rw [P.final_carrier_eq_symmDiff hS]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact P'.s_not_mem_label_carrier hS m (hcar ▸ h1)
      · exact hsupp m (Finset.mem_coe.1 h1))
    (fun m q => by
      rw [P.final_b]
      exact P'.adj_s_iff_adj_a_of_mem_range_b m (hb ▸ ⟨q, rfl⟩))
    (fun m => by
      have hmemA : L'.a (P'.idx m) ∈ Finset.univ.image L.a := by
        obtain ⟨q, hq⟩ : L'.a (P'.idx m) ∈ Set.range L.a := ha ▸ ⟨_, rfl⟩
        exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩
      have hK : L'.a (P'.idx m) ∉ P.replacedSet := fun h =>
        hKP m (by rw [support_eq_union]; exact Finset.mem_union_right _ h)
      have : L'.a (P'.idx m) ∈ Finset.univ.image P.final.a := by
        rw [P.final_image_a]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hmemA, hK⟩)
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 this
      exact ⟨q, hq⟩)
    (fun m q hq => by
      have hy : P.final.a q ∈ (Finset.univ.image L.a \ P.replacedSet) ∪ P.cloneSet := by
        rw [← P.final_image_a]
        exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩
      rcases Finset.mem_union.1 hy with hy | hy
      · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hy).1
        obtain ⟨q', hq'⟩ : L.a p ∈ Set.range L'.a := ha ▸ ⟨_, rfl⟩
        rw [← hp, ← hq'] at hq ⊢
        rcases (P'.adj_s_a_iff_all hclaw hS m q').1 hq with h | ⟨j', -, h⟩
        · exact ⟨m, by rw [h]⟩
        · exact ⟨j', by rw [h]⟩
      · obtain ⟨j, hj⟩ := P.mem_cloneSet.1 hy
        rw [← hj] at hq
        exact (hS (Finset.mem_coe.2 (P'.s_mem m)) (Finset.mem_coe.2 (P.s_mem j))
          hq.ne hq).elim)
  refine ⟨P'', ?_, hP''⟩
  unfold Untethered
  rw [hP'', P.symmDiff_symmDiff_final_image_a hS]
  exact hP'U

/-- **A path of the other colour class survives the toggle.**  Let `P` be an untethered path of `L`
along `S` and `P'` an untethered path along `S` of a labelling `L'` of the same carrier whose
`a`-class is the `b`-class of `L`.  Then the colour-swapped toggled hole `P.final.swapColors` (with
the same `a`-class `C_b`) has an untethered path along `S ⊕ P` with the same support as `P'`.

By `cloneSet_disjoint_support_of_other_class`, `P'` contains no deforming vertex `s_j`; by
`isInducedComponent_symmDiff_toggle` it is still a component of `G[(S ⊕ P) ⊕ C_b]`; and the
`b`-class of `P.final.swapColors` is `(C_a ∖ K) ∪ J` (up to the index shift `prev`): the vertices
of `P'` are non-adjacent to `J` (they are in `S`) and the `b'`-vertices of `P'` are non-adjacent to
`J` (a neighbour would put `s_j` on the component `P'`). -/
theorem exists_toggle_path_other_class (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    {L : G.EvenHoleLabeling k} (P : L.SetDeformationPath S) (hP : P.Untethered)
    {L' : G.EvenHoleLabeling k'} (P' : L'.SetDeformationPath S) (hP' : P'.Untethered)
    (hcar : L.carrier = L'.carrier) (ha : Set.range L.a = Set.range L'.b)
    (hb : Set.range L.b = Set.range L'.a)
    (hS' : G.IsIndepSet ((symmDiff S P.support : Finset V) : Set V)) :
    ∃ P'' : P.final.swapColors.SetDeformationPath (symmDiff S P.support),
      P''.Untethered ∧ P''.support = P'.support := by
  have hBB : Finset.univ.image L'.a = Finset.univ.image L.b :=
    (image_univ_eq_of_range_eq _ _ hb).symm
  have hP'U : G.IsInducedComponent ↑(symmDiff S (Finset.univ.image L.b)) ↑P'.support := by
    have h := hP'
    unfold Untethered at h
    rwa [hBB] at h
  have hJ : ∀ v ∈ P.cloneSet, v ∉ P'.support :=
    cloneSet_disjoint_support_of_other_class hclaw hS P P' hcar ha hP'U
  have hsupp : ∀ m, P'.s m ∉ P.support := by
    intro m h
    have hJ' : P'.s m ∈ P.cloneSet := by
      rw [← P.inter_support_eq_cloneSet hS]
      exact Finset.mem_inter.2 ⟨P'.s_mem m, h⟩
    exact hJ _ hJ' (P'.s_mem_support m)
  obtain ⟨P'', hP''⟩ := exists_transport hS' P' P.final.swapColors
    (fun m => Finset.mem_symmDiff.2 (Or.inl ⟨P'.s_mem m, hsupp m⟩))
    (fun m => by
      rw [swapColors_carrier, P.final_carrier_eq_symmDiff hS]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact P'.s_not_mem_label_carrier hS m (hcar ▸ h1)
      · exact hsupp m (Finset.mem_coe.1 h1))
    (fun m q => by
      have hy : P.final.a (P.final.prev q) ∈
          (Finset.univ.image L.a \ P.replacedSet) ∪ P.cloneSet := by
        rw [← P.final_image_a]
        exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
      show G.Adj (P'.s m) (P.final.a (P.final.prev q)) ↔
        G.Adj (L'.a (P'.idx m)) (P.final.a (P.final.prev q))
      rcases Finset.mem_union.1 hy with hy | hy
      · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hy).1
        rw [← hp]
        exact P'.adj_s_iff_adj_a_of_mem_range_b m (ha ▸ ⟨p, rfl⟩)
      · obtain ⟨j, hj⟩ := P.mem_cloneSet.1 hy
        rw [← hj]
        constructor
        · intro h
          exact (hS (Finset.mem_coe.2 (P'.s_mem m)) (Finset.mem_coe.2 (P.s_mem j))
            h.ne h).elim
        · intro h
          have hjU : P.s j ∈ (↑(symmDiff S (Finset.univ.image L.b)) : Set V) :=
            Finset.mem_coe.2 (Finset.mem_symmDiff.2
              (Or.inl ⟨P.s_mem j, Finset.disjoint_left.1 (P.cloneSet_disjoint_image_b hS)
                (P.mem_cloneSet.2 ⟨j, rfl⟩)⟩))
          exact (hJ _ (P.mem_cloneSet.2 ⟨j, rfl⟩)
            (Finset.mem_coe.1 (hP'U.2.2 (Finset.mem_coe.2 (P'.a_idx_mem_support m)) hjU
              h))).elim)
    (fun m => by
      obtain ⟨q, hq⟩ : L'.a (P'.idx m) ∈ Set.range L.b := hb ▸ ⟨_, rfl⟩
      exact ⟨q, by rw [swapColors_a, P.final_b]; exact hq⟩)
    (fun m q hq => by
      rw [swapColors_a, P.final_b] at hq ⊢
      obtain ⟨q', hq'⟩ : L.b q ∈ Set.range L'.a := hb ▸ ⟨_, rfl⟩
      rw [← hq'] at hq ⊢
      rcases (P'.adj_s_a_iff_all hclaw hS m q').1 hq with h | ⟨j', -, h⟩
      · exact ⟨m, by rw [h]⟩
      · exact ⟨j', by rw [h]⟩)
  refine ⟨P'', ?_, hP''⟩
  unfold Untethered
  rw [hP'']
  have himg : Finset.univ.image P.final.swapColors.a = Finset.univ.image L.b := by
    rw [← P.final_image_b]
    rfl
  rw [himg]
  exact isInducedComponent_symmDiff_toggle hS P hP hP'U hJ

end Transport

end SetDeformationPath

end EvenHoleLabeling

/-! ### The set `𝒫(C, S)` of supports of untethered runs -/

/-- `𝒫(C, S)`: the supports of the untethered deformation paths of the even hole `C` along the
independent set `S`, over all full-cyclic labellings of `C`, i.e. along both colour classes
(v1 proof of Theorem 1 (ii), L908-911: "there is at least one untethered path
`P = s₀ - a₀ - ⋯ - s_{ℓ-1} - a_{ℓ-1}`").  It is the finite set from which v1 fixes "a path by which
corresponding terms are paired" (L926-927). -/
noncomputable def untetheredSupports [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C : Set V)
    (S : Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun Q => ∃ (k : ℕ) (L : G.EvenHoleLabeling k),
    L.HasFullCyclicOrder ∧ L.carrier = C ∧
      ∃ P : L.SetDeformationPath S, P.Untethered ∧ P.support = Q

theorem mem_untetheredSupports [Fintype V] [DecidableEq V] {C : Set V} {S Q : Finset V} :
    Q ∈ G.untetheredSupports C S ↔ ∃ (k : ℕ) (L : G.EvenHoleLabeling k),
      L.HasFullCyclicOrder ∧ L.carrier = C ∧
        ∃ P : L.SetDeformationPath S, P.Untethered ∧ P.support = Q := by
  classical
  unfold untetheredSupports
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- An element of `𝒫(C, S)` is nonempty (it contains the initialising vertex `s₀`). -/
theorem nonempty_of_mem_untetheredSupports [Fintype V] [DecidableEq V] {C : Set V}
    {S Q : Finset V} (hQ : Q ∈ G.untetheredSupports C S) : Q.Nonempty := by
  obtain ⟨k, L, -, -, P, -, rfl⟩ := mem_untetheredSupports.1 hQ
  exact ⟨P.s P.first, P.s_mem_support P.first⟩

/-- **The toggle data of an element of `𝒫(C, S)`.**  If `Q ∈ 𝒫(C, S)`, then `S ⊕ Q` is independent,
has the same size as `S` and is reached from `S` by token slides (v1 L913, "`S~ ∈ μ`"), and
`C ⊕ Q` lies in the deformation closure `⟨C⟩` (v1 L913, "`C~ ∈ ⟨C₀⟩`"). -/
theorem toggle_data_of_mem_untetheredSupports [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {C : Set V} {S Q : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hQ : Q ∈ G.untetheredSupports C S) :
    G.IsIndepSet ↑(symmDiff S Q) ∧ (symmDiff S Q).card = S.card ∧
      G.TokenSlideReachable ↑S ↑(symmDiff S Q) ∧
      InEvenHoleDeformationClosure G C (symmDiff C ↑Q) := by
  obtain ⟨k, L, hL, hcar, P, hP, rfl⟩ := mem_untetheredSupports.1 hQ
  obtain ⟨h1, h2, h3⟩ := P.toggle_configuration hclaw hL hS hP
  refine ⟨h1, h2, h3, ?_⟩
  have := P.inEvenHoleDeformationClosure_final
  rwa [P.final_carrier_eq_symmDiff hS, hcar] at this

/-- **Stability, the elements of `𝒫(C, S)` survive the toggle.**  If `Q, Q' ∈ 𝒫(C, S)` then
`Q' ∈ 𝒫(C ⊕ Q, S ⊕ Q)`.  For `Q' = Q` this is the reverse run
(`SetDeformationPath.exists_reverse_untethered`); for `Q'` a different path of the same colour class
it is `exists_toggle_path_same_class`, and for a path of the other colour class
`exists_toggle_path_other_class`. -/
theorem mem_untetheredSupports_toggle_of_mem [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {C : Set V} {S Q Q' : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hQ : Q ∈ G.untetheredSupports C S) (hQ' : Q' ∈ G.untetheredSupports C S) :
    Q' ∈ G.untetheredSupports (symmDiff C ↑Q) (symmDiff S Q) := by
  obtain ⟨k, L, hL, hcar, P, hP, rfl⟩ := mem_untetheredSupports.1 hQ
  obtain ⟨k', L', hL', hcar', P', hP', rfl⟩ := mem_untetheredSupports.1 hQ'
  have hS' : G.IsIndepSet ((symmDiff S P.support : Finset V) : Set V) :=
    (P.toggle_configuration hclaw hL hS hP).1
  have hcc : L.carrier = L'.carrier := hcar.trans hcar'.symm
  have hCar : G.IsEvenHoleCarrier L.carrier := L.isEvenHoleCarrier_of_hasFullCyclicOrder hL
  have hfinal : P.final.carrier = symmDiff C ↑P.support := by
    rw [P.final_carrier_eq_symmDiff hS, hcar]
  have hfull := P.hasFullCyclicOrder_final hL
  by_cases hEq : P'.support = P.support
  · obtain ⟨P'', hU, hs⟩ := P.exists_reverse_untethered hclaw hS hP hS'
    exact mem_untetheredSupports.2 ⟨k, P.final, hfull, hfinal, P'', hU, hs.trans hEq.symm⟩
  · rcases L.colorClasses_eq_or_swap L' hCar hcc with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨P'', hU, hs⟩ :=
        P.exists_toggle_path_same_class hclaw hS hP P' hP' hcc ha hb hEq hS'
      exact mem_untetheredSupports.2 ⟨k, P.final, hfull, hfinal, P'', hU, hs⟩
    · obtain ⟨P'', hU, hs⟩ :=
        P.exists_toggle_path_other_class hclaw hS hP P' hP' hcc ha hb hS'
      exact mem_untetheredSupports.2 ⟨k, P.final.swapColors, hfull.swapColors,
        by rw [EvenHoleLabeling.swapColors_carrier, hfinal], P'', hU, hs⟩

/-- **Stability of the set of untethered runs under toggling** (the claim that v1 leaves
unargued, L926-927: the path chosen for the pair `(C, S)` is chosen again for `(C ⊕ P, S ⊕ P)`).
For `Q ∈ 𝒫(C, S)`, `𝒫(C ⊕ Q, S ⊕ Q) = 𝒫(C, S)`.

The same-class part is the observation that distinct components of `G[S ⊕ C_a]` do not see each
other; the new part is cross-class stability: a run of `G[S ⊕ C_b]` never meets the deforming
vertices `s_j` of a run in `G[S ⊕ C_a]` (`cloneSet_disjoint_support_of_other_class`), and the toggle
only exchanges the twins `s_j`, `a_{i_j}`, which have the same neighbours in `C_b`.  The proof
shows `⊆` by `mem_untetheredSupports_toggle_of_mem` and `⊇` by applying it to the toggled pair,
using that `Q ∈ 𝒫(C ⊕ Q, S ⊕ Q)` (the reverse run) and `(C ⊕ Q) ⊕ Q = C`.  The hypothesis that `C`
is an even-hole carrier is not used (it follows from `Q ∈ 𝒫(C, S)`). -/
theorem untetheredSupports_toggle_of_mem [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {C : Set V} {S Q : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hQ : Q ∈ G.untetheredSupports C S) :
    G.untetheredSupports (symmDiff C ↑Q) (symmDiff S Q) = G.untetheredSupports C S := by
  have hS' : G.IsIndepSet ((symmDiff S Q : Finset V) : Set V) :=
    (toggle_data_of_mem_untetheredSupports hclaw hS hQ).1
  have hQ' : Q ∈ G.untetheredSupports (symmDiff C ↑Q) (symmDiff S Q) :=
    mem_untetheredSupports_toggle_of_mem hclaw hS hQ hQ
  refine Finset.Subset.antisymm (fun Q' hQ'' => ?_) (fun Q' hQ'' =>
    mem_untetheredSupports_toggle_of_mem hclaw hS hQ hQ'')
  have := mem_untetheredSupports_toggle_of_mem hclaw hS' hQ' hQ''
  rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this

/-- **Stability of `𝒫(C, S)` under toggling** (the statement of work package H5).  For `C` an
even-hole carrier, `S` independent and `Q ∈ 𝒫(C, S)` an untethered support,
`𝒫(C ⊕ Q, S ⊕ Q) = 𝒫(C, S)`.  See `untetheredSupports_toggle_of_mem`; the hypothesis `hC` is
redundant (`Q ∈ 𝒫(C, S)` already presents `C` as the carrier of a full-cyclic labelling). -/
theorem untetheredSupports_toggle [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {C : Set V} (_hC : G.IsEvenHoleCarrier C) {S Q : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hQ : Q ∈ G.untetheredSupports C S) :
    G.untetheredSupports (symmDiff C ↑Q) (symmDiff S Q) = G.untetheredSupports C S :=
  untetheredSupports_toggle_of_mem hclaw hS hQ

/-! ### The pairing involution on pairs `(C, S)` -/

/-- A fixed element of `𝒫(C, S)`, chosen as a function of the set `𝒫(C, S)` alone (and `∅` when
`𝒫(C, S)` is empty).  This is the "fixed path by which corresponding terms are paired" of v1
L926-927, made into a function of the data `(C, S)`. -/
noncomputable def chosenUntethered [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C : Set V)
    (S : Finset V) : Finset V :=
  if h : (G.untetheredSupports C S).Nonempty then h.choose else ∅

/-- The chosen support lies in `𝒫(C, S)` whenever that set is nonempty. -/
theorem chosenUntethered_mem [Fintype V] [DecidableEq V] {C : Set V} {S : Finset V}
    (h : (G.untetheredSupports C S).Nonempty) :
    G.chosenUntethered C S ∈ G.untetheredSupports C S := by
  unfold chosenUntethered
  rw [dif_pos h]
  exact h.choose_spec

/-- The chosen support only depends on the set `𝒫(C, S)`. -/
theorem chosenUntethered_congr [Fintype V] [DecidableEq V] {C C' : Set V} {S S' : Finset V}
    (h : G.untetheredSupports C S = G.untetheredSupports C' S') :
    G.chosenUntethered C S = G.chosenUntethered C' S' := by
  unfold chosenUntethered
  simp only [h]

/-- **Stability of the chosen support.**  The chosen untethered support of `(C, S)` is the chosen
untethered support of the toggled pair `(C ⊕ Q, S ⊕ Q)`, `Q ∈ 𝒫(C, S)`: this is
`untetheredSupports_toggle_of_mem` (v1 L926-927: the toggled term is paired by the same path). -/
theorem chosenUntethered_toggle [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree) {C : Set V}
    {S Q : Finset V} (hS : G.IsIndepSet (S : Set V)) (hQ : Q ∈ G.untetheredSupports C S) :
    G.chosenUntethered (symmDiff C ↑Q) (symmDiff S Q) = G.chosenUntethered C S :=
  chosenUntethered_congr (untetheredSupports_toggle_of_mem hclaw hS hQ)

/-- Toggling an element of `𝒫(C, S)` in the `k`-configuration `S` gives a `k`-configuration. -/
theorem isNIndepSet_symmDiff_of_mem_untetheredSupports [Fintype V] [DecidableEq V]
    (hclaw : G.IsClawFree) {k : ℕ} {C : Set V} {S Q : Finset V} (hS : G.IsNIndepSet k S)
    (hQ : Q ∈ G.untetheredSupports C S) : G.IsNIndepSet k (symmDiff S Q) := by
  obtain ⟨h1, h2, -⟩ := toggle_data_of_mem_untetheredSupports hclaw hS.isIndepSet hQ
  exact ⟨h1, h2.trans hS.card_eq⟩

/-- The pairing of v1 L925-927 on pairs `(C, S)`: if `𝒫(C, S)` is nonempty, toggle the chosen
untethered path `Q` in both arguments, `(C, S) ↦ (C ⊕ Q, S ⊕ Q)`; otherwise do nothing. -/
noncomputable def cycleChargeToggle [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree) (s : ℕ)
    (p : Set V × G.TokenConfiguration s) : Set V × G.TokenConfiguration s :=
  if h : (G.untetheredSupports p.1 p.2.1).Nonempty then
    (symmDiff p.1 ↑(G.chosenUntethered p.1 p.2.1),
      ⟨symmDiff p.2.1 (G.chosenUntethered p.1 p.2.1),
        isNIndepSet_symmDiff_of_mem_untetheredSupports hclaw p.2.2 (chosenUntethered_mem h)⟩)
  else p

/-- On a pair with `𝒫(C, S)` nonempty, `cycleChargeToggle` toggles the chosen path in both
arguments. -/
theorem cycleChargeToggle_of_nonempty [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree) {s : ℕ}
    {p : Set V × G.TokenConfiguration s} (h : (G.untetheredSupports p.1 p.2.1).Nonempty) :
    ((cycleChargeToggle hclaw s p).1 = symmDiff p.1 ↑(G.chosenUntethered p.1 p.2.1)) ∧
      ((cycleChargeToggle hclaw s p).2.1 = symmDiff p.2.1 (G.chosenUntethered p.1 p.2.1)) := by
  unfold cycleChargeToggle
  rw [dif_pos h]
  exact ⟨rfl, rfl⟩

/-- On a pair with `𝒫(C, S)` empty, `cycleChargeToggle` is the identity. -/
theorem cycleChargeToggle_of_not_nonempty [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {s : ℕ} {p : Set V × G.TokenConfiguration s}
    (h : ¬ (G.untetheredSupports p.1 p.2.1).Nonempty) : cycleChargeToggle hclaw s p = p := by
  unfold cycleChargeToggle
  rw [dif_neg h]

/-- `cycleChargeToggle` is an involution: the toggled pair has the same set `𝒫`
(`untetheredSupports_toggle_of_mem`), hence the same chosen path, and `Q ⊕ Q = ∅`. -/
theorem cycleChargeToggle_involutive [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree) (s : ℕ)
    (p : Set V × G.TokenConfiguration s) :
    cycleChargeToggle hclaw s (cycleChargeToggle hclaw s p) = p := by
  by_cases h : (G.untetheredSupports p.1 p.2.1).Nonempty
  · obtain ⟨h1, h2⟩ := cycleChargeToggle_of_nonempty hclaw h
    have hQ : G.chosenUntethered p.1 p.2.1 ∈ G.untetheredSupports p.1 p.2.1 :=
      chosenUntethered_mem h
    have hP : G.untetheredSupports (cycleChargeToggle hclaw s p).1
        (cycleChargeToggle hclaw s p).2.1 = G.untetheredSupports p.1 p.2.1 := by
      rw [h1, h2]
      exact untetheredSupports_toggle_of_mem hclaw p.2.2.isIndepSet hQ
    have hne : (G.untetheredSupports (cycleChargeToggle hclaw s p).1
        (cycleChargeToggle hclaw s p).2.1).Nonempty := by
      rw [hP]
      exact h
    have hchosen : G.chosenUntethered (cycleChargeToggle hclaw s p).1
        (cycleChargeToggle hclaw s p).2.1 = G.chosenUntethered p.1 p.2.1 := by
      rw [h1, h2]
      exact chosenUntethered_toggle hclaw p.2.2.isIndepSet hQ
    obtain ⟨h3, h4⟩ := cycleChargeToggle_of_nonempty hclaw hne
    refine Prod.ext ?_ (Subtype.ext ?_)
    · rw [h3, hchosen, h1]
      exact symmDiff_symmDiff_cancel_right _ _
    · rw [h4, hchosen, h2]
      exact symmDiff_symmDiff_cancel_right _ _
  · rw [cycleChargeToggle_of_not_nonempty hclaw h, cycleChargeToggle_of_not_nonempty hclaw h]

/-- If `𝒫(C, S)` is nonempty then `cycleChargeToggle` moves the pair: the chosen path is nonempty,
and `C ⊕ Q = C` would force `Q = ∅`. -/
theorem cycleChargeToggle_ne_of_nonempty [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {s : ℕ} {p : Set V × G.TokenConfiguration s}
    (h : (G.untetheredSupports p.1 p.2.1).Nonempty) : cycleChargeToggle hclaw s p ≠ p := by
  intro heq
  obtain ⟨h1, -⟩ := cycleChargeToggle_of_nonempty hclaw h
  have hne : (G.chosenUntethered p.1 p.2.1).Nonempty :=
    nonempty_of_mem_untetheredSupports (chosenUntethered_mem h)
  have hfix : symmDiff p.1 ↑(G.chosenUntethered p.1 p.2.1) = p.1 := by
    rw [← h1, heq]
  rw [symmDiff_eq_left] at hfix
  exact hne.ne_empty (by simpa using hfix)

/-- If `p.1` lies in the deformation closure of `C₀`, so does the first component of its toggle. -/
theorem cycleChargeToggle_mem_closure [Fintype V] [DecidableEq V] (hclaw : G.IsClawFree)
    {C₀ : Set V} {s : ℕ} {p : Set V × G.TokenConfiguration s}
    (hp : InEvenHoleDeformationClosure G C₀ p.1) :
    InEvenHoleDeformationClosure G C₀ (cycleChargeToggle hclaw s p).1 := by
  by_cases h : (G.untetheredSupports p.1 p.2.1).Nonempty
  · obtain ⟨h1, -⟩ := cycleChargeToggle_of_nonempty hclaw h
    rw [h1]
    exact InEvenHoleDeformationClosure.trans hp
      (toggle_data_of_mem_untetheredSupports hclaw p.2.2.isIndepSet (chosenUntethered_mem h)).2.2.2
  · rw [cycleChargeToggle_of_not_nonempty hclaw h]
    exact hp

/-! ### Theorem 1 (ii) -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- The summand of the expansion `[J_{C₀}, q_{s,μ}] = Σ_{C ∈ ⟨C₀⟩, S ∈ μ} [h_C, h_S]` (v1 L904),
written over all pairs `(C, S)` with an indicator for `S ∈ μ`. -/
noncomputable def cycleChargeTerm [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {s : ℕ} (μ : G.TokenSlidingComponent s)
    (p : Set V × G.TokenConfiguration s) : A := by
  classical
  exact if G.tokenSlidingComponentMk s p.2 = μ then
    H.evenHoleOperator p.1 * H.independentProduct p.2.1 -
      H.independentProduct p.2.1 * H.evenHoleOperator p.1 else 0

/-- `cycleChargeTerm` with its decidability instance made explicit. -/
theorem cycleChargeTerm_eq_ite [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {s : ℕ} (μ : G.TokenSlidingComponent s)
    (p : Set V × G.TokenConfiguration s) [Decidable (G.tokenSlidingComponentMk s p.2 = μ)] :
    H.cycleChargeTerm μ p =
      if G.tokenSlidingComponentMk s p.2 = μ then
        H.evenHoleOperator p.1 * H.independentProduct p.2.1 -
          H.independentProduct p.2.1 * H.evenHoleOperator p.1 else 0 := by
  unfold cycleChargeTerm
  congr

open scoped Classical in
/-- Expansion of the commutator `[J_{C₀}, q_{s,μ}]` as a sum over the pairs
`(C, S) ∈ ⟨C₀⟩ × (k-configurations)` (v1 L904, `equation:conservedchargecyclecommutator`). -/
theorem commutator_generalizedCycleSymmetryOp_eq_sum [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (C₀ : Set V) {s : ℕ}
    (μ : G.TokenSlidingComponent s) :
    algebraCommutator (H.generalizedCycleSymmetryOp C₀) (H.tokenSlidingChargeOp s μ) =
      ∑ p ∈ (G.deformationClosureFinset C₀) ×ˢ (Finset.univ : Finset (G.TokenConfiguration s)),
        H.cycleChargeTerm μ p := by
  classical
  unfold generalizedCycleSymmetryOp generalizedCycleSymmetry tokenSlidingChargeOp
    tokenSlidingCharge algebraCommutator
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_product]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [H.cycleChargeTerm_eq_ite]
  by_cases h : G.tokenSlidingComponentMk s S = μ <;> simp [h]

/-- The terms of a pair `(C, S)` and of its toggle cancel: for `Q ∈ 𝒫(C, S)` and `p'` the pair
`(C ⊕ Q, S ⊕ Q)`, `[h_C, h_S] + [h_{C ⊕ Q}, h_{S ⊕ Q}] = 0` (v1 L920-925), and `S ⊕ Q` lies in the
same token-sliding component as `S`, so the indicators agree. -/
theorem cycleChargeTerm_add_eq_zero_of_toggle [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {s : ℕ}
    (μ : G.TokenSlidingComponent s) {p p' : Set V × G.TokenConfiguration s} {Q : Finset V}
    (hQ : Q ∈ G.untetheredSupports p.1 p.2.1) (h1 : p'.1 = symmDiff p.1 ↑Q)
    (h2 : p'.2.1 = symmDiff p.2.1 Q) :
    H.cycleChargeTerm μ p + H.cycleChargeTerm μ p' = 0 := by
  classical
  obtain ⟨k, L, hL, hcar, P, hP, rfl⟩ := mem_untetheredSupports.1 hQ
  have hS := p.2.2.isIndepSet
  obtain ⟨-, -, hreach, -⟩ := toggle_data_of_mem_untetheredSupports hclaw hS hQ
  have hcomp : G.tokenSlidingComponentMk s p'.2 = G.tokenSlidingComponentMk s p.2 :=
    (tokenSlidingComponentMk_eq_of_tokenSlideReachable (by rw [h2]; exact hreach)).symm
  have hop : H.evenHoleOperator p.1 = H.labelingOperator L := by
    rw [← hcar]
    exact H.evenHoleOperator_eq L hL
  have hop' : H.evenHoleOperator p'.1 = H.labelingOperator P.final := by
    have hfinal : P.final.carrier = p'.1 := by
      rw [h1, P.final_carrier_eq_symmDiff hS, hcar]
    rw [← hfinal]
    exact H.evenHoleOperator_eq P.final (P.hasFullCyclicOrder_final hL)
  obtain ⟨e1, e2⟩ := EvenHoleLabeling.SetDeformationPath.toggle_add_eq_zero H hclaw hL hS P hP
  rw [H.cycleChargeTerm_eq_ite μ p, H.cycleChargeTerm_eq_ite μ p', hcomp]
  by_cases hc : G.tokenSlidingComponentMk s p.2 = μ
  · rw [if_pos hc, if_pos hc, hop, hop', h2]
    have e := sub_add_sub_comm (H.labelingOperator L * H.independentProduct p.2.1)
      (H.independentProduct p.2.1 * H.labelingOperator L)
      (H.labelingOperator P.final * H.independentProduct (symmDiff p.2.1 P.support))
      (H.independentProduct (symmDiff p.2.1 P.support) * H.labelingOperator P.final)
    rw [e, e1, e2, sub_zero]
  · rw [if_neg hc, if_neg hc, add_zero]

/-- If `𝒫(C, S)` is empty then `h_C` and `h_S` commute, for `C ∈ ⟨C₀⟩` and `C₀` an even hole.
(Otherwise `|A(C, S)|` is odd by `labelingOperator_mul_independentProduct`'s sign, and
`exists_untethered_of_odd` gives an element of `𝒫(C, S)`.) -/
theorem commutator_evenHoleOperator_eq_zero_of_untetheredSupports_eq_empty [Fintype V]
    [DecidableEq V] (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {C₀ C : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀) (hCc : InEvenHoleDeformationClosure G C₀ C) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hempty : ¬ (G.untetheredSupports C S).Nonempty) :
    H.evenHoleOperator C * H.independentProduct S -
      H.independentProduct S * H.evenHoleOperator C = 0 := by
  obtain ⟨k, L, hL, hcar, hop⟩ := H.exists_fullCyclic_labeling_of_mem_closure hC₀ hCc
  have heven : Even (G.anticommutingVertices L.carrier S).card := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rcases L.exists_untethered_of_odd hclaw hL hS hodd with ⟨P, hP⟩ | ⟨P, hP⟩
    · exact hempty ⟨P.support, mem_untetheredSupports.2 ⟨k, L, hL, hcar, P, hP, rfl⟩⟩
    · exact hempty ⟨P.support, mem_untetheredSupports.2
        ⟨k, L.swapColors, hL.swapColors, by rw [EvenHoleLabeling.swapColors_carrier, hcar],
          P, hP, rfl⟩⟩
  rw [hop, sub_eq_zero, H.labelingOperator_mul_independentProduct L hS, heven.neg_one_pow,
    one_mul]

/-- **Theorem 1 (ii)** (v1 `theorem:conservedcharges` (ii), L864-871, proof L904-927).

For a Hamiltonian with claw-free (finite) frustration graph `G`, represented by
`H : G.PauliFrustrationRepresentation A`, and an even hole `C₀`, the generalized cycle symmetry
`J_{C₀} = Σ_{C ∈ ⟨C₀⟩} h_C` commutes with every token-sliding charge `q_{s,μ}`:
`[J_{C₀}, q_{s,μ}] = 0`.

There is no premise beyond the representation `H`, the finiteness of `V`, claw-freeness of `G`, and
`C₀` being an even hole (v1 defines `J_{C₀}` only for even holes); the ring `A` is arbitrary.

The proof is v1's: expand `[J_{C₀}, q_{s,μ}] = Σ_{C ∈ ⟨C₀⟩, S ∈ μ} [h_C, h_S]`; if `h_C` and `h_S`
anticommute, `𝒫(C, S)` of untethered supports is nonempty
(`EvenHoleLabeling.exists_untethered_of_odd`), and the term `(C, S)` is paired with
`(C ⊕ Q, S ⊕ Q)` for the chosen `Q ∈ 𝒫(C, S)` (`cycleChargeToggle`); the two terms cancel
(`SetDeformationPath.toggle_add_eq_zero`).  What v1 does not argue, and what is proved here, is that
the pairing is an involution: the chosen path is chosen again for the toggled pair, because
`𝒫(C ⊕ Q, S ⊕ Q) = 𝒫(C, S)` (`untetheredSupports_toggle`), including the cross-class case.  The
sum is then killed by `Finset.sum_involution`. -/
theorem paperTheorem1ii [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀) (s : ℕ) (μ : G.TokenSlidingComponent s) :
    algebraCommutator (H.generalizedCycleSymmetryOp C₀) (H.tokenSlidingChargeOp s μ) = 0 := by
  classical
  rw [H.commutator_generalizedCycleSymmetryOp_eq_sum]
  refine Finset.sum_involution (fun p _ => cycleChargeToggle hclaw s p) ?_ ?_ ?_ ?_
  · -- the terms of `p` and its partner cancel
    intro p hp
    have hpc : InEvenHoleDeformationClosure G C₀ p.1 :=
      mem_deformationClosureFinset.1 (Finset.mem_product.1 hp).1
    by_cases h : (G.untetheredSupports p.1 p.2.1).Nonempty
    · obtain ⟨h1, h2⟩ := cycleChargeToggle_of_nonempty hclaw h
      exact H.cycleChargeTerm_add_eq_zero_of_toggle hclaw μ (chosenUntethered_mem h) h1 h2
    · rw [cycleChargeToggle_of_not_nonempty hclaw h]
      have hz : H.cycleChargeTerm μ p = 0 := by
        rw [H.cycleChargeTerm_eq_ite,
          H.commutator_evenHoleOperator_eq_zero_of_untetheredSupports_eq_empty hclaw hC₀ hpc
            p.2.2.isIndepSet h]
        simp
      rw [hz, add_zero]
  · -- no fixed points among the nonzero terms
    intro p hp hne
    have hpc : InEvenHoleDeformationClosure G C₀ p.1 :=
      mem_deformationClosureFinset.1 (Finset.mem_product.1 hp).1
    by_cases h : (G.untetheredSupports p.1 p.2.1).Nonempty
    · exact cycleChargeToggle_ne_of_nonempty hclaw h
    · exfalso
      apply hne
      rw [H.cycleChargeTerm_eq_ite,
        H.commutator_evenHoleOperator_eq_zero_of_untetheredSupports_eq_empty hclaw hC₀ hpc
          p.2.2.isIndepSet h]
      simp
  · intro p hp
    refine Finset.mem_product.2 ⟨mem_deformationClosureFinset.2 ?_, Finset.mem_univ _⟩
    exact cycleChargeToggle_mem_closure hclaw (mem_deformationClosureFinset.1
      (Finset.mem_product.1 hp).1)
  · intro p _
    exact cycleChargeToggle_involutive hclaw s p

/-- **Theorem 1 (ii), conservation of `H`** (the last sentence of v1 `theorem:conservedcharges`,
for the charges `J_{C₀}`): `[H, J_{C₀}] = 0` for every even hole `C₀`.

By `Q^(1) = H` (`operatorIndependentSetChargeFull_one`) and `Σ_{μ ∈ Ξ₁} q_{1,μ} = Q^(1)`
(`sum_tokenSlidingChargeOp`), `H = Σ_μ q_{1,μ}`, and each `[J_{C₀}, q_{1,μ}]` vanishes by
`paperTheorem1ii`. -/
theorem hamiltonian_commute_generalizedCycleSymmetryOp [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {C₀ : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀) :
    algebraCommutator H.hamiltonian (H.generalizedCycleSymmetryOp C₀) = 0 := by
  have hH : H.hamiltonian =
      ∑ μ ∈ G.tokenSlidingComponentFinset 1, H.tokenSlidingChargeOp 1 μ :=
    (H.operatorIndependentSetChargeFull_one).symm.trans (H.sum_tokenSlidingChargeOp 1).symm
  rw [hH]
  have hsum : algebraCommutator (∑ μ ∈ G.tokenSlidingComponentFinset 1,
        H.tokenSlidingChargeOp 1 μ) (H.generalizedCycleSymmetryOp C₀) =
      ∑ μ ∈ G.tokenSlidingComponentFinset 1,
        algebraCommutator (H.tokenSlidingChargeOp 1 μ) (H.generalizedCycleSymmetryOp C₀) := by
    simp only [algebraCommutator, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have h := H.paperTheorem1ii hclaw hC₀ 1 μ
  unfold algebraCommutator at h ⊢
  rw [sub_eq_zero] at h ⊢
  exact h.symm

end PauliFrustrationRepresentation

end SimpleGraph
