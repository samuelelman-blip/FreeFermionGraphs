import FreeFermionGraphs.KrylovTreeMatrix
import FreeFermionGraphs.CliqueBubbleWand
import FreeFermionGraphs.CliqueRootedPathChildren
import FreeFermionGraphs.PauliCliqueHamiltonianKrylovStep
import FreeFermionGraphs.PauliCliqueHamiltonianTerminalContraction

/-!
# Exact one-row decomposition of `[H, h_P]`

This file is the finset form of the one-step expansion in the proof of
Theorem 3 (arXiv 2305.15625v1, Section "Krylov Subspaces", L1507-1514).  In
the Lean convention `[H, ·]` (without the factor `i` of `[iH, ·]`) the
displayed expansion reads, for a rooted induced path `P` of `G* = G + j*`,
```
[H, h_P] = -2 ( Σ_Q T_{PQ} h_Q + Σ_{j ∈ D(P)} h_P h_j + Σ_{j ∈ W(P)} h_P h_j ).
```
v1 splits the sum over `j` into `j ∈ P` (only the terminal vertex `j_ℓ`
anticommutes with `h_P`, giving the contraction `b_{j_ℓ}² h_{P ∖ j_ℓ}`) and
`j ∉ P`, where Lemma `lemma:vertexcyclerelations` (v1 L654, Table
`table:vertexcyclerelations`, L649) leaves three anticommuting cases: (b.iii) a
unit-weight one-vertex extension (announced in the proof but not treated in
v1), (b.i) a Definition 10 clone `j ≺_P k`, whose term cancels against a
deformed path, and (b.iv) a bubble wand `Γ_P(j) = {j_s, j_{s+1}, j_ℓ}` (v1
Definition at L692-698, root handle `s = 0` included).  Here

* `T` is the tree matrix `cliqueTreeMatrix G K b` (extension with weight `1`,
  contraction with weight `b_{terminal}²`; Eq. (decoratedtree), first two cases);
* `D(P) = RootedInducedPath.deformationBubbles P` is the set of clone vertices
  of Definition 10 (case (b.i));
* `W(P) = RootedInducedPath.wandBubbles P` is the set of bubbles of
  `CliqueBubbleWand`s on `P` (case (b.iv)), odd and even hoops together; the
  parity enters later.

The exactness statement of the package is also proved: the original vertices
anticommuting with `h_P` are partitioned into the terminal vertex, the
terminal extensions, `D(P)` and `W(P)`
(`mem_anticommutingOriginalVertices_iff_cases` and the pairwise
disjointness lemmas).

Main declarations.

* `RootedInducedPath.deformationBubbles`, `RootedInducedPath.wandBubbles`,
  `RootedInducedPath.childVertices`, `RootedInducedPath.terminalOriginalVertices`;
* `RootedInducedPath.disjoint_deformationBubbles_wandBubbles`;
* `RootedInducedPath.mem_anticommutingOriginalVertices_iff_cases`
  (exhaustiveness) together with the disjointness of the four classes;
* `PauliCliqueHamiltonianRepresentation.sum_cliqueTreeMatrix_smul_pathOperator`:
  `Σ_Q T_{PQ} h_Q` is the sum of `h_P h_j` over the children `j` of `P` plus the
  terminal term `h_P h_{j_ℓ} = b_{j_ℓ}² h_{P ∖ j_ℓ}`;
* `PauliCliqueHamiltonianRepresentation.commutator_pathOperator_decomposition`.

Fidelity.  This is the literal content of v1 L1507-1514, with the corrections
of the printed proof: the inductive display there drops the factor `(-2i)^m`
and uses `[iH, h_P]` where `[H, h_P]` is meant (so `-2i` becomes `-2` below),
and case (b.iii) is treated here.  The statement needs no premise beyond the
manuscript setup: `K` a simplicial clique and `G` claw-free (the setting of
Theorem 3).
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

/-! ### Anticommutation of the three non-wand classes -/

namespace IndexedInducedPath

variable {H : SimpleGraph V}

/-- A Definition 10 clone `s` of the internal vertex `P_i` has exactly the
three path neighbours `P_{i-1}, P_i, P_{i+1}`, so `h_s` anticommutes with the
path operator. -/
theorem SingleVertexDeformation.anticommutesWith
    {P : IndexedInducedPath H} {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) : P.AnticommutesWith s := by
  have hl := h.internal_left
  have hr := h.internal_right
  have hset : P.neighborIndexSet s =
      {⟨i.val - 1, by omega⟩, i, ⟨i.val + 1, hr⟩} := by
    ext q
    rw [IndexedInducedPath.mem_neighborIndexSet, h.adj_iff q, P.adj_iff i q]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
    omega
  have hcard : (P.neighborIndexSet s).ncard = 3 := by
    rw [hset, Set.ncard_eq_three]
    refine ⟨⟨i.val - 1, by omega⟩, i, ⟨i.val + 1, hr⟩, ?_, ?_, ?_, rfl⟩
    · intro h'
      have := congrArg Fin.val h'
      simp only at this
      omega
    · intro h'
      have := congrArg Fin.val h'
      simp only at this
      omega
    · intro h'
      have := congrArg Fin.val h'
      simp only at this
      omega
  apply (P.anticommutesWith_iff_neighborIndexSet_mod_eq_one s).2
  omega

/-- A terminal extension vertex has exactly one path neighbour (the terminal
vertex), so `h_s` anticommutes with the path operator. -/
theorem TerminalExtensionData.anticommutesWith
    {P : IndexedInducedPath H} {s : V} (h : P.TerminalExtensionData s) :
    P.AnticommutesWith s := by
  have hpos := P.nonempty
  apply P.anticommutesWith_of_unique_neighbor
    (i := ⟨P.card - 1, by omega⟩)
  · exact (h.adj_iff _).2 (by simp only; omega)
  · intro q hq
    apply Fin.ext
    have := (h.adj_iff q).1 hq
    simp only
    omega

end IndexedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-! ### The four classes of anticommuting original vertices -/

namespace RootedInducedPath

/-- The original vertices that are the terminal vertex of `P` (at most one). -/
noncomputable def terminalOriginalVertices [Fintype V]
    (P : CliqueRootedInducedPath G K) : Finset V := by
  classical
  exact Finset.univ.filter (fun j => P.terminalVertex = some j)

/-- The children `x ∈ C(P)` of `P` in the induced-path tree, as a finset:
the vertices `x` with `P + x` an induced path (case (b.iii)). -/
noncomputable def childVertices [Fintype V]
    (P : CliqueRootedInducedPath G K) : Finset V := by
  classical
  exact Finset.univ.filter (fun j => P.path.TerminalExtensionData (some j))

/-- The clone vertices `D(P)` of `P` (v1 Definition 10, case (b.i)): original
vertices that are a single-vertex deformation of some path vertex. -/
noncomputable def deformationBubbles [Fintype V]
    (P : CliqueRootedInducedPath G K) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun j => ∃ i : Fin P.path.card, P.path.SingleVertexDeformation (some j) i)

/-- The wand bubbles `W(P)` of `P` (v1 Definition 11, case (b.iv), root handle
included): original vertices that are the bubble of a `CliqueBubbleWand` on
`P`, with any hoop parity. -/
noncomputable def wandBubbles [Fintype V]
    (P : CliqueRootedInducedPath G K) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun j => ∃ w : CliqueBubbleWand G K P, w.bubble = j)

variable [Fintype V]

@[simp]
theorem mem_terminalOriginalVertices (P : CliqueRootedInducedPath G K) (j : V) :
    j ∈ P.terminalOriginalVertices ↔ P.terminalVertex = some j := by
  classical
  simp [terminalOriginalVertices]

@[simp]
theorem mem_childVertices (P : CliqueRootedInducedPath G K) (j : V) :
    j ∈ P.childVertices ↔ P.path.TerminalExtensionData (some j) := by
  classical
  simp [childVertices]

@[simp]
theorem mem_deformationBubbles (P : CliqueRootedInducedPath G K) (j : V) :
    j ∈ P.deformationBubbles ↔
      ∃ i : Fin P.path.card, P.path.SingleVertexDeformation (some j) i := by
  classical
  simp [deformationBubbles]

@[simp]
theorem mem_wandBubbles (P : CliqueRootedInducedPath G K) (j : V) :
    j ∈ P.wandBubbles ↔ ∃ w : CliqueBubbleWand G K P, w.bubble = j := by
  classical
  simp [wandBubbles]

/-- A wand bubble is never a clone: the clone set and the wand set are
disjoint (a clone has three consecutive path neighbours, a wand does not). -/
theorem disjoint_deformationBubbles_wandBubbles
    (P : CliqueRootedInducedPath G K) :
    Disjoint P.deformationBubbles P.wandBubbles := by
  rw [Finset.disjoint_left]
  intro j hjD hjW
  obtain ⟨i, hi⟩ := (mem_deformationBubbles P j).1 hjD
  obtain ⟨w, rfl⟩ := (mem_wandBubbles P j).1 hjW
  exact w.not_singleVertexDeformation i hi

/-- The terminal vertex of `P` is not a terminal extension (it lies on `P`). -/
theorem disjoint_terminalOriginalVertices_childVertices
    (P : CliqueRootedInducedPath G K) :
    Disjoint P.terminalOriginalVertices P.childVertices := by
  rw [Finset.disjoint_left]
  intro j hjT hjE
  have hT := (mem_terminalOriginalVertices P j).1 hjT
  exact ((mem_childVertices P j).1 hjE).outside ⟨_, hT⟩

/-- The terminal vertex of `P` is not a clone. -/
theorem disjoint_terminalOriginalVertices_deformationBubbles
    (P : CliqueRootedInducedPath G K) :
    Disjoint P.terminalOriginalVertices P.deformationBubbles := by
  rw [Finset.disjoint_left]
  intro j hjT hjD
  have hT := (mem_terminalOriginalVertices P j).1 hjT
  obtain ⟨i, hi⟩ := (mem_deformationBubbles P j).1 hjD
  exact hi.outside ⟨_, hT⟩

/-- The terminal vertex of `P` is not a wand bubble. -/
theorem disjoint_terminalOriginalVertices_wandBubbles
    (P : CliqueRootedInducedPath G K) :
    Disjoint P.terminalOriginalVertices P.wandBubbles := by
  rw [Finset.disjoint_left]
  intro j hjT hjW
  have hT := (mem_terminalOriginalVertices P j).1 hjT
  obtain ⟨w, rfl⟩ := (mem_wandBubbles P j).1 hjW
  exact w.terminalVertex_ne hT

/-- A terminal extension is not a clone: it has one path neighbour, a clone has
three. -/
theorem disjoint_childVertices_deformationBubbles
    (P : CliqueRootedInducedPath G K) :
    Disjoint P.childVertices P.deformationBubbles := by
  rw [Finset.disjoint_left]
  intro j hjE hjD
  have hE := (mem_childVertices P j).1 hjE
  obtain ⟨i, hi⟩ := (mem_deformationBubbles P j).1 hjD
  have h1 := (hE.adj_iff i).1 ((hi.adj_iff i).2 (Or.inl rfl))
  have h2 := hi.internal_right
  omega

/-- A terminal extension is not a wand bubble. -/
theorem disjoint_childVertices_wandBubbles
    (P : CliqueRootedInducedPath G K) :
    Disjoint P.childVertices P.wandBubbles := by
  rw [Finset.disjoint_left]
  intro j hjE hjW
  obtain ⟨w, rfl⟩ := (mem_wandBubbles P j).1 hjW
  exact w.not_terminalExtensionData ((mem_childVertices P w.bubble).1 hjE)

omit [Fintype V] in
/-- The terminal vertex of `P` anticommutes with `h_P`. -/
theorem anticommutesWith_of_terminalVertex_eq
    {P : CliqueRootedInducedPath G K} {j : V}
    (h : P.terminalVertex = some j) : P.path.AnticommutesWith (some j) := by
  have htwo := P.card_two_of_terminalVertex_eq_some (j := j) h
  have := P.path.terminalVertex_anticommutesWith htwo
  rwa [show P.path.terminalVertex = some j from h] at this

/-- Exhaustiveness (v1 Table 1, cases (b) and the terminal contraction): for a
simplicial clique `K` and claw-free `G`, an original vertex `j` anticommutes
with `h_P` exactly when it is the terminal vertex of `P`, a terminal
extension, a Definition 10 clone, or a wand bubble.  The four classes are
pairwise disjoint (`disjoint_*` lemmas). -/
theorem mem_anticommutingOriginalVertices_iff_cases
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (j : V) :
    j ∈ PauliCliqueHamiltonianRepresentation.anticommutingOriginalVertices P ↔
      j ∈ P.terminalOriginalVertices ∨ j ∈ P.childVertices ∨
        j ∈ P.deformationBubbles ∨ j ∈ P.wandBubbles := by
  rw [PauliCliqueHamiltonianRepresentation.mem_anticommutingOriginalVertices]
  simp only [mem_terminalOriginalVertices, mem_childVertices,
    mem_deformationBubbles, mem_wandBubbles]
  constructor
  · intro hanti
    by_cases hT : P.terminalVertex = some j
    · exact Or.inl hT
    by_cases hE : P.path.TerminalExtensionData (some j)
    · exact Or.inr (Or.inl hE)
    by_cases hD : ∃ i : Fin P.path.card, P.path.SingleVertexDeformation (some j) i
    · exact Or.inr (Or.inr (Or.inl hD))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hD' : ∀ i, ¬ P.path.SingleVertexDeformation (some j) i := by
        intro i hi
        exact hD ⟨i, hi⟩
      exact (P.exists_cliqueBubbleWand_iff hK hclaw j).2 ⟨hanti, hT, hE, hD'⟩
  · rintro (hT | hE | ⟨i, hi⟩ | hW)
    · exact anticommutesWith_of_terminalVertex_eq hT
    · exact hE.anticommutesWith
    · exact hi.anticommutesWith
    · exact ((P.exists_cliqueBubbleWand_iff hK hclaw j).1 hW).1

end RootedInducedPath

/-! ### Operator identities for the terminal and extension terms -/

namespace PauliCliqueHamiltonianRepresentation

variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Case (b.iii): a terminal extension `j` of `P` gives `h_P h_j = h_{P + j}`. -/
theorem pathOperator_mul_term_of_terminalExtensionData
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) {j : V}
    (hx : P.path.TerminalExtensionData (some j)) :
    H.pathOperator P * H.operator.term (some j) =
      H.pathOperator (P.appendTerminal hx) := by
  change H.operator.pathOperator P.path * H.operator.term (some j) =
    H.operator.pathOperator (P.appendTerminal hx).path
  rw [H.operator.pathOperator_extension
    (RootedInducedPath.isOneVertexExtension_appendTerminal P hx)]
  congr 2
  exact (RootedInducedPath.terminalVertex_appendTerminal P hx).symm

/-- The terminal term: if `Q` is the predecessor of `P` and `j` the terminal
vertex of `P`, then `h_P h_j = b_j² h_Q`. -/
theorem pathOperator_mul_term_terminal
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P Q : CliqueRootedInducedPath G K} (hQP : Q.IsOneVertexExtension P)
    {j : V} (hterminal : P.terminalVertex = some j) :
    H.pathOperator P * H.operator.term (some j) =
      H.coupling j ^ 2 • H.pathOperator Q := by
  change H.operator.pathOperator P.path * H.operator.term (some j) =
    H.coupling j ^ 2 • H.operator.pathOperator Q.path
  rw [H.operator.pathOperator_extension hQP]
  rw [show P.path.terminalVertex = some j from hterminal]
  rw [mul_assoc, H.original_term_sq, Algebra.smul_def, ← Algebra.commutes]

end PauliCliqueHamiltonianRepresentation

/-! ### The tree part of the row -/

namespace RootedInducedPath

/-- A path has at most one predecessor in the induced-path tree. -/
theorem IsOneVertexExtension.eq_of_extension_right
    {Q Q' P : CliqueRootedInducedPath G K}
    (h : Q.IsOneVertexExtension P) (h' : Q'.IsOneVertexExtension P) :
    Q = Q' := by
  have hcard : Q.path.card = Q'.path.card := by
    have h1 := h.card_eq
    have h2 := h'.card_eq
    omega
  apply ext_path
  apply IndexedInducedPath.ext_of_card_eq_vertex_cast hcard
  intro i
  have hi : i.val < Q.path.card := i.isLt
  have hi' : i.val < Q'.path.card := hcard ▸ hi
  have e1 := h.vertex_of_lt (j := ⟨i.val, by have := h.card_eq; omega⟩) hi
  have e2 := h'.vertex_of_lt (j := ⟨i.val, by have := h'.card_eq; omega⟩) hi'
  exact e1.symm.trans e2

end RootedInducedPath

namespace PauliCliqueHamiltonianRepresentation

variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The tree part of the row.  `Σ_Q T_{PQ} h_Q` is the sum of `h_P h_j` over
the children `j` of `P` (extension arcs, weight `1`) plus the terminal term
`h_P h_{j_ℓ} = b_{j_ℓ}² h_{P ∖ j_ℓ}` (contraction arc, weight `b_{j_ℓ}²`). -/
theorem sum_cliqueTreeMatrix_smul_pathOperator [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) :
    ∑ Q, cliqueTreeMatrix G K H.coupling P Q • H.pathOperator Q =
      (∑ j ∈ P.childVertices, H.pathOperator P * H.operator.term (some j)) +
        ∑ j ∈ P.terminalOriginalVertices,
          H.pathOperator P * H.operator.term (some j) := by
  classical
  -- split each row entry into its extension and contraction parts
  have hsplit : ∀ Q : CliqueRootedInducedPath G K,
      cliqueTreeMatrix G K H.coupling P Q • H.pathOperator Q =
        (if P.IsOneVertexExtension Q then H.pathOperator Q else 0) +
        (if Q.IsOneVertexExtension P then
          (P.terminalVertex.elim 0 (fun j => H.coupling j ^ 2)) •
            H.pathOperator Q else 0) := by
    intro Q
    by_cases h1 : P.IsOneVertexExtension Q
    · rw [cliqueTreeMatrix_of_extension _ h1, if_pos h1,
        if_neg h1.not_reverse, one_smul, add_zero]
    · by_cases h2 : Q.IsOneVertexExtension P
      · rw [cliqueTreeMatrix_of_contraction _ h2, if_neg h1, if_pos h2,
          zero_add]
      · have hn : ¬ P.TreeAdjacent Q := fun h => h.elim h1 h2
        rw [cliqueTreeMatrix_eq_zero_of_not_treeAdjacent _ hn, if_neg h1,
          if_neg h2, zero_smul, add_zero]
  rw [Finset.sum_congr rfl (fun Q _ => hsplit Q), Finset.sum_add_distrib]
  congr 1
  · -- extension arcs: the children of `P`
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun j hj => P.appendTerminal
      ((P.mem_childVertices j).1 hj)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        RootedInducedPath.isOneVertexExtension_appendTerminal P _⟩
    · intro j hj j' hj' hjj'
      have := (RootedInducedPath.appendTerminal_inj
        ((P.mem_childVertices j).1 hj) ((P.mem_childVertices j').1 hj')).1 hjj'
      exact this
    · intro Q hQ
      rw [Finset.mem_filter] at hQ
      obtain ⟨x, hx, rfl⟩ :=
        (P.isOneVertexExtension_iff_exists_appendTerminal Q).1 hQ.2
      exact ⟨x, (P.mem_childVertices x).2 hx, rfl⟩
    · intro j hj
      exact H.pathOperator_mul_term_of_terminalExtensionData P _
  · -- contraction arc: the unique predecessor of `P`
    rcases hT : P.terminalVertex with _ | j0
    · have hempty : P.terminalOriginalVertices = ∅ := by
        ext j
        simp [hT]
      rw [hempty, Finset.sum_empty]
      apply Finset.sum_eq_zero
      intro Q _
      simp
    · have htwo := P.card_two_of_terminalVertex_eq_some (j := j0) hT
      obtain ⟨Q0, hQ0⟩ := P.exists_terminalPredecessor (j := j0) hT
      have hsingle : P.terminalOriginalVertices = {j0} := by
        ext j
        simp [hT, eq_comm]
      rw [hsingle, Finset.sum_singleton,
        H.pathOperator_mul_term_terminal hQ0 hT]
      rw [Finset.sum_eq_single Q0]
      · rw [if_pos hQ0]
        rfl
      · intro Q _ hQ
        rw [if_neg]
        intro hQ'
        exact hQ (hQ'.eq_of_extension_right hQ0)
      · intro h
        exact absurd (Finset.mem_univ Q0) h

end PauliCliqueHamiltonianRepresentation

/-! ### The exact one-row decomposition -/

namespace PauliCliqueHamiltonianRepresentation

variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Exact one-row decomposition of the commutator `[H, h_P]` (v1 L1507-1514,
Theorem 3, in the convention `[H, ·]` instead of `[iH, ·]`):
```
[H, h_P] = -2 ( Σ_Q T_{PQ} h_Q + Σ_{j ∈ D(P)} h_P h_j + Σ_{j ∈ W(P)} h_P h_j ).
```
`T` is the tree matrix (`cliqueTreeMatrix`, weight `1` for children and
`b_t²` for the parent), `D(P)` the clone vertices of Definition 10, `W(P)` the
wand bubbles (Definition 11, all parities, root handle included).  The
deformation terms cancel in pairs and the wand terms against hole terms in
later packages; this statement only reorganizes the exact expansion.

Premises: `K` a simplicial clique and `G` claw-free, the setting of
Theorem 3. -/
theorem commutator_pathOperator_decomposition [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) :
    algebraCommutator H.physicalHamiltonian (H.pathOperator P) =
      ((-1 : A) - 1) * ((∑ Q, cliqueTreeMatrix G K H.coupling P Q • H.pathOperator Q)
        + (∑ j ∈ P.deformationBubbles, H.pathOperator P * H.operator.term (some j))
        + ∑ j ∈ P.wandBubbles, H.pathOperator P * H.operator.term (some j)) := by
  rw [H.commutator_physicalHamiltonian_pathOperator_eq_anticommuting_sum,
    ← Finset.mul_sum, sum_cliqueTreeMatrix_smul_pathOperator]
  congr 1
  classical
  have hunion : anticommutingOriginalVertices P =
      ((P.terminalOriginalVertices ∪ P.childVertices) ∪ P.deformationBubbles) ∪
        P.wandBubbles := by
    ext j
    rw [P.mem_anticommutingOriginalVertices_iff_cases hK hclaw j]
    simp only [Finset.mem_union]
    tauto
  have hd1 : Disjoint P.terminalOriginalVertices P.childVertices :=
    P.disjoint_terminalOriginalVertices_childVertices
  have hd2 : Disjoint (P.terminalOriginalVertices ∪ P.childVertices)
      P.deformationBubbles :=
    Finset.disjoint_union_left.2
      ⟨P.disjoint_terminalOriginalVertices_deformationBubbles,
        P.disjoint_childVertices_deformationBubbles⟩
  have hd3 : Disjoint
      ((P.terminalOriginalVertices ∪ P.childVertices) ∪ P.deformationBubbles)
      P.wandBubbles :=
    Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_left.2
        ⟨P.disjoint_terminalOriginalVertices_wandBubbles,
          P.disjoint_childVertices_wandBubbles⟩,
        P.disjoint_deformationBubbles_wandBubbles⟩
  rw [hunion, Finset.sum_union hd3, Finset.sum_union hd2,
    Finset.sum_union hd1]
  ac_rfl

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
