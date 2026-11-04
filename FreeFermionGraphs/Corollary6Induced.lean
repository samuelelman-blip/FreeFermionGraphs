import FreeFermionGraphs.Corollary6

/-!
# Compatibility of even holes in the induced-union sense

The manuscript (arXiv 2305.15625 v1) uses two inequivalent notions of
"compatible" even holes.

* In the definition of the collection `𝒞^(even)` (v1 line 313), two even holes
  `C`, `C'` are compatible when `G[C ∪ C']` is a disconnected graph whose
  components are `G[C]` and `G[C']`.  For connected hole carriers this says
  exactly that `C ∩ C' = ∅` and there is no edge between `C` and `C'`.  This
  is `EvenHoleInducedCompatible` below.
* In the "Recall" sentence immediately before the compatibility corollary
  (v1 line 748), `C` and `C'` are compatible when `j ∉ Γ[C']` for every
  `j ∈ Γ[C]`, i.e. `Γ[C] ∩ Γ[C'] = ∅`.  This is the strictly stronger notion
  `EvenHoleCompatible` of `FreeFermionGraphs.Corollary6`.

The corollary at v1 line 749 (v1 Corollary 5, repository `corollary6`) is
stated for the second notion.  This file shows that the strong notion implies
the first one, that the converse fails even in claw-free graphs (two
non-adjacent 4-holes together with one vertex adjacent to an edge of each; see
`Corollary6InducedExample`), and that the
corollary also holds for the first notion: for a claw-free graph and
`A ∈ ⟨A₀⟩` with `A₀` the carrier of an alternating labelling, a set `C` is
induced-compatible with `A₀` if and only if it is induced-compatible with `A`.
The key observation is that every carrier occurring in the deformation closure
of a labelling carrier is contained in its own open neighborhood, so that
`C` is induced-compatible with `A` exactly when `C` misses the open
neighborhood of `A`; Lemma 9 (`openNeighborhood_eq`) then transports this
statement along the closure.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The notion of compatibility from the definition of `𝒞^(even)` (v1 line 313):
the induced union `G[A ∪ B]` is the disjoint union of `G[A]` and `G[B]`, i.e.
`A` and `B` are disjoint and no edge joins them.  This is weaker than
`EvenHoleCompatible`, which is the notion recalled at v1 line 748 and asks for
disjoint open neighborhoods. -/
def EvenHoleInducedCompatible (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ ⦃x y : V⦄, x ∈ A → y ∈ B → ¬G.Adj x y

/-- Induced-union compatibility is symmetric. -/
theorem evenHoleInducedCompatible_comm {A B : Set V} :
    G.EvenHoleInducedCompatible A B ↔ G.EvenHoleInducedCompatible B A := by
  constructor
  · rintro ⟨hdisj, hadj⟩
    exact ⟨hdisj.symm, fun x y hx hy hxy => hadj hy hx hxy.symm⟩
  · rintro ⟨hdisj, hadj⟩
    exact ⟨hdisj.symm, fun x y hx hy hxy => hadj hy hx hxy.symm⟩

/-- Induced-union compatibility of `A` and `B` says that `A` is disjoint from `B`
and from every neighbor of `B`.  When `B ⊆ openNeighborhood B` (as for every
carrier occurring in a deformation closure, see
`InEvenHoleDeformationClosure.subset_openNeighborhood`), disjointness from `B`
is implied by disjointness from `openNeighborhood B`, so induced-union
compatibility reduces to `A ∩ openNeighborhood B = ∅`. -/
theorem evenHoleInducedCompatible_iff_disjoint_openNeighborhood
    {A B : Set V} (hB : B ⊆ G.openNeighborhood B) :
    G.EvenHoleInducedCompatible A B ↔ Disjoint A (G.openNeighborhood B) := by
  constructor
  · rintro ⟨-, hadj⟩
    refine Set.disjoint_left.2 ?_
    intro x hxA hxN
    obtain ⟨y, hyB, hxy⟩ := hxN
    exact hadj hxA hyB hxy
  · intro hdisj
    refine ⟨?_, ?_⟩
    · exact hdisj.mono_right hB
    · intro x y hx hy hxy
      exact Set.disjoint_left.1 hdisj hx ⟨y, hy, hxy⟩

/-- The strong compatibility of `A` and `B` (disjoint open neighborhoods)
implies induced-union compatibility, as soon as each set lies in its own open
neighborhood. -/
theorem EvenHoleCompatible.toInducedCompatible_of_subset {A B : Set V}
    (hA : A ⊆ G.openNeighborhood A) (hB : B ⊆ G.openNeighborhood B)
    (h : G.EvenHoleCompatible A B) :
    G.EvenHoleInducedCompatible A B := by
  refine (evenHoleInducedCompatible_iff_disjoint_openNeighborhood hB).2 ?_
  exact h.mono_left hA

namespace EvenHoleLabeling

/-- The carrier of an alternating labelling lies in its own open neighborhood
(`a i ~ b i`). -/
theorem carrier_subset_openNeighborhood {k : Nat} (L : EvenHoleLabeling G k) :
    L.carrier ⊆ G.openNeighborhood L.carrier := fun _ ht =>
  L.mem_openNeighborhood_carrier_of_mem ht

end EvenHoleLabeling

/-- A deformed carrier lies in its own open neighborhood. -/
theorem EvenHoleLabeling.CloneAt.deformedCarrier_subset_openNeighborhood {k : Nat}
    {C : EvenHoleLabeling G k} {s : V} {i : Fin k} (h : C.CloneAt s i) :
    C.deformedCarrier s i ⊆ G.openNeighborhood (C.deformedCarrier s i) := by
  intro t ht
  refine h.mem_openNeighborhood_deformedCarrier_of_mem_insert ?_
  rcases Set.mem_insert_iff.1 ht with rfl | ⟨htC, -⟩
  · exact Set.mem_insert_iff.2 (Or.inl rfl)
  · exact Set.mem_insert_iff.2 (Or.inr htC)

/-- Both ends of a single reversible deformation step lie in their own open
neighborhoods. -/
theorem EvenHoleDeformationStep.subset_openNeighborhood_right
    {A B : Set V} (hstep : EvenHoleDeformationStep G A B) :
    B ⊆ G.openNeighborhood B := by
  rcases hstep with ⟨k, C, s, i, h, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · exact h.deformedCarrier_subset_openNeighborhood
  · exact C.carrier_subset_openNeighborhood

/-- Every carrier in the deformation closure of a carrier that lies in its own
open neighborhood again lies in its own open neighborhood. -/
theorem InEvenHoleDeformationClosure.subset_openNeighborhood
    {A B : Set V} (hclosure : InEvenHoleDeformationClosure G A B)
    (hA : A ⊆ G.openNeighborhood A) :
    B ⊆ G.openNeighborhood B := by
  induction hclosure with
  | refl => exact hA
  | tail _ hstep _ => exact hstep.subset_openNeighborhood_right

/-- The strong notion (`EvenHoleCompatible`, v1 line 748) implies the notion
from the definition of `𝒞^(even)` (v1 line 313) for alternating even-hole
carriers.  The converse fails, see
`exists_evenHoleInducedCompatible_not_evenHoleCompatible`. -/
theorem EvenHoleCompatible.toInducedCompatible {k k' : ℕ} {L : G.EvenHoleLabeling k}
    {L' : G.EvenHoleLabeling k'} (h : G.EvenHoleCompatible L.carrier L'.carrier) :
    G.EvenHoleInducedCompatible L.carrier L'.carrier :=
  h.toInducedCompatible_of_subset L.carrier_subset_openNeighborhood
    L'.carrier_subset_openNeighborhood

/-- Corollary 5 of v1 (v1 line 749; repository Corollary 6) for the
induced-union notion of compatibility of v1 line 313: if `A₀` is the carrier of
an alternating labelling and `A ∈ ⟨A₀⟩`, then in a claw-free graph a set `C` is
induced-compatible with `A₀` if and only if it is induced-compatible with `A`.
-/
theorem InEvenHoleDeformationClosure.evenHoleInducedCompatible_right_iff {k : ℕ}
    {L : G.EvenHoleLabeling k} {B C : Set V}
    (hclosure : InEvenHoleDeformationClosure G L.carrier B) (hclaw : G.IsClawFree) :
    G.EvenHoleInducedCompatible C L.carrier ↔ G.EvenHoleInducedCompatible C B := by
  rw [evenHoleInducedCompatible_iff_disjoint_openNeighborhood
      L.carrier_subset_openNeighborhood,
    evenHoleInducedCompatible_iff_disjoint_openNeighborhood
      (hclosure.subset_openNeighborhood L.carrier_subset_openNeighborhood),
    hclosure.openNeighborhood_eq hclaw]

/-- Corollary 5 of v1 (v1 line 749; repository Corollary 6), for the induced-union
notion of compatibility of v1 line 313: if `C` is compatible with the carrier
`A₀` of an alternating labelling, then `C` is compatible with every carrier in
the deformation closure `⟨A₀⟩`.  (The set `C` need not itself be an even hole.) -/
theorem corollary6_induced {k : ℕ} {L : G.EvenHoleLabeling k} {B C : Set V}
    (hclosure : InEvenHoleDeformationClosure G L.carrier B)
    (hclaw : G.IsClawFree)
    (hcompat : G.EvenHoleInducedCompatible C L.carrier) :
    G.EvenHoleInducedCompatible C B :=
  (hclosure.evenHoleInducedCompatible_right_iff hclaw).mp hcompat

/-! ### The converse fails

Two non-adjacent 4-holes `{0,1,2,3}` and `{4,5,6,7}` together with one vertex
`8` adjacent to the edge `{0,1}` of the first and the edge `{4,5}` of the
second give a claw-free graph in which the two holes are compatible in the
induced-union sense of v1 line 313 but not in the sense of v1 line 748. -/

namespace Corollary6InducedExample

/-- The edges of the example graph: the 4-holes `0-1-2-3-0` and `4-5-6-7-4`, and the
vertex `8` adjacent to `0`, `1`, `4`, `5`. -/
def edgeList : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(0,3),(4,5),(5,6),(6,7),(4,7),(8,0),(8,1),(8,4),(8,5)]

/-- The nine-vertex example graph. -/
def graph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel (fun x y : Fin 9 => (x.val, y.val) ∈ edgeList)

instance : DecidableRel graph.Adj := fun x y => by unfold graph; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The example graph is claw-free. -/
theorem clawFree : graph.IsClawFree := by
  have h : ∀ center a b c : Fin 9, graph.Adj center a → graph.Adj center b → graph.Adj center c →
      a ≠ b → a ≠ c → b ≠ c → graph.Adj a b ∨ graph.Adj a c ∨ graph.Adj b c := by
    decide +kernel
  exact fun center a b c => h center a b c

/-- An alternating labelling with `k = 2` (a 4-hole) of the example graph, from
explicit colour classes `a`, `b`. -/
def labelling (a b : Fin 2 → Fin 9)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hdis : ∀ i j, a i ≠ b j)
    (haa : ∀ i j, ¬graph.Adj (a i) (a j)) (hbb : ∀ i j, ¬graph.Adj (b i) (b j))
    (hab : ∀ i j : Fin 2, graph.Adj (a i) (b j) ↔ j = i ∨ j = i + 1) : graph.EvenHoleLabeling 2 where
  two_le := le_rfl
  a := a
  b := b
  next := fun i => i + 1
  prev := fun i => i + 1
  next_ne := by decide
  next_next_ne := by intro h; omega
  next_prev := by decide
  prev_next := by decide
  a_injective := ha
  b_injective := hb
  color_disjoint := hdis
  adj_aa := haa
  adj_bb := hbb
  adj_ab_iff := hab

/-- The labelling of the 4-hole `0-1-2-3-0`. -/
def L₁ : graph.EvenHoleLabeling 2 :=
  labelling (fun i => if i = 0 then 0 else 2) (fun i => if i = 0 then 1 else 3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The labelling of the 4-hole `4-5-6-7-4`. -/
def L₂ : graph.EvenHoleLabeling 2 :=
  labelling (fun i => if i = 0 then 4 else 6) (fun i => if i = 0 then 5 else 7) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The carrier of `L₁`. -/
theorem carrier₁ : L₁.carrier = {x | x.val < 4} := by
  ext x
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp [L₁, labelling]
  · intro hx
    fin_cases x <;> simp at hx <;> simp [EvenHoleLabeling.carrier, L₁, labelling]

/-- The carrier of `L₂`. -/
theorem carrier₂ : L₂.carrier = {x | 4 ≤ x.val ∧ x.val < 8} := by
  ext x
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i <;> simp [L₂, labelling]
  · intro hx
    fin_cases x <;> simp at hx <;> simp [EvenHoleLabeling.carrier, L₂, labelling]

/-- The two holes are compatible in the induced-union sense. -/
theorem inducedCompatible : graph.EvenHoleInducedCompatible L₁.carrier L₂.carrier := by
  rw [carrier₁, carrier₂]
  refine ⟨?_, ?_⟩
  · refine Set.disjoint_left.2 ?_
    intro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    omega
  · intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    have h : ∀ x y : Fin 9, x.val < 4 → 4 ≤ y.val → y.val < 8 → ¬ graph.Adj x y := by decide
    exact h x y hx hy.1 hy.2

/-- The two holes are not compatible in the sense of disjoint open neighborhoods:
the vertex `8` is a common neighbor. -/
theorem not_compatible : ¬ graph.EvenHoleCompatible L₁.carrier L₂.carrier := by
  intro h
  have h8 : (8 : Fin 9) ∈ graph.openNeighborhood L₁.carrier ∩ graph.openNeighborhood L₂.carrier := by
    refine ⟨⟨0, ?_, ?_⟩, ⟨4, ?_, ?_⟩⟩
    · rw [carrier₁]; decide
    · decide
    · rw [carrier₂]; decide
    · decide
  exact Set.disjoint_left.1 h h8.1 h8.2

end Corollary6InducedExample

/-- The converse of `EvenHoleCompatible.toInducedCompatible` fails, even in
claw-free graphs: the notion of v1 line 313 is strictly weaker than the notion
recalled at v1 line 748.  The witness is the 9-vertex graph consisting of two
non-adjacent 4-holes and one further vertex adjacent to an edge of each. -/
theorem exists_evenHoleInducedCompatible_not_evenHoleCompatible :
    ∃ (G : SimpleGraph (Fin 9)) (L L' : G.EvenHoleLabeling 2),
      G.IsClawFree ∧ G.EvenHoleInducedCompatible L.carrier L'.carrier ∧
        ¬G.EvenHoleCompatible L.carrier L'.carrier :=
  ⟨Corollary6InducedExample.graph, Corollary6InducedExample.L₁,
    Corollary6InducedExample.L₂, Corollary6InducedExample.clawFree,
    Corollary6InducedExample.inducedCompatible,
    Corollary6InducedExample.not_compatible⟩

end SimpleGraph
