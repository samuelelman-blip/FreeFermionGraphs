import FreeFermionGraphs.T3FixedPairing
import FreeFermionGraphs.T3PairingIndex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The pairing index is invariant along a palindromic deformation

This module proves that the pairing index `Ψ` of `FreeFermionGraphs.T3PairingIndex` does not
change when both hole-class states are moved along a palindromic fixed-pairing-type deformation:
for `D : G.FPDeformation s s'` with `D.Palindromic`,
`Ψ(D.fwdEnd, D.bwdEnd) = Ψ(s, s')`  (`SimpleGraph.FPDeformation.pairingIndex_ends`).

## Relation to v1

v1 (arXiv 2305.15625 v1, Definition 21 `definition:obstructiongraphcoloringclasses`, L1017) takes
as the *source set* of the obstruction graph the coloring class of larger size, i.e. a majority
vote over pairing types, and the search process (L1158-1191) removes one vertex of the source set
and one of the obstruction set at each rerouting, so that the source set stays the larger class.
`Ψ` computes this majority vote (the count formula is the business of
`FreeFermionGraphs.T3PairingIndexCount`; it is not used here).  The statement proved here is what
makes the vote a *toggle invariant*: the palindromic deformation `D` replaces the pair of hole
classes `(s, s')` by `(D.fwdEnd, D.bwdEnd)`, and the sign of `Ψ` selects the same pairing in both.
v1 contains no counterpart of this identity; it is new relative to the manuscript and no claim of
v1 depends on its proof.  Neither claw-freeness nor any property of `W` is used.

## Main results

* `SimpleGraph.pairingForm G f g = Σ_{x, y} f(x) g(y) (A + 2 I)_{x y}`: the bilinear form behind
  `Ψ`, on arbitrary integer-valued functions on the vertices
  (`pairingIndex_eq_pairingForm`: `Ψ(s, s') = pairingForm (χ_s) (χ_{s'})`), with its bilinearity
  and symmetry.
* `SimpleGraph.pairingForm_clone`: the clone identity.  If `j ≺_X k` (`IsCloneIn`) and `f` vanishes
  off `X`, then `pairingForm (e_j - e_k) f = -f(k)`.  This is where the matrix `A + 2 I` (rather
  than `A`) enters: for `v = k` the entry of `A + 2 I` at `(j, k)` is `1` and at `(k, k)` is `2`.
* `SimpleGraph.FormMatched t t₁ t' t'f` is the bookkeeping predicate of the telescoping argument.
  For a forward run `t ⟶ t₁` and a backward run `t' ⟶ t'f` (on the reversed word; `t'` is the
  *start* of the backward run) it says `χ_{t'f} = χ_{t'} - (χ_{t₁} - χ_t)` and
  `⟨χ_{t₁} - χ_t, χ_{t₁} - χ_{t'}⟩ = 0`, where `⟨·, ·⟩` is `pairingForm`.  It implies
  `Ψ(t₁, t'f) = Ψ(t, t')` (`FormMatched.pairingIndex_eq`).  `FormMatched.trans` composes two such
  pieces, and `FormMatched.of_step` is the one-step case.
* `SimpleGraph.OddBlock.formMatched_fst` / `formMatched_snd`: a block of the first (second) class
  run forward from `t` and backward from `t'` is matched.  The proof goes through the auxiliary
  run relation `FstClassRun`, in which every step replaces a vertex of the first class.
* `SimpleGraph.SideBlock.formMatched_flatMap`: the same for a list of side blocks with distinct
  supports, by induction on the list, using the end-state computation
  `SideBlock.eq_of_classRun_flatMap` of `FreeFermionGraphs.T3FixedPairing` for the blocks which
  have run on the other side.
* `SimpleGraph.FPDeformation.pairingIndex_ends`: the theorem.

## Proof

Write the word of `D` as `(j_1, k_1), …, (j_n, k_n)`, let `σ_t` be the forward states (`σ_0 = s`,
`σ_n = D.fwdEnd`) and `τ_t` the backward states (`τ_n = s'`, `τ_0 = D.bwdEnd`; `τ_t` is the state
from which the reversed step `(k_t, j_t)` is taken), and let
`δ_t = χ_{σ_t} - χ_{σ_{t-1}} = ±(e_{j_t} - e_{k_t})`, the sign being `+` if the step replaces a
vertex of the first class and `-` for the second.  The clone relations at the forward step
`j_t ≺ k_t` (in `σ_{t-1}`) and at the backward step `k_t ≺ j_t` (in `τ_t`) give

* `⟨δ_t, χ_{σ_{t-1}}⟩ = -1`, `⟨δ_t, χ_{τ_t}⟩ = +1`, `⟨δ_t, δ_t⟩ = 2`.

The second needs that the backward step takes place in the *same* class as the forward step.  This
is the matching of the blocks of `D` with the blocks of the mirrored deformation (a block of
`C_a ⊕ C'_c` is read backwards as a block of `C'_c ⊕ C_a`): the steps of a first-class block are
`ClassStep.a` in both runs (`FstClassRun.of_classRun`), and those of a second-class block are
`ClassStep.b` in both (by exchanging the classes).  Hence
`⟨δ_t, χ_{σ_t} - χ_{τ_t}⟩ = (-1 + 2) - 1 = 0`.  Now `χ_{σ_t} - χ_{τ_t} = χ_{D.fwdEnd} - χ_{s'}` does
not depend on `t`, so the total change `Δ = Σ_t δ_t = χ_{D.fwdEnd} - χ_s` satisfies
`⟨Δ, χ_{D.fwdEnd} - χ_{s'}⟩ = 0`, and `χ_{D.bwdEnd} = χ_{s'} - Δ`.  Expanding
`Ψ(D.fwdEnd, D.bwdEnd) = ⟨χ_s + Δ, χ_{s'} - Δ⟩` bilinearly and using the symmetry of the form gives
`Ψ(s, s')` (`FormMatched.pairingIndex_eq`).  The formalisation carries out the sum over `t` by
induction (`FormMatched.trans`), peeling off one step (`FstClassRun.formMatched`) or one block
(`SideBlock.formMatched_flatMap`) at a time.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### The bilinear form behind `Ψ` -/

section PairingForm

variable [DecidableEq V]

/-- The matrix `A + 2 I` of `G`, as an integer-valued function of a pair of vertices.  The
definition is noncomputable so that no choice of decidable adjacency is carried as data (compare
`SimpleGraph.pairingIndex`). -/
noncomputable def pairingMat (G : SimpleGraph V) (x y : V) : ℤ := by
  classical
  exact (if G.Adj x y then 1 else 0) + (if x = y then 2 else 0)

theorem pairingMat_comm (x y : V) : G.pairingMat x y = G.pairingMat y x := by
  classical
  unfold pairingMat
  have hxy : (if x = y then (2 : ℤ) else 0) = if y = x then 2 else 0 := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  have hadj : (if G.Adj x y then (1 : ℤ) else 0) = if G.Adj y x then 1 else 0 := by
    simp only [G.adj_comm x y]
  rw [hxy, hadj]

/-- The diagonal entries of `A + 2 I` are `2`. -/
theorem pairingMat_self (x : V) : G.pairingMat x x = 2 := by
  classical
  simp [pairingMat]

/-- The entry of `A + 2 I` at an edge is `1`. -/
theorem pairingMat_of_adj {x y : V} (h : G.Adj x y) : G.pairingMat x y = 1 := by
  classical
  have : x ≠ y := h.ne
  simp [pairingMat, h, this]

/-- The entry of `A + 2 I` at a pair of distinct non-adjacent vertices is `0`. -/
theorem pairingMat_of_not_adj {x y : V} (h : ¬ G.Adj x y) (hne : x ≠ y) :
    G.pairingMat x y = 0 := by
  classical
  simp [pairingMat, h, hne]

variable [Fintype V]

/-- The symmetric bilinear form `⟨f, g⟩ = Σ_{x, y} f(x) g(y) (A + 2 I)_{x y}` on integer-valued
functions on the vertices; `Ψ(s, s') = ⟨χ_s, χ_{s'}⟩` (`pairingIndex_eq_pairingForm`). -/
noncomputable def pairingForm (G : SimpleGraph V) (f g : V → ℤ) : ℤ :=
  ∑ x, ∑ y, f x * g y * G.pairingMat x y

/-- The pairing index is the bilinear form on the sign functions of the two class pairs. -/
theorem pairingIndex_eq_pairingForm (s s' : Finset V × Finset V) :
    G.pairingIndex s s' = G.pairingForm (classSign s) (classSign s') := by
  unfold pairingIndex pairingForm pairingMat
  convert rfl

theorem pairingForm_comm (f g : V → ℤ) : G.pairingForm f g = G.pairingForm g f := by
  unfold pairingForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [pairingMat_comm x y]
  ring

theorem pairingForm_add_left (f f' g : V → ℤ) :
    G.pairingForm (f + f') g = G.pairingForm f g + G.pairingForm f' g := by
  unfold pairingForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.add_apply]
  ring

theorem pairingForm_sub_left (f f' g : V → ℤ) :
    G.pairingForm (f - f') g = G.pairingForm f g - G.pairingForm f' g := by
  unfold pairingForm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem pairingForm_neg_left (f g : V → ℤ) :
    G.pairingForm (-f) g = -G.pairingForm f g := by
  unfold pairingForm
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.neg_apply]
  ring

theorem pairingForm_zero_left (g : V → ℤ) : G.pairingForm 0 g = 0 := by
  simp [pairingForm]

theorem pairingForm_add_right (f g g' : V → ℤ) :
    G.pairingForm f (g + g') = G.pairingForm f g + G.pairingForm f g' := by
  rw [pairingForm_comm, pairingForm_add_left, pairingForm_comm g, pairingForm_comm g' f]

theorem pairingForm_sub_right (f g g' : V → ℤ) :
    G.pairingForm f (g - g') = G.pairingForm f g - G.pairingForm f g' := by
  rw [pairingForm_comm, pairingForm_sub_left, pairingForm_comm g, pairingForm_comm g' f]

theorem pairingForm_neg_right (f g : V → ℤ) :
    G.pairingForm f (-g) = -G.pairingForm f g := by
  rw [pairingForm_comm, pairingForm_neg_left, pairingForm_comm]

theorem pairingForm_zero_right (f : V → ℤ) : G.pairingForm f 0 = 0 := by
  rw [pairingForm_comm, pairingForm_zero_left]

theorem pairingForm_neg_neg (f g : V → ℤ) : G.pairingForm (-f) (-g) = G.pairingForm f g := by
  rw [pairingForm_neg_left, pairingForm_neg_right, neg_neg]

/-- Pairing the basis vector `e_j` with a function evaluates the `j`-th row of `A + 2 I`. -/
theorem pairingForm_single_left (j : V) (g : V → ℤ) :
    G.pairingForm (Pi.single j 1) g = ∑ y, g y * G.pairingMat j y := by
  unfold pairingForm
  rw [Finset.sum_eq_single j]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

/-- The matrix entry `⟨e_a, e_b⟩ = (A + 2 I)_{a b}`. -/
theorem pairingForm_single_single (a b : V) :
    G.pairingForm (Pi.single a 1) (Pi.single b 1) = G.pairingMat a b := by
  rw [pairingForm_single_left, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- The clone identity: if `j ≺_X k` and `f` vanishes off `X`, then
`⟨e_j - e_k, f⟩ = -f(k)`.

For `v ∈ X` with `v ≠ k` the rows of `A + 2 I` at `j` and at `k` agree at `v` (`j ≺_X k` says that
`j` and `k` have the same neighbours in `X ∖ {k}`, and `v ≠ j`, `v ≠ k` kill the `2 I` part); at
`v = k` the entries are `1` (as `j ~ k`) and `2`. -/
theorem pairingForm_clone {X : Set V} {j k : V} (hcl : G.IsCloneIn X j k) (f : V → ℤ)
    (hf : ∀ v, v ∉ X → f v = 0) :
    G.pairingForm (Pi.single j 1 - Pi.single k 1) f = -f k := by
  obtain ⟨hjX, hkX, hadj⟩ := hcl
  have hjk : j ≠ k := fun h => hjX (h ▸ hkX)
  rw [pairingForm_sub_left, pairingForm_single_left, pairingForm_single_left,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
  · have hadjk : G.Adj j k := (hadj k hkX).2 (Or.inl rfl)
    rw [pairingMat_of_adj hadjk, pairingMat_self]
    ring
  · intro y _ hy
    by_cases hyX : y ∈ X
    · have hyj : y ≠ j := fun h => hjX (h ▸ hyX)
      have hiff : G.Adj j y ↔ G.Adj k y := by
        rw [hadj y hyX]
        constructor
        · rintro (h | h)
          · exact absurd h hy
          · exact h
        · exact Or.inr
      have : G.pairingMat j y = G.pairingMat k y := by
        by_cases h : G.Adj j y
        · rw [pairingMat_of_adj h, pairingMat_of_adj (hiff.1 h)]
        · rw [pairingMat_of_not_adj h hyj.symm,
            pairingMat_of_not_adj (fun h' => h (hiff.2 h')) (Ne.symm hy)]
      rw [this]
      ring
    · rw [hf y hyX]
      ring
  · simp

end PairingForm

/-! ### Runs which only replace vertices of the first class -/

section FstClassRun

variable [DecidableEq V]

/-- A clone run all of whose steps replace a vertex of the *first* class (`ClassStep.a`).  A block
of the first class `G[C_a ⊕ C'_c]`, run forward from a state containing its removed vertices in the
first class, and its mirror image, run backward, are such runs. -/
inductive FstClassRun (G : SimpleGraph V) :
    Finset V × Finset V → List (V × V) → Finset V × Finset V → Prop
  | nil (s : Finset V × Finset V) : FstClassRun G s [] s
  | cons {A B : Finset V} {j k : V} {w : List (V × V)} {s'' : Finset V × Finset V} :
      G.IsCloneIn ↑(A ∪ B) j k → k ∈ A → FstClassRun G (insert j (A.erase k), B) w s'' →
      FstClassRun G (A, B) ((j, k) :: w) s''

namespace FstClassRun

variable {s t : Finset V × Finset V} {w : List (V × V)}

/-- A first-class run is a clone run. -/
theorem classRun (h : G.FstClassRun s w t) : G.ClassRun s w t := by
  induction h with
  | nil s => exact ClassRun.nil s
  | cons hcl hk _ ih => exact ClassRun.cons (ClassStep.a hcl hk) ih

/-- The two classes stay disjoint along a first-class run. -/
theorem disjoint (h : G.FstClassRun s w t) : Disjoint s.1 s.2 → Disjoint t.1 t.2 := by
  induction h with
  | nil s => exact id
  | @cons A B j k w s'' hcl hk _ ih =>
    intro hd
    refine ih ?_
    have hjB : j ∉ B := fun h => hcl.1 (by simp [h])
    refine Finset.disjoint_left.2 fun x hx hxB => ?_
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hjB hxB
    · exact Finset.disjoint_left.1 hd (Finset.mem_of_mem_erase hx) hxB

/-- A first-class run on a concatenated word factors through an intermediate state. -/
theorem exists_of_append {w₁ w₂ : List (V × V)} (h : G.FstClassRun s (w₁ ++ w₂) t) :
    ∃ u, G.FstClassRun s w₁ u ∧ G.FstClassRun u w₂ t := by
  induction w₁ generalizing s with
  | nil => exact ⟨s, FstClassRun.nil s, by simpa using h⟩
  | cons p w ih =>
    rw [List.cons_append] at h
    cases h with
    | cons hcl hk hrest =>
      obtain ⟨u, h₁, h₂⟩ := ih hrest
      exact ⟨u, FstClassRun.cons hcl hk h₁, h₂⟩

/-- A clone run out of a state with disjoint classes, on a word without repeated vertices and
whose removed vertices all lie in the first class, is a first-class run: no step can be a
`ClassStep.b`, since the removed vertex would lie in both classes. -/
theorem of_classRun (h : G.ClassRun s w t) (hd : Disjoint s.1 s.2)
    (hk : ∀ p ∈ w, p.2 ∈ s.1) (hnd : (wordVertices w).Nodup) : G.FstClassRun s w t := by
  induction h with
  | nil s => exact FstClassRun.nil s
  | @cons s s₁ s₂ p w hstep hrun ih =>
    obtain ⟨j, k⟩ := p
    have hnd' : (j :: k :: wordVertices w).Nodup := by simpa using hnd
    have hkw : k ∉ wordVertices w := (List.nodup_cons.1 (List.nodup_cons.1 hnd').2).1
    have hnd'' : (wordVertices w).Nodup := (List.nodup_cons.1 (List.nodup_cons.1 hnd').2).2
    cases hstep with
    | b hcl hkB =>
      exact absurd hkB (Finset.disjoint_left.1 hd (hk (j, k) (List.mem_cons_self ..)))
    | @a A B j k hcl hkA =>
      have hjB : j ∉ B := fun h => hcl.1 (by simp [h])
      have hsnd : ∀ q ∈ w, q.2 ∈ wordVertices w := fun q hq => by
        simp only [wordVertices, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨q, hq, Or.inr rfl⟩
      have hd' : Disjoint (insert j (A.erase k)) B := by
        refine Finset.disjoint_left.2 fun x hx hxB => ?_
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hjB hxB
        · exact Finset.disjoint_left.1 hd (Finset.mem_of_mem_erase hx) hxB
      have hk' : ∀ q ∈ w, q.2 ∈ (insert j (A.erase k), B).1 := fun q hq => by
        have hqA : q.2 ∈ A := hk q (List.mem_cons_of_mem _ hq)
        refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, hqA⟩)
        rintro hqk
        exact hkw (hqk ▸ hsnd q hq)
      exact FstClassRun.cons hcl hkA (ih hd' hk' hnd'')

end FstClassRun

end FstClassRun

/-! ### The matching predicate -/

section FormMatched

variable [DecidableEq V] [Fintype V]

/-- The bookkeeping predicate of the telescoping argument.  Let a forward run lead from `t` to
`t₁`, and a backward run from `t'` to `t'f` (so `t'` is the *start* of the backward run).
`FormMatched t t₁ t' t'f` says that the backward run undoes exactly the change of the sign function
made by the forward run,
`χ_{t'f} = χ_{t'} - (χ_{t₁} - χ_t)`, and that the change `Δ = χ_{t₁} - χ_t` is orthogonal to
`χ_{t₁} - χ_{t'}` for the form `⟨·, ·⟩ = pairingForm`.

For a palindromic deformation the whole run is matched
(`SideBlock.formMatched_flatMap`), and `FormMatched` implies
`Ψ(t₁, t'f) = Ψ(t, t')` (`FormMatched.pairingIndex_eq`). -/
def FormMatched (G : SimpleGraph V) (t t₁ t' t'f : Finset V × Finset V) : Prop :=
  classSign t'f = classSign t' - (classSign t₁ - classSign t) ∧
    G.pairingForm (classSign t₁ - classSign t) (classSign t₁ - classSign t') = 0

variable {t t₁ tf t' t'₁ t'f : Finset V × Finset V}

/-- The empty run is matched. -/
theorem FormMatched.refl (t t' : Finset V × Finset V) : G.FormMatched t t t' t' := by
  refine ⟨by simp, ?_⟩
  simp [pairingForm_zero_left]

/-- Matched pieces compose: a matched forward piece `t ⟶ t₁` with backward piece `t'₁ ⟶ t'f`,
and a matched forward piece `t₁ ⟶ tf` with backward piece `t' ⟶ t'₁`, give a matched piece
`t ⟶ tf`, `t' ⟶ t'f`.  Here the backward run of the whole is the backward run of the second piece
followed by that of the first. -/
theorem FormMatched.trans (h₁ : G.FormMatched t t₁ t'₁ t'f) (h₂ : G.FormMatched t₁ tf t' t'₁) :
    G.FormMatched t tf t' t'f := by
  obtain ⟨e₁, q₁⟩ := h₁
  obtain ⟨e₂, q₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [e₁, e₂]
    abel
  · have ha : classSign tf - classSign t =
        (classSign tf - classSign t₁) + (classSign t₁ - classSign t) := by abel
    have hb : classSign tf - classSign t' = classSign t₁ - classSign t'₁ := by
      rw [e₂]
      abel
    rw [ha, hb, pairingForm_add_left, q₁, add_zero]
    rw [← hb]
    exact q₂

/-- Exchanging the two classes of all four states preserves the matching predicate. -/
theorem FormMatched.of_swap (h1 : Disjoint t.1 t.2) (h2 : Disjoint t₁.1 t₁.2)
    (h3 : Disjoint t'.1 t'.2) (h4 : Disjoint t'f.1 t'f.2)
    (h : G.FormMatched t.swap t₁.swap t'.swap t'f.swap) : G.FormMatched t t₁ t' t'f := by
  have e : ∀ u : Finset V × Finset V, Disjoint u.1 u.2 → classSign u.swap = -classSign u :=
    fun u hu => funext (classSign_swap hu)
  unfold FormMatched at h ⊢
  rw [e t h1, e t₁ h2, e t' h3, e t'f h4] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · funext v
    have := congrFun h₁ v
    simp only [Pi.neg_apply, Pi.sub_apply] at this ⊢
    linarith
  · have ha : -classSign t₁ - -classSign t = -(classSign t₁ - classSign t) := by abel
    have hb : -classSign t₁ - -classSign t' = -(classSign t₁ - classSign t') := by abel
    rw [ha, hb, pairingForm_neg_neg] at h₂
    exact h₂

/-- A matched run does not change the pairing index of the pair of ends:
`FormMatched t t₁ t' t'f` gives `Ψ(t₁, t'f) = Ψ(t, t')`.

With `a = χ_t`, `c = χ_{t₁}`, `b = χ_{t'}`, the hypotheses read `χ_{t'f} = b - (c - a)` and
`⟨c - a, c - b⟩ = 0`, and then `⟨c, b - (c - a)⟩ - ⟨a, b⟩ = ⟨c, b⟩ - ⟨c, c⟩ + ⟨c, a⟩ - ⟨a, b⟩
= ⟨c, a⟩ - ⟨a, c⟩ = 0` by symmetry of the form. -/
theorem FormMatched.pairingIndex_eq (h : G.FormMatched t t₁ t' t'f) :
    G.pairingIndex t₁ t'f = G.pairingIndex t t' := by
  obtain ⟨e, q⟩ := h
  rw [pairingIndex_eq_pairingForm, pairingIndex_eq_pairingForm, e]
  simp only [pairingForm_sub_left, pairingForm_sub_right] at q ⊢
  have := pairingForm_comm (G := G) (classSign t) (classSign t₁)
  linarith

omit [Fintype V] in
/-- The change of the sign function under a first-class step `(j, k)`: `+1` at the introduced
vertex `j` and `-1` at the removed vertex `k`. -/
theorem classSign_stepFst_sub {A B : Finset V} {j k : V} (hd : Disjoint A B) (hj : j ∉ A ∪ B)
    (hk : k ∈ A) :
    classSign (insert j (A.erase k), B) - classSign (A, B) = Pi.single j 1 - Pi.single k 1 := by
  have hjA : j ∉ A := fun h => hj (Finset.mem_union_left _ h)
  have hjB : j ∉ B := fun h => hj (Finset.mem_union_right _ h)
  have hkB : k ∉ B := Finset.disjoint_left.1 hd hk
  have hjk : j ≠ k := fun h => hjA (h ▸ hk)
  funext v
  by_cases hvj : v = j
  · subst hvj
    simp [classSign, hjA, hjB, hjk]
  · by_cases hvk : v = k
    · subst hvk
      simp [classSign, hk, hkB, hvj]
    · simp [classSign, hvj, hvk]

omit [Fintype V] in
/-- The sign function vanishes off the carrier of a state. -/
theorem classSign_eq_zero_of_not_mem_carrier {A B : Finset V} {v : V}
    (hv : v ∉ (↑(A ∪ B) : Set V)) : classSign (A, B) v = 0 := by
  have h1 : v ∉ A := fun h => hv (Finset.mem_coe.2 (Finset.mem_union_left _ h))
  have h2 : v ∉ B := fun h => hv (Finset.mem_coe.2 (Finset.mem_union_right _ h))
  exact classSign_of_not_mem (s := (A, B)) h1 h2

/-- One forward step `t ⟶ t₁` (`j ≺ k` in the carrier of `t`, `k` in the first class) and the
matching backward step `t' ⟶ t'f` (`k ≺ j` in the carrier of `t'`, `j` in the first class) are
matched.

With `δ = e_j - e_k` one has `χ_{t₁} - χ_t = δ`, `χ_{t'f} - χ_{t'} = -δ`, and the clone identity
`pairingForm_clone` gives `⟨δ, χ_t⟩ = -1`, `⟨-δ, χ_{t'}⟩ = -1`, while `⟨δ, δ⟩ = 2`
(`j ~ k`); hence `⟨δ, χ_{t₁} - χ_{t'}⟩ = (-1 + 2) - 1 = 0`. -/
theorem FormMatched.of_step {A B A' B' : Finset V} {j k : V} (hd : Disjoint A B)
    (hd' : Disjoint A' B') (hcl : G.IsCloneIn (↑(A ∪ B) : Set V) j k) (hk : k ∈ A)
    (hcl' : G.IsCloneIn (↑(A' ∪ B') : Set V) k j) (hj : j ∈ A') :
    G.FormMatched (A, B) (insert j (A.erase k), B) (A', B') (insert k (A'.erase j), B') := by
  have F1 := classSign_stepFst_sub hd (fun h => hcl.1 (Finset.mem_coe.2 h)) hk
  have F2 := classSign_stepFst_sub hd' (fun h => hcl'.1 (Finset.mem_coe.2 h)) hj
  have F3 := pairingForm_clone hcl (classSign (A, B)) fun v hv =>
    classSign_eq_zero_of_not_mem_carrier hv
  rw [classSign_of_mem_fst (s := (A, B)) hk] at F3
  have F4 := pairingForm_clone hcl' (classSign (A', B')) fun v hv =>
    classSign_eq_zero_of_not_mem_carrier hv
  rw [classSign_of_mem_fst (s := (A', B')) hj] at F4
  have hadj : G.Adj j k := (hcl.2.2 k hcl.2.1).2 (Or.inl rfl)
  have F5 : G.pairingForm (Pi.single j 1 - Pi.single k 1) (Pi.single j 1 - Pi.single k 1) = 2 := by
    simp only [pairingForm_sub_left, pairingForm_sub_right, pairingForm_single_single,
      pairingMat_self, pairingMat_of_adj hadj, pairingMat_of_adj hadj.symm]
    norm_num
  have hδ : (Pi.single j 1 - Pi.single k 1 : V → ℤ) = -(Pi.single k 1 - Pi.single j 1) := by abel
  have F6 : G.pairingForm (Pi.single j 1 - Pi.single k 1) (classSign (A', B')) = 1 := by
    rw [hδ, pairingForm_neg_left, F4]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [F1, eq_add_of_sub_eq F2]
    abel
  · rw [F1, eq_add_of_sub_eq F1, pairingForm_sub_right, pairingForm_add_right, F3, F5, F6]
    norm_num

/-- A first-class run `t ⟶ tf` on the word `w` and a first-class run `t' ⟶ t'f` on the reversed
word are matched (`FormMatched t tf t' t'f`), provided the classes of `t` and `t'` are disjoint.

The induction peels off the first forward step `(j, k)` and the last backward step `(k, j)`;
the remaining runs are matched by the induction hypothesis, and the peeled pair of steps is matched
by `FormMatched.of_step`. -/
theorem FstClassRun.formMatched {t tf t' t'f : Finset V × Finset V} {w : List (V × V)}
    (hf : G.FstClassRun t w tf) (hb : G.FstClassRun t' (reverseWord w) t'f)
    (ht : Disjoint t.1 t.2) (ht' : Disjoint t'.1 t'.2) : G.FormMatched t tf t' t'f := by
  induction hf generalizing t' t'f with
  | nil s =>
    rw [reverseWord_nil] at hb
    cases hb
    exact FormMatched.refl _ _
  | @cons A B j k w s'' hcl hk hrest ih =>
    rw [reverseWord_cons] at hb
    obtain ⟨u, hb₁, hb₂⟩ := FstClassRun.exists_of_append hb
    have hjB : j ∉ B := fun h => hcl.1 (by simp [h])
    have hd : Disjoint A B := ht
    have hjAB : j ∉ A ∪ B := fun h => hcl.1 (Finset.mem_coe.2 h)
    have hd₁ : Disjoint (insert j (A.erase k)) B := by
      refine Finset.disjoint_left.2 fun x hx hxB => ?_
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hjB hxB
      · exact Finset.disjoint_left.1 hd (Finset.mem_of_mem_erase hx) hxB
    have hM := ih hb₁ hd₁ ht'
    have hdu : Disjoint u.1 u.2 := hb₁.disjoint ht'
    obtain ⟨A', B'⟩ := u
    cases hb₂ with
    | cons hcl' hj hrest' =>
      cases hrest'
      exact (FormMatched.of_step hd hdu hcl hk hcl' hj).trans hM

end FormMatched

/-! ### Blocks -/

namespace OddBlock

variable [DecidableEq V] [Fintype V] {X Y : Finset V}

/-- **A block of the first class is matched.**  Let `P` be an odd block of `G[X ⊕ Y]`, run forward
from a hole-class state `t` whose first class contains the removed vertices `X ∩ P.support`, and
run backward (the reversed word) from a hole-class state `t'` whose first class contains the
removed vertices of the reversed block, `Y ∩ P.support`.  Then `FormMatched t t₁ t' t'f`.

All steps of both runs are `ClassStep.a` (`FstClassRun.of_classRun`; the vertices of a path are
distinct), so the block-level statement is `FstClassRun.formMatched`. -/
theorem formMatched_fst (P : G.OddBlock X Y) {t t₁ t' t'f : Finset V × Finset V}
    (ht : G.IsHoleClasses t) (ht' : G.IsHoleClasses t')
    (hX : ∀ v ∈ P.support, v ∈ X → v ∈ t.1) (hY : ∀ v ∈ P.support, v ∈ Y → v ∈ t'.1)
    (hf : G.ClassRun t P.word t₁) (hb : G.ClassRun t' (reverseWord P.word) t'f) :
    G.FormMatched t t₁ t' t'f := by
  have hkf : ∀ p ∈ P.word, p.2 ∈ t.1 := fun p hp =>
    hX _ (snd_mem_support hp) (Finset.mem_sdiff.1 (snd_mem hp)).1
  have hb' : G.ClassRun t' P.reverse.word t'f := by rw [reverse_word]; exact hb
  have hkb : ∀ p ∈ P.reverse.word, p.2 ∈ t'.1 := fun p hp =>
    hY _ (by rw [← reverse_support]; exact snd_mem_support hp) (Finset.mem_sdiff.1 (snd_mem hp)).1
  have hf' := FstClassRun.of_classRun hf ht.disjoint hkf P.nodup_wordVertices
  have hb'' := FstClassRun.of_classRun hb' ht'.disjoint hkb P.reverse.nodup_wordVertices
  rw [reverse_word] at hb''
  exact hf'.formMatched hb'' ht.disjoint ht'.disjoint

/-- **A block of the second class is matched.**  The second-class version of `formMatched_fst`,
by exchanging the two classes of all four states (`FormMatched.of_swap`). -/
theorem formMatched_snd (P : G.OddBlock X Y) {t t₁ t' t'f : Finset V × Finset V}
    (ht : G.IsHoleClasses t) (ht' : G.IsHoleClasses t')
    (hX : ∀ v ∈ P.support, v ∈ X → v ∈ t.2) (hY : ∀ v ∈ P.support, v ∈ Y → v ∈ t'.2)
    (hf : G.ClassRun t P.word t₁) (hb : G.ClassRun t' (reverseWord P.word) t'f) :
    G.FormMatched t t₁ t' t'f :=
  FormMatched.of_swap ht.disjoint (hf.isHoleClasses ht).disjoint ht'.disjoint
    (hb.isHoleClasses ht').disjoint
    (P.formMatched_fst ht.swap ht'.swap hX hY hf.swap hb.swap)

end OddBlock

/-! ### Lists of side blocks -/

namespace SideBlock

variable [DecidableEq V] [Fintype V] {s s' : Finset V × Finset V}

omit [Fintype V] in
/-- Membership in the side-1 toggle of a list starting with a side-1 block. -/
theorem mem_listToggle₁_cons_inl_iff (P : G.OddBlock s.1 s'.1) (bs : List (G.SideBlock s s'))
    (h : P.support ∉ bs.map SideBlock.support) (v : V) :
    v ∈ listToggle₁ (Sum.inl P :: bs : List (G.SideBlock s s')) ↔
      v ∈ P.support ∨ v ∈ listToggle₁ bs := by
  have hd := disjoint_listToggle₁ P bs h
  rw [listToggle₁_cons_inl, Finset.mem_symmDiff]
  constructor
  · rintro (⟨hv, -⟩ | ⟨hv, -⟩)
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (hv | hv)
    · exact Or.inl ⟨hv, fun h' => Finset.disjoint_left.1 hd hv h'⟩
    · exact Or.inr ⟨hv, fun h' => Finset.disjoint_left.1 hd h' hv⟩

omit [Fintype V] in
/-- Membership in the side-2 toggle of a list starting with a side-2 block. -/
theorem mem_listToggle₂_cons_inr_iff (P : G.OddBlock s.2 s'.2) (bs : List (G.SideBlock s s'))
    (h : P.support ∉ bs.map SideBlock.support) (v : V) :
    v ∈ listToggle₂ (Sum.inr P :: bs : List (G.SideBlock s s')) ↔
      v ∈ P.support ∨ v ∈ listToggle₂ bs := by
  have hd := disjoint_listToggle₂ P bs h
  rw [listToggle₂_cons_inr, Finset.mem_symmDiff]
  constructor
  · rintro (⟨hv, -⟩ | ⟨hv, -⟩)
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (hv | hv)
    · exact Or.inl ⟨hv, fun h' => Finset.disjoint_left.1 hd hv h'⟩
    · exact Or.inr ⟨hv, fun h' => Finset.disjoint_left.1 hd h' hv⟩

/-- **A list of side blocks with distinct supports is matched.**  Run the flattened words of `bs`
forward from a hole-class state `t` and the reversed word backward from a hole-class state `t'`.
The hypotheses `h₁`, `h₂` (resp. `h₁'`, `h₂'`) say that the vertices toggled by the blocks and
lying in the classes `s.i` (resp. `s'.i`) of the *original* pair lie in the classes of `t` (resp.
`t'`); for `t = s`, `t' = s'` they are trivial.  Then `FormMatched t tf t' t'f`.

The proof is by induction on `bs`, generalising `t` and `t'`, in the style of
`SideBlock.eq_of_classRun_flatMap`.  For `bs = B :: bs'` the forward run is the block `B` followed
by the run of `bs'`, and the backward run is the backward run of `bs'` (the forward run of the
mirror list `mirrorList bs'`, whose end state is computed by `eq_of_classRun_flatMap`) followed by
the reversed block.  The block is matched by `OddBlock.formMatched_fst` / `formMatched_snd`, the
rest by induction, and the two compose by `FormMatched.trans`. -/
theorem formMatched_flatMap (bs : List (G.SideBlock s s'))
    (hnd : (bs.map SideBlock.support).Nodup) {t tf t' t'f : Finset V × Finset V}
    (ht : G.IsHoleClasses t) (ht' : G.IsHoleClasses t')
    (h₁ : ∀ v ∈ listToggle₁ bs, v ∈ s.1 → v ∈ t.1)
    (h₂ : ∀ v ∈ listToggle₂ bs, v ∈ s.2 → v ∈ t.2)
    (h₁' : ∀ v ∈ listToggle₁ bs, v ∈ s'.1 → v ∈ t'.1)
    (h₂' : ∀ v ∈ listToggle₂ bs, v ∈ s'.2 → v ∈ t'.2)
    (hf : G.ClassRun t (bs.flatMap SideBlock.word) tf)
    (hb : G.ClassRun t' (reverseWord (bs.flatMap SideBlock.word)) t'f) :
    G.FormMatched t tf t' t'f := by
  induction bs generalizing t tf t' t'f with
  | nil =>
    have e1 := ClassRun.eq_of_nil (by simpa using hf)
    have e2 := ClassRun.eq_of_nil (by simpa using hb)
    subst e1 e2
    exact FormMatched.refl _ _
  | cons B bs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.flatMap_cons] at hf hb
    obtain ⟨t₁, hB, hrest⟩ := ClassRun.exists_of_append hf
    rw [reverseWord_append] at hb
    obtain ⟨t'₁, hrb, hB'⟩ := ClassRun.exists_of_append hb
    have hrb0 := hrb
    rw [← flatMap_word_mirrorList] at hrb
    have ht₁ := hB.isHoleClasses ht
    cases B with
    | inl P =>
      have hmem := mem_listToggle₁_cons_inl_iff P bs hnd.1
      have hd := disjoint_listToggle₁ P bs hnd.1
      obtain ⟨hteq, -⟩ := P.eq_of_classRun_fst ht
        (fun v hv => h₁ v ((hmem v).2 (Or.inl hv))) hB
      obtain ⟨hend, -, -⟩ := eq_of_classRun_flatMap (mirrorList bs) (nodup_mirrorList hnd.2) ht'
        (fun v hv hvs => h₁' v ((hmem v).2
          (Or.inr (by rwa [listToggle₁_mirrorList hnd.2] at hv))) hvs)
        (fun v hv hvs => h₂' v (by
          rw [listToggle₂_cons_inl]
          rwa [listToggle₂_mirrorList hnd.2] at hv) hvs) hrb
      rw [listToggle₁_mirrorList hnd.2, listToggle₂_mirrorList hnd.2] at hend
      have hrest' := ih hnd.2 ht₁ ht'
        (fun v hv hvs => by
          rw [hteq]
          exact Finset.mem_symmDiff.2 (Or.inl ⟨h₁ v ((hmem v).2 (Or.inr hv)) hvs,
            fun hvP => Finset.disjoint_left.1 hd hvP hv⟩))
        (fun v hv hvs => by
          rw [hteq]
          exact h₂ v (by rwa [listToggle₂_cons_inl]) hvs)
        (fun v hv hvs => h₁' v ((hmem v).2 (Or.inr hv)) hvs)
        (fun v hv hvs => h₂' v (by rwa [listToggle₂_cons_inl]) hvs) hrest hrb0
      have ht'₁ := hrb0.isHoleClasses ht'
      refine (P.formMatched_fst ht ht'₁
        (fun v hv => h₁ v ((hmem v).2 (Or.inl hv)))
        (fun v hv hvs => by
          rw [hend]
          exact Finset.mem_symmDiff.2 (Or.inl ⟨h₁' v ((hmem v).2 (Or.inl hv)) hvs,
            fun hvT => Finset.disjoint_left.1 hd hv hvT⟩)) hB hB').trans hrest'
    | inr P =>
      have hmem := mem_listToggle₂_cons_inr_iff P bs hnd.1
      have hd := disjoint_listToggle₂ P bs hnd.1
      obtain ⟨hteq, -⟩ := P.eq_of_classRun_snd ht
        (fun v hv => h₂ v ((hmem v).2 (Or.inl hv))) hB
      obtain ⟨hend, -, -⟩ := eq_of_classRun_flatMap (mirrorList bs) (nodup_mirrorList hnd.2) ht'
        (fun v hv hvs => h₁' v (by
          rw [listToggle₁_cons_inr]
          rwa [listToggle₁_mirrorList hnd.2] at hv) hvs)
        (fun v hv hvs => h₂' v ((hmem v).2
          (Or.inr (by rwa [listToggle₂_mirrorList hnd.2] at hv))) hvs) hrb
      rw [listToggle₁_mirrorList hnd.2, listToggle₂_mirrorList hnd.2] at hend
      have hrest' := ih hnd.2 ht₁ ht'
        (fun v hv hvs => by
          rw [hteq]
          exact h₁ v (by rwa [listToggle₁_cons_inr]) hvs)
        (fun v hv hvs => by
          rw [hteq]
          exact Finset.mem_symmDiff.2 (Or.inl ⟨h₂ v ((hmem v).2 (Or.inr hv)) hvs,
            fun hvP => Finset.disjoint_left.1 hd hvP hv⟩))
        (fun v hv hvs => h₁' v (by rwa [listToggle₁_cons_inr]) hvs)
        (fun v hv hvs => h₂' v ((hmem v).2 (Or.inr hv)) hvs) hrest hrb0
      have ht'₁ := hrb0.isHoleClasses ht'
      refine (P.formMatched_snd ht ht'₁
        (fun v hv => h₂ v ((hmem v).2 (Or.inl hv)))
        (fun v hv hvs => by
          rw [hend]
          exact Finset.mem_symmDiff.2 (Or.inl ⟨h₂' v ((hmem v).2 (Or.inl hv)) hvs,
            fun hvT => Finset.disjoint_left.1 hd hv hvT⟩)) hB hB').trans hrest'

end SideBlock

/-! ### Palindromic deformations -/

namespace FPDeformation

variable [DecidableEq V] [Fintype V] {s s' : Finset V × Finset V}

/-- The forward run and the backward run of a palindromic deformation are matched. -/
theorem Palindromic.formMatched {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) :
    G.FormMatched s D.fwdEnd s' D.bwdEnd :=
  SideBlock.formMatched_flatMap D.blocks D.nodup hs hs' (fun _ _ hv => hv) (fun _ _ hv => hv)
    (fun _ _ hv => hv) (fun _ _ hv => hv) (hD.classRun_fwdEnd hs hs') (hD.classRun_bwdEnd hs hs')

/-- **The pairing index is invariant along a palindromic deformation**:
`Ψ(D.fwdEnd, D.bwdEnd) = Ψ(s, s')`.

Here `s = (C_a, C_b)` and `s' = (C'_c, C'_d)` are the colouring classes of two even holes `C`,
`C'` (hole-class states), `D` is a fixed-pairing-type deformation with pairing `a ↔ c`, `b ↔ d`
(v1 Definition 19, L978-994) which is palindromic (v1 L965-967 and L1015-1021: its word runs from
`s` and the reversed word runs from `s'`), and `D.fwdEnd`, `D.bwdEnd` are the two end states, with
carriers `C ⊕ T` and `C' ⊕ T` (`FPDeformation.carrier_fwdEnd`, `carrier_bwdEnd`).

This is what makes v1's choice of the larger pairing type as the source set of the obstruction
graph (Definition 21, L1017; the search process L1158-1191 keeps the source set larger) a *toggle
invariant*: `Ψ` computes the majority vote, and the vote is the same for `(C, C')` and for the
toggled pair `(C ⊕ T, C' ⊕ T)`.  v1 has no counterpart of this identity; it is a new statement
proved here, and no claim of v1 depends on it.  Neither claw-freeness nor oddness of the
deformation is used, and no premise beyond the manuscript setup (hole-class states, palindromic
fixed-pairing-type deformation) is assumed.

The proof is the telescoping argument described in the module docstring
(`Palindromic.formMatched` and `FormMatched.pairingIndex_eq`). -/
theorem pairingIndex_ends (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) :
    G.pairingIndex D.fwdEnd D.bwdEnd = G.pairingIndex s s' :=
  (hD.formMatched hs hs').pairingIndex_eq

end FPDeformation

end SimpleGraph
