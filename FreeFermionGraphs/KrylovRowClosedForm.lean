import FreeFermionGraphs.KrylovTreeMatrix
import FreeFermionGraphs.IndependenceSeries
import FreeFermionGraphs.CliqueRootedPathChildren
import FreeFermionGraphs.InducedPathDeformationPrefixes

/-!
# Closed form of the Krylov rows of the tree matrix

Manuscript reference: arXiv 2305.15625v1, Section "Krylov Subspaces" (L1324),
whose Theorem 3 is titled "Polynomial Divisibility" (L1328-1336) and is
inspired by a polynomial divisibility result of Godsil (L1326).  The
divisibility identity proved here is *not* stated in v1; it is the exact
closed form behind that title, and it replaces the walk-substitution arguments
of L1466-1485 and L1527-1576 for the tree part of the matrix of
Eq. (decoratedtree) (L1434-1445).

Let `G` be a finite claw-free graph, `K` a simplicial clique, `b : V → R`, and
let `T = cliqueTreeMatrix G K b` be the tree matrix of `KrylovTreeMatrix.lean`,
indexed by the rooted induced paths of `G* = G.adjoinRootAt K`.  For a rooted
path `Q` of `G*` write `|Q|` for its number of vertices (the root `j*`
included), `N(Q) = K ∪ ⋃_{i ≥ 1} Γ_G[j_i]` for its closed neighbourhood
(`PathClosedNeighborhood.lean`), and `I_U` for the weighted independence series
of `G[U]` with weights `b²` at `x = -X²` (`indepSeries`,
`IndependenceSeries.lean`).  The main theorem is

`(∑_n X^n (T^n)_{{j*},Q}) · I_V = X^{|Q| - 1} · I_{V \ N(Q)}`   in `R⟦X⟧`.

In words, the `{j*}`-row of `(1 - X T)^{-1}` is
`X^{|Q|-1} I_{G \ N(Q)}(-X²) / I_G(-X²)`.  No even-hole-freeness is used; the
only hypotheses are that `G` is finite, claw-free and that `K` is a simplicial
clique.  (For graphs with even holes, `T` is only the tree part of
Eq. (decoratedtree): the hole arcs are not part of this matrix.)

The proof avoids matrix inverses and works coefficientwise.  Put
`s_Q = ∑_n X^n (T^n)_{{j*},Q}` and `r_Q = X^{|Q|-1} I_{V \ N(Q)}`.

1. `krylovRowTarget_column`: `r_Q - X ∑_P T_{PQ} r_P = [Q = {j*}] I_V`.  The
   sources `P` with `T_{PQ} ≠ 0` are the parent of `Q` (weight `1`) and the
   children `Q + x`, `x ∈ C(Q)` (weight `b_x²`).  The identity is the clique
   splitting `indepSeries_clique_split` for `U = V \ N(P0)` and `D = C(Q)`,
   where `P0` is the parent, using `N(Q) = N(P0) ⊔ C(Q)` and
   `N(Q + x) = N(P0) ∪ Γ[x]` (`CliqueRootedPathChildren.lean`).  For
   `Q = {j*}` one takes `U = V`, `D = K`.
2. `krylovRowSeries_column`: `s_Q - X ∑_P T_{PQ} s_P = [Q = {j*}]`, from
   `T^{n+1} = T^n T` coefficientwise.
3. `u_Q = s_Q I_V - r_Q` satisfies `u_Q = X ∑_P T_{PQ} u_P`, hence all its
   coefficients vanish, by induction on the degree.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

namespace RootedInducedPath

/-! ### Parents in the induced-path tree -/

/-- The one-vertex-extension relation determines the shorter path: a rooted
induced path has at most one parent in the induced-path tree. -/
theorem IsOneVertexExtension.eq_of_right {P P' Q : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension Q) (h' : P'.IsOneVertexExtension Q) : P = P' := by
  have hcard : P.path.card = P'.path.card := by
    have h1 := h.card_eq
    have h2 := h'.card_eq
    omega
  apply ext_path
  apply IndexedInducedPath.ext_of_card_eq_vertex_cast hcard
  intro i
  have hlt : i.val < Q.path.card := by
    have := h.card_eq
    have := i.isLt
    omega
  have h1 := h.vertex_of_lt (j := ⟨i.val, hlt⟩) i.isLt
  have hlt' : i.val < P'.path.card := by
    have := i.isLt
    omega
  have h2 := h'.vertex_of_lt (j := ⟨i.val, hlt⟩) hlt'
  exact h1.symm.trans h2

/-- A rooted induced path with at least two vertices has a parent in the
induced-path tree (the prefix obtained by removing the terminal vertex). -/
theorem exists_isOneVertexExtension_of_two_le (Q : CliqueRootedInducedPath G K)
    (h : 2 ≤ Q.path.card) :
    ∃ P : CliqueRootedInducedPath G K, P.IsOneVertexExtension Q := by
  refine ⟨Q.initialSegment ⟨Q.path.card - 2, by omega⟩, ?_, ?_⟩
  · change (Q.path.card - 2 + 1) + 1 = Q.path.card
    omega
  · intro q
    rfl

/-- Nothing is a parent of the root path `{j*}`. -/
theorem not_isOneVertexExtension_cliqueRootPath (P : CliqueRootedInducedPath G K) :
    ¬P.IsOneVertexExtension (cliqueRootPath G K) := by
  rintro ⟨hcard, _⟩
  have := P.path.nonempty
  change P.path.card + 1 = 1 at hcard
  omega

open Classical in
/-- The sum over the one-vertex extensions `Q + x` of a path `Q`: it is the sum
over its children `x ∈ C(Q)`. -/
theorem sum_isOneVertexExtension [Fintype V] {S : Type w} [AddCommMonoid S]
    (Q : CliqueRootedInducedPath G K) (g : CliqueRootedInducedPath G K → S) :
    ∑ P : CliqueRootedInducedPath G K,
        (if Q.IsOneVertexExtension P then g P else 0) =
      ∑ x : Q.childCandidates, g (Q.appendTerminal x.2) := by
  rw [← Finset.sum_filter]
  have hsub := Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter fun P : CliqueRootedInducedPath G K => Q.IsOneVertexExtension P)
    (p := fun P : CliqueRootedInducedPath G K => Q.IsOneVertexExtension P)
    (fun P => by simp) g
  rw [hsub]
  exact (Fintype.sum_equiv (childCandidatesEquivExtensions Q)
    (fun x : Q.childCandidates => g (Q.appendTerminal x.2))
    (fun P : {P : CliqueRootedInducedPath G K // Q.IsOneVertexExtension P} => g P.1)
    (fun _ => rfl)).symm

end RootedInducedPath

/-! ### One step of the column recursion -/

section Column

variable [Fintype V] {R : Type w} [CommRing R]

open Classical in
/-- Splitting a sum over the sources `P` of a column `Q` of the tree matrix:
the parent of `Q` (weight one) and the children `Q + x`, `x ∈ C(Q)` (weight
`b_x²`), where `φ` is a ring homomorphism applied to the matrix entries. -/
theorem sum_cliqueTreeMatrix_column {S : Type*} [CommRing S] (φ : R →+* S)
    (b : V → R) (Q : CliqueRootedInducedPath G K)
    (f : CliqueRootedInducedPath G K → S) :
    ∑ P : CliqueRootedInducedPath G K, φ (cliqueTreeMatrix G K b P Q) * f P =
      (∑ P : CliqueRootedInducedPath G K,
          (if P.IsOneVertexExtension Q then f P else 0)) +
        ∑ x : Q.childCandidates,
          φ (b x ^ 2) * f (Q.appendTerminal x.2) := by
  have hpt : ∀ P : CliqueRootedInducedPath G K,
      φ (cliqueTreeMatrix G K b P Q) * f P =
        (if P.IsOneVertexExtension Q then f P else 0) +
          (if Q.IsOneVertexExtension P then
            φ (P.terminalVertex.elim 0 (fun j => b j ^ 2)) * f P else 0) := by
    intro P
    by_cases h1 : P.IsOneVertexExtension Q
    · have h2 : ¬Q.IsOneVertexExtension P := h1.not_reverse
      simp [h1, h2]
    · by_cases h2 : Q.IsOneVertexExtension P
      · simp [cliqueTreeMatrix_of_contraction b h2, h1, h2]
      · have h3 : ¬P.TreeAdjacent Q := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        simp [cliqueTreeMatrix_eq_zero_of_not_treeAdjacent b h3, h1, h2]
  rw [Finset.sum_congr rfl (fun P _ => hpt P), Finset.sum_add_distrib]
  congr 1
  rw [RootedInducedPath.sum_isOneVertexExtension]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [RootedInducedPath.terminalVertex_appendTerminal Q x.2]
  rfl

end Column

/-! ### The closed form target `r_Q = X^{|Q|-1} I_{V \ N(Q)}` -/

section ClosedForm

variable [Fintype V] {R : Type w} [CommRing R]

open Classical in
/-- The right-hand side `r_Q = X^{|Q| - 1} · I_{V \ N(Q)}` of the closed form
of the Krylov rows of the tree matrix, where `|Q|` counts the vertices of the
rooted path `Q` of `G*` (the root `j*` included), `N(Q)` is its closed
neighbourhood and `I` is the weighted independence series with weights `b²`. -/
noncomputable def krylovRowTarget (G : SimpleGraph V) (K : Set V) (b : V → R)
    (Q : CliqueRootedInducedPath G K) : PowerSeries R :=
  PowerSeries.X ^ (Q.path.card - 1) *
    indepSeries G (fun v => b v ^ 2) (Finset.univ.filter (fun v => v ∉ Q.closedNbhd))

open Classical in
/-- The children `x ∈ C(Q)` as a finset. -/
private noncomputable def childFinset (Q : CliqueRootedInducedPath G K) : Finset V :=
  Finset.univ.filter (fun x => x ∈ Q.childCandidates)

private theorem mem_childFinset (Q : CliqueRootedInducedPath G K) (x : V) :
    x ∈ childFinset Q ↔ x ∈ Q.childCandidates := by
  classical
  simp [childFinset]

open Classical in
/-- A sum over the subtype of children, of a function of the underlying vertex,
is the finset sum over `childFinset Q`. -/
private theorem sum_child_subtype (Q : CliqueRootedInducedPath G K)
    (F : V → PowerSeries R) :
    ∑ x : Q.childCandidates, F x = ∑ x ∈ childFinset Q, F x := by
  classical
  exact (Finset.sum_subtype (F := inferInstance) (childFinset Q)
    (p := fun x => x ∈ Q.childCandidates) (mem_childFinset Q) F).symm

/-- One step of the column recursion for the target:
`r_Q = [Q = {j*}] I_V + X ∑_P T_{PQ} r_P`.

For `Q = {j*}` this is the clique splitting `indepSeries_clique_split` for
`U = V`, `D = K`; for `Q = P0 + q` it is the same splitting for
`U = V \ N(P0)`, `D = C(Q)`, using `N(Q) = N(P0) ⊔ C(Q)` and
`N(Q + x) = N(P0) ∪ Γ[x]`. -/
theorem krylovRowTarget_column [DecidableEq V]
    [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (Q : CliqueRootedInducedPath G K) :
    krylovRowTarget G K b Q =
      (if Q = cliqueRootPath G K then
          indepSeries G (fun v => b v ^ 2) Finset.univ else 0) +
        PowerSeries.X * ∑ P : CliqueRootedInducedPath G K,
          PowerSeries.C (cliqueTreeMatrix G K b P Q) * krylovRowTarget G K b P := by
  classical
  rw [sum_cliqueTreeMatrix_column PowerSeries.C b Q]
  by_cases hroot : Q = cliqueRootPath G K
  · subst hroot
    rw [if_pos rfl]
    have hpar : ∑ P : CliqueRootedInducedPath G K,
        (if P.IsOneVertexExtension (cliqueRootPath G K) then
          krylovRowTarget G K b P else 0) = 0 :=
      Finset.sum_eq_zero fun P _ =>
        if_neg (RootedInducedPath.not_isOneVertexExtension_cliqueRootPath P)
    rw [hpar, zero_add]
    have hterm : ∀ x : (cliqueRootPath G K).childCandidates,
        PowerSeries.C (b x ^ 2) *
            krylovRowTarget G K b ((cliqueRootPath G K).appendTerminal x.2) =
          PowerSeries.C (b x ^ 2) * (PowerSeries.X *
            indepSeries G (fun v => b v ^ 2)
              (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x))) := by
      intro x
      unfold krylovRowTarget
      rw [closedNbhd_appendTerminal_cliqueRootPath hK.isClique x.2]
      have hc : ((cliqueRootPath G K).appendTerminal x.2).path.card - 1 = 1 := rfl
      rw [hc, pow_one]
    rw [Finset.sum_congr rfl (fun x _ => hterm x),
      sum_child_subtype (cliqueRootPath G K) (fun x => PowerSeries.C (b x ^ 2) *
        (PowerSeries.X * indepSeries G (fun v => b v ^ 2)
          (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x))))]
    have hD : G.IsClique (childFinset (cliqueRootPath G K) : Set V) := by
      have := RootedInducedPath.childCandidates_isClique hK hclaw (cliqueRootPath G K)
      convert this using 1
      ext x
      simp [mem_childFinset]
    have hsplit := indepSeries_clique_split G (fun v => b v ^ 2) hD
      (Finset.subset_univ (childFinset (cliqueRootPath G K)))
    have hUD : Finset.univ.filter (fun v => v ∉ childFinset (cliqueRootPath G K)) =
        Finset.univ.filter (fun v => v ∉ (cliqueRootPath G K).closedNbhd) := by
      ext v
      simp [mem_childFinset, childCandidates_cliqueRootPath,
        RootedInducedPath.closedNbhd_cliqueRootPath]
    have hS : ∑ x ∈ childFinset (cliqueRootPath G K), PowerSeries.C (b x ^ 2) *
        (PowerSeries.X * indepSeries G (fun v => b v ^ 2)
          (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x))) =
        PowerSeries.X * ∑ x ∈ childFinset (cliqueRootPath G K),
          PowerSeries.C (b x ^ 2) * indepSeries G (fun v => b v ^ 2)
            (Finset.univ.filter (fun v => v ∉ G.closedNeighborhood x)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hS, hsplit, hUD]
    unfold krylovRowTarget
    simp only [cliqueRootPath_card, Nat.sub_self, pow_zero, one_mul]
    ring
  · have h2 : 2 ≤ Q.path.card := by
      have h1 : Q.path.card ≠ 1 := fun h =>
        hroot ((RootedInducedPath.eq_cliqueRootPath_iff Q).2 h)
      have := Q.path.nonempty
      omega
    obtain ⟨P0, hP0⟩ := RootedInducedPath.exists_isOneVertexExtension_of_two_le Q h2
    obtain ⟨q, hq⟩ := Q.vertex_eq_some_of_pos ⟨Q.path.card - 1, by omega⟩
      (by simp only; omega)
    have hqt : Q.terminalVertex = some q := hq
    rw [if_neg hroot, zero_add]
    have hpar : ∑ P : CliqueRootedInducedPath G K,
        (if P.IsOneVertexExtension Q then krylovRowTarget G K b P else 0) =
          krylovRowTarget G K b P0 := by
      rw [Finset.sum_eq_single P0]
      · exact if_pos hP0
      · intro P _ hP
        exact if_neg fun h => hP (h.eq_of_right hP0)
      · intro h
        exact absurd (Finset.mem_univ P0) h
    rw [hpar]
    obtain ⟨hNQ, hdisj⟩ := RootedInducedPath.closedNbhd_eq_parent_union hP0 hqt
    obtain ⟨m, hm⟩ : ∃ m, Q.path.card = m + 2 := ⟨Q.path.card - 2, by omega⟩
    have hP0card : P0.path.card = m + 1 := by
      have := hP0.card_eq
      omega
    have hterm : ∀ x : Q.childCandidates,
        PowerSeries.C (b x ^ 2) * krylovRowTarget G K b (Q.appendTerminal x.2) =
          PowerSeries.C (b x ^ 2) * (PowerSeries.X ^ (m + 2) *
            indepSeries G (fun v => b v ^ 2)
              ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
                (fun v => v ∉ G.closedNeighborhood x))) := by
      intro x
      unfold krylovRowTarget
      rw [RootedInducedPath.closedNbhd_appendTerminal hK hclaw hP0 hqt x.2]
      have hc : (Q.appendTerminal x.2).path.card - 1 = m + 2 := by
        change Q.path.card + 1 - 1 = m + 2
        omega
      rw [hc]
      congr 3
      ext v
      simp [not_or]
    rw [Finset.sum_congr rfl (fun x _ => hterm x),
      sum_child_subtype Q (fun x => PowerSeries.C (b x ^ 2) * (PowerSeries.X ^ (m + 2) *
        indepSeries G (fun v => b v ^ 2)
          ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
            (fun v => v ∉ G.closedNeighborhood x))))]
    have hD : G.IsClique (childFinset Q : Set V) := by
      have := RootedInducedPath.childCandidates_isClique hK hclaw Q
      convert this using 1
      ext x
      simp [mem_childFinset]
    have hDU : childFinset Q ⊆ Finset.univ.filter (fun v => v ∉ P0.closedNbhd) := by
      intro x hx
      have hxC : x ∈ Q.childCandidates := (mem_childFinset Q x).1 hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hxN => Set.disjoint_left.1 hdisj hxN hxC
    have hsplit := indepSeries_clique_split G (fun v => b v ^ 2) hD hDU
    have hUD : (Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
          (fun v => v ∉ childFinset Q) =
        Finset.univ.filter (fun v => v ∉ Q.closedNbhd) := by
      ext v
      simp [mem_childFinset, hNQ, not_or]
    have hS : ∑ x ∈ childFinset Q, PowerSeries.C (b x ^ 2) *
        (PowerSeries.X ^ (m + 2) * indepSeries G (fun v => b v ^ 2)
          ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
            (fun v => v ∉ G.closedNeighborhood x))) =
        PowerSeries.X ^ (m + 2) * ∑ x ∈ childFinset Q, PowerSeries.C (b x ^ 2) *
          indepSeries G (fun v => b v ^ 2)
            ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
              (fun v => v ∉ G.closedNeighborhood x)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    have hI : indepSeries G (fun v => b v ^ 2) (Finset.univ.filter (fun v => v ∉ Q.closedNbhd)) =
        indepSeries G (fun v => b v ^ 2) (Finset.univ.filter (fun v => v ∉ P0.closedNbhd)) +
          PowerSeries.X ^ 2 * ∑ x ∈ childFinset Q, PowerSeries.C (b x ^ 2) *
            indepSeries G (fun v => b v ^ 2)
              ((Finset.univ.filter (fun v => v ∉ P0.closedNbhd)).filter
                (fun v => v ∉ G.closedNeighborhood x)) := by
      rw [← hUD]
      linear_combination -hsplit
    rw [hS]
    unfold krylovRowTarget
    rw [hm, hP0card, hI]
    have e1 : m + 2 - 1 = m + 1 := rfl
    have e2 : m + 1 - 1 = m := rfl
    rw [e1, e2]
    ring

end ClosedForm

/-! ### Uniqueness for the column recursion -/

section Recursion

variable {ι : Type*} [Fintype ι] {R : Type w} [CommRing R]

/-- A family of power series satisfying the column recursion
`f_Q = c_Q + X ∑_P T_{PQ} f_P` is determined by `c` and `T`: the difference of
two solutions has all coefficients zero, by induction on the degree. -/
theorem eq_of_column_recursion (T : Matrix ι ι R) (c f g : ι → PowerSeries R)
    (hf : ∀ Q, f Q = c Q + PowerSeries.X * ∑ P, PowerSeries.C (T P Q) * f P)
    (hg : ∀ Q, g Q = c Q + PowerSeries.X * ∑ P, PowerSeries.C (T P Q) * g P) :
    f = g := by
  have hu : ∀ Q, f Q - g Q =
      PowerSeries.X * ∑ P, PowerSeries.C (T P Q) * (f P - g P) := by
    intro Q
    rw [hf Q, hg Q]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hzero : ∀ (n : ℕ) (Q : ι), PowerSeries.coeff n (f Q - g Q) = 0 := by
    intro n
    induction n with
    | zero =>
        intro Q
        rw [hu Q]
        simp
    | succ n ih =>
        intro Q
        rw [hu Q, PowerSeries.coeff_succ_X_mul, map_sum]
        refine Finset.sum_eq_zero fun P _ => ?_
        rw [PowerSeries.coeff_C_mul, ih P, mul_zero]
  funext Q
  refine sub_eq_zero.1 (PowerSeries.ext fun n => ?_)
  rw [hzero n Q, map_zero]

end Recursion

section Series

variable [Fintype V] {R : Type w} [CommRing R]

/-- Column recursion for the row series `s_Q = ∑_n X^n (T^n)_{{j*},Q}`:
`s_Q = [Q = {j*}] + X ∑_P T_{PQ} s_P`, coefficientwise from
`T^{n+1} = T^n T`. -/
theorem krylovRowSeries_column [DecidableEq (CliqueRootedInducedPath G K)]
    (b : V → R) (Q : CliqueRootedInducedPath G K) :
    PowerSeries.mk (fun n => ((cliqueTreeMatrix G K b) ^ n) (cliqueRootPath G K) Q) =
      (if Q = cliqueRootPath G K then 1 else 0) +
        PowerSeries.X * ∑ P : CliqueRootedInducedPath G K,
          PowerSeries.C (cliqueTreeMatrix G K b P Q) *
            PowerSeries.mk (fun n =>
              ((cliqueTreeMatrix G K b) ^ n) (cliqueRootPath G K) P) := by
  ext n
  cases n with
  | zero =>
      by_cases h : Q = cliqueRootPath G K
      · subst h
        simp
      · simp [h, Ne.symm h]
  | succ n =>
      have h0 : PowerSeries.coeff (n + 1)
          (if Q = cliqueRootPath G K then (1 : PowerSeries R) else 0) = 0 := by
        split_ifs <;> simp
      rw [PowerSeries.coeff_mk, map_add, h0, zero_add, PowerSeries.coeff_succ_X_mul,
        map_sum, pow_succ, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_comm]

end Series

section Main

variable [Fintype V] {R : Type w} [CommRing R]

open Classical in
/-- **Closed form of the Krylov rows of the tree matrix** (Godsil-type
polynomial divisibility; not stated in arXiv 2305.15625v1, whose Theorem 3,
"Polynomial Divisibility", L1328-1336, is the existential form).

Let `G` be finite and claw-free, `K` a simplicial clique, `b : V → R` with `R`
commutative, `T = cliqueTreeMatrix G K b` the tree matrix and `Q` a rooted
induced path of `G*`.  Then in `R⟦X⟧`

`(∑_n X^n (T^n)_{{j*},Q}) · I_V = X^{|Q| - 1} · I_{V \ N(Q)}`,

where `I_U = indepSeries G (b²) U` is the weighted independence polynomial of
`G[U]` at `x = -X²` (v1 Definition `independencepolynomial`, L542-547) and
`N(Q)` is the closed neighbourhood of `Q` (`RootedInducedPath.closedNbhd`).
Equivalently, the `{j*}`-row of `(1 - X T)^{-1}` is
`X^{|Q|-1} I_{G \ N(Q)}(-X²) / I_G(-X²)`.  No even-hole-freeness is needed. -/
theorem krylovRow_mul_indepSeries [DecidableEq V]
    [DecidableEq (CliqueRootedInducedPath G K)]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (Q : CliqueRootedInducedPath G K) :
    PowerSeries.mk (fun n => ((cliqueTreeMatrix G K b) ^ n) (cliqueRootPath G K) Q) *
        indepSeries G (fun v => b v ^ 2) Finset.univ =
      PowerSeries.X ^ (Q.path.card - 1) *
        indepSeries G (fun v => b v ^ 2)
          (Finset.univ.filter (fun v => v ∉ Q.closedNbhd)) := by
  set I := indepSeries G (fun v => b v ^ 2) Finset.univ with hI
  have key := eq_of_column_recursion (cliqueTreeMatrix G K b)
    (fun Q => if Q = cliqueRootPath G K then I else 0)
    (fun P => PowerSeries.mk (fun n =>
      ((cliqueTreeMatrix G K b) ^ n) (cliqueRootPath G K) P) * I)
    (krylovRowTarget G K b)
    (by
      intro Q
      have h1 := krylovRowSeries_column (G := G) (K := K) b Q
      have hite : (if Q = cliqueRootPath G K then (1 : PowerSeries R) else 0) * I =
          if Q = cliqueRootPath G K then I else 0 := by
        split_ifs <;> simp
      rw [h1, add_mul, hite, mul_assoc, Finset.sum_mul]
      congr 2
      refine Finset.sum_congr rfl fun P _ => ?_
      ring)
    (krylovRowTarget_column hK hclaw b)
  exact congrFun key Q

end Main


end SimpleGraph
