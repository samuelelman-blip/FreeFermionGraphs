import FreeFermionGraphs.Lemma11BFullDefinition19

/-!
# Lemma 11(a): path-block bookkeeping

This module lifts the one-step degree calculation to a complete ordered
Definition 19 path block.  The useful invariant is an unsigned balance:
at every replacement, the new degree plus the indicator for adjacency to
the removed vertex equals the old degree plus the indicator for adjacency
to the introduced vertex.  Summing this identity through the block avoids
any subtraction in `Nat`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

open scoped BigOperators

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- A path vertex anticommutes with the path exactly only at an endpoint;
the interior path degree is two. -/
theorem endpoint_of_mem_range_of_anticommutesWith
    (P : IndexedInducedPath G) {u : V}
    (hu : u ∈ Set.range P.vertex)
    (hanti : P.AnticommutesWith u) :
    ∃ q : Fin P.card,
      P.vertex q = u ∧ P.IsEndpointIndex q := by
  classical
  obtain ⟨q, rfl⟩ := hu
  refine ⟨q, rfl, ?_⟩
  by_contra hendpoint
  have hqInterior : 0 < q.val ∧ q.val + 1 < P.card := by
    have hnot :=
      (P.isInteriorIndex_iff_not_isEndpointIndex q).2 hendpoint
    change 0 < q.val ∧ q.val + 1 < P.card
    have hqLt := q.isLt
    simp only [IndexedInducedPath.IsInteriorIndex] at hnot
    omega
  let previous : Fin P.card := ⟨q.val - 1, by omega⟩
  let next : Fin P.card := ⟨q.val + 1, hqInterior.2⟩
  have hprevNext : previous ≠ next := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [previous, next] at hval
    omega
  have hset : P.neighborIndexSet (P.vertex q) =
      ({previous, next} : Set (Fin P.card)) := by
    ext k
    change G.Adj (P.vertex q) (P.vertex k) ↔
      k = previous ∨ k = next
    rw [P.adj_iff]
    constructor
    · intro h
      rcases h with h | h
      · right
        apply Fin.ext
        dsimp [next]
        omega
      · left
        apply Fin.ext
        dsimp [previous]
        omega
    · intro h
      rcases h with rfl | rfl
      · right
        dsimp [previous]
        omega
      · left
        dsimp [next]
  have htwo : (P.neighborIndexSet (P.vertex q)).ncard = 2 := by
    rw [hset]
    simp [hprevNext]
  have hodd :=
    (P.anticommutesWith_iff_neighborIndexSet_mod_eq_one
      (P.vertex q)).1 hanti
  rw [htwo] at hodd
  omega

end IndexedInducedPath

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The `0`/`1` indicator of an edge. -/
noncomputable def adjacencyBit (G : SimpleGraph V) (u v : V) : Nat := by
  classical
  exact if G.Adj u v then 1 else 0

/-- Nat-indexed introduced vertex.  The fallback branch is unreachable in
all uses below; it only makes the bookkeeping functions total. -/
def introducedAtNat
    (D : ConcretePathDeformation O Cprime) (n : Nat) : V :=
  if hn : n < D.deformation.stepCount then
    (D.deformation.step ⟨n, hn⟩).introduced
  else
    (D.deformation.step D.firstIndex).introduced

/-- Nat-indexed removed vertex, with an unreachable totality fallback. -/
def removedAtNat
    (D : ConcretePathDeformation O Cprime) (n : Nat) : V :=
  if hn : n < D.deformation.stepCount then
    (D.deformation.step ⟨n, hn⟩).before.vertex
      (D.deformation.step ⟨n, hn⟩).removedIndex
  else
    (D.deformation.step D.firstIndex).before.vertex
      (D.deformation.step D.firstIndex).removedIndex

@[simp]
theorem introducedAtNat_of_lt
    (D : ConcretePathDeformation O Cprime)
    {n : Nat} (hn : n < D.deformation.stepCount) :
    D.introducedAtNat n =
      (D.deformation.step ⟨n, hn⟩).introduced := by
  simp [introducedAtNat, hn]

@[simp]
theorem removedAtNat_of_lt
    (D : ConcretePathDeformation O Cprime)
    {n : Nat} (hn : n < D.deformation.stepCount) :
    D.removedAtNat n =
      (D.deformation.step ⟨n, hn⟩).before.vertex
        (D.deformation.step ⟨n, hn⟩).removedIndex := by
  simp [removedAtNat, hn]

/-- Number of introduced neighbors among the first `n` replacements. -/
noncomputable def introducedNeighborCount
    (D : ConcretePathDeformation O Cprime) (u : V) (n : Nat) : Nat :=
  ∑ t ∈ Finset.range n, adjacencyBit G u (D.introducedAtNat t)

/-- Number of removed neighbors among the first `n` replacements. -/
noncomputable def removedNeighborCount
    (D : ConcretePathDeformation O Cprime) (u : V) (n : Nat) : Nat :=
  ∑ t ∈ Finset.range n, adjacencyBit G u (D.removedAtNat t)

/-- Split a sum over `0, ..., 2n-1` into its even and odd terms. -/
theorem sum_range_two_mul (f : Nat → Nat) (n : Nat) :
    (∑ q ∈ Finset.range (2 * n), f q) =
      (∑ t ∈ Finset.range n, f (2 * t)) +
        ∑ t ∈ Finset.range n, f (2 * t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- Cardinality of a finite predicate is the sum of its `0`/`1`
indicators. -/
theorem ncard_eq_sum_adjacencyBit
    {W : Type*} [Fintype W] (H : SimpleGraph V)
    (u : V) (v : W → V) :
    ({q : W | H.Adj u (v q)} : Set W).ncard =
      ∑ q : W, adjacencyBit H u (v q) := by
  classical
  let S : Set W := {q | H.Adj u (v q)}
  let hS : S.Finite := S.toFinite
  rw [Set.ncard_eq_toFinset_card S hS]
  have hfin : hS.toFinset =
      Finset.univ.filter (fun q => H.Adj u (v q)) := by
    ext q
    simp [S]
  rw [hfin, Finset.card_filter]
  rfl

/-- Under the complete `j₀-k₀-j₁-k₁-⋯` path order, the
active-path neighbor count is the sum of introduced and removed neighbor
counts. -/
theorem pathNeighborCount_eq_introduced_add_removed
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hcard : D.path.card = 2 * D.deformation.stepCount)
    (u : V) :
    (D.path.neighborIndexSet u).ncard =
      D.introducedNeighborCount u D.deformation.stepCount +
        D.removedNeighborCount u D.deformation.stepCount := by
  classical
  let f : Nat → Nat := fun q =>
    if hq : q < D.path.card then
      adjacencyBit G u (D.path.vertex ⟨q, hq⟩)
    else
      0
  have hfin :
      (∑ q : Fin D.path.card,
          adjacencyBit G u (D.path.vertex q)) =
        ∑ q ∈ Finset.range D.path.card, f q := by
    rw [← Fin.sum_univ_eq_sum_range f D.path.card]
    apply Finset.sum_congr rfl
    intro q _hq
    simp [f]
  have heven :
      (∑ t ∈ Finset.range D.deformation.stepCount, f (2 * t)) =
        D.introducedNeighborCount u D.deformation.stepCount := by
    unfold introducedNeighborCount
    apply Finset.sum_congr rfl
    intro t ht
    have htlt : t < D.deformation.stepCount := Finset.mem_range.mp ht
    have hq : 2 * t < D.path.card := by
      rw [hcard]
      omega
    have hindex :
        (⟨2 * t, hq⟩ : Fin D.path.card) =
          L.introducedPathIndex ⟨t, htlt⟩ := by
      apply Fin.ext
      simpa using (L.introduced_index_val ⟨t, htlt⟩).symm
    rw [show f (2 * t) =
        adjacencyBit G u (D.path.vertex ⟨2 * t, hq⟩) by
          simp [f, hq]]
    rw [hindex, L.introduced_eq]
    rw [D.introducedAtNat_of_lt htlt]
  have hodd :
      (∑ t ∈ Finset.range D.deformation.stepCount,
          f (2 * t + 1)) =
        D.removedNeighborCount u D.deformation.stepCount := by
    unfold removedNeighborCount
    apply Finset.sum_congr rfl
    intro t ht
    have htlt : t < D.deformation.stepCount := Finset.mem_range.mp ht
    have hq : 2 * t + 1 < D.path.card := by
      rw [hcard]
      omega
    have hindex :
        (⟨2 * t + 1, hq⟩ : Fin D.path.card) =
          L.removedPathIndex ⟨t, htlt⟩ := by
      apply Fin.ext
      simpa using (L.removed_index_val ⟨t, htlt⟩).symm
    rw [show f (2 * t + 1) =
        adjacencyBit G u (D.path.vertex ⟨2 * t + 1, hq⟩) by
          simp [f, hq]]
    rw [hindex, L.removed_eq]
    rw [D.removedAtNat_of_lt htlt]
  change ({q : Fin D.path.card | G.Adj u (D.path.vertex q)} :
      Set (Fin D.path.card)).ncard = _
  rw [ncard_eq_sum_adjacencyBit G u D.path.vertex, hfin]
  rw [hcard, sum_range_two_mul f D.deformation.stepCount,
    heven, hodd]

/-- Step indices whose introduced vertices neighbor `u`. -/
def introducedNeighborStepSet
    (D : ConcretePathDeformation O Cprime) (u : V) :
    Set (Fin D.deformation.stepCount) :=
  {i | G.Adj u (D.deformation.step i).introduced}

/-- Step indices whose removed vertices neighbor `u`. -/
def removedNeighborStepSet
    (D : ConcretePathDeformation O Cprime) (u : V) :
    Set (Fin D.deformation.stepCount) :=
  {i | G.Adj u
    ((D.deformation.step i).before.vertex
      (D.deformation.step i).removedIndex)}

/-- The recursive introduced-neighbor count agrees with the finite set of
introduced-neighbor steps. -/
theorem introducedNeighborCount_eq_ncard
    (D : ConcretePathDeformation O Cprime) (u : V) :
    D.introducedNeighborCount u D.deformation.stepCount =
      (D.introducedNeighborStepSet u).ncard := by
  classical
  unfold introducedNeighborStepSet
  rw [ncard_eq_sum_adjacencyBit G u
    (fun i : Fin D.deformation.stepCount =>
      (D.deformation.step i).introduced)]
  unfold introducedNeighborCount
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => adjacencyBit G u (D.introducedAtNat t))
    D.deformation.stepCount]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [D.introducedAtNat_of_lt i.isLt]

/-- The recursive removed-neighbor count agrees with the finite set of
removed-neighbor steps. -/
theorem removedNeighborCount_eq_ncard
    (D : ConcretePathDeformation O Cprime) (u : V) :
    D.removedNeighborCount u D.deformation.stepCount =
      (D.removedNeighborStepSet u).ncard := by
  classical
  unfold removedNeighborStepSet
  rw [ncard_eq_sum_adjacencyBit G u
    (fun i : Fin D.deformation.stepCount =>
      (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex)]
  unfold removedNeighborCount
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => adjacencyBit G u (D.removedAtNat t))
    D.deformation.stepCount]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [D.removedAtNat_of_lt i.isLt]

/-- Every index of the complete alternating active path is either an
introduced (even) index or a removed (odd) index. -/
theorem pathIndex_introduced_or_removed
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hcard : D.path.card = 2 * D.deformation.stepCount)
    (q : Fin D.path.card) :
    (∃ i : Fin D.deformation.stepCount,
      q = L.introducedPathIndex i) ∨
    (∃ i : Fin D.deformation.stepCount,
      q = L.removedPathIndex i) := by
  by_cases heven : q.val % 2 = 0
  · let t : Nat := q.val / 2
    have hqval : q.val = 2 * t := by
      dsimp [t]
      omega
    have ht : t < D.deformation.stepCount := by
      have hqLt : q.val < 2 * D.deformation.stepCount := by
        calc
          q.val < D.path.card := q.isLt
          _ = 2 * D.deformation.stepCount := hcard
      omega
    left
    refine ⟨⟨t, ht⟩, Fin.ext ?_⟩
    rw [L.introduced_index_val]
    exact hqval
  · let t : Nat := q.val / 2
    have hqval : q.val = 2 * t + 1 := by
      dsimp [t]
      omega
    have ht : t < D.deformation.stepCount := by
      have hqLt : q.val < 2 * D.deformation.stepCount := by
        calc
          q.val < D.path.card := q.isLt
          _ = 2 * D.deformation.stepCount := hcard
      omega
    right
    refine ⟨⟨t, ht⟩, Fin.ext ?_⟩
    rw [L.removed_index_val]
    exact hqval

/-- Introduced and removed path indices are disjoint. -/
theorem introducedPathIndex_ne_removedPathIndex
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (i j : Fin D.deformation.stepCount) :
    L.introducedPathIndex i ≠ L.removedPathIndex j := by
  intro h
  have hval := congrArg Fin.val h
  rw [L.introduced_index_val, L.removed_index_val] at hval
  omega

/-- Adjacent active-path indices lie on opposite introduced/removed
sides. -/
theorem adjacent_introduced_iff_removed
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hcard : D.path.card = 2 * D.deformation.stepCount)
    {p q : Fin D.path.card}
    (hpq : G.Adj (D.path.vertex p) (D.path.vertex q)) :
    (∃ i, p = L.introducedPathIndex i) ↔
      (∃ j, q = L.removedPathIndex j) := by
  rcases D.pathIndex_introduced_or_removed L hcard p with hpI | hpR
  · rcases hpI with ⟨i, rfl⟩
    constructor
    · intro _
      rcases D.pathIndex_introduced_or_removed L hcard q with hqI | hqR
      · obtain ⟨j, hq⟩ := hqI
        have hadj := (D.path.adj_iff
          (L.introducedPathIndex i) q).1 hpq
        rw [hq, L.introduced_index_val, L.introduced_index_val] at hadj
        omega
      · exact hqR
    · intro _
      exact ⟨i, rfl⟩
  · rcases hpR with ⟨i, hpi⟩
    constructor
    · rintro ⟨j, hpj⟩
      subst p
      exact (D.introducedPathIndex_ne_removedPathIndex L j i hpj.symm).elim
    · intro hqR
      rcases hqR with ⟨j, hqj⟩
      have hadj := (D.path.adj_iff p q).1 hpq
      rw [hpi, hqj, L.removed_index_val, L.removed_index_val] at hadj
      omega

/-- The only three-neighbor orientation not giving a net degree increase
must acquire a fourth path neighbor.  The next module derives this local
extension from the prime-hole and component geometry. -/
def RemovedIntroducedRemovedExtension
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (u : V) : Prop :=
  ∀ {a b c : Fin D.path.card},
    a ≠ b → a ≠ c → b ≠ c →
    G.IsInducedPathTriple
      (D.path.vertex a) (D.path.vertex b) (D.path.vertex c) →
    (∃ i, a = L.removedPathIndex i) →
    (∃ j, b = L.introducedPathIndex j) →
    (∃ k, c = L.removedPathIndex k) →
    G.Adj u (D.path.vertex a) →
    G.Adj u (D.path.vertex b) →
    G.Adj u (D.path.vertex c) →
    ∃ d : Fin D.path.card,
      G.Adj u (D.path.vertex d) ∧
      d ≠ a ∧ d ≠ b ∧ d ≠ c

/-- One introduced neighbor gives a positive introduced-step count. -/
theorem one_le_introducedNeighborCount
    (D : ConcretePathDeformation O Cprime) {u : V}
    {i : Fin D.deformation.stepCount}
    (hi : G.Adj u (D.deformation.step i).introduced) :
    1 ≤ D.introducedNeighborCount u D.deformation.stepCount := by
  rw [D.introducedNeighborCount_eq_ncard]
  have hsubset : ({i} : Set (Fin D.deformation.stepCount)) ⊆
      D.introducedNeighborStepSet u := by
    intro j hj
    simpa [introducedNeighborStepSet] using hj ▸ hi
  calc
    1 = ({i} : Set (Fin D.deformation.stepCount)).ncard := by simp
    _ ≤ (D.introducedNeighborStepSet u).ncard :=
      Set.ncard_le_ncard hsubset

/-- Two distinct introduced neighbors give introduced-step count at least
two. -/
theorem two_le_introducedNeighborCount
    (D : ConcretePathDeformation O Cprime) {u : V}
    {i j : Fin D.deformation.stepCount} (hij : i ≠ j)
    (hi : G.Adj u (D.deformation.step i).introduced)
    (hj : G.Adj u (D.deformation.step j).introduced) :
    2 ≤ D.introducedNeighborCount u D.deformation.stepCount := by
  rw [D.introducedNeighborCount_eq_ncard]
  have hsubset : ({i, j} : Set (Fin D.deformation.stepCount)) ⊆
      D.introducedNeighborStepSet u := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  calc
    2 = ({i, j} : Set (Fin D.deformation.stepCount)).ncard := by
      simp [hij]
    _ ≤ (D.introducedNeighborStepSet u).ncard :=
      Set.ncard_le_ncard hsubset

/-- One removed neighbor gives a positive removed-step count. -/
theorem one_le_removedNeighborCount
    (D : ConcretePathDeformation O Cprime) {u : V}
    {i : Fin D.deformation.stepCount}
    (hi : G.Adj u
      ((D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex)) :
    1 ≤ D.removedNeighborCount u D.deformation.stepCount := by
  rw [D.removedNeighborCount_eq_ncard]
  have hsubset : ({i} : Set (Fin D.deformation.stepCount)) ⊆
      D.removedNeighborStepSet u := by
    intro j hj
    simpa [removedNeighborStepSet] using hj ▸ hi
  calc
    1 = ({i} : Set (Fin D.deformation.stepCount)).ncard := by simp
    _ ≤ (D.removedNeighborStepSet u).ncard :=
      Set.ncard_le_ncard hsubset

/-- Anticommutation, Lemma 7, and the two endpoint/local extension facts
force exactly one more introduced neighbor than removed neighbor. -/
theorem anticommuting_neighborCount_balance
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hcard : D.path.card = 2 * D.deformation.stepCount)
    (hclaw : G.IsClawFree) {u : V}
    (huOutside : u ∉ Set.range D.path.vertex)
    (hanti : D.path.AnticommutesWith u)
    (hterminal : ∀ q : Fin D.path.card,
      q.val + 1 = D.path.card →
      ¬G.Adj u (D.path.vertex q))
    (hextend : D.RemovedIntroducedRemovedExtension L u) :
    D.introducedNeighborCount u D.deformation.stepCount =
      D.removedNeighborCount u D.deformation.stepCount + 1 := by
  classical
  have hsum := D.pathNeighborCount_eq_introduced_add_removed L hcard u
  have hcases :=
    D.path.anticommutesWith_count_eq_one_or_three
      hclaw huOutside hanti
  rcases hcases with hone | hthree
  · obtain ⟨p, hpSet⟩ := Set.ncard_eq_one.mp hone
    have hpAdj : G.Adj u (D.path.vertex p) := by
      change p ∈ D.path.neighborIndexSet u
      rw [hpSet]
      simp
    have hpEndpoint : D.path.IsEndpointIndex p := by
      rcases D.path.lemma7 hclaw huOutside with
        hzero | hOne | htwo | hthree' | hfour
      · omega
      · exact hOne.2 p hpAdj
      · omega
      · omega
      · omega
    have hpFirst : p.val = 0 := by
      rcases hpEndpoint with hpFirst | hpLast
      · exact hpFirst
      · exact (hterminal p hpLast hpAdj).elim
    let first : Fin D.deformation.stepCount := D.firstIndex
    have hpIndex : p = L.introducedPathIndex first := by
      apply Fin.ext
      rw [L.introduced_index_val]
      simpa [first, firstIndex] using hpFirst
    have hIntro :
        G.Adj u (D.deformation.step first).introduced := by
      rw [← L.introduced_eq first, ← hpIndex]
      exact hpAdj
    have hI : 1 ≤
        D.introducedNeighborCount u D.deformation.stepCount :=
      D.one_le_introducedNeighborCount hIntro
    rw [hone] at hsum
    omega
  · obtain ⟨p, q, r, hpq, hpr, hqr, hpSet⟩ :=
      Set.ncard_eq_three.mp hthree
    have hpAdj : G.Adj u (D.path.vertex p) := by
      change p ∈ D.path.neighborIndexSet u
      rw [hpSet]
      simp
    have hqAdj : G.Adj u (D.path.vertex q) := by
      change q ∈ D.path.neighborIndexSet u
      rw [hpSet]
      simp
    have hrAdj : G.Adj u (D.path.vertex r) := by
      change r ∈ D.path.neighborIndexSet u
      rw [hpSet]
      simp
    have hexact : ∀ k : Fin D.path.card,
        G.Adj u (D.path.vertex k) →
          k = p ∨ k = q ∨ k = r := by
      intro k hk
      change k ∈ D.path.neighborIndexSet u at hk
      rw [hpSet] at hk
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
    have hshape := D.path.three_external_neighbors_classification
      hclaw huOutside hpq hpr hqr hpAdj hqAdj hrAdj hexact
    have goodTriple
        (a b c : Fin D.path.card)
        (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
        (haAdj : G.Adj u (D.path.vertex a))
        (hbAdj : G.Adj u (D.path.vertex b))
        (hcAdj : G.Adj u (D.path.vertex c))
        (hpath : G.IsInducedPathTriple
          (D.path.vertex a) (D.path.vertex b) (D.path.vertex c))
        (hexactABC : ∀ d : Fin D.path.card,
          G.Adj u (D.path.vertex d) →
            d = a ∨ d = b ∨ d = c) :
        2 ≤ D.introducedNeighborCount u D.deformation.stepCount ∧
          1 ≤ D.removedNeighborCount u D.deformation.stepCount := by
      rcases D.pathIndex_introduced_or_removed L hcard b with hbI | hbR
      · obtain ⟨ib, hib⟩ := hbI
        have haR : ∃ ia, a = L.removedPathIndex ia := by
          rcases D.pathIndex_introduced_or_removed L hcard a with haI | haR
          · obtain ⟨ia, hia⟩ := haI
            have hbR' :=
              (D.adjacent_introduced_iff_removed L hcard hpath.1).mp
                ⟨ia, hia⟩
            obtain ⟨j, hj⟩ := hbR'
            exact (D.introducedPathIndex_ne_removedPathIndex L ib j
              (hib.symm.trans hj)).elim
          · exact haR
        have hcR : ∃ ic, c = L.removedPathIndex ic := by
          rcases D.pathIndex_introduced_or_removed L hcard c with hcI | hcR
          · obtain ⟨ic, hic⟩ := hcI
            have hbR' :=
              (D.adjacent_introduced_iff_removed L hcard hpath.2.1.symm).mp
                ⟨ic, hic⟩
            obtain ⟨j, hj⟩ := hbR'
            exact (D.introducedPathIndex_ne_removedPathIndex L ib j
              (hib.symm.trans hj)).elim
          · exact hcR
        obtain ⟨d, hdAdj, hda, hdb, hdc⟩ :=
          hextend hab hac hbc hpath haR ⟨ib, hib⟩ hcR
            haAdj hbAdj hcAdj
        rcases hexactABC d hdAdj with hdp | hdq | hdr
        · exact (hda hdp).elim
        · exact (hdb hdq).elim
        · exact (hdc hdr).elim
      · obtain ⟨ib, hib⟩ := hbR
        have haI : ∃ ia, a = L.introducedPathIndex ia :=
          (D.adjacent_introduced_iff_removed L hcard hpath.1).mpr
            ⟨ib, hib⟩
        have hcI : ∃ ic, c = L.introducedPathIndex ic :=
          (D.adjacent_introduced_iff_removed L hcard hpath.2.1.symm).mpr
            ⟨ib, hib⟩
        obtain ⟨ia, hia⟩ := haI
        obtain ⟨ic, hic⟩ := hcI
        have hiac : ia ≠ ic := by
          intro h
          apply hac
          rw [hia, hic, h]
        have haIntro :
            G.Adj u (D.deformation.step ia).introduced := by
          rw [← L.introduced_eq ia, ← hia]
          exact haAdj
        have hcIntro :
            G.Adj u (D.deformation.step ic).introduced := by
          rw [← L.introduced_eq ic, ← hic]
          exact hcAdj
        have hbRemoved : G.Adj u
            ((D.deformation.step ib).before.vertex
              (D.deformation.step ib).removedIndex) := by
          rw [← L.removed_eq ib, ← hib]
          exact hbAdj
        exact ⟨D.two_le_introducedNeighborCount hiac haIntro hcIntro,
          D.one_le_removedNeighborCount hbRemoved⟩
    have hbounds :
        2 ≤ D.introducedNeighborCount u D.deformation.stepCount ∧
          1 ≤ D.removedNeighborCount u D.deformation.stepCount := by
      rcases hshape with hpath | hendpoint
      · rcases hpath with hpCenter | hqCenter | hrCenter
        · exact goodTriple q p r hpq.symm hqr hpr
            hqAdj hpAdj hrAdj hpCenter (by
              intro d hd
              rcases hexact d hd with hdp | hdq | hdr
              · exact Or.inr (Or.inl hdp)
              · exact Or.inl hdq
              · exact Or.inr (Or.inr hdr))
        · exact goodTriple p q r hpq hpr hqr
            hpAdj hqAdj hrAdj hqCenter hexact
        · exact goodTriple p r q hpr hpq hqr.symm
            hpAdj hrAdj hqAdj hrCenter (by
              intro d hd
              rcases hexact d hd with hdp | hdq | hdr
              · exact Or.inl hdp
              · exact Or.inr (Or.inr hdq)
              · exact Or.inr (Or.inl hdr))
      · have endpointGood
            (e a b : Fin D.path.card)
            (hea : e ≠ a) (heb : e ≠ b) (hab : a ≠ b)
            (heAdj : G.Adj u (D.path.vertex e))
            (haAdj : G.Adj u (D.path.vertex a))
            (hbAdj : G.Adj u (D.path.vertex b))
            (he : D.path.IsEndpointIndex e)
            (habAdj : G.Adj (D.path.vertex a) (D.path.vertex b)) :
            2 ≤ D.introducedNeighborCount u D.deformation.stepCount ∧
              1 ≤ D.removedNeighborCount u D.deformation.stepCount := by
          have heFirst : e.val = 0 := by
            rcases he with heFirst | heLast
            · exact heFirst
            · exact (hterminal e heLast heAdj).elim
          let first : Fin D.deformation.stepCount := D.firstIndex
          have heI : e = L.introducedPathIndex first := by
            apply Fin.ext
            rw [L.introduced_index_val]
            simpa [first, firstIndex] using heFirst
          rcases D.pathIndex_introduced_or_removed L hcard a with haI | haR
          · obtain ⟨ia, hia⟩ := haI
            have hbR :=
              (D.adjacent_introduced_iff_removed L hcard habAdj).mp
                ⟨ia, hia⟩
            obtain ⟨ib, hib⟩ := hbR
            have hfirstia : first ≠ ia := by
              intro h
              apply hea
              rw [heI, hia, h]
            have heIntro : G.Adj u
                (D.deformation.step first).introduced := by
              rw [← L.introduced_eq first, ← heI]
              exact heAdj
            have haIntro : G.Adj u
                (D.deformation.step ia).introduced := by
              rw [← L.introduced_eq ia, ← hia]
              exact haAdj
            have hbRemoved : G.Adj u
                ((D.deformation.step ib).before.vertex
                  (D.deformation.step ib).removedIndex) := by
              rw [← L.removed_eq ib, ← hib]
              exact hbAdj
            exact ⟨D.two_le_introducedNeighborCount
                hfirstia heIntro haIntro,
              D.one_le_removedNeighborCount hbRemoved⟩
          · obtain ⟨ia, hia⟩ := haR
            have hbI :=
              (D.adjacent_introduced_iff_removed L hcard habAdj.symm).mpr
                ⟨ia, hia⟩
            obtain ⟨ib, hib⟩ := hbI
            have hfirstib : first ≠ ib := by
              intro h
              apply heb
              rw [heI, hib, h]
            have heIntro : G.Adj u
                (D.deformation.step first).introduced := by
              rw [← L.introduced_eq first, ← heI]
              exact heAdj
            have hbIntro : G.Adj u
                (D.deformation.step ib).introduced := by
              rw [← L.introduced_eq ib, ← hib]
              exact hbAdj
            have haRemoved : G.Adj u
                ((D.deformation.step ia).before.vertex
                  (D.deformation.step ia).removedIndex) := by
              rw [← L.removed_eq ia, ← hia]
              exact haAdj
            exact ⟨D.two_le_introducedNeighborCount
                hfirstib heIntro hbIntro,
              D.one_le_removedNeighborCount haRemoved⟩
        rcases hendpoint with hpEnd | hqEnd | hrEnd
        · exact endpointGood p q r hpq hpr hqr
            hpAdj hqAdj hrAdj hpEnd.1 hpEnd.2
        · exact endpointGood q p r hpq.symm hqr hpr
            hqAdj hpAdj hrAdj hqEnd.1 hqEnd.2
        · exact endpointGood r p q hpr.symm hqr.symm hpq
            hrAdj hpAdj hqAdj hrEnd.1 hrEnd.2
    rw [hthree] at hsum
    omega

/-- Definition 19 data additionally needed by the anticommuting half of
Lemma 11.  The terminal nonedge is the endpoint consequence used in the
paper after Corollaries 2 and 7; all interior three-neighbor geometry is
derived below rather than stored here. -/
structure FullDefinition19Lemma11AData
    (D : ConcretePathDeformation O Cprime) where
  neighborhood : D.FullDefinition19NeighborhoodData
  path_card_eq :
    D.path.card = 2 * D.deformation.stepCount
  terminalRemoved_not_mem_prime :
    (D.deformation.step D.lastIndex).before.vertex
        (D.deformation.step D.lastIndex).removedIndex ∉ Cprime
  terminalAnticommutingNonadjacency :
    ∀ {u : V},
      u ∈ Cprime →
      u ∉ Set.range D.path.vertex →
      D.path.AnticommutesWith u →
      ∀ q : Fin D.path.card,
        q.val + 1 = D.path.card →
        ¬G.Adj u (D.path.vertex q)
  primeA_mem_cc :
    ∀ i : Fin neighborhood.primeHalfLength,
      neighborhood.primeHole.labeling.a i ∈ O.Cc

namespace FullDefinition19Lemma11AData

variable {D : ConcretePathDeformation O Cprime}

/-- The last path index is the vertex removed at the last step. -/
theorem lastPathVertex_eq_terminalRemoved
    (F : D.FullDefinition19Lemma11AData)
    (q : Fin D.path.card)
    (hq : q.val + 1 = D.path.card) :
    D.path.vertex q =
      (D.deformation.step D.lastIndex).before.vertex
        (D.deformation.step D.lastIndex).removedIndex := by
  have hindex : q =
      F.neighborhood.pathOrder.removedPathIndex D.lastIndex := by
    apply Fin.ext
    rw [F.neighborhood.pathOrder.removed_index_val]
    have hpos := D.nonempty
    have hlastVal : D.lastIndex.val =
        D.deformation.stepCount - 1 := rfl
    have hcard := F.path_card_eq
    omega
  rw [hindex, F.neighborhood.pathOrder.removed_eq]

/-- A prime-hole anticommuting vertex distinct from `j₀` lies outside
the active path. -/
theorem anticommuting_not_mem_path
    (F : D.FullDefinition19Lemma11AData)
    {u : V}
    (huPrime : u ∈ Cprime)
    (huNeFirst : u ≠
      (D.deformation.step D.firstIndex).introduced)
    (hanti : D.path.AnticommutesWith u) :
    u ∉ Set.range D.path.vertex := by
  intro huPath
  obtain ⟨q, hqu, hqEndpoint⟩ :=
    D.path.endpoint_of_mem_range_of_anticommutesWith huPath hanti
  rcases hqEndpoint with hqFirst | hqLast
  · apply huNeFirst
    calc
      u = D.path.vertex q := hqu.symm
      _ = D.path.vertex
          (F.neighborhood.pathOrder.introducedPathIndex D.firstIndex) := by
        congr 1
        apply Fin.ext
        rw [F.neighborhood.pathOrder.introduced_index_val]
        simpa [firstIndex] using hqFirst
      _ = (D.deformation.step D.firstIndex).introduced :=
        F.neighborhood.pathOrder.introduced_eq D.firstIndex
  · apply F.terminalRemoved_not_mem_prime
    have hremovedEq :
        (D.deformation.step D.lastIndex).before.vertex
            (D.deformation.step D.lastIndex).removedIndex = u :=
      (F.lastPathVertex_eq_terminalRemoved q hqLast).symm.trans hqu
    rw [hremovedEq]
    exact huPrime

end FullDefinition19Lemma11AData

/-- The prime-hole alternation and `C_a ∪ C'_c` component maximality
discharge the bad removed-introduced-removed orientation in Lemma 7. -/
theorem removedIntroducedRemovedExtension_of_fullDefinition19
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {u : V} (huPrime : u ∈ Cprime) :
    D.RemovedIntroducedRemovedExtension
      F.neighborhood.pathOrder u := by
  classical
  let L := F.neighborhood.pathOrder
  let M := F.neighborhood.mechanical
  let P := F.neighborhood.primeHole
  intro a b c hab hac hbc hpath haSide hbSide hcSide
    hua hub huc
  obtain ⟨ia, ha⟩ := haSide
  obtain ⟨ib, hb⟩ := hbSide
  obtain ⟨ic, hc⟩ := hcSide
  have hiac : ia ≠ ic := by
    intro h
    apply hac
    rw [ha, hc, h]
  have oriented
      (x z : Fin D.path.card)
      (ix iz : Fin D.deformation.stepCount)
      (hx : x = L.removedPathIndex ix)
      (hz : z = L.removedPathIndex iz)
      (hixiz : ix.val < iz.val)
      (hxb : x ≠ b) (hxz : x ≠ z) (hbz : b ≠ z)
      (hpath' : G.IsInducedPathTriple
        (D.path.vertex x) (D.path.vertex b) (D.path.vertex z))
      (hux : G.Adj u (D.path.vertex x))
      (huz : G.Adj u (D.path.vertex z)) :
      ∃ d : Fin D.path.card,
        G.Adj u (D.path.vertex d) ∧
        d ≠ x ∧ d ≠ b ∧ d ≠ z := by
    have hxbIndex := (D.path.adj_iff x b).1 hpath'.1
    have hbzIndex := (D.path.adj_iff b z).1 hpath'.2.1
    have hibSucc : ib.val = ix.val + 1 := by
      rw [hx, hb, L.removed_index_val,
        L.introduced_index_val] at hxbIndex
      rw [hb, hz, L.introduced_index_val,
        L.removed_index_val] at hbzIndex
      omega
    have hiz : iz.val = ib.val := by
      rw [hx, hb, L.removed_index_val,
        L.introduced_index_val] at hxbIndex
      rw [hb, hz, L.introduced_index_val,
        L.removed_index_val] at hbzIndex
      omega
    let previousIntroduced : Fin D.path.card :=
      L.introducedPathIndex ix
    have hpreviousVal :
        previousIntroduced.val + 1 = x.val := by
      dsimp [previousIntroduced]
      rw [L.introduced_index_val, hx, L.removed_index_val]
    have hprevious_b : previousIntroduced ≠ b := by
      intro h
      have hval := congrArg Fin.val h
      dsimp [previousIntroduced] at hval
      rw [L.introduced_index_val, hb,
        L.introduced_index_val] at hval
      omega
    have hprevious_x : previousIntroduced ≠ x := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hprevious_z : previousIntroduced ≠ z := by
      intro h
      have hval := congrArg Fin.val h
      rw [hz, L.removed_index_val] at hval
      dsimp [previousIntroduced] at hval
      rw [L.introduced_index_val] at hval
      omega
    have hpreviousAdjX :
        G.Adj (D.path.vertex previousIntroduced)
          (D.path.vertex x) :=
      (D.path.adj_iff previousIntroduced x).2
        (Or.inl hpreviousVal)
    have hubIntroduced :
        G.Adj u (D.deformation.step ib).introduced := by
      rw [← L.introduced_eq ib, ← hb]
      exact hub
    obtain ⟨q, huq⟩ :=
      P.eq_b_of_mem_prime_and_adj_introduced
        ib huPrime hubIntroduced
    let r₀ : Fin F.neighborhood.primeHalfLength :=
      P.introducedIndex ib
    have hbPrimeA : P.labeling.a r₀ = D.path.vertex b := by
      calc
        P.labeling.a r₀ =
            (D.deformation.step ib).introduced := by
          simpa [r₀] using P.introduced_eq ib
        _ = D.path.vertex (L.introducedPathIndex ib) :=
          (L.introduced_eq ib).symm
        _ = D.path.vertex b := by rw [← hb]
    have hprimeAdj :
        G.Adj (P.labeling.a r₀) (P.labeling.b q) := by
      rw [hbPrimeA, ← huq]
      exact hub.symm
    obtain ⟨r', hr'ne, hr'Adj⟩ :
        ∃ r' : Fin F.neighborhood.primeHalfLength,
          r' ≠ r₀ ∧
          G.Adj (P.labeling.b q) (P.labeling.a r') := by
      rcases (P.labeling.adj_ab_iff r₀ q).1 hprimeAdj with hq | hq
      · subst q
        refine ⟨P.labeling.prev r₀,
          P.labeling.prev_ne r₀, ?_⟩
        exact (P.labeling.adj_a_prev_b r₀).symm
      · subst q
        refine ⟨P.labeling.next r₀,
          P.labeling.next_ne r₀, ?_⟩
        exact (P.labeling.adj_a_b (P.labeling.next r₀)).symm
    let v : V := P.labeling.a r'
    have huv : G.Adj u v := by
      rw [huq]
      exact hr'Adj
    have hvPrime : v ∈ Cprime := by
      exact P.mem_prime_of_mem_carrier
        (P.labeling.a_mem_carrier r')
    have hvCc : v ∈ O.Cc := F.primeA_mem_cc r'
    have hbCc : D.path.vertex b ∈ O.Cc := by
      rw [hb, L.introduced_eq]
      exact (M.stepGeometry ib).base.introduced_cc
    have hpreviousCc :
        D.path.vertex previousIntroduced ∈ O.Cc := by
      dsimp [previousIntroduced]
      rw [L.introduced_eq]
      exact (M.stepGeometry ix).base.introduced_cc
    have hvNeB : v ≠ D.path.vertex b := by
      intro h
      apply hr'ne
      apply P.labeling.a_injective
      rw [hbPrimeA]
      exact h
    by_cases hvPrevious : v = D.path.vertex previousIntroduced
    · refine ⟨previousIntroduced, ?_, hprevious_x, hprevious_b,
        hprevious_z⟩
      rw [← hvPrevious]
      exact huv
    have hvNotAdjX : ¬G.Adj v (D.path.vertex x) := by
      intro hvx
      have hleaves := hclaw
        hpreviousAdjX.symm hpath'.1 hvx.symm
        (fun h => hprevious_b (D.path.injective h))
        (fun h => hvPrevious h.symm)
        hvNeB.symm
      rcases hleaves with hpB | hpV | hbV
      · exact (M.stepGeometry ix).base.cc_independent
          hpreviousCc hbCc hpB
      · exact (M.stepGeometry ix).base.cc_independent
          hpreviousCc hvCc hpV
      · exact (M.stepGeometry ix).base.cc_independent
          hbCc hvCc hbV
    have hvNeX : v ≠ D.path.vertex x := by
      intro h
      have hxCc : D.path.vertex x ∈ O.Cc := by
        rw [← h]
        exact hvCc
      exact (M.stepGeometry ix).base.cc_independent
        hxCc hbCc hpath'.1
    have hvNeZ : v ≠ D.path.vertex z := by
      intro h
      have hzCc : D.path.vertex z ∈ O.Cc := h ▸ hvCc
      exact (M.stepGeometry iz).base.cc_independent
        hzCc hbCc hpath'.2.1.symm
    have hvAdjZ : G.Adj v (D.path.vertex z) := by
      rcases hclaw hux huz huv
          (fun h => hxz (D.path.injective h))
          (fun h => hvNeX h.symm)
          (fun h => hvNeZ h.symm) with hxzAdj | hxvAdj | hzvAdj
      · exact (hpath'.2.2.1 hxzAdj).elim
      · exact (hvNotAdjX hxvAdj.symm).elim
      · exact hzvAdj.symm
    have hzCa : D.path.vertex z ∈ O.Ca := by
      rw [hz, L.removed_eq]
      exact (M.stepGeometry iz).removed_ca
    obtain ⟨Q, hQ, hvQ, hzQ⟩ :=
      (M.stepGeometry iz).base.edgeCoverage
        hvCc hzCa hvAdjZ
    have hactiveAc : Set.range D.path.vertex ∈ O.acPaths := by
      rw [← D.activePath_eq iz]
      exact (M.stepGeometry iz).base.activePath_ac
    have hactiveQ : Set.range D.path.vertex = Q :=
      O.eq_of_mem_acPaths hactiveAc hQ ⟨z, rfl⟩ hzQ
    have hvPath : v ∈ Set.range D.path.vertex := by
      rw [hactiveQ]
      exact hvQ
    obtain ⟨d, hdv⟩ := hvPath
    refine ⟨d, ?_, ?_, ?_, ?_⟩
    · rw [hdv]
      exact huv
    · intro h
      apply hvNeX
      rw [← hdv, h]
    · intro h
      apply hvNeB
      rw [← hdv, h]
    · intro h
      apply hvNeZ
      rw [← hdv, h]
  by_cases hi : ia.val < ic.val
  · exact oriented a c ia ic ha hc hi hab hac hbc
      hpath hua huc
  · have hicia : ic.val < ia.val := by
      have hne : ia.val ≠ ic.val := by
        intro h
        exact hiac (Fin.ext h)
      omega
    obtain ⟨d, hd, hdc, hdb, hda⟩ :=
      oriented c a ic ia hc ha hicia hbc.symm hac.symm hab.symm
        ⟨hpath.2.1.symm, hpath.1.symm,
          (fun hca => hpath.2.2.1 hca.symm),
          hpath.2.2.2.symm⟩ huc hua
    exact ⟨d, hd, hda, hdb, hdc⟩

/-- One replacement satisfies the unsigned degree-balance identity. -/
theorem step_degree_balance
    (D : ConcretePathDeformation O Cprime)
    (i : Fin D.deformation.stepCount) (u : V) :
    (D.deformation.step i).degreeAfter u +
        adjacencyBit G u
          ((D.deformation.step i).before.vertex
            (D.deformation.step i).removedIndex) =
      (D.deformation.step i).degreeBefore u +
        adjacencyBit G u
          (D.deformation.step i).introduced := by
  classical
  by_cases hi : G.Adj u (D.deformation.step i).introduced <;>
    by_cases hr : G.Adj u
      ((D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex)
  · have hdegree :=
      (D.deformation.step i).deformation.externalDegree_deform_eq
        (show G.Adj u (D.deformation.step i).introduced ↔
          G.Adj u
            ((D.deformation.step i).before.vertex
              (D.deformation.step i).removedIndex) from ⟨fun _ => hr, fun _ => hi⟩)
    simpa [ConcreteDeformationStep.degreeAfter,
      ConcreteDeformationStep.degreeBefore,
      ConcreteDeformationStep.after, adjacencyBit, hi, hr] using hdegree
  · have hdegree :=
      (D.deformation.step i).deformation.externalDegree_deform_eq_add_one
        hi hr
    simpa [ConcreteDeformationStep.degreeAfter,
      ConcreteDeformationStep.degreeBefore,
      ConcreteDeformationStep.after, adjacencyBit, hi, hr] using hdegree
  · have hdegree :=
      (D.deformation.step i).deformation.externalDegree_eq_deform_add_one
        hi hr
    simpa [ConcreteDeformationStep.degreeAfter,
      ConcreteDeformationStep.degreeBefore,
      ConcreteDeformationStep.after, adjacencyBit, hi, hr] using hdegree.symm
  · have hdegree :=
      (D.deformation.step i).deformation.externalDegree_deform_eq
        (show G.Adj u (D.deformation.step i).introduced ↔
          G.Adj u
            ((D.deformation.step i).before.vertex
              (D.deformation.step i).removedIndex) from ⟨fun h => (hi h).elim, fun h => (hr h).elim⟩)
    simpa [ConcreteDeformationStep.degreeAfter,
      ConcreteDeformationStep.degreeBefore,
      ConcreteDeformationStep.after, adjacencyBit, hi, hr] using hdegree

/-- Degree balance after the first `n+1` concrete replacements. -/
theorem degree_balance_through
    (D : ConcretePathDeformation O Cprime)
    (u : V) {n : Nat} (hn : n < D.deformation.stepCount) :
    (D.deformation.step ⟨n, hn⟩).degreeAfter u +
        D.removedNeighborCount u (n + 1) =
      D.initialHole.externalDegree u +
        D.introducedNeighborCount u (n + 1) := by
  classical
  induction n with
  | zero =>
      have hbalance :=
        D.step_degree_balance (⟨0, hn⟩ : Fin D.deformation.stepCount) u
      simpa [ConcretePathDeformation.initialHole,
        ConcretePathDeformation.firstIndex,
        ConcreteDeformationStep.degreeBefore,
        introducedNeighborCount, removedNeighborCount,
        D.introducedAtNat_of_lt hn, D.removedAtNat_of_lt hn] using hbalance
  | succ n ih =>
      have hn' : n < D.deformation.stepCount := by omega
      let previous : Fin D.deformation.stepCount := ⟨n, hn'⟩
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      have hchain :
          (D.deformation.step previous).degreeAfter u =
            (D.deformation.step current).degreeBefore u :=
        D.deformation.degreeAfter_eq_nextDegreeBefore
          (i := previous) (j := current) (by rfl) u
      have hprevious :
          (D.deformation.step previous).degreeAfter u +
              D.removedNeighborCount u (n + 1) =
            D.initialHole.externalDegree u +
              D.introducedNeighborCount u (n + 1) := by
        simpa [previous] using ih hn'
      have hcurrent := D.step_degree_balance current u
      have hintroducedSucc :
          D.introducedNeighborCount u (n + 1 + 1) =
            D.introducedNeighborCount u (n + 1) +
              adjacencyBit G u (D.deformation.step current).introduced := by
        unfold introducedNeighborCount
        rw [Finset.sum_range_succ]
        rw [D.introducedAtNat_of_lt hn]
      have hremovedSucc :
          D.removedNeighborCount u (n + 1 + 1) =
            D.removedNeighborCount u (n + 1) +
              adjacencyBit G u
                ((D.deformation.step current).before.vertex
                  (D.deformation.step current).removedIndex) := by
        unfold removedNeighborCount
        rw [Finset.sum_range_succ]
        rw [D.removedAtNat_of_lt hn]
      dsimp [current, previous] at hcurrent hchain hprevious hintroducedSucc hremovedSucc
      omega

/-- The total degree balance for the complete path block. -/
theorem final_degree_balance
    (D : ConcretePathDeformation O Cprime) (u : V) :
    D.finalHole.externalDegree u +
        D.removedNeighborCount u D.deformation.stepCount =
      D.initialHole.externalDegree u +
        D.introducedNeighborCount u D.deformation.stepCount := by
  have hlast :
      D.deformation.stepCount - 1 < D.deformation.stepCount := by
    have hpos := D.nonempty
    omega
  have h := D.degree_balance_through u hlast
  have hcount : D.deformation.stepCount - 1 + 1 =
      D.deformation.stepCount := by omega
  simpa [ConcretePathDeformation.finalHole,
    ConcretePathDeformation.lastIndex,
    ConcreteDeformationStep.degreeAfter, hcount] using h

/-- If the active path has one more introduced neighbor than removed
neighbor, deforming along the entire path raises the hole degree by one. -/
theorem finalDegree_eq_initial_add_one_of_neighborCount
    (D : ConcretePathDeformation O Cprime) {u : V}
    (hcount :
      D.introducedNeighborCount u D.deformation.stepCount =
        D.removedNeighborCount u D.deformation.stepCount + 1) :
    D.finalHole.externalDegree u =
      D.initialHole.externalDegree u + 1 := by
  have hbalance := D.final_degree_balance u
  omega

/-- Lemma 11(a), first displayed equivalence, for one complete Definition
19 path block.  The right-to-left direction uses only `u ≠ j₀`; the
degree equality is then forced by the same path-neighbor balance. -/
theorem lemma11a_membership_iff_ne_first_and_degree
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    (∃ s : Nat, u ∈ D.dependentAt s) ↔
      u ≠ (D.deformation.step D.firstIndex).introduced ∧
        D.finalHole.externalDegree u =
          D.initialHole.externalDegree u + 1 := by
  constructor
  · rintro ⟨s, hu⟩
    have huNeFirst :
        u ≠ (D.deformation.step D.firstIndex).introduced := by
      intro huFirst
      have huPath : u ∈ Set.range D.path.vertex := by
        refine ⟨F.neighborhood.pathOrder.introducedPathIndex
          D.firstIndex, ?_⟩
        rw [F.neighborhood.pathOrder.introduced_eq D.firstIndex]
        exact huFirst.symm
      let i : Fin D.deformation.stepCount :=
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩
      have hui : u ∈ D.dependentAt i.val := by
        simpa [i] using hu
      obtain ⟨q, hqu, hqval⟩ :=
        D.dependent_mem_path_global_index
          F.neighborhood.pathOrder i hui huPath
      have hqFirst : q =
          F.neighborhood.pathOrder.introducedPathIndex D.firstIndex := by
        apply D.path.injective
        calc
          D.path.vertex q = u := hqu
          _ = (D.deformation.step D.firstIndex).introduced := huFirst
          _ = D.path.vertex
              (F.neighborhood.pathOrder.introducedPathIndex D.firstIndex) :=
            (F.neighborhood.pathOrder.introduced_eq D.firstIndex).symm
      have hqzero : q.val = 0 := by
        rw [hqFirst,
          F.neighborhood.pathOrder.introduced_index_val]
        rfl
      omega
    have huOutside :=
      F.anticommuting_not_mem_path huPrime huNeFirst hanti
    have hbalance := D.anticommuting_neighborCount_balance
      F.neighborhood.pathOrder F.path_card_eq hclaw
      huOutside hanti
      (F.terminalAnticommutingNonadjacency
        huPrime huOutside hanti)
      (D.removedIntroducedRemovedExtension_of_fullDefinition19
        F hclaw huPrime)
    exact ⟨huNeFirst,
      D.finalDegree_eq_initial_add_one_of_neighborCount hbalance⟩
  · rintro ⟨huNeFirst, _hdegree⟩
    have huOutside :=
      F.anticommuting_not_mem_path huPrime huNeFirst hanti
    have hbalance := D.anticommuting_neighborCount_balance
      F.neighborhood.pathOrder F.path_card_eq hclaw
      huOutside hanti
      (F.terminalAnticommutingNonadjacency
        huPrime huOutside hanti)
      (D.removedIntroducedRemovedExtension_of_fullDefinition19
        F hclaw huPrime)
    rw [D.introducedNeighborCount_eq_ncard,
      D.removedNeighborCount_eq_ncard] at hbalance
    have hnsub :
        ¬D.introducedNeighborStepSet u ⊆
          D.removedNeighborStepSet u := by
      intro hsub
      have hle := Set.ncard_le_ncard hsub
      omega
    obtain ⟨i, hiIntroduced, hiNotRemoved⟩ :=
      Set.not_subset.mp hnsub
    have hiAdj : G.Adj u (D.deformation.step i).introduced :=
      hiIntroduced
    have hiNotAdj : ¬G.Adj u
        ((D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex) :=
      hiNotRemoved
    have hiNe : u ≠
        (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex := by
      intro h
      apply huOutside
      refine ⟨F.neighborhood.pathOrder.removedPathIndex i, ?_⟩
      rw [F.neighborhood.pathOrder.removed_eq i]
      exact h.symm
    refine ⟨i.val, (D.mem_dependentAt_iff_definition20).2 ?_⟩
    exact ⟨i.isLt, huPrime, hiAdj, hiNe, hiNotAdj⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
