import FreeFermionGraphs.PauliCliqueHamiltonianBubbleWand

/-!
# Exhaustive constructed geometry for one external Hamiltonian vertex

The remaining endpoint-triple alternative is resolved into the three literal
geometries used in Appendix E.  A consecutive triple is a Definition 10
deformation.  A terminal endpoint with the root/first pair constructs the
empty-handle hoop.  A positive pair separated from the terminal constructs
the ordinary Definition 11 bubble wand.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- External odd support after every path-geometric target has been
constructed. -/
inductive ResolvedExternalKrylovGeometryCase
    (P : CliqueRootedInducedPath G K) (j : V) : Prop
  | endpoint
      (q : Fin P.path.card)
      (adjacent : (G.adjoinRootAt K).Adj (some j) (P.path.vertex q))
      (endpointIndex : P.path.IsEndpointIndex q)
      (exact : ∀ k : Fin P.path.card,
        (G.adjoinRootAt K).Adj (some j) (P.path.vertex k) → k = q) :
      ResolvedExternalKrylovGeometryCase P j
  | deformation
      (i : Fin P.path.card)
      (data : P.path.SingleVertexDeformation (some j) i) :
      ResolvedExternalKrylovGeometryCase P j
  | rootHoop
      (C : IndexedInducedHole G)
      (carrier : Set.range C.vertex = P.originalCarrier ∪ {j}) :
      ResolvedExternalKrylovGeometryCase P j
  | bubbleWand
      (B : BubbleWand G)
      (source : P.originalCarrier = Set.range B.path.vertex)
      (bubble : B.bubble = j)
      (ordered : ∃ htail : 2 ≤ P.path.card,
        B.path = P.originalTail htail) :
      ResolvedExternalKrylovGeometryCase P j

/-- Resolve an endpoint plus an ordered adjacent pair. -/
theorem resolve_ordered_endpoint_pair
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {endpoint left right : Fin P.path.card}
    (hel : endpoint ≠ left) (her : endpoint ≠ right)
    (hlr : left ≠ right)
    (hjEndpoint : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex endpoint))
    (hjLeft : (G.adjoinRootAt K).Adj (some j) (P.path.vertex left))
    (hjRight : (G.adjoinRootAt K).Adj (some j) (P.path.vertex right))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = endpoint ∨ q = left ∨ q = right)
    (hendpoint : P.path.IsEndpointIndex endpoint)
    (horder : left.val + 1 = right.val) :
    P.ResolvedExternalKrylovGeometryCase j := by
  have helVal : endpoint.val ≠ left.val := by
    intro h
    exact hel (Fin.ext h)
  have herVal : endpoint.val ≠ right.val := by
    intro h
    exact her (Fin.ext h)
  have hlrVal : left.val ≠ right.val := by
    intro h
    exact hlr (Fin.ext h)
  have hcardThree : 3 ≤ P.path.card := by omega
  rcases hendpoint with hroot | hterminal
  · have hrootEq : endpoint = ⟨0, P.path.nonempty⟩ := by
      apply Fin.ext
      exact hroot
    have hjRoot : (G.adjoinRootAt K).Adj (some j) none := by
      rw [← P.root_eq, ← hrootEq]
      exact hjEndpoint
    have hjK : j ∈ K := by simpa using hjRoot
    let first := P.firstOriginalIndex (by omega)
    obtain ⟨v, hv⟩ := P.vertex_eq_some_of_pos first (by
      simp [first, firstOriginalIndex])
    have hrootFirst : (G.adjoinRootAt K).Adj none (P.path.vertex first) := by
      have hadj : (G.adjoinRootAt K).Adj
          (P.path.vertex ⟨0, P.path.nonempty⟩) (P.path.vertex first) := by
        apply (P.path.adj_iff ⟨0, P.path.nonempty⟩ first).2
        left
        simp [first, firstOriginalIndex]
      rw [P.root_eq] at hadj
      exact hadj
    have hvK : v ∈ K := by
      rw [hv] at hrootFirst
      simpa using hrootFirst
    have hjv : j ≠ v := by
      intro hjv
      apply hjOutside
      exact ⟨first, hv.trans (congrArg some hjv.symm)⟩
    have hjFirst : (G.adjoinRootAt K).Adj
        (some j) (P.path.vertex first) := by
      rw [hv]
      exact hK hjK hvK hjv
    have hfirstLeft : first = left := by
      rcases hexact first hjFirst with hfirstEndpoint | hfirstLeft | hfirstRight
      · have hval := congrArg Fin.val hfirstEndpoint
        dsimp [first, firstOriginalIndex] at hval
        omega
      · exact hfirstLeft
      · have hval := congrArg Fin.val hfirstRight
        dsimp [first, firstOriginalIndex] at hval
        omega
    have hleftVal : left.val = 1 := by
      have hval := congrArg Fin.val hfirstLeft
      simpa [first, firstOriginalIndex] using hval.symm
    have hrightVal : right.val = 2 := by omega
    exact .deformation left
      (P.path.singleVertexDeformation_of_inducedPathTriple
        (left := endpoint) (center := left) (right := right) hjOutside
        hel her hlr hjEndpoint hjLeft hjRight hexact
        (P.path.consecutiveTriple (by omega) (by omega)))
  · by_cases hleftRoot : left.val = 0
    · have hrightFirst : right.val = 1 := by omega
      by_cases hshort : P.path.card = 3
      · exact .deformation right
          (P.path.singleVertexDeformation_of_inducedPathTriple
            (left := left) (center := right) (right := endpoint) hjOutside
            hlr hel.symm her.symm hjLeft hjRight hjEndpoint
            (by
              intro q hq
              rcases hexact q hq with hqe | hql | hqr
              · exact Or.inr (Or.inr hqe)
              · exact Or.inl hql
              · exact Or.inr (Or.inl hqr))
            (P.path.consecutiveTriple (by omega) (by omega)))
      · have hcardFour : 4 ≤ P.path.card := by omega
        have hleftEq : left = ⟨0, P.path.nonempty⟩ := by
          apply Fin.ext
          exact hleftRoot
        have hrightEq : right = P.firstOriginalIndex (by omega) := by
          apply Fin.ext
          simpa [firstOriginalIndex] using hrightFirst
        have hendpointEq : endpoint = P.terminalIndex := by
          apply Fin.ext
          dsimp [terminalIndex]
          omega
        obtain ⟨C, hcarrier⟩ := P.exists_rootHoop_of_root_first_terminal
          hcardFour hjOutside
          (by rw [← hrightEq]; exact hjRight)
          (by rw [← hendpointEq]; exact hjEndpoint)
          (by
            intro q hq
            rcases hexact q hq with hqe | hql | hqr
            · exact Or.inr (Or.inr (hqe.trans hendpointEq))
            · exact Or.inl (hql.trans hleftEq)
            · exact Or.inr (Or.inl (hqr.trans hrightEq)))
        exact .rootHoop C hcarrier
    · have hleftPos : 0 < left.val := by omega
      by_cases hgap : left.val + 3 < P.path.card
      · have hendpointEq : endpoint = P.terminalIndex := by
          apply Fin.ext
          dsimp [terminalIndex]
          omega
        obtain ⟨B, hsource, hbubble, hordered⟩ :=
          P.exists_bubbleWand_of_positive_pair_terminal hjOutside
            hleftPos horder hgap hjLeft hjRight
            (by rw [← hendpointEq]; exact hjEndpoint)
            (by
              intro q hq
              rcases hexact q hq with hqe | hql | hqr
              · exact Or.inr (Or.inr (hqe.trans hendpointEq))
              · exact Or.inl hql
              · exact Or.inr (Or.inl hqr))
        exact .bubbleWand B hsource hbubble hordered
      · exact .deformation right
          (P.path.singleVertexDeformation_of_inducedPathTriple
            (left := left) (center := right) (right := endpoint) hjOutside
            hlr hel.symm her.symm hjLeft hjRight hjEndpoint
            (by
              intro q hq
              rcases hexact q hq with hqe | hql | hqr
              · exact Or.inr (Or.inr hqe)
              · exact Or.inl hql
              · exact Or.inr (Or.inl hqr))
            (P.path.consecutiveTriple (by omega) (by omega)))

/-- Resolve the unordered adjacent pair in an endpoint triple. -/
theorem resolve_endpoint_pair
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {endpoint a b : Fin P.path.card}
    (hea : endpoint ≠ a) (heb : endpoint ≠ b) (hab : a ≠ b)
    (hjEndpoint : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex endpoint))
    (hjA : (G.adjoinRootAt K).Adj (some j) (P.path.vertex a))
    (hjB : (G.adjoinRootAt K).Adj (some j) (P.path.vertex b))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = endpoint ∨ q = a ∨ q = b)
    (hendpoint : P.path.IsEndpointIndex endpoint)
    (habAdj : (G.adjoinRootAt K).Adj (P.path.vertex a) (P.path.vertex b)) :
    P.ResolvedExternalKrylovGeometryCase j := by
  rcases (P.path.adj_iff a b).1 habAdj with habOrder | hbaOrder
  · exact P.resolve_ordered_endpoint_pair hK hjOutside
      hea heb hab hjEndpoint hjA hjB hexact hendpoint habOrder
  · exact P.resolve_ordered_endpoint_pair hK hjOutside
      heb hea hab.symm hjEndpoint hjB hjA
      (by
        intro q hq
        rcases hexact q hq with hqe | hqa | hqb
        · exact Or.inl hqe
        · exact Or.inr (Or.inr hqa)
        · exact Or.inr (Or.inl hqb))
      hendpoint hbaOrder

/-- Refine all external odd-support cases into constructed Appendix E
geometry. -/
theorem IndexedInducedPath.ExternalKrylovGeometryCase.resolve
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    (h : P.path.ExternalKrylovGeometryCase (some j)) :
    P.ResolvedExternalKrylovGeometryCase j := by
  rcases h with
    ⟨q, hq, hqEndpoint, hexact⟩ |
    ⟨i, hdeform⟩ |
    ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hexact, hshape⟩
  · exact .endpoint q hq hqEndpoint hexact
  · exact .deformation i hdeform
  · rcases hshape with
      ⟨hpEndpoint, hqrAdj⟩ |
      ⟨hqEndpoint, hprAdj⟩ |
      ⟨hrEndpoint, hpqAdj⟩
    · exact P.resolve_endpoint_pair hK hjOutside
        hpq hpr hqr hp hq hr hexact hpEndpoint hqrAdj
    · exact P.resolve_endpoint_pair hK hjOutside
        hpq.symm hqr hpr hq hp hr
        (by
          intro k hk
          rcases hexact k hk with hkp | hkq | hkr
          · exact Or.inr (Or.inl hkp)
          · exact Or.inl hkq
          · exact Or.inr (Or.inr hkr))
        hqEndpoint hprAdj
    · exact P.resolve_endpoint_pair hK hjOutside
        hpr.symm hqr.symm hpq hr hp hq
        (by
          intro k hk
          rcases hexact k hk with hkp | hkq | hkr
          · exact Or.inr (Or.inl hkp)
          · exact Or.inr (Or.inr hkq)
          · exact Or.inl hkr)
        hrEndpoint hpqAdj

end RootedInducedPath

end SimpleGraph
