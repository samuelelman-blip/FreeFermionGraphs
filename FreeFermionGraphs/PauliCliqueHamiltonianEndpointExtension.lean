import FreeFermionGraphs.PauliCliqueHamiltonianOddSupportGeometry
import FreeFermionGraphs.IndexedPathAppend

/-!
# The unique-endpoint Pauli support branch is a tree extension

For a clique-rooted path, an external original vertex with one path neighbour
must neighbour the current terminal.  If its unique neighbour were the
artificial root while another path vertex existed, clique adjacency would
force a second neighbour.  The terminal append constructor therefore gives
the literal target path and the unit-weight forward contribution in Eq. (E11).
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- In the unique-neighbour branch, the endpoint is the current terminal.
The one-vertex root path is included: there its root is also its terminal. -/
theorem uniqueOriginalEndpoint_is_terminal
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {q : Fin P.path.card}
    (hjq : (G.adjoinRootAt K).Adj (some j) (P.path.vertex q))
    (hqEndpoint : P.path.IsEndpointIndex q)
    (hexact : ∀ k : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex k) → k = q) :
    q.val + 1 = P.path.card := by
  rcases hqEndpoint with hqFirst | hqLast
  · by_cases hcard : P.path.card = 1
    · omega
    · have htwo : 2 ≤ P.path.card := by
        have := P.path.nonempty
        omega
      let zero : Fin P.path.card := ⟨0, P.path.nonempty⟩
      let one : Fin P.path.card := ⟨1, by omega⟩
      have hqZero : q = zero := by
        apply Fin.ext
        exact hqFirst
      have hzeroRoot : P.path.vertex zero = none := by
        exact P.root_eq
      have hqRoot : P.path.vertex q = none := by
        rw [hqZero]
        exact hzeroRoot
      have hjRoot : (G.adjoinRootAt K).Adj (some j) none := by
        simpa only [hqRoot] using hjq
      have hjK : j ∈ K := by
        simpa using hjRoot
      have hrootOne :
          (G.adjoinRootAt K).Adj none (P.path.vertex one) := by
        have hzeroOne : (G.adjoinRootAt K).Adj
            (P.path.vertex zero) (P.path.vertex one) := by
          apply (P.path.adj_iff zero one).2
          left
          rfl
        simpa only [hzeroRoot] using hzeroOne
      cases hone : P.path.vertex one with
      | none =>
          have hOneZero : one = zero :=
            P.path.injective (hone.trans P.root_eq.symm)
          have hval := congrArg Fin.val hOneZero
          simp [one, zero] at hval
      | some v =>
          have hvK : v ∈ K := by
            rw [hone] at hrootOne
            simpa using hrootOne
          have hjv : j ≠ v := by
            intro hjv
            subst v
            exact hjOutside ⟨one, hone⟩
          have hjvAdj : G.Adj j v := hK hjK hvK hjv
          have hjOne :
              (G.adjoinRootAt K).Adj (some j) (P.path.vertex one) := by
            rw [hone]
            exact hjvAdj
          have hOneQ := hexact one hjOne
          have hval := congrArg Fin.val hOneQ
          dsimp [one, zero] at hval
          rw [hqZero] at hval
          simp [zero] at hval
  · exact hqLast

/-- The unique-endpoint support data supplies the exact terminal-extension
adjacency interface. -/
theorem terminalExtensionData_of_uniqueOriginalEndpoint
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {q : Fin P.path.card}
    (hjq : (G.adjoinRootAt K).Adj (some j) (P.path.vertex q))
    (hqEndpoint : P.path.IsEndpointIndex q)
    (hexact : ∀ k : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex k) → k = q) :
    P.path.TerminalExtensionData (some j) := by
  have hqLast := P.uniqueOriginalEndpoint_is_terminal hK
    hjOutside hjq hqEndpoint hexact
  refine ⟨hjOutside, ?_⟩
  intro k
  constructor
  · intro hjk
    rw [hexact k hjk]
    exact hqLast
  · intro hkLast
    have hkq : k = q := by
      apply Fin.ext
      omega
    simpa [hkq] using hjq

/-- The unique-endpoint branch constructs a literal longer basis path whose
new terminal is the external original vertex. -/
theorem exists_extension_of_uniqueOriginalEndpoint
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {q : Fin P.path.card}
    (hjq : (G.adjoinRootAt K).Adj (some j) (P.path.vertex q))
    (hqEndpoint : P.path.IsEndpointIndex q)
    (hexact : ∀ k : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex k) → k = q) :
    ∃ Q : CliqueRootedInducedPath G K,
      P.IsOneVertexExtension Q ∧ Q.terminalVertex = some j := by
  let hdata := P.terminalExtensionData_of_uniqueOriginalEndpoint hK
    hjOutside hjq hqEndpoint hexact
  let Q := P.appendTerminal hdata
  refine ⟨Q, P.isOneVertexExtension_appendTerminal hdata, ?_⟩
  unfold RootedInducedPath.terminalVertex
  change Fin.lastCases (some j) P.path.vertex
      ⟨P.path.card + 1 - 1, by omega⟩ = some j
  rw [show (⟨P.path.card + 1 - 1, by omega⟩ :
      Fin (P.path.card + 1)) = Fin.last P.path.card by
    apply Fin.ext
    simp]
  simp

end RootedInducedPath

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Complete unit-weight forward contribution for a classified unique-endpoint
support vertex.  The target path is constructed, not supplied. -/
theorem exists_extension_commutator_of_uniqueOriginalEndpoint
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) (hK : G.IsClique K)
    {j : V} (hjOutside : some j ∉ Set.range P.path.vertex)
    {q : Fin P.path.card}
    (hjq : (G.adjoinRootAt K).Adj (some j) (P.path.vertex q))
    (hqEndpoint : P.path.IsEndpointIndex q)
    (hexact : ∀ k : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex k) → k = q) :
    ∃ Q : CliqueRootedInducedPath G K,
      P.IsOneVertexExtension Q ∧
      algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
        ((-1 : A) - 1) * H.pathOperator Q := by
  obtain ⟨Q, hPQ, hterminal⟩ :=
    P.exists_extension_of_uniqueOriginalEndpoint hK
      hjOutside hjq hqEndpoint hexact
  exact ⟨Q, hPQ, H.extension_commutator hPQ hterminal⟩

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
