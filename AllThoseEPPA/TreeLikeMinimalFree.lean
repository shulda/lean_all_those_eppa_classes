import AllThoseEPPA.TreeLikeEssentialNeighbors
import AllThoseEPPA.TreeLikeTwoSidedFree

/-!
# Minimal separators already give free decompositions

The graph-theoretic essential-neighbor lemma completes a structural
chain that no longer requires a chordality assumption:

* every pair of nonadjacent vertices u,v in a finite simple graph
  has an inclusion-minimal vertex separator S;
* every vertex of that separator has neighbors in the two endpoint
  components outside S;
* in a faithful EPPA witness all these separator vertices form a
  closed set under the unary functions;
* the two distinct components therefore give an actual
  `Structure.FreeDecomposition`.

Chordality is needed later to ensure S is an E-clique and hence
irreducible, so that the two pieces can be reassembled as a *tree
amalgamation of copies of A*. It is **not** needed for the preliminary
free decomposition.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- **Finite faithful witness dichotomy, decomposition direction.**
Any two nonadjacent vertices of the distinguished E-graph of a
finite faithful EPPA witness can be separated by a genuine free
decomposition of the entire witness. -/
theorem freeDecomposition_nonempty_of_nonadjacent
    [Finite β]
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (u v : β) (huv : u ≠ v) (hno : ¬ B.Edge E u v) :
    Nonempty B.FreeDecomposition := by
  let G : SimpleGraph β :=
    faithfulGraph act A B ψ E hfix hcomplete hfaith
  have hNoAdj : ¬ G.Adj u v := hno
  obtain ⟨S, hSep, hMin⟩ :=
    exists_inclusion_minimal_separator G u v huv hNoAdj
  obtain ⟨hu, hv, hCD⟩ := hSep
  let C : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
  let D : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩
  have hBoth : ∀ x ∈ S,
      (∃ c : β, c ∈ outsideComponent G S C ∧ B.Edge E x c) ∧
      (∃ d : β, d ∈ outsideComponent G S D ∧ B.Edge E x d) := by
    intro x hx
    obtain ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩ :=
      minimal_separator_two_sided_neighbors
        G u v S hu hv hCD hMin x hx
    exact ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩
  exact ⟨freeDecomposition_of_two_sided_neighbors
    act A B ψ E hfix hcomplete hfaith S C D hCD hBoth⟩

/-- Choose the actual free decomposition supplied by the preceding
existence theorem. Separating the Prop-valued existence argument from
this choice is essential: Lean prohibits elimination of arbitrary
existential proofs directly into the data type `FreeDecomposition`. -/
noncomputable def freeDecomposition_of_nonadjacent
    [Finite β]
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (u v : β) (huv : u ≠ v) (hno : ¬ B.Edge E u v) :
    B.FreeDecomposition :=
  Classical.choice (freeDecomposition_nonempty_of_nonadjacent
    act A B ψ E hfix hcomplete hfaith u v huv hno)

end TreeLike
end AllThoseEPPA
