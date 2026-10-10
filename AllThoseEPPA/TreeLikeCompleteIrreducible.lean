import AllThoseEPPA.TreeLikeClique

/-!
# E-complete structures are irreducible

An E-complete leaf in the recursive chordal clique-tree certificate
is a genuinely irreducible structure, not merely a graph clique.
This will allow the leaf to be embedded into the distinguished
irreducible structure A under the hypothesis of Lemma `lem:cuts`.

No finiteness, unary function hypothesis, or EPPA action is needed.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- An E-complete structure is irreducible as a structure with
arbitrary relations and set-valued functions. Any proper free
decomposition would separate two adjacent E-vertices. -/
theorem edgeComplete_isIrreducible
    (B : Structure L V) (E : L.RelSymbol 2)
    (hComplete : B.EdgeComplete E) :
    B.IsIrreducible := by
  constructor
  intro d
  have hClique : EdgeClique B E Set.univ := by
    intro x y _ _ hxy
    exact (hComplete x y).2 hxy
  rcases edgeClique_subset_one_side B E d Set.univ hClique with
    hLeft | hRight
  · apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    exact hLeft (Set.mem_univ x)
  · apply d.right_proper
    apply Set.eq_univ_of_forall
    intro x
    exact hRight (Set.mem_univ x)

end TreeLike
end AllThoseEPPA
