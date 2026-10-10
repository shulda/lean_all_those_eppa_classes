import AllThoseEPPA.TreeLikeInducedEmbeddings
import AllThoseEPPA.TreeLikeFaithfulGraph

/-!
# The full `lem:cuts` embedding hypothesis implies clique irreducibles

The paper assumes that every irreducible substructure of B embeds
into A, where E is a distinguished relation fixed under language
relabeling and is complete on A. Its graph-theoretic argument needs
the weaker statement `IrreduciblesAreCliques B E`.

This bridge proves precisely that implication for arbitrary B, with
no EPPA witness or faithfulness assumption. It therefore allows the
recursive chordal-cut theorem to be applied under the *actual*
assumptions of Lemma `lem:cuts`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type x}

/-- If all irreducible substructures of B embed into an E-complete A,
then every such substructure is an E-clique.

No faithful-witness hypothesis is present: the embedding is obtained
directly from the local assumption of `lem:cuts`. -/
theorem irreduciblesAreCliques_of_everyIrreducibleEmbedsIn
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hComplete : A.EdgeComplete E)
    (hEvery : EveryIrreducibleEmbedsIn act A B) :
    IrreduciblesAreCliques B E := by
  intro S hS hIrr x y hx hy hne
  obtain ⟨f⟩ := hEvery S hS hIrr
  let sx : S := ⟨x, hx⟩
  let sy : S := ⟨y, hy⟩
  have hxy : sx ≠ sy := by
    intro hEq
    exact hne (congrArg Subtype.val hEq)
  have hA : A.Edge E (f sx) (f sy) := by
    apply (hComplete (f sx) (f sy)).2
    exact f.injective.ne hxy
  have hInduced : (B.induce S hS).Edge E sx sy :=
    (f.edge_map_iff E hfix sx sy).1 hA
  change B.rel E (Subtype.val ∘ Structure.pairTuple sx sy) at hInduced
  rw [Structure.pairTuple_map] at hInduced
  exact hInduced

end TreeLike
end AllThoseEPPA
