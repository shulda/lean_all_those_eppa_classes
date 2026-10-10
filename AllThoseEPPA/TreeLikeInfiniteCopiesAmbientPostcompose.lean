import AllThoseEPPA.Automorphism
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Transport Γ-homomorphism-embeddings by ambient automorphisms

The induction in manuscript Lemma lem:infinitecopies repeatedly
repositions the image of a tree-side homomorphism-embedding
by an automorphism of the ambient structure M. The exact
Γ-language component must be composed along with the vertex map;
we cannot treat the ambient automorphism as an unlabelled
permutation.

An ambient automorphism is a genuine Γ-embedding of M into
itself (reflection of all relations, exact set-valued
function fibres), hence its postcomposition with a
homomorphism-embedding remains a homomorphism-embedding.
-/

namespace AllThoseEPPA
namespace Structure
namespace Automorphism

universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}

/-- Regard a Γ-automorphism of A as an actual Γ-embedding
of its whole structure, retaining the language component. -/
noncomputable def toEmbedding
    (act : L.Action Γ)
    {A : Structure L V}
    (g : Automorphism act A) : Embedding act A A where
  lang := g.lang
  toFun := g
  injective := g.toEquiv.injective
  map_rel_iff := by
    intro n R xs
    exact g.map_rel_iff R xs
  map_func := by
    intro n F xs
    exact g.map_func F xs

@[simp] theorem toEmbedding_apply
    (act : L.Action Γ)
    {A : Structure L V}
    (g : Automorphism act A) (x : V) :
    g.toEmbedding act x = g x := rfl

@[simp] theorem toEmbedding_lang
    (act : L.Action Γ)
    {A : Structure L V}
    (g : Automorphism act A) :
    (g.toEmbedding act).lang = g.lang := rfl

end Automorphism

namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Postcomposition with a total automorphism preserves the
homomorphism-embedding property on *all* closed irreducible
substructures, including exact set-valued function fibres.
No global injectivity is asserted for the original f. -/
theorem postcompose_automorphism_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {M : Structure L W}
    (f : Homomorphism act A M)
    (hF : IsHomomorphismEmbedding act f)
    (g : Automorphism act M) :
    IsHomomorphismEmbedding act
      ((g.toEmbedding act).toHomomorphism.comp f) := by
  have hg : IsHomomorphismEmbedding act
      (g.toEmbedding act).toHomomorphism := by
    intro S hS hIrr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      exact (g.toEmbedding act).injective hab
    · intro n R xs hxs
      exact (g.toEmbedding act).map_rel_iff R xs
    · intro n F xs hxs
      exact (g.toEmbedding act).map_func F xs
  exact comp_isHomomorphismEmbedding
    act (g.toEmbedding act).toHomomorphism f hg hF

end Homomorphism
end Structure
end AllThoseEPPA
