import AllThoseEPPA.StrongCompletionFibreBijection
import AllThoseEPPA.TreeLikeInfiniteCopiesIrreducibleHomEmb
import AllThoseEPPA.TreeLikeHomEmbComposition
import AllThoseEPPA.TreeLikeFreeCutBaseMapIdentities

/-!
# Γ-isomorphism between collapsed one-point closures

The previous module matched the fibres of a Γ-homomorphism-embedding
over two identified generator points. Here we upgrade the matching
to an EXACT Γ-structure embedding of their induced one-point
closures, using the general factorization infrastructure which
was already verified for the full-A tree constructions.

The central new fact is that every closed irreducible source
piece embeds exactly in the codomain of a homomorphism-embedding.
Each of the two one-point closures therefore admits a genuine
embedding into the common B. The first embeds into the image
of the second, so the existing Embedding.factorThrough supplies
a genuine Γ-embedding between the two source closures.

No artificial total injectivity of f is assumed.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Restriction of a homomorphism-embedding to a CLOSED IRREDUCIBLE
induced substructure is a genuine exact Γ-embedding into the
original codomain. This combines the already-checked image and
composition infrastructure and works in arbitrary arities. -/
noncomputable def restrictClosedIrreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible) :
    Embedding act (A.induce S hS) B := by
  let j : Embedding act (A.induce S hS) A :=
    Structure.inclusion act A S hS
  let q : Homomorphism act (A.induce S hS) B :=
    f.comp j.toHomomorphism
  have hj : IsHomomorphismEmbedding act j.toHomomorphism :=
    Embedding.toHomomorphism_isHomomorphismEmbedding act j
  have hq : IsHomomorphismEmbedding act q :=
    comp_isHomomorphismEmbedding act f j.toHomomorphism hf hj
  exact q.toEmbedding_of_irreducible act hq hIrr

/-- Exact restriction has the same underlying vertex map as f
on the induced carrier. -/
@[simp] theorem restrictClosedIrreducible_apply
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible)
    (a : S) :
    (f.restrictClosedIrreducible act hf S hS hIrr) a = f a.1 :=
  rfl

/-- The language part also stays equal to the original f.lang,
even for a genuinely nontrivial Γ. -/
@[simp] theorem restrictClosedIrreducible_lang
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible) :
    (f.restrictClosedIrreducible act hf S hS hIrr).lang = f.lang := by
  change f.lang * 1 = f.lang
  simp

/-- Every collision f(a)=f(b) yields a genuine Γ-embedding
between the irreducible one-point closures of a and b.
It preserves both relations (including negative tuples)
and exact set-valued unary/higher-arity function fibres. -/
noncomputable def closureFibreEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    Embedding act (A.closureAt a) (A.closureAt b) := by
  let Sa : Set V := A.closureAtSet a
  let Sb : Set V := A.closureAtSet b
  let ha : A.IsClosed Sa := A.isClosed_closureSet {a}
  let hb : A.IsClosed Sb := A.isClosed_closureSet {b}
  have hIa : (A.induce Sa ha).IsIrreducible :=
    A.closureAt_isIrreducible a
  have hIb : (A.induce Sb hb).IsIrreducible :=
    A.closureAt_isIrreducible b
  let ea : Embedding act (A.induce Sa ha) B :=
    f.restrictClosedIrreducible act hf Sa ha hIa
  let eb : Embedding act (A.induce Sb hb) B :=
    f.restrictClosedIrreducible act hf Sb hb hIb
  have hImage : imageSet f.toFun Sa = imageSet f.toFun Sb :=
    f.image_closureAt_eq_of_same_fibre act hf hab
  have hRange : ∀ u : Sa, ∃ v : Sb, eb v = ea u := by
    intro u
    have hu : f u.1 ∈ imageSet f.toFun Sb := by
      rw [← hImage]
      exact ⟨u.1, u.2, rfl⟩
    obtain ⟨z, hz, hfz⟩ := hu
    refine ⟨⟨z, hz⟩, ?_⟩
    change f z = f u.1
    exact hfz
  exact eb.factorThrough act ea hRange

end Homomorphism
end Structure
end AllThoseEPPA
