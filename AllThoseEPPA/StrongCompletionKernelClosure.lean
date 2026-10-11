import AllThoseEPPA.TreeLikeHomEmbClosedIrreducibleImage

/-!
# Fibres of homomorphism-embeddings on one-point closures

The key local ingredient of manuscript Proposition 11.3 is that an
identification f(x)=f(y) can only occur *between distinct irreducible
one-point closures*. On each closure f is an exact embedding.
Moreover, the images of Cl_A(x) and Cl_A(y) are both precisely
Cl_B(f(x)).

We prove these assertions with arbitrary set-valued function arities
and nontrivial Γ-language permutations. Unary functions are needed
later in Proposition 11.3 to construct a CLOSED five-part partition,
not for the elementary kernel facts here.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Preimages of closed sets are closed for arbitrary Γ-homomorphisms.
Only forward preservation of function values is required. -/
theorem preimage_isClosed
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (T : Set W)
    (hT : B.IsClosed T) :
    A.IsClosed (f.toFun ⁻¹' T) := by
  intro n F xs hxs y hy
  apply hT (act.onFunc f.lang F) (f.toFun ∘ xs)
  · intro i
    exact hxs i
  · exact f.map_func F xs ⟨y, hy, rfl⟩

/-- The image of a generated closure under any Γ-homomorphism
is contained in the closure of the image of its generators. -/
theorem image_closureSet_subset_closureSet
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (S : Set V) :
    imageSet f.toFun (A.closureSet S) ⊆
      B.closureSet (imageSet f.toFun S) := by
  let T : Set W := B.closureSet (imageSet f.toFun S)
  have hT : B.IsClosed T := B.isClosed_closureSet (imageSet f.toFun S)
  have hPre : A.IsClosed (f.toFun ⁻¹' T) :=
    f.preimage_isClosed act T hT
  have hGenerators : S ⊆ f.toFun ⁻¹' T := by
    intro a ha
    exact B.subset_closureSet (imageSet f.toFun S) ⟨a, ha, rfl⟩
  have hClosure : A.closureSet S ⊆ f.toFun ⁻¹' T :=
    A.closureSet_minimal hPre hGenerators
  rintro y ⟨a, ha, rfl⟩
  exact hClosure ha

/-- On the closure of a single generator, a homomorphism-
embedding induces an exact structure embedding, hence the
image is a closed subset of the codomain. -/
theorem image_closureAt_isClosed
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (a : V) :
    B.IsClosed (imageSet f.toFun (A.closureAtSet a)) := by
  let S : Set V := A.closureAtSet a
  let hS : A.IsClosed S := A.isClosed_closureSet {a}
  have hIrr : (A.induce S hS).IsIrreducible :=
    A.closureAt_isIrreducible a
  intro n F xs hxs y hy
  exact (f.image_isClosed_of_embeddingOn act S hS (hf S hS hIrr))
    F xs hxs hy

/-- The image of a one-point closure is EXACTLY the one-point
closure of the image. This relies crucially on local exactness
of the homomorphism-embedding, not just preservation. -/
theorem image_closureAt_eq_closureAt
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (a : V) :
    imageSet f.toFun (A.closureAtSet a) =
      B.closureAtSet (f a) := by
  apply Set.Subset.antisymm
  · have hImage := f.image_closureSet_subset_closureSet act {a}
    simpa only [Structure.closureAtSet, imageSet, Set.image_singleton] using hImage
  · apply B.closureSet_minimal (f.image_closureAt_isClosed act hf a)
    intro y hy
    have hya : y = f a := by simpa using hy
    subst y
    exact ⟨a, A.mem_closureAtSet a, rfl⟩

/-- Two points in one fibre have identical IMAGES of their
one-point closures, even though the closures in A need not
be equal or intersect. -/
theorem image_closureAt_eq_of_same_fibre
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V}
    (hab : f a = f b) :
    imageSet f.toFun (A.closureAtSet a) =
      imageSet f.toFun (A.closureAtSet b) := by
  calc
    imageSet f.toFun (A.closureAtSet a) =
        B.closureAtSet (f a) := f.image_closureAt_eq_closureAt act hf a
    _ = B.closureAtSet (f b) := by rw [hab]
    _ = imageSet f.toFun (A.closureAtSet b) :=
      (f.image_closureAt_eq_closureAt act hf b).symm

/-- A Γ-homomorphism-embedding is injective on every
one-point closure, since such a closed substructure is
irreducible. -/
theorem injOn_closureAt
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (a : V) :
    Set.InjOn f.toFun (A.closureAtSet a) := by
  let S : Set V := A.closureAtSet a
  let hS : A.IsClosed S := A.isClosed_closureSet {a}
  have hIrr : (A.induce S hS).IsIrreducible :=
    A.closureAt_isIrreducible a
  exact (hf S hS hIrr).1

/-- Distinct vertices identified by a homomorphism-embedding
cannot lie together in any single one-point closure. -/
theorem distinct_of_same_fibre_not_in_common_closure
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hne : a ≠ b) (hab : f a = f b)
    (z : V) :
    ¬ (a ∈ A.closureAtSet z ∧ b ∈ A.closureAtSet z) := by
  rintro ⟨ha, hb⟩
  exact hne (f.injOn_closureAt act hf z ha hb hab)

/-- In particular, two different vertices identified by f
cannot lie in one another's one-point closures. -/
theorem same_fibre_not_mem_closureAt
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hne : a ≠ b) (hab : f a = f b) :
    b ∉ A.closureAtSet a := by
  intro hb
  exact f.distinct_of_same_fibre_not_in_common_closure
    act hf hne hab a ⟨A.mem_closureAtSet a, hb⟩

end Homomorphism
end Structure
end AllThoseEPPA
