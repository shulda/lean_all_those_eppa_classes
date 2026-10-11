import AllThoseEPPA.StrongCompletionFibreBijection

/-!
# The first two layers of the five-part decomposition

Fix a Γ-homomorphism-embedding f : A → B and different vertices
l,r with f(l)=f(r). Set

  L₁ = Cl_A(l) \\ Cl_A(r),   R₁ = Cl_A(r) \\ Cl_A(l),
  L₂ = {v ∉ L₁ : L₁ ⊆ Cl_A(v)},
  R₂ = {v ∉ R₁ : R₁ ⊆ Cl_A(v)}.

These are exactly the four named parts of the decomposition
in manuscript Proposition 11.3. We prove without any
minimal-kernel assumption that L₁,R₁ are nonempty,
that their fibres match bijectively, and that L₂ and R₂
are disjoint. Only the remaining global partition,
closedness and relation-locality require the harder
minimality and unary-function arguments.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {V : Type w}

/-- Exclusive part of the closure of l. -/
def leftExclusive (A : Structure L V) (l r : V) : Set V :=
  A.closureAtSet l \ A.closureAtSet r

/-- Exclusive part of the closure of r. -/
def rightExclusive (A : Structure L V) (l r : V) : Set V :=
  A.closureAtSet r \ A.closureAtSet l

/-- Vertices outside L₁ whose closure contains all of L₁. -/
def leftAbove (A : Structure L V) (l r : V) : Set V :=
  {v | v ∉ A.leftExclusive l r ∧
    A.leftExclusive l r ⊆ A.closureAtSet v}

/-- Vertices outside R₁ whose closure contains all of R₁. -/
def rightAbove (A : Structure L V) (l r : V) : Set V :=
  {v | v ∉ A.rightExclusive l r ∧
    A.rightExclusive l r ⊆ A.closureAtSet v}

namespace Homomorphism

variable {Γ : Type v} [Group Γ] {W : Type x}

/-- The chosen left generator belongs to the exclusive L₁-part:
it cannot also lie in the right closure, since f is injective
on each individual irreducible closure. -/
theorem left_mem_leftExclusive_of_collision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r) :
    l ∈ A.leftExclusive l r := by
  constructor
  · exact A.mem_closureAtSet l
  · exact f.same_fibre_not_mem_closureAt
      act hf hne.symm hlr.symm

/-- The right generator similarly lies in R₁. -/
theorem right_mem_rightExclusive_of_collision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r) :
    r ∈ A.rightExclusive l r := by
  constructor
  · exact A.mem_closureAtSet r
  · exact f.same_fibre_not_mem_closureAt
      act hf hne hlr

/-- Every vertex of the exclusive left part has exactly one
image-mate in the exclusive right part. -/
theorem existsUnique_rightExclusive_fibreMate
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hlr : f l = f r)
    (x : V) (hx : x ∈ A.leftExclusive l r) :
    ∃! y : V, y ∈ A.rightExclusive l r ∧ f y = f x := by
  obtain ⟨yb, hyb, _⟩ :=
    f.existsUnique_fibreMate_in_closureAt act hf hlr
      ⟨x, hx.1⟩
  refine ⟨yb.1, ?_, ?_⟩
  · constructor
    · refine ⟨yb.2, ?_⟩
      intro hyLeft
      have hxy : x = yb.1 :=
        (f.injOn_closureAt act hf l) hx.1 hyLeft hyb.symm
      exact hx.2 (by simpa only [hxy] using yb.2)
    · exact hyb
  · intro y hy
    exact (f.injOn_closureAt act hf r) hy.1.1 yb.2
      (hy.2.trans hyb.symm)

/-- The two exclusive parts have the same image, but their
sets of vertices are disjoint. In particular, they are two
distinct preimages of the same irreducible substructure. -/
theorem image_leftExclusive_eq_rightExclusive
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hlr : f l = f r) :
    imageSet f.toFun (A.leftExclusive l r) =
      imageSet f.toFun (A.rightExclusive l r) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, _⟩ :=
      f.existsUnique_rightExclusive_fibreMate act hf hlr x hx
    exact ⟨y, hy.1, hy.2⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, _⟩ :=
      f.existsUnique_rightExclusive_fibreMate act hf
        hlr.symm y hy
    exact ⟨x, hx.1, hx.2⟩

/-- The sets L₂ and R₂ cannot intersect, since any vertex
whose one-point closure contained BOTH L₁ and R₁ would
contain l and r, contradicting local injectivity of f. -/
theorem leftAbove_disjoint_rightAbove
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r) :
    Disjoint (A.leftAbove l r) (A.rightAbove l r) := by
  apply Set.disjoint_left.mpr
  intro z hzL hzR
  have hl : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hr : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  have hlz : l ∈ A.closureAtSet z := hzL.2 hl
  have hrz : r ∈ A.closureAtSet z := hzR.2 hr
  exact (f.distinct_of_same_fibre_not_in_common_closure
    act hf hne hlr z) ⟨hlz, hrz⟩

end Homomorphism
end Structure
end AllThoseEPPA
