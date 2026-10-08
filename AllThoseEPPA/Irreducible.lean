import AllThoseEPPA.EPPA

/-!
# Irreducible structures and homomorphism-embeddings

This file introduces the local notions used from Proposition
`prop:faithful` onwards: free decompositions, irreducible structures,
homomorphism-embeddings and irreducible-structure faithful witnesses.
-/

namespace AllThoseEPPA

universe u v w z

namespace Structure

variable {L : Language.{u}}
variable {V : Type v} {W : Type w}

/-- A presentation of a structure as a free amalgam of two proper induced
substructures.

The closed sets `S` and `T` are the two sides.  Their intersection is the
amalgamation base.  Every relation tuple is contained in one side, and a
function tuple meeting both exclusive sides has empty value.  This is exactly
the paper's definition of a free strong amalgamation, specialized to
substructures of one ambient structure. -/
structure FreeDecomposition (A : Structure L V) where
  left : Set V
  right : Set V
  left_closed : A.IsClosed left
  right_closed : A.IsClosed right
  cover : left ∪ right = Set.univ
  left_proper : left ≠ Set.univ
  right_proper : right ≠ Set.univ
  rel_local :
    ∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V),
      A.rel R xs →
        (∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)
  func_cross_empty :
    ∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → V),
      ¬ ((∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)) →
        A.func F xs = ∅

/-- A structure is irreducible when it is not a free amalgam of proper
substructures. -/
def IsIrreducible (A : Structure L V) : Prop :=
  IsEmpty (FreeDecomposition A)

/-- The image in the ambient carrier of a closed subset of an induced
substructure is closed. -/
theorem isClosed_image_subtype
    (A : Structure L V) (S : Set V) (hS : A.IsClosed S)
    (T : Set S) (hT : (A.induce S hS).IsClosed T) :
    A.IsClosed (Subtype.val '' T) := by
  classical
  intro n F xs hxs y hy
  let zs : Fin n → S := fun i =>
    Classical.choose (hxs i)
  have hzs_mem : ∀ i, zs i ∈ T := by
    intro i
    exact (Classical.choose_spec (hxs i)).1
  have hzs_val : ∀ i, (zs i).1 = xs i := by
    intro i
    exact (Classical.choose_spec (hxs i)).2
  have hxsS : ∀ i, xs i ∈ S := by
    intro i
    rw [← hzs_val i]
    exact (zs i).2
  have hyS : y ∈ S :=
    hS F xs hxsS hy
  let zy : S := ⟨y, hyS⟩
  have hzy_func :
      zy ∈ (A.induce S hS).func F zs := by
    change y ∈ A.func F (Subtype.val ∘ zs)
    have htuple : (Subtype.val ∘ zs) = xs := by
      funext i
      exact hzs_val i
    rw [htuple]
    exact hy
  have hzyT : zy ∈ T :=
    hT F zs hzs_mem hzy_func
  exact ⟨zy, hzyT, rfl⟩

/-- Inside the induced structure on the closure of `x`, the vertex `x`
generates the whole carrier. -/
theorem closureAtSet_in_closureAt_eq_univ
    (A : Structure L V) (x : V) :
    (A.closureAt x).closureAtSet
        ⟨x, A.mem_closureAtSet x⟩ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  change
    z ∈ (A.closureAt x).closureSet
      {⟨x, A.mem_closureAtSet x⟩}
  intro T hT hxT
  have himageClosed :
      A.IsClosed (Subtype.val '' T) :=
    isClosed_image_subtype A (A.closureAtSet x)
      (A.isClosed_closureSet {x}) T hT
  have hxImage : x ∈ Subtype.val '' T := by
    refine ⟨⟨x, A.mem_closureAtSet x⟩, ?_, rfl⟩
    exact hxT (by simp)
  have hzImage :
      z.1 ∈ Subtype.val '' T :=
    A.closureSet_minimal himageClosed
      (by
        intro y hy
        have hyx : y = x := by simpa using hy
        subst y
        exact hxImage)
      z.2
  rcases hzImage with ⟨t, ht, htz⟩
  have htz' : t = z := by
    apply Subtype.ext
    exact htz
  simpa [htz'] using ht

/-- Every one-point closure is irreducible.  This is used repeatedly in the
faithfulness and restricted-witness sections of the paper. -/
theorem closureAt_isIrreducible
    (A : Structure L V) (x : V) :
    (A.closureAt x).IsIrreducible := by
  constructor
  intro d
  let x0 : A.closureAtSet x :=
    ⟨x, A.mem_closureAtSet x⟩
  have hxcover : x0 ∈ d.left ∪ d.right := by
    rw [d.cover]
    exact Set.mem_univ x0
  rcases hxcover with hxL | hxR
  · apply d.left_proper
    apply Set.eq_univ_of_forall
    intro z
    have hcl :
        z ∈ (A.closureAt x).closureAtSet x0 := by
      rw [closureAtSet_in_closureAt_eq_univ]
      exact Set.mem_univ z
    exact
      (A.closureAt x).closureSet_minimal d.left_closed
        (by
          intro y hy
          have hyx : y = x0 := by simpa using hy
          subst y
          exact hxL)
        hcl
  · apply d.right_proper
    apply Set.eq_univ_of_forall
    intro z
    have hcl :
        z ∈ (A.closureAt x).closureAtSet x0 := by
      rw [closureAtSet_in_closureAt_eq_univ]
      exact Set.mem_univ z
    exact
      (A.closureAt x).closureSet_minimal d.right_closed
        (by
          intro y hy
          have hyx : y = x0 := by simpa using hy
          subst y
          exact hxR)
        hcl


/-- An irreducible induced substructure of a free amalgam is contained in one
of the two sides.  This is the basic structural fact used later for tree
amalgamations. -/
theorem irreducible_subset_one_side
    (A : Structure L V)
    (d : A.FreeDecomposition)
    (S : Set V) (hS : A.IsClosed S)
    (hirr : (A.induce S hS).IsIrreducible) :
    S ⊆ d.left ∨ S ⊆ d.right := by
  by_contra hcontain
  have hnleft : ¬ S ⊆ d.left := by
    intro hleft
    exact hcontain (Or.inl hleft)
  have hnright : ¬ S ⊆ d.right := by
    intro hright
    exact hcontain (Or.inr hright)
  let leftS : Set S :=
    {x | x.1 ∈ d.left}
  let rightS : Set S :=
    {x | x.1 ∈ d.right}
  have hleftClosed :
      (A.induce S hS).IsClosed leftS := by
    intro n F xs hxs y hy
    change y.1 ∈ d.left
    apply d.left_closed F (Subtype.val ∘ xs)
    · intro i
      exact hxs i
    · exact hy
  have hrightClosed :
      (A.induce S hS).IsClosed rightS := by
    intro n F xs hxs y hy
    change y.1 ∈ d.right
    apply d.right_closed F (Subtype.val ∘ xs)
    · intro i
      exact hxs i
    · exact hy
  have hcover : leftS ∪ rightS = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.1 ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ x.1
    simpa [leftS, rightS] using hx
  have hleftProper : leftS ≠ Set.univ := by
    rcases Set.not_subset.mp hnleft with ⟨x, hxS, hxL⟩
    intro hall
    have hx : (⟨x, hxS⟩ : S) ∈ leftS := by
      rw [hall]
      exact Set.mem_univ _
    exact hxL hx
  have hrightProper : rightS ≠ Set.univ := by
    rcases Set.not_subset.mp hnright with ⟨x, hxS, hxR⟩
    intro hall
    have hx : (⟨x, hxS⟩ : S) ∈ rightS := by
      rw [hall]
      exact Set.mem_univ _
    exact hxR hx
  let dec : (A.induce S hS).FreeDecomposition :=
    { left := leftS
      right := rightS
      left_closed := hleftClosed
      right_closed := hrightClosed
      cover := hcover
      left_proper := hleftProper
      right_proper := hrightProper
      rel_local := by
        intro n R xs hrel
        have h :=
          d.rel_local R (Subtype.val ∘ xs) hrel
        rcases h with hl | hr
        · left
          intro i
          exact hl i
        · right
          intro i
          exact hr i
      func_cross_empty := by
        intro n F xs hcross
        have hamb :
            A.func F (Subtype.val ∘ xs) = ∅ := by
          apply d.func_cross_empty F (Subtype.val ∘ xs)
          intro hside
          apply hcross
          rcases hside with hl | hr
          · left
            intro i
            exact hl i
          · right
            intro i
            exact hr i
        ext y
        change
          (y.1 ∈ A.func F (Subtype.val ∘ xs)) ↔
            y ∈ (∅ : Set S)
        rw [hamb]
        simp }
  exact hirr.false dec


section Maps

variable {Γ : Type z} [Group Γ]
variable (act : L.Action Γ)
variable {A : Structure L V} {B : Structure L W}

namespace Homomorphism

/-- A homomorphism is an embedding on a subset if it is injective there and
reflects all relation and function data on tuples from that subset. -/
def IsEmbeddingOn
    (f : Homomorphism act A B) (S : Set V) : Prop :=
  Set.InjOn f S ∧
  (∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V),
    (∀ i, xs i ∈ S) →
      (B.rel (act.onRel f.lang R) (f.toFun ∘ xs) ↔ A.rel R xs)) ∧
  (∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → V),
    (∀ i, xs i ∈ S) →
      imageSet f.toFun (A.func F xs) =
        B.func (act.onFunc f.lang F) (f.toFun ∘ xs))

/-- A homomorphism-embedding is a homomorphism whose restriction to every
irreducible substructure of the domain is an embedding. -/
def IsHomomorphismEmbedding
    (f : Homomorphism act A B) : Prop :=
  ∀ (S : Set V) (hS : A.IsClosed S),
    (A.induce S hS).IsIrreducible →
      IsEmbeddingOn act f S

/-- An embedding, regarded as a homomorphism, is a homomorphism-embedding. -/
theorem Embedding.toHomomorphism_isHomomorphismEmbedding
    (f : Embedding act A B) :
    IsHomomorphismEmbedding act f.toHomomorphism := by
  intro S hS hirr
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact f.injective hxy
  · intro n R xs hxs
    exact f.map_rel_iff R xs
  · intro n F xs hxs
    exact f.map_func F xs

end Homomorphism

/-- Irreducible-structure faithfulness of a witness with respect to an
explicit embedded copy `ψ(A)`. -/
def IsIrreducibleStructureFaithful
    (ψ : Embedding act A B) : Prop :=
  ∀ (S : Set W) (hS : B.IsClosed S),
    (B.induce S hS).IsIrreducible →
      ∃ g : Automorphism act B,
        ∀ x, x ∈ S → ∃ a : V, g x = ψ a

end Maps

end Structure
end AllThoseEPPA
