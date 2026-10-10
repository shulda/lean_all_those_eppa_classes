import AllThoseEPPA.TreeLikeFreeCutGlueMap
import AllThoseEPPA.TreeLikeAmalgamFreeCover

/-!
# Exact relation and function data on each side of a glued free cut

The central universal property in the paper's `lem:cuts` must
show an embedding obtained by gluing exact side embeddings
preserves **all** structure, including *equality* of the sets
interpreting functions.

This file handles tuples that lie entirely within one closed
side of a genuine free decomposition. The opposite side may
have a nontrivial Γ-language component; agreement on the
overlap suffices to identify the resulting maps of vertices.

For a tuple on one side, the exact side embedding and the
closedness of that side give:
* reflection and preservation of the relation predicate;
* equality of the images of the complete function-value sets
  with the corresponding function fibre in the target.

Mixed tuples are handled later by `FreeCover` and
`FreeDecomposition.func_cross_empty`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- The glued map reflects and preserves any relation on
a tuple entirely inside the left closed side. -/
theorem glueFreeCutMap_rel_left
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition) (C : Structure L W)
    (l : Structure.Embedding act (B.induce d.left d.left_closed) C)
    (r : Structure.Embedding act (B.induce d.right d.right_closed) C)
    {n : ℕ} (R : L.RelSymbol n)
    (xs : Fin n → V) (hSide : ∀ i, xs i ∈ d.left) :
    C.rel (act.onRel l.lang R)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) ↔
      B.rel R xs := by
  let ys : Fin n → d.left := fun i => ⟨xs i, hSide i⟩
  have hTuple : l.toFun ∘ ys =
      glueFreeCutMap d l.toFun r.toFun ∘ xs := by
    funext i
    exact (glueFreeCutMap_left d l.toFun r.toFun (xs i) (hSide i)).symm
  have hRel := l.map_rel_iff R ys
  change C.rel (act.onRel l.lang R) (l.toFun ∘ ys) ↔
    B.rel R (Subtype.val ∘ ys) at hRel
  rw [hTuple] at hRel
  exact hRel

/-- The same exact relation equivalence on a tuple entirely
inside the right closed side, provided the glued maps agree
on all common vertices. -/
theorem glueFreeCutMap_rel_right
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition) (C : Structure L W)
    (l : Structure.Embedding act (B.induce d.left d.left_closed) C)
    (r : Structure.Embedding act (B.induce d.right d.right_closed) C)
    (hAgree : ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    {n : ℕ} (R : L.RelSymbol n)
    (xs : Fin n → V) (hSide : ∀ i, xs i ∈ d.right) :
    C.rel (act.onRel r.lang R)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) ↔
      B.rel R xs := by
  let ys : Fin n → d.right := fun i => ⟨xs i, hSide i⟩
  have hTuple : r.toFun ∘ ys =
      glueFreeCutMap d l.toFun r.toFun ∘ xs := by
    funext i
    exact (glueFreeCutMap_right d l.toFun r.toFun hAgree
      (xs i) (hSide i)).symm
  have hRel := r.map_rel_iff R ys
  change C.rel (act.onRel r.lang R) (r.toFun ∘ ys) ↔
    B.rel R (Subtype.val ∘ ys) at hRel
  rw [hTuple] at hRel
  exact hRel

/-- Exact equality of function-value sets on a left-side tuple.
The proof uses the side's **closedness** to ensure that every
source function value is represented by a left-side vertex.
This is stronger than a homomorphism law. -/
theorem glueFreeCutMap_func_left
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition) (C : Structure L W)
    (l : Structure.Embedding act (B.induce d.left d.left_closed) C)
    (r : Structure.Embedding act (B.induce d.right d.right_closed) C)
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → V) (hSide : ∀ i, xs i ∈ d.left) :
    Structure.imageSet (glueFreeCutMap d l.toFun r.toFun)
        (B.func F xs) =
      C.func (act.onFunc l.lang F)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) := by
  let ys : Fin n → d.left := fun i => ⟨xs i, hSide i⟩
  have hTuple : l.toFun ∘ ys =
      glueFreeCutMap d l.toFun r.toFun ∘ xs := by
    funext i
    exact (glueFreeCutMap_left d l.toFun r.toFun
      (xs i) (hSide i)).symm
  have hImage :
      Structure.imageSet (glueFreeCutMap d l.toFun r.toFun)
          (B.func F xs) =
        Structure.imageSet l.toFun
          ((B.induce d.left d.left_closed).func F ys) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haSide : a ∈ d.left :=
        d.left_closed F xs hSide ha
      refine ⟨⟨a, haSide⟩, ?_, ?_⟩
      · exact ha
      · exact (glueFreeCutMap_left d l.toFun r.toFun a haSide).symm
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.1, ?_, ?_⟩
      · exact ha
      · exact glueFreeCutMap_left d l.toFun r.toFun a.1 a.2
  calc
    Structure.imageSet (glueFreeCutMap d l.toFun r.toFun)
        (B.func F xs) =
      Structure.imageSet l.toFun
        ((B.induce d.left d.left_closed).func F ys) := hImage
    _ = C.func (act.onFunc l.lang F) (l.toFun ∘ ys) :=
      l.map_func F ys
    _ = C.func (act.onFunc l.lang F)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) := by rw [hTuple]

/-- Exact equality of function-value sets on a right-side
tuple, with arbitrary Γ relabelling on the right embedding. -/
theorem glueFreeCutMap_func_right
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition) (C : Structure L W)
    (l : Structure.Embedding act (B.induce d.left d.left_closed) C)
    (r : Structure.Embedding act (B.induce d.right d.right_closed) C)
    (hAgree : ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → V) (hSide : ∀ i, xs i ∈ d.right) :
    Structure.imageSet (glueFreeCutMap d l.toFun r.toFun)
        (B.func F xs) =
      C.func (act.onFunc r.lang F)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) := by
  let ys : Fin n → d.right := fun i => ⟨xs i, hSide i⟩
  have hTuple : r.toFun ∘ ys =
      glueFreeCutMap d l.toFun r.toFun ∘ xs := by
    funext i
    exact (glueFreeCutMap_right d l.toFun r.toFun hAgree
      (xs i) (hSide i)).symm
  have hImage :
      Structure.imageSet (glueFreeCutMap d l.toFun r.toFun)
          (B.func F xs) =
        Structure.imageSet r.toFun
          ((B.induce d.right d.right_closed).func F ys) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haSide : a ∈ d.right :=
        d.right_closed F xs hSide ha
      refine ⟨⟨a, haSide⟩, ?_, ?_⟩
      · exact ha
      · exact (glueFreeCutMap_right d l.toFun r.toFun
          hAgree a haSide).symm
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.1, ?_, ?_⟩
      · exact ha
      · exact glueFreeCutMap_right d l.toFun r.toFun
          hAgree a.1 a.2
  calc
    Structure.imageSet (glueFreeCutMap d l.toFun r.toFun)
        (B.func F xs) =
      Structure.imageSet r.toFun
        ((B.induce d.right d.right_closed).func F ys) := hImage
    _ = C.func (act.onFunc r.lang F) (r.toFun ∘ ys) :=
      r.map_func F ys
    _ = C.func (act.onFunc r.lang F)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) := by rw [hTuple]

end TreeLike
end AllThoseEPPA
