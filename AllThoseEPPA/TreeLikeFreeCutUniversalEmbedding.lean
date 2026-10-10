import AllThoseEPPA.TreeLikeFreeCutSideData

/-!
# Universal exact Γ-embedding from a free cut into a free cover

This is a genuine structure-level universal-property theorem.
Let B be split by a proper free decomposition and C admit a
(possibly degenerate) free cover. Suppose its two closed induced
sides embed *exactly* into C with:

* equal Γ-language component and agreement on the common base;
* injectivity across the images of the two sides;
* reflection of membership in the two sides of the target's
  free cover to membership in B's corresponding closed sides.

Then the map glued from the two source embeddings is itself an
**exact Γ-structure embedding of the entire B**.

The relation proof uses locality both in the original B and
the target free cover. Function-value equality on side-supported
tuples uses the lemmas in `TreeLikeFreeCutSideData`. Mixed
input tuples have *empty function fibres on both sides* by
their respective free-(cover/decomposition) axioms.

No restriction on function arity, language action, or target
carrier size is used. This theorem is immediately reusable
for the concrete Γ-amalgam once the two reflection conditions
are derived from its exact overlap geometry.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Universal exact Γ-embedding from a genuine free decomposition
into a target covered freely by the images of the two source
structures. Source-side agreement, cross-injectivity and exact
support reflection are the only additional hypotheses. -/
noncomputable def glueFreeCutEmbedding
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition)
    (C : Structure L W) (c : C.FreeCover)
    (l : Structure.Embedding act (B.induce d.left d.left_closed) C)
    (r : Structure.Embedding act (B.induce d.right d.right_closed) C)
    (hLang : l.lang = r.lang)
    (hAgree : ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (hCross : ∀ (x : d.left) (y : d.right),
      l x = r y → x.1 = y.1)
    (hSupportLeft : ∀ x : V,
      glueFreeCutMap d l.toFun r.toFun x ∈ c.left ↔ x ∈ d.left)
    (hSupportRight : ∀ x : V,
      glueFreeCutMap d l.toFun r.toFun x ∈ c.right ↔ x ∈ d.right) :
    Structure.Embedding act B C where
  lang := l.lang
  toFun := glueFreeCutMap d l.toFun r.toFun
  injective := glueFreeCutMap_injective d l.toFun r.toFun
    l.injective r.injective hCross
  map_rel_iff := by
    intro n R xs
    constructor
    · intro hRel
      have hSide := c.rel_local (act.onRel l.lang R)
        (glueFreeCutMap d l.toFun r.toFun ∘ xs) hRel
      rcases hSide with hL | hR
      · have hs : ∀ i, xs i ∈ d.left := fun i =>
          (hSupportLeft (xs i)).mp (hL i)
        exact (glueFreeCutMap_rel_left act B d C l r R xs hs).mp hRel
      · have hs : ∀ i, xs i ∈ d.right := fun i =>
          (hSupportRight (xs i)).mp (hR i)
        have hRelR : C.rel (act.onRel r.lang R)
            (glueFreeCutMap d l.toFun r.toFun ∘ xs) := by
          rw [← hLang]
          exact hRel
        exact (glueFreeCutMap_rel_right act B d C l r hAgree R xs hs).mp hRelR
    · intro hRel
      rcases d.rel_local R xs hRel with hL | hR
      · exact (glueFreeCutMap_rel_left act B d C l r R xs hL).mpr hRel
      · have hRelR := (glueFreeCutMap_rel_right act B d C l r
          hAgree R xs hR).mpr hRel
        rw [← hLang] at hRelR
        exact hRelR
  map_func := by
    intro n F xs
    by_cases hL : ∀ i, xs i ∈ d.left
    · exact glueFreeCutMap_func_left act B d C l r F xs hL
    · by_cases hR : ∀ i, xs i ∈ d.right
      · have hFunc := glueFreeCutMap_func_right act B d C l r
          hAgree F xs hR
        rw [← hLang] at hFunc
        exact hFunc
      · have hCrossSource :
            ¬ ((∀ i, xs i ∈ d.left) ∨
              (∀ i, xs i ∈ d.right)) := by
          intro h
          rcases h with hl | hr
          · exact hL hl
          · exact hR hr
        have hEmptySource : B.func F xs = ∅ :=
          d.func_cross_empty F xs hCrossSource
        have hCrossTarget :
            ¬ ((∀ i, (glueFreeCutMap d l.toFun r.toFun ∘ xs) i ∈ c.left) ∨
              (∀ i, (glueFreeCutMap d l.toFun r.toFun ∘ xs) i ∈ c.right)) := by
          intro h
          rcases h with hl | hr
          · apply hL
            intro i
            exact (hSupportLeft (xs i)).mp (hl i)
          · apply hR
            intro i
            exact (hSupportRight (xs i)).mp (hr i)
        have hEmptyTarget :
            C.func (act.onFunc l.lang F)
              (glueFreeCutMap d l.toFun r.toFun ∘ xs) = ∅ :=
          c.func_cross_empty (act.onFunc l.lang F)
            (glueFreeCutMap d l.toFun r.toFun ∘ xs) hCrossTarget
        rw [hEmptySource, hEmptyTarget]
        ext z
        constructor
        · rintro ⟨a, ha, _⟩
          exact ha.elim
        · intro hz
          exact hz.elim

end TreeLike
end AllThoseEPPA
