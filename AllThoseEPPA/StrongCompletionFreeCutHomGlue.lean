import AllThoseEPPA.StrongCompletionFreeCutLocalExactness
import AllThoseEPPA.TreeLikeFreeCutGlueMap

/-!
# Gluing genuine homomorphism-embeddings along a free decomposition

Suppose A is a genuine free union of closed left and right
sides, and l,r:A→B are Γ-homomorphisms agreeing on the common
intersection and having the SAME language component.

The two maps glue pointwise into a Γ-homomorphism k:A→B.
A realized relation tuple is contained in one source side,
and a function fibre on a mixed-side tuple is empty. Thus
all relation and set-valued function preservation transfers
from the corresponding source map to k.

If l and r are homomorphism-embeddings, then k also is one:
each irreducible closed source piece lives on one side, where
the glued map agrees with the corresponding locally exact map.
In particular this is a full Γ-homomorphism-embedding result,
not merely an injective map between glued carriers.

No unary-function or finiteness assumptions are needed.
The application to Proposition 11.3 will take
l = jL ∘ f and r = jR ∘ f for two exact embeddings
of the target K-completion B into a strong K-amalgam.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Two compatible Γ-homomorphisms of the WHOLE source A
glue to a genuine Γ-homomorphism along a free cut. The
first source side is selected whenever both are available;
the agreement hypothesis guarantees the right-side law. -/
noncomputable def glueFreeCutHomomorphism
    (act : L.Action Γ)
    (A : Structure L V) (d : A.FreeDecomposition)
    {B : Structure L W}
    (l r : Structure.Homomorphism act A B)
    (hLang : l.lang = r.lang)
    (hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l x = r x) :
    Structure.Homomorphism act A B where
  lang := l.lang
  toFun := glueFreeCutMap d
    (fun x : d.left => l x.1)
    (fun x : d.right => r x.1)
  map_rel := by
    intro n R xs hRel
    rcases d.rel_local R xs hRel with hsL | hsR
    · have ht : (glueFreeCutMap d
          (fun x : d.left => l x.1)
          (fun x : d.right => r x.1)) ∘ xs =
            l.toFun ∘ xs := by
        funext i
        exact glueFreeCutMap_left d
          (fun x : d.left => l x.1)
          (fun x : d.right => r x.1) (xs i) (hsL i)
      simpa only [ht] using l.map_rel R xs hRel
    · have hAGree : ∀ (x : V)
          (hxL : x ∈ d.left) (hxR : x ∈ d.right),
            (fun t : d.left => l t.1) ⟨x, hxL⟩ =
              (fun t : d.right => r t.1) ⟨x, hxR⟩ :=
        hAgree
      have ht : (glueFreeCutMap d
          (fun x : d.left => l x.1)
          (fun x : d.right => r x.1)) ∘ xs =
            r.toFun ∘ xs := by
        funext i
        exact glueFreeCutMap_right d
          (fun x : d.left => l x.1)
          (fun x : d.right => r x.1)
          hAGree (xs i) (hsR i)
      simpa only [hLang, ht] using r.map_rel R xs hRel
  map_func := by
    intro n F xs z hz
    obtain ⟨a, ha, hka⟩ := hz
    by_cases hsL : ∀ i, xs i ∈ d.left
    · have haL : a ∈ d.left := d.left_closed F xs hsL ha
      have hkaL : l a = z := by
        calc
          l a = glueFreeCutMap d
              (fun x : d.left => l x.1)
              (fun x : d.right => r x.1) a := by
                symm
                exact glueFreeCutMap_left d
                  (fun x : d.left => l x.1)
                  (fun x : d.right => r x.1) a haL
          _ = z := hka
      have ht : (glueFreeCutMap d
          (fun x : d.left => l x.1)
          (fun x : d.right => r x.1)) ∘ xs =
            l.toFun ∘ xs := by
        funext i
        exact glueFreeCutMap_left d
          (fun x : d.left => l x.1)
          (fun x : d.right => r x.1) (xs i) (hsL i)
      have hVal : l a ∈ B.func
          (act.onFunc l.lang F) (l.toFun ∘ xs) :=
        l.map_func F xs ⟨a, ha, rfl⟩
      rw [← hkaL]
      simpa only [ht] using hVal
    · by_cases hsR : ∀ i, xs i ∈ d.right
      · have haR : a ∈ d.right := d.right_closed F xs hsR ha
        have hAGree : ∀ (x : V)
            (hxL : x ∈ d.left) (hxR : x ∈ d.right),
              (fun t : d.left => l t.1) ⟨x, hxL⟩ =
                (fun t : d.right => r t.1) ⟨x, hxR⟩ :=
          hAgree
        have hkaR : r a = z := by
          calc
            r a = glueFreeCutMap d
                (fun x : d.left => l x.1)
                (fun x : d.right => r x.1) a := by
                  symm
                  exact glueFreeCutMap_right d
                    (fun x : d.left => l x.1)
                    (fun x : d.right => r x.1)
                    hAGree a haR
            _ = z := hka
        have ht : (glueFreeCutMap d
            (fun x : d.left => l x.1)
            (fun x : d.right => r x.1)) ∘ xs =
              r.toFun ∘ xs := by
          funext i
          exact glueFreeCutMap_right d
            (fun x : d.left => l x.1)
            (fun x : d.right => r x.1)
            hAGree (xs i) (hsR i)
        have hVal : r a ∈ B.func
            (act.onFunc r.lang F) (r.toFun ∘ xs) :=
          r.map_func F xs ⟨a, ha, rfl⟩
        rw [← hkaR]
        simpa only [hLang, ht] using hVal
      · have hCross : ¬ ((∀ i, xs i ∈ d.left) ∨
            (∀ i, xs i ∈ d.right)) := by
          intro h
          rcases h with hl | hr
          · exact hsL hl
          · exact hsR hr
        have hEmpty : A.func F xs = ∅ :=
          d.func_cross_empty F xs hCross
        rw [hEmpty] at ha
        exact ha.elim

/-- The glue is literally the left-side map, pointwise. -/
theorem glueFreeCutHomomorphism_left
    (act : L.Action Γ)
    (A : Structure L V) (d : A.FreeDecomposition)
    {B : Structure L W}
    (l r : Structure.Homomorphism act A B)
    (hLang : l.lang = r.lang)
    (hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l x = r x)
    (x : V) (hx : x ∈ d.left) :
    glueFreeCutHomomorphism act A d l r hLang hAgree x = l x := by
  exact glueFreeCutMap_left d
    (fun t : d.left => l t.1)
    (fun t : d.right => r t.1) x hx

/-- The glue is literally the right-side map, pointwise. -/
theorem glueFreeCutHomomorphism_right
    (act : L.Action Γ)
    (A : Structure L V) (d : A.FreeDecomposition)
    {B : Structure L W}
    (l r : Structure.Homomorphism act A B)
    (hLang : l.lang = r.lang)
    (hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l x = r x)
    (x : V) (hx : x ∈ d.right) :
    glueFreeCutHomomorphism act A d l r hLang hAgree x = r x := by
  exact glueFreeCutMap_right d
    (fun t : d.left => l t.1)
    (fun t : d.right => r t.1)
    hAgree x hx

/-- A global Γ-homomorphism glued from locally exact side
maps is again a Γ-homomorphism-embedding. -/
theorem glueFreeCutHomomorphism_isHomomorphismEmbedding
    (act : L.Action Γ)
    (A : Structure L V) (d : A.FreeDecomposition)
    {B : Structure L W}
    (l r : Structure.Homomorphism act A B)
    (hLang : l.lang = r.lang)
    (hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l x = r x)
    (hl : Structure.Homomorphism.IsHomomorphismEmbedding act l)
    (hr : Structure.Homomorphism.IsHomomorphismEmbedding act r) :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (glueFreeCutHomomorphism act A d l r hLang hAgree) := by
  exact Structure.Homomorphism.homomorphismEmbedding_of_freeCut_side_agreement
    act d (glueFreeCutHomomorphism act A d l r hLang hAgree)
      l r hl hr rfl hLang
      (fun x hx => glueFreeCutHomomorphism_left
        act A d l r hLang hAgree x hx)
      (fun x hx => glueFreeCutHomomorphism_right
        act A d l r hLang hAgree x hx)

end TreeLike
end AllThoseEPPA
