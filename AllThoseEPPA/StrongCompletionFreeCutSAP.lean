import AllThoseEPPA.StrongCompletionFreeCutHomGlue
import AllThoseEPPA.StrongCompletionClosedImageUnary
import AllThoseEPPA.StrongCompletionHereditaryStrongAmalgamation
import AllThoseEPPA.StrongCompletionClassAPI
import AllThoseEPPA.TreeLikeFreeCutBaseEmbeddings

/-!
# Strong amalgamation separates cross-side kernel collisions

Let K be a hereditary finite class with strong amalgamation
in a genuinely set-valued unary-function language. Suppose
A has a free decomposition A = L ∪ R and a K-completion
f:A→B which is a Γ-homomorphism-embedding and injective
on EACH of the two closed sides L and R.

Then A has a STRONG K-completion, even though f may still
identify vertices on opposite sides.

Construction:
* The actual image T=f(L∩R) is function-closed inside B,
  by the unary closed-image lemma for homomorphism-embeddings.
* Heredity puts the induced B-structure on T into K.
* Strongly amalgamate two independent copies B₁,B₂ of B
  over the exact induced structure B|T.
* Map A into the amalgam using the first copy of B on L,
  and the second copy on R. These maps agree on L∩R.
* The free-decomposition gluing theorem yields a genuine
  Γ-homomorphism-embedding of A.
* Strong amalgamation's exact-overlap condition plus the
  sidewise injectivity of f make the glued map globally
  injective.

This closes the LAST geometrical step in the published
Proposition 11.3 argument once the minimal-kernel
factorization shows both sides are f-injective. The
assumption of sidewise injectivity remains explicit here.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {V W : Type v}

/-- Free decomposition plus sidewise injectivity of a
homomorphism-embedding K-completion implies existence of a
strong K-completion. The completion f need not be globally
injective or globally reflect relations. -/
theorem strongCompletion_of_freeCut_sidewise_injective
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    (A : Structure L V) (d : A.FreeDecomposition)
    (B : Structure L W)
    (f : Structure.Homomorphism act A B)
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding act f)
    (hB : K.mem B)
    (hInjLeft : Set.InjOn f.toFun d.left)
    (hInjRight : Set.InjOn f.toFun d.right) :
    K.toAmalgamationClass.HasStrongCompletion A := by
  classical
  let C : Set V := d.left ∩ d.right
  have hC : A.IsClosed C := freeCut_base_isClosed A d
  let T : Set W := Structure.imageSet f.toFun C
  have hT : B.IsClosed T :=
    f.image_closedSet_isClosed_of_unary act hf C hC
  let D : Structure L T := B.induce T hT
  let e : Structure.Embedding act D B :=
    Structure.inclusion act B T hT
  have hKD : K.mem D := K.hereditary e hB
  obtain ⟨Z, hZ, H, hKH, jL, jR, hComm, hOverlap⟩ :=
    K.strong_amalgamate e e hKD hB hB
  letI : Finite Z := hZ
  have hjLang : jL.lang = jR.lang := by
    have h := congrArg
      (fun p : Structure.Embedding act D H => p.lang) hComm
    change jL.lang * (1 : Γ) = jR.lang * (1 : Γ) at h
    simpa using h
  let l : Structure.Homomorphism act A H :=
    jL.toHomomorphism.comp f
  let r : Structure.Homomorphism act A H :=
    jR.toHomomorphism.comp f
  have hLang : l.lang = r.lang := by
    change jL.lang * f.lang = jR.lang * f.lang
    rw [hjLang]
  have hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l x = r x := by
    intro x hxL hxR
    let t : T := ⟨f x, ⟨x, ⟨hxL, hxR⟩, rfl⟩⟩
    have heq := congrArg
      (fun p : Structure.Embedding act D H => p t) hComm
    exact heq
  let k : Structure.Homomorphism act A H :=
    glueFreeCutHomomorphism act A d l r hLang hAgree
  have hl : Structure.Homomorphism.IsHomomorphismEmbedding act l :=
    Structure.Homomorphism.comp_isHomomorphismEmbedding
      act jL.toHomomorphism f
      (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
        act jL) hf
  have hr : Structure.Homomorphism.IsHomomorphismEmbedding act r :=
    Structure.Homomorphism.comp_isHomomorphismEmbedding
      act jR.toHomomorphism f
      (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
        act jR) hf
  have hk : Structure.Homomorphism.IsHomomorphismEmbedding act k :=
    glueFreeCutHomomorphism_isHomomorphismEmbedding
      act A d l r hLang hAgree hl hr
  have hInjL : Function.Injective
      (fun x : d.left => l x.1) := by
    intro x y hxy
    apply Subtype.ext
    apply hInjLeft x.2 y.2
    exact jL.injective hxy
  have hInjR : Function.Injective
      (fun x : d.right => r x.1) := by
    intro x y hxy
    apply Subtype.ext
    apply hInjRight x.2 y.2
    exact jR.injective hxy
  have hCross : ∀ (x : d.left) (y : d.right),
      l x.1 = r y.1 → x.1 = y.1 := by
    intro x y hxy
    have hOverlapEq :
        jL (f x.1) = jR (f y.1) := hxy
    obtain ⟨t, htL, htR⟩ :=
      hOverlap (f x.1) (f y.1) hOverlapEq
    obtain ⟨c, hc, hfc⟩ := t.2
    have hxc : x.1 = c := by
      apply hInjLeft x.2 hc.1
      calc
        f x.1 = e t := htL.symm
        _ = t.1 := rfl
        _ = f c := hfc.symm
    have hyc : y.1 = c := by
      apply hInjRight y.2 hc.2
      calc
        f y.1 = e t := htR.symm
        _ = t.1 := rfl
        _ = f c := hfc.symm
    exact hxc.trans hyc.symm
  have hInjective : Function.Injective k.toFun := by
    change Function.Injective (glueFreeCutMap d
      (fun x : d.left => l x.1)
      (fun x : d.right => r x.1))
    exact glueFreeCutMap_injective d
      (fun x : d.left => l x.1)
      (fun x : d.right => r x.1)
      hInjL hInjR hCross
  exact ⟨Z, hZ, H, hKH, k, hk, hInjective⟩

end TreeLike
end AllThoseEPPA
