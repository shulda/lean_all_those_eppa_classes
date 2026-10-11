import AllThoseEPPA.StrongCompletionKernelClosure

/-!
# Matching the two one-point closures of a collapsed pair

If a Γ-homomorphism-embedding f identifies a and b, then
its restrictions to Cl_A(a) and Cl_A(b) are injections with
the same exact image Cl_B(f(a)). Thus they define a canonical
bijection between the two source closures, by matching equal
f-values.

This is the set-theoretic core of the "identify the two
irreducible substructures U and V" step in Proposition 11.3.
The next step is to upgrade the bijection to a Γ-isomorphism
and analyze the residual identifications.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Each point of Cl_A(a) has exactly one counterpart in
Cl_A(b) with the same image, provided f(a)=f(b). -/
theorem existsUnique_fibreMate_in_closureAt
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    (u : A.closureAtSet a) :
    ∃! v : A.closureAtSet b, f v.1 = f u.1 := by
  have hImg : imageSet f.toFun (A.closureAtSet a) =
      imageSet f.toFun (A.closureAtSet b) :=
    f.image_closureAt_eq_of_same_fibre act hf hab
  have hu : f u.1 ∈ imageSet f.toFun (A.closureAtSet b) := by
    rw [← hImg]
    exact ⟨u.1, u.2, rfl⟩
  obtain ⟨v, hv, hvf⟩ := hu
  refine ⟨⟨v, hv⟩, hvf, ?_⟩
  intro w hw
  apply Subtype.ext
  exact (f.injOn_closureAt act hf b) w.2 hv
    (hw.trans hvf.symm)

/-- The canonical fibre-matching equivalence between the
two one-point closures. It preserves the image under f
pointwise, and is canonical (not dependent on arbitrary
choice of which preimage to use) because those restrictions
are injective. -/
noncomputable def closureFibreEquiv
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    (A.closureAtSet a) ≃ (A.closureAtSet b) := by
  classical
  let mate : (A.closureAtSet a) → (A.closureAtSet b) :=
    fun u => Classical.choose
      (f.existsUnique_fibreMate_in_closureAt act hf hab u)
  have hmate (u : A.closureAtSet a) :
      f (mate u).1 = f u.1 :=
    (Classical.choose_spec
      (f.existsUnique_fibreMate_in_closureAt act hf hab u)).1
  have hInjective : Function.Injective mate := by
    intro u v heq
    apply Subtype.ext
    apply (f.injOn_closureAt act hf a) u.2 v.2
    calc
      f u.1 = f (mate u).1 := (hmate u).symm
      _ = f (mate v).1 := by rw [heq]
      _ = f v.1 := hmate v
  have hSurjective : Function.Surjective mate := by
    intro y
    obtain ⟨x, hx, _⟩ :=
      f.existsUnique_fibreMate_in_closureAt act hf hab.symm y
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply (f.injOn_closureAt act hf b) (mate x).2 y.2
    exact (hmate x).trans hx
  exact Equiv.ofBijective mate ⟨hInjective, hSurjective⟩

/-- The matching equivalence commutes with f at every vertex.
We deliberately state this independently of Γ-isomorphism:
it is the precise property later used when gluing images. -/
theorem closureFibreEquiv_map
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    (u : A.closureAtSet a) :
    f ((f.closureFibreEquiv act hf hab) u).1 = f u.1 := by
  classical
  unfold closureFibreEquiv
  exact (Classical.choose_spec
      (f.existsUnique_fibreMate_in_closureAt act hf hab u)).1

end Homomorphism
end Structure
end AllThoseEPPA
