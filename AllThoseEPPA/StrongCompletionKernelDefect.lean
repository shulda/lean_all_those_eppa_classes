import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega
import AllThoseEPPA.StrongCompletionCollisionMeasure

/-!
# Kernel defect and strict reduction under nontrivial factorization

The paper minimizes the number of unordered pairs identified by a
completion. A simpler equivalent well-founded strategy is to minimize
the **kernel defect** |A| - |f(A)| of a finite map f.

Suppose f = g ∘ q, with q : A → A' surjective.
If q is not injective, the kernel defect of g is strictly smaller
than that of f, regardless of g.
If g is not injective, the kernel defect of q is strictly smaller
than that of f.

This provides exactly the two strict reductions for the
minimal-counterexample proof of Proposition 11.3, without comparing
Finsets of pairs on different carrier types.

No homomorphism-embedding quotient q is constructed here: that is
the remaining geometric argument.
-/

namespace AllThoseEPPA
namespace TreeLike
namespace StrongCompletionKernel

universe u v w
variable {V : Type u} {U : Type v} {W : Type w}
variable [Fintype V] [Fintype U]

/-- Number of vertices lost after identifying all fibres of f. -/
noncomputable def kernelDefect {X : Type*} [Fintype X] {Y : Type*}
    (f : X → Y) : ℕ :=
  Fintype.card X - (Set.range f).ncard

/-- A surjective first factor identifies exactly enough points
to make the image of g ∘ q equal to the image of g. -/
theorem range_comp_of_surjective
    (q : V → U) (g : U → W)
    (hq : Function.Surjective q) :
    Set.range (g ∘ q) = Set.range g := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨q x, hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hxy⟩ := hq y
    refine ⟨x, ?_⟩
    simpa [Function.comp, hxy] using hy

/-- Every range of a map from a finite type has at most as
many distinct values as the domain has vertices. -/
theorem ncard_range_le_card (g : U → W) :
    (Set.range g).ncard ≤ Fintype.card U := by
  have h := Set.ncard_image_le (f := g)
    (s := (Set.univ : Set U)) Set.finite_univ
  simpa only [Set.image_univ, Set.ncard_univ,
    Nat.card_eq_fintype_card] using h

/-- If q is a noninjective surjection then g has strictly
smaller kernel defect than the composite g ∘ q. -/
theorem kernelDefect_second_lt_composite
    (q : V → U) (g : U → W)
    (hq : Function.Surjective q)
    (hnq : ¬ Function.Injective q) :
    kernelDefect g < kernelDefect (g ∘ q) := by
  have hcard : Fintype.card U < Fintype.card V :=
    Fintype.card_lt_of_surjective_not_injective q hq hnq
  have hk : (Set.range g).ncard ≤ Fintype.card U :=
    ncard_range_le_card g
  unfold kernelDefect
  rw [range_comp_of_surjective q g hq]
  exact Nat.sub_lt_sub_right hk hcard

/-- A noninjective map from a finite type has strictly
fewer different values than domain elements. -/
theorem ncard_range_lt_card_of_not_injective
    (g : U → W)
    (hng : ¬ Function.Injective g) :
    (Set.range g).ncard < Fintype.card U := by
  classical
  let p : U → Set.range g :=
    fun u => ⟨g u, ⟨u, rfl⟩⟩
  have hpSurj : Function.Surjective p := by
    intro z
    obtain ⟨y, hy⟩ := z.2
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy
  have hpNoninj : ¬ Function.Injective p := by
    intro hp
    apply hng
    intro a b hab
    apply hp
    apply Subtype.ext
    exact hab
  letI : Finite (Set.range g) :=
    Finite.of_surjective p hpSurj
  letI : Fintype (Set.range g) :=
    Fintype.ofFinite (Set.range g)
  have hlt :
      Fintype.card (Set.range g) < Fintype.card U :=
    Fintype.card_lt_of_surjective_not_injective p hpSurj hpNoninj
  simpa only [← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card] using hlt

/-- If the second factor g still identifies two points, then
q has strictly smaller kernel defect than its composite.
Together with the preceding theorem, this proves that a
nontrivial surjective factorization always decreases kernel
defect on either factor. -/
theorem kernelDefect_first_lt_composite
    (q : V → U) (g : U → W)
    (hq : Function.Surjective q)
    (hng : ¬ Function.Injective g) :
    kernelDefect q < kernelDefect (g ∘ q) := by
  have hqCard : Fintype.card U ≤ Fintype.card V :=
    Fintype.card_le_of_surjective q hq
  have hgCard : (Set.range g).ncard < Fintype.card U :=
    ncard_range_lt_card_of_not_injective g hng
  have hRangeQ : Set.range q = Set.univ :=
    Set.range_eq_univ.mpr hq
  unfold kernelDefect
  rw [hRangeQ, Set.ncard_univ, Nat.card_eq_fintype_card,
      range_comp_of_surjective q g hq]
  omega


/-- Applying an injective map after a finite-domain map does not
change the number of identifications: the two ranges have the
same cardinality. -/
theorem kernelDefect_postcompose_injective
    {X : Type*} [Fintype X] {Y Z : Type*}
    (q : X → Y) (e : Y → Z)
    (he : Function.Injective e) :
    kernelDefect (e ∘ q) = kernelDefect q := by
  unfold kernelDefect
  rw [Set.range_comp, Set.ncard_image_of_injective _ he]

end StrongCompletionKernel
end TreeLike
end AllThoseEPPA
