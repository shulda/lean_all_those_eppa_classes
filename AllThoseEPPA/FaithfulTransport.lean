import AllThoseEPPA.FaithfulProjectionImage
import AllThoseEPPA.Automorphism
import AllThoseEPPA.FinitePartialEquiv

/-!
# Transport infrastructure for the faithful witness

This file develops the action of base automorphisms on bad irreducible
substructures and their valuation-index types.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- The image of a closed set under a total automorphism is closed. -/
theorem automorphism_image_isClosed
    (g : Structure.Automorphism act B₀)
    {S : Set β} (hS : B₀.IsClosed S) :
    B₀.IsClosed (g '' S) := by
  classical
  intro n F xs hxs y hy
  choose as has hgas using hxs
  have htuple : g.toPartialIsomorphism.toPartialEquiv ∘ as = xs := by
    funext i
    exact hgas i
  let F₀ : L.FuncSymbol n := act.onFunc g.lang⁻¹ F
  have hsym : act.onFunc g.lang F₀ = F := by
    simp [F₀, ← Language.Action.onFunc_mul]
  have hsource :
      ∀ i, as i ∈ g.toPartialIsomorphism.source := by
    intro i
    rw [g.source_eq_univ]
    exact Set.mem_univ _
  have hmap :=
    g.toPartialIsomorphism.map_func F₀ as hsource
  rw [hsym, htuple] at hmap
  have hyimg :
      y ∈
        Structure.imageSet
          g.toPartialIsomorphism.toPartialEquiv
          (B₀.func F₀ as) := by
    rw [hmap]
    exact hy
  rcases hyimg with ⟨t, ht, hty⟩
  have htS : t ∈ S :=
    hS F₀ as has ht
  exact ⟨t, htS, hty⟩

/-- An automorphism induces an embedding from a closed induced substructure
onto the induced structure on its image. -/
noncomputable def automorphismInducedEmbedding
    (g : Structure.Automorphism act B₀)
    (S : Set β) (hS : B₀.IsClosed S) :
    Structure.Embedding act
      (B₀.induce S hS)
      (B₀.induce (g '' S)
        (automorphism_image_isClosed act B₀ g hS)) where
  lang := g.lang
  toFun := fun x =>
    ⟨g x.1, ⟨x.1, x.2, rfl⟩⟩
  injective := by
    intro x y hxy
    apply Subtype.ext
    have hval :
        g x.1 = g y.1 :=
      congrArg Subtype.val hxy
    have hinv :=
      congrArg
        (fun t => Structure.Automorphism.symm g t) hval
    simpa using hinv
  map_rel_iff := by
    intro n R xs
    have hsource :
        ∀ i, (xs i).1 ∈ g.toPartialIsomorphism.source := by
      intro i
      rw [g.source_eq_univ]
      exact Set.mem_univ _
    have hg :=
      g.toPartialIsomorphism.map_rel_iff
        R (fun i => (xs i).1) hsource
    change
      B₀.rel (act.onRel g.lang R)
          (fun i => g (xs i).1) ↔
        B₀.rel R (fun i => (xs i).1)
    simpa [Function.comp_def] using hg
  map_func := by
    intro n F xs
    have hsource :
        ∀ i, (xs i).1 ∈ g.toPartialIsomorphism.source := by
      intro i
      rw [g.source_eq_univ]
      exact Set.mem_univ _
    have hg :=
      g.toPartialIsomorphism.map_func
        F (fun i => (xs i).1) hsource
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change
        g z.1 ∈
          B₀.func (act.onFunc g.lang F)
            (fun i => g (xs i).1)
      have himg :
          g z.1 ∈
            Structure.imageSet
              g.toPartialIsomorphism.toPartialEquiv
              (B₀.func F (fun i => (xs i).1)) :=
        ⟨z.1, hz, rfl⟩
      simpa [Function.comp_def] using
        (show
          Structure.imageSet
              g.toPartialIsomorphism.toPartialEquiv
              (B₀.func F (fun i => (xs i).1)) =
            B₀.func (act.onFunc g.lang F)
              (fun i => g (xs i).1) by
          simpa [Function.comp_def] using hg) ▸ himg
    · intro hy
      have hy' :
          y.1 ∈
            B₀.func (act.onFunc g.lang F)
              (fun i => g (xs i).1) := by
        exact hy
      have himg :
          y.1 ∈
            Structure.imageSet
              g.toPartialIsomorphism.toPartialEquiv
              (B₀.func F (fun i => (xs i).1)) := by
        rw [hg]
        simpa [Function.comp_def] using hy'
      rcases himg with ⟨t, ht, hty⟩
      have htS :
          t ∈ S :=
        hS F (fun i => (xs i).1)
          (fun i => (xs i).2) ht
      refine ⟨⟨t, htS⟩, ht, ?_⟩
      apply Subtype.ext
      exact hty

theorem automorphismInducedEmbedding_surjective
    (g : Structure.Automorphism act B₀)
    (S : Set β) (hS : B₀.IsClosed S) :
    Function.Surjective
      (automorphismInducedEmbedding act B₀ g S hS) := by
  intro y
  rcases y.2 with ⟨x, hx, hgx⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hgx

namespace BadIrreducible

/-- Transport a bad irreducible substructure by a base automorphism. -/
noncomputable def transport
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    BadIrreducible act A B₀ ψ where
  carrier := g '' I.carrier
  closed := automorphism_image_isClosed act B₀ g I.closed
  irreducible :=
    irreducible_target_of_surjective_embedding act
      (automorphismInducedEmbedding act B₀ g I.carrier I.closed)
      (automorphismInducedEmbedding_surjective
        act B₀ g I.carrier I.closed)
      I.irreducible
  bad := by
    rintro ⟨k, hk⟩
    apply I.bad
    refine ⟨k.comp g, ?_⟩
    intro x hx
    exact hk (g x) ⟨x, hx, rfl⟩

@[simp] theorem transport_carrier
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    (I.transport act A B₀ ψ g).carrier =
      g '' I.carrier :=
  rfl

theorem transport_comp
    (h g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    (I.transport act A B₀ ψ g).transport
        act A B₀ ψ h =
      I.transport act A B₀ ψ (h.comp g) := by
  apply BadIrreducible.ext
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g z, ⟨z, hz, rfl⟩, rfl⟩

theorem transport_symm_transport
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    (I.transport act A B₀ ψ g).transport
        act A B₀ ψ g.symm = I := by
  apply BadIrreducible.ext
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
    simp

theorem transport_transport_symm
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ) :
    (I.transport act A B₀ ψ g.symm).transport
        act A B₀ ψ g = I := by
  apply BadIrreducible.ext
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    refine ⟨g.symm x, ⟨x, hx, rfl⟩, ?_⟩
    simp

end BadIrreducible

/-- Base automorphisms permute bad irreducible substructures. -/
noncomputable def badIrreducibleEquiv
    (g : Structure.Automorphism act B₀) :
    BadIrreducible act A B₀ ψ ≃
      BadIrreducible act A B₀ ψ where
  toFun := fun I => I.transport act A B₀ ψ g
  invFun := fun I => I.transport act A B₀ ψ g.symm
  left_inv := BadIrreducible.transport_symm_transport act A B₀ ψ g
  right_inv := BadIrreducible.transport_transport_symm act A B₀ ψ g

/-- A base automorphism transports the bad irreducibles containing `x` to
those containing `g x`. -/
noncomputable def badAtEquiv
    (g : Structure.Automorphism act B₀)
    (x : β) :
    BadAt act A B₀ ψ x ≃
      BadAt act A B₀ ψ (g x) where
  toFun := fun I =>
    ⟨I.1.transport act A B₀ ψ g,
      ⟨x, I.2, rfl⟩⟩
  invFun := fun J =>
    ⟨J.1.transport act A B₀ ψ g.symm,
      by
        change x ∈ g.symm '' J.1.carrier
        refine ⟨g x, J.2, ?_⟩
        simp⟩
  left_inv := by
    intro I
    apply Subtype.ext
    exact BadIrreducible.transport_symm_transport
      act A B₀ ψ g I.1
  right_inv := by
    intro J
    apply Subtype.ext
    exact BadIrreducible.transport_transport_symm
      act A B₀ ψ g J.1

end Faithful
end AllThoseEPPA
