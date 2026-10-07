import AllThoseEPPA.FaithfulIrreducible
import Mathlib.Data.Fintype.Card

/-!
# The projection of an irreducible faithful-witness substructure is not bad

This file proves the pigeonhole step in Proposition `prop:faithful`.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z t

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Irreducibility is invariant under a surjective embedding. -/
private theorem irreducible_target_of_surjective_embedding
    {V : Type*} {W : Type*}
    {C : Structure L V} {D : Structure L W}
    (f : Structure.Embedding act C D)
    (hsurj : Function.Surjective f)
    (hC : C.IsIrreducible) :
    D.IsIrreducible := by
  constructor
  intro d
  apply hC.false
  let left : Set V := f ⁻¹' d.left
  let right : Set V := f ⁻¹' d.right
  refine
    { left := left
      right := right
      left_closed := ?_
      right_closed := ?_
      cover := ?_
      left_proper := ?_
      right_proper := ?_
      rel_local := ?_
      func_cross_empty := ?_ }
  · intro n F xs hxs y hy
    have hfy :
        f y ∈ D.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
      have himg :
          f y ∈ Structure.imageSet f.toFun (C.func F xs) :=
        ⟨y, hy, rfl⟩
      rw [f.map_func F xs] at himg
      exact himg
    exact d.left_closed (act.onFunc f.lang F)
      (f.toFun ∘ xs) hxs hfy
  · intro n F xs hxs y hy
    have hfy :
        f y ∈ D.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
      have himg :
          f y ∈ Structure.imageSet f.toFun (C.func F xs) :=
        ⟨y, hy, rfl⟩
      rw [f.map_func F xs] at himg
      exact himg
    exact d.right_closed (act.onFunc f.lang F)
      (f.toFun ∘ xs) hxs hfy
  · apply Set.eq_univ_of_forall
    intro x
    have hx : f x ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ _
    exact hx
  · intro hleft
    apply d.left_proper
    apply Set.eq_univ_of_forall
    intro y
    rcases hsurj y with ⟨x, rfl⟩
    have hx : x ∈ left := by
      rw [hleft]
      exact Set.mem_univ x
    exact hx
  · intro hright
    apply d.right_proper
    apply Set.eq_univ_of_forall
    intro y
    rcases hsurj y with ⟨x, rfl⟩
    have hx : x ∈ right := by
      rw [hright]
      exact Set.mem_univ x
    exact hx
  · intro n R xs hrel
    have hfrel :
        D.rel (act.onRel f.lang R) (f.toFun ∘ xs) :=
      (f.map_rel_iff R xs).2 hrel
    rcases
        d.rel_local (act.onRel f.lang R)
          (f.toFun ∘ xs) hfrel with
      hleft | hright
    · exact Or.inl hleft
    · exact Or.inr hright
  · intro n F xs hcross
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro y hy
    have hcrossD :
        ¬ ((∀ i, f (xs i) ∈ d.left) ∨
          (∀ i, f (xs i) ∈ d.right)) := by
      intro h
      apply hcross
      exact h
    have hempty :=
      d.func_cross_empty (act.onFunc f.lang F)
        (f.toFun ∘ xs) hcrossD
    have hfy :
        f y ∈ D.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
      have himg :
          f y ∈ Structure.imageSet f.toFun (C.func F xs) :=
        ⟨y, hy, rfl⟩
      rw [f.map_func F xs] at himg
      exact himg
    rw [hempty] at hfy
    exact hfy

/-- Image of a witness subset under the projection. -/
def projectionImage
    (S : Set (WitnessVertex act A B₀ ψ)) : Set β :=
  (fun w : WitnessVertex act A B₀ ψ => w.base) '' S

/-- The projection image of a closed witness subset is function-closed in the
base witness. -/
theorem projectionImage_isClosed
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S) :
    B₀.IsClosed (projectionImage act A B₀ ψ S) := by
  classical
  intro n F xs hxs y hy
  have hex :
      ∀ i, ∃ w : WitnessVertex act A B₀ ψ,
        w ∈ S ∧ w.base = xs i := by
    intro i
    simpa [projectionImage] using hxs i
  choose ws hwsS hwsBase using hex
  have htuple :
      (fun i => (ws i).base) = xs := by
    funext i
    exact hwsBase i
  have hy' :
      y ∈
        B₀.func F (fun i => (ws i).base) := by
    rw [htuple]
    exact hy
  have hproj :=
    projection_map_func_eq act A B₀ ψ F ws
  rw [← hproj] at hy'
  rcases hy' with ⟨z, hz, hzy⟩
  have hzS : z ∈ S :=
    hS F ws hwsS hz
  refine ⟨z, hzS, ?_⟩
  exact hzy

/-- On a generic closed subset, projection induces a surjective embedding
onto its image. -/
noncomputable def projectionInducedEmbedding
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S) :
    Structure.Embedding act
      ((witnessStructure act A B₀ ψ).induce S hS)
      (B₀.induce (projectionImage act A B₀ ψ S)
        (projectionImage_isClosed act A B₀ ψ S hS)) where
  lang := 1
  toFun := fun w =>
    ⟨w.1.base, ⟨w.1, w.2, rfl⟩⟩
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply projection_injOn_of_generic act A B₀ ψ S hgen
      x.2 y.2
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro n R xs
    have hEmb :=
      projection_isEmbeddingOn_of_generic
        act A B₀ ψ S hgen
    have hrel :=
      hEmb.2.1 R (fun i => (xs i).1)
        (fun i => (xs i).2)
    simpa [Structure.induce, Function.comp_def] using hrel
  map_func := by
    intro n F xs
    have hEmb :=
      projection_isEmbeddingOn_of_generic
        act A B₀ ψ S hgen
    have hfun :=
      hEmb.2.2 F (fun i => (xs i).1)
        (fun i => (xs i).2)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have himg :
          z.1.base ∈
            Structure.imageSet
              (fun w : WitnessVertex act A B₀ ψ => w.base)
              ((witnessStructure act A B₀ ψ).func F
                (fun i => (xs i).1)) :=
        ⟨z.1, hz, rfl⟩
      rw [hfun] at himg
      exact himg
    · intro hy
      have hy' :
          y.1 ∈
            B₀.func F
              (fun i => (xs i).1.base) := by
        exact hy
      rw [← hfun] at hy'
      rcases hy' with ⟨z, hz, hzy⟩
      have hzS : z ∈ S :=
        hS F (fun i => (xs i).1)
          (fun i => (xs i).2) hz
      refine ⟨⟨z, hzS⟩, hz, ?_⟩
      apply Subtype.ext
      exact hzy

theorem projectionInducedEmbedding_surjective
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hgen : WitnessSetGeneric act A B₀ ψ S) :
    Function.Surjective
      (projectionInducedEmbedding act A B₀ ψ S hS hgen) := by
  intro y
  rcases y.2 with ⟨w, hw, hwy⟩
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  exact hwy

/-- The projection image of an irreducible witness substructure is
irreducible in the base witness. -/
theorem projectionImage_isIrreducible
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hirr :
      ((witnessStructure act A B₀ ψ).induce S hS).IsIrreducible) :
    (B₀.induce (projectionImage act A B₀ ψ S)
      (projectionImage_isClosed act A B₀ ψ S hS)).IsIrreducible := by
  let hgen :=
    irreducible_witnessSetGeneric act A B₀ ψ S hS hirr
  exact
    irreducible_target_of_surjective_embedding act
      (projectionInducedEmbedding act A B₀ ψ S hS hgen)
      (projectionInducedEmbedding_surjective
        act A B₀ ψ S hS hgen)
      hirr

/-- The projection of an irreducible witness substructure is not bad.  If it
were bad, genericity would label all of its vertices injectively by all
vertices except the chosen hole, contradicting finite pigeonhole. -/
theorem irreducible_projection_not_bad
    [Finite β]
    (S : Set (WitnessVertex act A B₀ ψ))
    (hS : (witnessStructure act A B₀ ψ).IsClosed S)
    (hirr :
      ((witnessStructure act A B₀ ψ).induce S hS).IsIrreducible) :
    ∃ g : Structure.Automorphism act B₀,
      ∀ w, w ∈ S → ∃ a : α, g w.base = ψ a := by
  classical
  let hgen :=
    irreducible_witnessSetGeneric act A B₀ ψ S hS hirr
  by_contra hmove
  let I : BadIrreducible act A B₀ ψ :=
    { carrier := projectionImage act A B₀ ψ S
      closed := projectionImage_isClosed act A B₀ ψ S hS
      irreducible :=
        projectionImage_isIrreducible
          act A B₀ ψ S hS hirr
      bad := by
        rintro ⟨g, hg⟩
        apply hmove
        refine ⟨g, ?_⟩
        intro w hw
        exact hg w.base ⟨w, hw, rfl⟩ }

  let witnessOf (b : I.carrier) :
      WitnessVertex act A B₀ ψ :=
    Classical.choose
      (show ∃ w : WitnessVertex act A B₀ ψ,
          w ∈ S ∧ w.base = b.1 by
        simpa [I, projectionImage] using b.2)

  have witnessOf_mem (b : I.carrier) :
      witnessOf b ∈ S :=
    (Classical.choose_spec
      (show ∃ w : WitnessVertex act A B₀ ψ,
          w ∈ S ∧ w.base = b.1 by
        simpa [I, projectionImage] using b.2)).1

  have witnessOf_base (b : I.carrier) :
      (witnessOf b).base = b.1 :=
    (Classical.choose_spec
      (show ∃ w : WitnessVertex act A B₀ ψ,
          w ∈ S ∧ w.base = b.1 by
        simpa [I, projectionImage] using b.2)).2

  let centerPoint (b : I.carrier) :
      B₀.closureAtSet (witnessOf b).base :=
    ⟨(witnessOf b).base,
      B₀.mem_closureAtSet (witnessOf b).base⟩

  have witnessOf_mem_I (b : I.carrier) :
      (witnessOf b).base ∈ I.carrier := by
    rw [witnessOf_base]
    exact b.2

  let label (b : I.carrier) :
      BadLabel act A B₀ ψ I :=
    ((witnessOf b).pointAt act A B₀ ψ (centerPoint b)).2
      ⟨I, witnessOf_mem_I b⟩

  have hlabel_injective : Function.Injective label := by
    intro b c hbc
    have hg :=
      hgen
        ⟨witnessOf b, witnessOf_mem b⟩
        ⟨witnessOf c, witnessOf_mem c⟩
        (centerPoint b) (centerPoint c)
    rcases hg with heq | ⟨hne, hlabels⟩
    · apply Subtype.ext
      have hbase :
          (witnessOf b).base = (witnessOf c).base :=
        congrArg Sigma.fst heq
      rw [witnessOf_base b, witnessOf_base c] at hbase
      exact hbase
    · exfalso
      apply hlabels I
        (witnessOf_mem_I b)
        (witnessOf_mem_I c)
      exact congrArg Subtype.val hbc

  let forget :
      BadLabel act A B₀ ψ I → I.carrier :=
    fun a => ⟨a.1, a.2.1⟩

  have hforget_injective : Function.Injective forget := by
    intro a b hab
    apply Subtype.ext
    exact congrArg Subtype.val hab

  have hforget_not_surjective :
      ¬ Function.Surjective forget := by
    intro hsurj
    let hole : I.carrier :=
      ⟨I.hole act A B₀ ψ,
        I.hole_mem act A B₀ ψ⟩
    rcases hsurj hole with ⟨a, ha⟩
    have haval :
        a.1 = I.hole act A B₀ ψ :=
      congrArg Subtype.val ha
    exact a.2.2 haval

  letI : Fintype I.carrier := Fintype.ofFinite _
  letI : Fintype (BadLabel act A B₀ ψ I) :=
    Fintype.ofFinite _
  have hcard :
      Fintype.card (BadLabel act A B₀ ψ I) <
        Fintype.card I.carrier :=
    Fintype.card_lt_of_injective_not_surjective
      forget hforget_injective hforget_not_surjective
  exact
    (Fintype.not_injective_of_card_lt label hcard)
      hlabel_injective

end Faithful
end AllThoseEPPA
