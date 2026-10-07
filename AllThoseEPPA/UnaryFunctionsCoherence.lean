import AllThoseEPPA.UnaryFunctions

/-!
# Coherence and extension for unary-function EPPA

This file continues the formalization of Proposition `prop:eppafunctions`
after the presentation-independent physical witness has been constructed.
-/

namespace AllThoseEPPA
namespace UnaryFunctions

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} [Fintype α]
variable (act : L.Action Γ) (A : Structure L α)
variable {β : Type z} [Finite β]
variable (B₀ : Structure L.relationalReduct β)


/-- A realised physical valuation has no function values outside its
support. -/
theorem PhysicalValuation.func_eq_empty_of_not_mem_support
    {x : β} (s : PhysicalValuation act A B₀ x)
    {n : ℕ} (F : L.FuncSymbol n) (a : β)
    (ha : a ∉ s.1.support) :
    s.1.func F a = ∅ := by
  rcases s.2 with ⟨v, hv⟩
  ext b
  constructor
  · intro hb
    have hb' :
        b ∈ Valuation.physicalFunc act A B₀ v F a := by
      change b ∈
        (Valuation.physicalSignature act A B₀ v).func F a
      rw [hv]
      exact hb
    rcases hb' with ⟨z, hza, y, hy, hby⟩
    exfalso
    apply ha
    rw [← hv]
    exact ⟨z, hza⟩
  · intro hb
    simpa using hb

/-- In the generic physical valuation, a relabelled function symbol has
exactly the embedded image of the corresponding original function values. -/
theorem genericPhysicalValuation_func_image
    (ψ₀ : Structure.Embedding act.relationalReduct
      A.relationalReduct B₀)
    (x a : α) (ha : a ∈ A.closureAtSet x)
    {n : ℕ} (F : L.FuncSymbol n) :
    (genericPhysicalValuation act A B₀ ψ₀ x).1.func
        (act.onFunc ψ₀.lang F) (ψ₀ a) =
      ψ₀ '' A.func F (fun _ => a) := by
  ext b
  rw [genericPhysicalValuation_mem_func_at_image_iff
    act A B₀ ψ₀ x a ha (act.onFunc ψ₀.lang F) b]
  constructor
  · rintro ⟨y, hy, hby⟩
    refine ⟨y, ?_, hby.symm⟩
    simpa [Structure.relabel_func, ← Language.Action.onFunc_mul] using hy
  · rintro ⟨y, hy, hby⟩
    refine ⟨y, ?_, hby.symm⟩
    simpa [Structure.relabel_func, ← Language.Action.onFunc_mul] using hy


/-- Physical witness vertices are determined by their base point and the
physical signature carried over that base. -/
theorem PhysicalWitnessVertex.ext_of_signature
    (w z : PhysicalWitnessVertex act A B₀)
    (hbase : w.base = z.base)
    (hsupport : w.valuation.1.support = z.valuation.1.support)
    (hfunc :
      ∀ {n : ℕ} (F : L.FuncSymbol n) (a : β),
        w.valuation.1.func F a = z.valuation.1.func F a) :
    w = z := by
  rcases w with ⟨x, s⟩
  rcases z with ⟨y, t⟩
  change x = y at hbase
  subst y
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply Subtype.ext
  apply ValuationSignature.ext
  · exact hsupport
  · funext n F a
    exact hfunc F a

/-- The language equation in an extension square also gives the inverse
conjugacy relation needed for transporting function symbols. -/
theorem inverse_language_conjugacy
    (ψ₀ : Structure.Embedding act.relationalReduct
      A.relationalReduct B₀)
    (p : Structure.PartialAutomorphism act A)
    (h : Structure.Automorphism act.relationalReduct B₀)
    (hext :
      Structure.ExtendsAlong act.relationalReduct ψ₀
        (reductPartialAutomorphism act A p) h) :
    h.lang⁻¹ = ψ₀.lang * p.lang⁻¹ * ψ₀.lang⁻¹ := by
  have hinv := congrArg Inv.inv hext.1
  have hinv' :
      ψ₀.lang⁻¹ * h.lang⁻¹ =
        p.lang⁻¹ * ψ₀.lang⁻¹ := by
    simpa [mul_inv_rev] using hinv
  calc
    h.lang⁻¹ =
        ψ₀.lang * (ψ₀.lang⁻¹ * h.lang⁻¹) := by
      simp [mul_assoc]
    _ = ψ₀.lang * (p.lang⁻¹ * ψ₀.lang⁻¹) := by
      rw [hinv']
    _ = ψ₀.lang * p.lang⁻¹ * ψ₀.lang⁻¹ := by
      simp [mul_assoc]

/-- A base extension maps the support of a generic physical valuation exactly
onto the support of the generic valuation at the image point. -/
theorem genericPhysicalValuation_transport_support_of_extends
    (ψ₀ : Structure.Embedding act.relationalReduct
      A.relationalReduct B₀)
    (p : Structure.PartialAutomorphism act A)
    (h : Structure.Automorphism act.relationalReduct B₀)
    (hext :
      Structure.ExtendsAlong act.relationalReduct ψ₀
        (reductPartialAutomorphism act A p) h)
    {x : α} (hx : x ∈ p.source) :
    (PhysicalValuation.transport act A B₀ h
        (genericPhysicalValuation act A B₀ ψ₀ x)).1.support =
      (genericPhysicalValuation act A B₀ ψ₀ (p x)).1.support := by
  rw [PhysicalValuation.transport_val,
    ValuationSignature.transport_support,
    genericPhysicalValuation_support,
    genericPhysicalValuation_support]
  have hclsrc :
      A.closureAtSet x ⊆ p.source :=
    partialAutomorphism_closureAtSet_subset_source act A p hx
  have hclmap :=
    partialAutomorphism_image_closureAtSet act A p hx
  ext b
  constructor
  · rintro ⟨c, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨p y, ?_, ?_⟩
    · rw [← hclmap]
      exact ⟨y, hy, rfl⟩
    · exact (hext.2 y (hclsrc hy)).symm
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ p.toPartialEquiv '' A.closureAtSet x := by
      rw [hclmap]
      exact hz
    rcases hz' with ⟨y, hy, rfl⟩
    refine ⟨ψ₀ y, ⟨y, hy, rfl⟩, ?_⟩
    exact hext.2 y (hclsrc hy)

/-- At every point of the source one-point closure, transporting the generic
physical valuation gives exactly the function data of the generic valuation
at the image point. -/
theorem genericPhysicalValuation_transport_func_of_extends
    (ψ₀ : Structure.Embedding act.relationalReduct
      A.relationalReduct B₀)
    (p : Structure.PartialAutomorphism act A)
    (h : Structure.Automorphism act.relationalReduct B₀)
    (hext :
      Structure.ExtendsAlong act.relationalReduct ψ₀
        (reductPartialAutomorphism act A p) h)
    {x y : α} (hx : x ∈ p.source)
    (hy : y ∈ A.closureAtSet x)
    {n : ℕ} (F : L.FuncSymbol n) :
    (PhysicalValuation.transport act A B₀ h
        (genericPhysicalValuation act A B₀ ψ₀ x)).1.func
        F (ψ₀ (p y)) =
      (genericPhysicalValuation act A B₀ ψ₀ (p x)).1.func
        F (ψ₀ (p y)) := by
  let e := automorphismEquiv act h
  let K : L.FuncSymbol n := act.onFunc ψ₀.lang⁻¹ F
  let K₀ : L.FuncSymbol n := act.onFunc p.lang⁻¹ K
  have hclsrc :
      A.closureAtSet x ⊆ p.source :=
    partialAutomorphism_closureAtSet_subset_source act A p hx
  have hysrc : y ∈ p.source := hclsrc hy
  have hpy : h (ψ₀ y) = ψ₀ (p y) :=
    hext.2 y hysrc
  have hpre : e.symm (ψ₀ (p y)) = ψ₀ y := by
    calc
      e.symm (ψ₀ (p y)) = e.symm (h (ψ₀ y)) :=
        congrArg e.symm hpy.symm
      _ = ψ₀ y := by
        simpa [e] using e.symm_apply_apply (ψ₀ y)
  have hinv :=
    inverse_language_conjugacy act A B₀ ψ₀ p h hext
  have hsourceSymbol :
      act.onFunc h.lang⁻¹ F =
        act.onFunc ψ₀.lang K₀ := by
    rw [hinv]
    change
      act.onFunc (ψ₀.lang * p.lang⁻¹ * ψ₀.lang⁻¹) F =
        act.onFunc ψ₀.lang
          (act.onFunc p.lang⁻¹
            (act.onFunc ψ₀.lang⁻¹ F))
    rw [Language.Action.onFunc_mul, Language.Action.onFunc_mul]
  have hpcl : p y ∈ A.closureAtSet (p x) := by
    rw [← partialAutomorphism_image_closureAtSet act A p hx]
    exact ⟨y, hy, rfl⟩
  have hsrc :=
    genericPhysicalValuation_func_image
      act A B₀ ψ₀ x y hy K₀
  have htgt :=
    genericPhysicalValuation_func_image
      act A B₀ ψ₀ (p x) (p y) hpcl K
  have htgt' :
      (genericPhysicalValuation act A B₀ ψ₀ (p x)).1.func
          F (ψ₀ (p y)) =
        ψ₀ '' A.func K (fun _ => p y) := by
    simpa [K, ← Language.Action.onFunc_mul] using htgt
  have hK :
      act.onFunc p.lang K₀ = K := by
    simp [K₀, ← Language.Action.onFunc_mul]
  have hpfunc :
      Structure.imageSet p.toPartialEquiv
          (A.func K₀ (fun _ => y)) =
        A.func K (fun _ => p y) := by
    have hm := p.map_func K₀ (fun _ => y) (fun _ => hysrc)
    simpa [hK, Function.comp_def] using hm
  rw [PhysicalValuation.transport_val,
    ValuationSignature.transport_func, hpre, hsourceSymbol, hsrc]
  rw [htgt']
  ext b
  constructor
  · rintro ⟨c, ⟨t, ht, rfl⟩, rfl⟩
    have htcl : t ∈ A.closureAtSet x :=
      (A.isClosed_closureSet ({x} : Set α))
        K₀ (fun _ => y) (fun _ => hy) ht
    have hpt : p t ∈ A.func K (fun _ => p y) := by
      rw [← hpfunc]
      exact ⟨t, ht, rfl⟩
    refine ⟨p t, hpt, ?_⟩
    exact (hext.2 t (hclsrc htcl)).symm
  · rintro ⟨u, hu, rfl⟩
    rw [← hpfunc] at hu
    rcases hu with ⟨t, ht, rfl⟩
    have htcl : t ∈ A.closureAtSet x :=
      (A.isClosed_closureSet ({x} : Set α))
        K₀ (fun _ => y) (fun _ => hy) ht
    refine ⟨ψ₀ t, ⟨t, ht, rfl⟩, ?_⟩
    exact hext.2 t (hclsrc htcl)


/-- A base extension carries every generic physical witness vertex to the
generic vertex prescribed by the original partial automorphism. -/
theorem genericPhysicalVertex_transport_of_extends
    (ψ₀ : Structure.Embedding act.relationalReduct
      A.relationalReduct B₀)
    (p : Structure.PartialAutomorphism act A)
    (h : Structure.Automorphism act.relationalReduct B₀)
    (hext :
      Structure.ExtendsAlong act.relationalReduct ψ₀
        (reductPartialAutomorphism act A p) h)
    {x : α} (hx : x ∈ p.source) :
    PhysicalWitnessVertex.transport act A B₀ h
        (genericPhysicalVertex act A B₀ ψ₀ x) =
      genericPhysicalVertex act A B₀ ψ₀ (p x) := by
  have hbase : h (ψ₀ x) = ψ₀ (p x) :=
    hext.2 x hx
  have hsupport :=
    genericPhysicalValuation_transport_support_of_extends
      act A B₀ ψ₀ p h hext hx
  apply PhysicalWitnessVertex.ext_of_signature act A B₀
  · exact hbase
  · exact hsupport
  · intro n F a
    by_cases ha :
        a ∈
          (genericPhysicalValuation act A B₀ ψ₀ (p x)).1.support
    · have ha' := ha
      rw [genericPhysicalValuation_support] at ha'
      rcases ha' with ⟨z, hz, rfl⟩
      have hz' :
          z ∈ p.toPartialEquiv '' A.closureAtSet x := by
        rw [partialAutomorphism_image_closureAtSet act A p hx]
        exact hz
      rcases hz' with ⟨y, hy, rfl⟩
      exact
        genericPhysicalValuation_transport_func_of_extends
          act A B₀ ψ₀ p h hext hx hy F
    · have haL :
          a ∉
            (PhysicalValuation.transport act A B₀ h
              (genericPhysicalValuation act A B₀ ψ₀ x)).1.support := by
        rw [hsupport]
        exact ha
      have hl :=
        PhysicalValuation.func_eq_empty_of_not_mem_support
          act A B₀
          (PhysicalValuation.transport act A B₀ h
            (genericPhysicalValuation act A B₀ ψ₀ x))
          F a haL
      have hr :=
        PhysicalValuation.func_eq_empty_of_not_mem_support
          act A B₀
          (genericPhysicalValuation act A B₀ ψ₀ (p x))
          F a ha
      exact hl.trans hr.symm

/-- The lifted witness automorphism extends the original partial automorphism
along the generic physical embedding. -/
theorem physicalWitnessAutomorphism_extends_generic
    (hA : A.HasFiniteRelabelOrbit act)
    (ψ₀ : Structure.Embedding act.relationalReduct
      A.relationalReduct B₀)
    (p : Structure.PartialAutomorphism act A)
    (h : Structure.Automorphism act.relationalReduct B₀)
    (hext :
      Structure.ExtendsAlong act.relationalReduct ψ₀
        (reductPartialAutomorphism act A p) h) :
    Structure.ExtendsAlong act
      (genericPhysicalEmbedding act A B₀ ψ₀) p
      (physicalWitnessAutomorphism act A B₀ hA h) := by
  constructor
  · change h.lang * ψ₀.lang = ψ₀.lang * p.lang
    exact hext.1
  · intro x hx
    change
      PhysicalWitnessVertex.transport act A B₀ h
          (genericPhysicalVertex act A B₀ ψ₀ x) =
        genericPhysicalVertex act A B₀ ψ₀ (p x)
    exact
      genericPhysicalVertex_transport_of_extends
        act A B₀ ψ₀ p h hext hx

/-- Conjugation of physical signatures is functorial in the base
automorphism. -/
theorem ValuationSignature.transport_comp
    (h g : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x) :
    (s.transport act B₀ g).transport act B₀ h =
      s.transport act B₀ (h.comp g) := by
  apply ValuationSignature.ext
  · change h '' (g '' s.support) = (fun z => h (g z)) '' s.support
    ext b
    constructor
    · rintro ⟨c, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, ⟨a, ha, rfl⟩, rfl⟩
  · funext n F a
    let eh := automorphismEquiv act h
    let eg := automorphismEquiv act g
    let ec := automorphismEquiv act (h.comp g)
    have hpre : eg.symm (eh.symm a) = ec.symm a := by
      apply ec.injective
      rw [ec.apply_symm_apply]
      change (h.comp g) (eg.symm (eh.symm a)) = a
      rw [Structure.Automorphism.comp_apply]
      rw [show g (eg.symm (eh.symm a)) = eh.symm a by
        exact eg.apply_symm_apply (eh.symm a)]
      exact eh.apply_symm_apply a
    have hsym :
        act.onFunc g.lang⁻¹ (act.onFunc h.lang⁻¹ F) =
          act.onFunc (h.comp g).lang⁻¹ F := by
      change
        act.onFunc g.lang⁻¹ (act.onFunc h.lang⁻¹ F) =
          act.onFunc (h.lang * g.lang)⁻¹ F
      rw [mul_inv_rev]
      exact (Language.Action.onFunc_mul act g.lang⁻¹ h.lang⁻¹ F).symm
    change
      h '' (g '' s.func
        (act.onFunc g.lang⁻¹ (act.onFunc h.lang⁻¹ F))
        (eg.symm (eh.symm a))) =
        (fun z => h (g z)) ''
          s.func (act.onFunc (h.comp g).lang⁻¹ F) (ec.symm a)
    rw [hpre, hsym]
    ext b
    constructor
    · rintro ⟨c, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨d, hd, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨g d, ⟨d, hd, rfl⟩, rfl⟩


/-- Functoriality descends to realised physical valuations. -/
theorem PhysicalValuation.transport_comp
    (h g : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : PhysicalValuation act A B₀ x) :
    PhysicalValuation.transport act A B₀ h
        (PhysicalValuation.transport act A B₀ g s) =
      PhysicalValuation.transport act A B₀ (h.comp g) s := by
  apply Subtype.ext
  exact ValuationSignature.transport_comp act B₀ h g s.1

/-- Transport of whole witness vertices is functorial. -/
theorem PhysicalWitnessVertex.transport_comp
    (h g : Structure.Automorphism act.relationalReduct B₀)
    (w : PhysicalWitnessVertex act A B₀) :
    PhysicalWitnessVertex.transport act A B₀ h
        (PhysicalWitnessVertex.transport act A B₀ g w) =
      PhysicalWitnessVertex.transport act A B₀ (h.comp g) w := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (PhysicalValuation.transport_comp act A B₀ h g w.2)

/-- Lifting base automorphisms to the unary witness preserves composition. -/
theorem physicalWitnessAutomorphism_comp
    (hA : A.HasFiniteRelabelOrbit act)
    (h g : Structure.Automorphism act.relationalReduct B₀) :
    physicalWitnessAutomorphism act A B₀ hA (h.comp g) =
      (physicalWitnessAutomorphism act A B₀ hA h).comp
        (physicalWitnessAutomorphism act A B₀ hA g) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro w
    change
      PhysicalWitnessVertex.transport act A B₀ (h.comp g) w =
        PhysicalWitnessVertex.transport act A B₀ h
          (PhysicalWitnessVertex.transport act A B₀ g w)
    exact (PhysicalWitnessVertex.transport_comp act A B₀ h g w).symm

end UnaryFunctions
end AllThoseEPPA
