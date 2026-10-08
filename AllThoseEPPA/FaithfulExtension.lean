import AllThoseEPPA.FaithfulWitnessAutomorphism

/-!
# Extension property of the faithful witness automorphism
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

/-- Every one-point closure of the faithful witness is a generic witness
subset. -/
theorem closureAtSet_witnessSetGeneric
    (w : WitnessVertex act A B₀ ψ) :
    WitnessSetGeneric act A B₀ ψ
      ((witnessStructure act A B₀ ψ).closureAtSet w) := by
  intro x y u v
  exact
    points_generic_of_mem_closure_same_ancestor
      act A B₀ ψ w x.1 y.1 x.2 y.2 u v

/-- The source of a partial automorphism contains the whole one-point closure
of each source vertex. -/
theorem partialAutomorphism_closure_subset_source
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    {w : WitnessVertex act A B₀ ψ}
    (hw : w ∈ p.source) :
    (witnessStructure act A B₀ ψ).closureAtSet w ⊆ p.source := by
  apply
    (witnessStructure act A B₀ ψ).closureSet_minimal
      p.source_closed
  intro x hx
  have hxw : x = w := by simpa using hx
  subst x
  exact hw

/-- A partial automorphism maps a source one-point closure into the one-point
closure of the image vertex. -/
theorem partialAutomorphism_maps_closure
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    {w d : WitnessVertex act A B₀ ψ}
    (hw : w ∈ p.source)
    (hd :
      d ∈ (witnessStructure act A B₀ ψ).closureAtSet w) :
    p d ∈
      (witnessStructure act A B₀ ψ).closureAtSet (p w) := by
  let C := witnessStructure act A B₀ ψ
  let T : Set (WitnessVertex act A B₀ ψ) :=
    {x | x ∈ p.source ∧ p x ∈ C.closureAtSet (p w)}
  have hTclosed : C.IsClosed T := by
    intro n F xs hxs y hy
    have hxsrc : ∀ i, xs i ∈ p.source :=
      fun i => (hxs i).1
    have hysrc : y ∈ p.source :=
      p.source_closed F xs hxsrc hy
    refine ⟨hysrc, ?_⟩
    have hpy :
        p y ∈
          C.func (act.onFunc p.lang F)
            (p.toPartialEquiv ∘ xs) := by
      have hmap := p.map_func F xs hxsrc
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    exact
      (C.isClosed_closureSet ({p w} : Set _))
        (act.onFunc p.lang F)
        (p.toPartialEquiv ∘ xs)
        (fun i => (hxs i).2)
        hpy
  have hwT : w ∈ T :=
    ⟨hw, C.mem_closureAtSet (p w)⟩
  have hsub : C.closureAtSet w ⊆ T := by
    apply C.closureSet_minimal hTclosed
    intro x hx
    have hxw : x = w := by simpa using hx
    subst x
    exact hwT
  exact (hsub hd).2

/-- A restriction-descendant of a source vertex is again in the source. -/
theorem restrictionVertex_mem_source
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    restrictionVertex act A B₀ ψ w y hy ∈ p.source :=
  partialAutomorphism_closure_subset_source
    act A B₀ ψ p hw
    (restrictionVertex_mem_closureAtSet
      act A B₀ ψ w y hy)

/-- Base compatibility and genericity determine the image of every
restriction-descendant exactly. -/
theorem partialAutomorphism_restrictionVertex
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    let hy' :
        g y ∈ B₀.closureAtSet (p w).base := by
      have h :=
        automorphism_maps_closureAtSet act B₀ g hy
      simpa [hcompat.2 w hw] using h
    p (restrictionVertex act A B₀ ψ w y hy) =
      restrictionVertex act A B₀ ψ
        (p w) (g y) hy' := by
  dsimp
  let d := restrictionVertex act A B₀ ψ w y hy
  let hy' : g y ∈ B₀.closureAtSet (p w).base := by
    have h :=
      automorphism_maps_closureAtSet act B₀ g hy
    simpa [hcompat.2 w hw] using h
  let r :=
    restrictionVertex act A B₀ ψ
      (p w) (g y) hy'
  have hdsrc : d ∈ p.source :=
    restrictionVertex_mem_source
      act A B₀ ψ p w hw y hy
  have hpdcl :
      p d ∈
        (witnessStructure act A B₀ ψ).closureAtSet (p w) :=
    partialAutomorphism_maps_closure
      act A B₀ ψ p hw
      (restrictionVertex_mem_closureAtSet
        act A B₀ ψ w y hy)
  have hrcl :
      r ∈
        (witnessStructure act A B₀ ψ).closureAtSet (p w) :=
    restrictionVertex_mem_closureAtSet
      act A B₀ ψ (p w) (g y) hy'
  have hbase :
      (p d).base = r.base := by
    calc
      (p d).base = g d.base :=
        (hcompat.2 d hdsrc).symm
      _ = g y := by rfl
      _ = r.base := by rfl
  exact
    projection_injOn_of_generic
      act A B₀ ψ
      ((witnessStructure act A B₀ ψ).closureAtSet (p w))
      (closureAtSet_witnessSetGeneric
        act A B₀ ψ (p w))
      hpdcl hrcl hbase


/-- The centre valuation point of a restriction-descendant is exactly the
corresponding internal valuation point of its ancestor. -/
theorem centerValuationPoint_restrictionVertex
    (w : WitnessVertex act A B₀ ψ)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    centerValuationPoint act A B₀ ψ
        (restrictionVertex act A B₀ ψ w y hy) =
      w.pointAt act A B₀ ψ
        (⟨y, hy⟩ : B₀.closureAtSet w.base) := by
  change
    valuationPointAt act A B₀ ψ
        (w.valuation.restrict act A B₀ ψ y hy).1
        (⟨y, B₀.mem_closureAtSet y⟩ :
          B₀.closureAtSet y) =
      valuationPointAt act A B₀ ψ w.valuation.1
        (⟨y, hy⟩ : B₀.closureAtSet w.base)
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  have hz :
      closureInclusion B₀ hy
          (⟨y, B₀.mem_closureAtSet y⟩ :
            B₀.closureAtSet y) =
        (⟨y, hy⟩ : B₀.closureAtSet w.base) := by
    apply Subtype.ext
    rfl
  exact
    congr_arg_heq
      (fun z : B₀.closureAtSet w.base =>
        w.valuation.1 z)
      hz

/-- Equal valuation points have the same label on a bad irreducible,
after transporting the irrelevant membership proof. -/
theorem valuationPointLabel_congr
    {q r : ValuationPoint act A B₀ ψ}
    (hqr : q = r)
    (I : BadIrreducible act A B₀ ψ)
    (hqI : q.1 ∈ I.carrier)
    (hrI : r.1 ∈ I.carrier) :
    q.2 ⟨I, hqI⟩ = r.2 ⟨I, hrI⟩ := by
  subst r
  rfl

/-- The centre label of a restriction-descendant is the corresponding
component of the ancestor valuation assignment. -/
theorem centerLabel_restrictionVertex
    (w : WitnessVertex act A B₀ ψ)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base)
    (I : BadIrreducible act A B₀ ψ)
    (hyI : y ∈ I.carrier) :
    centerLabel act A B₀ ψ
        (restrictionVertex act A B₀ ψ w y hy)
        I hyI =
      (w.valuation.1
        (⟨y, hy⟩ : B₀.closureAtSet w.base))
        ⟨I, hyI⟩ := by
  unfold centerLabel
  exact
    valuationPointLabel_congr
      act A B₀ ψ
      (centerValuationPoint_restrictionVertex
        act A B₀ ψ w y hy)
      I hyI hyI

/-- Centre labels are insensitive to replacing a witness vertex by an equal
one; the membership proofs are irrelevant. -/
theorem centerLabel_congr
    {u v : WitnessVertex act A B₀ ψ}
    (huv : u = v)
    (I : BadIrreducible act A B₀ ψ)
    (hu : u.base ∈ I.carrier)
    (hv : v.base ∈ I.carrier) :
    centerLabel act A B₀ ψ u I hu =
      centerLabel act A B₀ ψ v I hv := by
  subst v
  rfl


/-- On a source vertex, transport of the valuation function at every point of
its one-point closure is exactly the valuation function carried by the
partial-automorphism image at the transported point. -/
theorem valuationFunction_transport_eq_of_mem_source [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source)
    (y : β) (hy : y ∈ B₀.closureAtSet w.base) :
    let hy' :
        g y ∈ B₀.closureAtSet (p w).base := by
      have h :=
        automorphism_maps_closureAtSet act B₀ g hy
      simpa [hcompat.2 w hw] using h
    valuationFunctionEquiv act A B₀ ψ
        p g hsource htarget hcompat y
        (w.valuation.1
          (⟨y, hy⟩ : B₀.closureAtSet w.base)) =
      (p w).valuation.1
        (⟨g y, hy'⟩ :
          B₀.closureAtSet (p w).base) := by
  dsimp
  funext J
  rcases
      (badAtEquiv act A B₀ ψ g y).surjective J with
    ⟨I, rfl⟩
  rw [valuationFunctionEquiv_apply_transport
    act A B₀ ψ p g hsource htarget hcompat
    y
    (w.valuation.1
      (⟨y, hy⟩ : B₀.closureAtSet w.base))
    I]
  let d :=
    restrictionVertex act A B₀ ψ w y hy
  have hdsrc : d ∈ p.source :=
    restrictionVertex_mem_source
      act A B₀ ψ p w hw y hy
  let hy' : g y ∈ B₀.closureAtSet (p w).base := by
    have h :=
      automorphism_maps_closureAtSet act B₀ g hy
    simpa [hcompat.2 w hw] using h
  let r :=
    restrictionVertex act A B₀ ψ
      (p w) (g y) hy'
  have hpd : p d = r := by
    simpa [d, r, hy'] using
      (partialAutomorphism_restrictionVertex
        act A B₀ ψ p g hcompat w hw y hy)
  let GI :=
    I.1.transport act A B₀ ψ g
  let hpdI : (p d).base ∈ GI.carrier :=
    ⟨d.base, I.2, hcompat.2 d hdsrc⟩
  let hrI : r.base ∈ GI.carrier :=
    ⟨y, I.2, rfl⟩
  have hcenter :
      labelExtension act A B₀ ψ p g I.1
          hsource htarget hcompat
          (centerLabel act A B₀ ψ d I.1 I.2) =
        centerLabel act A B₀ ψ (p d) GI hpdI := by
    simpa [GI, hpdI] using
      (labelExtension_centerLabel
        act A B₀ ψ p g I.1
        hsource htarget hcompat
        d hdsrc I.2)
  have hsrc :
      centerLabel act A B₀ ψ d I.1 I.2 =
        (w.valuation.1
          (⟨y, hy⟩ : B₀.closureAtSet w.base)) I :=
    centerLabel_restrictionVertex
      act A B₀ ψ w y hy I.1 I.2
  rw [hsrc] at hcenter
  have hmove :
      centerLabel act A B₀ ψ (p d) GI hpdI =
        centerLabel act A B₀ ψ r GI hrI :=
    centerLabel_congr act A B₀ ψ hpd GI hpdI hrI
  have htgt :
      centerLabel act A B₀ ψ r GI hrI =
        (p w).valuation.1
          (⟨g y, hy'⟩ :
            B₀.closureAtSet (p w).base)
          ⟨GI, hrI⟩ := by
    simpa [r, GI, hrI] using
      (centerLabel_restrictionVertex
        act A B₀ ψ (p w) (g y) hy'
        GI hrI)
  calc
    labelExtension act A B₀ ψ p g I.1
        hsource htarget hcompat
        ((w.valuation.1
          (⟨y, hy⟩ : B₀.closureAtSet w.base)) I) =
      centerLabel act A B₀ ψ (p d) GI hpdI :=
        hcenter
    _ = centerLabel act A B₀ ψ r GI hrI := hmove
    _ =
      (p w).valuation.1
        (⟨g y, hy'⟩ :
          B₀.closureAtSet (p w).base)
        ⟨GI, hrI⟩ := htgt


/-- Equal witness vertices carry the same valuation function over a fixed
base point in their one-point closures. -/
theorem witnessValuationAt_congr
    {u v : WitnessVertex act A B₀ ψ}
    (huv : u = v)
    (z : β)
    (hu : z ∈ B₀.closureAtSet u.base)
    (hv : z ∈ B₀.closureAtSet v.base) :
    u.valuation.1 ⟨z, hu⟩ =
      v.valuation.1 ⟨z, hv⟩ := by
  subst v
  rfl


/-- The transported faithful witness vertex agrees with the prescribed
partial automorphism on its source. -/
theorem WitnessVertex.transport_eq_of_mem_source [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (hw : w ∈ p.source) :
    WitnessVertex.transport act A B₀ ψ
        p g hsource htarget hcompat w =
      p w := by
  generalize hpw : p w = pw
  rcases pw with ⟨b, Vp⟩
  have hbase : g w.base = b := by
    have hb := hcompat.2 w hw
    rw [hpw] at hb
    exact hb
  rw [Sigma.ext_iff]
  refine ⟨hbase, ?_⟩
  cases hbase
  change
    HEq
      (ValuationStructure.transport act A B₀ ψ
        p g hsource htarget hcompat w.valuation)
      Vp
  rw [heq_iff_eq]
  apply Subtype.ext
  funext z
  let e := closureTransportEquiv act B₀ g w.base
  let y := e.symm z
  have hz : e y = z := e.apply_symm_apply z
  rw [← hz]
  change
    valuationAssignmentEquiv act A B₀ ψ
        p g hsource htarget hcompat w.base
        w.valuation.1 (e y) =
      Vp.1 (e y)
  rw [valuationAssignmentEquiv_apply_transport
    act A B₀ ψ p g hsource htarget hcompat
    w.base w.valuation.1 y]
  let hy' :
      g y.1 ∈ B₀.closureAtSet (p w).base := by
    have h :=
      automorphism_maps_closureAtSet act B₀ g y.2
    simpa [hcompat.2 w hw] using h
  have ht :
      valuationFunctionEquiv act A B₀ ψ
          p g hsource htarget hcompat y.1
          (w.valuation.1
            (⟨y.1, y.2⟩ :
              B₀.closureAtSet w.base)) =
        (p w).valuation.1
          (⟨g y.1, hy'⟩ :
            B₀.closureAtSet (p w).base) := by
    simpa [hy'] using
      (valuationFunction_transport_eq_of_mem_source
        act A B₀ ψ p g hsource htarget hcompat
        w hw y.1 y.2)
  have hval :=
    witnessValuationAt_congr
      act A B₀ ψ hpw (g y.1)
      hy' (e y).2
  rw [ht]
  simpa [e, closureTransportEquiv] using hval

/-- The lifted automorphism extends the prescribed partial automorphism along
the identity embedding of the faithful witness. -/
theorem faithfulWitnessAutomorphism_extends [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    Structure.ExtendsAlong act
      (Structure.Embedding.id
        (witnessStructure act A B₀ ψ))
      p
      (faithfulWitnessAutomorphism act A B₀ ψ
        p g hsource htarget hcompat) := by
  constructor
  · change g.lang * (1 : Γ) = (1 : Γ) * p.lang
    simpa [hcompat.1]
  · intro w hw
    rw [faithfulWitnessAutomorphism_apply]
    exact
      WitnessVertex.transport_eq_of_mem_source
        act A B₀ ψ p g hsource htarget hcompat
        w hw

/-- **Lemma `lem:faithful-extension` (extension part).**  Any partial
automorphism with generic source and target whose projection extends to a base
automorphism extends to an automorphism of the faithful witness. -/
theorem faithfulExtension [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    ∃ h : Structure.Automorphism act
        (witnessStructure act A B₀ ψ),
      Structure.ExtendsAlong act
        (Structure.Embedding.id
          (witnessStructure act A B₀ ψ))
        p h :=
  ⟨faithfulWitnessAutomorphism act A B₀ ψ
      p g hsource htarget hcompat,
    faithfulWitnessAutomorphism_extends
      act A B₀ ψ p g hsource htarget hcompat⟩

end Faithful
end AllThoseEPPA
