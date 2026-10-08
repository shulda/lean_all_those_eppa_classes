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
  unfold centerValuationPoint centerPoint
  rw [restrictionVertex_pointAt]
  have hz :
      closureInclusion B₀ hy
          (⟨y, B₀.mem_closureAtSet y⟩ :
            B₀.closureAtSet y) =
        (⟨y, hy⟩ : B₀.closureAtSet w.base) := by
    apply Subtype.ext
    rfl
  rw [hz]

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
  rw [centerValuationPoint_restrictionVertex
    act A B₀ ψ w y hy]
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
  have hpd :=
    partialAutomorphism_restrictionVertex
      act A B₀ ψ p g hcompat w hw y hy
  have hcenter :=
    labelExtension_centerLabel
      act A B₀ ψ p g I.1
      hsource htarget hcompat
      d hdsrc I.2
  have hsrc :
      centerLabel act A B₀ ψ d I.1 I.2 =
        (w.valuation.1
          (⟨y, hy⟩ : B₀.closureAtSet w.base)) I := by
    exact
      centerLabel_restrictionVertex
        act A B₀ ψ w y hy I.1 I.2
  rw [hsrc] at hcenter
  rw [hpd] at hcenter
  have htgt :=
    centerLabel_restrictionVertex
      act A B₀ ψ (p w) (g y)
      (by
        have h :=
          automorphism_maps_closureAtSet act B₀ g hy
        simpa [hcompat.2 w hw] using h)
      (I.1.transport act A B₀ ψ g)
      ⟨y, I.2, rfl⟩
  rw [htgt] at hcenter
  exact hcenter


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
  have hbase :
      g w.base = (p w).base :=
    hcompat.2 w hw
  rw [Sigma.ext_iff]
  refine ⟨hbase, ?_⟩
  cases hbase
  apply heq_of_eq
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
      (p w).valuation.1 (e y)
  rw [valuationAssignmentEquiv_apply_transport
    act A B₀ ψ p g hsource htarget hcompat
    w.base w.valuation.1 y]
  exact
    valuationFunction_transport_eq_of_mem_source
      act A B₀ ψ p g hsource htarget hcompat
      w hw y.1 y.2

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
  · simpa [hcompat.1]
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
