import AllThoseEPPA.CycleSparseningRequiredSwitch

/-!
# Closure and restriction under partial automorphisms of sparsening witnesses

The closure argument is shared with the faithful witness construction.
This file adapts its checked proof while reusing closure transport and
genericity of descendants.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Every one-point closure is generic as a witness-vertex family. -/
theorem closureAtSet_witnessSetGeneric
    (w : WitnessVertex B₀ E) :
    WitnessSetGeneric B₀ E
      ((witnessStructure B₀ E).closureAtSet w) := by
  intro x y u v
  exact points_generic_of_mem_closure_same_ancestor
    B₀ E w x.1 y.1 x.2 y.2 u v

/-- Closedness of a partial automorphism source contains every descendant. -/
theorem partialAutomorphism_closure_subset_source
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    {w : WitnessVertex B₀ E}
    (hw : w ∈ p.source) :
    (witnessStructure B₀ E).closureAtSet w ⊆ p.source := by
  apply
    (witnessStructure B₀ E).closureSet_minimal p.source_closed
  intro x hx
  have hxw : x = w := by simpa using hx
  subst x
  exact hw

/-- A partial automorphism maps each source closure into the image closure. -/
theorem partialAutomorphism_maps_closure
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    {w d : WitnessVertex B₀ E}
    (hw : w ∈ p.source)
    (hd : d ∈ (witnessStructure B₀ E).closureAtSet w) :
    p d ∈ (witnessStructure B₀ E).closureAtSet (p w) := by
  let C := witnessStructure B₀ E
  let T : Set (WitnessVertex B₀ E) :=
    {x | x ∈ p.source ∧ p x ∈ C.closureAtSet (p w)}
  have hTclosed : C.IsClosed T := by
    intro n F xs hxs y hy
    have hxsrc : ∀ i, xs i ∈ p.source :=
      fun i => (hxs i).1
    have hysrc : y ∈ p.source :=
      p.source_closed F xs hxsrc hy
    refine ⟨hysrc, ?_⟩
    have hpy :
        p y ∈ C.func (act.onFunc p.lang F)
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

/-- Any restriction-descendant of a source vertex remains in the source. -/
theorem restrictionVertex_mem_source
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (w : WitnessVertex B₀ E)
    (hw : w ∈ p.source)
    (y : V) (hy : y ∈ B₀.closureAtSet (w.base B₀ E)) :
    restrictionVertex B₀ E w y hy ∈ p.source :=
  partialAutomorphism_closure_subset_source act B₀ E p hw
    (restrictionVertex_mem_closureAtSet B₀ E w y hy)

/-- Base compatibility uniquely identifies the image of any restriction
of a source valuation structure. -/
theorem partialAutomorphism_restrictionVertex
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hcompat : BaseCompatible act B₀ E p g)
    (w : WitnessVertex B₀ E)
    (hw : w ∈ p.source)
    (y : V) (hy : y ∈ B₀.closureAtSet (w.base B₀ E)) :
    let hy' : g y ∈ B₀.closureAtSet ((p w).base B₀ E) := by
      have h := Faithful.automorphism_maps_closureAtSet act B₀ g hy
      simpa [hcompat.2 w hw] using h
    p (restrictionVertex B₀ E w y hy) =
      restrictionVertex B₀ E (p w) (g y) hy' := by
  dsimp
  let d := restrictionVertex B₀ E w y hy
  let hy' : g y ∈ B₀.closureAtSet ((p w).base B₀ E) := by
    have h := Faithful.automorphism_maps_closureAtSet act B₀ g hy
    simpa [hcompat.2 w hw] using h
  let r := restrictionVertex B₀ E (p w) (g y) hy'
  have hdsrc : d ∈ p.source :=
    restrictionVertex_mem_source act B₀ E p w hw y hy
  have hpdcl :
      p d ∈ (witnessStructure B₀ E).closureAtSet (p w) :=
    partialAutomorphism_maps_closure act B₀ E p hw
      (restrictionVertex_mem_closureAtSet B₀ E w y hy)
  have hrcl :
      r ∈ (witnessStructure B₀ E).closureAtSet (p w) :=
    restrictionVertex_mem_closureAtSet B₀ E (p w) (g y) hy'
  have hbase : (p d).base B₀ E = r.base B₀ E := by
    calc
      (p d).base B₀ E = g (d.base B₀ E) :=
        (hcompat.2 d hdsrc).symm
      _ = g y := by rfl
      _ = r.base B₀ E := by rfl
  exact projection_injOn_of_generic B₀ E
    ((witnessStructure B₀ E).closureAtSet (p w))
    (closureAtSet_witnessSetGeneric B₀ E (p w))
    hpdcl hrcl hbase

/-- The centre valuation point of a restriction descendant is exactly
the ancestor's internal valuation point at that base coordinate. -/
theorem centerValuationPoint_restrictionVertex
    (w : WitnessVertex B₀ E)
    (y : V) (hy : y ∈ B₀.closureAtSet (w.base B₀ E)) :
    centerValuationPoint B₀ E (restrictionVertex B₀ E w y hy) =
      w.pointAt B₀ E
        (⟨y, hy⟩ : B₀.closureAtSet (w.base B₀ E)) := by
  change
    valuationPointAt B₀ E
        ((w.valuation B₀ E).restrict B₀ E y hy).1
        (⟨y, B₀.mem_closureAtSet y⟩ : B₀.closureAtSet y) =
      valuationPointAt B₀ E (w.valuation B₀ E).1
        (⟨y, hy⟩ : B₀.closureAtSet (w.base B₀ E))
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  have hz :
      closureInclusion B₀ hy
          (⟨y, B₀.mem_closureAtSet y⟩ : B₀.closureAtSet y) =
        (⟨y, hy⟩ : B₀.closureAtSet (w.base B₀ E)) := by
    apply Subtype.ext
    rfl
  exact congr_arg_heq
    (fun z : B₀.closureAtSet (w.base B₀ E) =>
      (w.valuation B₀ E).1 z) hz

/-- A centre bit at a restriction descendant agrees with the ancestor
valuation assignment at the corresponding closure point. -/
theorem centerBit_restrictionVertex
    (w : WitnessVertex B₀ E)
    (y : V) (hy : y ∈ B₀.closureAtSet (w.base B₀ E))
    (c : Structure.BadCycleSequence B₀ E)
    (hyc : y ∈ c.carrier) :
    centerBit B₀ E (restrictionVertex B₀ E w y hy) c hyc =
      ((w.valuation B₀ E).1
        (⟨y, hy⟩ : B₀.closureAtSet (w.base B₀ E))) ⟨c, hyc⟩ := by
  change
    ((w.valuation B₀ E).1
      (closureInclusion B₀ hy
        (⟨y, B₀.mem_closureAtSet y⟩ : B₀.closureAtSet y)))
      ⟨c, hyc⟩ =
    ((w.valuation B₀ E).1
      (⟨y, hy⟩ : B₀.closureAtSet (w.base B₀ E))) ⟨c, hyc⟩
  rfl

end Sparsening
end AllThoseEPPA
