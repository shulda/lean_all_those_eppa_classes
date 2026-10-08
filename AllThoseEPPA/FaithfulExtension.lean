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

end Faithful
end AllThoseEPPA
