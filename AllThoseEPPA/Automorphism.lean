import AllThoseEPPA.EPPA

/-!
# Inverses of total automorphisms

The core EPPA API represents automorphisms by total partial isomorphisms.
This file packages inversion of the underlying partial equivalence together
with inversion of the language component.
-/

namespace AllThoseEPPA
namespace Structure
namespace Automorphism

universe u v w

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}
variable {act : L.Action Γ}
variable {A : Structure L V}

/-- Inverse of a total automorphism. -/
noncomputable def symm (g : Automorphism act A) :
    Automorphism act A where
  toPartialIsomorphism :=
    { lang := g.lang⁻¹
      toPartialEquiv := g.toPartialIsomorphism.toPartialEquiv.symm
      source_closed := g.toPartialIsomorphism.target_closed
      target_closed := g.toPartialIsomorphism.source_closed
      map_rel_iff := by
        intro n R xs hxs
        let ys : Fin n → V :=
          g.toPartialIsomorphism.toPartialEquiv.symm ∘ xs
        have hys :
            ∀ i, ys i ∈ g.toPartialIsomorphism.toPartialEquiv.source := by
          intro i
          exact
            g.toPartialIsomorphism.toPartialEquiv.symm.map_source
              (hxs i)
        have hg :=
          g.toPartialIsomorphism.map_rel_iff
            (act.onRel g.lang⁻¹ R) ys hys
        change
          A.rel
              (act.onRel g.lang
                (act.onRel g.lang⁻¹ R))
              (g.toPartialIsomorphism.toPartialEquiv ∘ ys) ↔
            A.rel (act.onRel g.lang⁻¹ R) ys at hg
        have hsym :
            act.onRel g.lang (act.onRel g.lang⁻¹ R) = R := by
          simp [← Language.Action.onRel_mul]
        have htuple :
            g.toPartialIsomorphism.toPartialEquiv ∘ ys = xs := by
          funext i
          exact
            g.toPartialIsomorphism.toPartialEquiv.right_inv
              (hxs i)
        rw [hsym, htuple] at hg
        exact hg.symm
      map_func := by
        intro n F xs hxs
        let pe := g.toPartialIsomorphism.toPartialEquiv
        let ys : Fin n → V := pe.symm ∘ xs
        have hys : ∀ i, ys i ∈ pe.source := by
          intro i
          exact pe.symm.map_source (hxs i)
        have hg :=
          g.toPartialIsomorphism.map_func
            (act.onFunc g.lang⁻¹ F) ys hys
        change
          Structure.imageSet pe
              (A.func (act.onFunc g.lang⁻¹ F) ys) =
            A.func
              (act.onFunc g.lang
                (act.onFunc g.lang⁻¹ F))
              (pe ∘ ys) at hg
        have hsym :
            act.onFunc g.lang (act.onFunc g.lang⁻¹ F) = F := by
          simp [← Language.Action.onFunc_mul]
        have htuple : pe ∘ ys = xs := by
          funext i
          exact pe.right_inv (hxs i)
        rw [hsym, htuple] at hg
        ext y
        constructor
        · rintro ⟨z, hz, hzy⟩
          have hzimg :
              z ∈ Structure.imageSet pe
                (A.func (act.onFunc g.lang⁻¹ F) ys) := by
            rw [hg]
            exact hz
          rcases hzimg with ⟨t, ht, htz⟩
          have hztarget : z ∈ pe.target := by
            rw [show pe.target = Set.univ by
              simpa [pe, PartialIsomorphism.target] using
                g.target_eq_univ]
            exact Set.mem_univ z
          have hback : pe.symm z = t := by
            rw [← htz]
            exact pe.left_inv
              (by
                rw [show pe.source = Set.univ by
                  simpa [pe, PartialIsomorphism.source] using
                    g.source_eq_univ]
                exact Set.mem_univ t)
          rw [hzy] at hback
          simpa [hback] using ht
        · intro hy
          have hySource : y ∈ pe.source := by
            rw [show pe.source = Set.univ by
              simpa [pe, PartialIsomorphism.source] using
                g.source_eq_univ]
            exact Set.mem_univ y
          have hgy :
              pe y ∈ A.func F xs := by
            rw [← hg]
            exact ⟨y, hy, rfl⟩
          refine ⟨pe y, hgy, ?_⟩
          exact pe.left_inv hySource }
  source_eq_univ := by
    simpa [PartialIsomorphism.source] using g.target_eq_univ
  target_eq_univ := by
    simpa [PartialIsomorphism.target] using g.source_eq_univ

@[simp] theorem symm_lang (g : Automorphism act A) :
    g.symm.lang = g.lang⁻¹ :=
  rfl

@[simp] theorem symm_apply_apply (g : Automorphism act A) (x : V) :
    g.symm (g x) = x := by
  change
    g.toPartialIsomorphism.toPartialEquiv.symm
      (g.toPartialIsomorphism.toPartialEquiv x) = x
  exact
    g.toPartialIsomorphism.toPartialEquiv.left_inv
      (by
        rw [show
          g.toPartialIsomorphism.toPartialEquiv.source = Set.univ by
            simpa [PartialIsomorphism.source] using g.source_eq_univ]
        exact Set.mem_univ x)

@[simp] theorem apply_symm_apply (g : Automorphism act A) (x : V) :
    g (g.symm x) = x := by
  change
    g.toPartialIsomorphism.toPartialEquiv
      (g.toPartialIsomorphism.toPartialEquiv.symm x) = x
  exact
    g.toPartialIsomorphism.toPartialEquiv.right_inv
      (by
        rw [show
          g.toPartialIsomorphism.toPartialEquiv.target = Set.univ by
            simpa [PartialIsomorphism.target] using g.target_eq_univ]
        exact Set.mem_univ x)

end Automorphism
end Structure
end AllThoseEPPA
