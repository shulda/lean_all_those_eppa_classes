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
            ∀ i, ys i ∈ g.toPartialIsomorphism.source := by
          intro i
          change
            g.toPartialIsomorphism.toPartialEquiv.symm (xs i) ∈
              g.toPartialIsomorphism.toPartialEquiv.source
          exact
            g.toPartialIsomorphism.toPartialEquiv.symm.map_source
              (hxs i)
        have hg :=
          g.toPartialIsomorphism.map_rel_iff
            (act.onRel g.lang⁻¹ R) ys hys
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
        let ys : Fin n → V :=
          g.toPartialIsomorphism.toPartialEquiv.symm ∘ xs
        have hys :
            ∀ i, ys i ∈ g.toPartialIsomorphism.source := by
          intro i
          change
            g.toPartialIsomorphism.toPartialEquiv.symm (xs i) ∈
              g.toPartialIsomorphism.toPartialEquiv.source
          exact
            g.toPartialIsomorphism.toPartialEquiv.symm.map_source
              (hxs i)
        have hg :=
          g.toPartialIsomorphism.map_func
            (act.onFunc g.lang⁻¹ F) ys hys
        have hsym :
            act.onFunc g.lang (act.onFunc g.lang⁻¹ F) = F := by
          simp [← Language.Action.onFunc_mul]
        have htuple :
            g.toPartialIsomorphism.toPartialEquiv ∘ ys = xs := by
          funext i
          exact
            g.toPartialIsomorphism.toPartialEquiv.right_inv
              (hxs i)
        rw [hsym, htuple] at hg
        ext y
        constructor
        · rintro ⟨z, hz, hzy⟩
          have hzTarget :
              z ∈ g.toPartialIsomorphism.target := by
            rw [g.target_eq_univ]
            exact Set.mem_univ z
          have hgz :
              g.toPartialIsomorphism.toPartialEquiv
                  (g.toPartialIsomorphism.toPartialEquiv.symm z) = z :=
            g.toPartialIsomorphism.toPartialEquiv.right_inv hzTarget
          have hpre :
              g.toPartialIsomorphism.toPartialEquiv.symm z ∈
                A.func (act.onFunc g.lang⁻¹ F) ys := by
            rw [← hg]
            exact
              ⟨g.toPartialIsomorphism.toPartialEquiv.symm z,
                hz, hgz⟩
          exact hpre
        · intro hy
          have hyImg :
              g.toPartialIsomorphism.toPartialEquiv y ∈
                Structure.imageSet
                  g.toPartialIsomorphism.toPartialEquiv
                  (A.func (act.onFunc g.lang⁻¹ F) ys) :=
            ⟨y, hy, rfl⟩
          rw [hg] at hyImg
          have hgyTarget :
              g.toPartialIsomorphism.toPartialEquiv y ∈
                g.toPartialIsomorphism.target :=
            g.toPartialIsomorphism.map_source
              (by
                rw [g.source_eq_univ]
                exact Set.mem_univ y)
          refine
            ⟨g.toPartialIsomorphism.toPartialEquiv y, hyImg, ?_⟩
          exact
            g.toPartialIsomorphism.toPartialEquiv.left_inv
              (by
                rw [g.source_eq_univ]
                exact Set.mem_univ y) }
  source_eq_univ := g.target_eq_univ
  target_eq_univ := g.source_eq_univ

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
        rw [g.source_eq_univ]
        exact Set.mem_univ x)

@[simp] theorem apply_symm_apply (g : Automorphism act A) (x : V) :
    g (g.symm x) = x := by
  change
    g.toPartialIsomorphism.toPartialEquiv
      (g.toPartialIsomorphism.toPartialEquiv.symm x) = x
  exact
    g.toPartialIsomorphism.toPartialEquiv.right_inv
      (by
        rw [g.target_eq_univ]
        exact Set.mem_univ x)

end Automorphism
end Structure
end AllThoseEPPA
