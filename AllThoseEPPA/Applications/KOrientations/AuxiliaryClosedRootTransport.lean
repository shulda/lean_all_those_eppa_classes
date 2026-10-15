import AllThoseEPPA.Applications.KOrientations.AuxiliaryDomainLabelSaturation
import AllThoseEPPA.Applications.KOrientations.AuxiliaryAction

/-!
# Exact reflection of all R_P-labels on closed root domains

Let a graph automorphism g of the first-stage template map one
d-trace-closed domain T onto another T'. On corresponding tuples
of root vertices, all auxiliary R_P labels are preserved and
reflected, even if P's centre is outside the source structure.
The key is the precise centre-membership characterization.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Membership in two exactly transported source domains is equivalent. -/
private theorem center_mem_image_transport
    {V : Type u} [Fintype V] (G : Digraph V)
    (g : G.graphAut) (U U' : Set V)
    (hImage : g.1 '' U = U') (x : V) :
    x ∈ U ↔ g.1 x ∈ U' := by
  rw [← hImage]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hEq⟩
    have hyx : y = x := g.1.injective hEq
    exact hyx ▸ hy

/-- Positive and negative R_P relations are both reflected, for
all root labels (including those external to the partial domain). -/
theorem closed_dTrace_root_relation_transport_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    (hT' : (dTraceStructure G k S).IsClosed T')
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T')
    {n : ℕ} (P : RootPattern G k n)
    (xs ys : Fin n → RootsIn G k S)
    (hxs : ∀ i, (⟨(xs i).val, (xs i).property.1⟩ : S) ∈ T)
    (hys : ∀ i, (⟨(ys i).val, (ys i).property.1⟩ : S) ∈ T')
    (hxy : ∀ i, (ys i).val = g.1 (xs i).val) :
    (auxiliaryRootStructure G k S).rel (AuxiliaryRel.root P) xs ↔
      (auxiliaryRootStructure G k S).rel
        ((auxiliaryAction G k).onRel g (AuxiliaryRel.root P)) ys := by
  have hc :
      P.center ∈ Subtype.val '' T ↔
        (RootPattern.transportAut g P).center ∈
          Subtype.val '' T' := by
    change P.center ∈ Subtype.val '' T ↔
      g.1 P.center ∈ Subtype.val '' T'
    exact center_mem_image_transport G g _ _ hImage P.center
  have ht :
      (∀ i, (xs i).val = P.tuple i) ↔
      (∀ i, (ys i).val =
        (RootPattern.transportAut g P).tuple i) := by
    constructor
    · intro h i
      change (ys i).val = g.1 (P.tuple i)
      rw [hxy i, h i]
    · intro h i
      apply g.1.injective
      calc
        g.1 (xs i).val = (ys i).val := (hxy i).symm
        _ = g.1 (P.tuple i) := h i
  have hl := closed_dTrace_aux_root_rel_iff
    G k S T hT P xs hxs
  have hr := closed_dTrace_aux_root_rel_iff
    G k S T' hT' (RootPattern.transportAut g P) ys hys
  change (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root P) xs ↔
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root (RootPattern.transportAut g P)) ys
  exact hl.trans ((and_congr hc ht).trans hr.symm)

end AllThoseEPPA.Applications.KOrientations
