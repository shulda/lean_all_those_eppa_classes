import AllThoseEPPA.Applications.KOrientations.AuxiliaryDomainLabelSaturation
import AllThoseEPPA.Applications.KOrientations.GraphAutomorphismGroup

/-!
# Actual closed auxiliary root domains inherited from d-closed input pieces

A closed substructure of the source d-trace contains every directed
successor reachable from each of its vertices. Its root intersection
therefore is closed under the sole UNARY set-valued successor symbol
of the auxiliary B₁ root language. This uses the actual exact
set-valued function closure, not an ordinary relational reduct.

The carrier of a root-domain piece is defined by membership of the
corresponding vertex of the source subtype S, not by ambient V
coordinate equality. The induced root-set image is characterized
exactly, allowing a B₀ graph automorphism to transfer full closed
source/range domains even when it does NOT preserve S globally.
No additional finite-label or hidden global-equivalence assumptions
are needed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The roots of the canonical source root sort that belong to a
chosen closed subdomain of the INTRINSIC source d-trace. -/
def auxiliaryClosedRootDomain
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T : Set S) : Set (RootsIn G k S) :=
  {x | (⟨x.val, x.property.1⟩ : S) ∈ T}

/-- This is literal membership in the underlying V-image of T,
retaining the same root carrier, not a subset of all ambient roots. -/
theorem auxiliaryClosedRootDomain_mem_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T : Set S)
    (x : RootsIn G k S) :
    x ∈ auxiliaryClosedRootDomain G k S T ↔
      x.val ∈ Subtype.val '' T := by
  constructor
  · intro hx
    exact ⟨⟨x.val, x.property.1⟩, hx, rfl⟩
  · rintro ⟨a, ha, heq⟩
    have hEq : a = (⟨x.val, x.property.1⟩ : S) :=
      Subtype.ext heq
    exact hEq ▸ ha

/-- The actual auxiliary unary set-valued successor outputs at a
root of a d-closed T all remain in its root domain. This proves
CLOSEDNESS in the public Structure.IsClosed sense. -/
theorem auxiliaryClosedRootDomain_isClosed
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T : Set S)
    (hT : (dTraceStructure G k S).IsClosed T) :
    (auxiliaryRootStructure G k S).IsClosed
      (auxiliaryClosedRootDomain G k S T) := by
  intro n F xs hxs y hy
  cases F with
  | successor =>
      change G.Reaches (xs 0).val y.val at hy
      exact hT DFunctionSymbol.successor
        (fun _ : Fin 1 => (⟨(xs 0).val, (xs 0).property.1⟩ : S))
        (fun _ => hxs 0) hy

/-- A genuine global B₀ graph automorphism maps a root-domain
vertex exactly into another closed root-domain whenever the
underlying d-trace source images correspond. No preservation
of the entire original subset S by g is assumed. -/
theorem auxiliaryClosedRootDomain_transport_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T')
    (x y : RootsIn G k S)
    (hxy : y.val = g.1 x.val) :
    x ∈ auxiliaryClosedRootDomain G k S T ↔
      y ∈ auxiliaryClosedRootDomain G k S T' := by
  rw [auxiliaryClosedRootDomain_mem_iff,
      auxiliaryClosedRootDomain_mem_iff, hxy, ← hImage]
  constructor
  · intro hx
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨a, ha, heq⟩
    have hEq : a = x.val := g.1.injective heq
    exact hEq ▸ ha

end AllThoseEPPA.Applications.KOrientations
