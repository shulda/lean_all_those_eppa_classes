import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootDomainEquiv
import AllThoseEPPA.Applications.KOrientations.PartialEquivSubtypeBridge

/-!
# Exact auxiliary unary-function action across a closed root partial equivalence

An actual original d-trace closed partial domain T is successor
closed; its auxiliary ROOT subdomain therefore contains all
root-successor values of its roots. A first-stage automorphism g
mapping the underlying original closed T onto T' induces a
genuine partial equivalence of these ROOT domains, even when
g need not preserve all of S.

This file proves the exact equality of SET-VALUED auxiliary
unary successor fibres under the partial equivalence, not only
a homomorphic subset inclusion. This is the full function
axiom needed for an actual public Structure.PartialIsomorphism
of the auxiliary B₁ root language.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Genuine finite auxiliary root partial equivalence obtained by
restricting one B₀ graph automorphism to the exact original
d-trace-closed source/range root subdomains. -/
noncomputable def auxiliaryClosedRootPartialEquiv
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T') :
    PartialEquiv (RootsIn G k S) (RootsIn G k S) :=
  partialEquivFromSubtypeEquiv
    (auxiliaryClosedRootDomain G k S T)
    (auxiliaryClosedRootDomain G k S T')
    (auxiliaryClosedRootDomainEquiv G k S T T' g hImage)

/-- On its genuine source root domain, the root partial map is
literally the original B₀ graph automorphism's vertex map. -/
theorem auxiliaryClosedRootPartialEquiv_value
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T')
    (x : RootsIn G k S)
    (hx : x ∈ auxiliaryClosedRootDomain G k S T) :
    (auxiliaryClosedRootPartialEquiv G k S T T' g hImage x).val =
      g.1 x.val := by
  let U := auxiliaryClosedRootDomain G k S T
  let U' := auxiliaryClosedRootDomain G k S T'
  let e := auxiliaryClosedRootDomainEquiv G k S T T' g hImage
  change (partialEquivFromSubtypeEquiv U U' e x).val = g.1 x.val
  rw [partialEquivFromSubtypeEquiv_apply U U' e hx]
  exact auxiliaryClosedRootDomainEquiv_value G k S T T' g hImage ⟨x, hx⟩

/-- EXACT transport of the source's one-point root-successor
fibre, including preservation and reflection and all values
of the actual set-valued function. No global S invariance. -/
theorem auxiliaryClosedRootPartialEquiv_successor_image_eq
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    (hT' : (dTraceStructure G k S).IsClosed T')
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T')
    (x : RootsIn G k S)
    (hx : x ∈ auxiliaryClosedRootDomain G k S T) :
    Structure.imageSet
      (auxiliaryClosedRootPartialEquiv G k S T T' g hImage)
      ((auxiliaryRootStructure G k S).func
        AuxiliaryFunc.successor (fun _ : Fin 1 => x)) =
      (auxiliaryRootStructure G k S).func
        AuxiliaryFunc.successor
        (fun _ : Fin 1 =>
          auxiliaryClosedRootPartialEquiv G k S T T' g hImage x) := by
  let U := auxiliaryClosedRootDomain G k S T
  let U' := auxiliaryClosedRootDomain G k S T'
  let e := auxiliaryClosedRootDomainEquiv G k S T T' g hImage
  let p := auxiliaryClosedRootPartialEquiv G k S T T' g hImage
  have hpx : (p x).val = g.1 x.val :=
    auxiliaryClosedRootPartialEquiv_value G k S T T' g hImage x hx
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyU : y ∈ U :=
      auxiliaryClosedRootDomain_isClosed G k S T hT
        AuxiliaryFunc.successor (fun _ : Fin 1 => x)
        (fun _ => hx) hy
    have hpy : (p y).val = g.1 y.val :=
      auxiliaryClosedRootPartialEquiv_value G k S T T' g hImage y hyU
    change G.Reaches (p x).val (p y).val
    rw [hpx, hpy]
    exact (G.reaches_iff_perm g.1 g.2).2 hy
  · intro hz
    have hpIn : p x ∈ U' := p.map_source hx
    have hzU' : z ∈ U' :=
      auxiliaryClosedRootDomain_isClosed G k S T' hT'
        AuxiliaryFunc.successor (fun _ : Fin 1 => p x)
        (fun _ => hpIn) hz
    let y : U := e.symm ⟨z, hzU'⟩
    have hpy : p y.val = z := by
      change partialEquivFromSubtypeEquiv U U' e y.val = z
      rw [partialEquivFromSubtypeEquiv_apply U U' e y.property]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hzU'⟩)
    have hgy : g.1 y.val.val = z.val := by
      calc
        g.1 y.val.val = (e y).val.val :=
          (auxiliaryClosedRootDomainEquiv_value G k S T T' g hImage y).symm
        _ = z.val :=
          congrArg (fun w : U' => w.val.val)
            (e.apply_symm_apply ⟨z, hzU'⟩)
    have hpre : G.Reaches x.val y.val.val := by
      change G.Reaches (p x).val z.val at hz
      rw [hpx, ← hgy] at hz
      exact (G.reaches_iff_perm g.1 g.2).1 hz
    exact ⟨y.val, hpre, hpy⟩

end AllThoseEPPA.Applications.KOrientations
