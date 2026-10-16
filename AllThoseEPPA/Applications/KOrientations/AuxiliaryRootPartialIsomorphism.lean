import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootUnaryExactImage
import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRelationTransfer
import AllThoseEPPA.PartialIso

/-!
# The true induced Γ-partial isomorphism on the auxiliary root structure A₁

The original d-closed source/range substructures T,T' of the
source d-trace need not be invariant under a first-stage
graph automorphism g on all of the ambient B₀. It suffices
that g maps their actual underlying V-vertex sets EXACTLY.

The induced root-only Γ-map has group component g itself
(the full, potentially nonfaithful graph automorphism group),
and its actual PartialEquiv carrier is obtained by restricting
g to the d-closed root domains. Crucially, an arbitrary label
R_P or E_P whose centre lies outside the partial domain is
REFLECTED as well as preserved: this follows from full
d-function fibre closure and centre saturation. The only
unary set-valued auxiliary function also obeys *equality*
of transported images, not merely a one-sided inclusion.

This is the actual Structure.PartialIsomorphism API required
to feed the SECOND unrestricted coherent EPPA selector in
the orientation proof. It does not yet assert that every
partial d-isomorphism induces compatible such source data,
nor the final two-stage extension/gluing or coherence.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Full true auxiliary-language Γ-partial isomorphism of the
original root structure between the induced closed root
domains, with the ACTUAL B₀ graph automorphism as language
group component (no symbol-image lift choices).

Both directions of every R_P / E_P symbol and equality of
all unary successor SET-valued outputs are verified. -/
noncomputable def auxiliaryClosedRootPartialIsomorphism
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (hT : (dTraceStructure G k S).IsClosed T)
    (hT' : (dTraceStructure G k S).IsClosed T')
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T') :
    Structure.PartialIsomorphism
      (auxiliaryAction G k)
      (auxiliaryRootStructure G k S)
      (auxiliaryRootStructure G k S) := by
  classical
  let U := auxiliaryClosedRootDomain G k S T
  let U' := auxiliaryClosedRootDomain G k S T'
  let p := auxiliaryClosedRootPartialEquiv G k S T T' g hImage
  have hp (x : RootsIn G k S) (hx : x ∈ U) :
      (p x).val = g.1 x.val :=
    auxiliaryClosedRootPartialEquiv_value G k S T T' g hImage x hx
  refine
    { lang := g
      toPartialEquiv := p
      source_closed := ?_
      target_closed := ?_
      map_rel_iff := ?_
      map_func := ?_ }
  · change (auxiliaryRootStructure G k S).IsClosed U
    exact auxiliaryClosedRootDomain_isClosed G k S T hT
  · change (auxiliaryRootStructure G k S).IsClosed U'
    exact auxiliaryClosedRootDomain_isClosed G k S T' hT'
  · intro n R xs hxs
    let ys : Fin n → RootsIn G k S := p ∘ xs
    have hxU : ∀ i, xs i ∈ U := hxs
    have hxT : ∀ i : Fin n,
        (⟨(xs i).val, (xs i).property.1⟩ : S) ∈ T := hxU
    have hyU : ∀ i, ys i ∈ U' := by
      intro i
      exact p.map_source (hxU i)
    have hyT : ∀ i : Fin n,
        (⟨(ys i).val, (ys i).property.1⟩ : S) ∈ T' := hyU
    have hxy : ∀ i : Fin n,
        (ys i).val = g.1 (xs i).val := by
      intro i
      exact hp (xs i) (hxU i)
    change (auxiliaryRootStructure G k S).rel
        ((auxiliaryAction G k).onRel g R) ys ↔
      (auxiliaryRootStructure G k S).rel R xs
    exact (closed_dTrace_aux_relation_transport_iff
      G k S T T' hT hT' g hImage R xs ys hxT hyT hxy).symm
  · intro n F xs hxs
    cases F with
    | successor =>
        have hx : xs 0 ∈ U := hxs 0
        have hxsEq : xs = (fun _ : Fin 1 => xs 0) := by
          funext i
          have hi : i = 0 := Subsingleton.elim i 0
          subst i
          rfl
        change Structure.imageSet p
          ((auxiliaryRootStructure G k S).func
            AuxiliaryFunc.successor xs) =
          (auxiliaryRootStructure G k S).func
            AuxiliaryFunc.successor (p ∘ xs)
        rw [hxsEq]
        change Structure.imageSet p
          ((auxiliaryRootStructure G k S).func
            AuxiliaryFunc.successor (fun _ : Fin 1 => xs 0)) =
          (auxiliaryRootStructure G k S).func
            AuxiliaryFunc.successor (fun _ : Fin 1 => p (xs 0))
        exact auxiliaryClosedRootPartialEquiv_successor_image_eq
          G k S T T' hT hT' g hImage (xs 0) hx

end AllThoseEPPA.Applications.KOrientations
