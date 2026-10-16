import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRootDomains
import Mathlib.Logic.Equiv.Defs

/-!
# Exact induced B₀-automorphism equivalence of closed auxiliary root domains

The original d-trace T,T' need not be globally invariant under a
template B₀ graph automorphism g. Only the exact corresponding
image equality g[val(T)] = val(T') is assumed. At all input ROOTS
belonging to T, the restriction of g is nevertheless a bijection
onto the roots belonging to T', because graph automorphisms
preserve root status and are bijections on the ambient graph.

This constructs a genuine equivalence of the dependent root
subtype carriers, without choosing outside-domain representatives
or falsely assuming g[S]=S. It will feed the generic
PartialEquiv adapter and the exact arity-indexed R_P/E_P
and unary-successor reflection proofs for the induced auxiliary
partial isomorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The root-domain restriction of a whole B₀ graph automorphism:
the genuine V-vertex coordinates are related by y = g x,
even when S itself is not g-invariant. -/
noncomputable def auxiliaryClosedRootDomainEquiv
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S)
    (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T') :
    auxiliaryClosedRootDomain G k S T ≃
      auxiliaryClosedRootDomain G k S T' := by
  classical
  let f :
      auxiliaryClosedRootDomain G k S T →
        auxiliaryClosedRootDomain G k S T' := by
    intro x
    have hxV : x.val.val ∈ Subtype.val '' T :=
      (auxiliaryClosedRootDomain_mem_iff G k S T x.val).mp x.property
    have hyV : g.1 x.val.val ∈ Subtype.val '' T' := by
      rw [← hImage]
      exact ⟨x.val.val, hxV, rfl⟩
    obtain ⟨b, hb, hval⟩ := hyV
    have hInS : g.1 x.val.val ∈ S := by
      exact hval ▸ b.property
    have hRoot : G.IsRoot k (g.1 x.val.val) :=
      (G.graphAut_root_iff k g x.val.val).mpr x.val.property.2
    let y : RootsIn G k S :=
      ⟨g.1 x.val.val, ⟨hInS, hRoot⟩⟩
    have hyT : y ∈ auxiliaryClosedRootDomain G k S T' :=
      (auxiliaryClosedRootDomain_mem_iff G k S T' y).mpr
        ⟨b, hb, hval⟩
    exact ⟨y, hyT⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro x y h
    have hxy : g.1 x.val.val = g.1 y.val.val :=
      congrArg (fun z : auxiliaryClosedRootDomain G k S T' =>
        z.val.val) h
    apply Subtype.ext
    apply Subtype.ext
    exact g.1.injective hxy
  · intro y
    have hyV : y.val.val ∈ Subtype.val '' T' :=
      (auxiliaryClosedRootDomain_mem_iff G k S T' y.val).mp y.property
    have hpreimage : y.val.val ∈ g.1 '' (Subtype.val '' T) := by
      rw [hImage]
      exact hyV
    obtain ⟨v, ⟨a, ha, hva⟩, hgy⟩ := hpreimage
    have hMapped : g.1 a.val = y.val.val := by
      rw [hva]
      exact hgy
    have hRoot : G.IsRoot k a.val := by
      apply (G.graphAut_root_iff k g a.val).mp
      rw [hMapped]
      exact y.val.property.2
    let x : RootsIn G k S :=
      ⟨a.val, ⟨a.property, hRoot⟩⟩
    have hx : x ∈ auxiliaryClosedRootDomain G k S T := by
      change (⟨a.val, a.property⟩ : S) ∈ T
      exact ha
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hMapped

/-- The equivalence sends each source root to its ACTUAL
B₀-automorphism image in the ambient vertex set; only the
root subtype membership proof changes. -/
theorem auxiliaryClosedRootDomainEquiv_value
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (T T' : Set S) (g : G.graphAut)
    (hImage : g.1 '' (Subtype.val '' T) = Subtype.val '' T')
    (x : auxiliaryClosedRootDomain G k S T) :
    (auxiliaryClosedRootDomainEquiv G k S T T' g hImage x).val.val =
      g.1 x.val.val := by
  rfl

end AllThoseEPPA.Applications.KOrientations
