import AllThoseEPPA.Applications.KOrientations.AuxiliaryRootPartialIsomorphism

/-!
# Root Γ-partial isomorphism equivalence depends only on exact mathematical data

A genuine second-stage auxiliary root partial automorphism depends on
two closed intrinsic d-trace domains T,T' of an original first-stage
source S⊆B₀ and the ACTUAL first selected whole graph automorphism
g∈Aut(B₀). Its proofs that the domains are closed and g transports
their entire ambient vertex images are propositions; differing proof
terms MUST NOT affect the induced mathematical partial map.

This lemma proves that exactly equal source/range domain data and
equal group components induce Equivalent Γ-partial isomorphisms,
using the public Mathlib PartialEquiv.EqOnSource rather than
claiming equality of irrelevant total function values outside
the closed source domain. It never assumes g globally preserves S.
All R_P/E_P and set-valued unary fibres are retained by the
actual constructor whose two outputs are compared.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- The second-stage original auxiliary ROOT partial map, built
from actual d-closed domains and an arbitrary whole B₀ graph
automorphism, depends only on its exact source/range sets and
the selected graph group element. In particular, proof choices
for closure and image equality cannot affect the public
PartialIsomorphism.Equivalent class. -/
theorem auxiliaryClosedRootPartialIsomorphism_equivalent_of_equal_data
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V)
    (T₁ T₂ U₁ U₂ : Set S)
    (hT₁ : (dTraceStructure G k S).IsClosed T₁)
    (hT₂ : (dTraceStructure G k S).IsClosed T₂)
    (hU₁ : (dTraceStructure G k S).IsClosed U₁)
    (hU₂ : (dTraceStructure G k S).IsClosed U₂)
    (g h : G.graphAut)
    (hg : g.1 '' (Subtype.val '' T₁) = Subtype.val '' T₂)
    (hh : h.1 '' (Subtype.val '' U₁) = Subtype.val '' U₂)
    (hSource : T₁ = U₁) (hTarget : T₂ = U₂)
    (hGraph : g = h) :
    Structure.PartialIsomorphism.Equivalent
      (auxiliaryClosedRootPartialIsomorphism
        G k S T₁ T₂ hT₁ hT₂ g hg)
      (auxiliaryClosedRootPartialIsomorphism
        G k S U₁ U₂ hU₁ hU₂ h hh) := by
  subst U₁
  subst U₂
  subst h
  exact ⟨rfl, ⟨rfl, fun _ _ => rfl⟩⟩

end AllThoseEPPA.Applications.KOrientations
