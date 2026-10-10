import AllThoseEPPA.TreeLikeIrreducibleEmbeddingImage
import AllThoseEPPA.FaithfulEmbeddingInverse

/-!
# Extending irreducible copies through an embedded side

A key step in the paper's observation about tree amalgamations
is the following transport operation.

Suppose B has the property that every irreducible closed induced
substructure is contained in the image of a full A-copy.
If B embeds exactly into H, and an irreducible substructure
S of H lies in that embedding's image, then the same extension
property provides a full A-copy in H containing S.

The proof uses the already formalized exact inverse of an
embedding on a closed subset, followed by closed-image
irreducibility under Γ-isomorphisms. The final embedding is
the composite of the A-copy in B with the side embedding B→H.
There is no equality-of-language-component assumption.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {U : Type w} {V : Type x} {W : Type y}

/-- An exact formulation of the extension property needed in
Observation `obs:tree-amalgamation_irreducible`:
every irreducible closed induced substructure of H sits in a
full embedded copy of A. -/
def EveryIrreducibleExtendsToA
    (act : L.Action Γ)
    (A : Structure L U) (H : Structure L W) : Prop :=
  ∀ (S : Set W) (hS : H.IsClosed S),
    (H.induce S hS).IsIrreducible →
      ∃ a : Structure.Embedding act A H,
        S ⊆ Set.range a.toFun

/-- Lift the extension property from B to an irreducible
substructure of H lying inside the image of one Γ-embedding
j : B ↪ H.

The source substructure in B is genuinely irreducible:
`embeddingInverseOnClosedSubset` is a structure embedding
and `range_isIrreducible` transports this fact across
its exact induced-range isomorphism. -/
theorem extendIrreducible_throughEmbeddedSide
    (act : L.Action Γ)
    (A : Structure L U)
    (B : Structure L V) (H : Structure L W)
    (j : Structure.Embedding act B H)
    (hExtend : EveryIrreducibleExtendsToA act A B)
    (S : Set W) (hS : H.IsClosed S)
    (hIrr : (H.induce S hS).IsIrreducible)
    (hInside : S ⊆ Set.range j.toFun) :
    ∃ a : Structure.Embedding act A H,
      S ⊆ Set.range a.toFun := by
  classical
  let k : Structure.Embedding act (H.induce S hS) B :=
    Faithful.embeddingInverseOnClosedSubset act j S hS hInside
  let T : Set V := Set.range k.toFun
  let hT : B.IsClosed T := k.range_isClosed act
  have hIrrT : (B.induce T hT).IsIrreducible :=
    k.range_isIrreducible act hIrr
  obtain ⟨α, hα⟩ := hExtend T hT hIrrT
  refine ⟨j.comp α, ?_⟩
  intro z hz
  let sz : S := ⟨z, hz⟩
  have hkT : k sz ∈ T := ⟨sz, rfl⟩
  obtain ⟨a, ha⟩ := hα hkT
  refine ⟨a, ?_⟩
  calc
    (j.comp α) a = j (α a) := rfl
    _ = j (k sz) := congrArg j.toFun ha
    _ = z :=
      Faithful.embeddingInverseOnClosedSubset_apply_spec
        act j S hS hInside sz

end TreeLike
end AllThoseEPPA
