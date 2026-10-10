import AllThoseEPPA.TreeLikeEmbeddingCliqueBridge
import AllThoseEPPA.FaithfulEmbeddingInverse
import AllThoseEPPA.FaithfulTransport

/-!
# Recovering the full Lemma `lem:cuts` embedding hypothesis from faithfulness

The actual premise of `lem:cuts` is that every irreducible
substructure of B embeds into A. A faithful EPPA witness has the
apparently weaker property that some *automorphism of B* moves
each such substructure into the distinguished copy of A.

This file uses two independently checked, pre-existing facts:
* a total automorphism induces an embedding from a closed induced
  substructure to its image;
* an embedding A ↪ B can be inverted on any closed subset of its
  range, including exact set-valued function interpretations.

Composing these gives the missing embedding into A directly.
No new construction of functions, valuations, or automorphisms
is needed.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type x}

/-- **Faithfulness-to-cuts bridge.**
Every irreducible substructure of an irreducible-structure faithful
witness embeds into A. This is the full first hypothesis of the
paper's Lemma `lem:cuts`, not merely its clique consequence.

The proof reuses the pre-existing `Faithful` transport and inverse
embedding machinery. -/
theorem everyIrreducibleEmbedsIn_of_faithful
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (hFaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    EveryIrreducibleEmbedsIn act A B := by
  intro S hS hIrreducible
  obtain ⟨g, hg⟩ := hFaith S hS hIrreducible
  have hMoved : B.IsClosed (g '' S) :=
    Faithful.automorphism_image_isClosed act B g hS
  have hRange : g '' S ⊆ Set.range ψ := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := hg x hx
    exact ⟨a, ha.symm⟩
  let move : Structure.Embedding act
      (B.induce S hS) (B.induce (g '' S) hMoved) :=
    Faithful.automorphismInducedEmbedding act B g S hS
  let back : Structure.Embedding act
      (B.induce (g '' S) hMoved) A :=
    Faithful.embeddingInverseOnClosedSubset act ψ
      (g '' S) hMoved hRange
  exact ⟨back.comp move⟩

/-- An integration check: the old faithfulness-to-clique bridge
is also recovered through actual induced embeddings into A. -/
theorem irreduciblesAreCliques_of_faithful_via_embeddings
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hComplete : A.EdgeComplete E)
    (hFaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    IrreduciblesAreCliques B E := by
  exact irreduciblesAreCliques_of_everyIrreducibleEmbedsIn
    act A B E hfix hComplete
    (everyIrreducibleEmbedsIn_of_faithful act A B ψ hFaith)

end TreeLike
end AllThoseEPPA
