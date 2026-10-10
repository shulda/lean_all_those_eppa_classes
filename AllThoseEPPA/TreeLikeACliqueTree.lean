import AllThoseEPPA.TreeLikeCliqueTree
import AllThoseEPPA.TreeLikeInducedEmbeddings
import AllThoseEPPA.TreeLikeEmbeddingCliqueBridge
import AllThoseEPPA.TreeLikeCompleteIrreducible

/-!
# Clique-tree certificates with leaves embedded into A

`CliqueTree E B` is already a checked recursive free-amalgam
certificate: its leaves are E-complete structures and its internal
nodes are genuine proper free decompositions along closed irreducible
substructures.

The paper's `lem:cuts` requires more: a leaf must lie inside a
full copy of the distinguished structure A. Under the paper's local
hypothesis `EveryIrreducibleEmbedsIn act A B`, this can be proved
recursively, since the hypothesis passes to either closed side of
a free decomposition.

An `ACliqueTree` carries an **actual embedding into A at every
leaf**, not merely a cardinality bound or an E-clique certificate.
It remains a certificate for the existing B: construction of a
larger tree amalgamation of full copies of A is a separate step.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w t
variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {α : Type w}

/-- Canonical bijection between a carrier and the full subtype. -/
def carrierEquivUniv (V : Type t) :
    V ≃ (Set.univ : Set V) where
  toFun := fun x => ⟨x, Set.mem_univ x⟩
  invFun := Subtype.val
  left_inv := by intro x; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

/-- The full induced structure is isomorphic to the original
structure, including the interpretation of all set-valued
functions. -/
theorem irreducible_induce_univ
    {V : Type t} (B : Structure L V)
    (hIrr : B.IsIrreducible) :
    (B.induce (Set.univ : Set V) (B.isClosed_univ)).IsIrreducible := by
  exact Structure.irreducible_of_equiv B
    (B.induce (Set.univ : Set V) (B.isClosed_univ))
    (carrierEquivUniv V)
    (by intro n R xs; rfl)
    (by intro n F xs y; rfl)
    hIrr

/-- The canonical isomorphism is exposed as an embedding so that
it can be composed with a chosen embedding of the induced full
substructure into A. -/
noncomputable def embedding_induce_univ
    {V : Type t} (act : L.Action Γ) (B : Structure L V) :
    Structure.Embedding act B
      (B.induce (Set.univ : Set V) (B.isClosed_univ)) :=
  Structure.embeddingOfEquiv act B
    (B.induce (Set.univ : Set V) (B.isClosed_univ))
    (carrierEquivUniv V)
    (by intro n R xs; rfl)
    (by intro n F xs y; rfl)

/-- If all irreducible substructures of B embed into A, so does
B itself whenever B is irreducible. -/
theorem irreducible_embeds_into_A
    {V : Type t}
    (act : L.Action Γ) (A : Structure L α) (B : Structure L V)
    (hEvery : EveryIrreducibleEmbedsIn act A B)
    (hIrr : B.IsIrreducible) :
    Nonempty (Structure.Embedding act B A) := by
  obtain ⟨f⟩ :=
    hEvery (Set.univ : Set V) (B.isClosed_univ)
      (irreducible_induce_univ B hIrr)
  exact ⟨f.comp (embedding_induce_univ act B)⟩

/-- A recursive free decomposition in which **every E-complete leaf
comes with an actual structure embedding into A**.

The internal node carries a genuine `FreeDecomposition`; the
intersection is a closed irreducible substructure, not merely a
set-theoretic or graph-theoretic intersection. -/
inductive ACliqueTree (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2) :
    {V : Type t} → Structure L V → Prop where
  | complete {V : Type t} (B : Structure L V)
      (hComplete : B.EdgeComplete E)
      (hEmbed : Nonempty (Structure.Embedding act B A)) :
      ACliqueTree act A E B
  | free {V : Type t} (B : Structure L V)
      (d : B.FreeDecomposition)
      (hBase : ∃ hS : B.IsClosed (d.left ∩ d.right),
        (B.induce (d.left ∩ d.right) hS).IsIrreducible)
      (hLeft : ACliqueTree act A E (B.induce d.left d.left_closed))
      (hRight : ACliqueTree act A E (B.induce d.right d.right_closed)) :
      ACliqueTree act A E B

/-- Decorate the existing clique-tree certificate with embeddings
of all leaves into A, using heredity at every free-decomposition
node. This induction is on the **actual checked certificate**. -/
theorem CliqueTree.withEmbeddingsIntoA
    {V : Type t} {B : Structure L V}
    {E : L.RelSymbol 2}
    (act : L.Action Γ) (A : Structure L α)
    (hTree : CliqueTree E B) :
    EveryIrreducibleEmbedsIn act A B →
      ACliqueTree act A E B := by
  induction hTree with
  | complete C hComplete =>
      intro hEvery
      exact ACliqueTree.complete C hComplete
        (irreducible_embeds_into_A act A C hEvery
          (edgeComplete_isIrreducible C E hComplete))
  | free C d hBase hLeft hRight ihLeft ihRight =>
      intro hEvery
      exact ACliqueTree.free C d hBase
        (ihLeft (everyIrreducibleEmbedsIn_induced
          act A C hEvery d.left d.left_closed))
        (ihRight (everyIrreducibleEmbedsIn_induced
          act A C hEvery d.right d.right_closed))

/-- Under the actual local hypothesis of `lem:cuts`, a finite
chordal E-structure admits a clique-tree certificate whose leaves
are all explicitly embeddable into A.

This is the **leaf-embedding stage** of `lem:cuts`, rather than
the final construction of the enlarged tree amalgamation of A. -/
theorem chordal_hasACliqueTree
    [L.HasUnaryFunctions]
    {V : Type t} [Finite V]
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L V)
    (E : L.RelSymbol 2)
    (hFix : act.FixesRel E)
    (hComplete : A.EdgeComplete E)
    (hEvery : EveryIrreducibleEmbedsIn act A B)
    (hLoop : B.EdgeLoopless E)
    (hSymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False) :
    ACliqueTree act A E B := by
  exact (chordal_hasCliqueTree B E
      (irreduciblesAreCliques_of_everyIrreducibleEmbedsIn
        act A B E hFix hComplete hEvery)
      hLoop hSymm hNo).withEmbeddingsIntoA act A hEvery

end TreeLike
end AllThoseEPPA
