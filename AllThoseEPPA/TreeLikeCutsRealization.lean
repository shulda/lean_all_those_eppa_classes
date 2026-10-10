import AllThoseEPPA.TreeLikeFreeCutPushoutEmbedding
import AllThoseEPPA.TreeLikeTreeIrreducibleExtension
import AllThoseEPPA.TreeLikeACliqueTree
import AllThoseEPPA.TreeLikeEmbeddingFactorComposition
import AllThoseEPPA.TreeLikeLocalGraphAxioms

/-!
# Realize a chordal A-labelled clique tree in a tree of full A-copies

This is the construction at the heart of manuscript Lemma
`lem:cuts`. The earlier `ACliqueTree act A E B` certificate
decomposes B recursively into closed irreducible E-complete
pieces, each with an exact embedding into A. That is not
itself a full tree amalgamation of A-copies.

This file realizes **the entire B** inside a literal
`TreeAmalgamation act A H` by induction on that certificate.

At a free node, the induction hypothesis supplies exact
embeddings of B's induced sides into two full-A tree
amalgamations H₁,H₂. The common closed irreducible base
embeds into Hᵢ with an irreducible induced image. The
previously Lean-checked tree irreducible-extension
observation gives full A-copies αᵢ:A↪Hᵢ containing these
images. Exact Γ-embedding factorization gives maps
δᵢ:S↪A with αᵢ.comp δᵢ **equal to the actual base maps**,
including language components.

The literal recursive `TreeAmalgamation.glue` constructor
then glues H₁,H₂ along those A-contained bases. Finally the
concrete universal-property embedding
`freeCutPushoutEmbedding` sends the *whole* B exactly into
this new tree, with relation reflection and equality of all
set-valued function fibres.

No new axioms, sorry, or abstract postulated amalgams.
The final corollary converts the paper's local embedding +
no-induced-cycle hypotheses into this conclusion, via
the previously checked chordal `ACliqueTree` theorem.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {U : Type v}

/-- **The realisation half of `lem:cuts`.**
Any `ACliqueTree` certificate gives a genuine exact
Γ-embedding of the entire structure into a recursively
constructed tree amalgamation of *full copies of A*.

The type universe of A and the source vertex sets is shared,
as in the actual finite combinatorial application; the
language action can live in another universe. -/
theorem ACliqueTree.realizedInFullATree
    (act : L.Action Γ) (A : Structure L U)
    {V : Type v} {B : Structure L V}
    {E : L.RelSymbol 2}
    (h : ACliqueTree act A E B) :
    ∃ (W : Type v) (H : Structure L W),
      TreeAmalgamation act A H ∧
        Nonempty (Structure.Embedding act B H) := by
  classical
  induction h with
  | complete C hComplete hEmbed =>
      obtain ⟨f⟩ := hEmbed
      exact ⟨U, A, TreeAmalgamation.singleton act A, ⟨f⟩⟩
  | free C d hBase hLeft hRight ihLeft ihRight =>
      obtain ⟨W₁, H₁, hTree₁, ⟨eL⟩⟩ := ihLeft
      obtain ⟨W₂, H₂, hTree₂, ⟨eR⟩⟩ := ihRight
      obtain ⟨hS, hIrr⟩ := hBase
      have hIrrBase : (freeCut_base C d).IsIrreducible := by
        change (C.induce (d.left ∩ d.right) hS).IsIrreducible
        exact hIrr
      let f : Structure.Embedding act (freeCut_base C d) H₁ :=
        freeCutPushoutBaseLeft act C d eL
      let g : Structure.Embedding act (freeCut_base C d) H₂ :=
        freeCutPushoutBaseRight act C d eR
      have hIrrF : (H₁.induce (Set.range f.toFun)
          (f.range_isClosed act)).IsIrreducible :=
        f.range_isIrreducible act hIrrBase
      have hIrrG : (H₂.induce (Set.range g.toFun)
          (g.range_isClosed act)).IsIrreducible :=
        g.range_isIrreducible act hIrrBase
      obtain ⟨α₁, hα₁⟩ :=
        (TreeAmalgamation.everyIrreducibleExtendsToA
          act A hTree₁)
          (Set.range f.toFun) (f.range_isClosed act) hIrrF
      obtain ⟨α₂, hα₂⟩ :=
        (TreeAmalgamation.everyIrreducibleExtendsToA
          act A hTree₂)
          (Set.range g.toFun) (g.range_isClosed act) hIrrG
      have hRange₁ : ∀ s, ∃ a : U, α₁ a = f s := by
        intro s
        exact hα₁ ⟨s, rfl⟩
      have hRange₂ : ∀ s, ∃ a : U, α₂ a = g s := by
        intro s
        exact hα₂ ⟨s, rfl⟩
      let δ₁ : Structure.Embedding act (freeCut_base C d) A :=
        α₁.factorThrough act f hRange₁
      let δ₂ : Structure.Embedding act (freeCut_base C d) A :=
        α₂.factorThrough act g hRange₂
      have hFactor₁ : α₁.comp δ₁ = f :=
        Structure.Embedding.comp_factorThrough act α₁ f hRange₁
      have hFactor₂ : α₂.comp δ₂ = g :=
        Structure.Embedding.comp_factorThrough act α₂ g hRange₂
      have hTree :
          TreeAmalgamation act A
            (freeCutPushoutStructure act C d eL eR) := by
        change TreeAmalgamation act A (generalAmalgamStructure act f g)
        rw [← hFactor₁, ← hFactor₂]
        exact TreeAmalgamation.glue (freeCut_base C d)
          H₁ H₂ hTree₁ hTree₂ δ₁ δ₂ α₁ α₂
      exact ⟨AmalgamCarrier f.toFun g.toFun,
        freeCutPushoutStructure act C d eL eR,
        hTree, ⟨freeCutPushoutEmbedding act C d eL eR⟩⟩

/-- **Manuscript Lemma `lem:cuts` in the unary-function
setting.** If A has complete Γ-fixed E, every irreducible
substructure of a finite B embeds into A, and B has no long
induced E-cycles, then B embeds *exactly* into a tree
amalgamation of full copies of A.

The structure language allows arbitrary relational arities
and genuine set-valued unary functions. No other EPPA
witness hypotheses are assumed. -/
theorem chordal_embedsInFullATree
    [L.HasUnaryFunctions]
    [Finite U]
    {V : Type v} [Finite V]
    (act : L.Action Γ)
    (A : Structure L U) (B : Structure L V)
    (E : L.RelSymbol 2)
    (hFix : act.FixesRel E)
    (hComplete : A.EdgeComplete E)
    (hEvery : EveryIrreducibleEmbedsIn act A B)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False) :
    ∃ (W : Type v) (H : Structure L W),
      TreeAmalgamation act A H ∧
        Nonempty (Structure.Embedding act B H) := by
  exact (chordal_hasACliqueTree_of_everyIrreducibleEmbedsIn
    act A B E hFix hComplete hEvery hNo).realizedInFullATree act A

end TreeLike
end AllThoseEPPA
