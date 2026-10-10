import AllThoseEPPA.TreeLikeAmalgamGeneral

/-!
# Tree amalgamations of actual full copies of A

This is the *literal recursive shape* of Definition
`defn:tree-amalgamation` in the paper. It is stronger than the
previous `ACliqueTree` predicate: a base node is a genuine full
copy of A, and a recursive gluing step attaches **two tree
amalgamations of full A-copies** along a structure D embedded
inside a specified A-copy on each side.

The gluing constructor uses the previously defined concrete
Γ-structure `generalAmalgamStructure` and arbitrary embeddings
with possibly different language permutations. In particular,
an abstract decomposition into proper E-cliques cannot prove
this predicate without the subsequent actual realization
step of Lemma `lem:cuts`.

No theorem here claims `lem:cuts` finished. The next tasks are
to prove the irreducible-substructure extension observation
and realize an `ACliqueTree` inside this construction.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {U : Type v}

/-- A structure built by recursive free gluing of **full copies
of A**, exclusively over interfaces D embedded in A-copies on
both sides. The underlying amalgams are the *concrete* structures
defined in `TreeLikeAmalgamGeneral`, not existential placeholders.

This is the recursive definition preceding Lemma `lem:cuts`
in the manuscript. -/
inductive TreeAmalgamation
    (act : L.Action Γ) (A : Structure L U) :
    {V : Type v} → Structure L V → Prop where
  | copy {V : Type v} (C : Structure L V)
      (f : Structure.Embedding act A C)
      (hf : Function.Surjective f.toFun) :
      TreeAmalgamation act A C
  | glue {I X Y : Type v}
      (C : Structure L I)
      (B₁ : Structure L X) (B₂ : Structure L Y)
      (h₁ : TreeAmalgamation act A B₁)
      (h₂ : TreeAmalgamation act A B₂)
      (δ₁ δ₂ : Structure.Embedding act C A)
      (α₁ : Structure.Embedding act A B₁)
      (α₂ : Structure.Embedding act A B₂) :
      TreeAmalgamation act A
        (generalAmalgamStructure act
          (α₁.comp δ₁) (α₂.comp δ₂))

/-- The distinguished structure itself is a tree amalgamation
consisting of precisely one copy of A. -/
theorem TreeAmalgamation.singleton
    (act : L.Action Γ) (A : Structure L U) :
    TreeAmalgamation act A A :=
  .copy A (Structure.Embedding.id (act := act) A)
    (fun a => ⟨a, rfl⟩)

end TreeLike
end AllThoseEPPA
