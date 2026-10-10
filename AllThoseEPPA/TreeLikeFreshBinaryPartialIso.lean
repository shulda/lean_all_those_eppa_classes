import AllThoseEPPA.TreeLikeFreshBinaryComplete
import AllThoseEPPA.Automorphism

/-!
# Partial isomorphisms and automorphisms of the complete fresh-E expansion

Adding a new fixed binary E with the complete loopless interpretation
does not change any closed subset, partial automorphism, or ordinary
automorphism. Conversely, every partial map in the expanded language
restricts to one in the old language.

These are *actual* Γ-partial isomorphisms, retaining their source and
target PartialEquiv, language group element, reflection of all old
relations, and equality of arbitrary set-valued function fibres.
In particular, injectivity on the source makes the extra E condition
automatic; it does not require a globally defined permutation.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Function-closed sets remain exactly the same when the complete E is
added: the new symbol is relational, and all function fibres are unchanged. -/
theorem isClosed_withCompleteFixedBinary_iff
    (A : Structure L V) (S : Set V) :
    A.withCompleteFixedBinary.IsClosed S ↔ A.IsClosed S :=
  Iff.rfl

/-- Forgetting the new E leaves function-closed sets unchanged. -/
theorem isClosed_forgetFixedBinary_iff
    (B : Structure L.withFixedBinaryRel V) (S : Set V) :
    B.forgetFixedBinary.IsClosed S ↔ B.IsClosed S :=
  Iff.rfl

namespace PartialIsomorphism

/-- Every old-language partial isomorphism extends to the complete fresh-E
expansions without changing its underlying partial equivalence. -/
def withCompleteFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (p : PartialIsomorphism act A B) :
    PartialIsomorphism act.withFixedBinaryRel
      A.withCompleteFixedBinary B.withCompleteFixedBinary where
  lang := p.lang
  toPartialEquiv := p.toPartialEquiv
  source_closed := p.source_closed
  target_closed := p.target_closed
  map_rel_iff := by
    intro n R xs hxs
    cases R with
    | inl r =>
        exact p.map_rel_iff r xs hxs
    | inr e =>
        change Function.Injective (p.toPartialEquiv ∘ xs) ↔
          Function.Injective xs
        constructor
        · intro hinj i j hij
          exact hinj (congrArg p.toPartialEquiv hij)
        · intro hinj i j hij
          apply hinj
          have hback := congrArg p.toPartialEquiv.symm hij
          calc
            xs i = p.toPartialEquiv.symm (p.toPartialEquiv (xs i)) :=
              (p.toPartialEquiv.left_inv (hxs i)).symm
            _ = p.toPartialEquiv.symm (p.toPartialEquiv (xs j)) := hback
            _ = xs j := p.toPartialEquiv.left_inv (hxs j)
  map_func := by
    intro n F xs hxs
    exact p.map_func F xs hxs

/-- Forgetting E converts any expanded Γ-partial isomorphism back to a
genuine Γ-partial isomorphism in the original language. -/
def forgetFixedBinary
    (act : L.Action Γ)
    {A : Structure L.withFixedBinaryRel V}
    {B : Structure L.withFixedBinaryRel W}
    (p : PartialIsomorphism act.withFixedBinaryRel A B) :
    PartialIsomorphism act A.forgetFixedBinary B.forgetFixedBinary where
  lang := p.lang
  toPartialEquiv := p.toPartialEquiv
  source_closed := p.source_closed
  target_closed := p.target_closed
  map_rel_iff := by
    intro n R xs hxs
    exact p.map_rel_iff (.inl R) xs hxs
  map_func := by
    intro n F xs hxs
    exact p.map_func F xs hxs

/-- Adding E and then forgetting it restores the literal partial
isomorphism, including its Γ-language component. -/
@[simp] theorem forget_withCompleteFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (p : PartialIsomorphism act A B) :
    (p.withCompleteFixedBinary act).forgetFixedBinary act = p := by
  cases p
  rfl

/-- On structures that are already complete E expansions, every partial
isomorphism is determined by its old-language reduct. -/
@[simp] theorem withComplete_forgetFixedBinary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (p : PartialIsomorphism act.withFixedBinaryRel
      A.withCompleteFixedBinary B.withCompleteFixedBinary) :
    (p.forgetFixedBinary act).withCompleteFixedBinary act = p := by
  cases p
  rfl

end PartialIsomorphism

namespace Automorphism

/-- Every old-language Γ-automorphism lifts to the complete-E expansion.
It has precisely the same Γ-component and vertex partial equivalence. -/
def withCompleteFixedBinary
    (act : L.Action Γ) {A : Structure L V}
    (g : Automorphism act A) :
    Automorphism act.withFixedBinaryRel A.withCompleteFixedBinary where
  toPartialIsomorphism :=
    g.toPartialIsomorphism.withCompleteFixedBinary act
  source_eq_univ := g.source_eq_univ
  target_eq_univ := g.target_eq_univ

/-- Forget E from a Γ-automorphism of the expanded structure. -/
def forgetFixedBinary
    (act : L.Action Γ)
    {B : Structure L.withFixedBinaryRel V}
    (g : Automorphism act.withFixedBinaryRel B) :
    Automorphism act B.forgetFixedBinary where
  toPartialIsomorphism :=
    g.toPartialIsomorphism.forgetFixedBinary act
  source_eq_univ := g.source_eq_univ
  target_eq_univ := g.target_eq_univ

@[simp] theorem withCompleteFixedBinary_lang
    (act : L.Action Γ) {A : Structure L V}
    (g : Automorphism act A) :
    (g.withCompleteFixedBinary act).lang = g.lang := rfl

@[simp] theorem withCompleteFixedBinary_apply
    (act : L.Action Γ) {A : Structure L V}
    (g : Automorphism act A) (x : V) :
    (g.withCompleteFixedBinary act) x = g x := rfl

@[simp] theorem forget_withCompleteFixedBinary
    (act : L.Action Γ) {A : Structure L V}
    (g : Automorphism act A) :
    (g.withCompleteFixedBinary act).forgetFixedBinary act = g := by
  apply ext_of_lang_apply
  · rfl
  · intro x
    rfl

/-- Complete-E expansion preserves composition of genuine Γ-automorphisms. -/
theorem withCompleteFixedBinary_comp
    (act : L.Action Γ) {A : Structure L V}
    (g f : Automorphism act A) :
    (g.comp f).withCompleteFixedBinary act =
      (g.withCompleteFixedBinary act).comp
        (f.withCompleteFixedBinary act) := by
  apply ext_of_lang_apply
  · rfl
  · intro x
    rfl

end Automorphism
end Structure
end AllThoseEPPA
