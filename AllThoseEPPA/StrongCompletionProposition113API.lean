import AllThoseEPPA.StrongCompletionProposition113

/-!
# Close the named Proposition 11.3 strong-completion upgrade API

The earlier class interface `CanUpgradeCompletions` recorded
the difficult direction of Proposition 11.3 as an **open**
proposition without assuming it.

The independent kernel-defect induction now supplies precisely
this property for *every* hereditary finite strong-amalgamation
class in a set-valued unary-function Γ-language.

No type of completions involving automorphism lifts is claimed:
the conclusion is the genuinely injective Γ-homomorphism-
embedding completion of the original manuscript.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- The earlier named open property `CanUpgradeCompletions` is
now obtained by the fully constructive kernel-defect induction,
with no additional class assumptions. -/
theorem HereditaryFiniteStrongAmalgamationClass.canUpgradeCompletions
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act) :
    K.CanUpgradeCompletions := by
  intro V hV A hComp
  exact hereditaryStrongAmalgamation_completionsUpgrade
    act K A hComp

/-- A short paper-facing version of manuscript Proposition 11.3
expressed directly through the class's named upgrade predicate. -/
theorem strongCompletion_proposition_11_3
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    {V : Type v} [Finite V] (A : Structure L V) :
    K.toAmalgamationClass.HasCompletion A ↔
      K.toAmalgamationClass.HasStrongCompletion A :=
  K.completion_iff_strongCompletion_of_upgrade
    (K.canUpgradeCompletions act) A

end TreeLike
end AllThoseEPPA
