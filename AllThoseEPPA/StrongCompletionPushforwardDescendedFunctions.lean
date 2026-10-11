import AllThoseEPPA.StrongCompletionPushforward
import AllThoseEPPA.Irreducible

/-!
# Exact unary function preservation by descended maps

Let f:A→B be a Γ-homomorphism-embedding, with vertex map
f = g ∘ q for a *surjective* q:V→U. Give U the existential
pushforward structure q₊A. The earlier construction shows
g:q₊A→B is a homomorphism, but it does not automatically
show that g is a homomorphism-embedding.

When **all functions are unary**, however, the *function part*
of the embedding condition for g is actually automatic:
for any output tuple x in U, choose its one original preimage
a∈A. Because Cl_A(a) is irreducible, f preserves the entire
function fibre on a *exactly*, not just by inclusion. Hence
every target B-function value has a witness in q₊A.

This statement does not infer either global or local
injectivity of g and does not assert reflection of arbitrary
relations. Those remain independent mathematical obligations
for Proposition 11.3.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- In the unary-function setting, a descended map from an
existential quotient of a homomorphism-embedding preserves
*all* set-valued function fibres exactly.

This does not require function-fibre congruence of q:
such congruence is instead needed to make the *first*
factor q a homomorphism-embedding. -/
theorem fromPushforward_unary_map_func_exact
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hq : Function.Surjective q)
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → U) :
    imageSet g ((A.pushforwardAlong q).func F xs) =
      B.func (act.onFunc f.lang F) (g ∘ xs) := by
  classical
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  obtain ⟨a, ha⟩ := hq (xs 0)
  let ys : Fin 1 → V := fun _ => a
  have hTuple : q ∘ ys = xs := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact ha
  have hfTuple : f.toFun ∘ ys = g ∘ xs := by
    calc
      f.toFun ∘ ys = (g ∘ q) ∘ ys := by rw [hFactor]
      _ = g ∘ (q ∘ ys) := by funext i; rfl
      _ = g ∘ xs := by rw [hTuple]
  let S : Set V := A.closureAtSet a
  let hS : A.IsClosed S := A.isClosed_closureSet {a}
  have hIrr : (A.induce S hS).IsIrreducible :=
    A.closureAt_isIrreducible a
  have hExact : imageSet f.toFun (A.func F ys) =
      B.func (act.onFunc f.lang F) (g ∘ xs) := by
    have hLocal := (hf S hS hIrr).2.2 F ys
      (by intro i; exact A.mem_closureAtSet a)
    simpa only [hfTuple] using hLocal
  apply Set.Subset.antisymm
  · intro z hz
    exact (fromPushforward act f q g hFactor).map_func F xs hz
  · intro z hz
    rw [← hExact] at hz
    obtain ⟨b, hb, hfb⟩ := hz
    have hqb : q b ∈ (A.pushforwardAlong q).func F xs := by
      exact ⟨ys, hTuple, ⟨b, hb, rfl⟩⟩
    refine ⟨q b, hqb, ?_⟩
    calc
      g (q b) = f b := (congrFun hFactor b).symm
      _ = z := hfb

end Homomorphism
end Structure
end AllThoseEPPA
