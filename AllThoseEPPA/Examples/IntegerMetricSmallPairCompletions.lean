import AllThoseEPPA.Examples.IntegerMetricHomEmbPairModels
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Genuine small metric completions force pairwise colour consistency

The manuscript's restricted EPPA machinery produces small induced
substructures with ordinary homomorphism-embedding completions.
Those maps need NOT be globally injective, so one cannot merely
assert that the original partial colour structure is a metric.

Here is the precise local-to-global semantic bridge. If every
induced substructure on at most TWO vertices can be
homomorphism-embedded into an actual integer metric, then the
original partial distance-colour structure satisfies exactly
the three shape axioms:

* no positive-colour loops;
* each old directed colour occurs in the reverse direction;
* no distinct colours on the same ordered pair.

The proof uses the checked result #200 that a homomorphism-
embedding into a metric makes the entire induced pair
metrically consistent. No global injectivity, no finite
diameter-specific reasoning, and no metric triangle inequalities
in the initial partial source are assumed.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Every small induced subset has an ordinary
homomorphism-embedding into a true D-bounded integer
metric; no injectivity is required away from irreducible
substructures. The source carrier is finite, so all
its induced subsets are finite. -/
def HasSmallMetricHomEmbCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V) (n : ℕ) : Prop :=
  ∀ (S : Set V), S.ncard ≤ n →
    ∃ (W : Type u) (M : BoundedNatMetric D W)
      (f : Structure.Homomorphism (action D)
        (B.induce S (allSubsetsClosed B S))
        (toStructure M)),
      Structure.Homomorphism.IsHomomorphismEmbedding
        (action D) f

/-- An induced coloured pair on two (possibly equal) points
is metrically consistent whenever all 2-point induced
substructures have metric homomorphism-embedding completions. -/
private theorem inducedPair_isConsistent_of_smallCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V)
    (hSmall : HasSmallMetricHomEmbCompletions B 2)
    (x y : V) :
    IsConsistentPartialMetric
      (B.induce ({x,y} : Set V)
        (allSubsetsClosed B {x,y})) := by
  have hCard : ({x,y} : Set V).ncard ≤ 2 := by
    calc
      ({x,y} : Set V).ncard ≤ ({y} : Set V).ncard + 1 :=
        Set.ncard_insert_le x {y}
      _ = 2 := by simp
  obtain ⟨W, M, f, hf⟩ := hSmall {x,y} hCard
  exact isConsistent_of_metricHomomorphismEmbedding
    (B.induce ({x,y} : Set V)
      (allSubsetsClosed B {x,y})) M f hf

/-- Small ordinary metric completions on all pairs
already force all required shape conditions of the
candidate shortest-path completion. This is the concrete
two-point part of the local finiteness proof. -/
theorem consistent_of_smallPairMetricCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V)
    (hSmall : HasSmallMetricHomEmbCompletions B 2) :
    IsConsistentPartialMetric B := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro d x hd
    let S : Set V := {x,x}
    let X : S := ⟨x, by simp [S]⟩
    have hQ :
        (B.induce S (allSubsetsClosed B S)).rel
          (RelSymbol.edge d) ![X,X] := by
      change B.rel (RelSymbol.edge d)
        (Subtype.val ∘ ![X,X])
      have ht :
          (Subtype.val ∘ (![X,X] : Fin 2 → S)) =
            (![x,x] : Fin 2 → V) := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hd
    exact (inducedPair_isConsistent_of_smallCompletions
      B hSmall x x).no_loops d X hQ
  · intro d x y hd
    let S : Set V := {x,y}
    let X : S := ⟨x, by simp [S]⟩
    let Y : S := ⟨y, by simp [S]⟩
    have hQ :
        (B.induce S (allSubsetsClosed B S)).rel
          (RelSymbol.edge d) ![X,Y] := by
      change B.rel (RelSymbol.edge d)
        (Subtype.val ∘ ![X,Y])
      have ht :
          (Subtype.val ∘ (![X,Y] : Fin 2 → S)) =
            (![x,y] : Fin 2 → V) := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hd
    have hRev :=
      (inducedPair_isConsistent_of_smallCompletions
        B hSmall x y).symmetric d X Y hQ
    change B.rel (RelSymbol.edge d)
      (Subtype.val ∘ ![Y,X]) at hRev
    have ht :
        (Subtype.val ∘ (![Y,X] : Fin 2 → S)) =
          (![y,x] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rw [ht] at hRev
    exact hRev
  · intro d e x y hd he
    let S : Set V := {x,y}
    let X : S := ⟨x, by simp [S]⟩
    let Y : S := ⟨y, by simp [S]⟩
    have hQ (c : Fin D)
        (hc : B.rel (RelSymbol.edge c) ![x,y]) :
        (B.induce S (allSubsetsClosed B S)).rel
          (RelSymbol.edge c) ![X,Y] := by
      change B.rel (RelSymbol.edge c)
        (Subtype.val ∘ ![X,Y])
      have ht :
          (Subtype.val ∘ (![X,Y] : Fin 2 → S)) =
            (![x,y] : Fin 2 → V) := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hc
    exact (inducedPair_isConsistent_of_smallCompletions
      B hSmall x y).unique d e X Y (hQ d hd) (hQ e he)

end Bridge
end IntegerMetric
end AllThoseEPPA
