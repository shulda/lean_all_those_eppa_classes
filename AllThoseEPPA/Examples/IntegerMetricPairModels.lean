import AllThoseEPPA.Examples.IntegerMetricPartialCosts

/-!
# Pairwise exact metric models force correct partial distance colours

Before using shortest-path completion, an arbitrary partially
distance-coloured structure must be symmetric, loop-free, and
have at most one colour per ordered pair. These shape axioms are
not free assumptions in the eventual locally finite EPPA theorem:
they follow from metric completability of singletons and pairs.

This module isolates the mathematically precise intermediate
statement. Whenever at least one direction of a pair is coloured,
suppose there is a finite or infinite actual D-metric target and
a map which reflects AND preserves all colours on that pair,
in both orientations. Then the original partial structure has
all three required shape axioms. No global metric embedding or
global injectivity is assumed.

The next bridge will obtain these exact pair models using the
irreducible-pair restriction of the manuscript's
homomorphism-embedding completion interface.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- On each pair containing at least one old distance colour,
there is a genuine metric in which both orientations of that
pair have *exactly* their original colour relations. The
representing map may be arbitrary outside the chosen pair. -/
def HasExactColouredPairModels
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V) : Prop :=
  ∀ x y : V,
    (∃ d : Fin D,
      B.rel (RelSymbol.edge d) ![x, y] ∨
      B.rel (RelSymbol.edge d) ![y, x]) →
    ∃ (W : Type u) (M : BoundedNatMetric D W)
        (f : V → W),
      (∀ d : Fin D,
        B.rel (RelSymbol.edge d) ![x, y] ↔
          M.dist (f x) (f y) = d.val + 1) ∧
      (∀ d : Fin D,
        B.rel (RelSymbol.edge d) ![y, x] ↔
          M.dist (f y) (f x) = d.val + 1)

/-- Exact metric models of every already coloured pair force
the complete set of shape conditions for the canonical
partial-cost construction. This includes the empty-language
case D=0, for which the conclusion is vacuous. -/
theorem isConsistentPartialMetric_of_exactPairModels
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hModels : HasExactColouredPairModels B) :
    IsConsistentPartialMetric B := by
  refine ⟨?_, ?_, ?_⟩
  · intro d x hd
    obtain ⟨W, M, f, hForward, _⟩ :=
      hModels x x ⟨d, Or.inl hd⟩
    have hDistance : M.dist (f x) (f x) = d.val + 1 :=
      (hForward d).mp hd
    rw [M.dist_self] at hDistance
    omega
  · intro d x y hd
    obtain ⟨W, M, f, hForward, hReverse⟩ :=
      hModels x y ⟨d, Or.inl hd⟩
    have hDistance :
        M.dist (f x) (f y) = d.val + 1 :=
      (hForward d).mp hd
    have hBack :
        M.dist (f y) (f x) = d.val + 1 := by
      calc
        M.dist (f y) (f x) =
          M.dist (f x) (f y) := M.dist_symm _ _
        _ = d.val + 1 := hDistance
    exact (hReverse d).mpr hBack
  · intro d e x y hd he
    obtain ⟨W, M, f, hForward, _⟩ :=
      hModels x y ⟨d, Or.inl hd⟩
    have hD :
        M.dist (f x) (f y) = d.val + 1 :=
      (hForward d).mp hd
    have hE :
        M.dist (f x) (f y) = e.val + 1 :=
      (hForward e).mp he
    apply Fin.ext
    omega

end Bridge
end IntegerMetric
end AllThoseEPPA
