import AllThoseEPPA.Examples.IntegerMetricAllDMainTheorem

/-!
# Public API: EPPA for finite bounded integer metric spaces

This is the **recommended import for external Lean projects**:

```
import AllThoseEPPA.IntegerMetricEPPA
```

The two public entry points are
* `IntegerMetric.eppaPreservingUnitCliqueNumber D A` (stronger), and
* `IntegerMetric.eppa D A` (ordinary EPPA).

Both take `A : BoundedNatMetric D α` and `[Finite α]`, and provide a
finite bounded metric witness together with an isometric embedding
and extensions of **all** isometries between arbitrary subsets of α.
The stronger result additionally preserves `maximumUnitCliqueSize`.

This API intentionally depends only on the public natural-valued
metric vocabulary in its statements. The long manuscript/relational
proof chain is hidden behind the import. Theorems are existential,
not executable algorithms producing concrete witnesses.
See `INTEGER_METRIC_EPPA_API.md` for an example and Lake setup.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- **Strengthened finite metric EPPA (external-project entry point).**

For every `D : ℕ` (including 0 and 1), any finite genuine metric
`A` with natural distances at most D admits a finite such metric
`B` with an isometric embedding of A. Every isometry between
arbitrary subsets of A extends to a global B-isometry, and the
largest unit-distance clique has exactly the same cardinality.

No auxiliary Γ-action, tree presentation, or internal EPPA
hypothesis appears in the statement. -/
theorem eppaPreservingUnitCliqueNumber
    (D : ℕ) {α : Type u} [Finite α]
    (A : BoundedNatMetric D α) :
    ∃ (β : Type u) (_ : Finite β)
      (B : BoundedNatMetric D β) (ι : α ↪ β),
      (∀ x y : α, B.dist (ι x) (ι y) = A.dist x y) ∧
      (∀ (U V : Set α) (p : U ≃ V),
        (∀ x y : U,
          A.dist x.1 y.1 = A.dist (p x).1 (p y).1) →
        ∃ g : Equiv.Perm β,
          (∀ x y : β, B.dist (g x) (g y) = B.dist x y) ∧
          (∀ x : U, g (ι x.1) = ι (p x).1)) ∧
      maximumUnitCliqueSize B = maximumUnitCliqueSize A := by
  exact (Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique D) A

/-- **Ordinary finite metric EPPA (external-project entry point).**

A finite `D`-bounded integer metric embeds isometrically in a
finite `D`-bounded integer metric in which every partial isometry
of the original space extends to a global isometry.
Use `eppaPreservingUnitCliqueNumber` when clique-number preservation
is needed. -/
theorem eppa
    (D : ℕ) {α : Type u} [Finite α]
    (A : BoundedNatMetric D α) :
    ∃ (β : Type u) (_ : Finite β)
      (B : BoundedNatMetric D β) (ι : α ↪ β),
      (∀ x y : α, B.dist (ι x) (ι y) = A.dist x y) ∧
      (∀ (U V : Set α) (p : U ≃ V),
        (∀ x y : U,
          A.dist x.1 y.1 = A.dist (p x).1 (p y).1) →
        ∃ g : Equiv.Perm β,
          (∀ x y : β, B.dist (g x) (g y) = B.dist x y) ∧
          (∀ x : U, g (ι x.1) = ι (p x).1)) := by
  exact (Bridge.allFiniteBoundedMetricsHaveEPPA D) A

end IntegerMetric
end AllThoseEPPA
