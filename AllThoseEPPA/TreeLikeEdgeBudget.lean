import AllThoseEPPA.TreeLikeDescent
import Mathlib.Data.Fintype.Card

/-!
# The directed-edge budget in iterated sparsening

The cycle-sparsening trichotomy counts `Sparsening.EdgePairs`: the
**ordered** E-edge pairs supported by a vertex set. This number is at
most the square of the vertex count, without requiring irreflexivity
or symmetry. Thus `Q = n*n` is a uniform budget for every subset
with at most `n` vertices in the proof of `thm:maintree`.

This supplies the combinatorial bridge between the concrete
trichotomy and `TreeLike.exists_good_sparsening_step`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v

variable {L : Language.{u}} {V : Type v} [Finite V]

/-- Directed E-edges on S inject into the ordered pairs of elements of S. -/
theorem edgePairs_card_le_square
    (B : Structure L V) (E : L.RelSymbol 2) (S : Set V) :
    Nat.card (Sparsening.EdgePairs B E S) ≤ S.ncard * S.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype (Sparsening.EdgePairs B E S) := Fintype.ofFinite _
  let f : Sparsening.EdgePairs B E S → S × S := fun p =>
    (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1⟩)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : S × S => ((z.1 : V), (z.2 : V))) hpq
  have hc : Fintype.card S = S.ncard :=
    (Nat.card_eq_fintype_card (α := S)).symm.trans
      (Nat.card_coe_set_eq S)
  calc
    Nat.card (Sparsening.EdgePairs B E S) =
        Fintype.card (Sparsening.EdgePairs B E S) :=
      Nat.card_eq_fintype_card
    _ ≤ Fintype.card (S × S) :=
      Fintype.card_le_of_injective f hf
    _ = S.ncard * S.ncard := by
      simp only [Fintype.card_prod, hc]

/-- Uniform budget for the directed E-edge count of any set with
at most n vertices. This does not assume that E is a simple graph. -/
theorem edgePairs_card_le_budget
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (n : ℕ) (hS : S.ncard ≤ n) :
    Nat.card (Sparsening.EdgePairs B E S) ≤ n * n := by
  calc
    Nat.card (Sparsening.EdgePairs B E S) ≤ S.ncard * S.ncard :=
      edgePairs_card_le_square B E S
    _ ≤ n * S.ncard := Nat.mul_le_mul_right _ hS
    _ ≤ n * n := Nat.mul_le_mul_left _ hS

end TreeLike
end AllThoseEPPA
