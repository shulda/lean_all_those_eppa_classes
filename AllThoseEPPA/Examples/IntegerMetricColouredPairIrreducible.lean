import AllThoseEPPA.Examples.IntegerMetricBridge
import AllThoseEPPA.Irreducible
import Mathlib.Tactic.FinCases

/-!
# Every already-coloured pair is irreducible

This is the exact structural reason that ordinary
homomorphism-embeddings give **relation reflection** on a
pair supporting a positive distance edge. In a relational
language with no functions, every two-point set is closed.
If either orientation of that pair carries a relation,
its induced two-point substructure is irreducible.

The proof works equally for loops (a singleton) and for
different endpoints. Neither metric consistency nor a
global embedding is assumed. This will be combined with
local metric completions to derive symmetry, irreflexivity,
and unique labels of a partial distance-colour structure.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Any vertex subset is function-closed in the pure
distance-colour language. -/
theorem pair_isClosed {D : ℕ} {V : Type u}
    (B : Structure (language D) V) (x y : V) :
    B.IsClosed ({x, y} : Set V) := by
  intro n F xs hxs
  exact F.elim

/-- If every vertex is one of two given points and a
binary relation connects those two points, neither side
of a proper free decomposition can contain the relation:
the entire structure is irreducible. -/
private theorem irreducible_of_binary_relation_cover
    {D : ℕ} {W : Type u}
    (A : Structure (language D) W)
    (a b : W)
    (hCover : ∀ w : W, w = a ∨ w = b)
    (d : Fin D)
    (hRel : A.rel (RelSymbol.edge d) ![a, b]) :
    A.IsIrreducible := by
  constructor
  intro dec
  rcases dec.rel_local (RelSymbol.edge d) ![a, b] hRel with
    hLeft | hRight
  · apply dec.left_proper
    apply Set.eq_univ_of_forall
    intro z
    rcases hCover z with h | h
    · subst z
      exact hLeft 0
    · subst z
      exact hLeft 1
  · apply dec.right_proper
    apply Set.eq_univ_of_forall
    intro z
    rcases hCover z with h | h
    · subst z
      exact hRight 0
    · subst z
      exact hRight 1

/-- The induced substructure on an old coloured pair is
irreducible, even when the only colour is in the reversed
orientation. No triangle inequalities or consistency of
the original edge labels are assumed. -/
theorem colouredPair_isIrreducible
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (x y : V)
    (hLabel :
      ∃ d : Fin D,
        B.rel (RelSymbol.edge d) ![x, y] ∨
        B.rel (RelSymbol.edge d) ![y, x]) :
    (B.induce ({x, y} : Set V) (pair_isClosed B x y)).IsIrreducible := by
  let S : Set V := {x, y}
  let hS : B.IsClosed S := pair_isClosed B x y
  change (B.induce S hS).IsIrreducible
  have hx : x ∈ S := by simp [S]
  have hy : y ∈ S := by simp [S]
  let X : S := ⟨x, hx⟩
  let Y : S := ⟨y, hy⟩
  have hCover : ∀ z : S, z = X ∨ z = Y := by
    intro z
    have hz : z.1 = x ∨ z.1 = y := by
      simpa only [S, Set.mem_insert_iff,
        Set.mem_singleton_iff] using z.2
    rcases hz with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rcases hLabel with ⟨d, hd | hd⟩
  · apply irreducible_of_binary_relation_cover
      (B.induce S hS) X Y hCover d
    change B.rel (RelSymbol.edge d)
      (Subtype.val ∘ ![X, Y])
    have hTuple :
        (Subtype.val ∘ ![X, Y]) = (![x, y] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rw [hTuple]
    exact hd
  · have hCoverReverse : ∀ z : S, z = Y ∨ z = X := by
      intro z
      rcases hCover z with h | h
      · exact Or.inr h
      · exact Or.inl h
    apply irreducible_of_binary_relation_cover
      (B.induce S hS) Y X hCoverReverse d
    change B.rel (RelSymbol.edge d)
      (Subtype.val ∘ ![Y, X])
    have hTuple :
        (Subtype.val ∘ ![Y, X]) = (![y, x] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rw [hTuple]
    exact hd

end Bridge
end IntegerMetric
end AllThoseEPPA
