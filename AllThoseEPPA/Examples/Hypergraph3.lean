import AllThoseEPPA.Examples.Hypergraph3Faithful

/-!
# Finite 3-uniform hypergraphs have EPPA

The statement is deliberately standalone: it only uses a set of unordered
three-element edges, an induced embedding, a partial bijection preserving
edges, and a permutation extending it. No definitions from AllThoseEPPA
appear in the theorem statement.

This is a regression test for the irreducible-structure faithful EPPA theorem.
-/

universe u

/-- Every finite 3-uniform hypergraph has EPPA. -/
theorem Hypergraph3.eppa
    {α : Type u} [Finite α] (A : Hypergraph3 α) :
    ∃ (β : Type u) (_ : Finite β)
      (B : Hypergraph3 β) (ι : α ↪ β),

      -- A is an induced subhypergraph of B.
      (∀ a b c : α,
        A.edge {a, b, c} ↔
          B.edge {ι a, ι b, ι c}) ∧

      -- Every partial automorphism extends.
      (∀ (U V : Set α) (p : U ≃ V),
        (∀ a b c : U,
          A.edge {a.1, b.1, c.1} ↔
            A.edge {(p a).1, (p b).1, (p c).1}) →

        ∃ g : Equiv.Perm β,
          (∀ x y z : β,
            B.edge {x, y, z} ↔
              B.edge {g x, g y, g z}) ∧
          (∀ a : U,
            g (ι a.1) = ι ((p a).1))
      ) := by
  sorry
