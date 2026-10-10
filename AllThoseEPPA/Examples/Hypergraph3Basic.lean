import Mathlib.Data.Set.Card

universe u

/-- A 3-uniform hypergraph: edges are unordered sets of exactly three vertices. -/
structure Hypergraph3 (V : Type u) where
  edge : Set V → Prop
  uniform : ∀ e, edge e → e.ncard = 3
