import AllThoseEPPA.Examples.Hypergraph3Basic

universe u

/-- No four vertices span all four possible triples.

This set-theoretic formulation says that a four-element vertex set always
has a three-element subset which is not a hyperedge. -/
def Hypergraph3.IsK4Free {V : Type u} (H : Hypergraph3 V) : Prop :=
  ∀ S : Set V, S.ncard = 4 →
    ¬ ∀ T : Set V, T ⊆ S → T.ncard = 3 → H.edge T
