import AllThoseEPPA.Examples.IntegerMetricWalkSupport

/-!
# Local metric certificates exclude shortcuts

This is the central logical implication behind the forthcoming
locally finite metric-completion argument.

A walk whose labelled steps embed (as measured edges) in an arbitrary
integer metric has endpoint distance at most its total weight. In
particular, if its endpoint distance is also preserved, the walk
cannot shorten the prescribed endpoint distance.

Crucially the vertex map need NOT be injective. Ordinary
homomorphism-embeddings, rather than strong completions, will supply
the required local metric certificates.

The final theorem makes the quantifier pattern explicit: for a
specified pair, it suffices to realize each walk on at most D
vertices in *some* metric, preserving just the pair and the
walk's steps. Different walks may use different target metric
spaces. This isolates exactly the bounded-local-completion premise
needed for the checked restricted EPPA machinery.

A later bridge must turn local relational homomorphism-embeddings
into these certificates. The current theorem does not assume this
bridge and does not claim the all-D EPPA theorem.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u v

namespace Walk

/-- Each actual walk edge has its specified integer length
under an arbitrary map to a metric space. No injectivity of
the vertex map is assumed. -/
def EdgesPreserved {D : ℕ} {V : Type u} {W : Type v}
    (C : SymmetricCost D V) (M : NatMetric W) (f : V → W)
    {x y : V} (p : Walk V x y) : Prop :=
  match p with
  | .nil _ => True
  | .step (x := a) (y := b) _ tail =>
      M.dist (f a) (f b) = C.cost a b ∧
        tail.EdgesPreserved C M f

/-- The sum of the lengths of the measured walk edges
bounds the target metric distance between its endpoints,
even when the map identifies some unrelated source points. -/
theorem mapped_distance_le_weight
    {D : ℕ} {V : Type u} {W : Type v}
    (C : SymmetricCost D V) (M : NatMetric W) (f : V → W)
    {x y : V} (p : Walk V x y)
    (hPreserved : p.EdgesPreserved C M f) :
    M.dist (f x) (f y) ≤ p.weight C := by
  induction p with
  | nil a =>
      simpa only [weight] using
        Nat.le_of_eq (M.dist_self (f a))
  | @step a b z h tail ih =>
      obtain ⟨hEdge, hTail⟩ := hPreserved
      have hRemaining := ih hTail
      have hTriangle := M.dist_triangle (f a) (f b) (f z)
      change M.dist (f a) (f z) ≤
        C.cost a b + tail.weight C
      omega

/-- The cost of an explicitly preserved direct edge cannot
exceed the total cost of a walk whose edges are preserved.
The metric certificate does not require an injective map. -/
theorem endpoint_cost_le_weight_of_metric_certificate
    {D : ℕ} {V : Type u} {W : Type v}
    (C : SymmetricCost D V) (M : NatMetric W) (f : V → W)
    {x y : V} (p : Walk V x y)
    (hEndpoint : M.dist (f x) (f y) = C.cost x y)
    (hPreserved : p.EdgesPreserved C M f) :
    C.cost x y ≤ p.weight C := by
  rw [← hEndpoint]
  exact p.mapped_distance_le_weight C M f hPreserved

end Walk

namespace SymmetricCost

variable {D : ℕ} {V : Type u}

/-- If every potential shortcut with support of at most D
vertices can be realized in a genuine metric, preserving
the endpoint cost and all walk-step costs, then shortest-path
completion leaves that specified endpoint distance intact.

The metric target and the vertex map may depend on the walk,
and the vertex map need not be injective. -/
theorem shortest_eq_cost_of_bounded_local_certificates
    (C : SymmetricCost D V) [DecidableEq V]
    (x y : V)
    (hLocal :
      ∀ (p : Walk V x y), p.support.card ≤ D →
        ∃ (W : Type u) (M : NatMetric W) (f : V → W),
          M.dist (f x) (f y) = C.cost x y ∧
            p.EdgesPreserved C M f) :
    C.shortest x y = C.cost x y := by
  apply (C.shortest_eq_cost_iff_no_shortcut x y).2
  intro p
  by_contra hNot
  have hShort : p.weight C < C.cost x y :=
    Nat.lt_of_not_ge hNot
  have hSmall : p.support.card ≤ D :=
    p.support_card_le_diameter_of_shortcut C hShort
  obtain ⟨W, M, f, hEnd, hEdges⟩ := hLocal p hSmall
  have hBound :=
    p.endpoint_cost_le_weight_of_metric_certificate
      C M f hEnd hEdges
  exact (Nat.not_lt.mpr hBound) hShort

end SymmetricCost
end IntegerMetric
end AllThoseEPPA
