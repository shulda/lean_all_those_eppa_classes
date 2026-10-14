import AllThoseEPPA.Applications.KOrientations.ClosedGraphRootSets
import AllThoseEPPA.Applications.KOrientations.Closures

/-!
# Exact all-arity root-fibre transport on successor-closed pieces

An induced graph isomorphism between successor-closed subsets
preserves the full reachable-root map and the degree-defined root
predicate. Therefore it preserves and reflects *membership* in
every n-ary d-fibre, for any finite arity including the empty case.

No ambient rootedness is assumed. To turn this into a full isomorphism
of set-valued d-substructures, one also needs d-closedness of the
chosen pieces, ensuring all function outputs stay in those pieces.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Equality of the complete ambient root set to a tuple range is
equivalent to equality inside any successor-closed subset containing
the tuple and its centre. -/
private theorem roots_eq_tupleRange_iff_in_closed_subset
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (S : Set V)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    {n : ℕ} (xs : Fin n → S) (z : S) :
    G.roots k z.val = Set.range (fun i => (xs i).val) ↔
      {r : S | r.val ∈ G.roots k z.val} = Set.range xs := by
  constructor
  · intro hr
    ext r
    constructor
    · intro hval
      rw [hr] at hval
      obtain ⟨i, hi⟩ := hval
      exact ⟨i, Subtype.ext hi⟩
    · rintro ⟨i, hi⟩
      rw [hr]
      exact ⟨i, congrArg Subtype.val hi⟩
  · intro hr
    ext w
    constructor
    · intro hw
      have hwS : w ∈ S :=
        reaches_mem_of_successor_closed G S hS hw.2 z.property
      have hwRange : (⟨w, hwS⟩ : S) ∈ Set.range xs := by
        rw [← hr]
        exact hw
      obtain ⟨i, hi⟩ := hwRange
      exact ⟨i, congrArg Subtype.val hi⟩
    · rintro ⟨i, hi⟩
      have hv : xs i ∈ {r : S | r.val ∈ G.roots k z.val} := by
        rw [hr]
        exact ⟨i, rfl⟩
      have hval : (xs i).val ∈ G.roots k z.val := hv
      have hEq : (xs i).val = w := hi
      exact hEq ▸ hval

/-- Any isomorphism of successor-closed pieces preserves and reflects
every fibre F_n between tuples and vertices in those pieces. -/
theorem closedGraph_dFiber_iff
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    {n : ℕ} (xs : Fin n → S) (z : S) :
    z.val ∈ G.dFiber k (fun i => (xs i).val) ↔
      (e z).val ∈ H.dFiber k (fun i => (e (xs i)).val) := by
  let g : S → W := fun r => (e r).val
  have hginj : Function.Injective g := by
    intro r s hrs
    apply e.injective
    exact Subtype.ext hrs
  have hInj :
      Function.Injective (fun i : Fin n => (xs i).val) ↔
        Function.Injective (fun i : Fin n => (e (xs i)).val) := by
    constructor
    · intro hinj i j hij
      have h : xs i = xs j :=
        e.injective (Subtype.ext hij)
      exact hinj (congrArg Subtype.val h)
    · intro hinj i j hij
      exact hinj (congrArg g (Subtype.ext hij))
  have hRoot :
      (∀ i : Fin n, G.IsRoot k (xs i).val) ↔
      (∀ i : Fin n, H.IsRoot k (e (xs i)).val) := by
    constructor
    · intro h i
      exact (closedGraph_isRoot_iff G H k S T hS hT e hEdge
        (xs i)).mp (h i)
    · intro h i
      exact (closedGraph_isRoot_iff G H k S T hS hT e hEdge
        (xs i)).mpr (h i)
  have hRange :
      Set.range (fun i : Fin n => (e (xs i)).val) =
        g '' Set.range xs := by
    change Set.range (g ∘ xs) = g '' Set.range xs
    rw [Set.range_comp]
  have hRootSet :
      G.roots k z.val = Set.range (fun i => (xs i).val) ↔
      H.roots k (e z).val =
        Set.range (fun i => (e (xs i)).val) := by
    have hLocal := roots_eq_tupleRange_iff_in_closed_subset
      G k S hS xs z
    constructor
    · intro hG
      rw [closedGraph_roots_image G H k S T hS hT e hEdge z,
        hRange, hLocal.mp hG]
    · intro hH
      apply hLocal.mpr
      apply (Set.image_injective.mpr hginj)
      calc
        g '' {r : S | r.val ∈ G.roots k z.val} =
            H.roots k (e z).val :=
          (closedGraph_roots_image G H k S T hS hT e hEdge z).symm
        _ = Set.range (fun i => (e (xs i)).val) := hH
        _ = g '' Set.range xs := hRange
  change
    (0 < n ∧ Function.Injective (fun i => (xs i).val) ∧
      (∀ i, G.IsRoot k (xs i).val) ∧
      G.roots k z.val = Set.range (fun i => (xs i).val)) ↔
    (0 < n ∧ Function.Injective (fun i => (e (xs i)).val) ∧
      (∀ i, H.IsRoot k (e (xs i)).val) ∧
      H.roots k (e z).val =
        Set.range (fun i => (e (xs i)).val))
  exact and_congr Iff.rfl
    (and_congr hInj (and_congr hRoot hRootSet))

end AllThoseEPPA.Applications.KOrientations
