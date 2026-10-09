import AllThoseEPPA.CycleSparseningExtraEdge
import Mathlib.Data.Fintype.Card

/-!
# Strict edge-count increase on an injectively projected bad cycle

This is the finite-cardinality form of the extra-edge obstruction.
The sets of directed E-edges are represented as subtypes of ordered
vertex pairs, so an injective projection yields an injective edge map.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- All directed E-edges whose endpoints lie in a given vertex set. -/
abbrev EdgePairs {W : Type*}
    (D : Structure L W) (F : L.RelSymbol 2) (S : Set W) :=
  {p : W × W // p.1 ∈ S ∧ p.2 ∈ S ∧ D.Edge F p.1 p.2}

/-- The projection maps an E-edge in the sparsening witness to an E-edge
between its base vertices. -/
noncomputable def projectedEdgeMap
    (S : Set (WitnessVertex B₀ E)) :
    EdgePairs (witnessStructure B₀ E) E S →
    EdgePairs B₀ E (Set.image (fun w => w.base B₀ E) S) := by
  intro q
  rcases q with ⟨⟨x,y⟩,hx,hy,hxy⟩
  exact ⟨(x.base B₀ E, y.base B₀ E),
    ⟨x,hx,rfl⟩, ⟨y,hy,rfl⟩, hxy.1⟩

/-- On a subset on which the vertex projection is injective, the map on
ordered edges is injective as well. -/
theorem projectedEdgeMap_injective
    (S : Set (WitnessVertex B₀ E))
    (hinj : Set.InjOn (fun w => w.base B₀ E) S) :
    Function.Injective (projectedEdgeMap B₀ E S) := by
  intro a b hab
  rcases a with ⟨⟨x,y⟩,hx,hy,hxy⟩
  rcases b with ⟨⟨u,v⟩,hu,hv,huv⟩
  have hp : (x.base B₀ E, y.base B₀ E) =
      (u.base B₀ E, v.base B₀ E) :=
    congrArg Subtype.val hab
  have hxu : x = u := hinj hx hu (congrArg Prod.fst hp)
  have hyv : y = v := hinj hy hv (congrArg Prod.snd hp)
  subst u
  subst v
  rfl

/-- Any additional base edge witnesses the failure of surjectivity of
the map on ordered edge pairs. -/
theorem projectedEdgeMap_not_surjective_of_extra
    (S : Set (WitnessVertex B₀ E))
    (hinj : Set.InjOn (fun w => w.base B₀ E) S)
    (x y : WitnessVertex B₀ E)
    (hx : x ∈ S) (hy : y ∈ S)
    (hbase : B₀.Edge E (x.base B₀ E) (y.base B₀ E))
    (hnot : ¬ (witnessStructure B₀ E).Edge E x y) :
    ¬ Function.Surjective (projectedEdgeMap B₀ E S) := by
  intro hs
  let t : EdgePairs B₀ E
      (Set.image (fun w => w.base B₀ E) S) :=
    ⟨(x.base B₀ E, y.base B₀ E),
      ⟨x,hx,rfl⟩, ⟨y,hy,rfl⟩, hbase⟩
  obtain ⟨a, ha⟩ := hs t
  rcases a with ⟨⟨u,v⟩,hu,hv,huv⟩
  have hp : (u.base B₀ E, v.base B₀ E) =
      (x.base B₀ E, y.base B₀ E) :=
    congrArg Subtype.val ha
  have hux : u = x := hinj hu hx (congrArg Prod.fst hp)
  have hvy : v = y := hinj hv hy (congrArg Prod.snd hp)
  subst u
  subst v
  exact hnot huv

/-- Whenever a bad induced cycle lies inside S and the base projection is
injective on S, the full directed E-edge count of S strictly increases
under projection, not merely the edge count of the cycle itself. -/
theorem bad_cycle_projected_edges_strict [Finite V]
    (S : Set (WitnessVertex B₀ E))
    (c : Structure.BadCycleSequence (witnessStructure B₀ E) E)
    (hsub : c.carrier ⊆ S)
    (hinj : Set.InjOn (fun w => w.base B₀ E) S) :
    Nat.card (EdgePairs (witnessStructure B₀ E) E S) <
      Nat.card (EdgePairs B₀ E
        (Set.image (fun w => w.base B₀ E) S)) := by
  classical
  letI : Finite (WitnessVertex B₀ E) := witnessVertex_finite B₀ E
  letI : Fintype (WitnessVertex B₀ E) := Fintype.ofFinite _
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype (EdgePairs (witnessStructure B₀ E) E S) :=
    Fintype.ofFinite _
  letI : Fintype (EdgePairs B₀ E
      (Set.image (fun w => w.base B₀ E) S)) :=
    Fintype.ofFinite _
  have hcycleInj :
      Set.InjOn (fun w : WitnessVertex B₀ E => w.base B₀ E)
        c.carrier := by
    intro x hx y hy heq
    exact hinj (hsub hx) (hsub hy) heq
  obtain ⟨x,y,hx,hy,hbase,hnot⟩ :=
    extra_projection_edge_of_bad_cycle B₀ E c hcycleInj
  have hcard := Fintype.card_lt_of_injective_not_surjective
    (projectedEdgeMap B₀ E S)
    (projectedEdgeMap_injective B₀ E S hinj)
    (projectedEdgeMap_not_surjective_of_extra
      B₀ E S hinj x y (hsub hx) (hsub hy) hbase hnot)
  simpa only [Nat.card_eq_fintype_card] using hcard

end Sparsening
end AllThoseEPPA
