import AllThoseEPPA.CycleSparseningParityEdges
import AllThoseEPPA.FaithfulProjectionImage
import Mathlib.Data.Fintype.Card

/-!
# Projection image and irreducibility of a generic sparsening substructure

The projection-image argument is adapted from the machine-checked
`FaithfulProjectionImage` development.  It will allow the original
irreducible-structure-faithful EPPA witness B₀ to be applied to projections
of irreducible substructures of the sparsening witness.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Image of a witness subset under the projection. -/
def projectionImage
    (S : Set (WitnessVertex B₀ E)) : Set V :=
  (fun w : WitnessVertex B₀ E => w.base B₀ E) '' S

include act

/-- The projection image of a closed witness subset is function-closed in the
base witness. -/
theorem projectionImage_isClosed
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S) :
    B₀.IsClosed (projectionImage B₀ E S) := by
  classical
  intro n F xs hxs y hy
  have hex :
      ∀ i, ∃ w : WitnessVertex B₀ E,
        w ∈ S ∧ w.base B₀ E = xs i := by
    intro i
    simpa [projectionImage] using hxs i
  choose ws hwsS hwsBase using hex
  have htuple :
      (fun i => (ws i).base B₀ E) = xs := by
    funext i
    exact hwsBase i
  have hy' :
      y ∈
        B₀.func F (fun i => (ws i).base B₀ E) := by
    rw [htuple]
    exact hy
  have hproj :=
    projection_map_func_eq act B₀ E F ws
  have hproj' :
      Structure.imageSet
          (fun w : WitnessVertex B₀ E => w.base B₀ E)
          ((witnessStructure B₀ E).func F ws) =
        B₀.func F (fun i => (ws i).base B₀ E) := by
    simpa [projection, Function.comp_def] using hproj
  rw [← hproj'] at hy'
  rcases hy' with ⟨z, hz, hzy⟩
  have hzS : z ∈ S :=
    hS F ws hwsS hz
  refine ⟨z, hzS, ?_⟩
  exact hzy

/-- On a generic closed subset, projection induces a surjective embedding
onto its image. -/
noncomputable def projectionInducedEmbedding
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S) :
    Structure.Embedding act
      ((witnessStructure B₀ E).induce S hS)
      (B₀.induce (projectionImage B₀ E S)
        (projectionImage_isClosed act B₀ E S hS)) where
  lang := 1
  toFun := fun w =>
    ⟨w.1.base B₀ E, ⟨w.1, w.2, rfl⟩⟩
  injective := by
    intro x y hxy
    apply Subtype.ext
    apply projection_injOn_of_generic B₀ E S hgen
      x.2 y.2
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro n R xs
    have hEmb :=
      projection_isEmbeddingOn_of_generic
        act B₀ E S hgen
    have hrel :=
      hEmb.2.1 R (fun i => (xs i).1)
        (fun i => (xs i).2)
    have hrel' :
        B₀.rel R (fun i => (xs i).1.base B₀ E) ↔
          (witnessStructure B₀ E).rel R
            (fun i => (xs i).1) := by
      simpa [projection, Function.comp_def] using hrel
    simpa [Structure.induce, Function.comp_def] using hrel'
  map_func := by
    intro n F xs
    have hEmb :=
      projection_isEmbeddingOn_of_generic
        act B₀ E S hgen
    have hfun :=
      hEmb.2.2 F (fun i => (xs i).1)
        (fun i => (xs i).2)
    have hfun' :
        Structure.imageSet
            (fun w : WitnessVertex B₀ E => w.base B₀ E)
            ((witnessStructure B₀ E).func F
              (fun i => (xs i).1)) =
          B₀.func F (fun i => (xs i).1.base B₀ E) := by
      simpa [projection, Function.comp_def] using hfun
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzB :
          z.1 ∈
            (witnessStructure B₀ E).func F
              (fun i => (xs i).1) := by
        exact hz
      have himg :
          z.1.base B₀ E ∈
            Structure.imageSet
              (fun w : WitnessVertex B₀ E => w.base B₀ E)
              ((witnessStructure B₀ E).func F
                (fun i => (xs i).1)) :=
        ⟨z.1, hzB, rfl⟩
      rw [hfun'] at himg
      simpa [Structure.induce, Function.comp_def] using himg
    · intro hy
      have hy' :
          y.1 ∈ B₀.func F
            (fun i => (xs i).1.base B₀ E) := by
        simpa [Structure.induce, Function.comp_def] using hy
      rw [← hfun'] at hy'
      rcases hy' with ⟨z, hz, hzy⟩
      have hzS : z ∈ S :=
        hS F (fun i => (xs i).1)
          (fun i => (xs i).2) hz
      refine ⟨⟨z, hzS⟩, ?_, ?_⟩
      · exact hz
      · apply Subtype.ext
        exact hzy

theorem projectionInducedEmbedding_surjective
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hgen : WitnessSetGeneric B₀ E S) :
    Function.Surjective
      (projectionInducedEmbedding act B₀ E S hS hgen) := by
  intro y
  rcases y.2 with ⟨w, hw, hwy⟩
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  exact hwy

/-- The projection image of an irreducible witness substructure is
irreducible in the base witness. -/

theorem projectionImage_isIrreducible
    (S : Set (WitnessVertex B₀ E))
    (hS : (witnessStructure B₀ E).IsClosed S)
    (hirr :
      ((witnessStructure B₀ E).induce S hS).IsIrreducible) :
    (B₀.induce (projectionImage B₀ E S)
      (projectionImage_isClosed act B₀ E S hS)).IsIrreducible := by
  let hgen :=
    irreducible_witnessSetGeneric B₀ E S hS hirr
  exact
    Faithful.irreducible_target_of_surjective_embedding act
      (projectionInducedEmbedding act B₀ E S hS hgen)
      (projectionInducedEmbedding_surjective
        act B₀ E S hS hgen)
      hirr


end Sparsening
end AllThoseEPPA
