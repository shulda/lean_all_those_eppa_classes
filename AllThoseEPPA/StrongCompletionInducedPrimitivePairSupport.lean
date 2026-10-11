import AllThoseEPPA.StrongCompletionPrimitivePairWitness

/-!
# Primitive witnesses inside closed induced irreducibles

The primitive-pair theorem for a whole irreducible structure
is most useful when applied to a closed irreducible subset
S of a larger structure A.

We prove that closures computed inside the induced structure
A|S map into ambient A-closures. Therefore every pair of
vertices of a closed irreducible S is jointly generated,
in the AMBIENT structure A, by either one vertex of S or
one realized relation tuple with all inputs in S.

This bridge allows checking injectivity on all irreducible
substructures from injectivity on images of individual
one-point and relation-tuple closures.
-/

namespace AllThoseEPPA
namespace Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The vertex-set inclusion maps generated closures
in an induced substructure into ambient generated closures
of the same generators. Neither unarity nor irreducibility
is needed for this fundamental inclusion. -/
theorem induce_closureSet_to_ambient
    (A : Structure L V)
    (S : Set V) (hS : A.IsClosed S)
    (T : Set S)
    (z : S)
    (hz : (A.induce S hS).closureSet T z) :
    (z : V) ∈ A.closureSet (Subtype.val '' T) := by
  let U : Set S :=
    {t | (t : V) ∈ A.closureSet (Subtype.val '' T)}
  have hU : (A.induce S hS).IsClosed U := by
    intro n F xs hxs y hy
    change (y : V) ∈ A.closureSet (Subtype.val '' T)
    exact (A.isClosed_closureSet (Subtype.val '' T))
      F (Subtype.val ∘ xs) (fun i => hxs i) hy
  have hTU : T ⊆ U := by
    intro x hx
    exact A.subset_closureSet (Subtype.val '' T)
      ⟨x, hx, rfl⟩
  exact (A.induce S hS).closureSet_minimal hU hTU hz

/-- For unary-function structures, any pair of vertices in a
closed irreducible S admits a primitive witness **contained
inside S**. Its generated closure may be computed ambiently. -/
theorem irreducible_induced_primitivePairWitness
    [L.HasUnaryFunctions]
    (A : Structure L V)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (∃ z : V, z ∈ S ∧
      x ∈ A.closureAtSet z ∧
      y ∈ A.closureAtSet z) ∨
    (∃ (n : ℕ) (R : L.RelSymbol n)
        (xs : Fin n → V),
      (∀ i, xs i ∈ S) ∧ A.rel R xs ∧
      x ∈ A.closureSet (Set.range xs) ∧
      y ∈ A.closureSet (Set.range xs)) := by
  let D : Structure L S := A.induce S hS
  let xS : S := ⟨x, hx⟩
  let yS : S := ⟨y, hy⟩
  obtain ⟨z, hxD, hyD⟩ | ⟨n, R, xs, hRel, hxD, hyD⟩ :=
    hIrr.primitivePairWitness D xS yS
  · left
    refine ⟨z.1, z.2, ?_, ?_⟩
    · have h := A.induce_closureSet_to_ambient
        S hS {z} xS hxD
      simpa only [closureAtSet, Set.image_singleton]
        using h
    · have h := A.induce_closureSet_to_ambient
        S hS {z} yS hyD
      simpa only [closureAtSet, Set.image_singleton]
        using h
  · right
    let as : Fin n → V := Subtype.val ∘ xs
    have hRange :
        Subtype.val '' (Set.range xs) = Set.range as := by
      ext z
      constructor
      · rintro ⟨a, ⟨i, hi⟩, hval⟩
        refine ⟨i, ?_⟩
        change (xs i).1 = z
        rw [hi]
        exact hval
      · rintro ⟨i, rfl⟩
        exact ⟨xs i, ⟨i, rfl⟩, rfl⟩
    refine ⟨n, R, as, (fun i => (xs i).2), ?_, ?_, ?_⟩
    · exact hRel
    · have h := A.induce_closureSet_to_ambient
        S hS (Set.range xs) xS hxD
      rw [hRange] at h
      exact h
    · have h := A.induce_closureSet_to_ambient
        S hS (Set.range xs) yS hyD
      rw [hRange] at h
      exact h

end Structure
end AllThoseEPPA
