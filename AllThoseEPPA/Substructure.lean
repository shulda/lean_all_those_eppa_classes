import AllThoseEPPA.Map

/-!
# Substructures

For set-valued functions, an induced structure exists on a subset only when
the subset is closed under every function value.  This is the paper's notion
of substructure.
-/

namespace AllThoseEPPA

universe u v w

namespace Structure

variable {L : Language.{u}} {Γ : Type v} [Group Γ] {V : Type w}

/-- A subset is closed under all set-valued functions of a structure. -/
def IsClosed (A : Structure L V) (S : Set V) : Prop :=
  ∀ {n : ℕ} (F : L.FuncSymbol n) (x : Fin n → V),
    (∀ i, x i ∈ S) → A.func F x ⊆ S

/-- The structure induced on a closed subset. -/
def induce (A : Structure L V) (S : Set V) (hS : A.IsClosed S) :
    Structure L S where
  rel R x := A.rel R (Subtype.val ∘ x)
  func F x := {y | y.1 ∈ A.func F (Subtype.val ∘ x)}

/-- Inclusion of a closed induced substructure. -/
def inclusion (act : L.Action Γ) (A : Structure L V)
    (S : Set V) (hS : A.IsClosed S) :
    Embedding act (A.induce S hS) A where
  lang := 1
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := by
    intro n R x
    simp [induce]
  map_func := by
    intro n F x
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [induce] using hz
    · intro hy
      have hy' : y ∈ A.func F (Subtype.val ∘ x) := by
        simpa using hy
      have hyS : y ∈ S :=
        hS F (Subtype.val ∘ x) (fun i => (x i).2) hy'
      exact ⟨⟨y, hyS⟩, hy', rfl⟩

/-- The whole vertex set is closed. -/
theorem isClosed_univ (A : Structure L V) : A.IsClosed Set.univ := by
  intro n F x hx
  exact Set.subset_univ _

end Structure
end AllThoseEPPA
