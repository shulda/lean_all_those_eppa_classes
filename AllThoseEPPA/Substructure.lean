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

/-- The closure of a set: the intersection of all closed sets containing it. -/
def closureSet (A : Structure L V) (S : Set V) : Set V :=
  {x | ∀ T : Set V, A.IsClosed T → S ⊆ T → x ∈ T}

/-- Every set is contained in its closure. -/
theorem subset_closureSet (A : Structure L V) (S : Set V) :
    S ⊆ A.closureSet S := by
  intro x hx T hT hST
  exact hST hx

/-- The closure is itself closed. -/
theorem isClosed_closureSet (A : Structure L V) (S : Set V) :
    A.IsClosed (A.closureSet S) := by
  intro n F xs hxs y hy T hT hST
  apply hT F xs
  · intro i
    exact hxs i T hT hST
  · exact hy

/-- The closure is the least closed set containing the given set. -/
theorem closureSet_minimal (A : Structure L V) {S T : Set V}
    (hT : A.IsClosed T) (hST : S ⊆ T) :
    A.closureSet S ⊆ T := by
  intro x hx
  exact hx T hT hST

/-- Closure is monotone. -/
theorem closureSet_mono (A : Structure L V) {S T : Set V}
    (hST : S ⊆ T) :
    A.closureSet S ⊆ A.closureSet T := by
  apply A.closureSet_minimal (A.isClosed_closureSet T)
  exact hST.trans (A.subset_closureSet T)

/-- A closed set is equal to its closure. -/
theorem closureSet_eq_self (A : Structure L V) {S : Set V}
    (hS : A.IsClosed S) :
    A.closureSet S = S := by
  apply Set.Subset.antisymm
  · exact A.closureSet_minimal hS Set.Subset.rfl
  · exact A.subset_closureSet S

/-- Closure of a single vertex, as a subset of the ambient structure. -/
def closureAtSet (A : Structure L V) (x : V) : Set V :=
  A.closureSet {x}

/-- The generating vertex belongs to its one-point closure. -/
theorem mem_closureAtSet (A : Structure L V) (x : V) :
    x ∈ A.closureAtSet x := by
  exact A.subset_closureSet {x} (by simp)

/-- If y lies in the closure of x, then the closure of y is contained in the
closure of x. -/
theorem closureAtSet_subset_of_mem (A : Structure L V) {x y : V}
    (hy : y ∈ A.closureAtSet x) :
    A.closureAtSet y ⊆ A.closureAtSet x := by
  apply A.closureSet_minimal (A.isClosed_closureSet {x})
  intro z hz
  simpa [closureAtSet] using hy

/-- The induced structure on the closure of a set. -/
def closureStructure (A : Structure L V) (S : Set V) :
    Structure L (A.closureSet S) :=
  A.induce (A.closureSet S) (A.isClosed_closureSet S)

/-- The induced structure on the closure of one vertex. -/
def closureAt (A : Structure L V) (x : V) :
    Structure L (A.closureAtSet x) :=
  A.closureStructure {x}

end Structure
end AllThoseEPPA
