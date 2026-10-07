import AllThoseEPPA.Structure

/-!
# Relabelling and relational reducts

This file packages two operations used throughout the paper:

* the action of the language-permutation group on structures by relabelling;
* the relational reduct `A⁻` obtained by forgetting all function symbols.

They are introduced before the unary-function construction and are also used
later in the unrestricted and negative EPPA theorems.
-/

namespace AllThoseEPPA

universe u v w

namespace Language

variable {L : Language.{u}} {Γ : Type v} [Group Γ]

/-- Restrict a language action to the relational reduct. -/
def Action.relationalReduct (act : L.Action Γ) :
    L.relationalReduct.Action Γ where
  rel := act.rel
  func n := by
    exact
      { toFun := fun g => 1
        map_one' := rfl
        map_mul' := by intro g h; rfl }

@[simp] theorem Action.relationalReduct_onRel
    (act : L.Action Γ) {n : ℕ} (g : Γ) (R : L.RelSymbol n) :
    act.relationalReduct.onRel g R = act.onRel g R :=
  rfl

end Language

namespace Structure

variable {L : Language.{u}} {Γ : Type v} [Group Γ] {V : Type w}

/-- Relabel a structure by a language permutation.  This is the paper's
action `gA = (g,id_A)(A)`. -/
def relabel (act : L.Action Γ) (g : Γ) (A : Structure L V) :
    Structure L V where
  rel R xs := A.rel (act.onRel g⁻¹ R) xs
  func F xs := A.func (act.onFunc g⁻¹ F) xs

@[simp] theorem relabel_rel (act : L.Action Γ) (g : Γ)
    (A : Structure L V) {n : ℕ} (R : L.RelSymbol n)
    (xs : Fin n → V) :
    (A.relabel act g).rel R xs ↔ A.rel (act.onRel g⁻¹ R) xs :=
  Iff.rfl

@[simp] theorem relabel_func (act : L.Action Γ) (g : Γ)
    (A : Structure L V) {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → V) :
    (A.relabel act g).func F xs = A.func (act.onFunc g⁻¹ F) xs :=
  rfl

@[simp] theorem relabel_one (act : L.Action Γ) (A : Structure L V) :
    A.relabel act 1 = A := by
  cases A
  simp [relabel]

theorem relabel_mul (act : L.Action Γ) (g h : Γ) (A : Structure L V) :
    (A.relabel act h).relabel act g = A.relabel act (g * h) := by
  cases A
  simp [relabel, Language.Action.onRel_mul, Language.Action.onFunc_mul,
    mul_inv_rev]

/-- The orbit of a structure under language relabelling is finite. -/
def HasFiniteRelabelOrbit (act : L.Action Γ) (A : Structure L V) : Prop :=
  Set.Finite (Set.range fun g : Γ => A.relabel act g)

/-- Forget all function symbols. -/
def relationalReduct (A : Structure L V) :
    Structure L.relationalReduct V where
  rel := A.rel
  func := by
    intro n F xs
    exact Empty.elim F

@[simp] theorem relationalReduct_rel (A : Structure L V)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V) :
    A.relationalReduct.rel R xs ↔ A.rel R xs :=
  Iff.rfl

/-- Relabelling commutes with taking the relational reduct. -/
theorem relationalReduct_relabel
    (act : L.Action Γ) (g : Γ) (A : Structure L V) :
    (A.relabel act g).relationalReduct =
      A.relationalReduct.relabel act.relationalReduct g := by
  cases A
  rfl

theorem HasFiniteRelabelOrbit.relationalReduct
    {act : L.Action Γ} {A : Structure L V}
    (hA : A.HasFiniteRelabelOrbit act) :
    A.relationalReduct.HasFiniteRelabelOrbit act.relationalReduct := by
  let f : Structure L V → Structure L.relationalReduct V :=
    Structure.relationalReduct
  have himage :
      Set.range (fun g : Γ =>
        A.relationalReduct.relabel act.relationalReduct g) =
      f '' Set.range (fun g : Γ => A.relabel act g) := by
    ext B
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨A.relabel act g, ⟨g, rfl⟩,
        (relationalReduct_relabel act g A).symm⟩
    · rintro ⟨C, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, relationalReduct_relabel act g A⟩
  rw [himage]
  exact hA.image f

end Structure
end AllThoseEPPA
