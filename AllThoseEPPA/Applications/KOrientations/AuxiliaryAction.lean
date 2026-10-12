import AllThoseEPPA.Applications.KOrientations.GraphAutomorphismGroup
import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage

/-!
# Genuine graph-automorphism action on the root language

We use the **full** finite group `G.graphAut`, not its image in the
permutations of the relation labels.  A graph automorphism transports
the centre and the complete ordered tuple of each root pattern, while
fixing the binary edge relation and the unary successor symbol.

This explicitly supplies the nonfaithful language action required for
the second unrestricted coherent EPPA construction.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

namespace RootPattern

variable {V : Type u} [Fintype V] {G : Digraph V} {k n : ℕ}

/-- The root pattern is determined by its centre and enumeration;
all remaining data are propositions. -/
private theorem ext_fields
    (P Q : RootPattern G k n)
    (hc : P.center = Q.center)
    (ht : P.tuple = Q.tuple) : P = Q := by
  cases P
  cases Q
  cases hc
  cases ht
  rfl

/-- Transport all of a pattern (centre **and** ordered root tuple)
under an actual graph automorphism. -/
def transport (g : G.graphAut) (P : RootPattern G k n) :
    RootPattern G k n where
  center := g.1 P.center
  nonroot := by
    intro hr
    exact P.nonroot ((G.graphAut_root_iff k g P.center).mp hr)
  positive := P.positive
  tuple := fun i => g.1 (P.tuple i)
  injective := by
    intro i j h
    exact P.injective (g.1.injective h)
  roots_eq := by
    rw [G.graphAut_roots_image k g P.center, P.roots_eq]
    ext r
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨P.tuple i, ⟨i, rfl⟩, rfl⟩

@[simp] theorem transport_one (P : RootPattern G k n) :
    transport (1 : G.graphAut) P = P := by
  apply ext_fields
  · simp [transport]
  · funext i
    simp [transport]

theorem transport_mul (g h : G.graphAut)
    (P : RootPattern G k n) :
    transport (g * h) P = transport g (transport h P) := by
  apply ext_fields
  · change (g * h : G.graphAut).1 P.center =
      g.1 (h.1 P.center)
    simp
  · funext i
    change (g * h : G.graphAut).1 (P.tuple i) =
      g.1 (h.1 (P.tuple i))
    simp

@[simp] theorem transport_inv_left (g : G.graphAut)
    (P : RootPattern G k n) :
    transport g⁻¹ (transport g P) = P := by
  rw [← transport_mul]
  simp

@[simp] theorem transport_inv_right (g : G.graphAut)
    (P : RootPattern G k n) :
    transport g (transport g⁻¹ P) = P := by
  rw [← transport_mul]
  simp

end RootPattern

/-- Action on each relation symbol: the underlying edge symbol is
fixed, whereas both R_P and E_P are indexed by the transported pattern. -/
def auxiliaryRelTransport {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) {n : ℕ}
    (g : G.graphAut) : AuxiliaryRel G k n → AuxiliaryRel G k n
  | .edge => .edge
  | .root P => .root (RootPattern.transport g P)
  | .incoming P => .incoming (RootPattern.transport g P)

/-- The induced equivalence of relation symbols, including the
correct inverse-automorphism action. -/
def auxiliaryRelPermutation {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ) (g : G.graphAut) :
    Equiv.Perm (AuxiliaryRel G k n) where
  toFun := auxiliaryRelTransport G k g
  invFun := auxiliaryRelTransport G k g⁻¹
  left_inv := by
    intro R
    cases R with
    | edge => rfl
    | root P =>
        change AuxiliaryRel.root
          (RootPattern.transport g⁻¹ (RootPattern.transport g P)) =
          AuxiliaryRel.root P
        rw [RootPattern.transport_inv_left]
    | incoming P =>
        change AuxiliaryRel.incoming
          (RootPattern.transport g⁻¹ (RootPattern.transport g P)) =
          AuxiliaryRel.incoming P
        rw [RootPattern.transport_inv_left]
  right_inv := by
    intro R
    cases R with
    | edge => rfl
    | root P =>
        change AuxiliaryRel.root
          (RootPattern.transport g (RootPattern.transport g⁻¹ P)) =
          AuxiliaryRel.root P
        rw [RootPattern.transport_inv_right]
    | incoming P =>
        change AuxiliaryRel.incoming
          (RootPattern.transport g (RootPattern.transport g⁻¹ P)) =
          AuxiliaryRel.incoming P
        rw [RootPattern.transport_inv_right]

/-- The genuine monoid homomorphism on each arity's relation symbols. -/
def auxiliaryRelAction {V : Type u} [Fintype V]
    (G : Digraph V) (k n : ℕ) :
    G.graphAut →* Equiv.Perm (AuxiliaryRel G k n) where
  toFun := auxiliaryRelPermutation G k n
  map_one' := by
    ext R
    cases R with
    | edge => rfl
    | root P =>
        change AuxiliaryRel.root
          (RootPattern.transport (1 : G.graphAut) P) =
          AuxiliaryRel.root P
        rw [RootPattern.transport_one]
    | incoming P =>
        change AuxiliaryRel.incoming
          (RootPattern.transport (1 : G.graphAut) P) =
          AuxiliaryRel.incoming P
        rw [RootPattern.transport_one]
  map_mul' := by
    intro g h
    ext R
    cases R with
    | edge => rfl
    | root P =>
        change AuxiliaryRel.root (RootPattern.transport (g * h) P) =
          AuxiliaryRel.root (RootPattern.transport g
            (RootPattern.transport h P))
        rw [RootPattern.transport_mul]
    | incoming P =>
        change AuxiliaryRel.incoming (RootPattern.transport (g * h) P) =
          AuxiliaryRel.incoming (RootPattern.transport g
            (RootPattern.transport h P))
        rw [RootPattern.transport_mul]

/-- Full, possibly nonfaithful language action on the root-sort
auxiliary symbols.  Only relation labels are moved; the one
set-valued unary successor function is fixed. -/
def auxiliaryAction {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) :
    (auxiliaryLanguage G k).Action G.graphAut where
  rel n := auxiliaryRelAction G k n
  func _ := 1

/-- Finiteness of the *actual* automorphism group supplies the
finite-relabel-orbit hypothesis for every auxiliary structure. -/
theorem auxiliary_finiteRelabelOrbit {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) {W : Type u}
    (A : Structure (auxiliaryLanguage G k) W) :
    A.HasFiniteRelabelOrbit (auxiliaryAction G k) := by
  unfold Structure.HasFiniteRelabelOrbit
  exact Set.finite_range (fun g : G.graphAut =>
    A.relabel (auxiliaryAction G k) g)

end AllThoseEPPA.Applications.KOrientations
