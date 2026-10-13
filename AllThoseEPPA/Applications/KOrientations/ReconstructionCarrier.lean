import AllThoseEPPA.Applications.KOrientations.SecondStageRelationTransfer

/-!
# Choice-free vertex carrier for the reconstructed d-orientation

A reconstructed non-root is **the pair** (template centre, realized
root-support set), not a chosen representative of a quotient of
labelled tuples.  The witness of realization is proof-irrelevant.

The vertex type is the disjoint union of the B₁ root sort and these
canonical non-root pairs.  At this stage NO graph relation is defined:
in particular, this file does not assert the final d-EPPA theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The pair (x,W) is realized if an actual R_P tuple with centre x
enumerates precisely W.  Its proof retains no arbitrary ordering in
the data of a reconstructed vertex. -/
def IsRealizedNonroot {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (x : V) (U : Set W) : Prop :=
  ∃ (n : ℕ) (P : RootPattern G k n) (xs : Fin n → W),
    P.center = x ∧ B.rel (AuxiliaryRel.root P) xs ∧
      Set.range xs = U

/-- The intrinsic representation of a non-root: projection to B₀ and
unordered realized root set in B₁. -/
structure CanonicalNonroot {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) where
  center : V
  support : Set W
  witnessed : IsRealizedNonroot G k B center support

namespace CanonicalNonroot

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ}
variable {B : Structure (auxiliaryLanguage G k) W}

/-- Any actual R_P-realization determines exactly one canonical
centre/support pair. -/
def ofRelation {n : ℕ} (P : RootPattern G k n)
    (xs : Fin n → W)
    (h : B.rel (AuxiliaryRel.root P) xs) :
    CanonicalNonroot G k B where
  center := P.center
  support := Set.range xs
  witnessed := ⟨n, P, xs, rfl, h, rfl⟩

/-- Equality is *exactly* equality of projection and root support.
There is no arbitrary representative coordinate to compare. -/
theorem eq_of_center_support (p q : CanonicalNonroot G k B)
    (hc : p.center = q.center) (hs : p.support = q.support) :
    p = q := by
  cases p with
  | mk pc ps hp =>
    cases q with
    | mk qc qs hq =>
      dsimp at hc hs
      cases hc
      cases hs
      rfl

@[simp] theorem ofRelation_center {n : ℕ}
    (P : RootPattern G k n) (xs : Fin n → W)
    (h : B.rel (AuxiliaryRel.root P) xs) :
    (ofRelation P xs h).center = P.center :=
  rfl

@[simp] theorem ofRelation_support {n : ℕ}
    (P : RootPattern G k n) (xs : Fin n → W)
    (h : B.rel (AuxiliaryRel.root P) xs) :
    (ofRelation P xs h).support = Set.range xs :=
  rfl

/-- The projection is genuinely a non-root of the template graph. -/
theorem center_nonroot (p : CanonicalNonroot G k B) :
    ¬ G.IsRoot k p.center := by
  obtain ⟨n, P, xs, hc, _, _⟩ := p.witnessed
  intro hr
  exact P.nonroot (by simpa only [hc] using hr)

/-- All reconstructed non-root supports are nonempty; the label
contains a positive-length enumeration. -/
theorem support_nonempty (p : CanonicalNonroot G k B) :
    p.support.Nonempty := by
  obtain ⟨n, P, xs, _, _, hU⟩ := p.witnessed
  refine ⟨xs ⟨0, P.positive⟩, ?_⟩
  rw [← hU]
  exact Set.mem_range_self (⟨0, P.positive⟩ : Fin n)

end CanonicalNonroot

/-- The disjoint tagged union of roots of B₁ and realized non-roots;
the tags prevent any collision of the two concrete carrier types. -/
abbrev ReconstructedCarrier {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) :=
  W ⊕ CanonicalNonroot G k B

/-- The canonical non-root carrier is finite whenever both original
vertex sorts are finite, regardless of the number of possible
relation arities. -/
instance canonicalNonroot_finite
    {V : Type u} [Fintype V] {W : Type v} [Finite W]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) :
    Finite (CanonicalNonroot G k B) := by
  classical
  exact Finite.of_injective
    (fun p : CanonicalNonroot G k B => (p.center, p.support))
    (by
      intro p q h
      apply CanonicalNonroot.eq_of_center_support p q
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

/-- Hence the whole tagged carrier is finite. -/
instance reconstructedCarrier_finite
    {V : Type u} [Fintype V] {W : Type v} [Finite W]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) :
    Finite (ReconstructedCarrier G k B) := by
  unfold ReconstructedCarrier
  infer_instance

/-- Choose a finite enumeration of the canonical reconstructed carrier,
whose finiteness is already proved above. This instance is
noncomputable because realized root-support subsets have no
preferred ordering. -/
noncomputable instance reconstructedCarrier_fintype
    {V : Type u} [Fintype V] {W : Type v} [Finite W]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) :
    Fintype (ReconstructedCarrier G k B) :=
  Fintype.ofFinite _

/-- Root vertices carry their intrinsic B₁-closure as support.
Non-root vertices carry precisely their canonical realized set W. -/
def reconstructedSupport
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) :
    ReconstructedCarrier G k B → Set W
  | .inl w => B.closureAtSet w
  | .inr p => p.support

/-- Every vertex has nonempty support, even before proving that the
eventual graph's reachable roots equal this support. -/
theorem reconstructedSupport_nonempty
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (z : ReconstructedCarrier G k B) :
    (reconstructedSupport G k B z).Nonempty := by
  cases z with
  | inl w =>
      exact ⟨w, B.mem_closureAtSet w⟩
  | inr p =>
      exact p.support_nonempty

end AllThoseEPPA.Applications.KOrientations
