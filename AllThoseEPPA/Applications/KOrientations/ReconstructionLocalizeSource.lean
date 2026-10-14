import AllThoseEPPA.Applications.KOrientations.SourceReconstructionChoiceIndependence
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMovable
import AllThoseEPPA.Applications.KOrientations.ReconstructionPathAction
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportEquivariance

/-!
# Localizing reconstructed vertices in the canonical source copy

Fix a second-stage automorphism f sending the entire intrinsic
support of a reconstructed vertex z into the root-only source.
Then the *transformed* reconstructed vertex is exactly the image
under the canonical source-copy map of some vertex of S.

For root-sort vertices this follows directly from the image of
their singleton closure. For a nonroot (x,W), use the realized R_P
tuple, move all its coordinates by f into A₁, and reflect the
transformed label through the exact embedding ι₁. Its transformed
centre is (ι₁.lang⁻¹*f.lang)(x); the correct source-copy centre
maps back by ι₁.lang to f.lang(x). Equality of the complete realized
root supports then identifies the canonical nonroot pairs.

This is the key local source correspondence needed before lifting
paths to every member of a reconstructed support.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A B₁-root that has moved into the embedded root source is
literally an image of a source root under the canonical source-copy
vertex map. -/
theorem faithful_localize_reconstructed_root
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRooted : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a : W)
    (hMove : ∃ r : RootsIn G k S, f a = ι r) :
    ∃ x : {v : V // v ∈ S},
      reconstructedVertexPerm G k B f (.inl a) =
        sourceReconstructedVertex G k S hClosed hRooted B ι x := by
  obtain ⟨r, hr⟩ := hMove
  refine ⟨⟨r.val, r.property.1⟩, ?_⟩
  have hRoot : G.IsRoot k r.val := r.property.2
  change Sum.inl (f a) =
    sourceReconstructedVertex G k S hClosed hRooted B ι
      ⟨r.val,r.property.1⟩
  simp only [sourceReconstructedVertex, dif_pos hRoot]
  exact congrArg Sum.inl hr

/-- A canonical nonroot whose entire support has moved into A₁
is exactly an image of a source nonroot, not just an arbitrary
tuple with the right cardinality. The language component is treated
as the actual full graph automorphism throughout. -/
theorem faithful_localize_reconstructed_nonroot
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRooted : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (hMove : ∀ w ∈ p.support,
      ∃ r : RootsIn G k S, f w = ι r) :
    ∃ x : {v : V // v ∈ S},
      reconstructedVertexPerm G k B f (.inr p) =
        sourceReconstructedVertex G k S hClosed hRooted B ι x := by
  classical
  obtain ⟨n,P,xs,hc,hR,hU⟩ := p.witnessed
  have hPtsExist (i : Fin n) :
      ∃ r : RootsIn G k S, f (xs i) = ι r := by
    apply hMove
    rw [← hU]
    exact ⟨i, rfl⟩
  let ts : Fin n → RootsIn G k S :=
    fun i => Classical.choose (hPtsExist i)
  have hPts : ∀ i : Fin n, f (xs i) = ι (ts i) :=
    fun i => Classical.choose_spec (hPtsExist i)
  let g : G.graphAut := ι.lang⁻¹ * f.lang
  let Q : RootPattern G k n := RootPattern.transportAut g P
  have hPatternAction :
      RootPattern.transportAut ι.lang Q =
        RootPattern.transportAut f.lang P := by
    change RootPattern.transportAut ι.lang
      (RootPattern.transportAut (ι.lang⁻¹ * f.lang) P) =
      RootPattern.transportAut f.lang P
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang (AuxiliaryRel.root Q) =
      (auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P) := by
    change AuxiliaryRel.root (RootPattern.transportAut ι.lang Q) =
      AuxiliaryRel.root (RootPattern.transportAut f.lang P)
    exact congrArg AuxiliaryRel.root hPatternAction
  have hMapped :
      B.rel ((auxiliaryAction G k).onRel f.lang
        (AuxiliaryRel.root P)) (f ∘ xs) :=
    (Structure.Automorphism.map_rel_iff
      f (AuxiliaryRel.root P) xs).2 hR
  have hTuple : (f ∘ xs) = (ι.toFun ∘ ts) := by
    funext i
    exact hPts i
  have hSource :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.root Q) ts := by
    apply (ι.map_rel_iff (AuxiliaryRel.root Q) ts).1
    rw [hLabel, ← hTuple]
    exact hMapped
  have hx : Q.center ∈ S :=
    ((auxiliaryRootStructure_root G k n S Q ts).mp hSource).1
  let x : {v : V // v ∈ S} := ⟨Q.center,hx⟩
  let d : SourceNonrootPattern G k S x.val :=
    { n := n
      pattern := Q
      tuple := ts
      center_eq := rfl
      realized := hSource }
  have hSourceVertex :
      sourceReconstructedVertex G k S hClosed hRooted B ι x =
        (.inr (d.toCanonical B ι) : ReconstructedCarrier G k B) :=
    sourceReconstructedVertex_eq_of_pattern
      G k S hClosed hRooted B ι x Q.nonroot d
  have hCenter :
      (CanonicalNonroot.map f p).center =
        (d.toCanonical B ι).center := by
    change f.lang.1 p.center = ι.lang.1 Q.center
    have hCenterMap := congrArg RootPattern.center hPatternAction
    change ι.lang.1 Q.center = f.lang.1 P.center at hCenterMap
    rw [← hc]
    exact hCenterMap.symm
  have hRange :
      Set.range (f ∘ xs) = Set.range (ι.toFun ∘ ts) := by
    exact congrArg Set.range hTuple
  have hSupport :
      (CanonicalNonroot.map f p).support =
        (d.toCanonical B ι).support := by
    change f '' p.support = Set.range (ι.toFun ∘ ts)
    calc
      f '' p.support = f '' Set.range xs :=
        congrArg (fun T : Set W => f '' T) hU.symm
      _ = Set.range (f ∘ xs) := by
        rw [Set.range_comp]
      _ = Set.range (ι.toFun ∘ ts) := hRange
  have hpq : CanonicalNonroot.map f p = d.toCanonical B ι :=
    CanonicalNonroot.eq_of_center_support
      (CanonicalNonroot.map f p) (d.toCanonical B ι)
      hCenter hSupport
  refine ⟨x, ?_⟩
  change Sum.inr (CanonicalNonroot.map f p) =
    sourceReconstructedVertex G k S hClosed hRooted B ι x
  rw [hSourceVertex, hpq]

/-- For every reconstructed vertex, irreducible-structure faithfulness
produces one automorphism taking it into the canonical source copy.
The same automorphism transports its *entire* support to source roots. -/
theorem faithful_reconstructed_vertex_localizes
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRooted : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (z : ReconstructedCarrier G k B) :
    ∃ (f : Structure.Automorphism (auxiliaryAction G k) B)
      (x : {v : V // v ∈ S}),
      reconstructedVertexPerm G k B f z =
        sourceReconstructedVertex G k S hClosed hRooted B ι x ∧
      (∀ w ∈ reconstructedSupport G k B z,
        ∃ r : RootsIn G k S, f w = ι r) := by
  obtain ⟨f, hMove⟩ :=
    faithful_reconstructed_support_movable G k S B ι hFaith z
  cases z with
  | inl a =>
      obtain ⟨x, hx⟩ :=
        faithful_localize_reconstructed_root
          G k S hClosed hRooted B ι f a
          (hMove a (B.mem_closureAtSet a))
      exact ⟨f, x, hx, hMove⟩
  | inr p =>
      obtain ⟨x, hx⟩ :=
        faithful_localize_reconstructed_nonroot
          G k S hClosed hRooted B ι f p hMove
      exact ⟨f, x, hx, hMove⟩

end AllThoseEPPA.Applications.KOrientations
