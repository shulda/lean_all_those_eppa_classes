import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMonotone
import AllThoseEPPA.Substructure

/-!
# Intrinsic support pieces of the reconstructed orientation

For a subset T of the auxiliary B₁ root sort, define the
reconstructed piece D_T := {v | support(v) ⊆ T}. The already
Lean-certified monotonicity of supports along oriented paths
makes D_T closed under all directed successors, without invoking
the final d-closure theorem or any local correspondence.

When T itself is unary-closed inside B₁, its intersection with the
B₁-root sort is exactly T: closureAtSet(a) ⊆ T iff a∈T.
These facts will be used in the full d-closed-piece isomorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The reconstructed graph vertices whose complete intrinsic root
support lies in a specified subset of the B₁ root sort. -/
def ReconstructedSupportPiece
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (T : Set W) : Set (ReconstructedCarrier G k B) :=
  {z | reconstructedSupport G k B z ⊆ T}

/-- Every reconstructed support piece is closed under **all**
directed paths, purely by support monotonicity. -/
theorem faithful_reconstructed_supportPiece_reaches_closed
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (T : Set W)
    {x y : ReconstructedCarrier G k B}
    (hx : x ∈ ReconstructedSupportPiece G k B T)
    (hReach : (faithfulReconstructedDigraph G k S B ι hFaith).Reaches x y) :
    y ∈ ReconstructedSupportPiece G k B T :=
  (faithful_reconstructed_reaches_support_antitone
    G k S B ι hFaith hReach).trans hx

/-- For B₁'s unary-closed T, the root vertices of D_T are precisely
the tagged members of T. The statement does not require any
identification of degree-defined roots in the reconstructed graph. -/
theorem faithful_reconstructed_supportPiece_root_trace
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (T : Set W) (hT : B.IsClosed T)
    (a : W) :
    (.inl a : ReconstructedCarrier G k B) ∈
      ReconstructedSupportPiece G k B T ↔ a ∈ T := by
  change B.closureAtSet a ⊆ T ↔ a ∈ T
  constructor
  · intro ha
    exact ha (B.mem_closureAtSet a)
  · intro ha
    apply B.closureSet_minimal hT
    intro y hy
    have hya : y = a := by simpa using hy
    rw [hya]
    exact ha

end AllThoseEPPA.Applications.KOrientations
