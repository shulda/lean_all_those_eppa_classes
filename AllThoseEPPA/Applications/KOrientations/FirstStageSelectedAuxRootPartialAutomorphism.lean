import AllThoseEPPA.Applications.KOrientations.DTraceClosedImageTransport
import AllThoseEPPA.Applications.KOrientations.FirstStageFullDSourceEmbedding
import AllThoseEPPA.Applications.KOrientations.FirstStageSelectedGraphDomainImage
import AllThoseEPPA.Applications.KOrientations.AuxiliaryRootPartialIsomorphism

/-!
# Construct the TRUE second-stage Γ-root partial automorphism from a full d-partial map

Let p be an arbitrary genuine partial automorphism of the ORIGINAL
all-arity d(A), not of a fictitious unary presentation. The first
coherent successor EPPA selector gives an actual graph automorphism
g_p∈Aut(B₀) of the first-stage witness extending p.

The original successor embedding ι:A↪B₀ has image S⊆B₀ which is
successor-closed but need NOT be d-closed in the entire ambient
B₀. The certified source-to-intrinsic-d-trace embedding
E:d(A)≅dTrace(B₀,S) transports the two truly d-closed partial-map
domains of p to genuine closed subdomains T_p,T'_p of this trace.
The actual selected graph automorphism sends their ENTIRE embedded
underlying vertex sets exactly from T_p onto T'_p.

All hypotheses of auxiliaryClosedRootPartialIsomorphism are
therefore discharged: the second Γ-root partial automorphism
p_aux is the real root restriction of g_p, with language component
precisely g_p itself, full reflection of ALL R_P/E_P auxiliary
relation symbols (including external centres), and EXACT unary
successor fibre equality. No assumption g_p[S]=S.

This constructs the missing typed input to the SECOND coherent
EPPA selector. Naturality on original coherent triples and
equivalent partial maps, reconstructed gluing, and the final
k-orientation coherent EPPA theorem remain separate obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The true first-witness old-source embedding in the
INTRINSIC full d-trace retains the literal first successor
embedding's ambient vertex coordinate. -/
@[simp] theorem firstStageFullDSourceEmbedding_val
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (x : V) :
    ((firstStageFullDSourceEmbedding A G k ι).toFun x).val = ι x :=
  rfl

/-- Exact underlying first-witness vertex set of the embedded
old closed full-d partial domain, preserving every vertex and
without assuming the whole old S is ambient d-closed. -/
theorem firstStageFullDSourceEmbedding_val_image
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (T : Set V) :
    Subtype.val '' ((firstStageFullDSourceEmbedding A G k ι).toFun '' T) =
      ι.toFun '' T := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, hzx⟩, hzy⟩
    refine ⟨x, hx, ?_⟩
    calc
      ι x = ((firstStageFullDSourceEmbedding A G k ι).toFun x).val :=
        (firstStageFullDSourceEmbedding_val A G k ι x).symm
      _ = z.val := congrArg Subtype.val hzx
      _ = y := hzy
  · rintro ⟨x, hx, hxy⟩
    refine ⟨(firstStageFullDSourceEmbedding A G k ι).toFun x,
      ⟨x, hx, rfl⟩, ?_⟩
    exact (firstStageFullDSourceEmbedding_val A G k ι x).trans hxy

/-- Every source domain of a genuine FULL d-partial automorphism
becomes a genuinely closed substructure of the intrinsic first
EPPA witness d-trace. This includes all n-ary F_n fibres. -/
theorem firstStage_dPartialSourceTrace_isClosed
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    (dTraceStructure G k (Set.range ι.toFun)).IsClosed
      ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.source) :=
  dEmbedding_image_isClosed (dStructure A k)
    (dTraceStructure G k (Set.range ι.toFun))
    (firstStageFullDSourceEmbedding A G k ι) p.source p.source_closed

/-- Likewise its entire TRUE target domain, independently of
the first-stage B₀ automorphism's global action on S. -/
theorem firstStage_dPartialTargetTrace_isClosed
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    (dTraceStructure G k (Set.range ι.toFun)).IsClosed
      ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.target) :=
  dEmbedding_image_isClosed (dStructure A k)
    (dTraceStructure G k (Set.range ι.toFun))
    (firstStageFullDSourceEmbedding A G k ι) p.target p.target_closed

/-- The ACTUAL first selected full graph automorphism transports
all embedded original d-source vertices onto precisely the
embedded original target vertices in the dependent intrinsic
d-trace of the old source S. -/
theorem firstStage_selectedGraphAut_dTraceDomainImage
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p))).1 ''
        (Subtype.val '' ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.source)) =
      Subtype.val '' ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.target) := by
  rw [firstStageFullDSourceEmbedding_val_image A G k ι p.source,
    firstStageFullDSourceEmbedding_val_image A G k ι p.target]
  exact firstStage_coherentSelector_graphAut_exactDomainImage A G k ι s p

/-- For EVERY actual original all-arity d-partial automorphism,
the first chosen B₀ graph automorphism induces the REAL second
Γ-root partial automorphism in the complete public EPPA API.
Its language component is the actual B₀ graph automorphism;
ALL external R_P/E_P tuples are preserved AND reflected and
the set-valued unary successor function is preserved exactly.
Both source and target are genuinely d-trace-closed, rather than
being arbitrary nonclosed subsets of the auxiliary source. -/
noncomputable def firstStage_selectedAuxRootPartialAutomorphism
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    Structure.PartialAutomorphism
      (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) :=
  auxiliaryClosedRootPartialIsomorphism G k (Set.range ι.toFun)
    ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.source)
    ((firstStageFullDSourceEmbedding A G k ι).toFun '' p.target)
    (firstStage_dPartialSourceTrace_isClosed A G k ι p)
    (firstStage_dPartialTargetTrace_isClosed A G k ι p)
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p)))
    (firstStage_selectedGraphAut_dTraceDomainImage A G k ι s p)

end AllThoseEPPA.Applications.KOrientations
