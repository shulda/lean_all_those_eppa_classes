import AllThoseEPPA.Applications.KOrientations.DToSuccessorPartialAutomorphism
import AllThoseEPPA.Applications.KOrientations.FirstStageExactDomainImage
import AllThoseEPPA.Applications.KOrientations.FirstStageAutomorphismBridge

/-!
# Exact source/range images under the FIRST selected B₀ graph automorphism

An original input d-partial automorphism p first restricts to a
true unary-successor partial automorphism, with the SAME closed
source/target and exact pointwise map. The coherent first-stage
successor EPPA witness chooses an automorphism f of its whole B₀
successor structure. Its actual graph automorphism component
g = graphAutOfSuccessorAut B₀ f acts on the auxiliary symbols
R_P/E_P in the second EPPA step.

Crucially g takes ALL embedded vertices in the original d-closed
partial domain exactly onto ALL embedded vertices in its partial
range. The source of the auxiliary partial isomorphism does NOT
have to be invariant under g globally. This is the correctly
typed bridge connecting the public first-stage coherent selector
to the second-stage Γ-root partial-isomorphism API.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A first-stage successor automorphism extending the forgetful
partial map of a full d-partial automorphism induces the ACTUAL
graph automorphism with the exact required closed-domain image,
including surjectivity onto the entire target. -/
theorem firstStage_dPartialGraphAut_exactDomainImage
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (f : Structure.Automorphism successorAction (successorStructure G))
    (hf : Structure.ExtendsAlong successorAction ι
      (dPartialAutomorphism_to_successor A k p) f) :
    (graphAutOfSuccessorAut G f).1 '' (ι.toFun '' p.source) =
      ι.toFun '' p.target := by
  have heq := Structure.extendsAlong_image_source_eq_target
    successorAction ι (dPartialAutomorphism_to_successor A k p) f hf
  change f '' (ι.toFun '' p.source) = ι.toFun '' p.target at heq
  have hfGraph :
      ((graphAutOfSuccessorAut G f).1 : W → W) = f := by
    funext x
    exact graphAutOfSuccessorAut_apply G f x
  rw [hfGraph]
  exact heq

/-- The real FIRST coherent EPPA selector has the exact image
property automatically for EVERY original d-partial automorphism,
without choosing any automorphism lift or imposing global
preservation of the original source range. -/
theorem firstStage_coherentSelector_graphAut_exactDomainImage
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    (graphAutOfSuccessorAut G
      (s.extension (dPartialAutomorphism_to_successor A k p))).1 ''
      (ι.toFun '' p.source) = ι.toFun '' p.target :=
  firstStage_dPartialGraphAut_exactDomainImage A G k ι p
    (s.extension (dPartialAutomorphism_to_successor A k p))
    (s.extension_spec (dPartialAutomorphism_to_successor A k p))

end AllThoseEPPA.Applications.KOrientations
