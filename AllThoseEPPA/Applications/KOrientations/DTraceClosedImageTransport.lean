import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso

/-!
# Exact image of a closed original d-domain under genuine d-language embeddings

The original full d-language has one genuinely set-valued function
for each arity, not just the unary successor operation. The
k-orientation proof must transport a true closed partial-domain T
from the input d-expansion to the intrinsic d-trace of the
successor-embedded original source inside the first EPPA witness B₀.

Any exact embedding for this TRIVIALLY RELABELLED d-language sends
an arbitrary function-closed source set onto a function-closed
image in its target, without requiring surjectivity of the
embedding onto the whole target. Crucially, this is true because
Embedding.map_func asserts EQUALITY of sets, not mere inclusion.
The proof takes actual preimages of every input tuple and the
actual function-output vertex, and covers ALL higher-arity
root-fibre function symbols, including empty fibres.

The second theorem specializes this exact principle to the
already Lean-certified isomorphism of intrinsic d-traces on
successor-closed directed graph pieces, without falsely assuming
that the entire first-stage source S is ambient d-closed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An exact embedding of full arbitrarily high-arity d-language
structures sends the image of EVERY closed input domain to a
closed output domain, with no surjectivity-on-ambient assumption.
This is needed before restricting the induced Γ-auxiliary root
partial isomorphism to the original d-partial-map source/range. -/
theorem dEmbedding_image_isClosed
    {X : Type u} {Y : Type v}
    (A : Structure dLanguage X) (B : Structure dLanguage Y)
    (e : Structure.Embedding dTrivialAction A B)
    (T : Set X) (hT : A.IsClosed T) :
    B.IsClosed (e.toFun '' T) := by
  classical
  intro n F xs hxs y hy
  let a : Fin n → X := fun i => Classical.choose (hxs i)
  have ha (i : Fin n) : a i ∈ T :=
    (Classical.choose_spec (hxs i)).1
  have he (i : Fin n) : e.toFun (a i) = xs i :=
    (Classical.choose_spec (hxs i)).2
  have htuple : e.toFun ∘ a = xs := by
    funext i
    exact he i
  have hmap := e.map_func F a
  change (e.toFun '' A.func F a) =
      B.func F (e.toFun ∘ a) at hmap
  rw [htuple] at hmap
  rw [← hmap] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨b, hT F a ha hb, rfl⟩

/-- For an exact graph-induced isomorphism of intrinsic d-traces,
images of source d-closed subdomains remain exactly d-closed in
the TARGET trace even when neither ambient piece is globally
d-closed in its surrounding graph. -/
theorem closedGraph_dTraceEmbedding_image_isClosed
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ x y : V, x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ x y : W, x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (U : Set S)
    (hU : (dTraceStructure G k S).IsClosed U) :
    (dTraceStructure H k T).IsClosed
      ((closedGraph_dTraceEmbedding G H k S T
        hS hT e hEdge).toFun '' U) := by
  exact dEmbedding_image_isClosed
    (dTraceStructure G k S) (dTraceStructure H k T)
    (closedGraph_dTraceEmbedding G H k S T hS hT e hEdge)
    U hU

end AllThoseEPPA.Applications.KOrientations
