import AllThoseEPPA.Applications.KOrientations.SecondStageRootAnchor
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges

/-!
# A common root anchor transports incoming E_P relations

Fix one B₁ root a and a *single* automorphism f moving its entire
unary closure into the distinguished source roots. If a realized
E_P tuple describes an outgoing non-root neighbour p=(x,W), and
its support W lies in that closure, then the very same automorphism
transports this E_P relation into the original auxiliary root sort.

The template centre g(x), where g = ι.lang⁻¹ * f.lang, is then
an outgoing neighbour of the source root of a in the original graph.
This is the second half of the eventual injection from the complete
root outneighbourhood into the original template outneighbourhood.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

namespace AuxiliaryRootAnchor

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ} {S : Set V}
variable {B : Structure (auxiliaryLanguage G k) W}
variable {ι : Structure.Embedding (auxiliaryAction G k)
    (auxiliaryRootStructure G k S) B}
variable {a : W}

/-- The full B₀ automorphism associated with an anchor's language
component, corrected for the embedding language component. -/
def templateMap
    (anchor : AuxiliaryRootAnchor G k S B ι a) : G.graphAut :=
  ι.lang⁻¹ * anchor.mover.lang

/-- The source-moving automorphism witnesses the template edge
anchor.source → g(p.center) for every outgoing non-root p, provided
that all its realized roots are in the moved unary closure. -/
theorem move_incoming
    (anchor : AuxiliaryRootAnchor G k S B ι a)
    (p : CanonicalNonroot G k B)
    (hIncoming : IncomingRealized G k B a p)
    (hSupport : p.support ⊆ B.closureAtSet a) :
    G.edge anchor.source.val ((anchor.templateMap).1 p.center) := by
  classical
  obtain ⟨n, P, ys, hc, hE, ha, hU⟩ := hIncoming
  have hBase : anchor.mover (ys 0) = ι anchor.source := by
    rw [ha]
    exact anchor.source_eq
  have hTail (i : Fin n) :
      ∃ t : RootsIn G k S,
        anchor.mover (ys (Fin.succ i)) = ι t := by
    apply anchor.moves_closure
    apply hSupport
    rw [← hU]
    exact ⟨i, rfl⟩
  let ts : Fin (n + 1) → RootsIn G k S :=
    Fin.cases anchor.source
      (fun i => Classical.choose (hTail i))
  have hPts : ∀ i : Fin (n + 1), anchor.mover (ys i) = ι (ts i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [ts] using hBase
    · intro j
      simpa [ts] using (Classical.choose_spec (hTail j))
  let g : G.graphAut := anchor.templateMap
  have hLabel :
      (auxiliaryAction G k).onRel ι.lang
        (AuxiliaryRel.incoming (RootPattern.transportAut g P)) =
      (auxiliaryAction G k).onRel anchor.mover.lang
        (AuxiliaryRel.incoming P) := by
    change AuxiliaryRel.incoming
      (RootPattern.transportAut ι.lang
        (RootPattern.transportAut (ι.lang⁻¹ * anchor.mover.lang) P)) =
      AuxiliaryRel.incoming (RootPattern.transportAut anchor.mover.lang P)
    rw [← RootPattern.transportAut_mul]
    simp [← mul_assoc]
  have hMap : B.rel
      ((auxiliaryAction G k).onRel anchor.mover.lang
        (AuxiliaryRel.incoming P)) (anchor.mover ∘ ys) :=
    (Structure.Automorphism.map_rel_iff
      anchor.mover (AuxiliaryRel.incoming P) ys).2 hE
  have hTuple : (anchor.mover ∘ ys) = (ι.toFun ∘ ts) := by
    funext i
    exact hPts i
  have hSource :
      (auxiliaryRootStructure G k S).rel
        (AuxiliaryRel.incoming (RootPattern.transportAut g P)) ts := by
    apply (ι.map_rel_iff
      (AuxiliaryRel.incoming (RootPattern.transportAut g P)) ts).1
    rw [hLabel, ← hTuple]
    exact hMap
  have hData :=
    (auxiliaryRootStructure_incoming G k n S
      (RootPattern.transportAut g P) ts).mp hSource
  have hZero : ts 0 = anchor.source := by
    apply ι.injective
    calc
      ι (ts 0) = anchor.mover (ys 0) := (hPts 0).symm
      _ = ι anchor.source := hBase
  have hEdge : G.edge (ts 0).val (g.1 P.center) := hData.2.1
  change G.edge anchor.source.val ((anchor.templateMap).1 p.center)
  simpa only [hZero, hc] using hEdge

end AuxiliaryRootAnchor
end AllThoseEPPA.Applications.KOrientations
