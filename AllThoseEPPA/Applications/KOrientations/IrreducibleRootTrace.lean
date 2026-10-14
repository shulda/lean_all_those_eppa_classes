import AllThoseEPPA.Applications.KOrientations.SupportFreeSide
import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces
import Mathlib.Tactic.FinCases

/-!
# Irreducible reconstructed d-pieces have irreducible B₁-root traces

This is the full free-decomposition transfer lemma of the manuscript.
If the B₁-root trace U of a closed reconstructed piece D were freely
reducible, each canonical support inside D would lie wholly in one
side, by the exact support-irreducibility theorem.

Lift those root sides to the d-closed supported pieces on the
reconstructed vertex set. They cover D, are proper because their
B₁-root traces are proper, and admit no cross edges or mixed
function outputs:
* Edge support is antitone along directed edges.
* The unary successor symbol has only one input.
* Every input of a nonempty F_n-fibre is a reachable root of its
  output; its intrinsic support lies inside the output support.

This produces a genuine FreeDecomposition of D, contradicting
irreducibility. The statement uses the actual set-valued-function
formalism and the public IsIrreducible definition.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Irreducibility of a d-closed reconstructed substructure forces
irreducibility of its closed trace in the auxiliary root structure. -/
theorem faithful_reconstructed_irreducible_rootTrace
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (D : Set (ReconstructedCarrier G k B))
    (hD : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D)
    (hIrr : ((dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
        D hD).IsIrreducible) :
    (B.induce (reconstructedRootTrace G k B D)
      (faithful_reconstructed_rootTrace_isClosed
        G k S hBound hClosed hRooted B ι hFaith D hD)).IsIrreducible := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let A := dStructure H k
  let U := reconstructedRootTrace G k B D
  let hU : B.IsClosed U :=
    faithful_reconstructed_rootTrace_isClosed
      G k S hBound hClosed hRooted B ι hFaith D hD
  change (B.induce U hU).IsIrreducible
  constructor
  intro d
  let UL : Set W := Subtype.val '' d.left
  let UR : Set W := Subtype.val '' d.right
  let L : Set D :=
    {z | reconstructedSupport G k B z.val ⊆ UL}
  let R : Set D :=
    {z | reconstructedSupport G k B z.val ⊆ UR}
  have hSupportSides (z : D) :
      reconstructedSupport G k B z.val ⊆ UL ∨
        reconstructedSupport G k B z.val ⊆ UR :=
    faithful_reconstructedSupport_subset_one_free_root_side
      G k S hBound hClosed hRooted B ι hFaith D hD
      d z.val z.property
  have hLeftAmbient : A.IsClosed
      (reconstructedSupportedPiece G k B UL) :=
    faithful_reconstructed_supportedPiece_isClosed
      G k S hBound hClosed hRooted B ι hFaith UL
  have hRightAmbient : A.IsClosed
      (reconstructedSupportedPiece G k B UR) :=
    faithful_reconstructed_supportedPiece_isClosed
      G k S hBound hClosed hRooted B ι hFaith UR
  have hLeftClosed : (A.induce D hD).IsClosed L := by
    intro n F xs hxs z hz
    apply hLeftAmbient F (Subtype.val ∘ xs)
    · intro i
      exact hxs i
    · exact hz
  have hRightClosed : (A.induce D hD).IsClosed R := by
    intro n F xs hxs z hz
    apply hRightAmbient F (Subtype.val ∘ xs)
    · intro i
      exact hxs i
    · exact hz
  have hCover : L ∪ R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact hSupportSides z
  have hLeftProper : L ≠ Set.univ := by
    have hWitness : ∃ a : U, a ∉ d.left := by
      by_contra hh
      apply d.left_proper
      apply Set.eq_univ_of_forall
      intro a
      by_contra ha
      exact hh ⟨a, ha⟩
    obtain ⟨a, ha⟩ := hWitness
    let z : D := ⟨.inl a.val, a.property⟩
    have hzNot : z ∉ L := by
      intro hz
      have hSelf : a.val ∈
          reconstructedSupport G k B (.inl a.val) :=
        B.mem_closureAtSet a.val
      have hImage : a.val ∈ UL := hz hSelf
      obtain ⟨b, hb, heq⟩ := hImage
      have hba : b = a := Subtype.ext heq
      exact ha (hba ▸ hb)
    intro hAll
    apply hzNot
    rw [hAll]
    exact Set.mem_univ _
  have hRightProper : R ≠ Set.univ := by
    have hWitness : ∃ a : U, a ∉ d.right := by
      by_contra hh
      apply d.right_proper
      apply Set.eq_univ_of_forall
      intro a
      by_contra ha
      exact hh ⟨a, ha⟩
    obtain ⟨a, ha⟩ := hWitness
    let z : D := ⟨.inl a.val, a.property⟩
    have hzNot : z ∉ R := by
      intro hz
      have hSelf : a.val ∈
          reconstructedSupport G k B (.inl a.val) :=
        B.mem_closureAtSet a.val
      have hImage : a.val ∈ UR := hz hSelf
      obtain ⟨b, hb, heq⟩ := hImage
      have hba : b = a := Subtype.ext heq
      exact ha (hba ▸ hb)
    intro hAll
    apply hzNot
    rw [hAll]
    exact Set.mem_univ _
  let dD : (A.induce D hD).FreeDecomposition :=
    { left := L
      right := R
      left_closed := hLeftClosed
      right_closed := hRightClosed
      cover := hCover
      left_proper := hLeftProper
      right_proper := hRightProper
      rel_local := by
        intro n F xs hRel
        cases F with
        | edge =>
            have hEdge :
                ReconstructedEdge G k B (xs 0).val (xs 1).val := hRel
            have hAntitone :
                reconstructedSupport G k B (xs 1).val ⊆
                  reconstructedSupport G k B (xs 0).val :=
              faithful_reconstructedEdge_support_antitone
                G k S B ι hFaith hEdge
            rcases hSupportSides (xs 0) with hL | hR
            · left
              intro i
              fin_cases i
              · exact hL
              · exact hAntitone.trans hL
            · right
              intro i
              fin_cases i
              · exact hR
              · exact hAntitone.trans hR
      func_cross_empty := by
        intro n F xs hCross
        ext z
        constructor
        · intro hz
          have hNotMixed :
              (∀ i, xs i ∈ L) ∨ (∀ i, xs i ∈ R) := by
            cases F with
            | successor =>
                rcases hSupportSides (xs 0) with hL | hR
                · left
                  intro i
                  fin_cases i
                  exact hL
                · right
                  intro i
                  fin_cases i
                  exact hR
            | fiber n hpos =>
                have hFibre :
                    z.val ∈ H.dFiber k (fun i => (xs i).val) := hz
                have hTupleRoots :
                    H.roots k z.val =
                      Set.range (fun i => (xs i).val) :=
                  H.roots_eq_range_of_mem_dFiber k hFibre
                have hSmall (i : Fin n) :
                    reconstructedSupport G k B (xs i).val ⊆
                      reconstructedSupport G k B z.val := by
                  have hRoot : (xs i).val ∈ H.roots k z.val := by
                    rw [hTupleRoots]
                    exact ⟨i, rfl⟩
                  exact faithful_reconstructed_reaches_support_antitone
                    G k S B ι hFaith hRoot.2
                rcases hSupportSides z with hL | hR
                · left
                  intro i
                  exact (hSmall i).trans hL
                · right
                  intro i
                  exact (hSmall i).trans hR
          exact (hCross hNotMixed).elim
        · intro hz
          exact (Set.not_mem_empty _ hz).elim }
  letI : IsEmpty ((A.induce D hD).FreeDecomposition) := hIrr
  exact isEmptyElim dD

end AllThoseEPPA.Applications.KOrientations
