import AllThoseEPPA.Applications.KOrientations.FaithfulSuccessorExact

/-!
# The faithful first-stage witness retains the outdegree bound

An arbitrary unrestricted EPPA witness need not have bounded outdegree.
However, in the irreducible-structure-faithful witness, the complete
outneighbourhood of any vertex lies in its one-point closure.
Move that closure by one automorphism to the distinguished copy of
the source graph. This gives an injection of outneighbours into the
outneighbours of one source vertex, so the cardinality is bounded by k.

The proof uses actual finite cardinals, not an assumed degree bound.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Each faithful first-stage witness graph inherits the source
outdegree bound, despite being built by unrestricted EPPA. -/
theorem faithful_outdegree_le
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β]
    (G : Digraph α) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι) :
    (faithfulWitnessDigraph G B ι hFaith).HasOutdegreeAtMost k := by
  classical
  intro x
  let H : Digraph β := faithfulWitnessDigraph G B ι hFaith
  obtain ⟨g, hmove⟩ :=
    faithful_moves_vertexClosure successorAction
      (successorStructure G) B ι hFaith x
  obtain ⟨a, ha⟩ := hmove x (B.mem_closureAtSet x)
  let s : Finset β := H.outNeighbors x
  let t : Finset α := G.outNeighbors a
  have htarget (y : s) :
      ∃ b : α, b ∈ t ∧ g y.1 = ι b := by
    have hedge : B.rel EdgeSymbol.edge ![x, y.1] := by
      change H.edge x y.1
      exact (H.mem_outNeighbors x y.1).mp y.2
    have hyF :
        y.1 ∈ B.func SuccessorSymbol.successor ![x] :=
      faithful_edge_mem_successors G B ι hFaith hedge
    obtain ⟨b, hb⟩ :=
      hmove y.1 (successorValue_subset_closureAt B x hyF)
    have hRel :
        B.rel EdgeSymbol.edge ![g x, g y.1] := by
      have hg := (Structure.Automorphism.map_rel_iff
          g EdgeSymbol.edge ![x, y.1]).2 hedge
      have htup : (g ∘ ![x, y.1]) = ![g x, g y.1] := by
        funext i
        fin_cases i <;> rfl
      rw [htup] at hg
      simpa only [successorAction_on_edge] using hg
    have hEdgeSource : G.edge a b := by
      have hCopy : B.rel EdgeSymbol.edge ![ι a, ι b] := by
        simpa only [ha, hb] using hRel
      have htup : (ι.toFun ∘ ![a, b]) = ![ι a, ι b] := by
        funext i
        fin_cases i <;> rfl
      have hSource :=
        (ι.map_rel_iff EdgeSymbol.edge ![a, b]).1 (by
          simpa only [successorAction_on_edge, htup] using hCopy)
      exact hSource
    exact ⟨b, (G.mem_outNeighbors a b).2 hEdgeSource, hb⟩
  let f : s → t :=
    fun y => ⟨Classical.choose (htarget y),
      (Classical.choose_spec (htarget y)).1⟩
  have heq (y : s) : g y.1 = ι (f y).1 :=
    (Classical.choose_spec (htarget y)).2
  have hinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    apply g.toEquiv.injective
    calc
      g y.1 = ι (f y).1 := heq y
      _ = ι (f z).1 := by rw [hyz]
      _ = g z.1 := (heq z).symm
  have hcard : Fintype.card s ≤ Fintype.card t :=
    Fintype.card_le_of_injective f hinj
  change (H.outNeighbors x).card ≤ k
  calc
    (H.outNeighbors x).card = Fintype.card s :=
      (Fintype.card_coe s).symm
    _ ≤ Fintype.card t := hcard
    _ = (G.outNeighbors a).card := Fintype.card_coe t
    _ ≤ k := hBound a

end AllThoseEPPA.Applications.KOrientations
