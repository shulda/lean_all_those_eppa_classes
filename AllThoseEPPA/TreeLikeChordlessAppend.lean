import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Combining chordless walks

Two chordless walks can be concatenated without introducing new chords
provided every graph edge between the two supports already belongs to
one of the original walks.

This abstracts the cross-component analysis in the chordal
clique-separator proof. The disjoint-components hypotheses will later
be used to establish the condition about cross edges.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- The concatenation of two chordless walks is chordless when
every cross-support edge is already an edge of one of the walks. -/
theorem chordless_append_of_cross_edges
    (G : SimpleGraph V) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w)
    (hp : p.IsChordless) (hq : q.IsChordless)
    (hCross : ∀ a b : V,
      a ∈ p.support → b ∈ q.support → G.Adj a b →
        s(a,b) ∈ p.edges ∨ s(a,b) ∈ q.edges) :
    (p.append q).IsChordless := by
  apply SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mpr
  intro a b ha hb hab
  have ha' := (SimpleGraph.Walk.mem_support_append_iff p q).mp ha
  have hb' := (SimpleGraph.Walk.mem_support_append_iff p q).mp hb
  have he : s(a,b) ∈ p.edges ∨ s(a,b) ∈ q.edges := by
    rcases ha' with hap | haq
    · rcases hb' with hbp | hbq
      · exact Or.inl
          ((SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hp)
            hap hbp hab)
      · exact hCross a b hap hbq hab
    · rcases hb' with hbp | hbq
      · rcases hCross b a hbp haq hab.symm with heP | heQ
        · exact Or.inl (by
            simpa only [show s(b,a) = s(a,b) from Sym2.eq_swap]
              using heP)
        · exact Or.inr (by
            simpa only [show s(b,a) = s(a,b) from Sym2.eq_swap]
              using heQ)
      · exact Or.inr
          ((SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hq)
            haq hbq hab)
  simpa only [SimpleGraph.Walk.edges_append, List.mem_append] using he

end TreeLike
end AllThoseEPPA
