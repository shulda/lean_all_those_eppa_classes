import AllThoseEPPA.TreeLikeGraphInterface
import AllThoseEPPA.CycleSparseningCycleGraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Lean.Elab.Tactic.Omega

/-!
# Translate chordless graph cycles into the sparsening BadCycleSequence API

The structural EPPA construction already formalizes forbidden induced
cycles as `Structure.BadCycleSequence`, indexed by `Fin k`. The chordal
graph argument naturally constructs closed graph walks carrying
`SimpleGraph.Walk.IsCycle` and `IsChordless` certificates.

This file proves the exact conversion of an induced simple graph cycle
of length at least four into a `BadCycleSequence`. It is essential:
otherwise a Mathlib chordless cycle does not by itself contradict
the no-induced-cycle branch of `lem:sparsen`.

The proof:
* takes the first `k` vertices of the closed walk;
* obtains their injectivity from `IsCycle.getVert_injOn'`;
* uses `IsChordless` and `Walk.mk_mem_edges_iff_exists` to identify
  all graph edges among them with cyclic successor pairs; and
* treats the last-to-first wrap using `Walk.getVert_length`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- On a nonempty closed walk, the successor vertex is the vertex
at the successor index modulo the length, even at the final edge. -/
theorem closedWalk_getVert_succ_mod
    (G : SimpleGraph V) {u : V}
    (p : G.Walk u u) (k : ℕ)
    (hk : k < p.length) :
    p.getVert (k + 1) =
      p.getVert ((k + 1) % p.length) := by
  by_cases hnext : k + 1 < p.length
  · rw [Nat.mod_eq_of_lt hnext]
  · have heq : k + 1 = p.length := by omega
    rw [heq, Nat.mod_self]
    simp only [SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero]

variable {L : Language} (B : Structure L V) (E : L.RelSymbol 2)

/-- **Cycle-API bridge.** A chordless Mathlib cycle of length at
least four is a forbidden induced E-cycle in our sparsening API. -/
def badCycleOfChordlessGraphCycle
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    {u : V}
    (p : (distinguishedGraph B E hloop hsymm).Walk u u)
    (hcyc : p.IsCycle)
    (hchord : p.IsChordless)
    (hfour : 4 ≤ p.length) :
    Structure.BadCycleSequence B E := by
  let G : SimpleGraph V := distinguishedGraph B E hloop hsymm
  refine
    { length := p.length
      length_ge_four := hfour
      vertex := fun i => p.getVert i.val
      injective := ?_
      edge_iff := ?_ }
  · intro i j heq
    apply Fin.ext
    exact hcyc.getVert_injOn'
      (Nat.le_sub_one_of_lt i.isLt)
      (Nat.le_sub_one_of_lt j.isLt) heq
  · intro i j
    change G.Adj (p.getVert i.val) (p.getVert j.val) ↔
      Structure.CyclicAdjacent i j
    constructor
    · intro hadj
      have hiMem : p.getVert i.val ∈ p.support :=
        p.getVert_mem_support i.val
      have hjMem : p.getVert j.val ∈ p.support :=
        p.getVert_mem_support j.val
      have hedge : s(p.getVert i.val,p.getVert j.val) ∈ p.edges :=
        (SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hchord)
          hiMem hjMem hadj
      obtain ⟨k, hk, hEdge⟩ :=
        (SimpleGraph.Walk.mk_mem_edges_iff_exists p).mp hedge
      have hmod :
          p.getVert (k + 1) =
            p.getVert ((k + 1) % p.length) :=
        closedWalk_getVert_succ_mod G p k hk
      have hmodLt : (k + 1) % p.length < p.length :=
        Nat.mod_lt _ (by omega)
      rcases (Sym2.eq_iff.mp hEdge) with
          ⟨hkI, hkJ⟩ | ⟨hkJ, hkI⟩
      · have hki : k = i.val :=
          hcyc.getVert_injOn'
            (Nat.le_sub_one_of_lt hk) (Nat.le_sub_one_of_lt i.isLt) hkI
        have hkj : (k + 1) % p.length = j.val :=
          hcyc.getVert_injOn'
            (Nat.le_sub_one_of_lt hmodLt) (Nat.le_sub_one_of_lt j.isLt)
            (hmod.symm.trans hkJ)
        left
        change j.val = (i.val + 1) % p.length
        simpa only [← hki] using hkj.symm
      · have hkj : k = j.val :=
          hcyc.getVert_injOn'
            (Nat.le_sub_one_of_lt hk) (Nat.le_sub_one_of_lt j.isLt) hkJ
        have hki : (k + 1) % p.length = i.val :=
          hcyc.getVert_injOn'
            (Nat.le_sub_one_of_lt hmodLt) (Nat.le_sub_one_of_lt i.isLt)
            (hmod.symm.trans hkI)
        right
        change i.val = (j.val + 1) % p.length
        simpa only [← hkj] using hki.symm
    · intro hidx
      rcases hidx with hij | hji
      · change j.val = (i.val + 1) % p.length at hij
        have hiEdge : G.Adj (p.getVert i.val)
            (p.getVert (i.val + 1)) :=
          p.adj_getVert_succ i.isLt
        have hmod := closedWalk_getVert_succ_mod G p i.val i.isLt
        rw [hmod, ← hij] at hiEdge
        exact hiEdge
      · change i.val = (j.val + 1) % p.length at hji
        have hjEdge : G.Adj (p.getVert j.val)
            (p.getVert (j.val + 1)) :=
          p.adj_getVert_succ j.isLt
        have hmod := closedWalk_getVert_succ_mod G p j.val j.isLt
        rw [hmod, ← hji] at hjEdge
        exact hjEdge.symm

/-- In particular, if the E-structure has no bad induced cycles,
no chordless graph cycle of length at least four can exist. -/
theorem no_chordless_long_graph_cycle
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    {u : V}
    (p : (distinguishedGraph B E hloop hsymm).Walk u u)
    (hcyc : p.IsCycle)
    (hchord : p.IsChordless) :
    p.length < 4 := by
  by_contra hn
  exact hNo (badCycleOfChordlessGraphCycle
    B E hloop hsymm p hcyc hchord (by omega))

end TreeLike
end AllThoseEPPA
