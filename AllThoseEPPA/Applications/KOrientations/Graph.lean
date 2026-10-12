import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

/-!
# Directed graph core for \(k\)-orientations with \(d\)-closures

A separate application module for Section \`sec:orientations\` of
*All those EPPA classes*.

This is the first, graph-theoretic layer. We deliberately distinguish the
graph relation, reflexive directed reachability, the out-degree bound,
root status, and the set of reachable roots. Later modules encode the
set-valued successor function and the higher-arity \(d\)-closure functions.

No EPPA conclusion is postulated here.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A directed graph with neither loops nor antiparallel edges. -/
structure Digraph (V : Type u) where
  edge : V → V → Prop
  asymmetric : ∀ {x y : V}, edge x y → ¬ edge y x

namespace Digraph

variable {V : Type u} (G : Digraph V)

/-- Directed reachability, including a path of length zero. -/
inductive Reaches (G : Digraph V) : V → V → Prop where
  | refl (x : V) : Reaches G x x
  | step {x y z : V} : G.edge x y → Reaches G y z → Reaches G x z

theorem edge_irrefl (x : V) : ¬ G.edge x x := by
  intro h
  exact (G.asymmetric h) h

theorem reaches_refl (x : V) : G.Reaches x x :=
  Reaches.refl x

theorem reaches_of_edge {x y : V} (h : G.edge x y) :
    G.Reaches x y :=
  Reaches.step h (Reaches.refl y)

/-- Concatenation of two directed paths. -/
theorem reaches_trans {x y z : V}
    (hxy : G.Reaches x y) (hyz : G.Reaches y z) :
    G.Reaches x z := by
  induction hxy with
  | refl _ =>
      exact hyz
  | step h _ ih =>
      exact Reaches.step h ih

/-- The successor set in the paper, including the argument itself. -/
def successors (x : V) : Set V :=
  {y | G.Reaches x y}

theorem mem_successors_iff {x y : V} :
    y ∈ G.successors x ↔ G.Reaches x y :=
  Iff.rfl

theorem self_mem_successors (x : V) :
    x ∈ G.successors x :=
  G.reaches_refl x

theorem successors_antitone {x y : V} (h : G.Reaches x y) :
    G.successors y ⊆ G.successors x := by
  intro z hz
  exact G.reaches_trans h hz

/-- Actual outgoing neighbours (not transitive successors). -/
noncomputable def outNeighbors [Fintype V] (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => G.edge x y)

@[simp] theorem mem_outNeighbors [Fintype V] (x y : V) :
    y ∈ G.outNeighbors x ↔ G.edge x y := by
  classical
  simp [outNeighbors]

/-- Out-degree is at most \(k\), uniformly over all vertices. -/
def HasOutdegreeAtMost [Fintype V] (k : ℕ) : Prop :=
  ∀ x : V, (G.outNeighbors x).card ≤ k

/-- A root is a vertex of out-degree strictly smaller than \(k\). -/
def IsRoot [Fintype V] (k : ℕ) (x : V) : Prop :=
  (G.outNeighbors x).card < k

theorem degree_eq_of_not_root [Fintype V] (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k) {x : V}
    (hNot : ¬ G.IsRoot k x) :
    (G.outNeighbors x).card = k := by
  change ¬ (G.outNeighbors x).card < k at hNot
  exact le_antisymm (hBound x) (Nat.le_of_not_lt hNot)

/-- Roots reachable from a vertex by a path of length ≥ 0. -/
def roots [Fintype V] (k : ℕ) (x : V) : Set V :=
  {r | G.IsRoot k r ∧ G.Reaches x r}

@[simp] theorem mem_roots_iff [Fintype V] (k : ℕ)
    (x r : V) :
    r ∈ G.roots k x ↔ G.IsRoot k r ∧ G.Reaches x r :=
  Iff.rfl

theorem root_mem_own_roots [Fintype V] (k : ℕ)
    {x : V} (hx : G.IsRoot k x) :
    x ∈ G.roots k x :=
  ⟨hx, G.reaches_refl x⟩

/-- All root sets are nonempty: the \(s^+\)-assumption of the paper. -/
def HasReachableRoots [Fintype V] (k : ℕ) : Prop :=
  ∀ x : V, (G.roots k x).Nonempty

/-- Following an oriented path can only decrease the reachable-root set. -/
theorem roots_antitone [Fintype V] (k : ℕ) {x y : V}
    (h : G.Reaches x y) :
    G.roots k y ⊆ G.roots k x := by
  intro r hr
  exact ⟨hr.1, G.reaches_trans h hr.2⟩

theorem roots_antitone_edge [Fintype V] (k : ℕ)
    {x y : V} (h : G.edge x y) :
    G.roots k y ⊆ G.roots k x :=
  G.roots_antitone k (G.reaches_of_edge h)

end Digraph

/-- A concrete finite \(k\)-orientation, still without the rootedness
assumption needed for the \(d\)-expansion. -/
structure KOrientation (V : Type u) [Fintype V] (k : ℕ) where
  graph : Digraph V
  bound : graph.HasOutdegreeAtMost k

end AllThoseEPPA.Applications.KOrientations
