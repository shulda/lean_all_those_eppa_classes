import AllThoseEPPA.Applications.KOrientations.FaithfulOutdegree
import AllThoseEPPA.Applications.KOrientations.FirstWitness

/-!
# Package the first EPPA witness back into the exact successor class

The unrestricted faithful coherent EPPA theorem yields a structure B
in the unary successor language, not directly a k-orientation.
The preceding local proofs show its edge reduct is a k-orientation
and its entire unary function agrees with that graph's reachability.

We now combine those facts into an actual KOrientation object
and prove equality (not just a one-way homomorphism) with its
canonical successor expansion.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The concrete k-orientation underlying a finite faithful
successor-language witness. -/
def faithfulWitnessKOrientation
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β]
    (G : Digraph α) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι) :
    KOrientation β k where
  graph := faithfulWitnessDigraph G B ι hFaith
  bound := faithful_outdegree_le G k hBound B ι hFaith

/-- Structure extensionality for the two arity-indexed interpretation
functions, with no assumption on the language. -/
private theorem structure_eq_of_fields
    {L : Language} {V : Type v}
    (A C : Structure L V)
    (hRel : ∀ (n : ℕ) (R : L.RelSymbol n) (xs : Fin n → V),
      A.rel R xs = C.rel R xs)
    (hFunc : ∀ (n : ℕ) (F : L.FuncSymbol n) (xs : Fin n → V),
      A.func F xs = C.func F xs) :
    A = C := by
  cases A with
  | mk rA fA =>
    cases C with
    | mk rC fC =>
      -- Direct congruence keeps the implicit arity binder of each
      -- dependent interpretation function in scope.
      congr 1
      · funext n R xs
        exact hRel n R xs
      · funext n F xs
        exact hFunc n F xs

/-- Exact class membership: the raw first EPPA witness is precisely
the canonical successor structure of its reconstructed k-orientation.
This identity is used to transport the original coherent extension
data without changing any vertex set or relation/function value. -/
theorem faithfulWitness_eq_successorStructure
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β]
    (G : Digraph α) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι) :
    B = successorStructure
      (faithfulWitnessKOrientation G k hBound B ι hFaith).graph := by
  let H := faithfulWitnessKOrientation G k hBound B ι hFaith
  have hRel :
      ∀ (n : ℕ) (R : successorLanguage.RelSymbol n) (xs : Fin n → β),
        B.rel R xs = (successorStructure H.graph).rel R xs := by
    intro n R xs
    cases R with
    | edge =>
        have htup : xs = ![xs 0, xs 1] := by
          funext i
          fin_cases i <;> rfl
        rw [htup]
        rfl
  have hFunc :
      ∀ (n : ℕ) (F : successorLanguage.FuncSymbol n) (xs : Fin n → β),
        B.func F xs = (successorStructure H.graph).func F xs := by
    intro n F xs
    cases F with
    | successor =>
        change B.func SuccessorSymbol.successor xs =
          (faithfulWitnessDigraph G B ι hFaith).successors (xs 0)
        have htup : xs = ![xs 0] := by
          funext i
          fin_cases i
          rfl
        rw [htup]
        simpa only [Matrix.cons_val_zero] using
          faithful_successor_eq_graph_reach G B ι hFaith (xs 0)
  exact structure_eq_of_fields B (successorStructure H.graph) hRel hFunc

/-- A coherent, irreducible-structure faithful first EPPA witness,
explicitly accompanied by a k-orientation whose successor
expansion is *equal* to the witness structure. -/
theorem exists_firstStageKOrientationWitness
    {α : Type u} [Fintype α]
    (G : Digraph α) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k) :
    ∃ (β : Type u) (_ : Fintype β)
      (H : KOrientation β k)
      (B : Structure successorLanguage β)
      (ι : Structure.Embedding successorAction (successorStructure G) B),
      B = successorStructure H.graph ∧
      Structure.IsCoherentEPPAWitness successorAction ι ∧
      Structure.IsIrreducibleStructureFaithful successorAction ι := by
  classical
  obtain ⟨β, hβ, B, ι, hCoherent, hFaith⟩ :=
    exists_firstStageUnrestrictedWitness G
  letI : Fintype β := Fintype.ofFinite β
  let H : KOrientation β k :=
    faithfulWitnessKOrientation G k hBound B ι hFaith
  refine ⟨β, inferInstance, H, B, ι, ?_, hCoherent, hFaith⟩
  exact faithfulWitness_eq_successorStructure G k hBound B ι hFaith

end AllThoseEPPA.Applications.KOrientations
