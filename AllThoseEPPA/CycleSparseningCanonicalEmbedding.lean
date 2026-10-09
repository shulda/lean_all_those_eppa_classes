import AllThoseEPPA.CycleSparseningCanonical

/-!
# Canonical embedding for the cycle-sparsening witness

The original structure is embedded using the canonical valuation at every
vertex in its distinguished copy.  Both relations and unary function fibres
are preserved exactly.  This finishes Claim `c:cycles:emb`.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)

/-- A canonical witness vertex restricted along an original unary function
value is again the corresponding canonical witness vertex. -/
theorem canonical_functionValueVertex
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (a b : α) {n : ℕ} (F : L.FuncSymbol n)
    (hb : b ∈ A.func F (fun _ => a)) :
    functionValueVertex B₀ E
        (canonicalVertex act A B₀ ψ E hfix hcomplete a)
        (act.onFunc ψ.lang F) (ψ b)
        (Faithful.canonical_base_func_mem act A B₀ ψ a b F hb) =
      canonicalVertex act A B₀ ψ E hfix hcomplete b := by
  apply Sigma.ext rfl
  apply heq_of_eq
  change
    (canonicalValuationStructure act A B₀ ψ E
        hfix hcomplete a).restrict B₀ E (ψ b)
        (func_mem_closureAtSet B₀ (act.onFunc ψ.lang F)
          (Faithful.canonical_base_func_mem
            act A B₀ ψ a b F hb)) =
      canonicalValuationStructure act A B₀ ψ E hfix hcomplete b
  exact canonicalValuationStructure_restrict
    act A B₀ ψ E hfix hcomplete a b
    (func_mem_closureAtSet B₀ (act.onFunc ψ.lang F)
      (Faithful.canonical_base_func_mem act A B₀ ψ a b F hb))

/-- Claim `c:cycles:emb`: the canonical copy of the original structure
embeds in the cycle-sparsening witness and is generic. -/
noncomputable def canonicalEmbedding
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E) :
    Structure.Embedding act A (witnessStructure B₀ E) where
  lang := ψ.lang
  toFun := canonicalVertex act A B₀ ψ E hfix hcomplete
  injective := by
    intro a b hab
    apply ψ.injective
    exact congrArg Sigma.fst hab
  map_rel_iff := by
    intro n R xs
    constructor
    · intro hrel
      apply (ψ.map_rel_iff R xs).1
      simpa [canonicalVertex, WitnessVertex.base,
        Function.comp_def] using hrel.1
    · intro hrel
      refine ⟨?_, ?_⟩
      · have hb := (ψ.map_rel_iff R xs).2 hrel
        simpa [canonicalVertex, WitnessVertex.base,
          Function.comp_def] using hb
      · simpa [Function.comp_def] using
          (canonicalFamilyGeneric
            act A B₀ ψ E hfix hcomplete xs)
  map_func := by
    intro n F xs
    have hxs :
        xs = fun _ => xs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F xs
    rw [hxs]
    let a := xs (UnaryFunctions.unaryIndex F)
    ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb₀ :=
        Faithful.canonical_base_func_mem act A B₀ ψ a b F hb
      change
        ∃ (y : β)
          (hy :
            y ∈ B₀.func (act.onFunc ψ.lang F)
                (fun _ =>
                  (canonicalVertex act A B₀ ψ E
                    hfix hcomplete a).base)),
          canonicalVertex act A B₀ ψ E hfix hcomplete b =
            functionValueVertex B₀ E
              (canonicalVertex act A B₀ ψ E hfix hcomplete a)
              (act.onFunc ψ.lang F) y hy
      refine ⟨ψ b, ?_, ?_⟩
      · simpa [canonicalVertex, WitnessVertex.base] using hb₀
      · exact (canonical_functionValueVertex
          act A B₀ ψ E hfix hcomplete a b F hb).symm
    · intro hz
      change
        ∃ (y : β)
          (hy :
            y ∈ B₀.func (act.onFunc ψ.lang F)
                (fun _ =>
                  (canonicalVertex act A B₀ ψ E
                    hfix hcomplete a).base)),
          z =
            functionValueVertex B₀ E
              (canonicalVertex act A B₀ ψ E hfix hcomplete a)
              (act.onFunc ψ.lang F) y hy at hz
      rcases hz with ⟨y, hy, rfl⟩
      have hy' :
          y ∈ B₀.func (act.onFunc ψ.lang F)
              (ψ.toFun ∘ fun _ => a) := by
        simpa [canonicalVertex, WitnessVertex.base,
          Function.comp_def] using hy
      rw [← ψ.map_func F (fun _ => a)] at hy'
      rcases hy' with ⟨b, hb, hby⟩
      subst y
      refine ⟨b, hb, ?_⟩
      exact (canonical_functionValueVertex
        act A B₀ ψ E hfix hcomplete a b F hb).symm

end Sparsening
end AllThoseEPPA
