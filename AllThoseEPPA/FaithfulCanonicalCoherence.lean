import AllThoseEPPA.FaithfulEPPA

/-!
# Coherence of pushing partial automorphisms to the canonical faithful copy
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Membership in the source of the canonical pushed partial automorphism. -/
theorem mem_canonicalPartialAutomorphism_source_iff
    (p : Structure.PartialAutomorphism act A)
    (x : WitnessVertex act A B₀ ψ) :
    x ∈ (canonicalPartialAutomorphism act A B₀ ψ p).source ↔
      ∃ a : α, a ∈ p.source ∧
        x = canonicalVertex act A B₀ ψ a := by
  constructor
  · intro hx
    have hx' :
        x ∈ canonicalPartialSourceSet act A B₀ ψ p := by
      simpa [canonicalPartialAutomorphism] using hx
    rcases hx' with ⟨a, hax⟩
    refine ⟨a.1, a.2, ?_⟩
    change canonicalVertex act A B₀ ψ a.1 = x at hax
    exact hax.symm
  · rintro ⟨a, ha, rfl⟩
    have hm :=
      canonicalVertex_mem_partialSource
        act A B₀ ψ p a ha
    simpa [canonicalPartialAutomorphism] using hm

/-- Membership in the target of the canonical pushed partial automorphism. -/
theorem mem_canonicalPartialAutomorphism_target_iff
    (p : Structure.PartialAutomorphism act A)
    (x : WitnessVertex act A B₀ ψ) :
    x ∈ (canonicalPartialAutomorphism act A B₀ ψ p).target ↔
      ∃ a : α, a ∈ p.target ∧
        x = canonicalVertex act A B₀ ψ a := by
  let P :=
    canonicalPartialAutomorphism act A B₀ ψ p
  constructor
  · intro hx
    let y : WitnessVertex act A B₀ ψ :=
      P.toPartialEquiv.symm x
    have hy : y ∈ P.source :=
      P.toPartialEquiv.symm.map_source hx
    rcases
        (mem_canonicalPartialAutomorphism_source_iff
          act A B₀ ψ p y).1 hy with
      ⟨a, ha, hya⟩
    have hPx : P y = x :=
      P.right_inv hx
    refine ⟨p a, p.map_source ha, ?_⟩
    calc
      x = P y := hPx.symm
      _ = P (canonicalVertex act A B₀ ψ a) := by
        rw [hya]
      _ = canonicalVertex act A B₀ ψ (p a) := by
        simpa [P] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ p a ha)
  · rintro ⟨a, ha, rfl⟩
    let b : α := p.toPartialEquiv.symm a
    have hb : b ∈ p.source :=
      p.toPartialEquiv.symm.map_source ha
    have hsrc :
        canonicalVertex act A B₀ ψ b ∈ P.source := by
      simpa [P] using
        (mem_canonicalPartialAutomorphism_source_iff
          act A B₀ ψ p
          (canonicalVertex act A B₀ ψ b)).2
          ⟨b, hb, rfl⟩
    have htgt :
        P (canonicalVertex act A B₀ ψ b) ∈ P.target :=
      P.map_source hsrc
    have hba : p b = a :=
      p.right_inv ha
    have hPba :
        P (canonicalVertex act A B₀ ψ b) =
          canonicalVertex act A B₀ ψ a := by
      calc
        P (canonicalVertex act A B₀ ψ b) =
            canonicalVertex act A B₀ ψ (p b) := by
          simpa [P] using
            (canonicalPartialAutomorphism_apply
              act A B₀ ψ p b hb)
        _ = canonicalVertex act A B₀ ψ a :=
          congrArg (canonicalVertex act A B₀ ψ) hba
    rw [hPba] at htgt
    exact htgt

/-- Equivalent partial automorphisms remain equivalent after pushing them to
the canonical copy. -/
theorem canonicalPartialAutomorphism_equivalent
    (p q : Structure.PartialAutomorphism act A)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    Structure.PartialIsomorphism.Equivalent
      (canonicalPartialAutomorphism act A B₀ ψ p)
      (canonicalPartialAutomorphism act A B₀ ψ q) := by
  constructor
  · rw [canonicalPartialAutomorphism_lang,
      canonicalPartialAutomorphism_lang,
      hpq.1]
  · refine ⟨?_, ?_⟩
    · ext x
      constructor
      · intro hx
        rcases
            (mem_canonicalPartialAutomorphism_source_iff
              act A B₀ ψ p x).1 hx with
          ⟨a, ha, hxa⟩
        have haq : a ∈ q.source := by
          change a ∈ q.toPartialEquiv.source
          change a ∈ p.toPartialEquiv.source at ha
          rw [← hpq.2.1]
          exact ha
        exact
          (mem_canonicalPartialAutomorphism_source_iff
            act A B₀ ψ q x).2
            ⟨a, haq, hxa⟩
      · intro hx
        rcases
            (mem_canonicalPartialAutomorphism_source_iff
              act A B₀ ψ q x).1 hx with
          ⟨a, ha, hxa⟩
        have hap : a ∈ p.source := by
          change a ∈ p.toPartialEquiv.source
          change a ∈ q.toPartialEquiv.source at ha
          rw [hpq.2.1]
          exact ha
        exact
          (mem_canonicalPartialAutomorphism_source_iff
            act A B₀ ψ p x).2
            ⟨a, hap, hxa⟩
    · intro x hx
      rcases
          (mem_canonicalPartialAutomorphism_source_iff
            act A B₀ ψ p x).1 hx with
        ⟨a, ha, hxa⟩
      have haq : a ∈ q.source := by
        change a ∈ q.toPartialEquiv.source
        change a ∈ p.toPartialEquiv.source at ha
        rw [← hpq.2.1]
        exact ha
      have hpqa : p a = q a :=
        hpq.2.2 ha
      rw [hxa,
        canonicalPartialAutomorphism_apply
          act A B₀ ψ p a ha,
        canonicalPartialAutomorphism_apply
          act A B₀ ψ q a haq,
        hpqa]

/-- If the target of `p` is the source of `q`, the same is true after
pushing both partial automorphisms to the canonical copy. -/
theorem canonicalPartialAutomorphism_target_eq_source
    (p q : Structure.PartialAutomorphism act A)
    (ht : p.target = q.source) :
    (canonicalPartialAutomorphism act A B₀ ψ p).target =
      (canonicalPartialAutomorphism act A B₀ ψ q).source := by
  ext x
  constructor
  · intro hx
    rcases
        (mem_canonicalPartialAutomorphism_target_iff
          act A B₀ ψ p x).1 hx with
      ⟨a, ha, hxa⟩
    have haq : a ∈ q.source := by
      rw [← ht]
      exact ha
    exact
      (mem_canonicalPartialAutomorphism_source_iff
        act A B₀ ψ q x).2
        ⟨a, haq, hxa⟩
  · intro hx
    rcases
        (mem_canonicalPartialAutomorphism_source_iff
          act A B₀ ψ q x).1 hx with
      ⟨a, ha, hxa⟩
    have hap : a ∈ p.target := by
      rw [ht]
      exact ha
    exact
      (mem_canonicalPartialAutomorphism_target_iff
        act A B₀ ψ p x).2
        ⟨a, hap, hxa⟩

/-- Coherent triples remain coherent after pushing them to the canonical
faithful copy. -/
theorem canonicalPartialAutomorphism_coherentTriple
    (p q r : Structure.PartialAutomorphism act A)
    (hcoh :
      Structure.PartialIsomorphism.CoherentTriple p q r) :
    Structure.PartialIsomorphism.CoherentTriple
      (canonicalPartialAutomorphism act A B₀ ψ p)
      (canonicalPartialAutomorphism act A B₀ ψ q)
      (canonicalPartialAutomorphism act A B₀ ψ r) := by
  rcases hcoh with ⟨ht, heq⟩
  let P :=
    canonicalPartialAutomorphism act A B₀ ψ p
  let Q :=
    canonicalPartialAutomorphism act A B₀ ψ q
  let R :=
    canonicalPartialAutomorphism act A B₀ ψ r
  have ht' : P.target = Q.source := by
    simpa [P, Q] using
      (canonicalPartialAutomorphism_target_eq_source
        act A B₀ ψ p q ht)
  refine ⟨ht', ?_⟩
  constructor
  · have hlang : r.lang = q.lang * p.lang := by
      simpa [Structure.PartialIsomorphism.comp] using heq.1
    change R.lang = Q.lang * P.lang
    rw [show R.lang =
        ψ.lang * r.lang * ψ.lang⁻¹ by
      simpa [R] using
        (canonicalPartialAutomorphism_lang
          act A B₀ ψ r)]
    rw [show Q.lang =
        ψ.lang * q.lang * ψ.lang⁻¹ by
      simpa [Q] using
        (canonicalPartialAutomorphism_lang
          act A B₀ ψ q)]
    rw [show P.lang =
        ψ.lang * p.lang * ψ.lang⁻¹ by
      simpa [P] using
        (canonicalPartialAutomorphism_lang
          act A B₀ ψ p)]
    rw [hlang]
    simp [mul_assoc]
  · refine ⟨?_, ?_⟩
    · have hrs : r.source = p.source := by
        have hs := heq.2.1
        change r.toPartialEquiv.source =
          (p.toPartialEquiv.trans' q.toPartialEquiv ht).source at hs
        change r.toPartialEquiv.source = p.toPartialEquiv.source
        simpa [PartialEquiv.trans'] using hs
      change R.toPartialEquiv.source = P.toPartialEquiv.source
      ext x
      constructor
      · intro hx
        have hxR : x ∈ R.source := by
          exact hx
        rcases
            (mem_canonicalPartialAutomorphism_source_iff
              act A B₀ ψ r x).1
              (by simpa [R] using hxR) with
          ⟨a, ha, hxa⟩
        have hap : a ∈ p.source := by
          rw [← hrs]
          exact ha
        have hxP :
            x ∈
              (canonicalPartialAutomorphism
                act A B₀ ψ p).source :=
          (mem_canonicalPartialAutomorphism_source_iff
            act A B₀ ψ p x).2
            ⟨a, hap, hxa⟩
        change x ∈ P.toPartialEquiv.source
        change
          x ∈
            (canonicalPartialAutomorphism
              act A B₀ ψ p).toPartialEquiv.source at hxP
        simpa [P] using hxP
      · intro hx
        have hxP : x ∈ P.source := by
          exact hx
        rcases
            (mem_canonicalPartialAutomorphism_source_iff
              act A B₀ ψ p x).1
              (by simpa [P] using hxP) with
          ⟨a, ha, hxa⟩
        have har : a ∈ r.source := by
          rw [hrs]
          exact ha
        have hxR :
            x ∈
              (canonicalPartialAutomorphism
                act A B₀ ψ r).source :=
          (mem_canonicalPartialAutomorphism_source_iff
            act A B₀ ψ r x).2
            ⟨a, har, hxa⟩
        change x ∈ R.toPartialEquiv.source
        change
          x ∈
            (canonicalPartialAutomorphism
              act A B₀ ψ r).toPartialEquiv.source at hxR
        simpa [R] using hxR
    · intro x hx
      have hxR : x ∈ R.source := by
        exact hx
      rcases
          (mem_canonicalPartialAutomorphism_source_iff
            act A B₀ ψ r x).1
            (by simpa [R] using hxR) with
        ⟨a, ha, hxa⟩
      have hrs : r.source = p.source := by
        have hs := heq.2.1
        change r.toPartialEquiv.source =
          (p.toPartialEquiv.trans' q.toPartialEquiv ht).source at hs
        change r.toPartialEquiv.source = p.toPartialEquiv.source
        simpa [PartialEquiv.trans'] using hs
      have hap : a ∈ p.source := by
        rw [← hrs]
        exact ha
      have hpaq : p a ∈ q.source := by
        rw [← ht]
        exact p.map_source hap
      have hra : r a = q (p a) := by
        have h := heq.2.2 ha
        change r a = q (p a) at h
        exact h
      rw [hxa]
      change
        R (canonicalVertex act A B₀ ψ a) =
          Q (P (canonicalVertex act A B₀ ψ a))
      rw [show
          R (canonicalVertex act A B₀ ψ a) =
            canonicalVertex act A B₀ ψ (r a) by
        simpa [R] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ r a ha)]
      rw [show
          P (canonicalVertex act A B₀ ψ a) =
            canonicalVertex act A B₀ ψ (p a) by
        simpa [P] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ p a hap)]
      rw [show
          Q (canonicalVertex act A B₀ ψ (p a)) =
            canonicalVertex act A B₀ ψ (q (p a)) by
        simpa [Q] using
          (canonicalPartialAutomorphism_apply
            act A B₀ ψ q (p a) hpaq)]
      exact congrArg
        (canonicalVertex act A B₀ ψ) hra

end Faithful
end AllThoseEPPA
