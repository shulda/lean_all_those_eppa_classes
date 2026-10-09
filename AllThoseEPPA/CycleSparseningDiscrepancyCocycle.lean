import AllThoseEPPA.CycleSparseningSwitchSupport

/-!
# Cocycle identity for a prescribed Boolean correction

Once a partial automorphism and a compatible base map are fixed, every
source vertex on a bad cycle gives the discrepancy between its centre bit
and the target centre bit. Under composition these three bits telescope.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Centre bits are invariant under equal witness vertices and equal
indexed cycles, regardless of the proofs of cycle membership. -/
theorem centerBit_congr_vertex_cycle
    {x y : WitnessVertex B₀ E}
    (hxy : x = y)
    {c d : Structure.BadCycleSequence B₀ E}
    (hcd : c = d)
    (hx : x.base B₀ E ∈ c.carrier)
    (hy : y.base B₀ E ∈ d.carrier) :
    centerBit B₀ E x c hx = centerBit B₀ E y d hy := by
  subst y
  subst d
  rfl

/-- Pointwise discrepancies of composable partial automorphisms satisfy
the XOR cocycle identity, with the second discrepancy indexed by the
transported cycle. -/
theorem bitDiscrepancy_comp_of_source
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (ht : p.target = q.source)
    (hcp : BaseCompatible act B₀ E p gp)
    (hcq : BaseCompatible act B₀ E q gq)
    (hcomp : BaseCompatible act B₀ E (q.comp p ht) (gq.comp gp))
    (x : WitnessVertex B₀ E) (hx : x ∈ p.source)
    (c : Structure.BadCycleSequence B₀ E)
    (hxc : x.base B₀ E ∈ c.carrier) :
    let hxr : x ∈ (q.comp p ht).source :=
      (mem_comp_source_iff act B₀ E p q ht x).2 hx
    let hpx : p x ∈ q.source := by
      rw [← ht]
      exact p.map_source hx
    let hpxc : (p x).base B₀ E ∈ (c.transport gp hfix).carrier := by
      rw [← hcp.2 x hx]
      exact (Structure.BadCycleSequence.mem_transport_carrier_iff
        c gp hfix (x.base B₀ E)).2 hxc
    bitDiscrepancy act B₀ E (q.comp p ht) (gq.comp gp)
        hfix hcomp x hxr c hxc =
      (bitDiscrepancy act B₀ E p gp hfix hcp x hx c hxc !=
       bitDiscrepancy act B₀ E q gq hfix hcq
         (p x) hpx (c.transport gp hfix) hpxc) := by
  dsimp
  let hxr : x ∈ (q.comp p ht).source :=
    (mem_comp_source_iff act B₀ E p q ht x).2 hx
  let hpx : p x ∈ q.source := by
    rw [← ht]
    exact p.map_source hx
  let hpxc : (p x).base B₀ E ∈ (c.transport gp hfix).carrier := by
    rw [← hcp.2 x hx]
    exact (Structure.BadCycleSequence.mem_transport_carrier_iff
      c gp hfix (x.base B₀ E)).2 hxc
  let hqpc : (q (p x)).base B₀ E ∈
      ((c.transport gp hfix).transport gq hfix).carrier := by
    rw [← hcq.2 (p x) hpx]
    exact (Structure.BadCycleSequence.mem_transport_carrier_iff
      (c.transport gp hfix) gq hfix ((p x).base B₀ E)).2 hpxc
  let a : Bool := centerBit B₀ E x c hxc
  let b : Bool := centerBit B₀ E (p x) (c.transport gp hfix) hpxc
  let d : Bool := centerBit B₀ E (q (p x))
      ((c.transport gp hfix).transport gq hfix) hqpc
  have hcompAct : (q.comp p ht) x = q (p x) := rfl
  have hcompCycle :
      c.transport (gq.comp gp) hfix =
        (c.transport gp hfix).transport gq hfix :=
    (Structure.BadCycleSequence.transport_comp c gq gp hfix).symm
  have hcompMem :
      ((q.comp p ht) x).base B₀ E ∈
        (c.transport (gq.comp gp) hfix).carrier := by
    rw [← hcomp.2 x hxr]
    exact (Structure.BadCycleSequence.mem_transport_carrier_iff
      c (gq.comp gp) hfix (x.base B₀ E)).2 hxc
  have hcenter :
      centerBit B₀ E ((q.comp p ht) x)
        (c.transport (gq.comp gp) hfix) hcompMem = d := by
    exact centerBit_congr_vertex_cycle B₀ E
      hcompAct hcompCycle hcompMem hqpc
  have hr :
      bitDiscrepancy act B₀ E (q.comp p ht) (gq.comp gp)
        hfix hcomp x hxr c hxc = (a != d) := by
    change
      (centerBit B₀ E x c hxc !=
        centerBit B₀ E ((q.comp p ht) x)
          (c.transport (gq.comp gp) hfix) hcompMem) = (a != d)
    exact congrArg (fun t : Bool => a != t) hcenter
  have hp :
      bitDiscrepancy act B₀ E p gp hfix hcp x hx c hxc =
        (a != b) := by
    rfl
  have hq :
      bitDiscrepancy act B₀ E q gq hfix hcq (p x) hpx
        (c.transport gp hfix) hpxc = (b != d) := by
    rfl
  rw [hr, hp, hq]
  exact bool_discrepancy_cocycle a b d

end Sparsening
end AllThoseEPPA
