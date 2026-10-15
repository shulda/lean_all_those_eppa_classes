import AllThoseEPPA.Applications.KOrientations.AuxiliaryLabelReflectionRelative
import AllThoseEPPA.Applications.KOrientations.AuxiliaryAction

/-!
# All auxiliary relations: preservation AND reflection on relative d-closed roots

Let S be a distinguished successor-closed source inside the first
witness B₀, and let U,T⊆S be relatively d-closed partial domains.
A *genuine graph automorphism* g of B₀ identifies U and T and its
root-tuple action agrees with the chosen partial map.

Then the relabelled R_P, E_P and edge relation on the auxiliary
root-only structure all agree in BOTH directions, including labels
whose centres lie outside S. That last negative-tuple case is the
essential correction audited in the paper as ORI-022.

We take the tuple map as an explicit hypothesis to keep this lemma
usable independently of a particular PartialEquiv implementation.
The unary function-domain reflection is a separate obligation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Exact relation iff under root-tuple transport and the full
graph-automorphism action on every auxiliary relation symbol. -/
theorem auxiliaryRootStructure_rel_transport_iff_of_traceClosed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (S U T : Set V) (hUS : U ⊆ S) (hTS : T ⊆ S)
    (hU : (dTraceStructure G k S).IsClosed {x : S | x.val ∈ U})
    (hT : (dTraceStructure G k S).IsClosed {x : S | x.val ∈ T})
    (g : G.graphAut)
    (hMapDomain : ∀ x : V, x ∈ U ↔ g.1 x ∈ T)
    {n : ℕ} (R : AuxiliaryRel G k n)
    (xs ys : Fin n → RootsIn G k S)
    (hxs : ∀ i, (xs i).val ∈ U)
    (hys : ∀ i, (ys i).val ∈ T)
    (hMapTuple : ∀ i, (ys i).val = g.1 (xs i).val) :
    (auxiliaryRootStructure G k S).rel
      (auxiliaryRelTransport G k g R) ys ↔
    (auxiliaryRootStructure G k S).rel R xs := by
  cases R with
  | edge =>
      change G.edge (ys 0).val (ys 1).val ↔
        G.edge (xs 0).val (xs 1).val
      rw [hMapTuple 0, hMapTuple 1]
      exact g.property (xs 0).val (xs 1).val
  | root P =>
      have hLeft :=
        auxiliary_root_label_iff_center_in_traceClosed
          G k _ S U hUS hU P xs hxs
      have hRight :=
        auxiliary_root_label_iff_center_in_traceClosed
          G k _ S T hTS hT (RootPattern.transportAut g P) ys hys
      change
        (auxiliaryRootStructure G k S).rel
          (AuxiliaryRel.root (RootPattern.transportAut g P)) ys ↔
        (auxiliaryRootStructure G k S).rel (AuxiliaryRel.root P) xs
      constructor
      · intro h
        obtain ⟨hc, ht⟩ := hRight.mp h
        apply hLeft.mpr
        refine ⟨(hMapDomain P.center).mpr hc, ?_⟩
        intro i
        apply g.1.injective
        calc
          g.1 (xs i).val = (ys i).val := (hMapTuple i).symm
          _ = (RootPattern.transportAut g P).tuple i := ht i
          _ = g.1 (P.tuple i) := rfl
      · intro h
        obtain ⟨hc, ht⟩ := hLeft.mp h
        apply hRight.mpr
        refine ⟨(hMapDomain P.center).mp hc, ?_⟩
        intro i
        calc
          (ys i).val = g.1 (xs i).val := hMapTuple i
          _ = g.1 (P.tuple i) := congrArg g.1 (ht i)
          _ = (RootPattern.transportAut g P).tuple i := rfl
  | incoming P =>
      have hLeft :=
        auxiliary_incoming_label_iff_center_in_traceClosed
          G k _ S U hUS hU P xs hxs
      have hRight :=
        auxiliary_incoming_label_iff_center_in_traceClosed
          G k _ S T hTS hT (RootPattern.transportAut g P) ys hys
      change
        (auxiliaryRootStructure G k S).rel
          (AuxiliaryRel.incoming (RootPattern.transportAut g P)) ys ↔
        (auxiliaryRootStructure G k S).rel (AuxiliaryRel.incoming P) xs
      have hEdge :
          G.edge (ys 0).val (RootPattern.transportAut g P).center ↔
            G.edge (xs 0).val P.center := by
        change G.edge (ys 0).val (g.1 P.center) ↔
          G.edge (xs 0).val P.center
        rw [hMapTuple 0]
        exact g.property (xs 0).val P.center
      constructor
      · intro h
        obtain ⟨hc, he, ht⟩ := hRight.mp h
        apply hLeft.mpr
        refine ⟨(hMapDomain P.center).mpr hc, hEdge.mp he, ?_⟩
        intro i
        apply g.1.injective
        calc
          g.1 (xs (Fin.succ i)).val =
              (ys (Fin.succ i)).val :=
            (hMapTuple (Fin.succ i)).symm
          _ = (RootPattern.transportAut g P).tuple i := ht i
          _ = g.1 (P.tuple i) := rfl
      · intro h
        obtain ⟨hc, he, ht⟩ := hLeft.mp h
        apply hRight.mpr
        refine ⟨(hMapDomain P.center).mp hc, hEdge.mpr he, ?_⟩
        intro i
        calc
          (ys (Fin.succ i)).val =
              g.1 (xs (Fin.succ i)).val :=
            hMapTuple (Fin.succ i)
          _ = g.1 (P.tuple i) := congrArg g.1 (ht i)
          _ = (RootPattern.transportAut g P).tuple i := rfl

end AllThoseEPPA.Applications.KOrientations
