import Leader.L4.ReportFastSplice
import Leader.L4.ReportIngressOwnership

namespace L4.ReportFastSplice
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportLeaseOwner ReportPrelaunchAllOwners ReportGoodEightBank ReportFastRawEvent
open ReportGenerationAncestry ReportIngressOwnership

variable {s n : Nat} {h : Fin n→Bool} {P : Raw s n→Prop}

noncomputable def publicationTarget (G : GapInput h) (r : Owner h) : Owner h :=
  ⟨centre (charter G r),(canonical_centre G r).2.2.1⟩

theorem publicationTarget_ne_root (G : GapInput h) (r : Owner h) :
    publicationTarget G r≠r := by
  intro Eq
  let C := charter G r
  obtain ⟨A,D,_,_⟩ := canonical_centre G r
  have Pos : 0<C.a := A
  have Len : C.a<C.L := D
  have Root : C.root=r.val := owner_chart_root G r.val r.property
  have P0 : nextAt C.root C.a=r.val := congrArg Subtype.val Eq
  have Q0 : nextAt C.root C.a=nextAt C.root 0 := by
    rw [P0,show nextAt C.root 0=C.root by rfl,Root]
  have E := nextAt_injective_under C.root C.a 0
    (Nat.lt_trans Len C.length_lt) (Nat.lt_trans C.positive C.length_lt) Q0
  exact (Nat.ne_of_gt Pos) E

/-- Keep the actual late history as a proof witness. Its current rank
need not be definitionally recoverable from bytes, or unique. -/
structure LateWitnessRows (d : Sheet) (hh : ∃ i,h i=true)
    (P : Raw s n→Prop) (G : GapInput h) (r j : Owner h) (K : Nat) where
  centre_eq : j.val=centre (charter G r)
  atRank : ReportFastPostACQ.Context d hh P G r → List (Fin n) → Raw s n → Nat → Prop
  enter : ∀ (A : ReportFastPostACQ.Context d hh P G r) u,
    ReportFastPostACQ.UntilSeal A u →
    ReportFastPostACQ.Stop A (rawRun A.base u) →
    GoodEightBank d hh P G (rawRun A.base u) →
    ∃ k,atRank A u (rawRun A.base u) k
  bounds : ∀ A u x k,atRank A u x k→0<k ∧ k≤K
  advance : ∀ A u x e k,atRank A u x k→classify d h x e≠some j →
    ∃ k',atRank A u (rawNext s x e) k' ∧ k'≤k
  nominate : ∀ A u x k,atRank A u x k→
    ∃ e, classify d h x e=some j ∨
      ∃ k',atRank A u (rawNext s x e) k' ∧ k'<k

private theorem leastWitness (P : Nat→Prop) (H : ∃ k,P k) :
    ∃ k, P k ∧ ∀ l,P l→k≤l := by
  classical
  obtain ⟨k,K⟩ := H
  induction k using Nat.strongRecOn with
  | ind k IH =>
    by_cases H : ∃ l,l<k ∧ P l
    · obtain ⟨l,L,W⟩ := H
      exact IH l L W
    · exact ⟨k,K,fun l L=>Nat.le_of_not_gt (fun V=>H ⟨l,V,L⟩)⟩

noncomputable def chooseRank (P : Nat→Prop) : Nat := by
  classical
  exact if H : ∃ k,P k then Classical.choose (leastWitness P H) else 0

theorem chooseRank_spec (P : Nat→Prop) (H : ∃ k,P k) :
    P (chooseRank P) ∧ ∀ l,P l→chooseRank P≤l := by
  classical
  unfold chooseRank
  rw [dif_pos H]
  exact Classical.choose_spec (leastWitness P H)

/-- Existential historical stage data can be projected to the exact
raw target in SPLICE1 by choosing a least witness. All comparisons
are on one physical mark; there is no filtered schedule. -/
noncomputable def LateSealCommit.of_witness
    (d : Sheet) (hh : ∃ i,h i=true) (P : Raw s n→Prop)
    (G : GapInput h) (r j : Owner h) (K : Nat)
    (R : LateWitnessRows d hh P G r j K) :
    LateSealCommit d hh P G r j K where
  centre_eq := R.centre_eq
  good A u x := ∃ k,R.atRank A u x k
  rank A u x := chooseRank (R.atRank A u x)
  enter A u F S B := R.enter A u F S B
  bound A u x X := (R.bounds A u x _ (chooseRank_spec _ X).1).2
  positive A u x X := (R.bounds A u x _ (chooseRank_spec _ X).1).1
  advance A u x e X NC := by
    obtain ⟨k,K,L⟩ := R.advance A u x e _ (chooseRank_spec _ X).1 NC
    exact ⟨⟨k,K⟩,Nat.le_trans ((chooseRank_spec _ ⟨k,K⟩).2 k K) L⟩
  nominate A u x X := by
    obtain ⟨e,E|⟨k,K,L⟩⟩ := R.nominate A u x _ (chooseRank_spec _ X).1
    · exact ⟨e,.inl E⟩
    · exact ⟨e,.inr (Nat.lt_of_le_of_lt ((chooseRank_spec _ ⟨k,K⟩).2 k K) L)⟩

end L4.ReportFastSplice
