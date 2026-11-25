import Leader.L4.BStarSealOwnerFrame

namespace L4.BStarSealOutgoingFrame
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongWork BStarLongTransport BStarLongEvents BStarLongLiteral
open BStarH6WordChart BStarResetChartTouch BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarGeneratedOwner BStarSealOwnerFrame BStarSealPackedFrame BStarLongLandingFrame
open BStarBitNoAbort BStarLongPublication BStarLongLayout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- Every selected K1 departure is the left side of the actual mark.
In particular a first incoming observation at the same site never
changes its old STAGE or SEAL, even if an outward command is waiting. -/
theorem off_outgoing (x : X) (e i : Fin n) (off : e≠i) :
    RingNoLatch hp x e i := by
  intro s atSide c p picked side center
  dsimp only
  intro _
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have mem : c∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,picked,rfl⟩
  have E := center_of g c mem center
  subst c
  have sideL : s=.left := side.symm
  subst s
  exact (off atSide.symm).elim

/-- Exact preservation up to the mark that actually executes the
center. The owner may wait at its outward center on arbitrary other
marks. Mode exclusion is needed only at outgoing marks of the center. -/
theorem sealed_until_outgoing {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (le : k≤len) (idx : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : run origin lead=x)
    (d : Descriptor) (seed : SealedCenter d (x i).long)
    (head : ∀ u e v,w=u++e::v → oldH6 B (run x u) i=true)
    (scope : ∀ u v,w=u++i::v → ∃ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++u) m ∧
      Current hp base (fun j=>S.getD j fall) len (run x u) m ∧ Excluded k m)
    (held : ((grant 1).read (run x w i).long).getLsbD 0=true) :
    SealedCenter d (run x w i).long := by
  have reads := word_frame hp x w i sep (by
    intro u e v E
    refine ⟨head u e v E,?_⟩
    by_cases off : e=i
    · subst e
      obtain ⟨m,P,N,excluded⟩ := scope u v E
      have Y : run origin (lead++u)=run x u := by rw [BStarResetSchedule.run_append,landed]
      exact Y ▸ no_latch hp C sep i k le idx P (Y.symm ▸ N) excluded i
    · exact off_outgoing hp _ e i off)
  have s0 := congrArg Prod.fst reads
  have st := congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => z.2.1) reads
  have se := congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => z.2.2) reads
  change selector.read (run x w i).long=selector.read (x i).long at s0
  change stage.read (run x w i).long=stage.read (x i).long at st
  change sealField.read (run x w i).long=sealField.read (x i).long at se
  exact ⟨held,(by unfold readSel; rw [s0]; exact seed.2.1),
    (congrArg readOptional st).trans seed.2.2.1,(congrArg readOptional se).trans seed.2.2.2⟩

end L4.BStarSealOutgoingFrame
