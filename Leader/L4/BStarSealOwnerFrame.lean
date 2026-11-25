import Leader.L4.BStarSealPackedFrame
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarForwardProvenance

namespace L4.BStarSealOwnerFrame
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongWork BStarLongTransport BStarLongEvents
open BStarBankTrace (beforeOutgoing)
open BStarH6WordChart BStarResetChartTouch BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarResetMarkAdapter
open BStarAcquireForwardTrace BStarSealPackedFrame BStarLongLandingFrame

private theorem numeric_keeps_op (g : LongGeometry) (k : Fin 11) (x : BitVec LW) (p : Payload) :
    (BStarLongArithmetic.visit g k x p).2.fault=0 →
      p.fault=0 ∧ p.opcode=(BStarLongArithmetic.visit g k x p).2.opcode := by
  unfold BStarLongArithmetic.visit
  split
  · exact fun H => ⟨H,rfl⟩
  · split
    · exact fun H => ⟨H,rfl⟩
    · split
      · intro H
        contradiction
      · rename_i _ _ c _
        cases c <;> simp [BStarLongArithmetic.physicalDigit] <;> split <;> simp

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Controller chronology excludes exactly the latch writers at the
tracked center cursor, not unrelated same-mark activity. In particular
busy409 after the real SEAL and busy411 before the real center can
both satisfy this condition. -/
def Excluded (k : Nat) (m : Mode) : Prop :=
  ∀ op, (op=1 ∨ op=stageOp ∨ op=sealOp ∨ op=commitOp) → m≠.busy op (.out k)

theorem no_latch {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (le : k≤len) (idx : S.getD k fall=(i,1))
    {w : List (Fin n)} {m : Mode}
    (P : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j=>S.getD j fall) len (run x w) m)
    (off : Excluded k m) (e : Fin n) :
    RingNoLatch hp (run x w) e i := by
  intro s addr c offer selected atSide center
  dsimp only
  intro live
  let y := run x w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  let q := (beforeOutgoing g raw c offer).2
  have ⟨healthy,equal⟩ := numeric_keeps_op _ _ _ offer live
  obtain ⟨old,F,H,OP⟩ := BStarForwardProvenance.offer_origin g raw c offer selected healthy
  have sourceAddr : address e c.source=(i,1) :=
    Prod.ext ((congrArg (site e) atSide).trans addr.symm) (Fin.ext center)
  rw [BStarResetRailRing.old_read] at F
  change atCursor y (address e c.source)=.forward old at F
  rw [sourceAddr] at F
  have oldProj : project (fun j=>S.getD j fall) y k=.forward old := by
    change atCursor y (S.getD k fall)=_
    rwa [idx]
  have eqOp : old.opcode.toNat=q.opcode.toNat := congrArg BitVec.toNat (OP.trans equal)
  have own := (healthy_forward_origin hp C sep P now k le old oldProj q.opcode.toNat H eqOp).1
  exact ⟨fun O => off _ (.inl O) own,
    fun O => off _ (.inr (.inl O)) own,
    fun O => off _ (.inr (.inr (.inl O))) own,
    fun O => off _ (.inr (.inr (.inr O))) own⟩

open BStarBitNoAbort

/-- Sealed descriptor transport through the owner's actual suffix.
Prefix mode excludes only *same-center* destructive departures, so
before-center COMMIT and after-center SEAL are allowed. Writer custody
is a separate literal field hypothesis, to be supplied by grant
history; no successful final publication premise is needed. -/
theorem sealed_word {base origin x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (le : k≤len) (idx : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : run origin lead=x)
    (d : BStarLongPublication.Descriptor) (seed : SealedCenter d (x i).long)
    (scope : ∀ u e v,w=u++e::v → ∃ m,
      GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (lead++u) m ∧
      Current hp base (fun j=>S.getD j fall) len (run x u) m ∧
      oldH6 B (run x u) i=true ∧ Excluded k m)
    (held : ((BStarLongLayout.grant 1).read (run x w i).long).getLsbD 0=true) :
    SealedCenter d (run x w i).long := by
  have reads := word_frame hp x w i sep (by
    intro u e v E
    obtain ⟨m,P,N,head,off⟩ := scope u e v E
    have y : run origin (lead++u)=run x u := by rw [BStarResetSchedule.run_append,landed]
    exact ⟨head,y ▸ no_latch hp C sep i k le idx P (y.symm ▸ N) off e⟩)
  have sel := congrArg Prod.fst reads
  have staged := congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => z.2.1) reads
  have sEq := congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8 => z.2.2) reads
  change BStarLongLayout.selector.read (run x w i).long=BStarLongLayout.selector.read (x i).long at sel
  change BStarLongLayout.stage.read (run x w i).long=BStarLongLayout.stage.read (x i).long at staged
  change BStarLongLayout.sealField.read (run x w i).long=BStarLongLayout.sealField.read (x i).long at sEq
  refine ⟨held,?_,?_,?_⟩
  · unfold BStarLongPublication.readSel
    rw [sel]
    exact seed.2.1
  · rw [staged]
    exact seed.2.2.1
  · rw [sEq]
    exact seed.2.2.2

#print axioms no_latch
#print axioms sealed_word
end L4.BStarSealOwnerFrame
