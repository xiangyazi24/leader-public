import Leader.L4.BStarCopyRightInjectPositive
import Leader.L4.BStarCopyLeftMixed
import Leader.L4.BStarCopyEnableCoverage

namespace L4.BStarCopyLeftInjectPositive
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents BStarLongRouting BStarLongLiteral BStarLongDoor
open BStarResetQuiet BStarResetQuietTable BStarClearanceForward BStarLongCommandData
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatorControl BStarResetSchedule
open BStarLongPackets BStarLongPrep BStarLongFiberOwner
open BStarCopyRightK2Past BStarCopyRightReleaseOrder BStarCopyRightStrip BStarCopyRightReleaseClass BStarResetChartService BStarAcquireAckAncestry BStarAcquireHistoryReturn BStarCopyEnableTerminal

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring


open BStarCopyLeftK5Past BStarCopyRightInjectPositive
private theorem not_center_carries (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (N : C.source.occurrence.val≠1) :
    carried g raw C v=v := by
  unfold carried BStarLongArithmetic.visit
  have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
  simp only [M,Bool.true_or,if_true]
  rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
  rfl

/-- A healthy actual forward landing after an addressed left K5
crossing witnesses selected INJECT. No selected-prep hypothesis is
needed; the real healthy landing rules out any prep fault. -/
theorem healthy_k5_crossing {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (sep : e≠rightNeighbor e) (k : Nat) (kl : k<len) (i : Fin n)
    (chartKey : S.getD k fall=(i,5))
    (inside : (longGeometry B (base i)).inside=true)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy 10 (.out k)))
    (f : Payload) (land : project (fun j=>S.getD j fall) (ring x e) (k+1)=.forward f)
    (healthy : f.fault=0) (opcode : f.opcode.toNat=10) :
    rightNeighbor e=i ∧ BStarCopyInjection.injection .right false∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1 := by
  obtain ⟨C,d,v,sel,dst,src,arr⟩ := BStarNumericChronology.ring_departure
    hp chart e sep 10 k kl cur.1 cur.2.1 cur.2.2 f land healthy
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have hc : C.source.occurrence=5 := congrArg Prod.snd (src.symm.trans chartKey)
  have cs := raw_k5 g C mem hc
  have R5 : C.source=R 5 := by rw [cs]; cases g.2.axes.h6 <;> rfl
  have loc : rightNeighbor e=i := by
    have Q := congrArg Prod.fst (src.symm.trans chartKey)
    rwa [R5] at Q
  have no := (BStarAcquireReturn.link_shape g C d mem dst).1
  have safe : d=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : d.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have N := (BStarAcquireJoinedHop.k0_dest g C d mem dst J).2
    simp [Z] at N
  have Jraw := (move_lands g raw C v d dst sel (Ne.symm no)).2
  have E := (new_read B x e sep d).trans ((congrArg (atCursor (ring x e)) arr).symm)
  have DL := E.trans land
  change decode (readRaw (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) d)=_ at DL
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) d safe,Jraw,BStarLongToken.decode_encode] at DL
  rw [not_center_carries g raw C v (by rw [hc]; decide)] at DL
  have hv : v.fault=0 ∧ v.opcode=f.opcode := by
    unfold arrive at DL
    split at DL <;> cases DL <;> exact ⟨healthy,rfl⟩
  have I : (geometry g C.source.side).inside=true := by
    rw [R5]
    change (longGeometry B (x (rightNeighbor e))).inside=true
    have D := congrArg (fun z : Bool × Bool × Bool => z.2.1) (cur.1.1 (rightNeighbor e))
    rw [loc] at D ⊢
    exact D.symm.trans inside
  have lanes : Sheet.ls∈prepSites (geometry g C.source.side) C.source.occurrence .inject := by
    rw [hc]
    simp [prepSites,I]
  have M := selected_inject g raw C v .ls sel hv.1
    ((congrArg BitVec.toNat hv.2).trans opcode) lanes
  rw [R5] at M
  exact ⟨loc,M⟩

#print axioms healthy_k5_crossing


end L4.BStarCopyLeftInjectPositive
