import Leader.L4.BStarCopyRightReleaseOrder
import Leader.L4.BStarCopyEnableCoverage

namespace L4.BStarCopyRightInjectPositive
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
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

theorem selected_inject (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (sh : Sheet)
    (sel : (C,.advance v)∈actualOffers g raw)
    (good : v.fault=0) (op : v.opcode.toNat=10)
    (lane : sh∈prepSites (geometry g C.source.side) C.source.occurrence .inject) :
    (⟨⟨.inject,C.source,⟨C.source.side,sh⟩⟩,.empty⟩ : BStarLongPrep.Offer)
      ∈(arbitration (round g raw).prep).1 := by
  let a : BStarLongPrep.Offer := ⟨⟨.inject,C.source,⟨C.source.side,sh⟩⟩,.empty⟩
  have G : (C,.advance v)∈gated g raw := by
    unfold actualOffers BStarLongGrant.run at sel
    obtain ⟨entry,hm,E⟩ := List.mem_map.mp sel
    obtain ⟨claim,action⟩ := entry
    have unchanged : (claim,action) = (C,.advance v) := by
      by_cases pos : claim.source.occurrence.val<3
      · cases action with
        | advance u =>
          simp only [BStarLongGrant.update,dif_pos pos] at E
          split at E
          · rename_i H
            have A := beq_iff_eq.mp (Bool.and_eq_true_iff.mp H).2
            have Q := (Prod.mk.inj E).2
            have opc := congrArg (fun t : Payload => t.opcode.toNat)
              (BStarLongCommand.Offer.advance.inj Q)
            unfold BStarLongGrant.capture BStarLongGrant.captureFields at opc
            split at opc <;> (simp only [A,op] at opc; contradiction)
          · exact E
        | _ => simpa only [BStarLongGrant.update,dif_pos pos] using E
      · simpa only [BStarLongGrant.update,dif_neg pos] using E
    rw [unchanged] at hm
    obtain ⟨entry,eIn,E⟩ := List.mem_map.mp hm
    obtain ⟨cl,act⟩ := entry
    cases act with
    | advance u =>
      simp only [cancel] at E
      split at E
      · cases E
        contradiction
      · cases E
        exact eIn
    | _ => cases E
  have off : a∈(round g raw).prep := by
    apply List.mem_flatMap.mpr
    refine ⟨(C,.advance v),G,?_⟩
    change a∈fieldOffers g raw C.source v
    have P : prepOf v.opcode.toNat=some .inject := by rw [op]; rfl
    simp only [fieldOffers,good,bne_self_eq_false,P]
    exact List.mem_map.mpr ⟨a.claim,List.mem_map.mpr ⟨sh,lane,rfl⟩,rfl⟩
  change a∈(arbitration (round g raw).prep).1
  refine BStarCopyInjection.exclusive_winner a _ off ?_
  intro b mem same
  have nd := List.pairwise_map.mp (BStarResetNoFault.prep_lanes_nodup g raw)
  generalize equation : (round g raw).prep = ls at mem off nd
  clear equation
  induction ls with
  | nil => cases mem
  | cons z tail ih =>
    obtain ⟨head,rest⟩ := List.pairwise_cons.mp nd
    rcases List.mem_cons.mp mem with rfl|bm
    · rcases List.mem_cons.mp off with rfl|am
      · rfl
      · exact (head a am same).elim
    · rcases List.mem_cons.mp off with rfl|am
      · exact (head b bm same.symm).elim
      · exact ih bm am rest

private theorem not_center_carries (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (N : C.source.occurrence.val≠1) :
    carried g raw C v=v := by
  unfold carried BStarLongArithmetic.visit
  have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
  simp only [M,Bool.true_or,if_true]
  rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
  rfl

/-- A healthy actual forward landing after an addressed right K2
crossing witnesses selected INJECT. No selected-prep hypothesis is
needed; the real healthy landing rules out any prep fault. -/
theorem healthy_k2_crossing {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (sep : e≠rightNeighbor e) (k : Nat) (kl : k<len) (i : Fin n)
    (chartKey : S.getD k fall=(i,2))
    (inside : (longGeometry B (base i)).inside=true)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy 10 (.out k)))
    (f : Payload) (land : project (fun j=>S.getD j fall) (ring x e) (k+1)=.forward f)
    (healthy : f.fault=0) (opcode : f.opcode.toNat=10) :
    e=i ∧ BStarCopyInjection.injection .left true∈
      (arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1 := by
  obtain ⟨C,d,v,sel,dst,src,arr⟩ := BStarNumericChronology.ring_departure
    hp chart e sep 10 k kl cur.1 cur.2.1 cur.2.2 f land healthy
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have hc : C.source.occurrence=2 := congrArg Prod.snd (src.symm.trans chartKey)
  have cs := raw_k2 g C mem hc
  have L2 : C.source=L 2 := by rw [cs]; cases g.2.axes.h6 <;> rfl
  have loc : e=i := by
    have Q := congrArg Prod.fst (src.symm.trans chartKey)
    rwa [L2] at Q
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
    rw [L2]
    change (longGeometry B (x e)).inside=true
    have D := congrArg (fun z : Bool × Bool × Bool => z.2.1) (cur.1.1 e)
    rw [loc] at D ⊢
    exact D.symm.trans inside
  have lanes : Sheet.rs∈prepSites (geometry g C.source.side) C.source.occurrence .inject := by
    rw [hc]
    simp [prepSites,I]
  have M := selected_inject g raw C v .rs sel hv.1
    ((congrArg BitVec.toNat hv.2).trans opcode) lanes
  rw [L2] at M
  exact ⟨loc,M⟩

#print axioms healthy_k2_crossing

/-- Find the genuine ISSUE10/terminal outward word, with healthy old
F10, from the actual accepted own consume to PC11. -/
theorem accepted10_terminal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {ack : Fin n}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w (.busy 10 (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len (play x w) ack (.busy 10 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat=11) :
    ∃ (lead back : List (Fin n)) (turn : Fin n) (f : Payload),
      w=lead++turn::back ∧
      Found hp base (fun j => S.getD j fall) len 10 x lead (.out len) ∧
      project (fun j => S.getD j fall) (play x lead) len=.forward f ∧
      f.fault=0 ∧ f.opcode.toNat=10 := by
  have current := BStarGeneratedTapeCuts.at_end hp G
  obtain ⟨H,K⟩ := root_header hp chart current.1.1
  have low : 7≤(ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat := by rw [accepted]; decide
  have high : (ctrlOp.read (ring (play x w) ack (S.getD 0 fall).1).long).toNat≤408 := by rw [accepted]; decide
  obtain ⟨_,ans,returned,healthy,op10⟩ :=
    BStarGeneratedPCAncestry.consume_to_band hp (base:=base) (x:=play x w)
      (addr:=fun j=>S.getD j fall) (len:=len) (op:=10) (e:=ack) K H (sep ack) current event low high
  obtain ⟨lead,turn,back,D,found,_,ret⟩ := found_split_turn hp (from_idle hp G)
  have keep := found
  obtain ⟨u,v,launch,L,_,_,_,F⟩ := keep
  have old : Current hp base (fun j => S.getD j fall) len (play x lead) (.busy 10 (.out len)) := by
    rw [L,BStarResetSchedule.run_append]
    change Current hp base (fun j => S.getD j fall) len (play (ring (play x u) launch) v) (.busy 10 (.out len))
    exact busy_end hp F
  have rebuilt : Found hp base (fun j=>S.getD j fall) len 10 x lead (.out len) := by assumption
  have returned' : let y := play (ring (play x lead) turn) back
      let i := (S.getD 0 fall).1
      bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.reply ans := by
    rw [D,BStarResetSchedule.run_append] at returned
    exact returned
  obtain ⟨f,FF,cl,op⟩ := terminal_old_healthy hp chart sep turn back 10 old ret ans healthy
    (by rw [op10]; decide) returned'
  exact ⟨lead,back,turn,f,D,rebuilt,FF,cl,(congrArg BitVec.toNat op).trans op10⟩


#print axioms accepted10_terminal
end L4.BStarCopyRightInjectPositive
