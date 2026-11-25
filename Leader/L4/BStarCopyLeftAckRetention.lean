import Leader.L4.BStarCopyRightAckRetention
import Leader.L4.BStarCopyLeftAcquireBank
import Leader.L4.BStarCopyLeftLoadToInject

namespace L4.BStarCopyLeftAckRetention
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedBandScan BStarGeneratedOwner BStarCaptureDoorHistory
open BStarLongDoor BStarLongLayout BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCommitOperands BStarCutOperandReadout
open BStarCopyRightStrip (addr)
open BStarCopyLeftStrip BStarCopyLeftAcquireBank BStarCopyRightAckRetention BStarClearanceDataChart BStarLongCommandData

/-- Crop the original COMMIT-acquisition witness to an earlier
LOAD prefix after the same ACK, using only equalities of raw words. -/
theorem cut_after_matching_ack {x : X} {cut whole : List (Fin n)} {header : Fin n}
    (A : Acquisition hp x cut whole header 0)
    (common : ∃ v,whole=cut++v)
    (ackLead loadLead after : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ between,ackLead=A.lead++A.mark::between)
    (ackBeforeLoad : ∃ between,loadLead=ackLead++ack::between)
    (loadPrefix : whole=loadLead++after) :
    ∃ p u, loadLead=cut++p ∧ loadLead=A.lead++A.mark::u ∧ A.post=u++after := by
  obtain ⟨tail,R⟩ := common
  obtain ⟨q,Q⟩ := lead_after (R.symm.trans A.exactTape) A.afterCut
  obtain ⟨t,T⟩ := birthBeforeAck
  obtain ⟨z,Z⟩ := ackBeforeLoad
  let u := t++ack::z
  have read : loadLead=A.lead++A.mark::u := by
    rw [Z,T]
    simp only [u,List.append_assoc,List.cons_append]
  have postEq : A.post=u++after := by
    have E : A.lead++(A.mark::A.post)=A.lead++(A.mark::(u++after)) := by
      calc
        _ = whole := A.exactTape.symm
        _ = loadLead++after := loadPrefix
        _ = (A.lead++A.mark::u)++after := congrArg (·++after) read
        _ = _ := by simp only [List.append_assoc,List.cons_append]
    exact (List.cons.inj ((List.append_right_inj A.lead).mp E)).2
  exact ⟨q++A.mark::u,u,by rw [read,Q,List.append_assoc],read,postEq⟩

/-- Single physical operand bridge from matched earlier ACK and won
incidence 0 to the immutable packed bytes on any selected LOAD cut
within that same acquired lifetime. Retention of the source's high
capture is derived on the exact ACK→ISSUE8 raw word. -/
theorem packed_after_actual_ack {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh owner S len fall)
    (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (root : a=(endpoint (oldH6 B base) hh owner 0).1)
    (bound : r≤seam)
    (A : Acquisition hp x cut whole (endpoint (oldH6 B base) hh owner 0).1 0)
    (common : ∃ v,whole=cut++v)
    (ackLead beforeIssue loadTrail after : List (Fin n)) (ack issue : Fin n) (m : Mode)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (loadPrefix : whole=((((ackLead++[ack])++beforeIssue)++issue::loadTrail)++after))
    (history : GeneratedOwner hp base (fun t => S.getD t fall) len
      (ring (play x ackLead) ack) .idle beforeIssue m)
    (region : ∀ p q,beforeIssue=p++q →
      let y := play x ((ackLead++[ack])++p)
      Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ w,oldH6 B (play x (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play x (cut++w)) e z
      (endpoint (oldH6 B base) hh owner 0).1)
    (bank : Fin 3)
    (bank8 : bank.val=(captures.read (play x ((ackLead++[ack])++beforeIssue) (S.getD 0 fall).1).long).toNat/16%4)
    (ack0 : ((capturedSelector 0).read (ring (play x ackLead) ack (S.getD 0 fall).1).long).toNat=
      (BStarLongPublication.readSel ((play x A.lead) (endpoint (oldH6 B base) hh owner 0).1).long).val) :
    ∀ digit : Fin r,
      let i := addr a digit.val
      let old := play x (((ackLead++[ack])++beforeIssue)++issue::loadTrail)
      let captured := play x A.lead
      let header := (endpoint (oldH6 B base) hh owner 0).1
      oldBankPacket (old i).long bank =
        oldBankPacket (captured i).long (BStarLongPublication.readSel (captured header).long) := by
  let loadLead := ((ackLead++[ack])++beforeIssue)++issue::loadTrail
  have ackBefore : ∃ t,loadLead=ackLead++ack::t := by
    refine ⟨beforeIssue++issue::loadTrail,?_⟩
    simp [loadLead,List.append_assoc]
  obtain ⟨p,u,P,U,V⟩ := BStarCopyLeftAckRetention.cut_after_matching_ack hp A common ackLead loadLead after ack
    birthBeforeAck ackBefore loadPrefix
  have kept := captures_on_original_cut hp chart sep ackLead beforeIssue ack m history region
  intro d
  dsimp only
  change oldBankPacket ((play x loadLead) (addr a d.val)).long bank=_
  rw [P]
  exact packed_before_load hp hh owner a seam width strip root bound A u after p V
    (P.symm.trans U) sep layout auth _ _ bank bank8 kept ack0 d

open BStarCopyLeftLoadToInject BStarCopyLeftFrozen BStarCopyLeftPreinject
open BStarCopyRightLoadToInject (OwnMiddle)
open BStarLongPackets BStarCopyOwnedFrozen BStarCopyOperand BStarCopyLoadCarry BStarCopyLoadHistory
open BStarAcquireHistorySample BStarAcquireHistoryReturn BStarAcquireForwardTrace BStarResetMarkAdapter BStarLongToken BStarLongCommand
open BStarSeparatingRail
open BStarOwnerLaunchOrigin
open BStarClearanceSource

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

theorem after_load_frame {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w8 middle w10 : List (Fin n)) (load : Fin n) (side : Side)
    (C : CommandClaim) (k j : Nat) (kl : k≤len) (jl : j≤len)
    (injectAddr : S.getD j fall=(site load side,5))
    (loadLoc : address load C.source=S.getD k fall)
    (source : C.source=⟨side,0⟩)
    (own : dataOwner (oldH6 B base) (site load side) .ls=o.val)
    (before : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy 8 (.out k)))
    (loadEvent : Event hp (fun t => S.getD t fall) len (play origin lead) load
      (.busy 8 (.out k)) (.busy 8 (.out (k+1))))
    (b8 : BusyOnly hp base (fun t => S.getD t fall) len 8 (ring (play origin lead) load) (.out (k+1)) w8 (.back 0))
    (M : OwnMiddle hp base origin (fun t => S.getD t fall) len ((lead++[load])++w8) middle)
    (b10 : BusyOnly hp base (fun t => S.getD t fall) len 10
      (play origin (((lead++[load])++w8)++middle)) (.out 0) w10 (.out j))
    (fiber : ∀ a b, ((((lead++[load])++w8)++middle)++w10)=a++b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play origin a) v) :
    (readLane (Sheet.index .ls)
      (play origin ((((lead++[load])++w8)++middle)++w10) (site load side)).long).frozen =
    (readLane (Sheet.index .ls) (ring (play origin lead) load (site load side)).long).frozen := by
  let i := site load side
  have idx : S.getD k fall=(i,0) := by
    rw [←loadLoc,source]
  have pre8 : play origin (lead++[load])=ring (play origin lead) load := by
    rw [BStarResetSchedule.run_append]; rfl
  have reached8 := BStarGeneratedTapeCuts.at_end hp before
  have G8 : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle (lead++[load]) (.busy 8 (.out (k+1))) := by
    apply generated_append hp before
    exact .next reached8 loadEvent (.endpoint (busy_start hp b8))
  have F8 := frozen_busy_suffix hp chart sep i k kl idx own 8 (.inl rfl)
    (lead++[load]) pre8.symm G8 b8 (fun _ => Nat.lt_succ_self _)
    (fun a e b eq => by
      have H := fiber ((lead++[load])++a) ((e::b)++middle++w10) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append,pre8] at H
      exact H)
  have F9 := ls_frozen_between hp chart sep ((lead++[load])++w8) middle (.busy 10 (.out 0))
    M.end10 i own
    (fun a e b eq => fiber (((lead++[load])++w8)++a) ((e::b)++w10) (by simp [eq,List.append_assoc]))
    (fun a e b eq op j I => by
      have pc := M.outward9 a e b eq op j I
      exact ⟨by omega,by omega,by omega,by omega⟩)
  have F10 := frozen_pc10_prefix hp chart sep i j jl injectAddr own (((lead++[load])++w8)++middle)
    rfl M.end10 b10 (fun a e b eq => by
      have H := fiber ((((lead++[load])++w8)++middle)++a) (e::b) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append] at H
      exact H)
  rw [←BStarResetSchedule.run_append] at F10
  rw [←pre8,←BStarResetSchedule.run_append] at F8
  rw [pre8] at F8
  exact F10.trans (F9.trans F8)

/-- Exact original left ACQUIRE→LOAD8→pre-INJECT value on a common
physical tape. The supplied launch and onward visit are row-derived
certificates; there is no assumed equality of raw bytes or selectors. -/
theorem frozen_after_actual_ack {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh owner S len fall)
    (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (root : a=(endpoint (oldH6 B base) hh owner 0).1) (bound : r≤seam)
    (A : Acquisition hp x cut whole (endpoint (oldH6 B base) hh owner 0).1 0)
    (common : ∃ v,whole=cut++v)
    (ackLead beforeIssue loadTrail after lead w8 middle w10 : List (Fin n))
    (ack issue load : Fin n) (side : Side) (m : Mode) (d : Fin r)
    (atDigit : site load side=addr a d.val)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (leadEq : lead=((ackLead++[ack])++beforeIssue)++issue::loadTrail)
    (loadPrefix : whole=lead++after)
    (history : GeneratedOwner hp base (fun t => S.getD t fall) len
      (ring (play x ackLead) ack) .idle beforeIssue m)
    (region : ∀ p q,beforeIssue=p++q →
      let y := play x ((ackLead++[ack])++p)
      Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ w,oldH6 B (play x (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play x (cut++w)) e z
      (endpoint (oldH6 B base) hh owner 0).1)
    (ack0 : ((capturedSelector 0).read (ring (play x ackLead) ack (S.getD 0 fall).1).long).toNat=
      (BStarLongPublication.readSel ((play x A.lead) (endpoint (oldH6 B base) hh owner 0).1).long).val)
    (C : CommandClaim) (k j : Nat) (kl : k≤len) (jl : j≤len)
    (injectAddr : S.getD j fall=(site load side,5))
    (loadLoc : address load C.source=S.getD k fall)
    (source : C.source=⟨side,0⟩)
    (selected : C∈orderedCommands (oldPair B (play x lead) load))
    (noDoor : C.kind≠.door)
    (inside : (geometry (oldPair B (play x lead) load) side).inside=true)
    (own : dataOwner (oldH6 B base) (site load side) .ls=owner.val)
    (before : GeneratedOwner hp base (fun t => S.getD t fall) len x .idle lead (.busy 8 (.out k)))
    (loadEvent : Event hp (fun t => S.getD t fall) len (play x lead) load
      (.busy 8 (.out k)) (.busy 8 (.out (k+1))))
    (b8 : BusyOnly hp base (fun t => S.getD t fall) len 8 (ring (play x lead) load) (.out (k+1)) w8 (.back 0))
    (M : OwnMiddle hp base x (fun t => S.getD t fall) len ((lead++[load])++w8) middle)
    (b10 : BusyOnly hp base (fun t => S.getD t fall) len 10
      (play x (((lead++[load])++w8)++middle)) (.out 0) w10 (.out j))
    (fiber : ∀ a b, ((((lead++[load])++w8)++middle)++w10)=a++b →
      ∀ v,Layout B base v=Layout B (play x a) v)
    (L : Launch (play x ((ackLead++[ack])++beforeIssue) (S.getD 0 fall).1).long
      (ring (play x ((ackLead++[ack])++beforeIssue)) issue (S.getD 0 fall).1).long)
    (op8 : (ctrlOp.read (play x ((ackLead++[ack])++beforeIssue) (S.getD 0 fall).1).long).toNat=8)
    (T : LoadWord hp (ring (play x ((ackLead++[ack])++beforeIssue)) issue)
      ((S.getD 0 fall).1,0) loadTrail (address load C.source)) :
    (readLane (Sheet.index .ls)
      (play x ((((lead++[load])++w8)++middle)++w10) (site load side)).long).frozen =
      oldBankPacket (play x A.lead (site load side)).long
        (BStarLongPublication.readSel (play x A.lead (endpoint (oldH6 B base) hh owner 0).1).long) := by
  have current := BStarGeneratedTapeCuts.at_end hp before
  have replay : play x lead=play (ring (play x ((ackLead++[ack])++beforeIssue)) issue) loadTrail := by
    rw [leadEq,BStarResetSchedule.run_append]
    rfl
  obtain ⟨bank,bank8,F⟩ := pointed_freeze_from_launch hp chart L op8 loadTrail load side false C
    (sep load) k T (replay ▸ current) loadLoc own (replay ▸ selected) noDoor source (replay ▸ inside)
  rw [←replay] at F
  have K := packed_after_actual_ack hp hh owner chart a seam width strip root bound A common ackLead
    beforeIssue loadTrail after ack issue m birthBeforeAck (loadPrefix.trans (congrArg (·++after) leadEq))
    history region sep layout auth bank bank8 ack0 d
  dsimp only at K
  rw [←leadEq,←atDigit] at K
  exact (after_load_frame hp chart sep lead w8 middle w10 load side C k j kl jl injectAddr
    loadLoc source own before loadEvent b8 M b10 fiber).trans (F.trans K)

end L4.BStarCopyLeftAckRetention
