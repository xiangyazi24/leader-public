import Leader.L4.BStarCopyRightAcquireBank
import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarCopyRightAckRetention
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

/-- The exact controller trace in the post-ACK band supplies the
live-capture mark requirements automatically. A second matching
ACQUIRE installation cannot occur while the old PC is in band. -/
theorem live_capture_band {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m m' : Mode}
    (hist : GeneratedOwner hp base (fun t => S.getD t fall) len x m w m')
    (region : ∀ a b, w=a++b →
      Band (play x a) (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B (play x a) i)) :
    LiveWord hp (S.getD 0 fall).1 x w := by
  induction hist with
  | endpoint _ =>
    intro a e b Eq
    have K := congrArg List.length Eq
    simp only [List.length_nil,List.length_append,List.length_cons] at K
    omega
  | @next x m e w d fin I E tail ih =>
    intro a f b Eq
    cases a with
    | nil =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj Eq
      have before := region [] (e::w) rfl
      have after := region [e] w rfl
      have J := BStarGeneratedTapeCuts.at_start hp tail
      rcases reflect hp chart before.2 sep e m d I J E after.1 with good|⟨p,_,K,_,_,_,_,_,_⟩
      · exact good
      · subst m
        have oldPc : pc x (S.getD 0 fall).1=5 := I.1.2.2.2
        have band := before.1.1
        change 6≤pc x (S.getD 0 fall).1 at band
        omega
    | cons s a =>
      obtain ⟨rfl,Q⟩ := List.cons.inj Eq
      exact ih (fun a b E => region (e::a) b (congrArg (List.cons e) E)) a f b Q

/-- From the real ACK cut to the real ISSUE8 old cut, preserve the
six capture bits on every raw mark. The resulting next bank selection
is the one installed by the original ACK, not current header state. -/
theorem captures_on_original_cut {base original : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ackLead beforeIssue : List (Fin n)) (ack : Fin n) (m : Mode)
    (H : GeneratedOwner hp base (fun t => S.getD t fall) len
      (ring (play original ackLead) ack) .idle beforeIssue m)
    (region : ∀ a b,beforeIssue=a++b →
      let y := play original ((ackLead++[ack])++a)
      Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)) :
    let root := (S.getD 0 fall).1
    captures.read (play original ((ackLead++[ack])++beforeIssue) root).long=
      captures.read (ring (play original ackLead) ack root).long := by
  let y := ring (play original ackLead) ack
  have replay (u : List (Fin n)) : play original ((ackLead++[ack])++u)=play y u := by
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rfl
  have live := live_capture_band hp chart sep H (fun a b E => by
    have Q := region a b E
    change Band (play original ((ackLead++[ack])++a)) (S.getD 0 fall).1 ∧
      (∀ i,Layout B base i=Layout B (play original ((ackLead++[ack])++a)) i) at Q
    rw [replay] at Q
    exact Q)
  dsimp only
  rw [replay]
  exact (word_capture_hold hp y (S.getD 0 fall).1 beforeIssue sep
    (fun a e b Q => (live a e b Q).2)).2.1

open BStarCommitOperands BStarCutOperandReadout BStarCopyRightStrip
open BStarCopyRightAcquireBank BStarClearanceDataChart BStarLongCommandData

/-- Crop the original COMMIT-acquisition witness to an earlier
LOAD prefix after the same ACK, using only equalities of raw words. -/
theorem cut_after_matching_ack {x : X} {cut whole : List (Fin n)} {header : Fin n}
    (A : Acquisition hp x cut whole header 2)
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
incidence 2 to the immutable packed bytes on any selected LOAD cut
within that same acquired lifetime. Retention of the source's low
capture is derived on the exact ACK→ISSUE8 raw word. -/
theorem packed_after_actual_ack {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh owner S len fall)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=owner.val)
    (width : seam+r-1≤tail)
    (A : Acquisition hp x cut whole (endpoint (oldH6 B base) hh owner 2).1 2)
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
      (endpoint (oldH6 B base) hh owner 2).1)
    (bank : Fin 3)
    (bank8 : bank.val=(captures.read (play x ((ackLead++[ack])++beforeIssue) (S.getD 0 fall).1).long).toNat%4)
    (ack2 : ((capturedSelector 2).read (ring (play x ackLead) ack (S.getD 0 fall).1).long).toNat=
      (BStarLongPublication.readSel ((play x A.lead) (endpoint (oldH6 B base) hh owner 2).1).long).val) :
    ∀ digit : Fin r,
      let i := addr a (seam+digit.val)
      let old := play x (((ackLead++[ack])++beforeIssue)++issue::loadTrail)
      let captured := play x A.lead
      let header := (endpoint (oldH6 B base) hh owner 2).1
      oldBankPacket (old i).long bank =
        oldBankPacket (captured i).long (BStarLongPublication.readSel (captured header).long) := by
  let loadLead := ((ackLead++[ack])++beforeIssue)++issue::loadTrail
  have ackBefore : ∃ t,loadLead=ackLead++ack::t := by
    refine ⟨beforeIssue++issue::loadTrail,?_⟩
    simp [loadLead,List.append_assoc]
  obtain ⟨p,u,P,U,V⟩ := cut_after_matching_ack hp A common ackLead loadLead after ack
    birthBeforeAck ackBefore loadPrefix
  have kept := captures_on_original_cut hp chart sep ackLead beforeIssue ack m history region
  intro d
  dsimp only
  change oldBankPacket ((play x loadLead) (addr a (seam+d.val))).long bank=_
  rw [P]
  exact packed_before_load hp hh owner a seam tail strip ownerHead width A u after p V
    (P.symm.trans U) sep layout auth _ _ bank bank8 kept ack2 d

end L4.BStarCopyRightAckRetention
