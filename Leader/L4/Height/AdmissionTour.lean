import Leader.L4.Height.FreshAttempt
import Leader.L4.BStarCopyOwnedFrozen
import Leader.L4.BStarGateStutter
import Leader.L4.BStarAcquireAckAncestry
import Leader.L4.BStarStageTerminalHealth
import Leader.L4.BStarCommitNoPrior

import Leader.L4.BStarFenceReceiverChart
namespace L4.AdmissionOffset
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarH6Ordinal
open BStarAcquireAnchors BStarLongFiberOwner BStarFenceReceiverChart

private theorem word_at_back {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (k : Nat) (i : Fin n) (K : ordinal h hh i=k) :
    word h (back i k)=word h i := by
  induction k generalizing i with
  | zero => rw [back_zero]
  | succ k ih =>
    let prev := RearTrace.predecessor i
    have E : rightNeighbor prev=i := RearTrace.right_predecessor i
    have H : h i=false := Bool.eq_false_iff.mpr (fun U => by
      have Z := (ordinal_zero h hh i).mpr U; omega)
    have P := ordinal_body h hh prev (E.symm ▸ H)
    rw [E,K] at P
    have Q := ih prev (by omega)
    rw [←E,back_right_succ,E]
    have R := right_word h prev
    rw [E,H] at R
    obtain ⟨lo,hi⟩ := word_range h prev hh
    simp only [Bool.toNat_false,Int.natCast_zero,Int.add_zero,Int.emod_eq_of_lt lo hi] at R
    exact Q.trans R.symm

private theorem digit_back {n : Nat} (i : Fin n) (k : Nat) :
    digitFrom (back i k) k=i := by
  induction k generalizing i with
  | zero => simp [digitFrom,back_zero]
  | succ k ih =>
    let prev := RearTrace.predecessor i
    have E : rightNeighbor prev=i := RearTrace.right_predecessor i
    have P : back i (k+1)=back prev k := by rw [←E,back_right_succ]
    rw [P]
    change rightNeighbor (digitFrom (back prev k) k)=i
    rw [ih,E]

theorem same_ordinal_same_word {n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (i j : Fin n) (O : ordinal h hh i=ordinal h hh j) (W : word h i=word h j) : i=j := by
  let k := ordinal h hh i
  have Hi : h (back i k)=true := (ordinal_spec h hh i).2.1
  have Hj : h (back j k)=true := by rw [show k=ordinal h hh j from O]; exact (ordinal_spec h hh j).2.1
  have T := header_word_injective h (a₁:=⟨back i k,Hi⟩) (a₂:=⟨back j k,Hj⟩)
    ((word_at_back h hh k i rfl).trans (W.trans (word_at_back h hh k j O.symm).symm))
  have T' := congrArg Subtype.val T
  exact (digit_back i k).symm.trans ((congrArg (fun a => digitFrom a k) T').trans (digit_back j k))

end L4.AdmissionOffset

namespace L4.Height.AdmissionTour
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongEvents BStarLongRouting
open BStarLongLiteral BStarLongCommandData BStarResetQuiet BStarResetQuietTable
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarGeneratedPCAncestry BStarLiteralPC BStarResetControllerProgress
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarResetQuietAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService BStarClearanceSource
open BStarLongDoor BStarResetControllerEntry BStarClearanceOffset BStarAdmitIncidentGeometry
open BStarBitParity
open BStarLongLayout (kField)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def opcode (admission : Bool) : Nat := if admission then admit else 3

def packet (admission decision : Bool) : Payload :=
  if admission then FreshAttempt.admitReply decision else ⟨0,3,0,0,0⟩

def atGate (z : BitVec 3) : Payload := {packet true false with race:=z}

theorem pace_has_no_gate (g : LongGeometry) (j : Fin 11) :
    gate (opcode false) j g=false := by
  simp [opcode,gate,admit,bitOp]

private theorem packet_opcode (a b : Bool) : (packet a b).opcode.toNat=opcode a := by
  cases a <;> rfl

private theorem packet_fault (a b : Bool) : (packet a b).fault=0 := by
  cases a <;> rfl

theorem packet_bound (g : LongGeometry) (j : Fin 11) (a b : Bool)
    (off : gate (opcode a) j g=false) :
    BStarLongCommand.bind g j (.forward (packet a b))=.forward (packet a b) := by
  cases a
  · exact (BStarAdmissionPaceCore.pace_unit_packet g j).1
  · change gate 4 j g=false at off
    cases b <;> simp [packet,FreshAttempt.admitReply,BStarLongCommand.bind,off,
      forwardWidth,admit,bitOp,cropped,low]

theorem packet_finish (a b : Bool) :
    finish (packet a b)=.reply (packet a b) ∧
      BStarReplyBack.normal (packet a b)=.reply (packet a b) := by
  cases a <;> cases b <;> decide

private theorem packet_depart (g : LongGeometry) (j : Fin 11) (a b : Bool)
    (off : gate (opcode a) j g=false) :
    depart g j (packet a b)=some (packet a b) := by
  simp [depart,packet_opcode,off]

private theorem packet_arrive (g : LongGeometry) (j : Fin 11) (a b : Bool) :
    arrive g j (packet a b)=
      if gate (opcode a) j g then .forward (atGate 1) else .forward (packet a b) := by
  cases a
  · exact by simpa only [pace_has_no_gate,if_false,Bool.false_eq_true,packet] using
      (BStarAdmissionPaceCore.pace_unit_packet g j).2.2.1
  · cases b <;> simp [arrive,packet,opcode,atGate,FreshAttempt.admitReply,admit]

theorem gate_packet_bound (g : LongGeometry) (z : BitVec 3)
    (gateHere : gate admit 1 g=true) (range : 1≤z.toNat ∧ z.toNat≤5) :
    BStarLongCommand.bind g 1 (.forward (atGate z))=.forward (atGate z) :=
  BStarGateStutter.rebind_gate_race g false (packet true false) z
    (by rfl) (by rfl) (by rfl) (by rfl) gateHere range

private theorem packet_carried (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (a b : Bool) :
    BStarClearanceForward.carried g x C (packet a b)=packet a b := by
  have p3 : BStarLongArithmetic.nodeOf 3=none := by decide
  have p4 : BStarLongArithmetic.nodeOf 4=none := by decide
  cases a <;> cases b <;>
    simp [BStarClearanceForward.carried,BStarLongArithmetic.visit,BStarLongOutgoing.execute,
      BStarLongOutgoing.hold,packet,FreshAttempt.admitReply,p3,p4,stageOp,sealOp,commitOp]

private theorem bound_departure_selected (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (v : Payload) (a b : Bool)
    (mem : C∈orderedCommands g) (nonDoor : C.kind≠.door)
    (old : bound g (readK raw) C.source=.forward v)
    (leaves : depart (geometry g C.source.side) C.source.occurrence v=some (packet a b)) :
    (C,.advance (packet a b))∈actualOffers g raw := by
  let t := packet a b
  have checks : gatedAt g raw C=.advance t := by
    unfold gatedAt classifyOld
    change checkOffer g _ (C,classify C _ (bound g (readK raw) C.source) _) = _
    rw [old]
    have small : t.opcode.toNat≠11 := by cases a <;> cases b <;> decide
    simp [t,classify,nonDoor,leaves,checkOffer,checkFence,show (packet a b).opcode.toNat≠11 from small]
  have gatedMem := (gated_mem g raw C (.advance t)).mpr ⟨mem,checks.symm⟩
  have noPrep : C.source∉(round g raw).faults := by
    intro H
    change C.source∈BStarLongPrep.prepFaults (BStarLongPrep.view raw) (round g raw).prep at H
    simp only [BStarLongPrep.prepFaults,BStarResetNoFault.arb_no_losers g raw,
      List.map_nil,List.nil_append] at H
    obtain ⟨u,M,src⟩ := List.mem_map.mp H
    obtain ⟨win,_⟩ := List.mem_filter.mp M
    obtain ⟨K,f,_,F,_,prep,_,origin,_,_⟩ := BStarCopyOwnedFrozen.winner_origin g raw u win
    obtain ⟨memK,checkK⟩ := (gated_mem g raw K (.advance f)).mp F
    have eq : K=C := BStarResetNoFault.origin_unique g K C memK mem (origin.symm.trans src)
    subst K
    have eq : f=t := Offer.advance.inj (checkK.trans checks)
    subst f
    have impossible : prepOf t.opcode.toNat=none := by cases a <;> cases b <;> decide
    rw [impossible] at prep
    contradiction
  have offered : (C,.advance t)∈(round g raw).offered := by
    exact List.mem_map.mpr ⟨(C,.advance t),gatedMem,by
      change cancel (round g raw).faults (C,Offer.advance t) = _
      simp only [cancel,if_neg noPrep]⟩
  unfold actualOffers BStarLongGrant.run
  refine List.mem_map.mpr ⟨(C,.advance t),offered,?_⟩
  have notAcquire : t.opcode.toNat≠acquire := by cases a <;> cases b <;> decide
  by_cases small : C.source.occurrence.val<3 <;>
    simp [BStarLongGrant.update,small,notAcquire]; all_goals rfl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- The literal selected command link carries a PACE or ADMIT packet.
The departing gate payload may have its completed race code instead. -/
theorem joined_link (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (dst : AtK) (v : Payload) (a b : Bool) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.destination=some dst →
    bound g (readK raw) C.source=.forward v →
    depart (geometry g C.source.side) C.source.occurrence v=some (packet a b) →
    readK (Pair.map LargeSite.long (largePair B x)) dst =
      if gate (opcode a) dst.occurrence (geometry g dst.side)
      then .forward (atGate 1) else .forward (packet a b) := by
  dsimp only
  intro mem hd source departure
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have shape := BStarAcquireReturn.link_shape g C dst mem hd
  have sel := bound_departure_selected g raw C v a b mem (by rw [shape.2.1]; decide) source departure
  have valid : dst=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E H
    have Z := congrArg (fun z : AtK=>z.occurrence.val) E
    have body := (BStarAcquireJoinedHop.k0_dest g C dst mem hd Z).2
    simp [H] at body
  have lands := (BStarClearanceForward.move_lands g raw C (packet a b) dst hd sel (Ne.symm shape.1)).2
  rw [BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp x dst (by
    intro h k
    cases H : g.2.axes.h6
    · exact .inl rfl
    · have E : dst=R 0 := by cases dst; simp_all [R]
      exact .inr (valid E H))]
  change decode (readRaw (patchPair (longWork g raw) raw) dst)=_
  rw [lands,decode_encode]
  change arrive _ _ (BStarClearanceForward.carried g raw C (packet a b)) = _
  rw [packet_carried g raw C a b]
  exact packet_arrive _ _ _ _

theorem pace_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=3) (good : f.fault=0) (same : f.opcode.toNat=3) :
    pcNext old f=admit := by
  simp [pcNext,op,good,same,show (arithKind 3).isSome=false by decide,nextOrdinary,admit]

theorem actual_pace_consumes_to_admit {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy 3 (.back 0)))
    (evt : Event hp addr len x e (.busy 3 (.back 0)) .idle)
    (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=3)
    (w : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f) :
    snapshot (step x e (addr 0).1).long=((.empty,1),BitVec.ofNat 9 admit) := by
  obtain ⟨g,G,E⟩ := consume_exact hp H hh sep cur evt
  have eq := Token.reply.inj (G.symm.trans w)
  subst g
  rw [pace_successor _ _ cur.1.2.2.2 F O] at E
  exact E

/-- The literal terminal handler preserves the canonical decision bit. -/
theorem joined_terminal (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a b : Bool) :
    let g := Pair.map (longGeometry B) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.kind=.terminal → C.destination=none → C.source.occurrence.val=10 →
    gate (opcode a) C.source.occurrence (geometry g C.source.side)=false →
    readK raw C.source=.forward (packet a b) →
    readK (Pair.map LargeSite.long (largePair B x)) C.source=.reply (packet a b) := by
  dsimp only
  intro mem kind hd port off src
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have boundOld : bound g (readK raw) C.source=.forward (packet a b) := by
    unfold bound
    rw [src,packet_bound _ _ _ _ off]
  have sel := bound_departure_selected g raw C (packet a b) a b mem (by rw [kind]; decide)
    boundOld (packet_depart _ _ _ _ off)
  rw [BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp x C.source (by intro _ zero; omega)]
  change decode (readRaw (patchPair (longWork g raw) raw) C.source)=_
  rw [terminal_finish g raw C (packet a b) hd sel,decode_encode]
  change finish (BStarClearanceForward.carried g raw C (packet a b)) = _
  rw [packet_carried g raw C a b]
  exact (packet_finish _ _).1

private theorem quiet_route (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (boundOld : bound g (readK raw) a=.forward p) (healthy : p.fault=0)
    (noObservation : observe a (geometry g a.side) p=none)
    (keep : a∉discarded g) (mid : avoids a (middle g raw)) :
    avoids a (routing g raw) := by
  rw [routing_parts]
  intro w hw E
  rcases w with ⟨q,t⟩
  change q=a at E
  subst q
  rcases List.mem_append.mp hw with H|H
  · rcases List.mem_append.mp H with H|H
    · rcases List.mem_append.mp H with H|H
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
        dsimp only at Q
        split at Q
        · have eq := congrArg Prod.fst (Option.some.inj Q)
          change q=a at eq
          subst q
          rename_i faulty
          rw [boundOld] at faulty
          simp [isFault,healthy] at faulty
        · contradiction
      · obtain ⟨q,h,Q⟩ := List.mem_map.mp H
        have eq := congrArg Prod.fst Q
        change q=a at eq
        subst q
        exact keep h
    · exact mid _ H rfl
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
    split at Q
    · contradiction
    · split at Q
      all_goals try contradiction
      rename_i f hf
      cases eq : observe q (geometry g q.side) f with
      | none => simp [eq] at Q
      | some v =>
        rw [eq] at Q
        have same := congrArg Prod.fst (Option.some.inj Q)
        change q=a at same
        subst q
        rw [boundOld] at hf
        cases hf
        rw [noObservation] at eq
        contradiction

open BStarAcquireNonRouting (actual_door actual_hold) in
private theorem local_middle_quiet (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK)
    (p : Payload) (boundOld : bound g (readK raw) a=.forward p)
    (noOut : ∀ C∈orderedCommands g, C.source=a → C.kind=.door)
    (oldTrail : ∀ C∈orderedCommands g, C.destination=some a → readK raw C.source=.trail) :
    avoids a (middle g raw) := by
  apply middle_avoids_of_chart
  rintro ⟨C,t⟩ ht touch w hw eq
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨(C,t),ht,rfl⟩
  have incident : a=C.source ∨ C.destination=some a := by
    cases dc : C.destination <;> simpa [Claim.slots,dc,eq_comm] using touch
  rcases incident with hs|hd
  · have door := noOut C mem hs.symm
    have H : gatedAt g raw C=.door (bound g (readK raw) a) := by
      unfold gatedAt classifyOld
      simp [door,classify,hs,checkOffer,bound,readK,oldTokens]
    have Q := actual_door g raw (C,t) ht _ H
    dsimp only at Q
    subst t
    unfold selected at hw
    dsimp only at hw
    split at hw <;> cases hw
  · have kind := (BStarAcquireReturn.link_shape g C a mem hd).2.1
    have H : gatedAt g raw C=.hold := by
      unfold gatedAt classifyOld
      change checkOffer g _ (C,classify C _ (bound g (readK raw) C.source)
        ((C.destination.map (bound g (readK raw))).getD .empty))=.hold
      rw [hd,Option.map_some,Option.getD_some,boundOld]
      have K : bound g (readK raw) C.source=.trail := by
        simp [bound,oldTrail C mem hd,BStarLongCommand.bind]
      rw [K]
      simp [classify,kind,checkOffer]
    have Q := actual_hold g raw (C,t) ht H
    dsimp only at Q
    subst t
    cases hw

/-- A mark missing the selected link and terminal leaves the exact
canonical old payload whenever the old observer is disabled. This
includes a completed gate waiting for its selected physical link. -/
theorem silent {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (e : Fin n) (sep : e≠rightNeighbor e) (op k : Nat)
    (W : Waiting hp base (S.getD 0 fall).1 op x)
    (oldGood : Good anyTag len (project (fun j=>S.getD j fall) x) (.out k))
    (p : Payload) (F : project (fun j=>S.getD j fall) x k=.forward p)
    (healthy : p.fault=0)
    (binding : let a := S.getD k fall
      BStarLongCommand.bind (longGeometry B (x a.1)) a.2 (.forward p)=.forward p)
    (quiet : ∀ s : Side, let a := S.getD k fall
      observe ⟨s,a.2⟩ (longGeometry B (x a.1)) p=none)
    (noL : ¬linkAt hp x e (fun j=>S.getD j fall) len k)
    (noT : k=len → ¬onTerminal hp x e (fun j=>S.getD j fall) len) :
    project (fun j=>S.getD j fall) (step x e) k=.forward p := by
  let addr := fun j=>S.getD j fall
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old (j : Nat) (a : AtK) (A : addr j=address e a) :
      readK raw a=project addr x j :=
    (old_read x e a).trans ((congrArg (atCursor x) A).symm)
  have frame (a : AtK) (E : addr k=address e a) :
      project addr (step x e) k=project addr x k := by
    have noOut (cl : CommandClaim) (hcl : cl∈orderedCommands g) (src : cl.source=a) :
        cl.kind=.door := by
      subst a
      rcases touches hp C W.1 e k oldGood.1 cl cl.source hcl (by simp [Claim.slots]) E with D|T|L|⟨i,ik,I⟩
      · exact D.2.1
      · exact (noT T.1 T.2).elim
      · exact (noL L).elim
      · obtain ⟨_,J,d,mem,hd,_,dst⟩ := I
        have eq : cl.source=d := address_inj e sep (E.symm.trans (ik ▸ dst))
        have same := BStarAcquireIncidence.same_claim g cl J cl.source hcl mem
          (by simp [Claim.slots]) (by simp [Claim.slots,hd,eq])
        subst J
        exact ((BStarAcquireReturn.link_shape g cl d hcl hd).1 eq.symm).elim
    have noPred (cl : CommandClaim) (hc : cl∈orderedCommands g) (hd : cl.destination=some a) :
        readK raw cl.source=.trail := by
      obtain ⟨_,kind,_⟩ := BStarAcquireReturn.link_shape g cl a hc hd
      rcases touches hp C W.1 e k oldGood.1 cl a hc (by simp [Claim.slots,hd]) E with D|T|L|⟨i,ik,I⟩
      · rw [kind] at D; cases D.2.1
      · exact (noT T.1 T.2).elim
      · exact (noL L).elim
      · obtain ⟨_,J,d,mem,dh,src,dst⟩ := I
        have ed : a=d := address_inj e sep (E.symm.trans (ik ▸ dst))
        have same := BStarAcquireIncidence.same_claim g cl J a hc mem
          (by simp [Claim.slots,hd]) (by simp [Claim.slots,dh,ed])
        subst J
        exact (old _ _ src).trans (oldGood.2.2 i (by omega))
    have bind' : bound g (readK raw) a=.forward p := by
      unfold bound
      rw [(old k a E).trans F]
      change BStarLongCommand.bind (longGeometry B (x (addr k).1)) (addr k).2 _ = _ at binding
      rw [E] at binding
      cases a with
      | mk s j => cases s <;> exact binding
    have observe' : observe a (geometry g a.side) p=none := by
      have same := quiet a.side
      dsimp only at same
      change observe ⟨a.side,(addr k).2⟩ (longGeometry B (x (addr k).1)) p=none at same
      rw [E] at same
      cases a with
      | mk s j => cases s <;> exact same
    have MF := frames_any hp C W.1 e (.out k) (by intro zz; cases zz) oldGood W.2.1 W.2.2.1
    obtain ⟨keep,safe⟩ := MF.safe k oldGood.1 a E
    have route := quiet_route g raw a p bind' healthy observe' keep
      (local_middle_quiet g raw a p bind' noOut noPred)
    have post := (new_read B x e sep a).trans ((congrArg (atCursor (step x e)) E).symm)
    exact post.symm.trans ((BStarAcquireHistorySample.joined_silent _ _ _ _ _ _ _ _ _ hp
      (x e,x (rightNeighbor e)) a safe route).trans (old _ _ E))
  have stay : project addr (step x e) k=project addr x k := by
    by_cases l : (addr k).1=e
    · exact frame (L (addr k).2) (Prod.ext l rfl)
    · by_cases r : (addr k).1=rightNeighbor e
      · exact frame (R (addr k).2) (Prod.ext r rfl)
      · exact BStarResetIdleRing.idle_off_pair hp x e (addr k) l r
  exact stay.trans F

def settledGate (decision : Bool) : Payload :=
  atGate (BitVec.ofNat 3 (4+decision.toNat))

def resolved (a b : Bool) (gateIdx : Option Nat) (j : Nat) : Payload :=
  if gateIdx=some j then settledGate b else packet a b

private theorem resolved_rules (g : LongGeometry) (slot : Fin 11)
    (a b : Bool) (gateIdx : Option Nat) (j : Nat)
    (isGate : gate (opcode a) slot g=true ↔ gateIdx=some j)
    (shape : gateIdx=some j → a=true ∧ slot=1) :
    let f := resolved a b gateIdx j
    f.fault=0 ∧ BStarLongCommand.bind g slot (.forward f)=.forward f ∧
      depart g slot f=some (packet a b) ∧ ∀ side : Side, observe ⟨side,slot⟩ g f=none := by
  dsimp only
  by_cases H : gateIdx=some j
  · obtain ⟨rfl,rfl⟩ := shape H
    have on : gate admit 1 g=true := isGate.mpr H
    rw [resolved,if_pos H]
    refine ⟨rfl,gate_packet_bound g _ on (by cases b <;> decide),?_,?_⟩
    · exact FreshAttempt.admit_gate_departure g 1 on b
    · intro s
      cases s <;> cases b <;>
        simp [observe,settledGate,atGate,packet,FreshAttempt.admitReply,show gate 4 1 g=true from on]
  · have off : gate (opcode a) slot g=false := Bool.eq_false_iff.mpr (fun K=>H (isGate.mp K))
    rw [resolved,if_neg H]
    refine ⟨packet_fault a b,packet_bound g slot a b off,packet_depart g slot a b off,?_⟩
    intro s
    simp [observe,packet_opcode,off]

private theorem terminal_reply {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (_C : Chart hp base hh o S len fall)
    (e : Fin n) (sep : e≠rightNeighbor e) (a b : Bool)
    (term : onTerminal hp x e (fun j=>S.getD j fall) len)
    (F : project (fun j=>S.getD j fall) x len=.forward (packet a b)) :
    project (fun j=>S.getD j fall) (step x e) len=.reply (packet a b) := by
  obtain ⟨cl,mem,kind,none,k10,idx⟩ := term
  have read : readK ((x e).long,(x (rightNeighbor e)).long) cl.source=.forward (packet a b) :=
    (old_read x e cl.source).trans ((congrArg (atCursor x) idx).symm.trans F)
  have off : gate (opcode a) cl.source.occurrence (geometry (oldPair B x e) cl.source.side)=false := by
    have slot : cl.source.occurrence=10 := Fin.ext k10
    rw [slot] <;> rfl
  exact (congrArg (atCursor (step x e)) idx).trans ((new_read B x e sep cl.source).symm.trans
    (joined_terminal hp (x e,x (rightNeighbor e)) cl a b mem kind none k10 off read))

private theorem seen_advance {len : Nat} {x : X} {e : Fin n} {addr : Nat→Pos n}
    {z d : Cursor} (H : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases H with
  | cons _ _ A _ tail => cases tail; exact A

/-- All emitted marks from a completed ADMIT gate to the terminal
preserve its decided bit. The gate-free instance covers all of PACE.
Scope means exactly one current chart occurrence binds as the gate. -/
theorem resolved_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a b : Bool) (gateIdx : Option Nat)
    (shape : ∀ j,gateIdx=some j → j<len ∧ a=true ∧ (S.getD j fall).2=1)
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len (opcode a) x z w d) :
    ∀ (k l : Nat), z=.out k → d=.out l →
      (∀ j,gateIdx=some j → j≤k) →
      (∀ pre tail,w=pre++tail → ∀ j≤l,
        gate (opcode a) (S.getD j fall).2 (longGeometry B (run x pre (S.getD j fall).1))=true ↔
          gateIdx=some j) →
      project (fun j=>S.getD j fall) x k=.forward (resolved a b gateIdx k) →
      project (fun j=>S.getD j fall) (run x w) l=.forward (resolved a b gateIdx l) := by
  induction P with
  | nil _ =>
    intro k l K L _ _ F
    have eq : k=l := Cursor.out.inj (K.symm.trans L)
    subst l
    exact F
  | @cons raw z d final e w I E tail ih =>
    intro k l Z D lower scope old
    subst z
    obtain ⟨k',Q⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,D⟩
    subst d
    have adv : Advance len (.out k) (.out k') := by
      cases E
      case transit H => exact seen_advance hp H
    have nextLe := BStarCommitNoPrior.outward_mono hp tail k' l rfl D
    have oldLe : k≤l := by cases adv <;> omega
    let addr := fun j=>S.getD j fall
    let g := oldPair B raw e
    let bytes : Pair (BitVec LW) := ((raw e).long,(raw (rightNeighbor e)).long)
    let f := resolved a b gateIdx k
    have scope0 := scope [] (e::w) rfl
    have scope1 (pre rest : List (Fin n)) (W : w=pre++rest) :
        ∀ j≤l, gate (opcode a) (addr j).2 (longGeometry B (run (step raw e) pre (addr j).1))=true ↔
          gateIdx=some j :=
      scope (e::pre) rest (congrArg (List.cons e) W)
    have limit : k≤len := I.2.1.1
    obtain ⟨healthy,bindOld,departOld,quiet⟩ :=
      resolved_rules (longGeometry B (raw (addr k).1)) (addr k).2 a b gateIdx k
        (scope0 k oldLe) (fun h=>(shape k h).2)
    have post := busy_start hp tail
    have uniq : ∀ i≤len, anyTag.F (project addr (step raw e) i) ↔ i=k' :=
      BStarOwnerControlHistory.pointed_unique_forward _ _ _ post.2.1 post.2.2
    by_cases link : linkAt hp raw e addr len k
    · obtain ⟨lt,cl,dst,mem,hd,source,target⟩ := link
      have geom (u : AtK) (j : Nat) (H : addr j=address e u) :
          geometry g u.side=longGeometry B (raw (addr j).1) := by
        rw [H]
        cases u with
        | mk side slot => cases side <;> rfl
      have srcSlot : cl.source.occurrence=(addr k).2 := congrArg Prod.snd source.symm
      have src : readK bytes cl.source=.forward f :=
        (old_read raw e cl.source).trans ((congrArg (atCursor raw) source).symm.trans old)
      have bnd : bound g (readK bytes) cl.source=.forward f := by
        unfold bound
        rw [src,geom _ _ source,srcSlot]
        exact bindOld
      have dep : depart (geometry g cl.source.side) cl.source.occurrence f=some (packet a b) := by
        rw [geom _ _ source,srcSlot]
        exact departOld
      have tgtSlot : dst.occurrence=(addr (k+1)).2 := congrArg Prod.snd target.symm
      have skip : gateIdx≠some (k+1) := by
        intro eq
        have H := lower (k+1) eq
        omega
      have lands := joined_link hp (raw e,raw (rightNeighbor e)) cl dst f a b mem hd bnd dep
      change readK (Pair.map LargeSite.long (largePair B (raw e,raw (rightNeighbor e)))) dst =
        (if gate (opcode a) dst.occurrence (geometry g dst.side) then _ else _) at lands
      rw [geom _ _ target,tgtSlot] at lands
      have value := (congrArg (atCursor (step raw e)) target).trans
        ((new_read B raw e (sep e) dst).symm.trans lands)
      have tagged : anyTag.F (project addr (step raw e) (k+1)) := by
        change anyTag.F (atCursor (step raw e) (addr (k+1)))
        rw [value]
        split <;> exact ⟨_,rfl⟩
      have eq := (uniq (k+1) (by omega)).mp tagged
      have off : gate (opcode a) (addr (k+1)).2 (longGeometry B (raw (addr (k+1)).1))=false :=
        Bool.eq_false_iff.mpr (fun H=>skip ((scope0 _ (eq.symm ▸ nextLe)).mp H))
      have F : project addr (step raw e) (k+1)=.forward (resolved a b gateIdx (k+1)) := by
        rw [resolved,if_neg skip]
        rw [off,if_neg (by decide : ¬ false=true)] at value
        exact value
      exact ih (k+1) l (congrArg Cursor.out eq.symm) D
        (fun j J=>Nat.le_succ_of_le (lower j J)) scope1 F
    · have notT : k=len → ¬onTerminal hp raw e addr len := by
        intro K H
        have skip : gateIdx≠some k := by
          intro eq
          have early := (shape k eq).1
          omega
        have atEnd : project addr raw len=.forward (packet a b) := by
          rwa [resolved,if_neg skip,K] at old
        have R := terminal_reply hp C e (sep e) a b H atEnd
        have same : k'=len := by
          have lim := post.2.1.1
          cases adv <;> omega
        obtain ⟨p,postF⟩ := post.2.1.2.1
        rw [same] at postF
        exact Token.noConfusion (R.symm.trans postF)
      have F := silent hp C e (sep e) (opcode a) k I.1 I.2.1 f old
        healthy bindOld quiet link notT
      have eq := (uniq k limit).mp ⟨_,F⟩
      exact ih k l (congrArg Cursor.out eq.symm) D lower scope1 F

/-- A completed outward and return tour consumes the exact PACE or
settled ADMIT packet. In particular a right-first rival schedules
DUMMY on that raw mark. -/
theorem resolved_consumes {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a b : Bool) (gateIdx : Option Nat) (k : Nat)
    (shape : ∀ j,gateIdx=some j → j<len ∧ a=true ∧ (S.getD j fall).2=1)
    {w : List (Fin n)} (P : BusyOnly hp base (fun j=>S.getD j fall) len (opcode a)
      x (.out k) w (.back 0))
    (lower : ∀ j,gateIdx=some j → j≤k)
    (scope : ∀ pre rest,w=pre++rest → ∀ j≤len,
      gate (opcode a) (S.getD j fall).2 (longGeometry B (run x pre (S.getD j fall).1))=true ↔
        gateIdx=some j)
    (old : project (fun j=>S.getD j fall) x k=.forward (resolved a b gateIdx k))
    (ack : Fin n)
    (E : Event hp (fun j=>S.getD j fall) len (run x w) ack (.busy (opcode a) (.back 0)) .idle) :
    (snapshot (step (run x w) ack (S.getD 0 fall).1).long =
      ((.empty,1),BitVec.ofNat 9 (if a then if b then acquire else 412 else admit))) ∧
    let site := run x w (S.getD 0 fall).1
    BStarLongCommand.bind (longGeometry B site) 0 (atSite site.long 0)=.reply (packet a b) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  obtain ⟨pre,turn,back,W,out,_,ret⟩ := BStarAcquireAckAncestry.split_turn hp P
  let y := run x pre
  have front := resolved_outward hp C sep a b gateIdx shape out k len rfl rfl lower
    (fun u v V=>scope u (v++turn::back) (by rw [W,V,List.append_assoc])) old
  have skip : gateIdx≠some len := fun G=>Nat.lt_irrefl _ (shape len G).1
  rw [resolved,if_neg skip] at front
  have T : onTerminal hp y turn addr len := by
    obtain ⟨cl,q,M,kind,none,slot,atCl⟩ := BStarStageTerminalHealth.selected_turn
      hp C turn (sep turn) (opcode a) (BStarAcquireHistoryReturn.busy_end hp out) (busy_start hp ret)
    have mem : cl∈orderedCommands (oldPair B y turn) := by
      rw [←actualOffers_claims]
      exact List.mem_map.mpr ⟨(cl,.advance q),M,rfl⟩
    exact ⟨cl,mem,kind,none,slot,atCl⟩
  let f := packet a b
  have terminal := terminal_reply hp C turn (sep turn) a b T front
  obtain ⟨j,J,R⟩ := FreshAttempt.canonical_reply_returns hp C sep ret f
    (packet_finish a b).2 len rfl terminal
  have eq : j=0 := (Cursor.back.inj J).symm
  subst j
  have replay : run x w=run (step y turn) back := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  have cur : Current hp base addr len (run x w) (.busy (opcode a) (.back 0)) :=
    replay.symm ▸ BStarAcquireHistoryReturn.busy_end hp ret
  obtain ⟨head,slot⟩ := root_header hp C cur.1.1
  have O : atSite (run x w root).long 0=.reply f := by
    rw [replay]
    change atSite (run (step y turn) back root).long (addr 0).2=.reply f at R
    rwa [slot] at R
  have bound : BStarLongCommand.bind (longGeometry B (run x w root)) 0
      (atSite (run x w root).long 0)=.reply f := by
    rw [O,BStarReplyBack.normal_eq]
    exact (packet_finish a b).2
  refine ⟨?_,bound⟩
  cases a
  · exact actual_pace_consumes_to_admit hp (base:=base) (x:=run x w) (addr:=addr) (len:=len) (e:=ack) slot head (sep ack)
      cur E f rfl rfl bound
  · have H := BStarAdmissionPaceCore.actual_admit_consumes hp (base:=base) (x:=run x w) (addr:=addr) (len:=len) (e:=ack) slot head (sep ack)
      cur E f rfl rfl bound
    cases b <;> exact H

/-- The actual freshly issued PACE flight from K0 has a matching unit
reply. The consuming mark schedules ISSUE4 on this same tape. -/
theorem pace_from_clean_issue {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door : Fin n) (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=3)
    (L : Launch (x (S.getD 0 fall).1).long (step x door (S.getD 0 fall).1).long)
    {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len 3 (step x door) (.out 0) w (.back 0))
    (ack : Fin n)
    (E : Event hp (fun j=>S.getD j fall) len (run (step x door) w) ack (.busy 3 (.back 0)) .idle) :
    snapshot (step (run (step x door) w) ack (S.getD 0 fall).1).long =
      ((.empty,1),BitVec.ofNat 9 admit) := by
  let adr := fun j=>S.getD j fall
  obtain ⟨_,u,H,launched⟩ := L
  rw [pc] at H
  have U : u=0 := by exact (Option.some.inj (show some 0=some u from H)).symm
  subst u
  have slot := (root_header hp C (busy_start hp P).1.1).2
  have front : project adr (step x door) 0=.forward (packet false false) := by
    change atSite (step x door (adr 0).1).long (adr 0).2=_
    rw [slot]
    have F := congrArg (fun s : (Token×BitVec 2)×BitVec 9=>s.1.1) launched
    change atSite (step x door (adr 0).1).long 0=.forward _ at F
    rw [pc] at F
    exact F
  exact (resolved_consumes hp C sep false false none 0 (by simp) P (by simp)
    (by intro u v W j J; simp [pace_has_no_gate]) front ack E).1

/-- The fixed chart has just one current ADMIT gate at its K1 offset
two. No token history or selected side enters this geometry. -/
theorem admit_gate_scope {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (ready : correct (oldH6 B base) hh 5 x)
    (k : Nat) (K : k≤len) (port : (S.getD k fall).2=1)
    (ord : BStarH6Ordinal.oldOrdinal B base hh (S.getD k fall).1=2)
    (j : Nat) (J : j≤len) :
    gate admit (S.getD j fall).2 (longGeometry B (x (S.getD j fall).1))=true ↔ j=k := by
  let hs := oldH6 B base
  let u := S.getD j fall
  let v := S.getD k fall
  have on : gate admit v.2 (longGeometry B (x v.1))=true :=
    (selected_gate_iff hp hh fixed ready v.1 v.2 false).mpr ⟨congrArg Fin.val port,ord⟩
  refine ⟨?_,fun H=>H.symm ▸ on⟩
  intro G
  obtain ⟨uj,ou⟩ := (selected_gate_iff hp hh fixed ready u.1 u.2 false).mp G
  have u1 : u.2=1 := Fin.ext uj
  have lenS := C.length
  have entry (p : Nat) (P : p≤len) : S.getD p fall∈S := by
    rw [←List.getElem_eq_getD (h:=show p<S.length by omega)]
    exact List.getElem_mem _
  have U := (C.entries u (entry j J)).2
  have V := (C.entries v (entry k K)).2
  rw [u1] at U
  change v.2=1 at port
  rw [port] at V
  have whole : word hs u.1=word hs v.1 := by
    let m : Int := total hs
    let d := BStarLongFiberOwner.cmdDispl 1
    have W := congrArg (fun t=>BStarLongFiberOwner.addressWord m t d) (U.trans V.symm)
    change BStarLongFiberOwner.addressWord m (BStarLongFiberOwner.owner m (word hs u.1) d) d =
      BStarLongFiberOwner.addressWord m (BStarLongFiberOwner.owner m (word hs v.1) d) d at W
    rw [BStarLongFiberOwner.address_inverse,BStarLongFiberOwner.address_inverse] at W
    rw [Int.emod_eq_of_lt (word_range hs u.1 hh).1 (word_range hs u.1 hh).2,
      Int.emod_eq_of_lt (word_range hs v.1 hh).1 (word_range hs v.1 hh).2] at W
    exact W
  have positions := AdmissionOffset.same_ordinal_same_word hs hh u.1 v.1 (ou.trans ord.symm) whole
  exact (List.getD_inj (by omega) (by omega) C.nodup).mp (Prod.ext positions (u1.trans port.symm))

/-- The original ISSUE4 command arrives with race one on the first
real selected link to the unique ADMIT gate. Prior marks can interleave
arbitrarily within its generated outbound tape. -/
theorem admission_from_ready_issue_to_gate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door : Fin n) (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=admit)
    (L : Launch (x (S.getD 0 fall).1).long (step x door (S.getD 0 fall).1).long)
    {w : List (Fin n)} (k : Nat)
    (P : BusyOnly hp base (fun j=>S.getD j fall) len admit (step x door) (.out 0) w (.out k))
    (scope : ∀ u v,w=u++v → ∀ j≤len,
      gate admit (S.getD j fall).2 (longGeometry B (run (step x door) u (S.getD j fall).1))=true ↔
        j=k+1)
    (e : Fin n) (link : linkAt hp (run (step x door) w) e (fun j=>S.getD j fall) len k) :
    project (fun j=>S.getD j fall) (step (run (step x door) w) e) (k+1)=.forward (atGate 1) := by
  let addr := fun j=>S.getD j fall
  let y := run (step x door) w
  obtain ⟨_,u,H,launched⟩ := L
  rw [pc] at H
  have U : u=0 := (Option.some.inj (show some 0=some u from H)).symm
  subst u
  have slot := (root_header hp C (busy_start hp P).1.1).2
  have init : project addr (step x door) 0=.forward (resolved true false none 0) := by
    change atSite (step x door (addr 0).1).long (addr 0).2=_
    rw [slot]
    have F := congrArg (fun s : (Token×BitVec 2)×BitVec 9=>s.1.1) launched
    change atSite (step x door (addr 0).1).long 0=.forward _ at F
    rw [pc] at F
    exact F
  obtain ⟨K,cl,dst,mem,hd,src,tgt⟩ := link
  have before (u v : List (Fin n)) (W : w=u++v) (j : Nat) (J : j≤k) :
      gate admit (addr j).2 (longGeometry B (run (step x door) u (addr j).1))=true ↔
        (none : Option Nat)=some j := by
    rw [scope u v W j (by omega)]
    simp [show j≠k+1 by omega]
  have out := resolved_outward hp C sep true false none (by simp) P 0 k rfl rfl (by simp) before init
  have old : project addr y k=.forward (packet true false) := out
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  have geom (a : AtK) (j : Nat) (E : addr j=address e a) :
      geometry g a.side=longGeometry B (y (addr j).1) := by
    rw [E]
    cases a with
    | mk s k => cases s <;> rfl
  have localScope := scope w [] (List.append_nil _).symm
  have srcOff : gate admit cl.source.occurrence (geometry g cl.source.side)=false := by
    rw [geom _ _ src]
    have eq : cl.source.occurrence=(addr k).2 := congrArg Prod.snd src.symm
    rw [eq]
    exact Bool.eq_false_iff.mpr (fun O=>Nat.ne_of_lt (Nat.lt_succ_self k) ((localScope k (by omega)).mp O))
  have dstOn : gate admit dst.occurrence (geometry g dst.side)=true := by
    rw [geom _ _ tgt]
    have eq : dst.occurrence=(addr (k+1)).2 := congrArg Prod.snd tgt.symm
    rw [eq]
    exact (localScope (k+1) (by omega)).mpr rfl
  have rawOld : readK raw cl.source=.forward (packet true false) :=
    (old_read y e cl.source).trans ((congrArg (atCursor y) src).symm.trans old)
  have Bnd : bound g (readK raw) cl.source=.forward (packet true false) := by
    unfold bound
    rw [rawOld,packet_bound _ _ true false srcOff]
  have arrived := joined_link hp (y e,y (rightNeighbor e)) cl dst (packet true false) true false
    mem hd Bnd (packet_depart _ _ true false srcOff)
  change _ = (if gate admit dst.occurrence (geometry g dst.side) then _ else _) at arrived
  exact (congrArg (atCursor (step y e)) tgt).trans ((new_read B y e (sep e) dst).symm.trans
    (by simpa only [dstOn,if_true] using arrived))

private theorem run_closed (Q : X→Prop) (closed : ∀ x,Q x→∀ e,Q (step x e))
    (x : X) (qx : Q x) (w : List (Fin n)) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact qx
  | cons e w ih => exact ih (step x e) (closed x qx e)

/-- The first actual side chooses the bit. Same-side and exterior
marks between FIRST and the opposite incidence keep the old choice. -/
theorem two_race_marks {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (loc : S.getD k fall=(i,1))
    (ord : BStarH6Ordinal.oldOrdinal B base hh i=2)
    (qx : Q x) (cur : Current hp base (fun j=>S.getD j fall) len x (.busy admit (.out k)))
    (old : project (fun j=>S.getD j fall) x k=.forward (atGate 1))
    (s t : Side) (opposite : t≠s) (first other : Fin n)
    (firstAt : BStarAcquireDoorHistory.siteOf first s=i)
    (otherAt : BStarAcquireDoorHistory.siteOf other t=i)
    (middle : List (Fin n))
    (avoid : ∀ e∈middle, ∀ u, BStarAcquireDoorHistory.siteOf e u=i → u=s) :
    let y := step (run (step x first) middle) other
    Current hp base (fun j=>S.getD j fall) len y (.busy admit (.out k)) ∧
      project (fun j=>S.getD j fall) y k=.forward (settledGate (s==.left)) := by
  dsimp only
  have gateAt (y : X) (qy : Q y) : gate admit 1 (longGeometry B (y i))=true :=
    (selected_gate_iff hp hh (fun j=>(congrArg Prod.fst (fiber y qy j)).symm)
      (ready y qy) i 1 false).mpr ⟨rfl,ord⟩
  have oldRaw : atSite (x i).long 1=.forward (atGate 1) := by
    change atSite (x (S.getD k fall).1).long (S.getD k fall).2=_ at old
    rwa [loc] at old
  have binder : BStarLongCommand.bind (longGeometry B (x i)) 1 (atSite (x i).long 1)=.forward (atGate 1) := by
    rw [oldRaw]
    exact gate_packet_bound _ _ (gateAt x qx) (by decide)
  have Qfirst := closed x qx first
  obtain ⟨rawFirst,_,curFirst,boundFirst⟩ := BStarGateStutter.observed_race_step
    hp C Q fiber closed sep i first false k qx loc cur (atGate 1) binder rfl rfl
    (ready x qx) (ready _ Qfirst) (gateAt x qx) s firstAt (firstCode s) (.inl ⟨rfl,rfl⟩)
  let z := run (step x first) middle
  have qz : Q z := run_closed hp Q closed _ Qfirst middle
  have held := BStarGateStutter.first_wait_word hp C Q fiber closed ready sep i false k loc ord
    (atGate (firstCode s)) rfl rfl s rfl middle (step x first) Qfirst curFirst boundFirst rawFirst avoid
  obtain ⟨rawEnd,_,curEnd,_⟩ := BStarGateStutter.observed_race_step
    hp C Q fiber closed sep i other false k qz loc held.1 (atGate (firstCode s))
    held.2.1 rfl rfl (ready z qz) (ready _ (closed z qz other)) (gateAt z qz)
    t otherAt (finalCode s) (.inr ⟨s,Ne.symm opposite,rfl,rfl⟩)
  refine ⟨curEnd,?_⟩
  change atSite (step z other (S.getD k fall).1).long (S.getD k fall).2=_
  rw [loc]
  unfold atSite
  rw [rawEnd,decode_encode]
  cases s <;> rfl

/-- Issue4, the first gate arrival, both observed incidences, and the
literal returning consume are all on the specified raw tape. The
right-first branch ends this tape at the source ready to issue DUMMY. -/
theorem admission_from_ready_issue {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (qx : Q x)
    (door : Fin n) (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=admit)
    (L : Launch (x (S.getD 0 fall).1).long (step x door (S.getD 0 fall).1).long)
    (i : Fin n) (k : Nat) (K : k+1<len)
    (loc : S.getD (k+1) fall=(i,1)) (ord : BStarH6Ordinal.oldOrdinal B base hh i=2)
    (before : List (Fin n))
    (P : BusyOnly hp base (fun j=>S.getD j fall) len admit (step x door) (.out 0) before (.out k))
    (enter : Fin n) (hit : linkAt hp (run (step x door) before) enter (fun j=>S.getD j fall) len k)
    (s t : Side) (opposite : t≠s)
    (first other : Fin n) (firstAt : BStarAcquireDoorHistory.siteOf first s=i)
    (otherAt : BStarAcquireDoorHistory.siteOf other t=i)
    (middle : List (Fin n))
    (avoid : ∀ e∈middle, ∀ u, BStarAcquireDoorHistory.siteOf e u=i → u=s) :
    let arrived := step (run (step x door) before) enter
    let settled := step (run (step arrived first) middle) other
    ∀ (after : List (Fin n)) (ack : Fin n),
      BusyOnly hp base (fun j=>S.getD j fall) len admit settled (.out (k+1)) after (.back 0) →
      Event hp (fun j=>S.getD j fall) len (run settled after) ack (.busy admit (.back 0)) .idle →
      (snapshot (step (run settled after) ack (S.getD 0 fall).1).long =
        ((.empty,1),BitVec.ofNat 9 (if s==.left then acquire else 412))) ∧
      let site := run settled after (S.getD 0 fall).1
      BStarLongCommand.bind (longGeometry B site) 0 (atSite site.long 0)=.reply (packet true (s==.left)) := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let y := run (step x door) before
  let z := step y enter
  let u := step (run (step z first) middle) other
  have qStarted := closed x qx door
  have qy : Q y := run_closed hp Q closed _ qStarted before
  have qz : Q z := closed y qy enter
  have qu : Q u := closed _ (run_closed hp Q closed _ (closed z qz first) middle) other
  have gateAt (state : X) (qs : Q state) (j : Nat) (J : j≤len) :
      gate admit (addr j).2 (longGeometry B (state (addr j).1))=true ↔ j=k+1 := by
    apply admit_gate_scope hp C
      (fun i=>(congrArg Prod.fst (fiber state qs i)).symm) (ready state qs)
      (k+1) (by omega) (congrArg Prod.snd loc) _ j J
    rw [loc]
    exact ord
  have arrival : project addr z (k+1)=.forward (atGate 1) :=
    admission_from_ready_issue_to_gate hp C sep door pc L k P
      (fun a b _ j h=>gateAt _ (run_closed hp Q closed _ qStarted a) j h) enter hit
  have atY := BStarAcquireHistoryReturn.busy_end hp P
  obtain ⟨d,ev,cur⟩ := current_step hp C Q fiber closed sep qy enter (.busy admit (.out k)) atY
  have curGate : Current hp base addr len z (.busy admit (.out (k+1))) := by
    cases ev with
    | transit _ _ dest _ _ =>
      cases dest with
      | back j =>
        exact (BStarOwnerControlHistory.pointed_backward_no_forward _ _ _ cur.2.1 (k+1)
          (by omega) ⟨_,arrival⟩).elim
      | out j =>
        have eq := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ cur.2.1 cur.2.2
          (k+1) (by omega)).mp ⟨_,arrival⟩
        subst j
        exact cur
  obtain ⟨_,F⟩ := two_race_marks hp C Q fiber closed ready sep i (k+1) loc ord
    qz curGate arrival s t opposite first other firstAt otherAt middle avoid
  intro after ack busy event
  have shape (j : Nat) (J : some (k+1)=some j) :
      j<len ∧ true=true ∧ (addr j).2=1 := by
    cases J
    exact ⟨K,rfl,congrArg Prod.snd loc⟩
  have scope (pre rest : List (Fin n)) (_ : after=pre++rest) (j : Nat) (J : j≤len) :
      gate (opcode true) (addr j).2 (longGeometry B (run u pre (addr j).1))=true ↔ some (k+1)=some j := by
    rw [show opcode true=admit from rfl,gateAt _ (run_closed hp Q closed _ qu pre) j J,Option.some.injEq]
    exact eq_comm
  have front : project addr u (k+1)=.forward (resolved true (s==.left) (some (k+1)) (k+1)) := by
    rw [resolved,if_pos rfl]
    exact F
  exact resolved_consumes hp C sep true (s==.left) (some (k+1)) (k+1) shape busy
    (fun j J=>(Option.some.inj J) ▸ Nat.le_refl (k+1)) scope front ack event

/-- Consume denials remain binding after arbitrary later generated
cycles. The premise is tested on the old bound reply of each raw
mark, so a fresh rival cannot return to ACQUIRE after its release. -/
theorem denied_rival_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m d : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x m w d)
    (frame : ∀ a j,Layout B base j=Layout B (run x a) j)
    (init : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat≠acquire)
    (denied : ∀ a e b,w=a++e::b → ∀ f,
      let u := run x a (S.getD 0 fall).1
      BStarLongCommand.bind (longGeometry B u) 0 (atSite u.long 0)=.reply f →
      f.fault=0 → f.opcode.toNat=admit → f.argument.toNat%2≠1) :
    (ctrlOp.read (run x w (S.getD 0 fall).1).long).toNat≠acquire := by
  induction G with
  | endpoint _ => exact init
  | @next raw a e w b dest cur ev tail ih =>
    apply ih
    · exact fun pre j=>frame (e::pre) j
    · have post : Current hp base (fun j=>S.getD j fall) len (step raw e) b := by
        cases tail <;> assumption
      exact FreshAttempt.denied_source_step hp C sep (frame []) e cur ev post init
        (fun f _ _ F H O=>denied [] e w rfl f F H O)
    · intro a f b W
      exact denied (e::a) f b (congrArg (List.cons e) W)

private theorem split_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} (pre post : List (Fin n))
    (P : BusyOnly hp base addr len op x z (pre++post) d) :
    ∃ mid, BusyOnly hp base addr len op x z pre mid ∧
      BusyOnly hp base addr len op (run x pre) mid post d := by
  induction pre generalizing x z with
  | nil => exact ⟨z,.nil (busy_start hp P),P⟩
  | cons e pre ih =>
    cases P with
    | cons I E tail =>
      obtain ⟨mid,L,R⟩ := ih tail
      exact ⟨mid,.cons I E L,R⟩

private theorem front_points_to {base x : X} {addr : Nat→Pos n} {len op j : Nat}
    {d : Cursor} (cur : Current hp base addr len x (.busy op d))
    (J : j≤len) (p : Payload) (F : project addr x j=.forward p) :
    d=.out j := by
  cases d with
  | out k =>
    have eq := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ cur.2.1 cur.2.2 j J).mp ⟨p,F⟩
    exact congrArg Cursor.out eq.symm
  | back k =>
    exact (BStarOwnerControlHistory.pointed_backward_no_forward _ _ _ cur.2.1 j J ⟨p,F⟩).elim

private theorem earliest {α : Type} (P : α→Prop) (w : List α) :
    (∀ e∈w,¬P e) ∨ ∃ pre e post,w=pre++e::post ∧ (∀ f∈pre,¬P f) ∧ P e := by
  classical
  induction w with
  | nil => exact .inl (by simp)
  | cons e w ih =>
    by_cases hit : P e
    · exact .inr ⟨[],e,w,rfl,by simp,hit⟩
    · rcases ih with misses|⟨pre,f,post,eq,skip,found⟩
      · exact .inl (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hit misses)
      · exact .inr ⟨e::pre,f,post,congrArg (List.cons e) eq,
          by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hit skip,found⟩

private theorem unchanged_site (x : X) (i : Fin n) (w : List (Fin n))
    (skip : ∀ e∈w,∀ s, BStarAcquireDoorHistory.siteOf e s≠i) :
    run x w i=x i := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have left : i≠e := Ne.symm (skip e List.mem_cons_self .left)
    have right : i≠rightNeighbor e := Ne.symm (skip e List.mem_cons_self .right)
    have frame : step x e i=x i := by simp only [AllSizeS1Geometry.step,if_neg left,if_neg right]
    exact (ih (step x e) (fun a M=>skip a (List.mem_cons_of_mem _ M))).trans frame

/-- A generated tape which returns after arriving at a fresh gate
contains the first incident mark and the next opposite incident mark.
The suffix starts with a completed race on that same chart and tape. -/
theorem gate_observations_for_return {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (qx : Q x)
    (i : Fin n) (k : Nat) (K : k≤len) (loc : S.getD k fall=(i,1))
    (ord : BStarH6Ordinal.oldOrdinal B base hh i=2)
    {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len admit x (.out k) w (.back 0))
    (initial : project (fun j=>S.getD j fall) x k=.forward (atGate 1)) :
    ∃ (pre middle after : List (Fin n)) (first other : Fin n) (s t : Side),
      w=pre++first::(middle++other::after) ∧
      (∀ e∈pre,∀ u,BStarAcquireDoorHistory.siteOf e u≠i) ∧
      BStarAcquireDoorHistory.siteOf first s=i ∧
      t≠s ∧ BStarAcquireDoorHistory.siteOf other t=i ∧
      (∀ e∈middle,∀ u,BStarAcquireDoorHistory.siteOf e u=i → u=s) ∧
      let z := step (run (step (run x pre) first) middle) other
      BusyOnly hp base (fun j=>S.getD j fall) len admit z (.out k) after (.back 0) ∧
        project (fun j=>S.getD j fall) z k=.forward (settledGate (s==.left)) := by
  let addr := fun j=>S.getD j fall
  have loc' : addr k=(i,1) := loc
  have untouched (p : List (Fin n)) (avoid : ∀ e∈p,∀ s,BStarAcquireDoorHistory.siteOf e s≠i) :
      project addr (run x p) k=.forward (atGate 1) := by
    change atSite (run x p (addr k).1).long (addr k).2=_
    rw [loc',unchanged_site hp x i p avoid]
    change atSite (x (addr k).1).long (addr k).2=_ at initial
    rwa [loc'] at initial
  have gateAt (y : X) (qy : Q y) : gate admit 1 (longGeometry B (y i))=true :=
    (selected_gate_iff hp hh (fun j=>(congrArg Prod.fst (fiber y qy j)).symm)
      (ready y qy) i 1 false).mpr ⟨rfl,ord⟩
  rcases earliest (fun e=>∃ s,BStarAcquireDoorHistory.siteOf e s=i) w with none|⟨pre,e,rest,W,skip,s,atS⟩
  · have avoid : ∀ e∈w,∀ s,BStarAcquireDoorHistory.siteOf e s≠i :=
      fun e H s D=>none e H ⟨s,D⟩
    have impossible := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp P) K _ (untouched w avoid)
    cases impossible
  have noHit : ∀ e∈pre,∀ s,BStarAcquireDoorHistory.siteOf e s≠i :=
    fun e H s D=>skip e H ⟨s,D⟩
  let y := run x pre
  have qy : Q y := run_closed hp Q closed x qx pre
  have atY := untouched pre noHit
  obtain ⟨mid,lead,restBusy⟩ := split_busy hp pre (e::rest) (W ▸ P)
  have atPoint := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp lead) K _ atY
  subst mid
  have cur : Current hp base addr len y (.busy admit (.out k)) := busy_start hp restBusy
  have bindY : BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward (atGate 1) := by
    change atSite (y (addr k).1).long (addr k).2=_ at atY
    rw [loc'] at atY
    rw [atY]
    exact gate_packet_bound _ _ (gateAt y qy) (by decide)
  have qe := closed y qy e
  obtain ⟨rawFirst,_,afterFirst,boundFirst⟩ := BStarGateStutter.observed_race_step
    hp C Q fiber closed sep i e false k qy loc cur (atGate 1) bindY rfl rfl
    (ready y qy) (ready _ qe) (gateAt y qy) s atS (firstCode s) (.inl ⟨rfl,rfl⟩)
  have firstToken : project addr (step y e) k=.forward (atGate (firstCode s)) := by
    change atSite (step y e (addr k).1).long (addr k).2=_
    rw [loc']
    unfold atSite
    rw [rawFirst,decode_encode]
    rfl
  cases restBusy with
  | @cons _ _ next _ _ _ _ _ restBusy =>
    have nextAt := front_points_to hp (busy_start hp restBusy) K _ firstToken
    subst next
    have wait (p : List (Fin n))
        (avoid : ∀ e∈p,∀ t,BStarAcquireDoorHistory.siteOf e t=i → t=s) :=
      BStarGateStutter.first_wait_word hp C Q fiber closed ready sep i false k loc ord
        (atGate (firstCode s)) rfl rfl s rfl p (step y e) qe afterFirst boundFirst rawFirst avoid
    have heldToken (p : List (Fin n)) (avoid : ∀ f∈p,∀ t,BStarAcquireDoorHistory.siteOf f t=i → t=s) :
        project addr (run (step y e) p) k=.forward (atGate (firstCode s)) := by
      change atSite (run (step y e) p (addr k).1).long (addr k).2=_
      rw [loc']
      unfold atSite
      rw [(wait p avoid).2.2,decode_encode]
    rcases earliest (fun f=>∃ t,t≠s ∧ BStarAcquireDoorHistory.siteOf f t=i) rest with
      none|⟨middle,f,after,V,quiet,t,opp,atT⟩
    · have avoid (b : Fin n) (H : b∈rest) (t : Side) (atT : BStarAcquireDoorHistory.siteOf b t=i) :
          t=s := Classical.byContradiction (fun N=>none b H ⟨t,N,atT⟩)
      have impossible := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp restBusy) K _ (heldToken rest avoid)
      cases impossible
    have avoid (b : Fin n) (H : b∈middle) (t : Side) (atT : BStarAcquireDoorHistory.siteOf b t=i) :
        t=s := Classical.byContradiction (fun N=>quiet b H ⟨t,N,atT⟩)
    have accepted := two_race_marks hp C Q fiber closed ready sep i k loc ord qy cur atY
      s t opp e f atS atT middle avoid
    obtain ⟨mid,lead,rem⟩ := split_busy hp middle (f::after) (V ▸ restBusy)
    have ptr := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp lead) K _ (heldToken middle avoid)
    subst mid
    cases rem with
    | @cons _ _ next _ _ _ _ _ afterBusy =>
      have pt := front_points_to hp (busy_start hp afterBusy) K _ accepted.2
      subst next
      exact ⟨pre,middle,after,e,f,s,t,by rw [W,V],noHit,atS,opp,atT,avoid,afterBusy,accepted.2⟩

end L4.Height.AdmissionTour
