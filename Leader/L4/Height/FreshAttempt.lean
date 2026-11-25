import Leader.L4.BStarAcquireHistoryReturn
import Leader.L4.BStarAdmissionPaceCore
import Leader.L4.BStarResetEndpointZero
import Leader.L4.BStarOwnedGrantLife
import Leader.L4.BStarReplyBack

namespace L4.Height.FreshAttempt
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongFixedRouting BStarAcquireRailCoverage BStarResetMarkAdapter BStarOwnerControlHistory
open BStarLongCommand BStarLongCommandData BStarLongGrant BStarAcquireLatch
open BStarLongDoor BStarLiteralPC BStarResetControllerProgress BStarArithmeticControllerReturn
open BStarSeparatingRail BStarSeparatorControl BStarResetSchedule

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem endpoint_owner_shift {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (o : Owners h) (k j : Fin 11) :
    commandOwner h (endpoint h hh o k).1 j =
      (o.val+BStarLongFiberOwner.cmdDispl k-BStarLongFiberOwner.cmdDispl j)%(total h : Int) := by
  let m : Int := total h
  let i := (endpoint h hh o k).1
  let d := BStarLongFiberOwner.cmdDispl
  have own : BStarLongFiberOwner.owner m (word h i) (d k)=o.val :=
    (endpoint_spec h hh o k).2.1
  have E := (BStarLongFiberOwner.address_inverse m (word h i) (d k)).symm
  rw [own] at E
  have fix : word h i % m=word h i := by
    unfold word m
    exact Int.emod_emod _ _
  rw [fix] at E
  change (word h i-d j)%m=(o.val+d k-d j)%m
  rw [E]
  unfold BStarLongFiberOwner.addressWord
  rw [Int.sub_emod,Int.emod_emod,←Int.sub_emod]

/-- The four grant incidences that can obstruct the target ACQUIRE are
owned by the two cyclic neighbors of the target owner. -/
theorem conflicting_port_owners {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (o : Owners h) :
    let u := (endpoint h hh o 0).1
    let v := (endpoint h hh o 1).1
    let z := (endpoint h hh o 2).1
    let m : Int := total h
    commandOwner h u 1=(o.val-1)%m ∧ commandOwner h v 2=(o.val-1)%m ∧
      commandOwner h v 0=(o.val+1)%m ∧ commandOwner h z 1=(o.val+1)%m := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simpa [BStarLongFiberOwner.cmdDispl] using endpoint_owner_shift h hh o 0 1
  · rw [endpoint_owner_shift h hh o 1 2]
    change (o.val+1-2)%(total h : Int)=(o.val-1)%(total h : Int)
    congr 1
    omega
  · simpa [BStarLongFiberOwner.cmdDispl] using endpoint_owner_shift h hh o 1 0
  · rw [endpoint_owner_shift h hh o 2 1]
    change (o.val+2-1)%(total h : Int)=(o.val+1)%(total h : Int)
    congr 1
    omega

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- A transition to ACQUIRE consumes a left-first ADMIT. Other source
replies, including a right-first ADMIT and arithmetic replies, cannot
enter that opcode. -/
theorem acquire_requires_admit (old : BitVec LW) (f : Payload)
    (valid : LongDoorGuard.valid manifest old=true) (A : pcNext old f=acquire) :
    (ctrlOp.read old).toNat=admit ∧ f.fault=0 ∧ f.opcode.toNat=admit ∧
      f.argument.toNat%2=1 := by
  have next := A
  let op := (ctrlOp.read old).toNat
  have range : op<413 := of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2
  change (if f.fault != 0 || f.opcode.toNat != op then 0
    else if (arithKind op).isSome then successor old op else nextOrdinary old op f)=acquire at A
  by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
  · rw [if_pos bad] at A
    contradiction
  rw [if_neg bad] at A
  have clean := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bad)
  have fg : f.fault=0 := by simpa using clean.1
  have fe : f.opcode.toNat=op := by simpa using clean.2
  by_cases ar : (arithKind op).isSome=true
  · rw [if_pos ar] at A
    have P := arithmetic_range op ar
    rcases successor_order old op P.2 with E|E
    · rw [E] at A
      contradiction
    · unfold acquire at A
      omega
  rw [if_neg ar] at A
  have small : op<5 := by
    rcases ordinary_progress old op f range with E|E
    · rw [E] at A
      contradiction
    · unfold acquire at A
      omega
  have options : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 := by omega
  have P : op=admit := by
    rcases options with E|E|E|E|E <;> simp [E,nextOrdinary,admit,acquire] at A ⊢
  refine ⟨P,fg,fe.trans P,?_⟩
  have exactPC := BStarAdmissionPaceCore.admit_successor old f P fg (fe.trans P)
  by_cases parity : f.argument.toNat%2=1
  · exact parity
  · rw [if_neg parity,next] at exactPC
    exact ((by decide : acquire≠412) exactPC).elim

/-- Across every generated event a rival whose old source is outside
ACQUIRE stays outside ACQUIRE if a consuming mark cannot accept a
positive ADMIT reply. The guard is on the bound reply at the old source. -/
theorem denied_source_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n)
    {m d : Mode}
    (cur : Current hp base (fun j=>S.getD j fall) len x m)
    (ev : Event hp (fun j=>S.getD j fall) len x e m d)
    (after : Current hp base (fun j=>S.getD j fall) len (step x e) d)
    (old : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat≠acquire)
    (denied : ∀ f, m=.busy admit (.back 0) → d=.idle →
      let u := x (S.getD 0 fall).1
      bind (longGeometry B u) 0 (atSite u.long 0)=.reply f →
      f.fault=0 → f.opcode.toNat=admit →
      f.argument.toNat%2≠1) :
    (ctrlOp.read (step x e (S.getD 0 fall).1).long).toNat≠acquire := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  have idle (I : Current hp base addr len x .idle) :
      (ctrlOp.read (step x e root).long).toNat≠acquire := by
    rcases idle_launch_or_hold hp C same I.2 sep e I.1 with A|A|A
    · have pc := congrArg (fun c : BitVec 2×BitVec 9=>c.2.toNat) A.2.2.1
      exact pc.symm ▸ old
    · have pc := congrArg (fun c : (Token×BitVec 2)×BitVec 9=>c.2.toNat) A.2.2.1
      exact pc.symm ▸ (by decide : 0≠acquire)
    · obtain ⟨_,_,snap⟩ := A.2.1.2
      have pc := congrArg (fun c : (Token×BitVec 2)×BitVec 9=>c.2.toNat) snap
      exact pc.symm ▸ old
  cases ev with
  | idle_hold => exact idle cur
  | bad_issue => exact idle cur
  | launch => exact idle cur
  | transit => exact after.1.2.2.2.symm ▸ cur.1.2.2.2 ▸ old
  | arrived_hold => exact after.1.2.2.2.symm ▸ cur.1.2.2.2 ▸ old
  | consume op own cleared =>
    obtain ⟨head,slot⟩ := BStarResetChartService.root_header hp C same
    have event : Event hp addr len x e (.busy op (.back 0)) .idle :=
      .consume op own cleared
    obtain ⟨f,F,new⟩ :=
      BStarGeneratedPCAncestry.consume_pc hp (base:=base) (x:=x) (addr:=addr)
        (len:=len) (op:=op) (e:=e) slot head (sep e) cur event
    intro next
    obtain ⟨A,healthy,matched,parity⟩ := acquire_requires_admit _ f cur.1.2.1 (new.symm.trans next)
    have pc : op=admit := cur.1.2.2.2.symm.trans A
    subst op
    exact denied f rfl rfl F healthy matched parity

/-- An ACQUIRE front at an owned grant incidence belongs to the current
generated tour on that chart. This also applies to the rival ports. -/
theorem owned_no_acquire {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j=>S.getD j fall) len (run x w) m)
    (i : Fin n) (port : Fin 3)
    (own : commandOwner (oldH6 B base) i (BStarResetNoAcquire.slot port)=o.val)
    (off : ∀ z, m≠.busy acquire z) :
    BStarResetNoAcquire.NoAcquireAt (run x w) i port := by
  intro q old healthy
  let k : Fin 11 := BStarResetNoAcquire.slot port
  have acts : active (longGeometry B (base i)) k=true := by
    have h := port.isLt
    simp [active,k,show port.val≠8 by omega,show port.val≠9 by omega]
  obtain ⟨j,hj,J⟩ := List.getElem_of_mem (C.cover (i,k) acts own)
  have idx : S.getD j fall=(i,k) := (List.getElem_eq_getD _).symm.trans J
  have size := C.length
  have pos : j≤len := by omega
  have atJ : project (fun a=>S.getD a fall) (run x w) j=.forward q :=
    (congrArg (atCursor (run x w)) idx).trans old
  exact off _ (healthy_forward_origin hp C sep G now j pos q atJ acquire healthy.1 healthy.2).1

/-- An empty old grant alone does not rule out a concurrent writer.
An absent healthy ACQUIRE front rules out its selected request. -/
theorem no_request_at (x : X) (e : Fin n) (s : Side) (port : Fin 3)
    (N : BStarResetNoAcquire.NoAcquireAt x (site e s) port) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    requested (round g raw).offered s port acquire=false := by
  dsimp only
  apply Bool.eq_false_iff.mpr
  intro req
  obtain ⟨C,_,q,_,side,occ,_,_,old,healthy⟩ :=
    BStarReleaseOrigin.pre_grant_acquire_origin _ _ s port req
  have addr : address e C.source=(site e s,BStarResetNoAcquire.slot port) :=
    Prod.ext (congrArg (site e) side) (Fin.ext occ)
  have rd : oldTokens ((x e).long,(x (rightNeighbor e)).long) C.source =
      atCursor x (address e C.source) := by
    obtain ⟨u,j⟩ := C.source
    cases u <;> rfl
  exact N q ((congrArg (atCursor x) addr).symm.trans (rd.symm.trans old)) healthy

/-- A released physical grant stays zero on any suffix whose old owner
mode rules out ACQUIRE. Other charts can advance on the same tape. -/
theorem owned_zero_without_acquire {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w : List (Fin n)) (i : Fin n) (port : Fin 3)
    (own : commandOwner (oldH6 B base) i (BStarResetNoAcquire.slot port)=o.val)
    (zero : BStarGrantBirth.bit (run x lead) i port=0)
    (off : ∀ a e b, w=a++e::b →
      ∃ m, GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (lead++a) m ∧
        Current hp base (fun j=>S.getD j fall) len (run x (lead++a)) m ∧
        ∀ z,m≠.busy acquire z) :
    BStarGrantBirth.bit (run x (lead++w)) i port=0 := by
  rw [BStarResetSchedule.run_append]
  apply BStarGrantBirth.zero_along hp sep _ i port w zero
  intro a e b W
  obtain ⟨m,G,cur,no⟩ := off a e b W
  have absent := owned_no_acquire hp C sep G cur i port own no
  rw [BStarResetSchedule.run_append] at absent
  exact BStarResetNoAcquire.no_win_at hp _ e i port absent

/-- The two reader visits need an empty old writer port, their own empty
port, and absence of a concurrent writer request. The other reader is
free to request or to hold its grant. The writer visit instead requires
all three old ports to be empty. -/
theorem acquire_wins (old rel ask : Ports) (j : Fin 3)
    (self : old j=false) (writer : old 1=false)
    (askJ : ask j=true) (relJ : rel j=false)
    (others : if j=1 then old 0=false ∧ old 2=false else ask 1=false) :
    win old rel ask j=true := by
  by_cases J : j=1
  · subst j
    have O : old 0=false ∧ old 2=false := by simpa using others
    simp [win,canonical,writer,O.1,O.2,askJ,relJ]
  · have A : ask 1=false := by simpa [J] using others
    simp [win,canonical,J,self,writer,askJ,relJ,A]

/-- The literal selected healthy ACQUIRE offer creates a grant under the
old-port conditions. No arrival or subsequent reply is used here. -/
theorem selected_acquire_wins (x : X) (e : Fin n) (C : CommandClaim)
    (q : Payload) (j : Fin 3) (port : C.source.occurrence.val=j.val)
    (F : q.fault=0) (A : q.opcode.toNat=acquire) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let s := C.source.side
    let o := (round g raw).offered
    let old := original (BStarLongGrant.atOld raw s)
    let ask := fun k=>requested o s k acquire
    (C,.advance q)∈o →
    (geometry g s).axes.h6=true →
    old j=false → old 1=false → requested o s j releaseOp=false →
    (if j=1 then old 0=false ∧ old 2=false else ask 1=false) →
    BStarGrantBirth.WonAt hp x e (site e s) j := by
  dsimp only
  intro member header self writer released others
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let o := (round g raw).offered
  have request : requested o C.source.side j acquire=true := by
    apply List.any_eq_true.mpr
    exact ⟨(C,.advance q),member,by simp [port,F,A]⟩
  exact ⟨C.source.side,rfl,header,acquire_wins _ _ _ j self writer request released others,
    C,q,member,rfl,port,F,A⟩

private theorem seen_advance {len : Nat} {x : X} {e : Fin n} {addr : Nat → Pos n}
    {z d : Cursor} (H : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases H with
  | cons _ _ A _ rest => cases rest; exact A

/-- An already canonical terminal reply survives the actual return
through every generated raw mark. PACE, ADMIT and FENCE can use this
direction without first assuming a source ACK. -/
theorem canonical_reply_returns {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len op x z w d)
    (p : Payload) (fixed : BStarReplyBack.normal p=.reply p) :
    ∀ k, z=.back k → project (fun j=>S.getD j fall) x k=.reply p →
      ∃ j, d=.back j ∧ project (fun j=>S.getD j fall) (run x w) j=.reply p := by
  induction P with
  | nil _ => exact fun k E D=>⟨k,E,D⟩
  | @cons raw z d final e w I E tail ih =>
    intro k Z D
    subst z
    let addr := fun j=>S.getD j fall
    have good := I.2.1
    have uniq (l j : Nat) (J : Good anyTag len (project addr (step raw e)) (.back l))
        (Lj : j≤len) (atJ : project addr (step raw e) j=.reply p) : l=j := by
      rcases Nat.lt_trichotomy l j with H|H|H
      · exact Token.noConfusion (atJ.symm.trans (J.2.2.2 j H Lj))
      · exact H
      · exact Token.noConfusion (atJ.symm.trans (J.2.2.1 j H))
    cases k with
    | zero =>
      cases E with
      | arrived_hold _ away =>
        have next := BStarReplyBack.arrived_payload hp C I.1.1 e (sep e) away p
          ⟨good.2.1,good.2.2.2⟩ D
        rw [fixed] at next
        exact ih 0 rfl (next.elim id id)
      | transit _ _ _ nz _ => exact (nz rfl).elim
    | succ k =>
      have A : Advance len (.back (k+1)) d := by
        cases E with
        | transit _ _ _ _ H => exact seen_advance hp H
      have post := (busy_start hp tail).2.1
      have next := BStarReplyBack.reverse_or_hold hp C e (sep e) op k I.1 p good D
      dsimp only at next
      split at next
      · have landed := next.1.trans fixed
        have idx : d=.back k := by
          cases A
          · have H := uniq (k+1) k post (by have := good.1; omega) landed
            omega
          · rfl
        exact ih k idx landed
      · rw [fixed] at next
        have stayed := next.elim id id
        have idx : d=.back (k+1) := by
          cases A
          · rfl
          · have H := uniq k (k+1) post good.1 stayed
            omega
        exact ih (k+1) idx stayed

def admitReply (grant : Bool) : Payload :=
  ⟨0,4,0,0,BitVec.ofNat 34 grant.toNat⟩

theorem admit_terminal (grant : Bool) :
    finish (admitReply grant)=.reply (admitReply grant) ∧
      BStarReplyBack.normal (admitReply grant)=.reply (admitReply grant) := by
  cases grant <;> decide

/-- The completed first-side race carries its decision as the outgoing
bit before any terminal mark or source consume. -/
theorem admit_gate_departure (g : LongGeometry) (j : Fin 11)
    (gateHere : gate admit j g=true) (grant : Bool) :
    depart g j ⟨0,4,BitVec.ofNat 3 (4+grant.toNat),0,0⟩=some (admitReply grant) := by
  have op : (4 : BitVec 9).toNat=admit := by decide
  simp only [depart,op,gateHere,Bool.and_true,beq_self_eq_true,if_true] <;>
    cases grant <;> decide

/-- From a literal terminal ADMIT answer on the same generated tape,
the source schedules ACQUIRE or DUMMY according to that exact bit. -/
theorem consume_admit_terminal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} (P : BusyOnly hp base (fun j=>S.getD j fall) len admit x (.back len) w (.back 0))
    (grant : Bool) (atEnd : project (fun j=>S.getD j fall) x len=.reply (admitReply grant))
    (door : Fin n)
    (E : Event hp (fun j=>S.getD j fall) len (run x w) door (.busy admit (.back 0)) .idle) :
    BStarResetControllerEntry.snapshot (step (run x w) door (S.getD 0 fall).1).long =
      ((.empty,1),BitVec.ofNat 9 (if grant then acquire else 412)) := by
  let f := admitReply grant
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let y := run x w
  have V := (admit_terminal grant).2
  obtain ⟨k,K,R⟩ := canonical_reply_returns hp C sep P f V len rfl atEnd
  have eq : k=0 := (Cursor.back.inj K).symm
  subst k
  have current := BStarAcquireHistoryReturn.busy_end hp P
  obtain ⟨head,slot⟩ := BStarResetChartService.root_header hp C current.1.1
  have old : atSite (y root).long 0=.reply f := by
    change atSite (y root).long (addr 0).2=.reply f at R
    rwa [slot] at R
  have bound : bind (longGeometry B (y root)) 0 (atSite (y root).long 0)=.reply f := by
    rw [old,BStarReplyBack.normal_eq]
    exact V
  have H := BStarAdmissionPaceCore.actual_admit_consumes hp
    (base:=base) (x:=y) (addr:=addr) (len:=len) (e:=door)
    slot head (sep door) current E f (by rfl) (by rfl) bound
  have parity : f.argument.toNat%2=1 ↔ grant=true := by cases grant <;> decide
  simpa only [parity] using H

private theorem fold_outcome (vs : List Visit) (p : Payload) :
    (vs.foldl (fun x v=>v.apply x) p).outcome=p.outcome := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    rw [List.foldl_cons,ih]
    cases H : v.wins <;> simp [Visit.apply,captureFields,H]

/-- Carry a completed actual all-win ACQUIRE itinerary through the
unchanged terminal receipt and consume it at the source. -/
theorem successful_acquire_receipt {base x y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {ps : List (Pos n)} {vs : List Visit}
    (trace : BStarAcquireForwardTrace.Trace hp base x (S.getD 0 fall) w y (S.getD len fall) ps vs)
    (init : atCursor x (S.getD 0 fall)=.forward BStarAcquireSource.initPayload)
    (wins : vs.all Visit.wins=true)
    (turn : Fin n) (C : CommandClaim) (hc : C∈orderedCommands (oldPair B y turn))
    (ht : C.kind=.terminal) (hd : C.destination=none) (hk : C.source.occurrence.val=10)
    (atC : S.getD len fall=(site turn C.source.side,C.source.occurrence))
    (ret : List (Fin n))
    (P : BusyOnly hp base (fun j=>S.getD j fall) len acquire
      (step y turn) (.back len) ret (.back 0))
    (door : Fin n)
    (E : Event hp (fun j=>S.getD j fall) len (run (step y turn) ret) door
       (.busy acquire (.back 0)) .idle) :
    BStarResetControllerEntry.snapshot (step (run (step y turn) ret) door (S.getD 0 fall).1).long =
      ((.empty,1),BitVec.ofNat 9 6) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let z := run (step y turn) ret
  obtain ⟨f,tag,finished,V,_⟩ :=
    completes_at hp trace init turn (sep turn) C hc ht hd hk atC
  have H := finish_itinerary vs BStarAcquireSource.initPayload (by rfl) (by rfl)
  dsimp only at H finished
  have starts : latch BStarAcquireSource.initPayload=true := by decide
  rw [starts,wins] at H
  simp only [Bool.and_true] at H
  have F := congrArg Payload.outcome (Token.reply.inj (finished.symm.trans H))
  change f.outcome=(vs.foldl (fun q v=>v.apply q) BStarAcquireSource.initPayload).outcome at F
  rw [fold_outcome] at F
  have good : f.outcome=0 := F
  have tag' : project addr (step y turn) len=.reply f := tag
  obtain ⟨k,K,R⟩ := BStarAcquireHistoryReturn.busy_return_payload hp chart sep P f V len rfl tag'
  have eq : k=0 := (BStarSeparatingRail.Cursor.back.inj K).symm
  subst k
  have current := BStarAcquireHistoryReturn.busy_end hp P
  obtain ⟨head,slot⟩ := BStarResetChartService.root_header hp chart current.1.1
  have old : atSite (z root).long 0=.reply f := by
    change atSite (z root).long (addr 0).2=.reply f at R
    rwa [slot] at R
  have bound : bind (longGeometry B (z root)) 0 (atSite (z root).long 0)=.reply f := by
    rw [old]
    exact BStarAcquireReturn.valid_reply_binding _ _ _ V
  have H := BStarAdmissionPaceCore.actual_acquire_consumes hp
    (base:=base) (x:=z) (addr:=addr) (len:=len) (e:=door)
    slot head (sep door) current E f V.1 V.2.1 bound
  have success : f.outcome≠1 :=
    fun eq=>(by decide : (0 : BitVec 2)≠1) (good.symm.trans eq)
  rw [if_neg success] at H
  exact H

end L4.Height.FreshAttempt

