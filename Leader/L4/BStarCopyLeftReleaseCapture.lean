import Leader.L4.BStarWriterTransferWindow
import Leader.L4.BStarCopyLeftReadyWord
import Leader.L4.BStarCopyLeftOneCapture
import Leader.L4.BStarCopyLeftAckRetention
import Leader.L4.BStarCopyLeftReleaseOrder
import Leader.L4.BStarCopyRightLoadCoverage
import Leader.L4.BStarCopyLeftInjectionMark

namespace L4.BStarCopyLeftReleaseCapture
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongDoor BStarLongCommandData
open BStarCopyRightStrip (addr)
open BStarCopyLeftStrip BStarCopyLeftInjectionMark BStarCopyRightLoadCoverage
open BStarCopyLoadHistory BStarCopyLoadCarry BStarCopyOperand BStarCopyOwnedFrozen
open BStarAcquireVisitOrder BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireLiteralChain
open BStarResetChartTouch BStarClearanceDataChart BStarAcquireAnchors BStarResetMarkAdapter
open BStarSeparatingRail BStarAcquireForwardTrace BStarAcquireHistoryReturn BStarResetChartService
open BStarLongPackets BStarLongCommand

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem busy_append {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b c : Cursor} {u v : List (Fin n)}
    (P : BusyOnly hp base addr len op x a u b)
    (Q : BusyOnly hp base addr len op (play x u) b v c) :
    BusyOnly hp base addr len op x a (u++v) c := by
  induction P with
  | nil _ => exact Q
  | cons I E _ ih => exact .cons I E (ih Q)

open BStarCopyLeftOneCapture
theorem common_bank_and_cuts {base x : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (rootAt : a=(S.getD 0 fall).1)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 8 (.back 0))) :
    ∃ (lead : List (Fin n)) (launch : Fin n) (suffix : List (Fin n)) (bank : Fin 3),
      w=lead++launch::suffix ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      bank.val=(captures.read ((play x lead) (S.getD 0 fall).1).long).toNat / 16 % 4 ∧
      BStarClearanceSource.Launch ((play x lead) (S.getD 0 fall).1).long
        ((ring (play x lead) launch) (S.getD 0 fall).1).long ∧
      (ctrlOp.read ((play x lead) (S.getD 0 fall).1).long).toNat=8 ∧
      let y := ring (play x lead) launch
      ∀ i, i<seam → (longGeometry B (base (addr a i))).inside=true →
        ∃ (pre : List (Fin n)) (rest : List (Fin n)) (k : Nat),
          suffix=pre++(addr a i)::rest ∧ k<len ∧ S.getD k fall=(addr a i,0) ∧
          BusyOnly hp base (fun j=>S.getD j fall) len 8 y (.out 0) pre (.out k) ∧
          BusyOnly hp base (fun j=>S.getD j fall) len 8
            (ring (play y pre) (addr a i)) (.out (k+1)) rest (.back 0) ∧
          Event hp (fun j=>S.getD j fall) len (play y pre) (addr a i)
            (.busy 8 (.out k)) (.busy 8 (.out (k+1))) ∧
          (readLane (Sheet.index .ls) (ring (play y pre) (addr a i) (addr a i)).long).frozen=
            oldBankPacket ((play y pre) (addr a i)).long bank := by
  obtain ⟨lead,suffix,launch,W,D,Launch,pc8,T⟩ := from_idle hp G
  let y := ring (play x lead) launch
  let root := (S.getD 0 fall).1
  let old : BitVec LW := ((play x lead) root).long
  let u := (captures.read old).toNat
  have launchCopy := Launch
  obtain ⟨_,arg,init,snap⟩ := launchCopy
  change initial (ctrlOp.read old).toNat old=some arg at init
  change (ctrlOp.read old).toNat=8 at pc8
  rw [pc8] at init
  obtain ⟨argEq,validArg⟩ := issue_load_operand _ _ init
  have valid : selTriple u=true := by rw [argEq] at validArg; exact validArg
  have uw : u<64 := (captures.read old).isLt
  obtain ⟨bank,_,idxBank⟩ := captured_operand_index u uw valid false
  have root0 := (root_header hp chart (busy_start hp T).1.1).2
  have start : project (fun j=>S.getD j fall) y 0=.forward (payload u) := by
    change atSite (y root).long (S.getD 0 fall).2=_
    rw [root0]
    have F := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) snap
    change atSite (y root).long 0=forward (ctrlOp.read old).toNat arg at F
    rw [pc8] at F
    exact F.trans (load_issue_payload old arg init)
  refine ⟨lead,launch,suffix,bank,W,D,idxBank,Launch,pc8,?_⟩
  dsimp only
  intro i hi inBase
  obtain ⟨k,kl,idx⟩ := ls_ord hp chart a seam width i strip rootAt hi
  obtain ⟨pre,e,rest,R,part,ev,after⟩ := busy_crosses hp T kl 0 rfl (Nat.zero_le _)
  let z := play y pre
  have cur := busy_end hp part
  have part' := busy_append hp part (.cons cur ev (.nil (busy_start hp after)))
  have trail' := busy_load_word hp chart sep part' u uw valid 0 (k+1) rfl rfl start
  have afterF := load_word_carries hp trail' u uw valid start
  rw [BStarResetSchedule.run_append] at afterF
  have q : project (fun j=>S.getD j fall) (ring z e) (k+1)=.forward (payload u) := afterF
  obtain ⟨cl,d,f,selected,dest,src,_⟩ := BStarNumericChronology.ring_departure
    hp chart e (sep e) 8 k kl cur.1 cur.2.1 cur.2.2 (payload u) q rfl
  have kc : cl.source.occurrence=0 := congrArg Prod.snd (src.symm.trans idx)
  have mem : cl∈orderedCommands (oldPair B z e) := by
    rw [←actualOffers_claims _ ((z e).long,(z (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,selected,rfl⟩
  obtain ⟨srcL,nd⟩ := k0_link_left (oldPair B z e) cl d mem kc dest
  have loc := congrArg Prod.fst (src.symm.trans idx)
  have ee : e=addr a i := by rwa [srcL] at loc
  have inside : (longGeometry B (z e)).inside=true := by
    have same := congrArg (fun z : Bool × Bool × Bool => z.2.1) (cur.1.1 e)
    exact same.symm.trans (ee.symm ▸ inBase)
  have ow := BStarCopyLeftReadyWord.all_owner hp chart a seam width strip rootAt i (by omega)
  have own : dataOwner (oldH6 B base) e .ls=o.val := by
    rw [ee]
    simpa [rail,hi] using ow
  have tr := busy_load_word hp chart sep part u uw valid 0 k rfl rfl start
  have Z : (root,0)=S.getD 0 fall := Prod.ext rfl root0.symm
  have loadWord : LoadWord hp y (root,0) pre (address e cl.source) := by
    rw [Z,←src]; exact tr
  obtain ⟨actualBank,bk,F⟩ := pointed_freeze_from_launch hp chart Launch pc8 pre e .left false cl
    (sep e) k loadWord cur src.symm own mem nd srcL inside
  have one : actualBank=bank := Fin.ext (bk.trans idxBank.symm)
  subst actualBank
  exact ⟨pre,rest,k,ee ▸ R,kl,idx,part,ee ▸ after,ee ▸ ev,ee ▸ F⟩



open BStarCopyRightLoadToInject (OwnMiddle)
open BStarCopyLeftLoadToInject BStarCopyLeftFrozen BStarCopyLeftPreinject
open BStarAcquireVisitOrder BStarAcquireHistoryReturn BStarAcquireForwardTrace BStarResetMarkAdapter
open BStarCopyLeftReleaseClass BStarCopyLeftReleaseOrder
open BStarCopyLeftMark
open BStarCommitOperands BStarCutOperandReadout BStarLongLayout BStarLongFixedRouting
open BStarGeneratedBandScan BStarLongPublication

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

theorem frame_after_exact_load {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w8 middle w10 : List (Fin n)) (load : Fin n)
     (k j : Nat) (kl : k≤len) (jl : j≤len)
    (injectAddr : S.getD j fall=(load,5))
    (idx : S.getD k fall=(load,0))
    (own : dataOwner (oldH6 B base) (load) .ls=o.val)
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
      (play origin ((((lead++[load])++w8)++middle)++w10) (load)).long).frozen =
    (readLane (Sheet.index .ls) (ring (play origin lead) load (load)).long).frozen := by
  let i := load
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


open BStarClearanceSource BStarGeneratedTapeCuts

private theorem busy_generated {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (T : BusyOnly hp base addr len op x z w d) :
    GeneratedOwner hp base addr len x (.busy op z) w (.busy op d) := by
  induction T with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- One named operand table, in physical source LS order. -/
def digitTable (x : X) (header a : Fin n) (j : Nat) : BitVec 36 :=
  (bankPart (readSel (x header).long) 9 36 (by decide)).read (x (addr a j)).long

/-- Each selected pre-K5 release uses its same-site original K0 load.
The single remaining ACK-to-ISSUE8 match identifies the controller's
common capture; no per-source command, witness tape, or bytes equality
is assumed. -/
theorem release_bytes {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (root : a=(S.getD 0 fall).1) (bound : r≤seam)
    (width_eq : width=r)
    (flag : ∀ j<seam,(longGeometry B (base (addr a j))).inside=true ↔ j<width)
    (w8 middle u : List (Fin n)) (e : Fin n) (m : Mode)
    (R : ReleaseAt hp (play origin ((w8++middle)++u)) e a seam (fun j=>S.getD j fall) len m)
    (M : OwnMiddle hp base origin (fun t=>S.getD t fall) len w8 middle)
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (w8++middle)) (.out 0) u (.out R.k))
    (fiber : ∀ q z, ((w8++middle)++u)=q++z →
      ∀ i,Layout B base i=Layout B (play origin q) i)
    (cut whole : List (Fin n))
    (A : Acquisition hp origin cut whole (endpoint (oldH6 B base) hh o 0).1 0)
    (common : ∃ v,whole=cut++v)
    (sameWhole : ∃ suffix,whole=((w8++middle)++u)++suffix)
    (ackLead : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (ack0 : ((capturedSelector 0).read (ring (play origin ackLead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play origin A.lead) (endpoint (oldH6 B base) hh o 0).1).long).val)
    (launchAfterAck : ∀ lead issue suffix,
      Found hp base (fun j=>S.getD j fall) len 8 origin w8 (.back 0) →
      w8=lead++issue::suffix →
      pc (play origin lead) (S.getD 0 fall).1=8 →
      BusyOnly hp base (fun j=>S.getD j fall) len 8 (ring (play origin lead) issue)
        (.out 0) suffix (.back 0) →
      ∃ beforeIssue k,
        lead=(ackLead++[ack])++beforeIssue ∧
        GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
          .idle beforeIssue k ∧
        (∀ p q,beforeIssue=p++q →
          let y := play origin ((ackLead++[ack])++p)
          Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)))
    (layout : ∀ w,oldH6 B (play origin (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play origin (cut++w)) e z
      (endpoint (oldH6 B base) hh o 0).1) :
    (sample (play origin ((w8++middle)++u)) a seam R.i).frozen=
      .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 0).1 a R.i) := by
  let x := play origin ((w8++middle)++u)
  let i := addr a R.i
  let key := fun j=>S.getD j fall
  let rootSite := (key 0).1
  have ow := BStarCopyLeftReadyWord.all_owner hp chart a seam width strip root R.i (by have := R.range; omega)
  have own : dataOwner (oldH6 B base) i .ls=o.val := by
    simpa [i,rail,R.range] using ow
  have insideNow := release_inside hp R
  have eq := congrArg (fun b : Bool×Bool×Bool=>b.2.1) (fiber ((w8++middle)++u) [] (by simp) i)
  have inside : (longGeometry B (base i)).inside=true := eq.trans insideNow
  let d : Fin r := ⟨R.i,(width_eq ▸ (flag R.i R.range).mp inside)⟩
  obtain ⟨lead,issue,suffix,bank,W,door,sel,L,pc8,every⟩ :=
    common_bank_and_cuts hp chart sep a seam width strip root M.start8
  obtain ⟨pre,rest,k,U,kl,idx,P,B8,event,freeze⟩ := every R.i R.range inside
  let y := ring (play origin lead) issue
  have complete : BusyOnly hp base key len 8 y (.out 0) suffix (.back 0) := by
    have H := busy_append hp P (.cons (busy_end hp P) event B8)
    rw [U]
    exact H
  have found : Found hp base key len 8 origin w8 (.back 0) :=
    ⟨lead,suffix,issue,W,door,L,pc8,complete⟩
  obtain ⟨delta,mode,leadEq,Gack,band⟩ := launchAfterAck lead issue suffix found W pc8 complete
  have gsplit : GeneratedOwner hp base key len origin .idle (lead++issue::suffix) (.busy 8 (.back 0)) :=
    W ▸ M.start8
  obtain ⟨z,prior,Grest⟩ := BStarGeneratedTapeCuts.split hp lead (issue::suffix) gsplit
  have mid := BStarGeneratedTapeCuts.at_start hp Grest
  have zIdle := idle_of_issue hp mid L.1
  subst z
  let loadLead := lead++issue::pre
  have replay : play origin loadLead=play y pre := by rw [BStarResetSchedule.run_append]; rfl
  have priorLoad : GeneratedOwner hp base key len origin .idle loadLead (.busy 8 (.out k)) := by
    have launchEvent := Event.launch (hp:=hp) (addr:=key) (len:=len) door L
    rw [pc8] at launchEvent
    exact generated_append hp prior (.next mid launchEvent (busy_generated hp P))
  have cut8 : (loadLead++[i])++rest=w8 := by
    rw [W,U]
    simp [loadLead,i,List.append_assoc,List.cons_append]
  have wholeCut : ∃ after,whole=loadLead++after := by
    obtain ⟨s,S⟩ := sameWhole
    refine ⟨i::(rest++middle++u++s),?_⟩
    rw [S,←cut8]
    simp [List.append_assoc]
  obtain ⟨after,wholeRead⟩ := wholeCut
  have E : whole=((((ackLead++[ack])++delta)++issue::pre)++after) := by
    rw [wholeRead,←leadEq]
  have mf : OwnMiddle hp base origin key len ((loadLead++[i])++rest) middle := cut8.symm ▸ M
  have pf : BusyOnly hp base key len 10 (play origin (((loadLead++[i])++rest)++middle))
      (.out 0) u (.out R.k) := cut8.symm ▸ P10
  have forward := frame_after_exact_load hp chart sep loadLead rest middle u i k R.k
    (Nat.le_of_lt kl) (Nat.le_of_lt R.strict) R.ptr idx own priorLoad (replay.symm ▸ event)
    (replay.symm ▸ B8) mf pf (by rw [cut8]; exact fiber)
  rw [cut8,replay] at forward
  have bankArg : bank.val=(captures.read (play origin ((ackLead++[ack])++delta) rootSite).long).toNat/16%4 :=
    leadEq ▸ sel
  have rootSpec : a=(endpoint (oldH6 B base) hh o 0).1 :=
    root.trans (congrArg Prod.fst chart.root)
  have valEq := BStarCopyLeftAckRetention.packed_after_actual_ack hp hh o chart a seam width strip
    rootSpec bound A common ackLead delta pre after ack issue mode birthBeforeAck E Gack band sep
    layout auth bank bankArg ack0 d
  dsimp only at valEq
  rw [←leadEq,←show loadLead=lead++issue::pre from rfl,replay] at valEq
  unfold sample
  rw [rail,if_pos R.range]
  exact forward.trans (freeze.trans valEq)


/-- Match the common LOAD launch to the named successful ACQUIRE
ACK already on this same tape. An earlier launch is impossible:
its literal WAIT-8 flight would cross the old ACK5 state. -/
theorem exact_match_after_ack {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (_chart : Chart hp base hh o S len fall)
    (w8 ackLead postAck : List (Fin n)) (ack : Fin n)
    (after : w8=ackLead++ack::postAck)
    (pc5 : pc (play origin ackLead) (S.getD 0 fall).1=5)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
      .idle postAck (.busy 8 (.back 0)))
    (Bnd : ∀ p q,postAck=p++q →
      let y := play origin ((ackLead++[ack])++p)
      Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i))
    (lead : List (Fin n)) (issue : Fin n) (suffix : List (Fin n))
    (W : w8=lead++issue::suffix)
    (old8 : pc (play origin lead) (S.getD 0 fall).1=8)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len 8 (ring (play origin lead) issue)
      (.out 0) suffix (.back 0)) :
    ∃ beforeIssue k,
        lead=(ackLead++[ack])++beforeIssue ∧
        GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
          .idle beforeIssue k ∧
        (∀ p q,beforeIssue=p++q →
          let y := play origin ((ackLead++[ack])++p)
          Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)) := by
  let root := (S.getD 0 fall).1
  have E : ackLead++ack::postAck=lead++issue::suffix := after.symm.trans W
  rcases List.append_eq_append_iff.mp E with ⟨w,F,H⟩|⟨w,F,H⟩
  · cases w with
    | nil =>
      have equal : ackLead=lead := by simpa using F.symm
      rw [equal] at pc5
      omega
    | cons f v =>
      have word : lead=(ackLead++[ack])++v := by
        obtain ⟨h,_⟩ := List.cons.inj H
        simp [F,h,List.append_assoc]
      have cut : postAck=v++issue::suffix := (List.cons.inj H).2
      obtain ⟨mode,P,Q⟩ := BStarGeneratedTapeCuts.split hp v (issue::suffix) (cut ▸ G)
      refine ⟨v,mode,word,P,?_⟩
      intro p q C
      exact Bnd p (q++issue::suffix) (by rw [cut,C,List.append_assoc])
  · cases w with
    | nil =>
      have equal : ackLead=lead := by simpa using F
      rw [equal] at pc5
      omega
    | cons f v =>
      have reverse : ackLead=lead++issue::v := by
        obtain ⟨h,_⟩ := List.cons.inj H
        simp [F,h]
      have cut : suffix=v++ack::postAck := (List.cons.inj H).2
      have still := BStarWriterTransferWindow.busy_prefix_pc hp T v (ack::postAck) cut
      have state : play origin ackLead=play (ring (play origin lead) issue) v := by
        rw [reverse,BStarResetSchedule.run_append]
        rfl
      rw [state] at pc5
      change pc (play (ring (play origin lead) issue) v) root=8 at still
      change pc (play (ring (play origin lead) issue) v) root=5 at pc5
      omega

/-- Pointwise premise of the left outward ledger's immutable table,
derived from the matched generated tape, not a per-release oracle. -/
theorem release_bytes_on_matched_tape {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam width : Nat) (strip : Strip B base a seam width)
    (root : a=(S.getD 0 fall).1) (bound : r≤seam)
    (width_eq : width=r)
    (flag : ∀ j<seam,(longGeometry B (base (addr a j))).inside=true ↔ j<width)
    (w8 middle u : List (Fin n)) (e : Fin n) (m : Mode)
    (R : ReleaseAt hp (play origin ((w8++middle)++u)) e a seam (fun j=>S.getD j fall) len m)
    (M : OwnMiddle hp base origin (fun t=>S.getD t fall) len w8 middle)
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (w8++middle)) (.out 0) u (.out R.k))
    (fiber : ∀ q z, ((w8++middle)++u)=q++z →
      ∀ i,Layout B base i=Layout B (play origin q) i)
    (cut whole : List (Fin n))
    (A : Acquisition hp origin cut whole (endpoint (oldH6 B base) hh o 0).1 0)
    (common : ∃ v,whole=cut++v)
    (sameWhole : ∃ suffix,whole=((w8++middle)++u)++suffix)
    (ackLead : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (ack0 : ((capturedSelector 0).read (ring (play origin ackLead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play origin A.lead) (endpoint (oldH6 B base) hh o 0).1).long).val)
    (postAck : List (Fin n))
    (after : w8=ackLead++ack::postAck)
    (pc5 : pc (play origin ackLead) (S.getD 0 fall).1=5)
    (Gafter : GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
      .idle postAck (.busy 8 (.back 0)))
    (Bnd : ∀ p q,postAck=p++q →
      let y := play origin ((ackLead++[ack])++p)
      Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i))
    (layout : ∀ w,oldH6 B (play origin (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play origin (cut++w)) e z
      (endpoint (oldH6 B base) hh o 0).1) :
    (sample (play origin ((w8++middle)++u)) a seam R.i).frozen=
      .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 0).1 a R.i) :=
  release_bytes hp chart sep a seam width strip root bound width_eq flag w8 middle u e m R M P10 fiber
    cut whole A common sameWhole ackLead ack birthBeforeAck ack0
    (fun lead issue tail _ W old8 T =>
      exact_match_after_ack hp chart w8 ackLead postAck ack after pc5 Gafter Bnd lead issue tail W old8 T)
    layout auth

#print axioms release_bytes_on_matched_tape
#print axioms frame_after_exact_load
#print axioms common_bank_and_cuts
#print axioms release_bytes
#print axioms exact_match_after_ack
end L4.BStarCopyLeftReleaseCapture
