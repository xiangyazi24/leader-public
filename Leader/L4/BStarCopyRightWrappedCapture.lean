import Leader.L4.BStarCopyRightWrappedAck
import Leader.L4.BStarCopyRightWrappedLoadCoverage
import Leader.L4.BStarCopyRightReleaseCursor
import Leader.L4.BStarCopyLoadAckOrder
import Leader.L4.BStarCopyRightAckRetention
import Leader.L4.BStarCopyRightLoadToInject
import Leader.L4.BStarCopyRightActiveFold

namespace L4.BStarCopyRightWrappedCapture
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedBandScan BStarGeneratedOwner BStarCaptureDoorHistory
open BStarLongDoor BStarLongLayout BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightAckRetention BStarCopyRightStrip BStarCopyRightAuthority
open BStarCopyRightLoadCoverage BStarCopyRightLoadToInject BStarCopyRightReleaseClass
open BStarClearanceDataChart BStarLongToken BStarLongCommandData BStarLongPackets
open BStarCommitOperands BStarCutOperandReadout BStarLongPublication
open BStarSeparatingRail BStarOwnerLaunchOrigin
open BStarCopyRightMark BStarCopyRightDeposit

open BStarLongCommand BStarLongEvents BStarLongPrep BStarCopyLoadHistory
open BStarCopyRightPostload BStarCopyRightPreinject BStarCopyRightCapture BStarCopyOwnedFrozen
open BStarSeparatorControl BStarCopyLoadCarry BStarAcquireAnchors BStarResetMarkAdapter
open BStarCopyOperand BStarClearanceSource BStarResetChartService
local notation "step" => ring

open BStarAcquireForwardTrace BStarAcquireHistoryReturn BStarCopyLoadAckOrder
open BStarCopyRightReleaseCapture (digitTable)

private theorem append_busy {base x : X} {slot : Nat→Pos n} {len op : Nat}
    {a b c : Cursor} {u v : List (Fin n)}
    (P : BusyOnly hp base slot len op x a u b)
    (Q : BusyOnly hp base slot len op (play x u) b v c) :
    BusyOnly hp base slot len op x a (u++v) c := by
  induction P with
  | nil _ => exact Q
  | cons I E _ ih => exact .cons I E (ih Q)

private theorem load_word_linked {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (G : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy 8 (.out j))) :
    ∃ (pre : List (Fin n)) (e : Fin n) (post : List (Fin n)),
      w=pre++e::post ∧ e=RearTrace.predecessor (S.getD 0 fall).1 ∧
      let root := (S.getD 0 fall).1
      let old := play x pre
      let new := step old e
      (ctrlOp.read (old root).long).toNat=8 ∧
      Launch (old root).long (new root).long ∧
      BusyOnly hp base (fun k=>S.getD k fall) len 8 new (.out 0) post (.out j) ∧
      LoadWord hp new (S.getD 0 fall) post (S.getD j fall) ∧
      atCursor (play x w) (S.getD j fall)=.forward (payload (captures.read (old root).long).toNat) := by
  obtain ⟨pre,post,e,eq,door,launch,op,P⟩ := from_idle hp G
  let addr := fun k => S.getD k fall
  let root := (addr 0).1
  let old := play x pre
  let new := step old e
  obtain ⟨I,a,F,snap⟩ := launch
  rw [op] at F
  obtain ⟨operand,ok⟩ := issue_load_operand _ _ F
  subst a
  have h16 : (captures.read (old root).long).toNat<64 := (captures.read (old root).long).isLt
  have K := (root_header hp C (busy_start hp P).1.1).2
  have init : atCursor new (addr 0)=.forward (payload (captures.read (old root).long).toNat) := by
    change atSite (new root).long (addr 0).2=_
    rw [K]
    have A := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) snap
    change atSite (new root).long 0= forward (ctrlOp.read (old root).long).toNat _ at A
    rw [op] at A
    exact A
  have trace := busy_load_word hp C sep P _ h16 ok 0 j rfl rfl init
  refine ⟨pre,e,post,eq,door,op,⟨I,_,by rwa [op],snap⟩,P,trace,?_⟩
  rw [eq,BStarResetSchedule.run_append]
  exact load_word_carries hp trace _ h16 ok init

private theorem freezes_with_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (G : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy 8 (.out j)))
    (e : Fin n) (s : Side) (rev : Bool) (cl : CommandClaim) :
    let y := play x w
    let g := oldPair B y e
    let i := site e s
    address e cl.source=S.getD j fall →
    dataOwner (oldH6 B base) i (loadLane s rev).occurrence=o.val →
    cl∈orderedCommands g → cl.kind≠.door →
    cl.source=⟨s,loadOcc rev⟩ → (geometry g s).inside=true →
    ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
      w=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      let root := (S.getD 0 fall).1
      (ctrlOp.read ((play x pre) root).long).toNat=8 ∧
      Launch ((play x pre) root).long ((step (play x pre) launch) root).long ∧
      BusyOnly hp base (fun k=>S.getD k fall) len 8 (step (play x pre) launch) (.out 0) post (.out j) ∧
      let capture := (captures.read ((play x pre) root).long).toNat
      bank.val=(if rev then capture%4 else capture/16%4) ∧
      (readLane (Sheet.index (loadLane s rev).occurrence) (step y e i).long).frozen=
        oldBankPacket (y i).long bank := by
  dsimp only
  intro ptr own sel noDoor origin inside
  obtain ⟨pre,a,post,decomp,door,op,L,P8,T,_⟩ := load_word_linked hp C sep G
  have cur : Current hp base (fun k => S.getD k fall) len (play x w) (.busy 8 (.out j)) := by
    obtain ⟨u,v,k,W,_,_,_,P⟩ := from_idle hp G
    rw [W,BStarResetSchedule.run_append]
    change Current hp base (fun t => S.getD t fall) len (play (step (play x u) k) v) (.busy 8 (.out j))
    exact BStarAcquireHistoryReturn.busy_end hp P
  have Eq : play x w=play (step (play x pre) a) post := by
    rw [decomp,BStarResetSchedule.run_append]; rfl
  have tr : LoadWord hp (step (play x pre) a) ((S.getD 0 fall).1,0) post (address e cl.source) := by
    have K := (root_header hp C cur.1.1).2
    rw [ptr,show ((S.getD 0 fall).1,0)=S.getD 0 fall from Prod.ext rfl K.symm]
    exact T
  rw [Eq] at cur sel inside
  obtain ⟨bank,H,V⟩ :=
    pointed_freeze_from_launch hp C L op post e s rev cl (sep e) j tr cur ptr own sel noDoor origin inside
  refine ⟨pre,post,a,bank,decomp,door,op,L,P8,H,?_⟩
  rw [Eq]
  exact V

private theorem generated_append {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem original_with_launch {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead w8 middle w10 : List (Fin n)) (load : Fin n) (side : Side)
    (C : CommandClaim) (f : Payload) (k : Nat) (kl : k≤len)
    (loadLoc : address load C.source=S.getD k fall)
    (source : C.source=⟨side,2⟩)
    (selected : C∈orderedCommands (oldPair B (play origin lead) load))
    (noDoor : C.kind≠.door)
    (advanced : (C,.advance f)∈actualOffers (oldPair B (play origin lead) load)
      (((play origin lead) load).long,((play origin lead) (rightNeighbor load)).long))
    (inside : (geometry (oldPair B (play origin lead) load) side).inside=true)
    (own : dataOwner (oldH6 B base) (site load side) .rs=o.val)
    (before : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle lead (.busy 8 (.out k)))
    {z : Cursor}
    (loadEvent : Event hp (fun t => S.getD t fall) len (play origin lead) load
      (.busy 8 (.out k)) (.busy 8 z))
    (b8 : BusyOnly hp base (fun t => S.getD t fall) len 8 (ring (play origin lead) load) z w8 (.back 0))
    (M : OwnMiddle hp base origin (fun t => S.getD t fall) len ((lead++[load])++w8) middle)
    (b10 : BusyOnly hp base (fun t => S.getD t fall) len 10
      (play origin (((lead++[load])++w8)++middle)) (.out 0) w10 (.out k))
    (fiber : ∀ a b, ((((lead++[load])++w8)++middle)++w10)=a++b →
      ∀ v,BStarLongFixedRouting.Layout B base v=BStarLongFixedRouting.Layout B (play origin a) v) :
    ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
      lead=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
      (ctrlOp.read ((play origin pre) (S.getD 0 fall).1).long).toNat=8 ∧
      Launch ((play origin pre) (S.getD 0 fall).1).long
        ((ring (play origin pre) launch) (S.getD 0 fall).1).long ∧
      BusyOnly hp base (fun j=>S.getD j fall) len 8 (ring (play origin pre) launch)
        (.out 0) post (.out k) ∧
      bank.val=(captures.read ((play origin pre) (S.getD 0 fall).1).long).toNat % 4 ∧
      (readLane (Sheet.index .rs)
        (play origin ((((lead++[load])++w8)++middle)++w10) (site load side)).long).frozen=
        oldBankPacket ((play origin lead) (site load side)).long bank := by
  let i := site load side
  have idx : S.getD k fall=(i,2) := by
    rw [←loadLoc,source]
  have k2 : C.source.occurrence=2 := congrArg At.occurrence source
  have past := load_enters_past hp load (sep load) C f k2 loadLoc advanced loadEvent (busy_start hp b8)
  have pre8 : play origin (lead++[load])=ring (play origin lead) load := by
    rw [BStarResetSchedule.run_append]; rfl
  obtain ⟨pre,post,launch,bank,L,D,pc8,launch8,Busy8,bidx,freeze⟩ :=
    freezes_with_origin hp chart sep before load side true C loadLoc own selected noDoor source inside
  have reached8 := BStarGeneratedTapeCuts.at_end hp before
  have G8 : GeneratedOwner hp base (fun t => S.getD t fall) len origin .idle (lead++[load]) (.busy 8 z) := by
    apply generated_append hp before
    exact .next reached8 loadEvent (.endpoint (busy_start hp b8))
  have F8 := frozen_busy_suffix hp chart sep i k kl idx own 8 (.inl rfl)
    (lead++[load]) pre8.symm G8 b8 (fun _ => past)
    (fun a e b eq => by
      have H := fiber ((lead++[load])++a) ((e::b)++middle++w10) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append,pre8] at H
      exact H)
  have F9 := rs_frozen_between hp chart sep ((lead++[load])++w8) middle (.busy 10 (.out 0))
    M.end10 i own
    (fun a e b eq => fiber (((lead++[load])++w8)++a) ((e::b)++w10) (by simp [eq,List.append_assoc]))
    (fun a e b eq op j I => by
      have pc := M.outward9 a e b eq op j I
      exact ⟨by omega,by omega,fun ne => (ne pc).elim⟩)
  have F10 := frozen_pc10_prefix hp chart sep i k kl idx own (((lead++[load])++w8)++middle)
    rfl M.end10 b10 (fun a e b eq => by
      have H := fiber ((((lead++[load])++w8)++middle)++a) (e::b) (by simp [eq,List.append_assoc])
      rw [BStarResetSchedule.run_append] at H
      exact H)
  rw [←BStarResetSchedule.run_append] at F10
  rw [←pre8,←BStarResetSchedule.run_append] at F8
  have orig : (readLane (Sheet.index .rs) (play origin (lead++[load]) i).long).frozen =
      oldBankPacket ((play origin lead) i).long bank := by
    rw [pre8]
    exact freeze
  have result := F10.trans (F9.trans (F8.trans orig))
  exact ⟨pre,post,launch,bank,L,D,pc8,launch8,Busy8,bidx,result⟩

/-- Exact captured bytes at a literal right release. LOAD coverage is
derived from the completed original word; the matched ACK-to-LOAD
launch chronology remains supplied explicitly, but no per-site bank,
old packet equality, or frozen-field premise is supplied. -/
theorem linked_release_bytes {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : tail+1=seam+r)
    (w8 middle u : List (Fin n)) (e : Fin n) (m : Mode)
    (R : ReleaseAt hp (play origin ((w8++middle)++u)) e a seam tail (fun j=>S.getD j fall) len m)
    (M : OwnMiddle hp base origin (fun t=>S.getD t fall) len w8 middle)
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (w8++middle)) (.out 0) u (.out R.k))
    (fiber : ∀ q z, ((w8++middle)++u)=q++z →
      ∀ i,Layout B base i=Layout B (play origin q) i)
    (cut whole : List (Fin n))
    (A : Acquisition hp origin cut whole (endpoint (oldH6 B base) hh o 2).1 2)
    (common : ∃ v,whole=cut++v)
    (sameWhole : ∃ suffix,whole=((w8++middle)++u)++suffix)
    (ackLead : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (ack2 : ((capturedSelector 2).read (ring (play origin ackLead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play origin A.lead) (endpoint (oldH6 B base) hh o 2).1).long).val)
    (ackTape : ∃ rest,w8=ackLead++ack::rest)
    (old5 : pc (play origin ackLead) (S.getD 0 fall).1=5)
    (afterAck : ∀ before rest,w8=((ackLead++[ack])++before)++rest →
      ∃ m,GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
        .idle before m ∧
      (∀ p q,before=p++q →
        let y := play origin ((ackLead++[ack])++p)
        Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)))
    (layout : ∀ w,oldH6 B (play origin (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play origin (cut++w)) e z
      (endpoint (oldH6 B base) hh o 2).1) :
    (lanes (play origin ((w8++middle)++u)) (addr a R.i) .rs).frozen=
      .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam (R.i-seam)) := by
  obtain ⟨loadLead,load,rest,k,C,f,W,kl,idx,loc,src,nd,G,E,remainder,offer,inside⟩ :=
    BStarCopyRightWrappedLoadCoverage.original_rs_load_visit hp chart sep a seam tail strip ownHead M.start8 R.i R.range.1 R.range.2
  have sameK : k=R.k := by
    have h := chart.length
    exact (List.getD_inj (by omega) (by have := R.strict; omega) chart.nodup).mp (idx.trans R.ptr.symm)
  subst k load
  let load := addr a R.i
  have wEq : w8=(loadLead++[load])++rest := W.trans (by simp [load,List.append_assoc])
  have ptr : address load C.source=S.getD R.k fall := by rw [src,idx]; rfl
  have own := (BStarCopyRightWrappedReleaseClass.strip_same_owner strip R.i R.range.2).trans ownHead
  rw [show rail seam R.i=.rs from if_neg (Nat.not_lt_of_ge R.range.1)] at own
  have sel : C∈orderedCommands (oldPair B (play origin loadLead) load) := by
    rw [←actualOffers_claims _ (((play origin loadLead) load).long,
      ((play origin loadLead) (rightNeighbor load)).long)]
    exact List.mem_map.mpr ⟨_,offer,rfl⟩
  obtain ⟨lead,t,issue,bank,L,_,pc8,_,b8,bank8,F⟩ := original_with_launch hp chart sep loadLead rest middle u
    load .left C f R.k (Nat.le_of_lt kl) ptr src sel nd offer inside own G E remainder
    (wEq ▸ M) ((congrArg (· ++ middle) wEq) ▸ P10)
    (fun q z E => fiber q z (by rwa [wEq]))
  have preEq : play origin loadLead=play (ring (play origin lead) issue) t := by
    rw [L,BStarResetSchedule.run_append]; rfl
  have follow : BusyOnly hp base (fun j=>S.getD j fall) len 8 (play origin loadLead)
      (.out R.k) (load::rest) (.back 0) :=
    .cons (BStarGeneratedTapeCuts.at_end hp G) E remainder
  have tailBusy : BusyOnly hp base (fun j=>S.getD j fall) len 8
      (play (ring (play origin lead) issue) t) (.out R.k) (load::rest) (.back 0) := by
    rw [←preEq]; exact follow
  have wholeBusy := append_busy hp b8 tailBusy
  obtain ⟨z,wt⟩ := ackTape
  have wEq' : w8=lead++issue::(t++load::rest) := by
    rw [W,L,List.append_assoc,List.cons_append]
  obtain ⟨beforeIssue,Bef⟩ := issue8_after_ack5 hp (base:=base) (origin:=origin) (slot:=fun j=>S.getD j fall) (len:=len) lead ackLead (t++load::rest) z issue ack
    (wEq'.symm.trans wt) pc8 old5 wholeBusy
  obtain ⟨mode,H,Band⟩ := afterAck beforeIssue (issue::(t++load::rest))
    (wEq'.trans (by rw [←Bef]))
  let d : Fin r := ⟨R.i-seam,by have := R.range.1; have := R.range.2; omega⟩
  have I : seam+d.val=R.i := by dsimp [d]; have := R.range.1; omega
  obtain ⟨zs,WS⟩ := sameWhole
  have loadWhole : whole=((((ackLead++[ack])++beforeIssue)++issue::t)++(load::rest)++middle++u++zs) := by
    rw [←Bef,←L,WS,W]

  have pack := BStarCopyRightWrappedAck.packed_after_actual_ack hp hh o chart a seam tail strip ownHead (by omega) A common
    ackLead beforeIssue t ((load::rest)++middle++u++zs) ack issue mode birthBeforeAck
    (loadWhole.trans (by simp [List.append_assoc])) H Band sep layout auth bank
    (by rwa [←Bef]) ack2 d
  dsimp only at pack
  rw [←Bef,←L,I] at pack
  change (readLane (Sheet.index .rs) (play origin ((w8++middle)++u) load).long).frozen=_
  have prefixField : (readLane (Sheet.index .rs) (play origin ((w8++middle)++u) load).long).frozen=
      oldBankPacket ((play origin loadLead) load).long bank :=
    (congrArg (fun word => (readLane (Sheet.index .rs) (play origin ((word++middle)++u) load).long).frozen) wEq).trans F
  refine prefixField.trans (pack.trans ?_)
  unfold oldBankPacket digitTable
  rw [I]

open BStarCopyRightReleaseCursor

theorem all_linked_release_bytes {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : tail+1=seam+r)
    (w8 middle tour : List (Fin n)) {fin : Cursor}
    (M : OwnMiddle hp base origin (fun t=>S.getD t fall) len w8 middle)
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin (w8++middle)) (.out 0) tour fin)
    (fiber : ∀ q z, ((w8++middle)++tour)=q++z →
      ∀ i,Layout B base i=Layout B (play origin q) i)
    (cut whole : List (Fin n))
    (A : Acquisition hp origin cut whole (endpoint (oldH6 B base) hh o 2).1 2)
    (common : ∃ v,whole=cut++v)
    (sameWhole : ∃ suffix,whole=((w8++middle)++tour)++suffix)
    (ackLead : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (ack2 : ((capturedSelector 2).read (ring (play origin ackLead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play origin A.lead) (endpoint (oldH6 B base) hh o 2).1).long).val)
    (ackTape : ∃ rest,w8=ackLead++ack::rest)
    (old5 : pc (play origin ackLead) (S.getD 0 fall).1=5)
    (afterAck : ∀ before rest,w8=((ackLead++[ack])++before)++rest →
      ∃ m,GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play origin ackLead) ack)
        .idle before m ∧
      (∀ p q,before=p++q →
        let y := play origin ((ackLead++[ack])++p)
        Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)))
    (layout : ∀ w,oldH6 B (play origin (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play origin (cut++w)) e z
      (endpoint (oldH6 B base) hh o 2).1) :
    ∀ u e v,tour=u++e::v →
      ∀ m (R : ReleaseAt hp (play (play origin (w8++middle)) u) e a seam tail (fun j=>S.getD j fall) len m),
      (lanes (play (play origin (w8++middle)) u) (addr a R.i) .rs).frozen=
        .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam (R.i-seam)) := by
  intro u e v E
  obtain ⟨cursor,P,_⟩ := cut_busy hp u (e::v) (E ▸ P10)
  have exactAt (y : X) (Y : y=play origin ((w8++middle)++u)) :
      ∀ m (R : ReleaseAt hp y e a seam tail (fun j=>S.getD j fall) len m),
      Current hp base (fun j=>S.getD j fall) len y (.busy 10 cursor) →
      (lanes y (addr a R.i) .rs).frozen=
        .data (digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam (R.i-seam)) := by
    subst y
    intro m R cur
    have pos := release_cursor hp cur R
    have cl := P
    rw [pos] at cl
    apply linked_release_bytes hp chart sep a seam tail strip ownHead width w8 middle u e m R M cl _ cut whole A common _
      ackLead ack birthBeforeAck ack2 ackTape old5 afterAck layout auth
    · intro q z D
      apply fiber q (z++e::v)
      exact (congrArg ((w8++middle)++·) E).trans
        ((List.append_assoc _ u _).symm.trans (by rw [D,List.append_assoc]))
    · obtain ⟨z,W⟩ := sameWhole
      refine ⟨(e::v)++z,?_⟩
      rw [W]
      exact congrArg (· ++ z) ((congrArg ((w8++middle)++·) E).trans (List.append_assoc _ u _).symm) |>.trans
        (List.append_assoc _ _ _)
  exact fun m R => exactAt _ (BStarResetSchedule.run_append _ _ _ _).symm m R (busy_end hp P)

#print axioms all_linked_release_bytes
#print axioms linked_release_bytes
end L4.BStarCopyRightWrappedCapture
