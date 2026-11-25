import Leader.L4.BStarCopyRightAttemptAuthenticated
import Leader.L4.BStarAttemptSafety
import Leader.L4.BStarPostCutAttempt
import Leader.L4.BStarOwnedGrantLife
import Leader.L4.BStarAcquireAckWindow

namespace L4.BStarCopyRightActualWitness
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarLongDoor BStarLongCommand
open BStarClearanceSource BStarOwnerLaunchOrigin BStarSeparatingRail BStarLongLayout
open BStarAcquireAckWindow BStarGrantBirth BStarGrantWriterHistory
open BStarNativeReceiptTape (Hit)
open BStarOwnedGrantLife BStarAttemptSafety BStarPostCutAttempt BStarLongGrant
open BStarAcquireLatch BStarAcquireReadout BStarWriterTransferWindow BStarCommitTailScan

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

/-- From the same attempt and actual old centered publication, each
winning ACQUIRE stays live from its recorded mark through the
old publication point. The center cannot publish anywhere in that
interval, including during the genuine ISSUE411 flight. -/
private theorem attempt_wins_with_cut {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w flight : List (Fin n)) (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (centerOwner : commandOwner (oldH6 B base) center 1=o.val)
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (A : AttemptPrefix hp base x (fun j => S.getD j fall) len w)
    (launch : Launch (run x w (S.getD 0 fall).1).long (step (run x w) door (S.getD 0 fall).1).long)
    (op : pc (run x w) (S.getD 0 fall).1=411)
    (F : BusyOnly hp base (fun j => S.getD j fall) len commitOp
      (step (run x w) door) (.out 0) flight (.out k)) :
    ∃ (ackLead : List (Fin n)) (ack : Fin n),
      (∃ middle,w=ackLead++ack::middle) ∧
      ∀ j : Fin 3,
      ∃ (pre post suffix : List (Fin n)) (birth i : Fin n) (v : Visit),
        ackLead=pre++birth::post ∧ w++door::flight=pre++birth::suffix ∧
        let old := run x pre
        let born := step old birth
        let src := (step (run x ackLead) ack (S.getD 0 fall).1).long
        commandOwner (oldH6 B base) i ⟨j.val,by have := j.isLt; omega⟩=o.val ∧
        oldH6 B base i=true ∧ WonAt hp old birth i j ∧ Continuous hp born i j suffix ∧
        v.incidence=j ∧ v.selector=BStarLongPublication.readSel (old i).long ∧
        v.headers=headerBits (old i).long ∧
        (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
          (v.selector.val,v.headers.toNat) ∧
        BeforePublication hp born center suffix := by
  obtain ⟨ackLead,mid,late,hold,ack,pick,op0,W,AG,AE,A6,al,ar,M,_,live,L,_,P,_,_,_,tape,band,foreign⟩ := A
  subst late
  let root := (S.getD 0 fall).1
  let ready := at_start hp G
  refine ⟨ackLead,ack,⟨_,W⟩,?_⟩
  intro j
  obtain ⟨pre,birth,post,i,v,V,owned,H,won,inc,sel,heads,fields,pcs,safe⟩ :=
    consume_six_owned_window hp C sep j AG AE A6
  let born := step (run x pre) birth
  let cutpre := pre++[birth]
  let middle := post++ack::(al++(ar++pick::hold))
  have beforeAck : run born post=run x ackLead := by
    exact (BStarResetSchedule.run_append step x pre (birth::post)).symm.trans
      (congrArg (run x) V.symm)
  have old5 : pc (run born post) root=5 := by
    have Q := pcs (birth::post) ack [] rfl
    exact Q
  have join : w=cutpre++middle := by
    rw [W,V,M]
    simp only [cutpre,middle,List.append_assoc,List.cons_append,List.nil_append]
  have bornEq : run x cutpre=born := by
    rw [BStarResetSchedule.run_append]
    rfl
  have safePost : SafePC hp root born post := by
    intro u e t E
    apply safe u e (t++[ack])
    rw [E,List.append_assoc,List.cons_append]
  have Haccept : step (run born post) ack=step (run x ackLead) ack :=
    congrArg (fun z : X => step z ack) beforeAck
  let addr := fun j => S.getD j fall
  have inputs (y : X) (E : y=step (run x ackLead) ack) :
      BStarGeneratedBandScan.LiveWord hp root y al ∧ PreBand hp (run y al) root ar ∧
      GeneratedOwner hp base addr len (step (run (run y al) ar) pick) .idle hold .idle ∧
      TailBand hp (step (run (run y al) ar) pick) root hold := by
    subst y
    exact ⟨live,P,tape,band⟩
  obtain ⟨l1,l2,l3,l4⟩ := inputs _ Haccept
  have prior : PreIssue hp root born middle :=
    @prelude k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base born addr len post al ar hold ack pick
      safePost old5 l1 l2 l3 l4 foreign
  have B0 : PreIssue hp root (run x cutpre) middle := by
    rw [bornEq]
    exact prior
  have use (ws : List (Fin n)) (E : ws=w) :
      Launch (run x ws root).long (step (run x ws) door root).long ∧ pc (run x ws) root=411 ∧
      BusyOnly hp base addr len commitOp (step (run x ws) door) (.out 0) flight (.out k) := by
    subst ws
    exact ⟨launch,op,F⟩
  obtain ⟨l5,l6,l7⟩ := use _ join.symm
  have SS := @safe_to_commit k₁ k₂ t₂ J₁ J₂ r c p c₁ n hp base x hh o S len fall
    C Q I fiber closed sep ready cutpre middle flight door center k K loc centerOwner B0 l5 l6 l7
  let suffix := middle++door::flight
  have localS : ReleaseFree hp root born suffix ∧ BeforePublication hp born center suffix :=
    by simpa only [bornEq] using SS
  have hdr (y : X) (Hy : Q y) : (longGeometry B (y i)).axes.h6=true := by
    have same := congrArg Prod.fst (fiber y Hy i)
    exact same.symm.trans H
  have stay : Continuous hp born i j suffix := by
    apply continuous hp C sep pre birth i j suffix owned won
    intro a e z E
    let trace := pre++birth::a
    have xeq : run x trace=run born a := BStarResetSchedule.run_append step x pre (birth::a)
    obtain ⟨m,Tr,Q0,Now⟩ := generated_word hp C Q fiber (fun y J d => closed y d J) sep trace .idle I ready
    refine ⟨m,Tr,Now,?_,hdr _ Q0⟩
    exact xeq.symm ▸ localS.1 a e z E
  refine ⟨pre,post,suffix,birth,i,v,V,?_,owned,H,won,stay,inc,sel,heads,fields,localS.2⟩
  rw [join]
  simp only [cutpre,suffix,List.append_assoc,List.cons_append,List.nil_append]


open BStarCommitOperands BStarCopyRightAttemptAuthenticated BStarCopyRightStrip
open BStarCopyRightRetained BStarClearanceDataChart BStarH6Ordinal BStarCustodyCuts
open BStarCopyRightFence BStarCopyRightFenceHold BStarCopyRightMixed BStarCopyRightReleaseCapture
open BStarCopyFenceSaturation BStarLongPackets

/-- Build the continuous port-2 acquisition inside the supplied
actual attempt witness. The longer COMMIT flight proves custody
using its genuine selected winning mark. We then truncate the life
predicate at the exact pre-ISSUE411 prefix, retaining the same mark. -/
theorem selected_right_acquisition {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop) (I : Q origin)
    (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w flight : List (Fin n)) (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (centerOwner : commandOwner (oldH6 B base) center 1=o.val)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w .idle)
    (A : AttemptPrefix hp base origin (fun j=>S.getD j fall) len w)
    (launch : Launch (run origin w (S.getD 0 fall).1).long (step (run origin w) door (S.getD 0 fall).1).long)
    (op : pc (run origin w) (S.getD 0 fall).1=411)
    (F : BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step (run origin w) door) (.out 0) flight (.out k)) :
    ∃ (ackLead : List (Fin n)) (ack : Fin n)
      (Ac : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2),
      (∃ tail,w=ackLead++ack::tail) ∧
      (∃ tail,ackLead=Ac.lead++Ac.mark::tail) ∧
      ((capturedSelector 2).read (step (run origin ackLead) ack (S.getD 0 fall).1).long).toNat=
        (BStarLongPublication.readSel ((run origin Ac.lead) (endpoint (oldH6 B base) hh o 2).1).long).val := by
  obtain ⟨ackLead,ack,⟨ackTail,T⟩,wins⟩ :=
    attempt_wins_with_cut hp C Q I fiber closed sep w flight door center k K loc centerOwner G A launch op F
  obtain ⟨pre,post,suffix,birth,i,v,Ack,Cut,owned,head,won,life,_,sel,_,fields,_⟩ := wins (2 : Fin 3)
  have siteEq : i=(endpoint (oldH6 B base) hh o 2).1 :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 2).2.2 i head owned)
  subst i
  let throughAck := post++ack::ackTail
  have short : w=pre++birth::throughAck := by
    rw [T,Ack]
    simp only [throughAck,List.append_assoc,List.cons_append]
  have extend : suffix=throughAck++door::flight := by
    have eq : pre++birth::suffix=pre++birth::(throughAck++door::flight) := by
      rw [←Cut,short,List.append_assoc,List.cons_append]
    exact (List.cons.inj (List.append_cancel_left eq)).2
  have shortLife : Continuous hp (step (run origin pre) birth)
      (endpoint (oldH6 B base) hh o 2).1 2 throughAck := by
    intro a b E
    exact life a (b++door::flight) (by rw [extend,E,List.append_assoc])
  let Ac := Acquisition.reader hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2
    (by decide) pre birth throughAck short (Nat.zero_le _) won shortLife
  have cap := (congrArg Prod.fst fields).trans (congrArg Fin.val sel)
  exact ⟨ackLead,ack,Ac,⟨ackTail,T⟩,⟨post,Ack⟩,cap⟩

/-- Right retained readout from the *same* supplied witness of
actual_attempt. No acquisition, matching selector, post-ACK band,
or body write/read authority is supplied by this interface. -/
theorem packed_right_from_actual_witness {base global : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q global) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    {u v tail pre reset w flight : List (Fin n)}
    (facts : CutFacts hp base global u v)
    (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (ownCenter : commandOwner (oldH6 B base) center 1=o.val)
    (ancestry : (u++v)++tail=(pre++reset)++w++door::flight)
    (below : u.length≤pre.length)
    (root a : Fin n) (seam last : Nat)
    (dest : Dest B base root r) (strip : Strip B base a seam last)
    (join : addr a 0=addr root (r-1))
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : last+1=seam+r) (rootAt : root=(S.getD len fall).1)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    let origin := run global (pre++reset)
    let slot := fun j=>S.getD j fall
    GeneratedOwner hp base slot len origin .idle w .idle →
    AttemptPrefix hp base origin slot len w →
    Launch (run origin w (slot 0).1).long (step (run origin w) door (slot 0).1).long →
    pc (run origin w) (slot 0).1=411 →
    BusyOnly hp base slot len commitOp (step (run origin w) door) (.out 0) flight (.out k) →
    ∃ (Ac : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2)
      (before after : List (Fin n)),
      w=before++after ∧
      (∃ preAck e,before=preAck++[e] ∧ Hit hp base slot len (run origin preAck) e 11) ∧
     
      BStarCopySetupFinalCut.Floor hp (slot 0).1 (run origin before) after ∧
      pc (run origin before) (slot 0).1=12 ∧
      (∀ i sh,Region root a r seam last i sh →
        (readLane (Sheet.index sh) (run origin before i).long).mobile=.empty) ∧
      laneRead (rdRead (run origin before) root r) 0 r=
        (planOf (fun i=>i-seam) seam last).reverse.map
          (Digit9.data ∘ digitTable (run origin Ac.lead) (endpoint (oldH6 B base) hh o 2).1 a seam) := by
  intro origin slot G A launch op Busy
  have keep (x : X) (w : List (Fin n)) (J : Q x) : Q (run x w) := by
    induction w generalizing x with
    | nil => exact J
    | cons e w ih => exact ih _ (closed x e J)
  have originOK : Q origin := keep global (pre++reset) I
  obtain ⟨_,_,Ac,_,_,_⟩ := selected_right_acquisition hp C Q originOK fiber closed sep
    w flight door center k K loc ownCenter G A launch op Busy
  have W : (u++v)++tail=(pre++reset)++(w++door::flight) :=
    ancestry.trans (List.append_assoc _ _ _)
  obtain ⟨before,after,eq,hit,floor,pc12,mobile,read⟩ :=
    packed_right_of_attempt_authenticated hp C sep Q originOK fiber closed A Ac ⟨w,rfl⟩
      facts rfl W below root a seam last dest strip join ownHead width rootAt inside notShort
  exact ⟨Ac,before,after,eq,hit,floor,pc12,mobile,read⟩

#print axioms selected_right_acquisition
#print axioms packed_right_from_actual_witness
end L4.BStarCopyRightActualWitness
