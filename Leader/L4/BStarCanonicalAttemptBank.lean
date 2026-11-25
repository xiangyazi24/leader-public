import Leader.L4.BStarOperandBank
import Leader.L4.BStarCopyIncidenceAuthority
import Leader.L4.BStarAttemptSafety
import Leader.L4.BStarPostCutAttempt
import Leader.L4.BStarOwnedGrantLife
import Leader.L4.BStarAcquireAckWindow

namespace L4.BStarCanonicalAttemptBank
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarLongDoor BStarLongCommand
open BStarClearanceSource BStarOwnerLaunchOrigin BStarSeparatingRail BStarLongLayout
open BStarAcquireAckWindow BStarGrantBirth BStarGrantWriterHistory
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
theorem wins_from_chosen_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w flight : List (Fin n)) (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (centerOwner : commandOwner (oldH6 B base) center 1=o.val)
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (ackLead ackTail : List (Fin n)) (ack : Fin n)
    (W : w=ackLead++ack::ackTail)
    (AG : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle ackLead (.busy acquire (.back 0)))
    (AE : Event hp (fun j=>S.getD j fall) len (run x ackLead) ack (.busy acquire (.back 0)) .idle)
    (A6 : pc (step (run x ackLead) ack) (S.getD 0 fall).1=6)
    (P : PreIssue hp (S.getD 0 fall).1 (step (run x ackLead) ack) ackTail)
    (launch : Launch (run x w (S.getD 0 fall).1).long (step (run x w) door (S.getD 0 fall).1).long)
    (op : pc (run x w) (S.getD 0 fall).1=411)
    (F : BusyOnly hp base (fun j => S.getD j fall) len commitOp
      (step (run x w) door) (.out 0) flight (.out k)) :
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
  let root := (S.getD 0 fall).1
  let ready := at_start hp G
  intro j
  obtain ⟨pre,birth,post,i,v,V,owned,H,won,inc,sel,heads,fields,pcs,safe⟩ :=
    consume_six_owned_window hp C sep j AG AE A6
  let born := step (run x pre) birth
  let cutpre := pre++[birth]
  let middle := post++ack::ackTail
  have beforeAck : run born post=run x ackLead := by
    exact (BStarResetSchedule.run_append step x pre (birth::post)).symm.trans
      (congrArg (run x) V.symm)
  have old5 : pc (run born post) root=5 := by
    have Q := pcs (birth::post) ack [] rfl
    exact Q
  have join : w=cutpre++middle := by
    rw [W,V]
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
  have prior : PreIssue hp root born middle := by
    refine pre_append hp root born post (ack::ackTail) (pre_safe hp root born post safePost) ?_
    change PreIssue hp root (run born post) ([ack]++ackTail)
    refine pre_append hp root (run born post) [ack] ackTail (pre_single hp _ _ _ ?_) ?_
    · rw [old5]
      exact ⟨by decide,.inr (by decide)⟩
    change PreIssue hp root (step (run born post) ack) ackTail
    rw [Haccept]
    exact P
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

open BStarCustodyCuts BStarCommitOperands BStarCutOperandReadout BStarOperandBank BStarOperandSites
open BStarH6Ordinal L4.Compiler.Native

theorem from_chosen_ack {base x : X} (u v tail : List (Fin n))
    (facts : CutFacts hp base x u v) (hh : ∃ i,oldH6 B base i=true)
    (noShort : ∀ z,oldH6 B base (rightNeighbor z)=true → r≤ordinal (oldH6 B base) hh z+1)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (pre reset lead flight : List (Fin n)) (door center : Fin n)
    (k : Nat) (K : k≤len)
    (W : (u++v)++tail=(pre++reset)++lead++door::flight)
    (early : u.length≤pre.length)
    (own : commandOwner (oldH6 B base) center 1=o.val)
    (loc : S.getD k fall=(center,1))
    (centerHeader : oldH6 B (run x ((u++v)++tail)) center=true)
    (leadA ackTail : List (Fin n)) (ack : Fin n)
    (WA : lead=leadA++ack::ackTail) :
    let origin := run x (pre++reset)
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let entry := step (run origin leadA) ack
    let issue := run origin lead
    GeneratedOwner hp base addr len origin .idle lead .idle →
    GeneratedOwner hp base addr len origin .idle leadA (.busy acquire (.back 0)) →
    Event hp addr len (run origin leadA) ack (.busy acquire (.back 0)) .idle →
    pc entry root=6 →
    PreIssue hp root entry ackTail →
    Launch (issue root).long (step issue door root).long →
    pc issue root=411 →
    BusyOnly hp base addr len commitOp (step issue door) (.out 0) flight (.out k) →
    let header := fun j : Fin 3 => (endpoint (oldH6 B base) hh o
      ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
    let bank : Bank := bankAt (r:=r) (run x ((u++v)++tail)) header
    let src := (step (run x ((pre++reset)++leadA)) ack root).long
    ∀ j : Fin 3, ∃ (i : Fin n) (visit : Visit)
          (A : Acquisition hp x u (u++(v++tail)) i j),
        i=header j ∧ (j=1 → i=center) ∧
        (∃ remainder, (pre++reset)++leadA=A.lead++A.mark::remainder) ∧
        visit.incidence=j ∧
        visit.selector=BStarLongPublication.readSel ((run x A.lead) i).long ∧
        visit.headers=headerBits ((run x A.lead) i).long ∧
        (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
           (visit.selector.val,visit.headers.toNat) ∧
        (∀ sites : Fin r → Fin n, WordSites (oldH6 B base) i sites →
          OperandAt (run x ((u++v)++tail)) i sites=OperandAt (run x A.lead) i sites) ∧
        bank.digits j=(bankAt (r:=r) (run x A.lead) header).digits j ∧
        ∀ f : Fin 9, (bank.hdr j f).toNat=((capturedHeader j f).read src).toNat := by
  dsimp only
  intro G AG AE A6 P launch pc411 F
  let cut := pre++reset
  let origin := run x cut
  let root := (S.getD 0 fall).1
  let whole := (u++v)++tail
  let hdr := fun j : Fin 3 => (endpoint (oldH6 B base) hh o
    ⟨j.val,Nat.lt_trans j.isLt (by decide : 3<11)⟩).1
  let src := (step (run x (cut++leadA)) ack root).long
  have keep (z : X) (w : List (Fin n)) (J : Q z) : Q (run z w) := by
    induction w generalizing z with
    | nil => exact J
    | cons e w ih => exact ih _ (closed z e J)
  have same (w : List (Fin n)) : oldH6 B (run x w)=oldH6 B base :=
    funext (fun i => (congrArg Prod.fst (fiber _ (keep x w I) i)).symm)
  have hc : oldH6 B base center=true := by
    rw [←same whole]
    exact centerHeader
  have all := wins_from_chosen_ack hp C Q (keep x cut I) fiber closed sep lead flight
    door center k K loc own G leadA ackTail ack WA AG AE A6 P launch pc411 F
  intro j
  obtain ⟨a,b0,suffix,birth,i,visit,matchA,matchC,owned,head,won,live,inc,vs,vh,fields,before⟩ := all j
  let atBirth := cut++a
  have orig (w : List (Fin n)) : run x (cut++w)=run origin w :=
    BStarResetSchedule.run_append step x cut w
  have centerEq : j=1 → i=center := by
    intro E
    have owns : commandOwner (oldH6 B base) i 1=o.val := by
      rw [E] at owned
      exact owned
    have H := (endpoint_spec (oldH6 B base) hh o 1).2.2
    exact congrArg Prod.fst ((H i head owns).trans (H center hc own).symm)
  have split : u++(v++tail)=atBirth++birth::suffix := by
    calc
      u++(v++tail) = (u++v)++tail := (List.append_assoc _ _ _).symm
      _ = cut++(lead++door::flight) := by simpa only [cut,List.append_assoc] using W
      _ = cut++(a++birth::suffix) := congrArg (cut++·) matchC
      _ = atBirth++birth::suffix := (List.append_assoc _ _ _).symm
  have later : u.length≤atBirth.length := by
    simp only [atBirth,cut,List.length_append]
    omega
  have held : Continuous hp (step (run x atBirth) birth) i j suffix :=
    (orig a).symm ▸ live
  have prior : j=1 → BeforePublication hp (step (run x atBirth) birth) i suffix := by
    intro eq
    have siteEq := centerEq eq
    exact siteEq.symm ▸ ((orig a).symm ▸ before)
  let acq : Acquisition hp x u (u++(v++tail)) i j :=
    ⟨atBirth,birth,suffix,split,later,(orig a).symm ▸ won,held,prior⟩
  have atSlot : i=hdr j :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o _).2.2 i head owned)
  have vsel : visit.selector=BStarLongPublication.readSel ((run x atBirth) i).long :=
    (orig a).symm ▸ vs
  have vhdr : visit.headers=headerBits ((run x atBirth) i).long :=
    (orig a).symm ▸ vh
  have install : (((capturedSelector j).read src).toNat,((headerBlock j).read src).toNat) =
           (visit.selector.val,visit.headers.toNat) := by
    dsimp only [src]
    rw [orig leadA]
    exact fields
  have operand (sites : Fin r→Fin n) (H : WordSites (oldH6 B base) i sites) :
      OperandAt (run x ((u++v)++tail)) i sites=OperandAt (run x atBirth) i sites := by
    have E := operand_at_acquire hp base x u (v++tail) i j sites acq sep
      (fun w => same (u++w)) (fun w e z => facts.body w e z i head) H
    simpa only [List.append_assoc] using E
  have canonical : OperandAt (run x whole) (hdr j) (sites (r:=r) (hdr j))=
      OperandAt (run x atBirth) (hdr j) (sites (r:=r) (hdr j)) := by
    rw [←atSlot]
    exact operand _ (exact_sites hh i head noShort).2.2
  refine ⟨i,visit,acq,atSlot,centerEq,⟨b0,?_⟩,inc,vsel,vhdr,install,operand,
    digit_agree hdr j canonical,?_⟩
  · change cut++leadA=atBirth++birth::b0
    rw [matchA]
    simp only [atBirth,List.append_assoc]
  · intro f
    have eq : (headerBlock j).read src=headerBits ((run x atBirth) i).long :=
      BitVec.eq_of_toNat_eq ((congrArg Prod.snd install).trans (congrArg BitVec.toNat vhdr))
    change ((headerBits ((run x whole) (hdr j)).long).getLsbD (8-f.val)).toNat=
      ((capturedHeader j f).read src).toNat
    let digit := fun w : BitVec 9 => (w.getLsbD (8-f.val)).toNat
    exact (congrArg digit (header_agree hdr j canonical)).trans
      ((congrArg digit ((congrArg (fun j : Fin n => headerBits (run x atBirth j).long) atSlot.symm).trans eq.symm)).trans
        (BStarCapturedCompilerInputs.header_bit src j f).symm)

end L4.BStarCanonicalAttemptBank
