import Leader.L4.BStarNativeSetupStage
import Leader.L4.BStarNativeLoadData
import Leader.L4.BStarNativeInputAccepted
import Leader.L4.BStarCopyCenterActualWitness
import Leader.L4.BStarNativeSetupTape
import Leader.L4.BStarNativeInputAssembly
import Leader.L4.BStarCopyBothAtIssue12
import Leader.L4.BStarCopyCenterChosenAck

namespace L4.BStarNativeActualLoadAccepted
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand BStarLongLayout
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarCustodyCuts BStarPublicationBirth BStarGrantWriterHistory
open BStarPostCutAttempt BStarGeneratedBandScan BStarCommitOperands BStarLongPackets BStarLongArithmetic
open BStarCopyFenceSaturation BStarNativeReceiptTape BStarGeneratedOwner BStarNativeSetupTape
open BStarNativeLoadTours BStarNativeInputAssembly BStarNativeInputAccepted BStarNativeCopyTransport
open BStarCopyLeftActualWitness BStarCopyCenterActualWitness BStarCopyCenterChosenAck
open BStarCopyRightStrip (addr rail)
open BStarCopyRightRetained (Dest)
open BStarCopyLeftPending (pending)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)
open BStarCopyRightMixed (planOf)
open BStarCopyFenceCuts BStarNativeCompilerEntry BStarLongPublication
open L4.Compiler.Digits
open L4.Compiler.Native (Bank)
open BStarNativeLoadBankWords
open BStarOperandBank (bankAt)
open BStarGrantBirth (Continuous)
open BStarOwnerLaunchOrigin BStarSeparatingRail BStarLongEvents BStarLongDoor BStarCommitIssue
open BStarCommitTailScan (TailBand)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem append_gen {base x : X} {slot : Nat→Pos n} {len : Nat}
    {a b z : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base slot len x a u b)
    (Q : GeneratedOwner hp base slot len (play x u) b v z) :
    GeneratedOwner hp base slot len x a (u++v) z := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem run_mark (x : X) (w : List (Fin n)) (e : Fin n) (v : List (Fin n)) :
    play x (w++e::v)=play (step (play x w) e) v := by rw [BStarResetSchedule.run_append]; rfl

private theorem live_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {a b : Mode}
    (G : GeneratedOwner hp base (fun i=>S.getD i fall) len x a w b)
    (V : LiveAt hp chart x w) :
    LiveWord hp (S.getD 0 fall).1 x w := by
  intro u e v W
  obtain ⟨mid,_,T⟩ := BStarGeneratedTapeCuts.split hp u (e::v) (W ▸ G)
  have O := V u (e::v) W
  have New := V (u++[e]) v (by rw [W,List.append_assoc]; rfl)
  have Post : Band (step (play x u) e) (S.getD 0 fall).1 := by
    rw [BStarResetSchedule.run_append] at New
    exact New.2
  cases T with
  | next I E R =>
    rcases reflect hp chart O.1 sep e _ _ I (BStarGeneratedTapeCuts.at_start hp R) E Post with H|H
    · exact H
    · obtain ⟨_,_,mode,_,_,_,_,_⟩ := H
      rw [mode] at I
      have eq : pc (play x u) (S.getD 0 fall).1=5 := I.1.2.2.2
      have lo := O.2.1
      omega

/-- Metadata of the same actual attempt, preserved beyond the last
accepted native compiler receipt through its stopping publication. -/
structure CommitHandoff (base old x408 : X) (slot : Nat→Pos n) (len : Nat)
    (remainder rest : List (Fin n)) (mark center : Fin n) where
  hit408 : pc x408 (slot 0).1=408
  tail : GeneratedOwner hp base slot len x408 .idle remainder .idle
  band : TailBand hp x408 (slot 0).1 remainder
  issue411 : pc (play x408 remainder) (slot 0).1=411
  door : Fin n
  flight : List (Fin n)
  cursor : Nat
  split : rest=door::flight
  cursor_le : cursor≤len
  atCenter : slot cursor=(center,1)
  centerH6 : oldH6 B base center=true
  launch : Event hp slot len (play x408 remainder) door .idle (.busy commitOp (.out 0))
  fly : BusyOnly hp base slot len commitOp (step (play x408 remainder) door) (.out 0) flight (.out cursor)
  noEarlier : BeforePublication hp (step (play x408 remainder) door) center flight
  descriptor : Descriptor
  bank : Fin 3
  decoded : decode (sourceDescriptor.read (play x408 remainder (slot 0).1).long)=some descriptor
  permitted : Allows (play x408 remainder (slot 0).1).long descriptor=true
  choice : (choice.read (play x408 remainder (slot 0).1).long).toNat=bank.val
  selected :
    ∃ K payload,
      let g := oldPair B old mark
      let raw : Pair (BitVec LW) := ((old mark).long,(old (rightNeighbor mark)).long)
      (K,.advance payload)∈actualOffers g raw ∧
      LiteralCommit (geometry g K.source.side) K.source (atOld raw K.source) payload bank ∧
      decode (BStarCommitPayload.descriptorBits payload)=some descriptor

/-- The actual publication owns one original tape. Its chosen setup
provides the very ACK12 used to start the 395-receipt compiler, and
its earlier ACK11 is aligned to both COPY ledgers by the last-cut
proof, not by comparing controller PCs. Each native LOAD has the
exact captured-operand value at its genuine consume. -/
theorem before_publication {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (play initial ((u++v)++tail)) mark center)
    (hr : 0<r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n)
      (pre reset w entryWord compiler remainder rest : List (Fin n)),
      (u++v)++tail=(pre++reset)++(w++rest) ∧ w=entryWord++compiler++remainder ∧
      Chart hp base hh o S len fall ∧
      let origin := play initial (pre++reset)
      let source := (S.getD 0 fall).1
      let root := (S.getD len fall).1
      let x := play origin entryWord
      (∃ p e,entryWord=p++[e] ∧ Hit hp base (fun j=>S.getD j fall) len (play origin p) e 12) ∧
      NativeTape hp base (fun j=>S.getD j fall) len x 13 compiler 395 ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle compiler .idle ∧
      CompilerBand hp x source compiler ∧
      (∀ a i, Layout B base i=Layout B (play x a) i) ∧
      ∃ (AcL : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 0).1 0)
        (AcC : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 1).1 1)
        (AcR : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2)
        (a : Fin n) (seam : Nat),
      let left := BStarCopyLeftReleaseCapture.digitTable (play origin AcL.lead) (endpoint (oldH6 B base) hh o 0).1 source
      let right := BStarCopyRightReleaseCapture.digitTable (play origin AcR.lead) (endpoint (oldH6 B base) hh o 2).1 a seam
      let old := play origin AcC.lead
      let bank := readSel (old (endpoint (oldH6 B base) hh o 1).1).long
      let cent : Fin 9→Word r := fun f j=>
        ⟨((bankDigit bank f).read (old (addr root j.val)).long).toNat,
          ((bankDigit bank f).read (old (addr root j.val)).long).isLt⟩
      (∀ p a t,compiler=p++a::t →
        ((capturedSelector 1).read (play x p source).long).toNat=bank.val) ∧
      (let hdr := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
       let actual : Bank := bankAt (r:=r) (play initial ((u++v)++tail)) hdr
       (∀ q f, val (inputWords left right cent q f)=actual.digits q f) ∧
       (∀ p a t,compiler=p++a::t → ∀ q f,
         ((capturedHeader q f).read (play x p source).long).toNat=(actual.hdr q f).toNat)) ∧
      (∀ q f,∃ p ack t,compiler=p++ack::t ∧
        Hit hp base (fun j=>S.getD j fall) len (play x p) ack (loadOp q f) ∧
        ∀ j : Fin r,
          let d := addr root j.val
          num (play x p d).long (loadNode q f)=(inputWords left right cent q f j).val ∧
          num (step (play x p) ack d).long (loadNode q f)=(inputWords left right cent q f j).val) ∧
      (∃ p e,compiler=p++[e] ∧ Hit hp base (fun j=>S.getD j fall) len (play x p) e 407) ∧
      Nonempty (CommitHandoff hp base (play initial ((u++v)++tail)) (play x compiler)
        (fun j=>S.getD j fall) len remainder rest mark center) := by
  obtain ⟨o,S,len,fall,pre,reset,w,flight,door,k,desc,candidate,W,below,_,_,own,C,K,loc,atDoor,launch,op,decodeIssue,allow,choiceIssue,G,A,F,before,selected⟩ :=
    actual_attempt hp u v tail cuts hh sep Q I fiber closed mark center pub
  let origin := play initial (pre++reset)
  let slot := fun i=>S.getD i fall
  let source := (slot 0).1
  let root := (slot len).1
  have keep (x : X) (l : List (Fin n)) (J : Q x) : Q (play x l) := by
    induction l generalizing x with
    | nil => exact J
    | cons e l ih => exact ih _ (closed _ e J)
  have ok : Q origin := keep initial (pre++reset) I
  obtain ⟨lead,b8,b9,b10,fence,numeric,compiler,post,a5,a8,a9,a10,a11,a12,_,full,
    floor,G5,E5,pc6,preIssue,_,live,G8,_,H8,G9,_,H9,G10,_,H10,G11,H11,G12,_,H12,Gcomp,native,after,H407,Tail⟩ :=
    BStarNativeSetupStage.original_setup_stage hp C sep Q ok fiber closed A
  let entry := step (play origin lead) a5
  let x8 := step (play entry b8) a8
  let x9 := step (play x8 b9) a9
  let x10 := step (play x9 b10) a10
  let x11 := step (play x10 fence) a11
  let x12 := step (play x11 numeric) a12
  let w9 := b8++a8::b9
  let bridge := b10++a10::(fence++[a11])
  let p11 := w9++a9::bridge
  let to11 := (lead++[a5])++p11
  let to11old := (lead++[a5])++(w9++a9::(b10++a10::fence))
  let calcWord := numeric++a12::compiler
  let after11 := numeric++a12::(compiler++post)
  let to12 := to11++(numeric++[a12])
  let after5 := b8++a8::(b9++a9::(b10++a10::(fence++a11::(numeric++a12::(compiler++post)))))
  have rew11 : play entry p11=x11 := by
    dsimp only [p11,w9,bridge]
    simp only [List.append_assoc,List.cons_append]
    rw [run_mark,run_mark,run_mark,BStarResetSchedule.run_append]
    rfl
  have rew11old : play origin to11old=play x10 fence := by
    simp only [to11old,w9,List.append_assoc,List.cons_append]
    rw [run_mark]
    simp only [List.nil_append]
    rw [run_mark,run_mark,run_mark]
  have F11 : to11=to11old++[a11] := by
    simp only [to11,to11old,p11,w9,bridge,List.append_assoc,List.cons_append]
  have cut11 : w=to11++after11 := by
    simpa only [to11,p11,w9,bridge,after11,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using full
  have fold11 : play origin to11=x11 := by
    simp only [to11,List.append_assoc,List.singleton_append]
    rw [run_mark,rew11]
  have cut12 : w=to12++compiler++post := by
    simpa only [to12,after11,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using cut11
  have fold12 : play origin to12=x12 := by
    rw [show to12=to11++(numeric++[a12]) from rfl,BStarResetSchedule.run_append,fold11,
      BStarResetSchedule.run_append]
    rfl
  have top : w=lead++a5::after5 := full
  have Fold : BStarCopySetupFinalCut.Floor hp source (play origin to11) after11 := fold11.symm ▸ floor
  have Hit11 : Hit hp base slot len (play origin to11old) a11 11 := rew11old.symm ▸ H11
  have pc411 : pc (play origin w) source=411 := op
  obtain ⟨AcL,leftSeam,bl,al,leftStrip,WL,⟨pl,el,EL,HL⟩,floorL,_,drainL,readsL⟩ :=
    packed_left_from_actual_witness hp C sep Q I fiber closed cuts door center k K loc own W below
      hr flags notShort G A launch pc411 F
  obtain ⟨rightA,rightSeam,last,dest,rightStrip,join,size,ownHead⟩ :=
    BStarCopyRightWrappedGeometry.wrapped_of_chart hp C hr flags notShort
  obtain ⟨AcR,br,ar,WR,⟨pr,er,ER,HR⟩,floorR,_,drainR,readsR⟩ :=
    BStarCopyRightWrappedWitness.packed_right_from_actual_witness hp C sep Q I fiber closed cuts door center k K loc own W below
      root rightA rightSeam last dest rightStrip join ownHead size rfl (fun j=>(flags j).1) notShort G A launch pc411 F
  have TL : w=(pl++[el])++al := EL ▸ WL
  have TR : w=(pr++[er])++ar := ER ▸ WR
  have TO : w=(to11old++[a11])++after11 := F11 ▸ cut11
  obtain ⟨plEq,elEq,_⟩ := BStarCopyLastCut.unique hp source w pl to11old al after11 el a11
    TL TO HL.2.2.1 Hit11.2.2.1 (EL ▸ floorL) (F11 ▸ Fold)
  obtain ⟨prEq,erEq,_⟩ := BStarCopyLastCut.unique hp source w pr to11old ar after11 er a11
    TR TO HR.2.2.1 Hit11.2.2.1 (ER ▸ floorR) (F11 ▸ Fold)
  have leftEq : bl=to11 := by rw [EL,plEq,elEq,←F11]
  have rightEq : br=to11 := by rw [ER,prEq,erEq,←F11]
  rw [leftEq,fold11] at drainL readsL
  rw [rightEq,fold11] at drainR readsR
  obtain ⟨ss,strip,centerAddr,_,_⟩ := BStarCopyLeftStrip.of_chart hp C hr flags notShort
  have seamEq : leftSeam=ss := by
    by_cases low : leftSeam<ss
    · have bad := strip.ls_body leftSeam leftStrip.seam_pos low
      rw [leftStrip.dest_header] at bad
      contradiction
    · by_cases hi : ss<leftSeam
      · have bad := leftStrip.ls_body ss strip.seam_pos hi
        rw [strip.dest_header] at bad
        contradiction
      · omega
  have leftCenter : addr source leftSeam=root := by rw [seamEq]; exact centerAddr
  have centerHdr : oldH6 B base center=true :=
    actual_center_header hp mark center (fiber _ (keep initial _ I)) pub
  obtain ⟨AcC,⟨between,born⟩,cap⟩ :=
    selected_center_from_ack hp C Q ok fiber closed sep w flight door center k K loc centerHdr own G
      lead after5 a5 top G5 E5 pc6 preIssue launch pc411 F
  obtain ⟨rootHead,rootOwner,_⟩ := endpoint_spec (oldH6 B base) hh o 10
  rw [←C.terminal] at rootHead rootOwner
  have owner1 : commandOwner (oldH6 B base) root 1=o.val := rootOwner
  have RPair : (root, (1 : Fin 11))=endpoint (oldH6 B base) hh o 1 :=
    (endpoint_spec (oldH6 B base) hh o 1).2.2 root rootHead owner1
  have root1 : root=(endpoint (oldH6 B base) hh o 1).1 := by
    have E := congrArg (fun g : Pos n=>g.1) RPair
    exact E
  have ancestry : (u++v)++tail=(pre++reset)++(w++door::flight) :=
    W.trans (List.append_assoc _ _ _)
  have centerBody := body_of_acquisition hp cuts Q I fiber closed pre reset tail (w++door::flight)
    ancestry below w AcC notShort
  let whole := p11++calcWord
  have scope : LiveAt hp C entry whole := by
    simpa only [whole,p11,w9,bridge,calcWord,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using live
  have frontG : GeneratedOwner hp base slot len entry .idle w9 (.busy 9 (.back 0)) :=
    append_gen hp G8 (.next H8.1 H8.2.1 G9)
  have before9 : play entry w9=play x8 b9 := run_mark hp entry b8 a8 b9
  have wholeGen : GeneratedOwner hp base slot len entry .idle whole .idle := by
    have fullGen := append_gen hp G8 (.next H8.1 H8.2.1
      (append_gen hp G9 (.next H9.1 H9.2.1 (append_gen hp G10 (.next H10.1 H10.2.1
        (append_gen hp G11 (.next H11.1 H11.2.1 (append_gen hp G12 (.next H12.1 H12.2.1 Gcomp)))))))))
    simpa only [whole,p11,w9,bridge,calcWord,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using fullGen
  have at12 : play x11 (numeric++[a12])=x12 := by rw [BStarResetSchedule.run_append]; rfl
  have hold (p : List (Fin n)) (e : Fin n) (t : List (Fin n)) (E : compiler=p++e::t) (j : Fin r) :
      let d := addr root j.val
      readLane 1 (play x12 p d).long=readLane 1 (x11 d).long ∧
      readLane 3 (play x12 p d).long=readLane 3 (x11 d).long := by
    have late : 11≤pc (play entry p11) source := by
      rw [rew11]
      have E : pc x11 source=12 := H11.2.2.2.1
      rw [E]
      decide
    have Hd := both_follow_on_tape hp C sep w9 bridge calcWord a9 .idle frontG
      (before9.symm ▸ H9.2.1) (before9.symm ▸ H9.2.2.2.1) wholeGen scope
      late root source rightA leftSeam rightSeam last
      leftStrip rfl leftCenter dest rightStrip join ownHead
      (rew11.symm ▸ drainL) (rew11.symm ▸ drainR)
      ((numeric++[a12])++p) (e::t) (by simp only [calcWord,E,List.append_assoc,List.cons_append,List.nil_append]) j
    have E : play (play entry p11) ((numeric++[a12])++p)=play x12 p := by
      rw [rew11,BStarResetSchedule.run_append,at12]
    let d := addr root j.val
    change readLane 1 (play (play entry p11) ((numeric++[a12])++p) d).long=
        readLane 1 (play entry p11 d).long ∧
      readLane 3 (play (play entry p11) ((numeric++[a12])++p) d).long=
        readLane 3 (play entry p11 d).long at Hd
    rw [E,rew11] at Hd
    exact Hd
  let old := play origin AcC.lead
  let bank := readSel (old (endpoint (oldH6 B base) hh o 1).1).long
  let cent : Fin 9→Word r := fun f j=>
    ⟨((bankDigit bank f).read (old (addr root j.val)).long).toNat,
      ((bankDigit bank f).read (old (addr root j.val)).long).isLt⟩
  have sel (p : List (Fin n)) (e : Fin n) (t : List (Fin n)) (E : compiler=p++e::t) :
      ((capturedSelector 1).read (play x12 p source).long).toNat=bank.val := by
    let cp := p11++((numeric++[a12])++p)
    have exactCut : whole=cp++e::t := by
      simp only [whole,calcWord,cp,E,List.append_assoc,List.cons_append,List.nil_append]
    have L := live_word hp C sep wholeGen scope
    have pv : LiveWord hp source entry cp := by
      intro a b c U
      exact L a b (c++e::t) (by rw [exactCut,U,List.append_assoc]; rfl)
    have capHold := (BStarCapturedCompilerInputs.retain_blocks hp entry source cp sep pv 1).1
    have H := congrArg BitVec.toNat capHold
    change _=((capturedSelector 1).read (entry source).long).toNat at H
    rw [show play entry cp=play x12 p from by
      rw [show cp=p11++((numeric++[a12])++p) from rfl,BStarResetSchedule.run_append,rew11,
        BStarResetSchedule.run_append,at12]] at H
    exact H.trans cap
  have readCenter (p : List (Fin n)) (e : Fin n) (t : List (Fin n)) (E : compiler=p++e::t) (f : Fin 9) (j : Fin r) :
      digitLoad (play x12 p (addr root j.val)).long 1 f bank.val=some (cent f j).val := by
    let peekWord := p11++((numeric++[a12])++p)
    have cut : w=(lead++[a5]++peekWord)++(e::(t++post)) := by
      simpa only [peekWord,to12,to11,E,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using cut12
    have H := digit_at_numeric_prefix hp sep AcC centerBody lead peekWord (e::(t++post)) between a5 born cut j f
    have eq : play origin (lead++[a5]++peekWord)=play x12 p := by
      simp only [peekWord,List.append_assoc,List.singleton_append]
      rw [run_mark]
      rw [show p11++(numeric++a12::p)=p11++((numeric++[a12])++p) by simp [List.append_assoc]]
      rw [BStarResetSchedule.run_append,rew11,BStarResetSchedule.run_append,at12]
    rw [eq] at H
    change digitLoad (play x12 p (addr root j.val)).long 1 f bank.val=
      some (((bankDigit bank f).read (old (addr root j.val)).long).toNat)
    rw [root1]
    exact H
  let left := BStarCopyLeftReleaseCapture.digitTable (play origin AcL.lead) (endpoint (oldH6 B base) hh o 0).1 source
  let right := BStarCopyRightReleaseCapture.digitTable (play origin AcR.lead) (endpoint (oldH6 B base) hh o 2).1 rightA rightSeam
  have Lr : laneRead (ldRead x11 root) 0 r=(pending id r).reverse.map (Digit9.data ∘ left) := by
    rw [←leftCenter]
    exact readsL
  have readAt := all_accepted_from_images hp C sep native (fun j=>(flags j).1) notShort bank left right cent
    rightSeam last size Lr readsR sel hold readCenter
  have Hit12 : ∃ p e,to12=p++[e] ∧ Hit hp base slot len (play origin p) e 12 := by
    refine ⟨to11++numeric,a12,by simp only [to12,List.append_assoc],?_⟩
    rw [BStarResetSchedule.run_append,fold11]
    exact H12
  let hdr := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
  let actual : Bank := bankAt (r:=r) (play initial ((u++v)++tail)) hdr
  have actualHdr : oldH6 B (play initial ((u++v)++tail)) center=true :=
    (congrArg Prod.fst (fiber _ (keep initial _ I) center)).symm.trans centerHdr
  have canon := BStarCanonicalAttemptBank.from_chosen_ack hp u v tail cuts hh notShort sep Q I fiber closed
    C pre reset w flight door center k K (by simpa only [List.append_assoc] using ancestry) below own loc actualHdr
    lead after5 a5 top G G5 E5 pc6 preIssue launch pc411 F
  have val_at_witness (q : Fin 3) (AC : Acquisition hp origin [] w (hdr q) q) :
      ∀ f,actual.digits q f=(bankAt (r:=r) (play origin AC.lead) hdr).digits q f := by
    obtain ⟨i,visit,D,eq,_,⟨rem,prior⟩,_,_,_,_,_,dig,_⟩ := canon q
    change i=hdr q at eq
    subst i
    have Cut : (pre++reset)++w++(door::flight)=D.lead++D.mark::D.post := by
      calc
        _ = (u++v)++tail := by rw [ancestry,List.append_assoc]
        _ = u++(v++tail) := List.append_assoc _ _ _
        _ = _ := D.exactTape
    have before : D.lead.length<((pre++reset)++w).length := by
      have L := congrArg List.length prior
      have T := congrArg List.length top
      simp only [List.length_append,List.length_cons] at L T ⊢
      omega
    have replay := replay_of_same_birth hp AC Cut before D.won D.live
    change play origin AC.lead=play initial D.lead at replay
    intro f
    rw [replay]
    exact congrFun dig f
  have mainValue (q : Fin 3) (f : Fin 9) : val (inputWords left right cent q f)=actual.digits q f := by
    have hdr0 : source=hdr 0 := congrArg Prod.fst C.root
    have hdr1 : root=hdr 1 := root1
    have rightHdr : addr rightA rightSeam=hdr 2 :=
      BStarCopyRightWrappedBank.right_header hp hh o rightA rightSeam last rightStrip ownHead
    have values := BStarNativeLoadBankWords.words (r:=r) (play origin AcL.lead) old
      (play origin AcR.lead) hdr rightA rightSeam rightHdr f
    have leftE : left=BStarCopyLeftReleaseCapture.digitTable (play origin AcL.lead) (hdr 0) (hdr 0) := by
      unfold left
      rw [hdr0]
      rfl
    have centerE : cent=(fun g j=>
        ⟨((bankDigit (readSel (old (hdr 1)).long) g).read (old (addr (hdr 1) j.val)).long).toNat,
          ((bankDigit (readSel (old (hdr 1)).long) g).read (old (addr (hdr 1) j.val)).long).isLt⟩) := by
      unfold cent bank
      rw [hdr1]
      rfl
    have split : q=0 ∨ q=1 ∨ q=2 := by
      have J := q.isLt
      rcases (show q.val=0 ∨ q.val=1 ∨ q.val=2 by omega) with h|h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases split with h|h|h
    · subst q
      rw [leftE,centerE]
      exact values.1.trans (val_at_witness 0 AcL f).symm
    · subst q
      rw [leftE,centerE]
      exact values.2.1.trans (val_at_witness 1 AcC f).symm
    · subst q
      rw [leftE,centerE]
      exact values.2.2.trans (val_at_witness 2 AcR f).symm
  have capAll (p : List (Fin n)) (e : Fin n) (t : List (Fin n)) (E : compiler=p++e::t)
      (q : Fin 3) (f : Fin 9) :
      ((capturedHeader q f).read (play x12 p source).long).toNat=(actual.hdr q f).toNat := by
    let cp := p11++((numeric++[a12])++p)
    have exactCut : whole=cp++e::t := by
      simp only [whole,calcWord,cp,E,List.append_assoc,List.cons_append,List.nil_append]
    have L := live_word hp C sep wholeGen scope
    have pv : LiveWord hp source entry cp := by
      intro a b c U
      exact L a b (c++e::t) (by rw [exactCut,U,List.append_assoc]; rfl)
    have capHold := (BStarCapturedCompilerInputs.retain_blocks hp entry source cp sep pv q).2
    have H := (BStarCapturedCompilerInputs.header_bit (play entry cp source).long q f).trans
      ((congrArg (fun z : BitVec 9 => (z.getLsbD (8-f.val)).toNat) capHold).trans
        (BStarCapturedCompilerInputs.header_bit (entry source).long q f).symm)
    change _=((capturedHeader q f).read (entry source).long).toNat at H
    rw [show play entry cp=play x12 p from by
      rw [show cp=p11++((numeric++[a12])++p) from rfl,BStarResetSchedule.run_append,rew11,
        BStarResetSchedule.run_append,at12]] at H
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,header⟩ := canon q
    have h : (actual.hdr q f).toNat=
      ((capturedHeader q f).read (step (play initial ((pre++reset)++lead)) a5 source).long).toNat :=
      header.2 f
    have E5replay := BStarResetSchedule.run_append step initial (pre++reset) lead
    rw [E5replay] at h
    exact H.trans h.symm
  have stable12 (a : List (Fin n)) (i : Fin n) : Layout B base i=Layout B (play x12 a) i := by
    rw [←fold12]
    exact fiber _ (keep (play origin to12) a (keep origin to12 ok)) i
  have band12 : CompilerBand hp x12 source compiler := by
    intro p t E
    have head := (endpoint_spec (oldH6 B base) hh o 0).1
    rw [←C.root] at head
    refine ⟨(congrArg Prod.fst (stable12 p source)).symm.trans head,?_⟩
    have PC : pc x12 source=13 := H12.2.2.2.1
    exact BStarNativeLoadData.pc_window hp native PC p t E
  have issueEq : play (play x12 compiler) post=play origin w := by
    rw [←BStarResetSchedule.run_append,←fold12,←BStarResetSchedule.run_append,←List.append_assoc,←cut12]
  have x408pc : pc (play x12 compiler) source=408 := by
    obtain ⟨pre,last,E,H⟩ := H407
    rw [E,BStarResetSchedule.run_append]
    exact H.2.2.2.1
  have afterMode : _ = Mode.idle :=
    BStarGeneratedTapeCuts.idle_of_issue hp
      (BStarGeneratedTapeCuts.at_end hp after) (issueEq.symm ▸ launch.1)
  have afterIdle : GeneratedOwner hp base slot len (play x12 compiler) .idle post .idle :=
    afterMode ▸ after
  have exactLaunch : Event hp slot len (play (play x12 compiler) post) door .idle (.busy commitOp (.out 0)) := by
    rw [issueEq,←op]
    exact .launch atDoor launch
  have Handoff : CommitHandoff hp base (play initial ((u++v)++tail)) (play x12 compiler)
      slot len post (door::flight) mark center :=
    ⟨x408pc,afterIdle,Tail,issueEq.symm ▸ pc411,door,flight,k,rfl,K,loc,centerHdr,
      exactLaunch,issueEq.symm ▸ F,issueEq.symm ▸ before,desc,candidate,
      issueEq.symm ▸ decodeIssue,issueEq.symm ▸ allow,issueEq.symm ▸ choiceIssue,selected⟩
  refine ⟨o,S,len,fall,pre,reset,w,to12,compiler,post,door::flight,ancestry,cut12,C,Hit12,fold12.symm ▸ native,
    fold12.symm ▸ Gcomp,fold12.symm ▸ band12,fold12.symm ▸ stable12,
    AcL,AcC,AcR,rightA,rightSeam,?_⟩
  rw [fold12]
  exact ⟨sel,⟨mainValue,capAll⟩,readAt,H407,⟨Handoff⟩⟩

end L4.BStarNativeActualLoadAccepted
