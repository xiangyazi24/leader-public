import Leader.L4.BStarCopySetupFinalCut
import Leader.L4.BStarCopyLeftCaptureIdentity
import Leader.L4.BStarCopyIncidenceAuthority
import Leader.L4.BStarCopySetupScoped
import Leader.L4.BStarCopyRightSetupMiddle
import Leader.L4.BStarCopyLeftRecoveryFinish
import Leader.L4.BStarCopyLeftRecovered
import Leader.L4.BStarCopyLeftReleaseCursor
import Leader.L4.BStarCopyLeftReleaseCapture
import Leader.L4.BStarCopySetupReplay

namespace L4.BStarCopyLeftAttemptAuthenticated
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarClearanceSource BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarH6Ordinal
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNativeReceiptTape BStarGeneratedTapeCuts BStarAcquireHistoryReturn
open BStarCopyFenceCuts BStarCopySetupReplay BStarCopySetupScoped
open BStarCopyRightSetupFlights BStarCopyRightSetupMiddle
open BStarCopyLeftReleaseCapture BStarCopyLeftRecovered BStarCopyLeftRecoveryFinish
open BStarCopyLeftFence BStarCopyLeftRetained BStarCopyLeftMark BStarCopyLeftPending BStarCopyLeftDeposit
open BStarCopyLeftStrip
open BStarCopySetupSafe BStarCopyLeftCaptureIdentity BStarCustodyCuts
open BStarCopyRightStrip (addr)
open BStarCommitOperands BStarLongLayout BStarLongPublication BStarLongPackets BStarCopyFenceSaturation

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

private theorem append_gen {base x : X} {slot : Nat→Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base slot len x a u b)
    (Q : GeneratedOwner hp base slot len (play x u) b v c) :
    GeneratedOwner hp base slot len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem after_busy {base x : X} {slot : Nat→Pos n} {len op : Nat}
    {a b : Cursor} {w : List (Fin n)} (P : BusyOnly hp base slot len op x a w b) :
    GeneratedOwner hp base slot len x (.busy op a) w (.busy op b) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

private theorem run_cons_after (x : X) (w : List (Fin n)) (e : Fin n) (v : List (Fin n)) :
    play x (w++e::v)=play (ring (play x w) e) v := by rw [BStarResetSchedule.run_append]; rfl

/-- The whole physical left COPY readout immediately after actual
FENCE ACK11, from the same original post-cut COMMIT attempt. All
per-mark and per-source conditions are derived, and even the source
seam is recovered from the settled chart. -/
theorem packed_left_of_attempt_authenticated {base global origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q origin) (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (ring y e))
    {w cut : List (Fin n)}
    (attempt : BStarPostCutAttempt.AttemptPrefix hp base origin (fun j=>S.getD j fall) len w)
    (A : Acquisition hp origin cut w (endpoint (oldH6 B base) hh o 0).1 0)
    (common : ∃ rem,w=cut++rem)
    {u v t pre reset remaining : List (Fin n)}
    (F : CutFacts hp base global u v)
    (originEq : origin=play global (pre++reset))
    (ancestry : (u++v)++t=(pre++reset)++(w++remaining))
    (below : u.length≤pre.length)
    (hr : 0<r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    ∃ (seam : Nat) (before after : List (Fin n)),
      let a := (S.getD 0 fall).1
      Strip B base a seam r ∧
      w=before++after ∧
      (∃ preAck e,before=preAck++[e] ∧ Hit hp base (fun j=>S.getD j fall) len (play origin preAck) e 11) ∧
      BStarCopySetupFinalCut.Floor hp (S.getD 0 fall).1 (play origin before) after ∧
      pc (play origin before) (S.getD 0 fall).1=12 ∧
      (∀ i sh, BStarCopyLeftFenceHold.Region a seam r i sh →
        (readLane (Sheet.index sh) (play origin before i).long).mobile=.empty) ∧
      laneRead (ldRead (play origin before) (addr a seam)) 0 r=
        (pending id r).reverse.map
          (Digit9.data ∘ digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 0).1 a) := by
  obtain ⟨lead,b8,b9,b10,fence,num,more,ack5,ack8,ack9,ack10,ack11,ack12,mode,W,
    floor,G5,E5,pc6,safeAfter,boundedLive,G8,_,H8,G9,_,H9,G10,F10,H10,G11,H11,G12,_,_,_⟩ :=
    BStarCopySetupFinalCut.original_setup_final hp chart sep Q I fiber closed attempt
  let slot := fun j=>S.getD j fall
  let entry := ring (play origin lead) ack5
  let x8 := ring (play entry b8) ack8
  let x9 := ring (play x8 b9) ack9
  let x10 := ring (play x9 b10) ack10
  let x11 := ring (play x10 fence) ack11
  let remainder := num++ack12::more
  let body := b8++ack8::(b9++ack9::(b10++ack10::(fence++[ack11])))
  have W' : w=lead++ack5::(body++remainder) := by
    rw [W]
    simp only [body,remainder,List.append_assoc,List.cons_append,List.nil_append]
  have at12 : play entry body=x11 := by
    change play entry (b8++ack8::(b9++ack9::(b10++ack10::(fence++[ack11]))))=_
    rw [run_cons_after,run_cons_after,run_cons_after,run_cons_after]
    rfl
  have V : LiveAt hp chart entry body := by
    apply (split_live hp chart (u:=body) (v:=num++[ack12]) (x:=entry) ?_).1
    change LiveAt hp chart entry (body++(num++[ack12]))
    simpa only [body,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using boundedLive
  have stable (t : List (Fin n)) : Q (play origin t) := by
    have all (x : X) (t : List (Fin n)) (hx : Q x) : Q (play x t) := by
      induction t generalizing x with
      | nil => exact hx
      | cons e v ih => exact ih _ (closed _ e hx)
    exact all origin t I
  obtain ⟨birth,ackSel⟩ := left_ack_matches_acquisition hp chart sep Q I fiber closed A W G5 E5 pc6 safeAfter
  have auth : ∀ p e z,BStarBodyStageProvenance.BodyAuthority hp (play origin (cut++p)) e z
      (endpoint (oldH6 B base) hh o 0).1 := by
    intro p e z
    rw [originEq]
    exact BStarCopyIncidenceAuthority.all_three hp F hh o t pre reset (w++remaining) ancestry below (cut++p) e z 0
  let a := (S.getD 0 fall).1
  have root : a=(S.getD 0 fall).1 := rfl
  obtain ⟨seam,strip,_,_,_⟩ := of_chart hp chart hr flags notShort
  obtain ⟨bound,sourceFlags⟩ := BStarCopyLeftOneCapture.source_digit_chart hp chart a seam r
    strip root (fun i=>(flags i).1) notShort
  have flag : ∀ j<seam,(longGeometry B (base (addr a j))).inside=true ↔ j<r :=
    fun j J=>(sourceFlags j J).2.1
  obtain ⟨pre,out,back,issue,turn,f,F10split,issueAt,oldPC,launch,flight,raw,good,op,turnE,ret,retE,pc11⟩ :=
    flight10_of_setup hp chart sep F10 H10
  let pre9 := b8++ack8::b9
  let rest10 := pre++[issue]
  let start := pre9++ack9::rest10
  let early := ack8::(b9++ack9::pre)
  let w8 := (lead++[ack5])++b8
  let middle := early++[issue]
  let lead10 := pre9++ack9::pre
  have e8 : play origin w8=play entry b8 := by
    rw [show w8=(lead++[ack5])++b8 from rfl,BStarResetSchedule.run_append]
    have J := run_cons_after hp origin lead ack5 ([] : List (Fin n))
    rw [J]
    rfl
  have e9 : play entry pre9=play x8 b9 := run_cons_after hp entry b8 ack8 b9
  have idleBefore : GeneratedOwner hp base slot len x9 .idle pre .idle := by
    have splitEq : b10=pre++issue::(out++turn::back) :=
      F10split.trans (by simp only [List.append_assoc,List.cons_append])
    obtain ⟨m,H,_⟩ := BStarGeneratedTapeCuts.split hp pre (issue::(out++turn::back)) (splitEq ▸ G10)
    have M := idle_of_issue hp (BStarGeneratedTapeCuts.at_end hp H) launch.1
    exact M ▸ H
  have G9post : GeneratedOwner hp base slot len entry .idle pre9 (.busy 9 (.back 0)) :=
    append_gen hp G8 (.next H8.1 H8.2.1 G9)
  have G10idle : GeneratedOwner hp base slot len entry .idle lead10 .idle := by
    change GeneratedOwner hp base slot len entry .idle (pre9++ack9::pre) .idle
    apply append_gen hp G9post
    rw [e9]
    exact .next H9.1 H9.2.1 idleBefore
  have G8global : GeneratedOwner hp base slot len origin .idle w8 (.busy 8 (.back 0)) := by
    change GeneratedOwner hp base slot len origin .idle ((lead++[ack5])++b8) (.busy 8 (.back 0))
    rw [List.append_assoc]
    exact append_gen hp G5 (.next (BStarGeneratedTapeCuts.at_end hp G5) E5 G8)
  have eEarly : play (play origin w8) early=play x9 pre := by
    rw [e8]
    change play x8 (b9++ack9::pre)=_
    exact run_cons_after hp x8 b9 ack9 pre
  have Gmid : GeneratedOwner hp base slot len (play origin w8) (.busy 8 (.back 0)) early .idle := by
    rw [e8]
    change GeneratedOwner hp base slot len (play entry b8) (.busy 8 (.back 0))
      (ack8::(b9++ack9::pre)) .idle
    exact .next H8.1 H8.2.1 (append_gen hp G9 (.next H9.1 H9.2.1 idleBefore))
  have prep : start=lead10++[issue] := by
    simp only [start,rest10,lead10,List.append_assoc,List.cons_append]
  have src : w8++middle=(lead++[ack5])++start := by
    simp only [w8,middle,early,start,pre9,rest10,List.append_assoc,List.cons_append]
  have initial : play entry start=ring (play x9 pre) issue := by
    rw [prep,BStarResetSchedule.run_append]
    have E : play entry lead10=play x9 pre := by
      change play entry (pre9++ack9::pre)=_
      rw [run_cons_after,e9]
    rw [E]
    rfl
  have eqStart : play origin (w8++middle)=play entry start := by
    rw [src,List.append_assoc]
    exact run_cons_after hp origin lead ack5 start
  have T10 : BusyOnly hp base slot len 10 (play entry start) (.out 0) out (.out len) :=
    initial.symm ▸ flight
  have Ppre : BusyOnly hp base slot len 10 (play origin (w8++middle)) (.out 0) out (.out len) :=
    eqStart.symm ▸ T10
  have EGlobal : ring (play (play origin w8) early) issue=play entry start := by rw [eEarly,initial]
  have suffixBody : body= (start++out) ++ turn::(back++ack10::(fence++[ack11])) := by
    dsimp [body,start,rest10,pre9]
    rw [F10split]
    simp only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append]
  have midLive : LiveAt hp chart (play origin w8) early := by
    intro u v E
    have E' : body=(b8++u)++(v++issue::(out++turn::(back++ack10::(fence++[ack11])))) := by
      have P : start=b8++(early++[issue]) := by
        simp only [start,early,pre9,rest10,List.append_assoc,List.cons_append]
      rw [suffixBody,P,E]
      simp only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append]
    have scopeK := V (b8++u) _ E'
    rw [BStarResetSchedule.run_append] at scopeK
    rw [e8]
    exact scopeK
  have C10 : Current hp base slot len (play entry start) (.busy 10 (.out 0)) := busy_start hp T10
  have launchGlobal : Launch ((play (play origin w8) early) (slot 0).1).long
      ((ring (play (play origin w8) early) issue) (slot 0).1).long := by rw [eEarly]; exact launch
  have endEarly : pc (play (play origin w8) early) (slot 0).1=10 := by rw [eEarly]; exact oldPC
  have CG : Current hp base slot len (ring (play (play origin w8) early) issue) (.busy 10 (.out 0)) :=
    EGlobal.symm ▸ C10
  have mid := middle_from_actual_cuts hp chart sep w8 early issue G8global Gmid midLive
    endEarly issueAt launchGlobal CG
  have idlePC : pc (play entry lead10) (slot 0).1=10 := by
    change pc (play entry (pre9++ack9::pre)) (slot 0).1=10
    rw [run_cons_after,e9]
    exact oldPC
  have launchE : Event hp slot len (play entry lead10) issue .idle (.busy 10 (.out 0)) := by
    have YY : play entry lead10=play x9 pre := by
      change play entry (pre9++ack9::pre)=_
      rw [run_cons_after,e9]
    rw [YY]
    have K := Event.launch (hp:=hp) (len:=len) (addr:=slot) issueAt launch
    exact oldPC ▸ K
  have G10start : GeneratedOwner hp base slot len entry .idle start (.busy 10 (.out 0)) := by
    rw [prep]
    apply append_gen hp G10idle
    apply GeneratedOwner.next (BStarGeneratedTapeCuts.at_end hp G10idle) launchE
    apply GeneratedOwner.endpoint
    have A0 : play entry start=ring (play entry lead10) issue := by
      rw [prep,BStarResetSchedule.run_append]; rfl
    exact A0 ▸ C10
  have Gturn := append_gen hp G10start (after_busy hp T10)
  have startPC : pc entry (slot 0).1≤6 := Nat.le_of_eq pc6
  have pc5 : pc (play origin lead) (slot 0).1=5 := (BStarGeneratedTapeCuts.at_end hp G5).1.2.2.2
  have atTurn : play entry (start++out)=play (ring (play x9 pre) issue) out := by
    rw [BStarResetSchedule.run_append,initial]
  have at10 : play (ring (play entry (start++out)) turn) back=play x9 b10 := by
    rw [atTurn,F10split,BStarResetSchedule.run_append]
    rw [BStarResetSchedule.run_append]
    rfl
  have after10 : ring (play (ring (play entry (start++out)) turn) back) ack10=x10 :=
    congrArg (fun y => ring y ack10) at10
  have wholeBody : body=((((start++out)++[turn])++back)++[ack10])++(fence++[ack11]) := by
    rw [suffixBody]
    simp only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append]
  have all : GeneratedOwner hp base slot len entry .idle body .idle := by
    apply append_gen hp G8
    apply GeneratedOwner.next H8.1 H8.2.1
    apply append_gen hp G9
    apply GeneratedOwner.next H9.1 H9.2.1
    apply append_gen hp G10
    apply GeneratedOwner.next H10.1 H10.2.1
    apply append_gen hp G11
    exact .next H11.1 H11.2.1 (.endpoint (BStarGeneratedTapeCuts.at_start hp G12))
  have pc12 : pc x11 (slot 0).1=12 := H11.2.2.2.1
  let digits := digitTable (play origin A.lead) (endpoint (oldH6 B base) hh o 0).1 a
  have bw : w8=lead++ack5::b8 := by simp only [w8,List.append_assoc,List.singleton_append]
  have prefixB (u v : List (Fin n)) (E : b8=u++v) :
      let y := play origin ((lead++[ack5])++u)
      Band y (slot 0).1 ∧ (∀ i,Layout B base i=Layout B y i) := by
    have scope := V u (v++ack8::(b9++ack9::(b10++ack10::(fence++[ack11])))) (by
      simp only [body,E,List.append_assoc])
    have eq : play origin ((lead++[ack5])++u)=play entry u := by
      rw [List.append_assoc]
      exact run_cons_after hp origin lead ack5 u
    rw [eq]
    exact ⟨scope.2,scope.1⟩
  have sameWhole : ∃ suffix,w=((w8++middle)++out)++suffix := by
    refine ⟨turn::(back++ack10::(fence++ack11::remainder)),?_⟩
    rw [W',suffixBody]
    simp only [w8,middle,early,start,pre9,rest10,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append,List.nil_append]
  have cap := BStarCopyLeftReleaseCursor.all_release_bytes hp chart sep a seam r strip root bound rfl flag
    w8 middle out mid Ppre (fun q _ _=>fiber _ (stable q)) cut w A common sameWhole
    lead ack5 birth ackSel b8 bw pc5 G8 prefixB
    (fun p => funext fun i => (congrArg Prod.fst (fiber _ (stable (cut++p)) i)).symm) auth
  have capPost : ∀ u e v,out=u++e::v →
      ∀ m (R : BStarCopyLeftReleaseClass.ReleaseAt hp (play (play entry start) u) e a seam slot len m),
      (sample (play (play entry start) u) a seam R.i).frozen=.data (digits R.i) := by
    rw [←eqStart]
    exact cap
  have validOut : LiveAt hp chart entry (start++out) :=
    (split_live hp chart (suffixBody ▸ V)).1
  obtain ⟨t,lab,pend,ordered,old,mobile⟩ :=
    recovered_left_outward hp chart sep digits a seam r strip root bound flag start out lead10 issue prep
      G10idle startPC idlePC G10start T10 pre9 rest10 ack9 rfl G9post
      (e9.symm ▸ H9.2.1) (e9.symm ▸ H9.2.2.2.1) Gturn validOut
      f (initial.symm ▸ raw) good op capPost
  have turnTape : start++out=pre9++ack9::(rest10++out) := by
    simp only [start,List.append_assoc,List.cons_append]
  have finalTape : body=((pre9++ack9::((rest10++out)++turn::back++[ack10]))++(fence++[ack11])) := by
    simpa only [start,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using wholeBody
  have fin := finish_left hp digits chart sep a r seam strip root flags notShort pre9 (rest10++out) back fence
    ack9 turn ack10 ack11 G9post (e9.symm ▸ H9.2.1) (e9.symm ▸ H9.2.2.2.1)
    (turnTape ▸ Gturn) (turnTape ▸ (atTurn.symm ▸ turnE))
    (turnTape ▸ (atTurn.symm ▸ ret)) (turnTape ▸ (at10.symm ▸ H10.2.1))
    (turnTape ▸ (after10.symm ▸ BStarGeneratedTapeCuts.at_start hp G11))
    (turnTape ▸ (after10.symm ▸ H10.2.2.2.1)) (turnTape ▸ (after10.symm ▸ G11))
    (turnTape ▸ (after10.symm ▸ H11))
    (finalTape ▸ all) (fun u v E=>V u v (finalTape.trans E))
    (pending id r) t lab (by simp [pending]) pend ordered
    (turnTape ▸ (by rw [BStarResetSchedule.run_append]; exact old))
    (turnTape ▸ (by rw [BStarResetSchedule.run_append]; exact mobile))
  have wire : play origin ((lead++[ack5])++body)=play entry body := by
    rw [List.append_assoc]; exact run_cons_after hp origin lead ack5 body
  refine ⟨seam,(lead++[ack5])++body,remainder,strip,?_,?_,?_,?_,?_⟩
  · rw [W']; simp only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append]
  · let oldBody := b8++ack8::(b9++ack9::(b10++ack10::fence))
    let preAck := (lead++[ack5])++oldBody
    have beforeWord : (lead++[ack5])++body=preAck++[ack11] := by
      simp only [body,oldBody,preAck,List.append_assoc,List.cons_append]
    have old : play origin preAck=play x10 fence := by
      change play origin ((lead++[ack5])++oldBody)=_
      rw [List.append_assoc,List.singleton_append,run_cons_after]
      dsimp only [oldBody]
      rw [run_cons_after,run_cons_after,run_cons_after]
    exact ⟨preAck,ack11,beforeWord,old.symm ▸ H11⟩
  · rw [wire,at12]; exact floor
  · rw [wire,at12]; exact pc12
  · rw [wire,finalTape]
    exact fin

#print axioms packed_left_of_attempt_authenticated
end L4.BStarCopyLeftAttemptAuthenticated
