import Leader.L4.BStarStageHopExtract
import Leader.L4.BStarPostCutAttempt

namespace L4.BStarExactStageFlight
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting BStarLongCommand
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireRailCoverage BStarAcquireAnchors
open BStarStageCandidateRetention BStarBankTrace BStarStageProvenance
open BStarLongFiberOwner BStarGeneratedTapeCuts BStarCommitTailScan
open BStarStageAckExtract BStarStageHopExtract BStarClearanceSource BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

/-- Exact missing leaf for the Stage tape: a healthy acknowledged
Stage reply cannot originate from a faulty terminal forward. The
terminal state, its mark and its actual BusyOnly return are fixed. -/
def TerminalHealth (base : X) (addr : Nat → Pos n) (len : Nat) : Prop :=
  ∀ (y : X) (turn : Fin n) (back : List (Fin n)) (f : Payload),
    Current hp base addr len y (.busy stageOp (.out len)) →
    Event hp addr len y turn (.busy stageOp (.out len)) (.busy stageOp (.back len)) →
    BusyOnly hp base addr len stageOp (step y turn) (.back len) back (.back 0) →
    (let z := run (step y turn) back
     bind (longGeometry B (z (addr 0).1)) 0 (atSite (z (addr 0).1).long 0)=.reply f) →
    Stage f →
    ∃ q, project addr y len=.forward q ∧ Stage q

/-- The own STAGE and COMMIT stages have exact shared chronology on
the old ISSUE411 tape. This internal skeleton follows the last actual
407->408 entry, first 408 ACK, and first ready411 entry on that same
tape. It records the old terminal forward as the sole remaining
healthy-return implication, without assuming any bank or register
equality. -/
theorem issue411_skeleton {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (T : GeneratedOwner hp base addr len x .idle w .idle)
    (K0 : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ a b,w=a++b → oldH6 B (run x a) (addr 0).1=true)
    (early : pc x (addr 0).1<408) (late : pc (run x w) (addr 0).1=411)
    (leaf : TerminalHealth hp base addr len) :
    ∃ (entry lead back mid hold : List (Fin n)) (ent turn ack pick : Fin n) (op : Nat)
      (pay : Payload),
      w=entry++ent::(lead++turn::(back++ack::(mid++pick::hold))) ∧
      let origin := step (run x entry) ent
      let atTurn := run origin lead
      let atAck := run (step atTurn turn) back
      let atMid := step atAck ack
      let atPick := run atMid mid
      let ready := step atPick pick
      GeneratedOwner hp base addr len x .idle (entry++[ent]) .idle ∧
      Found hp base addr len stageOp origin lead (.out len) ∧
      project addr atTurn len=.forward pay ∧ Stage pay ∧
      Event hp addr len atTurn turn (.busy stageOp (.out len)) (.busy stageOp (.back len)) ∧
      BusyOnly hp base addr len stageOp (step atTurn turn) (.back len) back (.back 0) ∧
      Event hp addr len atAck ack (.busy stageOp (.back 0)) .idle ∧ pc atMid (addr 0).1=409 ∧
      GeneratedOwner hp base addr len atMid .idle mid (.busy op (.back 0)) ∧
      PreBand hp atMid (addr 0).1 mid ∧
      Event hp addr len atPick pick (.busy op (.back 0)) .idle ∧
      pc ready (addr 0).1=411 ∧
      GeneratedOwner hp base addr len ready .idle hold .idle ∧
      TailBand hp ready (addr 0).1 hold ∧ (∀ e∈hold,rightNeighbor e≠(addr 0).1) := by
  rcases last_stage_entry hp K0 sep T head late with band|⟨entry,ent,rest,W,_,_,first,T0,band⟩
  · have Q := (band [] w rfl).2.1
    change 408≤pc x (addr 0).1 at Q
    omega
  let origin := step (run x entry) ent
  have oldTape : run x w=run origin rest := by rw [W,BStarResetSchedule.run_append]; rfl
  have t : pc (run origin rest) (addr 0).1=411 := oldTape ▸ late
  have start : pc origin (addr 0).1<411 := by
    rw [show pc origin (addr 0).1=408 from first]; decide
  obtain ⟨before,pick,hold,op,split0,_,pre,IP,pickEv,ready411,Hr⟩ :=
    first_411 hp K0 sep T0 band start t
  obtain ⟨m,init,_⟩ := BStarGeneratedTapeCuts.split hp (entry++[ent]) rest
    ((show w=(entry++[ent])++rest by rw [W,List.append_assoc]; rfl) ▸ T)
  have startRun : run x (entry++[ent])=origin := by rw [BStarResetSchedule.run_append]; rfl
  have mode : m=.idle := idle_of_issue hp (at_end hp init)
    (startRun.symm ▸ (at_start hp T0).1)
  subst m
  obtain ⟨m,P,_⟩ := BStarGeneratedTapeCuts.split hp before (pick::hold) (split0 ▸ T0)
  -- The prefix at the actual selecting consume really has mode busy op/back0.
  have eq : m=.busy op (.back 0) := by
    have cm := at_end hp P
    cases m with
    | idle => exact ((by decide : (2:Nat)≠1) (IP.1.2.2.1.symm.trans cm.1.2)).elim
    | busy a j =>
      have opeq : a=op := cm.1.2.2.2.symm.trans IP.1.2.2.2
      subst a
      cases j with
      | out j =>
        exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 IP.2.1 j cm.2.1.1 cm.2.1.2.1).elim
      | back j =>
        cases j with
        | zero => rfl
        | succ j =>
          have ra := cm.2.1.2.2.1 0 (Nat.zero_lt_succ _)
          obtain ⟨q,F⟩ := IP.2.1.2.1
          exact Token.noConfusion (ra.symm.trans F)
  subst m
  have high : 409≤pc (run origin before) (addr 0).1 := by
    have H := (pre before [] (List.append_nil _).symm).1
    obtain ⟨_,f,F,G,O,N,_,_,last⟩ := BStarCommitGeneratedTail.consume_tail hp K0 H (sep pick) IP pickEv
      (.inr (.inr ready411))
    have cur : pc (run origin before) (addr 0).1=op := IP.1.2.2.2
    rcases last ready411 with a|a <;> omega
  obtain ⟨lead,turn,back,ack,mid,f,split,found,turnEv,ret,ackEv,reply,fok,at409,midTrace,postBand⟩ :=
    stage_tour hp P K0 sep pre first high
  have atPickEq : run origin before=run (step (run (step (run origin lead) turn) back) ack) mid := by
    rw [split,BStarResetSchedule.run_append]
    change run (step (run origin lead) turn) (back++ack::mid)=_
    rw [BStarResetSchedule.run_append]; rfl
  have cur : Current hp base addr len (run origin lead) (.busy stageOp (.out len)) := by
    obtain ⟨p,q,e,V,_,_,_,Busy⟩ := found
    rw [V,BStarResetSchedule.run_append]
    change Current hp base addr len (run (step (run origin p) e) q) (.busy stageOp (.out len))
    exact BStarAcquireHistoryReturn.busy_end hp Busy
  obtain ⟨pay,D,S⟩ := leaf (run origin lead) turn back f cur turnEv ret reply fok
  refine ⟨entry,lead,back,mid,hold,ent,turn,ack,pick,op,pay,?_,init,found,D,S,turnEv,ret,ackEv,at409,midTrace,postBand,
    atPickEq ▸ pickEv,atPickEq ▸ ready411,atPickEq ▸ Hr,?_,?_⟩
  · rw [W,split0,split]
    simp only [List.append_assoc,List.cons_append]
  · have H : TailBand hp (step (run origin before) pick) (addr 0).1 hold := by
      intro u v E
      have U : rest=(before++pick::u)++v := by rw [split0,E]; simp only [List.append_assoc,List.cons_append]
      have B0 := band (before++pick::u) v U
      rw [BStarResetSchedule.run_append] at B0
      exact B0
    exact atPickEq ▸ H
  · have H : TailBand hp (step (run origin before) pick) (addr 0).1 hold := by
      intro u v E
      have U : rest=(before++pick::u)++v := by rw [split0,E]; simp only [List.append_assoc,List.cons_append]
      have B0 := band (before++pick::u) v U
      rw [BStarResetSchedule.run_append] at B0
      exact B0
    exact ready_411_foreign hp K0 sep Hr H rfl rfl ready411

open BStarStageThroughCommit BStarStagePast

private theorem app {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base addr len x a u b)
    (Q : GeneratedOwner hp base addr len (run x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem busy_app {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b c : Cursor} {u v : List (Fin n)}
    (P : BusyOnly hp base addr len op x a u b)
    (Q : BusyOnly hp base addr len op (run x u) b v c) :
    BusyOnly hp base addr len op x a (u++v) c := by
  induction P with
  | nil I => exact Q
  | cons I E _ ih => exact .cons I E (ih Q)

private theorem busy_word {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {a b : Cursor} {w : List (Fin n)} (P : BusyOnly hp base addr len op x a w b) :
    GeneratedOwner hp base addr len x (.busy op a) w (.busy op b) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- For each actual chart K1, follow its own selected healthy STAGE
write on the old ISSUE411 tape and preserve each candidate's physical
bytes into and across the COMMIT mark. The argument is per site, so
it covers both the center and each IN digit without conflating their
distinct advancing marks. The only terminal-ancestry premise is
`TerminalHealth` at the real STAGE turn. -/
theorem retained_chart_site {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w fly : List (Fin n)) (door pub i : Fin n) (k j : Nat) (hk : k<len)
    (idx : S.getD k fall=(i,1)) (own : commandOwner (oldH6 B base) i 1=o.val)
    (K0 : (S.getD 0 fall).2=0)
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (head : ∀ a b,w=a++b → oldH6 B (run x a) (S.getD 0 fall).1=true)
    (early : pc x (S.getD 0 fall).1<408) (late : pc (run x w) (S.getD 0 fall).1=411)
    (leaf : TerminalHealth hp base (fun j => S.getD j fall) len)
    (issue : Event hp (fun j => S.getD j fall) len (run x w) door .idle (.busy commitOp (.out 0)))
    (flight : BusyOnly hp base (fun j => S.getD j fall) len commitOp
      (step (run x w) door) (.out 0) fly (.out j)) :
    ∃ before rest K pay, w=before++i::rest ∧
      let old := run x before
      let g := oldPair B old i
      let raw := ((old i).long,(old (rightNeighbor i)).long)
      (K,.advance pay)∈actualOffers g raw ∧ K.source=L 1 ∧ Stage pay ∧
      ∀ b : Fin 3,
        let y := run (step (run x w) door) fly
        BankAt b (y i).long=BankAt b (step old i i).long ∧
        BankAt b (step y pub i).long=BankAt b (step old i i).long := by
  let addr := fun j => S.getD j fall
  obtain ⟨entry,lead,back,mid,hold,ent,turn,ack,pick,op,pay,W,init,found,H,healthy,
      turnEv,ret,ackEv,PC,midTrace,band,pickEv,ready411,holdTrace,tailBand,foreign⟩ :=
    issue411_skeleton hp T K0 sep head early late leaf
  let origin := step (run x entry) ent
  obtain ⟨start,out,launch,V,loc,L,issue408,Out⟩ := found
  let stageIssue := run origin start
  let active := step stageIssue launch
  have toTurn : run origin lead=run active out := by rw [V,BStarResetSchedule.run_append]; rfl
  have H' : project addr (run active out) len=.forward pay := toTurn ▸ H
  obtain ⟨pre,e,post,E,preOut,stageEv,postOut,K,a,q,selected,_,srcAddr,dstAddr,StageQ,_⟩ :=
    find_stage_departure hp chart sep Out k pay healthy 0 len rfl rfl (Nat.zero_le _) hk (Nat.le_refl _) H'
  let src := run active pre
  have k1 : K.source.occurrence.val=1 :=
    (congrArg (fun p : Pos n => p.2.val) (srcAddr.symm.trans idx))
  have exactSite : e=i := by
    obtain ⟨h,_⟩ := departure_trail hp src e (sep e) K q selected k1
    rw [h] at srcAddr
    exact congrArg Prod.fst (srcAddr.symm.trans idx)
  subst e
  let startTape := (entry++[ent])++start
  let before := (startTape++[launch])++pre
  let rest := post++turn::(back++ack::(mid++pick::hold))
  have splitStart : w=startTape++launch::(out++turn::(back++ack::(mid++pick::hold))) := by
    rw [W,V]
    simp only [startTape,List.append_assoc,List.cons_append,List.nil_append]
  have splitMain : w=before++i::rest := by
    rw [splitStart,E]
    simp only [before,rest,List.append_assoc,List.cons_append,List.nil_append]
  have replayStart : run x startTape=stageIssue := by
    simp only [startTape,BStarResetSchedule.run_append]; rfl
  have replay : run x before=src := by
    simp only [before,BStarResetSchedule.run_append,replayStart]; rfl
  obtain ⟨m,G0,_⟩ := BStarGeneratedTapeCuts.split hp startTape
    (launch::(out++turn::(back++ack::(mid++pick::hold)))) (splitStart ▸ T)
  have mode : m=.idle := idle_of_issue hp (at_end hp G0) (replayStart.symm ▸ L.1)
  subst m
  have launchEv : Event hp addr len (run x startTape) launch .idle (.busy stageOp (.out 0)) := by
    rw [replayStart]
    have Z : Event hp addr len stageIssue launch .idle
        (.busy (ctrlOp.read (stageIssue (addr 0).1).long).toNat (.out 0)) := .launch loc L
    rw [issue408] at Z
    exact Z
  have G1 := app hp G0 (.next (at_end hp G0) launchEv (.endpoint (replayStart.symm ▸ busy_start hp Out)))
  have fromActive : run x (startTape++[launch])=active := by
    rw [BStarResetSchedule.run_append,replayStart]; rfl
  have lifted : GeneratedOwner hp base addr len (run x (startTape++[launch]))
      (.busy stageOp (.out 0)) pre (.busy stageOp (.out k)) := by
    rw [fromActive]; exact busy_word hp preOut
  have G2 := app hp G1 lifted
  have runStage : run active out=run (step src i) post := by rw [E,BStarResetSchedule.run_append]; rfl
  have Eq : run origin lead=run (step src i) post := toTurn.trans runStage
  have throughTurn : BusyOnly hp base addr len stageOp (run origin lead) (.out len)
      (turn::back) (.back 0) :=
    .cons (toTurn.symm ▸ BStarAcquireHistoryReturn.busy_end hp Out) turnEv ret
  have untilAck := busy_app hp postOut (Eq ▸ throughTurn)
  let returned := run (step src i) (post++turn::back)
  have returnedEq : returned=run (step (run origin lead) turn) back := by
    simp only [returned,BStarResetSchedule.run_append]; rw [Eq]; rfl
  have holdEq : run x w=
      run (step (run (step returned ack) mid) pick) hold := by
    rw [returnedEq,W,BStarResetSchedule.run_append]
    change run origin (lead++turn::(back++ack::(mid++pick::hold)))=_
    simp only [BStarResetSchedule.run_append]
    change run (step (run origin lead) turn) (back++ack::(mid++pick::hold))=_
    rw [BStarResetSchedule.run_append]
    change run (step (run (step (run origin lead) turn) back) ack) (mid++pick::hold)=_
    rw [BStarResetSchedule.run_append]; rfl
  have chosen : (K,.advance q)∈actualOffers (oldPair B (run x before) i)
      (((run x before) i).long,((run x before) (rightNeighbor i)).long) := replay.symm ▸ selected
  have hstage : K.source=BStarLongClaims.L 1 := (departure_trail hp src i (sep i) K q selected k1).1
  refine ⟨before,rest,K,q,splitMain,chosen,hstage,StageQ,?_⟩
  intro b
  have H := bank_survives hp chart sep k j (Nat.le_of_lt hk) K0 before (post++turn::back) mid hold fly
    i ack pick door pub idx own b K q k1 (.out (k+1)) (.busy op (.back 0))
    chosen G2 (replay.symm ▸ stageEv) (replay.symm ▸ untilAck)
  have r : run (step (run x before) i) (post++turn::back)=run (step (run origin lead) turn) back := by
    rw [replay]; exact returnedEq
  simp only [r] at H
  have Z : run x w=run (step (run (step (run (step (run origin lead) turn) back) ack) mid) pick) hold := by
    rw [returnedEq] at holdEq
    exact holdEq
  rw [Z] at issue flight
  rw [Z]
  exact H ackEv midTrace band (Nat.le_of_eq PC.symm) pickEv ready411 holdTrace tailBand foreign issue flight

end L4.BStarExactStageFlight
