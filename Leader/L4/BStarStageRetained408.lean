import Leader.L4.BStarStageFrom407
import Leader.L4.BStarStageAuthorizedHop
import Leader.L4.BStarStageArgFrom407

namespace L4.BStarStageRetained408
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

open BStarExactStageFlight BStarStageFrom407 BStarStageThroughCommit
open BStarStagePast

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
    (startBand : TailBand hp x (S.getD 0 fall).1 w)
    (first : pc x (S.getD 0 fall).1=408) (late : pc (run x w) (S.getD 0 fall).1=411)
    (leaf : TerminalHealth hp base (fun j => S.getD j fall) len)
    (issue : Event hp (fun j => S.getD j fall) len (run x w) door .idle (.busy commitOp (.out 0)))
    (flight : BusyOnly hp base (fun j => S.getD j fall) len commitOp
      (step (run x w) door) (.out 0) fly (.out j)) :
    ∃ before rest K pay, w=before++i::rest ∧
      (∀ a e b,before=a++e::b → 408≤pc (run x a) (S.getD 0 fall).1) ∧
      GeneratedOwner hp base (fun j => S.getD j fall) len x .idle before (.busy stageOp (.out k)) ∧
      let old := run x before
      let g := oldPair B old i
      let raw := ((old i).long,(old (rightNeighbor i)).long)
      (K,.advance pay)∈actualOffers g raw ∧ K.source=L 1 ∧ Stage pay ∧
      arg pay=BStarStageIssue.argument (x (S.getD 0 fall).1).long ∧
      (∀ d, BStarLongPublication.decode (descriptorBits pay)=some d →
        oldH6 B old i=true → BStarLongOutgoing.actual raw.1 d=true) ∧
      ∀ b : Fin 3,
        let y := run (step (run x w) door) fly
        BankAt b (y i).long=BankAt b (step old i i).long ∧
        BankAt b (step y pub i).long=BankAt b (step old i i).long := by
  let addr := fun j => S.getD j fall
  obtain ⟨lead,back,mid,hold,turn,ack,pick,op,pay,W,found,H,healthy,
      turnEv,ret,ackEv,PC,midTrace,band,pickEv,ready411,holdTrace,tailBand,foreign⟩ :=
    skeleton_from408 hp T K0 sep startBand first late leaf
  have terminalArg := BStarStageArgFrom407.turned_argument hp chart sep K0 T startBand W found H healthy
  obtain ⟨start,out,launch,V,loc,L,issue408,Out⟩ := found
  let stageIssue := run x start
  let active := step stageIssue launch
  have toTurn : run x lead=run active out := by rw [V,BStarResetSchedule.run_append]; rfl
  have H' : project addr (run active out) len=.forward pay := toTurn ▸ H
  obtain ⟨pre,e,post,E,preOut,stageEv,postOut,K,a,q,selected,_,srcAddr,dstAddr,StageQ,argQ,grant⟩ :=
    BStarStageAuthorizedHop.find hp chart sep Out k pay healthy 0 len rfl rfl (Nat.zero_le _) hk (Nat.le_refl _) H'
  let src := run active pre
  have k1 : K.source.occurrence.val=1 :=
    (congrArg (fun p : Pos n => p.2.val) (srcAddr.symm.trans idx))
  have exactSite : e=i := by
    obtain ⟨h,_⟩ := departure_trail hp src e (sep e) K q selected k1
    rw [h] at srcAddr
    exact congrArg Prod.fst (srcAddr.symm.trans idx)
  subst e
  let startTape := start
  let before := (startTape++[launch])++pre
  let rest := post++turn::(back++ack::(mid++pick::hold))
  have splitStart : w=startTape++launch::(out++turn::(back++ack::(mid++pick::hold))) := by
    rw [W,V]
    simp only [startTape,List.append_assoc,List.cons_append]
  have splitMain : w=before++i::rest := by
    rw [splitStart,E]
    simp only [before,rest,List.append_assoc,List.cons_append,List.nil_append]
  have replayStart : run x startTape=stageIssue := by
    rfl
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
  have Eq : run x lead=run (step src i) post := toTurn.trans runStage
  have throughTurn : BusyOnly hp base addr len stageOp (run x lead) (.out len)
      (turn::back) (.back 0) :=
    .cons (toTurn.symm ▸ BStarAcquireHistoryReturn.busy_end hp Out) turnEv ret
  have untilAck := busy_app hp postOut (Eq ▸ throughTurn)
  let returned := run (step src i) (post++turn::back)
  have returnedEq : returned=run (step (run x lead) turn) back := by
    simp only [returned,BStarResetSchedule.run_append]; rw [Eq]; rfl
  have holdEq : run x w=
      run (step (run (step returned ack) mid) pick) hold := by
    rw [returnedEq,W,BStarResetSchedule.run_append]
    change run (step (run x lead) turn) (back++ack::(mid++pick::hold))=_
    rw [BStarResetSchedule.run_append]
    change run (step (run (step (run x lead) turn) back) ack) (mid++pick::hold)=_
    rw [BStarResetSchedule.run_append]; rfl
  have chosen : (K,.advance q)∈actualOffers (oldPair B (run x before) i)
      (((run x before) i).long,((run x before) (rightNeighbor i)).long) := replay.symm ▸ selected
  have hstage : K.source=BStarLongClaims.L 1 := (departure_trail hp src i (sep i) K q selected k1).1
  have safe (a : List (Fin n)) (e : Fin n) (b : List (Fin n))
      (E : before=a++e::b) : 408≤pc (run x a) (S.getD 0 fall).1 :=
    (startBand a (e::(b++i::rest))
      (by rw [splitMain,E]; simp only [List.append_assoc,List.cons_append])).2.1
  refine ⟨before,rest,K,q,splitMain,safe,G2,chosen,hstage,StageQ,argQ.trans terminalArg,?_,?_⟩
  · intro d hd hHeader
    change oldH6 B (run x before) i=true at hHeader
    change BStarLongOutgoing.actual ((run x before) i).long d=true
    rw [replay] at hHeader ⊢
    exact grant hstage d hd hHeader
  · intro b
    have H := bank_survives hp chart sep k j (Nat.le_of_lt hk) K0 before (post++turn::back) mid hold fly
      i ack pick door pub idx own b K q k1 (.out (k+1)) (.busy op (.back 0))
      chosen G2 (replay.symm ▸ stageEv) (replay.symm ▸ untilAck)
    have r : run (step (run x before) i) (post++turn::back)=run (step (run x lead) turn) back := by
      rw [replay]; exact returnedEq
    simp only [r] at H
    have Z : run x w=run (step (run (step (run (step (run x lead) turn) back) ack) mid) pick) hold := by
      rw [returnedEq] at holdEq
      exact holdEq
    rw [Z] at issue flight
    rw [Z]
    exact H ackEv midTrace band (Nat.le_of_eq PC.symm) pickEv ready411 holdTrace tailBand foreign issue flight
  
  
#print axioms retained_chart_site
end L4.BStarStageRetained408
