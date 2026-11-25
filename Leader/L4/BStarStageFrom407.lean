import Leader.L4.BStarExactStageFlight
import Leader.L4.BStarPostCutAttempt

namespace L4.BStarStageFrom407
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

open BStarExactStageFlight BStarStagePast

theorem skeleton_from408 {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (T : GeneratedOwner hp base addr len x .idle w .idle)
    (K0 : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (band : TailBand hp x (addr 0).1 w)
    (first : pc x (addr 0).1=408) (late : pc (run x w) (addr 0).1=411)
    (leaf : TerminalHealth hp base addr len) :
    ∃ (lead back mid hold : List (Fin n)) (turn ack pick : Fin n) (op : Nat)
      (pay : Payload),
      w=lead++turn::(back++ack::(mid++pick::hold)) ∧
      let atTurn := run x lead
      let atAck := run (step atTurn turn) back
      let atMid := step atAck ack
      let atPick := run atMid mid
      let ready := step atPick pick
      Found hp base addr len stageOp x lead (.out len) ∧
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
  have start : pc x (addr 0).1<411 := by rw [first]; decide
  obtain ⟨before,pick,hold,op,split0,_,pre,IP,pickEv,ready411,Hr⟩ :=
    first_411 hp K0 sep T band start late
  obtain ⟨m,P,_⟩ := BStarGeneratedTapeCuts.split hp before (pick::hold) (split0 ▸ T)
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
  have high : 409≤pc (run x before) (addr 0).1 := by
    have H := (pre before [] (List.append_nil _).symm).1
    obtain ⟨_,f,F,G,O,N,_,_,last⟩ := BStarCommitGeneratedTail.consume_tail hp K0 H (sep pick) IP pickEv
      (.inr (.inr ready411))
    have cur : pc (run x before) (addr 0).1=op := IP.1.2.2.2
    rcases last ready411 with a|a <;> omega
  obtain ⟨lead,turn,back,ack,mid,f,split,found,turnEv,ret,ackEv,reply,fok,at409,midTrace,postBand⟩ :=
    stage_tour hp P K0 sep pre first high
  have atPickEq : run x before=run (step (run (step (run x lead) turn) back) ack) mid := by
    rw [split,BStarResetSchedule.run_append]
    change run (step (run x lead) turn) (back++ack::mid)=_
    rw [BStarResetSchedule.run_append]; rfl
  have cur : Current hp base addr len (run x lead) (.busy stageOp (.out len)) := by
    obtain ⟨p,q,e,V,_,_,_,Busy⟩ := found
    rw [V,BStarResetSchedule.run_append]
    change Current hp base addr len (run (step (run x p) e) q) (.busy stageOp (.out len))
    exact BStarAcquireHistoryReturn.busy_end hp Busy
  obtain ⟨pay,D,S⟩ := leaf (run x lead) turn back f cur turnEv ret reply fok
  refine ⟨lead,back,mid,hold,turn,ack,pick,op,pay,?_,found,D,S,turnEv,ret,ackEv,at409,midTrace,postBand,
    atPickEq ▸ pickEv,atPickEq ▸ ready411,atPickEq ▸ Hr,?_,?_⟩
  · rw [split0,split]
    simp only [List.append_assoc,List.cons_append]
  · have H : TailBand hp (step (run x before) pick) (addr 0).1 hold := by
      intro u v E
      have U : w=(before++pick::u)++v := by rw [split0,E]; simp only [List.append_assoc,List.cons_append]
      have B0 := band (before++pick::u) v U
      rw [BStarResetSchedule.run_append] at B0
      exact B0
    exact atPickEq ▸ H
  · have H : TailBand hp (step (run x before) pick) (addr 0).1 hold := by
      intro u v E
      have U : w=(before++pick::u)++v := by rw [split0,E]; simp only [List.append_assoc,List.cons_append]
      have B0 := band (before++pick::u) v U
      rw [BStarResetSchedule.run_append] at B0
      exact B0
    exact ready_411_foreign hp K0 sep Hr H rfl rfl ready411


/-- The successful selected STAGE at any actual forward K1 occurs
strictly in the literal tail after the chosen final native receipt.
Each premark before it still sees root PC at least 408. -/
theorem selected_from408 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (hk : k<len) (idx : S.getD k fall=(i,1))
    (K0 : (S.getD 0 fall).2=0) {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (band : TailBand hp x (S.getD 0 fall).1 w)
    (first : pc x (S.getD 0 fall).1=408)
    (late : pc (run x w) (S.getD 0 fall).1=411)
    (leaf : TerminalHealth hp base (fun j=>S.getD j fall) len) :
    ∃ before after K pay, w=before++i::after ∧
      (∀ a e b,before=a++e::b → 408≤pc (run x a) (S.getD 0 fall).1) ∧
      let old := run x before
      let raw := ((old i).long,(old (rightNeighbor i)).long)
      (K,.advance pay)∈actualOffers (oldPair B old i) raw ∧ K.source=L 1 ∧ Stage pay := by
  let addr := fun j=>S.getD j fall
  obtain ⟨lead,back,mid,hold,turn,ack,pick,op,pay,W,found,H,healthy,
      turnEv,ret,ackEv,PC,midTrace,mb,pickEv,ready411,holdTrace,tailBand,foreign⟩ :=
    skeleton_from408 hp T K0 sep band first late leaf
  obtain ⟨start,out,launch,V,loc,L,issue408,Out⟩ := found
  let active := step (run x start) launch
  have toTurn : run x lead=run active out := by rw [V,BStarResetSchedule.run_append]; rfl
  have H' : project addr (run active out) len=.forward pay := toTurn ▸ H
  obtain ⟨pre,e,post,E,preOut,stageEv,postOut,K,a,q,selected,_,srcAddr,dstAddr,StageQ,_⟩ :=
    find_stage_departure hp chart sep Out k pay healthy 0 len rfl rfl (Nat.zero_le _) hk (Nat.le_refl _) H'
  let src := run active pre
  have k1 : K.source.occurrence.val=1 :=
    (congrArg (fun p : Pos n => p.2.val) (srcAddr.symm.trans idx))
  obtain ⟨fromLeft,which⟩ := departure_trail hp src e (sep e) K q selected k1
  have exactSite : e=i := by
    rw [fromLeft] at srcAddr
    exact congrArg Prod.fst (srcAddr.symm.trans idx)
  subst e
  let before := (start++[launch])++pre
  let after := post++turn::(back++ack::(mid++pick::hold))
  have splitMain : w=before++i::after := by
    rw [W,V,E]
    simp only [before,after,List.append_assoc,List.cons_append,List.nil_append]
  have replay : run x before=src := by
    simp only [before,BStarResetSchedule.run_append]; rfl
  refine ⟨before,after,K,q,splitMain,?_,?_,fromLeft,StageQ⟩
  · intro a e b E
    exact (band a (e::(b++i::after)) (by rw [splitMain,E]; simp only [List.append_assoc,List.cons_append])).2.1
  · exact replay.symm ▸ selected

#print axioms selected_from408
end L4.BStarStageFrom407
