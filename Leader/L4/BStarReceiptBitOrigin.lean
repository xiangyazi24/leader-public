import Leader.L4.BStarPhysicalPairLaw
import Leader.L4.BStarBitFlight
import Leader.L4.BStarBitOneObservation
import Leader.L4.BStarBitPhysicalSwap

namespace L4.BStarReceiptBitOrigin
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongCommand BStarLongEvents BStarResetQuiet
open BStarLongRouting BStarLongCommandData BStarClearanceForward
open BStarLongFixedRouting BStarAcquireLiteralChain BStarH6WordChart
open BStarAcquireForwardTrace BStarResetMarkAdapter BStarResetRailRing
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarBitTerminalHealth BStarBitParity BStarNumericChronology
open BStarClearanceOffset BStarBitGateGeometry BStarBitGateArrival BStarBitGateOutcome

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarAcquireHistorySample BStarOwnerControlHistory
open BStarAcquireVisitOrder BStarResetChartTouch

open BStarBitReplay BStarBitFlight BStarBitSegment BStarBitDepart BStarClearanceRaceMark BStarLongLiteral
open BStarH6Ordinal BStarFenceReceiverChart
open BStarStageProvenance BStarNativeActualLoadAccepted BStarCommitReceiptAuth

private theorem play_eq (x : X) (w : List (Fin n)) : BStarBitReplay.play hp x w=play x w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (step x e)

private theorem split_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {w : List (Fin n)} {z endC : Cursor} (T : BusyOnly hp base addr len op x z w endC) :
    ∀ u v,w=u++v → ∃ t, BusyOnly hp base addr len op x z u t ∧
      BusyOnly hp base addr len op (play x u) t v endC := by
  induction T with
  | nil I =>
    intro u v S
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp S.symm
    exact ⟨_,.nil I,.nil I⟩
  | @cons x z t endC e w I E T ih =>
    intro u v S
    cases u with
    | nil =>
      change e::w=v at S
      subst v
      exact ⟨_,.nil I,.cons I E T⟩
    | cons a u =>
      obtain ⟨rfl,P⟩ := List.cons.inj S
      obtain ⟨m,U,V⟩ := ih u v P
      exact ⟨m,.cons I E U,V⟩

theorem from_handoff {base old x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x (fun j=>S.getD j fall) len rem rest mark center)
    (need : H.descriptor.need=true) (width : 5≤r)
    (notShort : ∀ a,oldH6 B base (rightNeighbor a)=true → r≤oldOrdinal B base hh a+1)
    (fixed : ∀ u v,rem=u++v → ∀ a,oldH6 B (play x u) a=oldH6 B base a)
    (initial : correct (oldH6 B base) hh 5 x) :
    let addr := fun j=>S.getD j fall
    let i := digitFrom (addr len).1 4
    ∃ (start pre spectators residual out back after : List (Fin n)) (issue arrive turn ack : Fin n)
      (j : Nat) (p f : Payload) (s : Side),
      rem=start++issue::(pre++arrive::(spectators++incident i s::(residual++i::(out++turn::(back++ack::after))))) ∧
      Labels i .fresh ((spectators++incident i s::residual)++[i]) s ∧
      (∀ e∈spectators, e≠incident i .left ∧ e≠incident i .right) ∧
      let landed := step (play (step (play x start) issue) pre) arrive
      let oldRead := play landed spectators
      let exit := step (play landed (spectators++incident i s::residual)) i
      let atAck := play (step (play exit out) turn) back
      j<len ∧ addr j=(i,1) ∧ oldOrdinal B base hh i=4 ∧
      BusyOnly hp base addr len bitOp landed (.out j) spectators (.out j) ∧
      BStarBitOneObservation.Observes i j oldRead (.out j) (incident i s) ∧
      atSite (oldRead i).long 1=.forward p ∧
      BusyOnly hp base addr len bitOp exit (.out (j+1)) out (.out len) ∧
      project addr exit (j+1)=.forward (cleanBit p s) ∧
      bind (longGeometry B (atAck (addr 0).1)) 0 (atSite (atAck (addr 0).1).long 0)=.reply f ∧
      Event hp addr len atAck ack (.busy bitOp (.back 0)) .idle ∧
      ReceiptBank bitOp H.descriptor f H.bank ∧
      BStarBitCarry.parity f=(firstBit s).toNat := by
  let addr := fun j=>S.getD j fall
  let i := digitFrom (addr len).1 4
  obtain ⟨start,pre,post,back,after,issue,e,turn,ack,j,_,_,f,p,_,_,_,
    W,_,J,idx,_,_,_,_,_,_,land,_,hp0,R1,A0,O0,tail,_,_,reply,bank,hf,ret,Ack⟩ :=
    need_commit_landing hp C sep H need width notShort fixed initial
  let landed := step (play (step (play x start) issue) pre) e
  let leadW := start++issue::(pre++[e])
  have LP : play x leadW=landed := by
    simp [leadW,landed,BStarResetSchedule.run_append,BStarResetSchedule.run]
  have settled (u v : List (Fin n)) (split : rem=u++v) :
      correct (oldH6 B base) hh 5 (play x u) :=
    BStarNativeOffsetTrace.closed_word hp _ hh sep x u initial
      (fun a b E => funext (fixed a (b++v) (by rw [split,E,List.append_assoc])))
  have layouts (u v : List (Fin n)) (split : post=u++v) :
      (∀ a,oldH6 B (play landed u) a=oldH6 B base a) ∧ correct (oldH6 B base) hh 5 (play landed u) := by
    let a := leadW++u
    let b := v++turn::(back++ack::after)
    have S0 : rem=a++b := by simp [a,b,leadW,W,split,List.append_assoc]
    have Y : play x a=play landed u := by rw [BStarResetSchedule.run_append,LP]
    rw [←Y]
    exact ⟨fixed a b S0,settled a b S0⟩
  obtain ⟨fixed0,ready0⟩ := layouts [] post rfl
  have O : oldOrdinal B base hh i=4 :=
    ((bit_gate_iff hp hh fixed0 ready0 i 1).mp
      (chart_gate hp C width notShort fixed0 ready0).2.1).2
  change atCursor landed (addr j)=.forward p at land
  change addr j=(i,1) at idx
  rw [idx] at land
  have old : atSite (landed i).long 1=.forward {p with race:=cycleCode .fresh} := by
    change atCursor landed (i,1)=_
    rw [land]
    cases p
    simp_all [cycleCode]
  obtain ⟨hands,out,s,Q,read,before,trail,recv,Out⟩ :=
    busy_segment hp C sep i j idx O J p hp0.1 hp0.2 O0 A0 tail rfl
      (fun U => (Nat.ne_of_lt J) (Cursor.out.inj U.symm)) .fresh old
      (fun u a v Z => by rw [play_eq]; exact layouts u (a::v) Z)
  let xOld := play landed hands
  let exit := step xOld i
  have eqPlay := play_eq hp landed hands
  rw [eqPlay] at before trail recv Out
  have P : play landed post=play exit out := by rw [Q,BStarResetSchedule.run_append,BStarResetSchedule.run_append]; rfl
  rw [P] at reply ret Ack
  have next := chart_successor hp C (layouts hands (i::out) (by simp [Q,List.append_assoc])).1 i j J idx
  have output : project addr exit (j+1)=.forward (cleanBit p s) := by
    change atCursor exit (S.getD (j+1) fall)=_
    rw [next]
    exact recv
  have exactLayout (u v : List (Fin n)) (split : out=u++v) :
      (∀ a,oldH6 B (play exit u) a=oldH6 B base a) ∧ correct (oldH6 B base) hh 5 (play exit u) := by
    have Y : play landed (hands++i::u)=play exit u := by rw [BStarResetSchedule.run_append]; rfl
    rw [←Y]
    exact layouts (hands++i::u) v (by simp [Q,split,List.append_assoc])
  have Ord : (S.getD j fall).2=1 ∧ oldOrdinal B base hh (S.getD j fall).1=4  := by
    change (addr j).2=1 ∧ oldOrdinal B base hh (addr j).1=4
    rw [idx]
    exact ⟨rfl,O⟩
  have parity := BStarBitAckParity.exit_to_ack hp C sep j J turn (cleanBit p s) f output Out ret reply hf Ord
    (fun u v E => (exactLayout u v E).1) (exactLayout [] out rfl).2
  have D : incident i .left≠incident i .right := by
    intro E
    exact Side.noConfusion (incident_injective (oldH6 B base) hh i i O O .left .right E).2
  have labels := scanner_labels i D _ _ _ read
  obtain ⟨u,v,Huv,avoid⟩ := labels_bit labels
  have haveTail : ∃ residue, hands=u++incident i s::residue := by
    -- The completing outgoing mark cannot also be the first hit.
    by_cases lengths : u.length<hands.length
    · have A := List.take_append_drop u.length hands
      have U : hands.take u.length=u := by
        have H := congrArg (List.take u.length) Huv
        simpa [List.take_append_of_le_length,show u.length≤hands.length by omega] using H
      have V : hands.drop u.length≠[] := by
        intro E
        have N := congrArg List.length E
        simp at N
        omega
      cases Qv : hands.drop u.length with
      | nil => contradiction
      | cons a rest =>
        have eq : hands=u++a::rest := by rw [U,Qv] at A; exact A.symm
        have joined : u++(a::rest++[i])=u++(incident i s::v) := by rw [←List.append_assoc,←eq,Huv]
        have hit := (List.cons.inj (List.append_cancel_left joined)).1
        exact ⟨rest,hit ▸ eq⟩
    · have amount := congrArg List.length Huv
      simp at amount
      have l : u.length=hands.length := by omega
      have U : hands=u := by
        have eq := congrArg (List.take hands.length) Huv
        simpa [List.take_append_of_le_length, l] using eq
      have W : readSegment i .fresh (u++[i])=some s := by rwa [U] at read
      have impossible (w : List (Fin n))
          (A : ∀ e∈w, e≠incident i .left ∧ e≠incident i .right) :
          readSegment i .fresh (w++[i])=none := by
        induction w with
        | nil => simp [readSegment,nextPhase,incident]
        | cons a w ih =>
          obtain ⟨L,R⟩ := A a List.mem_cons_self
          simpa [readSegment,nextPhase,L,R] using ih (fun e M => A e (List.mem_cons_of_mem _ M))
      rw [impossible u avoid] at W
      cases W
  obtain ⟨residue,HU⟩ := haveTail
  have spec : atSite (play landed u i).long 1=.forward p := by
    rw [BStarBitPhysicalSwap.spectator_word hp i u avoid]
    exact land
  have postSplit : post=u++(incident i s::(residue++i::out)) := by
    simp [Q,HU,List.append_assoc]
  obtain ⟨z,P,T⟩ := split_busy hp tail u _ postSplit
  obtain ⟨z',Z'⟩ := busy_no_back_to_out hp T ⟨len,rfl⟩
  subst z
  have co := BStarAcquireHistoryReturn.busy_end hp P
  have slotF : project addr (play landed u) j=.forward p := by
    change atCursor (play landed u) (addr j)=_
    rw [idx]
    exact spec
  have atj := (BStarOwnerControlHistory.pointed_unique_forward _ len z' co.2.1 co.2.2 j (Nat.le_of_lt J)).mp ⟨p,slotF⟩
  subst z'
  have seen : BStarBitOneObservation.Observes i j (play landed u) (.out j) (incident i s) :=
    ⟨rfl,by cases s <;> simp,p,spec,hp0.1,hp0.2,O0,A0,R1⟩
  refine ⟨start,pre,u,residue,out,back,after,issue,e,turn,ack,j,p,f,s,?_,
    HU ▸ labels,avoid,J,idx,O,P,seen,spec,?_,?_,?_,?_,bank,?_⟩
  · simp only [W,Q,HU,List.append_assoc,List.cons_append,List.nil_append]
    rfl
  · exact HU ▸ Out
  · exact HU ▸ output
  · exact HU ▸ reply
  · exact HU ▸ Ack
  · rw [←parity]
    cases s <;> rfl

#print axioms from_handoff

open BStarAcquireAnchors BStarPhysicalPairLaw BStarPhysicalIncrementLedger BStarIncrementLedger

/-- Exact known-side specialization of chart_reveal. The current gate
and the actual COMMIT center belong to the same owner by chart entries,
not by an assumed owner map. The cut may be rebased to any earlier
origin by giving its exact raw replay equality. -/
theorem chart_reveal_known_side {base origin x old : X}
    {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x (fun j=>S.getD j fall) len rem rest mark center)
    (start : Fin n→Nat) (past : List (Fin n))
    (gate : Fin n) (j : Nat) (J : j≤len) (loc : S.getD j fall=(gate,1))
    (ord : oldOrdinal B base hh gate=4) (side : Side)
    (read : BStarBitOneObservation.Observes gate j (play origin past) (.out j) (incident gate side)) :
    ownerAt hp base hh gate=center ∧
    reveal hp base hh origin (ownerAt hp base hh) start past (incident gate side)=
      some ((center,count start (tapeInc hp base hh origin past) center past.length), firstBit side) := by
  have sz := C.length
  have belongs (k : Nat) (K : k≤len) : S.getD k fall∈S := by
    rw [←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have ga := (C.entries _ (loc ▸ belongs j J)).2
  have ce := (C.entries _ (H.atCenter ▸ belongs H.cursor H.cursor_le)).2
  have same : commandOwner (oldH6 B base) gate 1 = commandOwner (oldH6 B base) center 1 :=
    ga.trans ce.symm
  have own := ownerAt_center hp base hh gate center H.centerH6 same
  obtain ⟨_,_,v,raw,F,P,O,A,R⟩ := read
  have fresh : Fresh hp base hh (play origin past) gate := ⟨ord,v,raw,F,P,R,O,A⟩
  refine ⟨own,?_⟩
  rw [reveal_incident hp base hh origin (ownerAt hp base hh) start past gate side fresh,own]

#print axioms chart_reveal_known_side
end L4.BStarReceiptBitOrigin
