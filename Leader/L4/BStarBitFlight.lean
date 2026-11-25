import Leader.L4.BStarBitGateOutcome
import Leader.L4.BStarBitAckParity
import Leader.L4.BStarBitGateGeometry
import Leader.L4.BStarNumericChronology
import Leader.L4.BStarNativeOffsetTrace

namespace L4.BStarBitFlight
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

/-- Crossing a fixed BIT chart address in a healthy outward tour gives
the exact raw leadW, selected old mark, and initialized landing. -/
theorem busy_gate_landing {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {i : Fin n} {j : Nat} (atJ : S.getD j fall=(i,1))
    {w : List (Fin n)} {z d : Cursor}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len bitOp x z w d) :
    ∀ k l f, z=.out k → d=.out l → k<j → j≤l → l≤len →
      project (fun j=>S.getD j fall) (play x w) l=.forward f → HealthyBit f →
      (∀ pre e post,w=pre++e::post→gate bitOp 1 (longGeometry B (play x pre i))=true) →
      ∃ pre e post after K a offer, w=pre++e::post ∧
        let y := play x pre
        (K,.advance offer)∈actualOffers (oldPair B y e)
          ((y e).long,(y (rightNeighbor e)).long) ∧ K.destination=some a ∧
        address e a=(i,1) ∧
        project (fun j=>S.getD j fall) (step y e) j=.forward after ∧
        Current hp base (fun j=>S.getD j fall) len (step y e) (.busy bitOp (.out j)) ∧
        HealthyBit after ∧ after.race=1 ∧ after.argument=0 ∧ after.outcome=0 ∧
        BusyOnly hp base (fun j=>S.getD j fall) len bitOp (step y e) (.out j) post (.out l) := by
  induction P with
  | nil _ =>
    intro k l f Z D K J _ _ _ _
    have E := Cursor.out.inj (Z.symm.trans D)
    omega
  | @cons x z d final e w I E tail ih =>
    intro k l f Z L K J V F H Gate
    subst z
    obtain ⟨k',Z'⟩ := busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    have A : Advance len (.out k) (.out k') := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ A _ rest => cases rest; exact A
    by_cases lt : k'<j
    · obtain ⟨pre,e',post,after,D,a,offer,W,R⟩ := ih k' l f rfl L lt J V F H
        (fun u b v Q => Gate (e::u) b v (congrArg (List.cons e) Q))
      exact ⟨e::pre,e',post,after,D,a,offer,congrArg (List.cons e) W,R⟩
    · have eq : k'=j := by cases A <;> omega
      have inc : k+1=j := by cases A <;> omega
      have current := busy_start hp tail
      obtain ⟨b,hb,q,Q,hq,O⟩ := busy_origin hp C sep tail l V f F H.1
      have U := (pointed_unique_forward _ len _ current.2.1 current.2.2 b hb).mp ⟨q,Q⟩
      subst b
      have qh : HealthyBit q := ⟨hq, (congrArg BitVec.toNat O).trans H.2⟩
      have Q' : project (fun j=>S.getD j fall) (step x e) (k+1)=.forward q := by
        rwa [inc,←eq]
      obtain ⟨D,a,offer,sel,dst,_,ad⟩ := ring_departure hp C e (sep e) bitOp k
        (by omega) I.1 I.2.1 I.2.2 q Q' hq
      rw [inc,atJ] at ad
      have K1 : a.occurrence=1 := (congrArg Prod.snd ad).symm
      have G0 := Gate [] e w rfl
      have ad1 : site e a.side=i := (congrArg Prod.fst ad).symm
      have geom : geometry (oldPair B x e) a.side=longGeometry B (x i) := by
        rw [←ad1]
        cases a with
        | mk s j => cases s <;> rfl
      have post := (new_read B x e (sep e) a).trans
        ((congrArg (atCursor (step x e)) (show address e a=S.getD j fall from ad.symm.trans atJ.symm)).trans
          (eq ▸ Q))
      have race := joined_gate_arrival hp (x e,x (rightNeighbor e)) D a offer q K1
        (show gate bitOp 1 (geometry (oldPair B x e) a.side)=true by rw [geom]; exact G0)
        dst sel post qh
      have outcome := joined_outcome k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) D a offer q K1 dst sel post qh
      exact ⟨[],e,w,q,D,a,offer,rfl,sel,dst,ad.symm,eq ▸ Q,eq ▸ current,qh,race.1,race.2,outcome,by simpa only [BStarResetSchedule.run,eq,L] using tail⟩


open BStarStageProvenance BStarNativeActualLoadAccepted BStarCommitReceiptAuth
open BStarFenceReceiverChart BStarH6Ordinal

/-- The selecting ACK attached to the given COMMIT comes from a tour
with a real ordinal-four BIT landing. The returned witness is a split
of that very physical tape, and the landed token is the current front. -/
theorem need_commit_landing {base old x : X} {hh : ∃ i,oldH6 B base i=true}
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
    ∃ (start pre post back after : List (Fin n)) (issue e turn ack : Fin n)
      (j : Nat) (q p f passed : Payload) (K : CommandClaim) (a : AtK) (offer : Payload),
      rem=start++issue::(pre++e::(post++turn::(back++ack::after))) ∧
      let issued := step (play x start) issue
      let y := play issued pre
      let landed := step y e
      let atTurn := play landed post
      let atAck := play (step atTurn turn) back
      0<j ∧ j<len ∧ addr j=(i,1) ∧
      project addr issued 0=.forward q ∧ HealthyBit q ∧ q.race=0 ∧
      (K,.advance offer)∈actualOffers (oldPair B y e)
        ((y e).long,(y (rightNeighbor e)).long) ∧ K.destination=some a ∧ address e a=(i,1) ∧
      project addr landed j=.forward passed ∧
      Current hp base addr len landed (.busy bitOp (.out j)) ∧
      HealthyBit passed ∧ passed.race=1 ∧ passed.argument=0 ∧ passed.outcome=0 ∧
      BusyOnly hp base addr len bitOp landed (.out j) post (.out len) ∧
      project addr atTurn len=.forward p ∧ HealthyBit p ∧
      bind (longGeometry B (atAck (addr 0).1)) 0 (atSite (atAck (addr 0).1).long 0)=.reply f ∧
      ReceiptBank bitOp H.descriptor f H.bank ∧ HealthyBit f ∧
      BusyOnly hp base addr len bitOp (step atTurn turn) (.back len) back (.back 0) ∧
      Event hp addr len atAck ack (.busy bitOp (.back 0)) .idle := by
  have settled (u v : List (Fin n)) (split : rem=u++v) :
      correct (oldH6 B base) hh 5 (play x u) :=
    BStarNativeOffsetTrace.closed_word hp _ hh sep x u initial
      (fun a b E => funext (fixed a (b++v) (by rw [split,E,List.append_assoc])))
  have K : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  obtain ⟨start,out,back,after,issue,turn,ack,f,q,W,_,F,hq,opq,zero,Out,_,ret,Ack,reply,hf,opf,bank⟩ :=
    BStarBitSelectingTrace.needed_bit_route hp H K sep need
  obtain ⟨p,_,_,P,hp0,_,_,_,_⟩ :=
    terminal_of_ack hp C sep turn back f (BStarAcquireHistoryReturn.busy_end hp Out) ret reply ⟨hf,opf⟩
  let issued := step (play x start) issue
  let i := digitFrom (S.getD len fall).1 4
  obtain ⟨_,_,_,j,J,addr⟩ :=
    chart_gate hp C width notShort (fixed [] rem rfl) (settled [] rem rfl)
  have positive : 0<j := by
    apply Nat.pos_of_ne_zero
    intro z
    rw [z,C.root] at addr
    exact (by decide : (0:Fin 11)≠1) (congrArg Prod.snd addr)
  have G : ∀ pre e post,out=pre++e::post→gate bitOp 1 (longGeometry B (play issued pre i))=true := by
    intro pre e post E
    let u := start++issue::pre
    let v := e::(post++turn::(back++ack::after))
    have split : rem=u++v := by simp [u,v,W,E,List.append_assoc]
    have old : play x u=play issued pre := by simp [u,issued,BStarResetSchedule.run_append,BStarResetSchedule.run]
    obtain ⟨_,Gate,_,_⟩ := chart_gate hp C width notShort (fixed u v split) (settled u v split)
    rwa [old] at Gate
  obtain ⟨pre,e,post,passed,K,a,offer,E,sel,dst,idx,L,current,hL,race,zeroL,outcome,tail⟩ :=
    busy_gate_landing hp C sep addr Out 0 len p rfl rfl positive (Nat.le_of_lt J) (Nat.le_refl _) P hp0 G
  rw [E,BStarResetSchedule.run_append] at P reply ret Ack
  exact ⟨start,pre,post,back,after,issue,e,turn,ack,j,q,p,f,passed,K,a,offer,
    by simp [W,E,List.append_assoc],positive,J,addr,F,⟨hq,opq⟩,zero,sel,dst,idx,L,current,hL,race,zeroL,outcome,tail,P,hp0,reply,bank,⟨hf,opf⟩,ret,Ack⟩

open BStarBitSegment BStarBitDepart BStarClearanceRaceMark BStarLongLiteral

/-- The physical receiver of the completed BIT mark is precisely the
next occurrence of the same chart, including the seam K2 case. -/
theorem chart_successor {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ a,oldH6 B x a=oldH6 B base a)
    (i : Fin n) (j : Nat) (J : j<len) (idx : S.getD j fall=(i,1)) :
    S.getD (j+1) fall=(rightNeighbor i,slot hp x i) := by
  have size := C.length
  have start : (i,(1:Fin 11))∈S := by
    rw [←idx,←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  let g := oldPair B base i
  let k : Fin 11 := if g.2.axes.h6 then 2 else 1
  have sk : slot hp x i=k := by change (if oldH6 B x (rightNeighbor i) then 2 else 1)=_; rw [fixed]; rfl
  have E : Edge B base (i,1) (rightNeighbor i,k) :=
    ⟨i,centerLink g,R k,center_mem g,rfl,rfl,rfl⟩
  obtain ⟨d,D,src,dst⟩ := C.edge (i,1) (rightNeighbor i,k) start E
  have S0 : S.getD d fall=(i,1) := (List.getElem_eq_getD (h:=show d<S.length by omega) fall).symm.trans src
  have j0 : d=j := (List.getD_inj (by omega) (by omega) C.nodup).mp (S0.trans idx.symm)
  rw [←j0,←List.getElem_eq_getD (h:=D),dst,sk]

private theorem play_eq (x : X) (w : List (Fin n)) : BStarBitReplay.play hp x w=play x w := by
  induction w generalizing x with
  | nil => rfl
  | cons a v ih => exact ih (step x a)

/-- On the very selecting receipt belonging to a given NEED COMMIT,
identify the true initialized gate, its exact actual handshake prefix,
the physical departure and the matching raw ACK's first-side parity. -/
theorem need_commit_first_side {base old x : X} {hh : ∃ i,oldH6 B base i=true}
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
    ∃ (start pre hands out back after : List (Fin n)) (issue arrive turn ack : Fin n)
      (j : Nat) (p f : Payload) (s : Side),
      rem=start++issue::(pre++arrive::(hands++i::(out++turn::(back++ack::after)))) ∧
      Labels i .fresh (hands++[i]) s ∧
      (∃ u v, hands++[i]=u++incident i s::v ∧
        ∀ e∈u, e≠incident i .left ∧ e≠incident i .right) ∧
      let landed := step (play (step (play x start) issue) pre) arrive
      let exit := step (play landed hands) i
      let atAck := play (step (play exit out) turn) back
      j<len ∧ addr j=(i,1) ∧
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
  refine ⟨start,pre,hands,out,back,after,issue,e,turn,ack,j,p,f,s,?_,
    labels,labels_bit labels,J,idx,Out,output,reply,Ack,bank,?_⟩
  · change rem=start++issue::(pre++e::(hands++i::(out++turn::(back++ack::after))))
    simp only [W,Q,List.append_assoc,List.cons_append,List.nil_append]
  · rw [←parity]
    cases s <;> rfl

#print axioms need_commit_landing
#print axioms need_commit_first_side
end L4.BStarBitFlight
