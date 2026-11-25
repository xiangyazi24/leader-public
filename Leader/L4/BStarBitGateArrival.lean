import Leader.L4.BStarBitTerminalHealth
import Leader.L4.BStarBitGateGeometry
import Leader.L4.BStarNumericChronology
import Leader.L4.BStarNativeOffsetTrace

namespace L4.BStarBitGateArrival
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongCommand BStarLongEvents BStarResetQuiet
open BStarLongRouting BStarLongCommandData BStarClearanceForward
open BStarLongFixedRouting BStarAcquireLiteralChain BStarH6WordChart
open BStarAcquireForwardTrace BStarResetMarkAdapter BStarResetRailRing
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarBitTerminalHealth BStarBitParity BStarNumericChronology
open BStarClearanceOffset BStarBitGateGeometry

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A literal selected advance landing with healthy BIT at a physical
BIT gate initializes race one and clears the argument. -/
theorem joined_gate_arrival (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (offer after : Payload)
    (K : a.occurrence=1)
    (G : gate bitOp 1 (geometry (Pair.map (longGeometry B) x) a.side)=true)
    (D : C.destination=some a)
    (M : (C,.advance offer)∈actualOffers (Pair.map (longGeometry B) x) (Pair.map LargeSite.long x))
    (F : readK (Pair.map LargeSite.long (largePair B x)) a=.forward after)
    (H : HealthyBit after) : after.race=1 ∧ after.argument=0 := by
  let g := Pair.map (longGeometry B) x
  let raw := Pair.map LargeSite.long x
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,M,rfl⟩
  have A := (move_lands g raw C offer a D M
    (Ne.symm (BStarAcquireReturn.link_shape g C a mem D).1)).2
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E
    subst a
    contradiction
  change decode (readRaw _ a)=_ at F
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode] at F
  rw [K] at F
  unfold arrive at F
  split at F
  · cases F
    exact ⟨rfl,rfl⟩
  · rename_i no
    cases F
    exact (no (by simp [H.1,H.2]; exact G)).elim

open BStarAcquireHistorySample BStarOwnerControlHistory
open BStarAcquireVisitOrder BStarResetChartTouch

/-- Crossing a fixed BIT chart address in a healthy outward tour gives
the exact raw prefix, selected old mark, and initialized landing. -/
theorem busy_gate_arrival {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
        HealthyBit after ∧ after.race=1 ∧ after.argument=0 := by
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
      exact ⟨[],e,w,q,D,a,offer,rfl,sel,dst,ad.symm,eq ▸ Q,eq ▸ current,qh,race⟩

open BStarStageProvenance BStarNativeActualLoadAccepted BStarCommitReceiptAuth
open BStarFenceReceiverChart BStarH6Ordinal

/-- The selecting ACK attached to the given COMMIT comes from a tour
with a real ordinal-four BIT landing. The returned witness is a split
of that very physical tape, and the landed token is the current front. -/
theorem need_commit_gate {base old x : X} {hh : ∃ i,oldH6 B base i=true}
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
      HealthyBit passed ∧ passed.race=1 ∧ passed.argument=0 ∧
      project addr atTurn len=.forward p ∧ HealthyBit p ∧
      bind (longGeometry B (atAck (addr 0).1)) 0 (atSite (atAck (addr 0).1).long 0)=.reply f ∧
      ReceiptBank bitOp H.descriptor f H.bank := by
  have settled (u v : List (Fin n)) (split : rem=u++v) :
      correct (oldH6 B base) hh 5 (play x u) :=
    BStarNativeOffsetTrace.closed_word hp _ hh sep x u initial
      (fun a b E => funext (fixed a (b++v) (by rw [split,E,List.append_assoc])))
  obtain ⟨start,out,back,after,issue,turn,ack,f,q,p,W,F,hq,zero,Out,P,hp0,reply,bank,_⟩ :=
    needed_commit_terminal hp C sep H need
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
  obtain ⟨pre,e,post,passed,K,a,offer,E,sel,dst,idx,L,current,hL,race,zeroL⟩ :=
    busy_gate_arrival hp C sep addr Out 0 len p rfl rfl positive (Nat.le_of_lt J) (Nat.le_refl _) P hp0 G
  rw [E,BStarResetSchedule.run_append] at P reply
  exact ⟨start,pre,post,back,after,issue,e,turn,ack,j,q,p,f,passed,K,a,offer,
    by simp [W,E,List.append_assoc],positive,J,addr,F,hq,zero,sel,dst,idx,L,current,hL,race,zeroL,P,hp0,reply,bank⟩

end L4.BStarBitGateArrival
