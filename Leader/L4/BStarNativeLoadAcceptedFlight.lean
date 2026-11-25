import Leader.L4.BStarNativeLoadTours
import Leader.L4.BStarNumericHealthy

namespace L4.BStarNativeLoadAcceptedFlight
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongDoor BStarLongCommand BStarLongLayout BStarLongArithmetic BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin BStarClearanceSource
open BStarNativeReceiptTape BStarNumericHitSweep BStarNumericCarry BStarNumericConsecutive
open BStarSeparatingRail BStarNativeLoadTours
open BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Exact successful outward flight, turn and return of each LOAD;
the launch and the terminal packet come from the same Found/Hit. -/
theorem all_load_accepted_flights {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : NativeTape hp base (fun j=>S.getD j fall) len x 13 w 395)
    (q : Fin 3) (f : Fin 9) :
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    let op := loadOp q f
    ∃ (past launchPre flight back future : List (Fin n)) (launch turn ack : Fin n) (pay : Payload),
      w=past++launchPre++launch::(flight++turn::back)++ack::future ∧
      let old := play x (past++launchPre)
      let start := step old launch
      let out := play start flight
      let ret := play (step out turn) back
      (ctrlOp.read (old root).long).toNat=op ∧
      Launch (old root).long (start root).long ∧
      project slot out len=.forward pay ∧
      Numeric pay ∧ pay.opcode.toNat=op ∧
      Sweep hp base start slot len op flight (loadNode q f) (.load q f) ∧
      BusyOnly hp base slot len op out (.out len) (turn::back) (.back 0) ∧
      Hit hp base slot len ret ack op := by
  dsimp only
  let slot := fun j=>S.getD j fall
  let op := loadOp q f
  have lo : 13≤op := by unfold op loadOp; omega
  have hi : op<408 := by have := q.isLt; have := f.isLt; unfold op loadOp; omega
  obtain ⟨past,tour,future,ack,W,F,H⟩ := find_receipt hp T op lo hi
  obtain ⟨pre,turn,ret,E,P,ev,back⟩ := BStarAcquireAckAncestry.found_split_turn hp F
  obtain ⟨u,v,e,D,_,L,oldOp,outward⟩ := P
  have preEq : play (play x past) pre=play (step (play (play x past) u) e) v := by
    rw [D,BStarResetSchedule.run_append]
    rfl
  have retEq : play (play x past) tour=play (step (play (play x past) pre) turn) ret := by
    rw [E,BStarResetSchedule.run_append]
    rfl
  have I : Current hp base slot len (play (play x past) pre) (.busy op (.out len)) :=
    preEq.symm ▸ BStarAcquireHistoryReturn.busy_end hp outward
  obtain ⟨C,p,sel,_,dst,K,idx⟩ :=
    BStarStageTerminalHealth.selected_turn hp chart turn (sep turn) op I (busy_start hp back)
  obtain ⟨health,opEq,_⟩ := BStarReplyBack.numeric_selected_from_hit hp chart sep back (retEq ▸ H) lo hi C p K dst idx sel
  obtain ⟨⟨a,A,N,ao⟩,_⟩ :=
    BStarNumericTerminal.selected_return hp chart sep back C p K dst idx sel health
  have value : a.opcode.toNat=op := (congrArg BitVec.toNat ao).trans opEq
  obtain ⟨node,code,_⟩ := literal_load_slots q f
  have nodeA : nodeOf a.opcode.toNat=some (loadNode q f) := by rw [value]; exact node
  have SW := BStarNumericHealthy.successful_sweep hp chart sep outward (Nat.le_refl _) a (preEq ▸ A) N (loadNode q f) (.load q f) nodeA code
  have Bk : BusyOnly hp base slot len op (play (play x past) pre) (.out len) (turn::ret) (.back 0) :=
    .cons I ev back
  refine ⟨past,u,v,ret,future,e,turn,ack,a,?_,?_⟩
  · simp only [W,E,D,List.append_assoc,List.cons_append]
  · rw [BStarResetSchedule.run_append]
    exact ⟨oldOp,L,preEq ▸ A,N,value,SW,preEq ▸ Bk,preEq ▸ (retEq ▸ H)⟩

#print axioms all_load_accepted_flights
end L4.BStarNativeLoadAcceptedFlight
