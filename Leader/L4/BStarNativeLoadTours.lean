import Leader.L4.BStarNativeCompilerEntry
import Leader.L4.BStarNumericCompleteSweep

namespace L4.BStarNativeLoadTours
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongDoor BStarLongCommand BStarLongLayout BStarLongArithmetic
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarNativeReceiptTape BStarNumericHitSweep
open BStarSeparatingRail L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def loadOp (q : Fin 3) (f : Fin 9) : Nat := 18+19*q.val+f.val
def loadNode (q : Fin 3) (f : Fin 9) : Nat := 7+29*q.val+f.val

theorem literal_load_slots :
    ∀ q : Fin 3,∀ f : Fin 9,
      nodeOf (loadOp q f)=some (loadNode q f) ∧
      get (loadNode q f)=some (.load q f) ∧
      arithKind (loadOp q f)=some (if q=1 then .centerLoad else .unit) := by
  decide +kernel

/-- Each native receipt is found once by ordinal in the original
compiler tape. The returned Busy flight and accepted Hit have the
same initial replay and own consume mark. -/
theorem find_receipt {base x : X} {slot : Nat→Pos n} {len op count : Nat}
    {w : List (Fin n)}
    (T : NativeTape hp base slot len x op w count) (j : Nat)
    (L : op≤j) (U : j<op+count) :
    ∃ (pre flight tail : List (Fin n)) (ack : Fin n),
      w=pre++flight++ack::tail ∧
      Found hp base slot len j (play x pre) flight (.back 0) ∧
      Hit hp base slot len (play (play x pre) flight) ack j := by
  induction T with
  | done _ _ _ => omega
  | @take x op flight tail ack k _ _ F H T ih =>
    by_cases E : j=op
    · subst j
      exact ⟨[],flight,tail,ack,rfl,F,H⟩
    · obtain ⟨pre,out,back,e,W,A,D⟩ := ih (by omega) (by omega)
      have replay : play x ((flight++[ack])++pre)=play (step (play x flight) ack) pre := by
        rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
        rfl
      refine ⟨(flight++[ack])++pre,out,back,e,?_,replay.symm ▸ A,replay.symm ▸ D⟩
      rw [W]
      simp only [List.append_assoc,List.cons_append,List.nil_append]

/-- All 27 literal LOAD operands have the actual selected
departures and receipt on this one successful compiler tape. -/
theorem all_load_sweeps {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : NativeTape hp base (fun j=>S.getD j fall) len x 13 w 395) :
    ∀ q : Fin 3,∀ f : Fin 9,
      let slot := fun j=>S.getD j fall
      let op := loadOp q f
      ∃ (past out ret future launchPre flight : List (Fin n))
        (launch turn ack : Fin n),
        w=past++(out++turn::ret)++ack::future ∧
        out=launchPre++launch::flight ∧
        Found hp base slot len op (play x past) (out++turn::ret) (.back 0) ∧
        Hit hp base slot len (play (play x past) (out++turn::ret)) ack op ∧
        Sweep hp base (step (play (play x past) launchPre) launch)
          slot len op flight (loadNode q f) (.load q f) := by
  intro q f
  dsimp only
  let op := loadOp q f
  have LO : 13≤op := by unfold op loadOp; omega
  have HI : op<408 := by
    have hq := q.isLt
    have hf := f.isLt
    unfold op loadOp
    omega
  obtain ⟨past,tour,future,ack,W,F,H⟩ := find_receipt hp T op LO HI
  obtain ⟨out,turn,ret,C,v,D,_,_,_,_,_,_,init,launch,flight,nodeId,instr,E,N,K,Sw⟩ :=
    BStarNumericCompleteSweep.of_found hp chart sep F H LO HI
  obtain ⟨node,code,kind⟩ := literal_load_slots q f
  change nodeOf op=some (loadNode q f) at node
  obtain rfl := Option.some.inj (N.symm.trans node)
  obtain rfl := Option.some.inj (K.symm.trans code)
  exact ⟨past,out,ret,future,init,flight,launch,turn,ack,D ▸ W,E,D ▸ F,D ▸ H,Sw⟩

#print axioms literal_load_slots
#print axioms find_receipt
#print axioms all_load_sweeps
end L4.BStarNativeLoadTours
