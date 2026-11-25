import Leader.L4.BStarNumericTailCarry
import Leader.L4.BStarNumericChartCoverage
import Leader.L4.BStarNativeZeroHead
import Leader.L4.BStarScalarFits
import Leader.L4.Compiler.DigitsWords

namespace L4.BStarNativeSubHead
open AllSizeProtocol BStarTrace BStarLongToken BStarLongLayout
open BStarLongArithmetic BStarLongRegisters BStarPhysicalDigitSem BStarPhysicalWordSem
open L4.Compiler.Digits L4.Compiler.Native L4.Compiler.Interp
open BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction BStarScalarFits

/-- Discharge the SUB arithmetic and distinct carry-store obligations
from a physical DigitSweep. Operand agreement is with the accepted
register indices, not with an unconstrained semantic head value. -/
theorem sub_refines {r : Nat} (T : PrimTable r) (bank : Bank) (P : PrimSem T bank)
    {geom : Fin r → LongGeometry} {old fresh : Fin r → BitVec LW}
    {i a b : Nat} {tokens : Nat → Payload}
    (S : DigitSweep geom old fresh i (.sub a b) tokens)
    (hi : WordSlot i) (ha : WordSlot a) (hb : WordSlot b)
    (regs : List Value)
    (A : val (readWord old a ha)=argW r (readArgs regs [a,b]) 0)
    (B : val (readWord old b hb)=argW r (readArgs regs [a,b]) 1)
    (initial : arg tokens 0=0) :
    evalInstr (toInstr T bank (.sub a b)) regs=.word (val (readWord fresh i hi)) ∧
    arg tokens r<2 := by
  have wordEq := physical_sub_word S hi ha hb initial
  rw [A,B] at wordEq
  have lt : val (readWord fresh i hi)<16^r := valJ_lt _ _ _
  have carry := (follows S hi 2 (by decide)
    (fun j c => subStep (nib (old j) a ha) (nib (old j) b hb) c)
    (by rw [initial]; decide)
    (fun j c h => sub_row (geom j) (old j) i a b (tokens j.val) ha hb c h)).1 r (Nat.le_refl _)
  refine ⟨?_,carry⟩
  change Value.word (den T.sub (readArgs regs [a,b]))=_
  rw [P.sub]
  let base := 16^r
  let u := argW r (readArgs regs [a,b]) 0
  let v := argW r (readArgs regs [a,b]) 1
  let y := val (readWord fresh i hi)
  have Eq : y+v=u+base*arg tokens r := wordEq
  have dy : y<base := lt
  apply congrArg Value.word
  change ((u+base-v)%base)=y
  rcases (show arg tokens r=0 ∨ arg tokens r=1 by omega) with Z|O
  · rw [Z,Nat.mul_zero,Nat.add_zero] at Eq
    have L : u+base-v=y+base := by omega
    rw [L,Nat.add_mod_right,Nat.mod_eq_of_lt dy]
  · rw [O,Nat.mul_one] at Eq
    rw [show u+base-v=y by omega,Nat.mod_eq_of_lt dy]

/-- The actual bound NumericTailCarry output of an SUB tour is still
the same one-bit carry; transport does not reinterpret it as the
distributed word stored at K1. -/
theorem sub_reply_fit {r : Nat} {geom : Fin r → LongGeometry} {old fresh : Fin r → BitVec LW}
    {i a b : Nat} {tokens : Nat → Payload}
    (S : DigitSweep geom old fresh i (.sub a b) tokens)
    (hi : WordSlot i) (ha : WordSlot a) (hb : WordSlot b)
    (initial : arg tokens 0=0) (actual : Payload)
    (reply : actual=BStarNumericReceipt.output (tokens r)) :
    PayloadBound (.sub a b) actual.argument.toNat := by
  change actual.argument.toNat<2
  rw [reply]
  change ((tokens r).argument.toNat % 2^(BStarNumericReceipt.resultWidth (tokens r).opcode.toNat)) % 2^34<2
  apply Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _))
  exact (follows S hi 2 (by decide)
    (fun j c => subStep (nib (old j) a ha) (nib (old j) b hb) c)
    (by rw [initial]; decide)
    (fun j c h => sub_row (geom j) (old j) i a b (tokens j.val) ha hb c h)).1 r (Nat.le_refl _)

/-- An SUB head adds neither a Boolean nor a comparison register.
The actual one-bit carry pending write therefore extends scalar
WellRep unchanged on prior slots. -/
theorem sub_pending_rep (x : BitVec LW) (p : Payload) (k a b result : Nat)
    (regs : List Value) (J : regs.length=start k) (G : get (start k)=some (.sub a b))
    (R : WellRep x [] regs literalCmp) :
    WellRep x (headPending x k p (.sub a b)) (regs++[.word result]) literalCmp := by
  intro i I
  by_cases E : i=start k
  · subst i
    have H : readReg (regs++[Value.word result]) (start k)=.word result := by
      rw [←J]; simp [readReg]
    constructor
    · intro b h
      rw [H] at h
      contradiction
    · simp [literalCmp,G,BStarCmpReceipt.isCmp]
  · have less : i<regs.length := by simp only [List.length_append,List.length_singleton] at I; omega
    have W := readReg_append_left regs [Value.word result] i less
    have F : newest x (headPending x k p (.sub a b)) i=newest x [] i := by
      simp [headPending,nodeResult,newest,show start k≠i from Ne.symm E]
    have ⟨U,V⟩ := R i less
    exact ⟨fun b h => F.trans (U b (W.symm ▸ h)),
      fun q => by simpa only [CmpRep,W,F] using V q⟩

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongArithmetic BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarOwnerLaunchOrigin BStarSeparatingRail BStarAcquireForwardTrace
open BStarNumericCarry BStarNumericContinuity BStarNumericConsecutive BStarNumericChronology
open BStarNumericReceipt BStarLongEvents

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)
open BStarH6Ordinal

theorem actual_sub_refines {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {turn door : Fin n} {w ret : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (T : BusyOnly hp base (fun j => S.getD j fall) len op (step (run x w) turn) (.back len) ret (.back 0))
    (hit : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len
      (run (step (run x w) turn) ret) door op)
    (lo : 13≤op) (hi : op<408)
    (C : CommandClaim) (v : Payload) (K : C.source.occurrence.val=10) (hd : C.destination=none)
    (idx : S.getD len fall=address turn C.source)
    (sel : let y := run x w
      (C,.advance v)∈actualOffers (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long))
    (i a b : Nat) (Nd : nodeOf op=some i) (Cd : get i=some (.sub a b))
    (before : List D) (d : D)
    (last : ds.filter (significant hp base (fun j => S.getD j fall))=before++[d])
    (tokens : Nat → Payload) (hiSlot : WordSlot i) (ha : WordSlot a) (hb : WordSlot b)
    {width : Nat}
    (flags : ∀ j, (longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (TT : PrimTable width) (bank : Bank) (sem : PrimSem TT bank)
    (regs : List Value) (rs : regs.length=start (op-13))
    (oldScalar : WellRep ((run (step (run x w) turn) ret) (S.getD 0 fall).1).long [] regs literalCmp)
    (initial : arg tokens 0=0) :
    let addr := fun j => S.getD j fall
    let z := run (step (run x w) turn) ret
    let wire := (z (addr 0).1).long
    let visits := ds.filter (significant hp base addr)
    let old := fun j : Fin visits.length => byte visits[j.val]
    let geom' := fun j : Fin visits.length => geom hp visits[j.val]
    let fresh := fun j => ((physicalDigit (geom' j) (old j) i (.sub a b) visits[j.val].offer).1).apply (old j)
    (∀ j : Fin visits.length,tokens j.val=visits[j.val].offer) →
    DigitSweep geom' old fresh i (.sub a b) tokens →
    (val (readWord old a ha)=argW width (readArgs regs [a,b]) 0) →
    (val (readWord old b hb)=argW width (readArgs regs [a,b]) 1) →
    let result := val (readWord fresh i hiSlot)
    evalInstr (toInstr TT bank (.sub a b)) regs=.word result ∧
      ∃ actual, bind (longGeometry B (z (addr 0).1)) 0 (atSite wire 0)=.reply actual ∧
        PayloadBound (.sub a b) actual.argument.toNat ∧
        WellRep wire (headPending wire (op-13) actual (.sub a b))
          (regs++[.word result]) literalCmp := by
  dsimp only
  intro seq sweep lhs rhs
  have L := BStarNumericChartCoverage.significant_length hp chart A flags notShort
  have sites := BStarNumericChartCoverage.aligned_sites hp A
  have lenEq := congrArg List.length sites
  rw [List.length_map,L] at lenEq
  obtain ⟨_,returned⟩ := BStarNumericTailCarry.receipt_of_sweep hp chart sep A T hit lo hi
    C v K hd idx sel i (.sub a b) Nd Cd before d last tokens seq sweep
  have initialOp : 13+(op-13)=op := by omega
  have rank : op-13<395 := by omega
  have equalIdx : start (op-13)=i := by
    have E := scheduled_node rank
    rw [initialOp] at E
    exact Option.some.inj (E.symm.trans Nd)
  have good : get (start (op-13))=some (.sub a b) := equalIdx ▸ Cd
  revert TT sem lhs rhs
  cases lenEq
  intro TT sem lhs rhs
  have E := sub_refines TT bank sem sweep hiSlot ha hb regs lhs rhs initial
  refine ⟨E.1,_,returned,sub_reply_fit sweep hiSlot ha hb initial _ rfl,?_⟩
  exact sub_pending_rep _ _ _ a b _ regs rs good oldScalar

#print axioms actual_sub_refines
#print axioms sub_refines
#print axioms sub_reply_fit
#print axioms sub_pending_rep
end L4.BStarNativeSubHead
