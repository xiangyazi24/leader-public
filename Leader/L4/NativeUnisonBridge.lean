import Leader.L4.Compiler.NativeSpec
import Leader.L4.UnisonLiteralRecovery

namespace L4.NativeUnisonBridge
open Compiler.Native UnisonRows

def clock (x : NativeRecord) : Clock := ⟨x.err,x.tick⟩

def category : ClockAction → Action
  | .reset => .reset
  | .propagate _ => .propagate
  | .clear => .clear
  | .inc _ => .inc
  | .hold => .hold

private theorem bool_eq_of_guard {a b : Bool} (H : (a=true ↔ b=true)) : a=b := by
  cases a <;> cases b <;> simp_all

private theorem successor_equiv (M : Nat) (P : Int) (H : (M : Int)=2*P)
    (pos : 0<P) (half : (↑(M/2) : Int)=P) (t : Nat) :
    (↑(successor M t) : Int)=biasedSucc P t := by
  have sub : (↑(M-1) : Int)=(M:Int)-1 := by omega
  have E : t=M-1 ↔ (t:Int)=2*P-1 := by omega
  unfold successor biasedSucc
  by_cases K : t=M-1
  · rw [if_pos K,if_pos (E.mp K),half]
  · rw [if_neg K,if_neg (fun h => K (E.mpr h))]
    omega

/-- The native clock action (including HOLD) and result agree with
the literal biased row. Snapshot edits and BIT are immaterial to the
clock projection but do not weaken its action classification. -/
theorem native_biased (M : Nat) (P : Int) (H : (M:Int)=2*P) (pos : 0<P)
    (B : Nat) (l x r : NativeRecord) (d : Bool) :
    let a := nativeClock M l x r
    (category a,clock (finishNative B l x r a d))=biasedRow P (clock l) (clock x) (clock r) := by
  dsimp only
  have half : (↑(M/2) : Int)=P := by omega
  have sub : (↑(M-1) : Int)=(M:Int)-1 := by omega
  have Gap (y : NativeRecord) :
      (decide (x.tick+2≤y.tick) && !(decide (x.tick=M/2) && decide (y.tick=M-1))) =
        biasedLowerGap P (clock x).value (clock y).value := by
    apply bool_eq_of_guard
    simp [biasedLowerGap,clock]
    omega
  have Lower (y : NativeRecord) :
      (y.err && decide (y.tick<x.tick))=lowerError (clock x) (clock y) := by
    apply bool_eq_of_guard
    simp [lowerError,clock]
  have Sug (y : NativeRecord) :
      (↑(if y.err && decide (y.tick+1<M/2) && decide (y.tick+1<x.tick)
        then y.tick+1 else x.tick : Nat) : Int)=biasedSuggestion P (clock x) (clock y) := by
    have E : y.tick+1<M/2 ↔ (y.tick:Int)<P-1 := by omega
    have F : y.tick+1<x.tick ↔ (y.tick:Int)+1<(x.tick:Int) := by omega
    have k (y : NativeRecord) : (clock y).value=(y.tick:Int) := rfl
    have e (y : NativeRecord) : (clock y).err=y.err := rfl
    simp only [biasedSuggestion,k,e,E,F]
    by_cases h : (y.err && decide ((y.tick:Int)<P-1) &&
      decide ((y.tick:Int)+1<(x.tick:Int)))=true
    · simp [h]
    · simp [h]
  have Near (y : NativeRecord) :
      (decide (y.tick≤x.tick+1) && decide (x.tick≤y.tick+1) &&
        (decide (y.tick≤x.tick) || !y.err))=biasedClearOK (clock x) (clock y) := by
    have E : (decide (y.tick≤x.tick+1) && decide (x.tick≤y.tick+1))=
        biasedNear (clock x).value (clock y).value := by
      apply bool_eq_of_guard
      simp [biasedNear,clock]
      omega
    rw [E]
    simp [biasedClearOK,clock]
  have Front (y : NativeRecord) :
      (decide (y.tick=x.tick) || decide (y.tick=successor M x.tick))=
        biasedIncOK P (clock x) (clock y) := by
    apply bool_eq_of_guard
    have Q : biasedSucc P (clock x).value=(successor M x.tick : Int) :=
      (successor_equiv M P H pos half x.tick).symm
    change ((decide (y.tick=x.tick) || decide (y.tick=successor M x.tick))=true) ↔
      decide ((y.tick:Int)=(x.tick:Int) ∨ (y.tick:Int)=biasedSucc P (x.tick:Int))=true
    have E : biasedSucc P (x.tick:Int)=(successor M x.tick:Int) := Q
    simp [E]
    omega
  let s (y : NativeRecord) : Nat :=
    if y.err && decide (y.tick+1<M/2) && decide (y.tick+1<x.tick) then y.tick+1 else x.tick
  have propEq : (↑(min (s l) (s r)) : Int)=biasedProp P (clock l) (clock x) (clock r) := by
    have A : (↑(s l) : Int)=_ := Sug l
    have Z : (↑(s r) : Int)=_ := Sug r
    unfold biasedProp
    rw [←A,←Z]
    omega
  have lt : min (s l) (s r)<x.tick ↔ biasedProp P (clock l) (clock x) (clock r)<(clock x).value := by
    rw [←propEq]
    change min (s l) (s r)<x.tick ↔ (↑(min (s l) (s r)) : Int)<(x.tick:Int)
    omega
  have zero : x.tick=0 ↔ (clock x).value=0 := by simp [clock]
  have rootEq :
      (if x.err then !(lowerError (clock x) (clock l) || lowerError (clock x) (clock r))
          else biasedLowerGap P (clock x).value (clock l).value || biasedLowerGap P (clock x).value (clock r).value) =
      biasedRoot P (clock l) (clock x) (clock r) := rfl
  unfold nativeClock
  dsimp only
  simp only [Lower,Gap,Near,Front,rootEq,zero]
  let rr := (biasedRoot P (clock l) (clock x) (clock r) && !(x.err && decide ((clock x).value=0)))=true
  let nn := (x.err && biasedClearOK (clock x) (clock l) && biasedClearOK (clock x) (clock r))=true
  let ii := (!x.err && biasedIncOK P (clock x) (clock l) && biasedIncOK P (clock x) (clock r))=true
  let pp := min (s l) (s r)
  let vv := biasedProp P (clock l) (clock x) (clock r)
  let ss := successor M x.tick
  let tt := biasedSucc P (clock x).value
  let a := if rr then ClockAction.reset else if pp<x.tick then .propagate pp
    else if nn then .clear else if ii then .inc ss else .hold
  change (category a,clock (finishNative B l x r a d))=
    (if rr then (Action.reset,⟨true,0⟩) else if vv<(clock x).value then (Action.propagate,⟨true,vv⟩)
     else if nn then (Action.clear,⟨false,(clock x).value⟩) else if ii then (Action.inc,⟨false,tt⟩)
     else (Action.hold,clock x))
  by_cases hR : rr
  · simp only [a,if_pos hR,category,finishNative,clock]
    rfl
  simp only [a,if_neg hR]
  by_cases hP : pp<x.tick
  · have q : vv<(clock x).value := lt.mp hP
    simp only [if_pos hP,if_pos q]
    change (Action.propagate,Clock.mk true (pp:Int))=(Action.propagate,Clock.mk true vv)
    exact Prod.ext rfl (congrArg (Clock.mk true) propEq)
  · have q : ¬vv<(clock x).value := fun H => hP (lt.mpr H)
    simp only [if_neg hP,if_neg q]
    by_cases hc : nn
    · simp only [if_pos hc,category,finishNative,clock]
    simp only [if_neg hc]
    by_cases hi : ii
    · simp only [if_pos hi,category,finishNative,clock]
      exact Prod.ext rfl (congrArg (Clock.mk false) (successor_equiv M P H pos half x.tick))
    · simp only [if_neg hi,category,finishNative]

open Compiler.Native UnisonRing UnisonLiteralRecovery

def halfMod (r : Nat) : Int := (modulus r/2 : Nat)

theorem modulus_twice (r : Nat) (hr : 0<r) :
    (modulus r:Int)=2*halfMod r ∧ 0<halfMod r := by
  cases r with
  | zero => omega
  | succ r =>
    have H : 0<16^r := Nat.pow_pos (by decide)
    have S : modulus (r+1)=16^r*16 := by unfold modulus; rw [Nat.pow_succ]
    unfold halfMod
    rw [S]
    omega

/-- Raw clock as represented by the held bank's tick and error bits.
The modulo operation is a no-op on physical r-nibble ticks. -/
def rawClock (r : Nat) (bank : Bank) (side : Fin 3) : Clock :=
  ⟨bank.hdr side 0,bank.digits side 0 % modulus r⟩

theorem decode_bank_clock (r : Nat) (bank : Bank) (side : Fin 3) :
    clock (decodeBank r bank side)=normalizeBiased (halfMod r) (rawClock r bank side) := by
  have guard : modulus r/2≤bank.digits side 0 % modulus r ↔
      halfMod r≤(bank.digits side 0 % modulus r : Nat) := by
    unfold halfMod
    omega
  unfold normalizeBiased rawClock
  change clock (decodeBank r bank side)=
    if bank.hdr side 0 && decide (halfMod r≤(bank.digits side 0 % modulus r : Nat)) then
      ⟨true,0⟩ else ⟨bank.hdr side 0,(bank.digits side 0 % modulus r : Nat)⟩
  by_cases e : bank.hdr side 0
  · by_cases v : modulus r/2≤bank.digits side 0 % modulus r
    · have V := guard.mp v
      simp only [clock,decodeBank,e,v,V,decide_true,Bool.true_and,if_true]
      rfl
    · have V : ¬halfMod r≤(bank.digits side 0 % modulus r : Nat) := fun H => v (guard.mpr H)
      simp only [clock,decodeBank,e,v,V,decide_false,Bool.true_and,Bool.false_eq_true,if_false]
  · simp [clock,decodeBank,e]

def outputClock (y : Output) : Clock := ⟨y.hdr 0,y.digits 0⟩

theorem output_clock (r : Nat) (hr : 0<r) (bank : Bank) (d : Bool) :
    let N := fun i => normalizeBiased (halfMod r) (rawClock r bank i)
    outputClock ((nativeSpec r bank).2 d)=(biasedRow (halfMod r) (N 0) (N 1) (N 2)).2 := by
  let l := decodeBank r bank 0
  let x := decodeBank r bank 1
  let z := decodeBank r bank 2
  have h := modulus_twice r hr
  have A := congrArg Prod.snd (native_biased (modulus r) (halfMod r) h.1 h.2 (heightMod r) l x z d)
  change clock (finishNative (heightMod r) l x z (nativeClock (modulus r) l x z) d)=_ at A
  change clock (finishNative (heightMod r) l x z (nativeClock (modulus r) l x z) d)=_
  rw [A,show clock l=_ from decode_bank_clock r bank 0,show clock x=_ from decode_bank_clock r bank 1,
    show clock z=_ from decode_bank_clock r bank 2]

/-- Once a real publication is known to emit the native bank, the
actual single-site update projects to the signed poll. HOLD is
an allowed publication here; no strictness or change predicate occurs. -/
theorem decode_publication {m : Nat} (R : Ring m) (r : Nat) (hr : 0<r)
    (before after : UnisonRing.State m) (e : Fin m) (bank : Bank) (d : Bool)
    (range : RawInRange (halfMod r) before)
    (L : rawClock r bank 0=before (R.left e))
    (C : rawClock r bank 1=before e)
    (V : rawClock r bank 2=before (R.right e))
    (frame : ∀ i, i≠e → after i=before i)
    (write : after e=outputClock ((nativeSpec r bank).2 d)) :
    decodeRing (halfMod r) after=UnisonRing.step R (halfMod r) (decodeRing (halfMod r) before) e := by
  have E : after=rawAtomic R (halfMod r) before e := by
    funext i
    by_cases h : i=e
    · subst i
      simp only [rawAtomic,if_true]
      rw [write,output_clock r hr bank d]
      dsimp only
      rw [L,C,V]
    · simpa [rawAtomic,h] using frame i h
  rw [E]
  exact raw_decode_step R _ (modulus_twice r hr).2 before e range

#print axioms decode_publication
#print axioms native_biased
end L4.NativeUnisonBridge
