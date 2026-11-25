import Leader.L4.Compiler.Code
import Leader.L4.Compiler.DigitsWords

/-! Concrete register primitives over the accepted digit visits. -/
namespace L4.Compiler.PrimInstance
open Interp Digits Native
open L4.Compiler

def nibs (r x : Nat) : Digits.Word r :=
  fun i => ⟨x / 16 ^ i.val % 16, Nat.mod_lt _ (by decide)⟩

theorem nibs_prefix (r x : Nat) : ∀ j (h : j≤r), valJ (nibs r x) j h=x % 16^j := by
  intro j
  induction j with
  | zero => intro _; simp [valJ,Nat.mod_one]
  | succ j ih =>
    intro h
    rw [val_succ,ih _]
    exact (Nat.mod_pow_succ (x:=x) (b:=16) (k:=j)).symm

theorem nibs_value (r x : Nat) : val (nibs r x)=x%16^r :=
  nibs_prefix r x r (Nat.le_refl r)

def argument (r : Nat) (x : List Value) (j : Nat) : Digits.Word r :=
  nibs r (x.getD j (.word 0)).asWord

theorem argument_value (r : Nat) (x : List Value) (j : Nat) :
    val (argument r x j)=argW r x j := nibs_value ..

private theorem fin_take_succ {r j : Nat} (h : j<r) :
    (List.finRange r).take (j+1) = (List.finRange r).take j ++ [⟨j,h⟩] := by
  have H : j<(List.finRange r).length := by simpa using h
  rw [List.take_succ_eq_append_getElem H]
  congr 2
  apply Fin.ext
  rw [List.getElem_finRange]
  rfl

/-- Generic adaptor whose state invariant is the actual prefix fold.
The denotation is specified separately from the serial finish. -/
def fromFold {r : Nat} {X D A : Type} (input : List Value → X)
    (digit : X → Fin r → D) (init : X → A) (tick : Fin r → A → D → A)
    (enc : A → Nat) (dec : Nat → A) (hd : ∀ a, dec (enc a)=a)
    (out : A → Nat) (math : X → Nat)
    (sound : ∀ x, out ((List.finRange r).foldl (fun a j => tick j a (digit x j)) (init x))=math x) :
    Primitive r where
  Input := X
  Digit := D
  inputOf := input
  digit := digit
  init := fun x => enc (init x)
  step := fun j s d => enc (tick j (dec s) d)
  Inv := fun x j s => s=enc (((List.finRange r).take j).foldl (fun a i => tick i a (digit x i)) (init x))
  denotation := math
  finish := fun s => out (dec s)
  inv_zero := fun _ => rfl
  inv_step := by
    intro x j hj s H
    rw [H,hd,fin_take_succ hj,List.foldl_append]
    rfl
  inv_done := by
    intro x s H
    rw [H,List.take_of_length_le (by simp),hd,sound]

private theorem sum_prefix {r : Nat} (w : Digits.Word r) :
    ∀ j (h : j≤r),
    ((List.finRange r).take j).foldl (fun a i => a+16^i.val*(w i).val) 0=valJ w j h := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [fin_take_succ (Nat.lt_of_succ_le h),List.foldl_append,ih (Nat.le_of_succ_le h), val_succ]
    rfl

def gather {r : Nat} {X : Type} (input : List Value → X) (w : X → Digits.Word r)
    (math : X → Nat) (sound : ∀ x, val (w x)=math x) : Primitive r :=
  fromFold input w (fun _ => 0) (fun i a d => a+16^i.val*d.val)
    id id (fun _ => rfl) id math (by
      intro x
      have H := sum_prefix (w x) r (Nat.le_refl r)
      rw [List.take_of_length_le (by simp)] at H
      exact H.trans (sound x))

def load (r : Nat) (bank : Bank) (s : Fin 3) (i : Fin 9) : Primitive r :=
  gather (fun _ => ()) (fun _ j => copyStep (nibs r (bank.digits s i) j))
    (fun _ => bank.digits s i%16^r) (fun _ => nibs_value ..)

def maskB (r : Nat) (hr : 3≤r) : Primitive r :=
  gather id (fun x j => maskStep (argument r x 0 j) (positionAt r j.val))
    (fun x => argW r x 0 % 16^(r-2)) (fun x => by
      rw [mask_word (by omega : 2≤r),argument_value])

def mux (r : Nat) : Primitive r :=
  gather id (fun x j => muxStep (argB x 0) (argument r x 1 j) (argument r x 2 j))
    (fun x => if argB x 0 then argW r x 1 else argW r x 2) (fun x => by
      rw [mux_word,argument_value,argument_value])

/-- Comparison digit state holds separately the running equal and less flags. -/
def encCmp (a : Bool × Bool) : Nat := 2*a.1.toNat+a.2.toNat
def decCmp (a : Nat) : Bool × Bool := (a/2%2==1,a%2==1)
theorem dec_enc_cmp (a : Bool × Bool) : decCmp (encCmp a)=a := by
  obtain ⟨x,y⟩ := a
  cases x <;> cases y <;> rfl

def finishCmp (a : Bool × Bool) : Nat := if a.1 then 1 else if a.2 then 2 else 0

def cmp (r : Nat) : Primitive r :=
  fromFold id (fun x j => (argument r x 0 j,argument r x 1 j))
    (fun _ => (true,false)) (fun _ a d => cmpStep a.1 a.2 d.1 d.2)
    encCmp decCmp dec_enc_cmp finishCmp
    (fun x => cmpCode (argW r x 0) (argW r x 1))
    (by
      intro x
      rw [cmp_word,argument_value,argument_value]
      simp [finishCmp,cmpCode])

def decScan (s : Nat) : Fin 32 := ⟨s%32,Nat.mod_lt _ (by decide)⟩
theorem dec_enc_scan (a : Fin 32) : decScan a.val=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

def scanFive (r : Nat) (hr : 3≤r) : Primitive r :=
  fromFold id (fun x j => argument r x 0 j) (fun _ => (0 : Fin 32))
    (fun j a d => scan5Step j.val a d) Fin.val decScan dec_enc_scan Fin.val
    (fun x => argW r x 0 % 32) (fun x => by
      rw [scan_word (by omega : 2≤r),argument_value])

theorem cmp_tour (r : Nat) (x : List Value) :
    (cmp r).finish (runPrefix (cmp r) ((cmp r).inputOf x) r (Nat.le_refl r))=
      cmpCode (argW r x 0) (argW r x 1) :=
  primitive_tour_correct (cmp r) ((cmp r).inputOf x)

theorem scan5_tour (r : Nat) (hr : 3≤r) (x : List Value) :
    (scanFive r hr).finish (runPrefix (scanFive r hr) ((scanFive r hr).inputOf x) r (Nat.le_refl r))=
      argW r x 0 % 32 :=
  primitive_tour_correct (scanFive r hr) ((scanFive r hr).inputOf x)

def constNib (r : Nat) (c : ConstId) (i : Fin r) : Nib :=
  let p := positionAt r i.val
  match c with
  | .zero => constSmallStep 0 p
  | .one => constSmallStep 1 p
  | .eight => constSmallStep 8 p
  | .p => constPStep p
  | .bm1 => constBM1Step p
  | .max => constMaxStep

theorem const_word (r : Nat) (hr : 3≤r) (c : ConstId) :
    val (constNib r c)=c.val r := by
  cases c with
  | zero => exact small_word (by omega) 0
  | one => exact small_word (by omega) 1
  | eight => exact small_word (by omega) 8
  | p => exact p_word (by omega)
  | bm1 => exact bm1_word (by omega)
  | max => exact max_word

def literal (r : Nat) (hr : 3≤r) (c : ConstId) : Primitive r :=
  gather (fun _ => ()) (fun _ => constNib r c) (fun _ => c.val r%16^r) (fun _ => by
    have M := valJ_lt (constNib r c) r (Nat.le_refl r)
    change val (constNib r c)<16^r at M
    rw [const_word r hr c] at M ⊢
    exact (Nat.mod_eq_of_lt M).symm)

theorem applicable_subset (r : Nat) (hr : 3≤r) (bank : Bank) :
    (∀ s i xs, den (load r bank s i) xs=bank.digits s i%16^r) ∧
    (∀ c xs, den (literal r hr c) xs=c.val r%16^r) ∧
    (∀ xs, den (maskB r hr) xs=argW r xs 0%16^(r-2)) ∧
    (∀ xs, den (mux r) xs=(if argB xs 0 then argW r xs 1 else argW r xs 2)) ∧
    (∀ xs, den (cmp r) xs=cmpCode (argW r xs 0) (argW r xs 1)) ∧
    (∀ xs, den (scanFive r hr) xs=argW r xs 0%32) :=
  ⟨fun _ _ _ => rfl,fun _ _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

def accPrefix {r : Nat} {X C : Type} (step : X → Fin r → C → Nib × C)
    (zero : C) (x : X) (j : Nat) : C :=
  ((List.finRange r).take j).foldl (fun c i => (step x i c).2) zero

def serialWord {r : Nat} {X C : Type} (step : X → Fin r → C → Nib × C)
    (zero : C) (x : X) : Digits.Word r :=
  fun i => (step x i (accPrefix step zero x i.val)).1

theorem accPrefix_step {r : Nat} {X C : Type} (step : X → Fin r → C → Nib × C)
    (zero : C) (x : X) (i : Fin r) :
    accPrefix step zero x (i.val+1)=(step x i (accPrefix step zero x i.val)).2 := by
  unfold accPrefix
  rw [fin_take_succ i.isLt,List.foldl_append]
  rfl

private theorem serialFold_prefix {r : Nat} {X C : Type} (step : X → Fin r → C → Nib × C)
    (zero : C) (x : X) : ∀ j (hj : j≤r),
    ((List.finRange r).take j).foldl
      (fun (a : Nat × C) i =>
        let d := step x i a.2
        (a.1+16^i.val*d.1.val,d.2)) (0,zero) =
      (valJ (serialWord step zero x) j hj,accPrefix step zero x j) := by
  intro j
  induction j with
  | zero => intro h; rfl
  | succ j ih =>
    intro H
    let i : Fin r := ⟨j,by omega⟩
    rw [fin_take_succ i.isLt,List.foldl_append,ih (by omega),val_succ]
    have E := accPrefix_step step zero x i
    exact congrArg (Prod.mk _) E.symm

def encCarry {k : Nat} (a : Nat × Fin k) : Nat := a.1*k+a.2.val

def decCarry {k : Nat} (hk : 0<k) (s : Nat) : Nat × Fin k :=
  (s/k,⟨s%k,Nat.mod_lt _ hk⟩)

theorem dec_enc_carry {k : Nat} (hk : 0<k) (a : Nat × Fin k) :
    decCarry hk (encCarry a)=a := by
  simp only [decCarry,encCarry]
  apply Prod.ext
  · change (a.1*k+a.2.val)/k=a.1
    rw [Nat.mul_comm,Nat.mul_add_div hk,Nat.div_eq_of_lt a.2.isLt,Nat.add_zero]
  · apply Fin.ext
    change (a.1*k+a.2.val)%k=a.2.val
    simp [Nat.mul_comm,Nat.mod_eq_of_lt a.2.isLt]

def arithmetic {r k : Nat} (hk : 0<k)
    (step : List Value → Fin r → Fin k → Nib × Fin k)
    (math : List Value → Nat) (sound : ∀ x, val (serialWord step ⟨0,hk⟩ x)=math x) :
    Primitive r :=
  fromFold id (fun x j => step x j) (fun _ => (0,⟨0,hk⟩))
    (fun j a f => let d := f a.2; (a.1+16^j.val*d.1.val,d.2))
    encCarry (decCarry hk) (dec_enc_carry hk) Prod.fst math (by
      intro x
      have e := serialFold_prefix step ⟨0,hk⟩ x r (Nat.le_refl r)
      rw [List.take_of_length_le (by simp)] at e
      exact (congrArg Prod.fst e).trans (sound x))

def addVisit {r : Nat} (x : List Value) (i : Fin r) (c : Fin 2) : Nib × Fin 2 :=
  addStep (argument r x 0 i) (argument r x 1 i) c

def subVisit {r : Nat} (x : List Value) (i : Fin r) (c : Fin 2) : Nib × Fin 2 :=
  subStep (argument r x 0 i) (argument r x 1 i) c

def shiftVisit {r : Nat} (x : List Value) (i : Fin r) (c : Fin 8) : Nib × Fin 8 :=
  shl3Step (argument r x 0 i) c

theorem add_sound (r : Nat) (x : List Value) :
    val (serialWord (r:=r) addVisit 0 x)=(argW r x 0+argW r x 1)%16^r := by
  let c := accPrefix (r:=r) addVisit 0 x
  have eq := add_word (argument r x 0) (argument r x 1)
      (serialWord addVisit 0 x) (fun j => (c j).val) (fun _ => rfl)
      (fun j hj => by
        refine ⟨c j,rfl,?_⟩
        rw [show c (j+1)=(addVisit x (⟨j,hj⟩ : Fin r) (c j)).2 from accPrefix_step (r:=r) addVisit 0 x ⟨j,hj⟩]
        exact ⟨rfl,rfl⟩)
  have B := valJ_lt (serialWord (r:=r) addVisit 0 x) r (Nat.le_refl r)
  change val (serialWord (r:=r) addVisit 0 x)<16^r at B
  rw [argument_value,argument_value] at eq
  have Em := congrArg (fun z => z%16^r) eq
  simpa [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt B,Nat.mul_comm] using Em

theorem shift_sound (r : Nat) (x : List Value) :
    val (serialWord (r:=r) shiftVisit 0 x)=(8*argW r x 0)%16^r := by
  let c := accPrefix (r:=r) shiftVisit 0 x
  have eq := shl3_word (argument r x 0) (serialWord shiftVisit 0 x)
    (fun j => (c j).val) (fun _ => rfl) (fun j hj => by
      refine ⟨c j,rfl,?_⟩
      rw [show c (j+1)=(shiftVisit x (⟨j,hj⟩ : Fin r) (c j)).2 from accPrefix_step (r:=r) shiftVisit 0 x ⟨j,hj⟩]
      exact ⟨rfl,rfl⟩)
  have B := valJ_lt (serialWord (r:=r) shiftVisit 0 x) r (Nat.le_refl r)
  change val (serialWord (r:=r) shiftVisit 0 x)<16^r at B
  rw [argument_value] at eq
  have Em := congrArg (fun z => z%16^r) eq
  simpa [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt B,Nat.mul_comm] using Em

theorem sub_sound (r : Nat) (x : List Value) :
    val (serialWord (r:=r) subVisit 0 x)=(argW r x 0+16^r-argW r x 1)%16^r := by
  let c := accPrefix (r:=r) subVisit 0 x
  have eq := sub_word (argument r x 0) (argument r x 1)
    (serialWord subVisit 0 x) (fun j => (c j).val) (fun _ => rfl) (fun j hj => by
      refine ⟨c j,rfl,?_⟩
      have e := sub_digit_fact (argument r x 0 ⟨j,hj⟩) (argument r x 1 ⟨j,hj⟩) (c j)
      rw [show c (j+1)=(subVisit x (⟨j,hj⟩ : Fin r) (c j)).2 from accPrefix_step (r:=r) subVisit 0 x ⟨j,hj⟩]
      exact e.1)
  let y := val (serialWord (r:=r) subVisit 0 x)
  have Y : y<16^r := valJ_lt _ _ (Nat.le_refl r)
  have R : (c r).val<2 := (c r).isLt
  rw [argument_value,argument_value] at eq
  change y+argW r x 1=argW r x 0+16^r*(c r).val at eq
  by_cases B : (c r).val=0
  · rw [B,Nat.mul_zero,Nat.add_zero] at eq
    have E : argW r x 0+16^r-argW r x 1=y+16^r := by omega
    rw [E,Nat.add_mod_right,Nat.mod_eq_of_lt Y]
  · have K : (c r).val=1 := by omega
    rw [K,Nat.mul_one] at eq
    have E : argW r x 0+16^r-argW r x 1=y := by omega
    rw [E,Nat.mod_eq_of_lt Y]

def add (r : Nat) : Primitive r :=
  arithmetic (by decide : 0<2) addVisit (fun x => (argW r x 0+argW r x 1)%16^r) (add_sound r)

def sub (r : Nat) : Primitive r :=
  arithmetic (by decide : 0<2) subVisit (fun x => (argW r x 0+16^r-argW r x 1)%16^r) (sub_sound r)

def shiftThree (r : Nat) : Primitive r :=
  arithmetic (by decide : 0<8) shiftVisit (fun x => (8*argW r x 0)%16^r) (shift_sound r)

def table (r : Nat) (hr : 3≤r) (bank : Bank) : PrimTable r :=
  ⟨load r bank,literal r hr,maskB r hr,add r,sub r,shiftThree r,mux r,cmp r,scanFive r hr⟩

theorem semantics (r : Nat) (hr : 3≤r) (bank : Bank) : PrimSem (table r hr bank) bank :=
  ⟨fun _ _ _ => rfl,fun _ _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,
    fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

theorem concrete_tour {r : Nat} (p : Primitive r) (x : List Value) :
    p.finish (runPrefix p (p.inputOf x) r (Nat.le_refl r))=den p x :=
  primitive_tour_correct p (p.inputOf x)

def runOne {r : Nat} (p : Primitive r) (vs : List Value) : Nat :=
  p.finish (runPrefix p (p.inputOf vs) r (Nat.le_refl r))

theorem runOne_correct {r : Nat} (p : Primitive r) (vs : List Value) :
    runOne p vs=den p vs := concrete_tour p vs

/-- Width-three literal carry-out, full borrow, shift overflow, and
the two nonzero comparison encodings. Evaluates the actual visits. -/
theorem serial_fixtures :
    runOne (add 3) [.word 4095,.word 2]=1 ∧
    runOne (sub 3) [.word 0,.word 1]=4095 ∧
    runOne (shiftThree 3) [.word 513]=8 ∧
    runOne (cmp 3) [.word 31,.word 32]=2 ∧
    runOne (cmp 3) [.word 96,.word 96]=1 ∧
    runOne (scanFive 3 (by decide)) [.word 63]=31 := by
  decide +kernel

end L4.Compiler.PrimInstance
