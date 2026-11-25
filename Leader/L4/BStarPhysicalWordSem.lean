import Leader.L4.BStarPhysicalDigitSem

/-! Value transfer of a complete chronological sweep. Routing must
separately supply these significant visits in order; this module
does not assume a physical input is already the output of a compiler. -/
namespace L4.BStarPhysicalWordSem
open AllSizeProtocol BStarTrace BStarLongToken BStarLongArithmetic
open BStarPhysicalDigitSem L4.Compiler.Digits
open L4.Compiler.Native

structure DigitSweep {r : Nat} (geom : Fin r → LongGeometry)
    (old updated : Fin r → BitVec LW) (reg : Nat) (c : Code) (tokens : Nat → Payload) : Prop where
  step : ∀ j : Fin r,
    let z := physicalDigit (geom j) (old j) reg c (tokens j.val)
    (z.1.apply (old j),z.2)=(updated j,tokens (j.val+1))

def readWord {r : Nat} (xs : Fin r → BitVec LW) (i : Nat) (h : WordSlot i) : Word r :=
  fun j => nib (xs j) i h

def arg (tokens : Nat → Payload) (j : Nat) : Nat := (tokens j).argument.toNat

/-- Transfer the small accumulator invariant and the actual target
field from every exact packed digit handler. -/
theorem follows {r : Nat} {geom : Fin r → LongGeometry} {old updated : Fin r → BitVec LW}
    {reg : Nat} {c : Code} {tokens : Nat → Payload} (H : DigitSweep geom old updated reg c tokens)
    (hi : WordSlot reg) (limit : Nat) (hlim : limit≤2^34)
    (f : Fin r → Fin limit → Nib × Fin limit)
    (start : arg tokens 0<limit)
    (correct : ∀ (j : Fin r) (a : Fin limit), arg tokens j.val=a.val →
      physicalDigit (geom j) (old j) reg c (tokens j.val) =
        (writeNum reg (f j a).1.val,withAcc (tokens j.val) (f j a).2.val)) :
    (∀ j, j≤r → arg tokens j<limit) ∧
      ∀ j : Fin r, ∃ a : Fin limit, arg tokens j.val=a.val ∧
        (readWord updated reg hi j).val=(f j a).1.val ∧
        arg tokens (j.val+1)=(f j a).2.val := by
  have single (j : Fin r) (a : Fin limit) (ha : arg tokens j.val=a.val) :
      (readWord updated reg hi j).val=(f j a).1.val ∧
        arg tokens (j.val+1)=(f j a).2.val := by
    have e := H.step j
    dsimp only at e
    rw [correct j a ha] at e
    have ew := congrArg Prod.fst e
    have et := congrArg Prod.snd e
    change (writeNum reg (f j a).1.val).apply (old j) = updated j at ew
    change withAcc (tokens j.val) (f j a).2.val = tokens (j.val+1) at et
    constructor
    · change num (updated j) reg=(f j a).1.val
      rw [←ew]
      exact num_write_of_lt hi (f j a).1.isLt (old j)
    · unfold arg
      rw [←et]
      exact acc_read _ _ (Nat.lt_of_lt_of_le (f j a).2.isLt hlim)
  have bound : ∀ j, j≤r → arg tokens j<limit := by
    intro j
    induction j with
    | zero => intro _; exact start
    | succ j ih =>
      intro hj
      let k : Fin r := ⟨j,by omega⟩
      let a : Fin limit := ⟨arg tokens j,ih (by omega)⟩
      have E := (single k a rfl).2
      exact E ▸ (f k a).2.isLt
  exact ⟨bound,fun j => ⟨⟨arg tokens j.val,bound j.val (by omega)⟩,rfl,single j _ rfl⟩⟩

theorem physical_add_word {r : Nat} {geom : Fin r → LongGeometry} {old updated : Fin r → BitVec LW}
    {i a b : Nat} {tokens : Nat → Payload}
    (H : DigitSweep geom old updated i (.add a b) tokens)
    (hi : WordSlot i) (ha : WordSlot a) (hb : WordSlot b) (h0 : arg tokens 0=0) :
    val (readWord updated i hi)+16^r*arg tokens r=
      val (readWord old a ha)+val (readWord old b hb) := by
  apply add_word
  · intro h
    simp [valJ,h0]
  · intro j hj
    let f (q : Fin r) (c : Fin 2) := addStep (nib (old q) a ha) (nib (old q) b hb) c
    obtain ⟨c,hc,hy,hh⟩ := (follows H hi 2 (by decide) f (by simp [h0])
      (fun q c hc => add_row (geom q) (old q) i a b (tokens q.val) ha hb c hc)).2 ⟨j,hj⟩
    exact ⟨c,hc,hy,hh⟩

theorem physical_sub_word {r : Nat} {geom : Fin r → LongGeometry} {old updated : Fin r → BitVec LW}
    {i a b : Nat} {tokens : Nat → Payload}
    (H : DigitSweep geom old updated i (.sub a b) tokens)
    (hi : WordSlot i) (ha : WordSlot a) (hb : WordSlot b) (h0 : arg tokens 0=0) :
    val (readWord updated i hi)+val (readWord old b hb)=
      val (readWord old a ha)+16^r*arg tokens r := by
  apply sub_word
  · intro h
    simp [valJ,h0]
  · intro j hj
    let f (q : Fin r) (c : Fin 2) := subStep (nib (old q) a ha) (nib (old q) b hb) c
    obtain ⟨c,hc,hy,hh⟩ := (follows H hi 2 (by decide) f (by simp [h0])
      (fun q c hc => sub_row (geom q) (old q) i a b (tokens q.val) ha hb c hc)).2 ⟨j,hj⟩
    refine ⟨c,hc,?_⟩
    let q : Fin r := ⟨j,hj⟩
    change (readWord updated i hi q).val+(nib (old q) b hb).val+c.val =
      (nib (old q) a ha).val+16*arg tokens (q.val+1)
    rw [hy,hh]
    exact (sub_digit_fact (nib (old q) a ha) (nib (old q) b hb) c).1

theorem physical_shift_word {r : Nat} {geom : Fin r → LongGeometry} {old updated : Fin r → BitVec LW}
    {i a : Nat} {tokens : Nat → Payload}
    (H : DigitSweep geom old updated i (.shl3 a) tokens)
    (hi : WordSlot i) (ha : WordSlot a) (h0 : arg tokens 0=0) :
    val (readWord updated i hi)+16^r*arg tokens r=8*val (readWord old a ha) := by
  apply shl3_word
  · intro h
    simp [valJ,h0]
  · intro j hj
    let f (q : Fin r) (c : Fin 8) := shl3Step (nib (old q) a ha) c
    obtain ⟨c,hc,hy,hh⟩ := (follows H hi 8 (by decide) f (by simp [h0])
      (fun q c hc => shift_row (geom q) (old q) i a (tokens q.val) ha c hc)).2 ⟨j,hj⟩
    exact ⟨c,hc,hy,hh⟩

end L4.BStarPhysicalWordSem
