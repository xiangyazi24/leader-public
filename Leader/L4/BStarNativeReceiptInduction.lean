import Leader.L4.BStarAliasRoster

/-! Arithmetic receipt induction for the literal roster. This does
not assert that the physical history supplies the head certificate:
its numeric input file, COPY load, primitive geometry/carries, and
packed frame have to be connected to the actual chronological rows. -/
namespace L4.BStarNativeReceiptInduction
open BStarAliasRoster BStarAliasFold BStarLongArithmetic
open AllSizeProtocol BStarTrace BStarLongLayout
open L4.Compiler.Native L4.Compiler.Interp

theorem bounds {k : Nat} (K : k<395) : start k<start (k+1) ∧ start (k+1)≤474 := by
  have H := valid_chunk K
  unfold legalChunk at H
  simp only [Bool.and_eq_true] at H
  exact ⟨of_decide_eq_true H.1.1.1.1,of_decide_eq_true H.1.1.1.2⟩

theorem chunk_cons {k : Nat} (K : k<395) (c : Code) (G : get (start k)=some c) :
    chunk k=c::suffix k := by
  obtain ⟨A,B⟩ := bounds K
  have I : start k<literal.length := by rw [literal_length]; omega
  have E : literal[start k]=c := by
    change literal[start k]?=some c at G
    rw [List.getElem?_eq_getElem I] at G
    exact Option.some.inj G
  unfold chunk suffix
  rw [List.drop_eq_getElem_cons I,E,
    show start (k+1)-start k=(start (k+1)-start k-1)+1 by omega,
    List.take_succ_cons,Nat.add_sub_cancel]

def regsBefore {r : Nat} (T : PrimTable r) (bank : Bank) (k : Nat) : List Value :=
  runCodes T bank [] (literal.take (start k))

theorem prefix_zero {r : Nat} (T : PrimTable r) (bank : Bank) : regsBefore T bank 0=[] := by
  unfold regsBefore
  rw [show start 0=0 by decide +kernel]
  rfl

theorem prefix_length {r : Nat} (T : PrimTable r) (bank : Bank) {k : Nat}
    (K : k≤395) : (regsBefore T bank k).length=start k := by
  have B : start k≤474 := by
    cases k with
    | zero => decide +kernel
    | succ k => exact (bounds (k:=k) (by omega)).2
  simp only [regsBefore,runCodes_length,List.length_nil,Nat.zero_add,List.length_take,
    literal_length,Nat.min_eq_left B]

theorem prefix_step {r : Nat} (T : PrimTable r) (bank : Bank) {k : Nat}
    (K : k<395) : regsBefore T bank (k+1)=runCodes T bank (regsBefore T bank k) (chunk k) := by
  unfold regsBefore
  rw [←partition_prefix (k:=k+1) (by omega),←partition_prefix (k:=k) (by omega)]
  rw [List.range_succ,List.flatMap_append,runCodes_append]
  simp

theorem prefix_final {r : Nat} (T : PrimTable r) (bank : Bank) :
    regsBefore T bank 395=runCodes T bank [] literal := by
  rw [regsBefore,←partition_prefix (by decide),partition]

/-- The actual one-head overlay, formed before the same-receipt aliases. -/
def headPending (old : BitVec LW) (k : Nat) (payload : BStarLongToken.Payload)
    (c : Code) : Pending :=
  (nodeResult old payload.argument.toNat c).toList.map (fun v => (start k,v))

/-- One physical chronological receipt's obligations, with all data
tied to the same old image and externally supplied genuine receipt.
`Rep` may also track a distributed numeric file, not just this scalar
header. The next image may be taken at the next true receipt (so its
certificate includes retention across any intervening raw marks). -/
structure Receipt {r : Nat} (T : PrimTable r) (bank : Bank)
    {Image : Type} (Rep : Image → List Value → Prop)
    (k : Nat) (old fresh : Image) (wire : Image → BitVec LW) where
  code : Code
  code_eq : get (start k)=some code
  head : Value
  payload : BStarLongToken.Payload
  head_exact : ∀ regs, regs.length=start k → Rep old regs →
    head=evalInstr (toInstr T bank code) regs
  capture : ∀ q i, ((capturedHeader q i).read (wire old)).toNat=(bank.hdr q i).toNat
  pending_exact : ∀ regs, regs.length=start k → Rep old regs →
    WellRep (wire old) (headPending (wire old) k payload code) (regs++[head]) literalCmp
  store : ∀ regs, regs.length=start k → Rep old regs →
    let completed := runCodes T bank (regs++[head]) (suffix k)
    WellRep (wire old) (aliases (wire old) (start k+1)
      (literal.drop (start k+1)) (headPending (wire old) k payload code)) completed literalCmp →
      Rep fresh completed

theorem receipt_step {r : Nat} {T : PrimTable r} {bank : Bank}
    {Image : Type} {Rep : Image → List Value → Prop} {wire : Image → BitVec LW}
    {old fresh : Image} {k : Nat} (K : k<395)
    (R : Receipt T bank Rep k old fresh wire) {regs : List Value}
    (L : regs.length=start k) (H : Rep old regs) :
    Rep fresh (runCodes T bank regs (chunk k)) := by
  rw [chunk_cons K R.code R.code_eq]
  have E := R.head_exact regs L H
  have M : (regs++[R.head]).length=start k+1 := by simp [L]
  have F := roster_alias_run T bank (wire old) K (regs++[R.head]) (headPending (wire old) k R.payload R.code)
    R.capture M (R.pending_exact regs L H)
  have S := R.store regs L H F
  change Rep fresh (runCodes T bank
    (regs++[evalInstr (toInstr T bank R.code) regs]) (suffix k))
  rwa [←E]

/-- The complete accepted 395-receipt induction. The old images must
be on one and the same chronological tape; this theorem does not
conjure actual rows, their numeric slots, or their COPY initialization. -/
theorem run_receipts {r : Nat} (T : PrimTable r) (bank : Bank)
    {Image : Type} (Rep : Image → List Value → Prop) (wire : Image → BitVec LW)
    (image : Nat → Image)
    (initial : Rep (image 0) [])
    (steps : ∀ k<395, Receipt T bank Rep k (image k) (image (k+1)) wire) :
    (∀ k≤395, Rep (image k) (regsBefore T bank k)) ∧
      Rep (image 395) (runCodes T bank [] literal) := by
  have P : ∀ k≤395, Rep (image k) (regsBefore T bank k) := by
    intro k
    induction k with
    | zero => intro _; simpa only [prefix_zero] using initial
    | succ k ih =>
      intro K
      have lt : k<395 := by omega
      rw [prefix_step T bank lt]
      exact receipt_step lt (steps k lt) (prefix_length T bank (by omega)) (ih (by omega))
  exact ⟨P,by simpa only [prefix_final] using P 395 (by decide)⟩

end L4.BStarNativeReceiptInduction
