import Leader.L4.Compiler.StagesClock
import Leader.L4.Compiler.NativeSpec
import Leader.L4.Compiler.GeneratedLoad

namespace L4.Compiler.Native
open Interp

private theorem bool_eq {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p=decide q := by
  by_cases hp : p
  · simp [hp,h.mp hp]
  · have hn : ¬q := fun hq => hp (h.mpr hq)
    simp [hp,hn]

private theorem upperSide_eq (r t u : Nat) (ht : t<modulus r) (hu : u<modulus r) :
    rootCSide r t ((t+1)%modulus r) u =
      (decide (t+2≤u) && !(decide (t=modulus r/2) && decide (u=modulus r-1))) := by
  by_cases h : t<u
  · have m : (t+1)%modulus r=t+1 := Nat.mod_eq_of_lt (by omega)
    have o : (decide (t+1<u) : Bool)=decide (t+2≤u) := bool_eq (by omega)
    simp [rootCSide,modulus] at m ⊢
    simp [h,m,o] <;> rfl
  · have k : ¬t+2≤u := by omega
    simp [rootCSide,h,k]

private theorem proposal_eq (r t u : Nat) (b : Bool) (hu : u<modulus r) :
    propVal r t u b =
      if b && decide (u+1<modulus r/2) && decide (u+1<t) then u+1 else t := by
  have m : 0<modulus r := Nat.pow_pos (by decide)
  have q : (decide (u<modulus r/2-1) : Bool)=decide (u+1<modulus r/2) :=
    bool_eq (by omega)
  have half := Nat.div_le_self (modulus r) 2
  change (if (b && decide (u<modulus r/2-1)) && decide ((u+1)%modulus r<t)
      then (u+1)%modulus r else t)=_
  rw [q]
  by_cases h : u+1<modulus r/2
  · have k : (u+1)%modulus r=u+1 := Nat.mod_eq_of_lt (by omega)
    rw [k]
  · simp [h]

private theorem near_eq (r t u : Nat) (b : Bool)
    (ht : t<modulus r) (hu : u<modulus r) :
    clearSideVal r t ((t+1)%modulus r) u b =
      (decide (u≤t+1) && decide (t≤u+1) && (decide (u≤t) || !b)) := by
  change ((decide (u=t) || (decide (u<t) && decide ((u+1)%modulus r=t)) ||
      (decide (t<u) && decide ((t+1)%modulus r=u))) && (!decide (t<u) || !b))=_
  rcases Nat.lt_trichotomy u t with h|h|h
  · have m : (u+1)%modulus r=u+1 := Nat.mod_eq_of_lt (by omega)
    have eq : (decide (u+1=t) : Bool)=decide (t≤u+1) := bool_eq (by omega)
    simp [h,show ¬u=t by omega,show ¬t<u by omega,show u≤t by omega,show u≤t+1 by omega,m,eq]
  · subst u; simp
  · have m : (t+1)%modulus r=t+1 := Nat.mod_eq_of_lt (by omega)
    have eq : (decide (t+1=u) : Bool)=decide (u≤t+1) := bool_eq (by omega)
    simp [h,show ¬u=t by omega,show ¬u<t by omega,show ¬u≤t by omega,show t≤u+1 by omega,m,eq]

def rawSucc (r : Nat) (C : NativeRecord) := (C.tick+1)%modulus r
def clockReset (r : Nat) (L C R : NativeRecord) :=
  resetVal r C.tick (rawSucc r C) L.tick R.tick C.err L.err R.err
def clockLeast (r : Nat) (L C R : NativeRecord) :=
  minVal (propVal r C.tick L.tick L.err) (propVal r C.tick R.tick R.err)
def clockProp (r : Nat) (L C R : NativeRecord) : Bool := decide (clockLeast r L C R<C.tick)
def clockClear (r : Nat) (L C R : NativeRecord) :=
  C.err && (clearSideVal r C.tick (rawSucc r C) L.tick L.err &&
    clearSideVal r C.tick (rawSucc r C) R.tick R.err)
def clockInc (r : Nat) (L C R : NativeRecord) :=
  let sv := successor (modulus r) C.tick
  !C.err && ((decide (L.tick=C.tick) || decide (L.tick=sv)) &&
    (decide (R.tick=C.tick) || decide (R.tick=sv)))

private theorem minVal_eq (a b : Nat) : minVal a b=min a b := by
  by_cases h : a<b
  · simp [minVal,h,Nat.le_of_lt h]
  · by_cases eq : a=b
    · subst b
      simp [minVal]
    · simp [minVal,h,Nat.min_def,show ¬a≤b by omega]

theorem clock_spec (r : Nat) (L C R : NativeRecord)
    (hL : L.tick<modulus r) (hC : C.tick<modulus r) (hR : R.tick<modulus r) :
    nativeClock (modulus r) L C R =
      if clockReset r L C R then .reset
      else if clockProp r L C R then .propagate (clockLeast r L C R)
      else if clockClear r L C R then .clear
      else if clockInc r L C R then .inc (successor (modulus r) C.tick)
      else .hold := by
  unfold nativeClock clockReset clockClear clockProp clockLeast clockInc
  dsimp only
  unfold resetVal rawSucc
  change _=_
  rw [upperSide_eq r _ _ hC hL,upperSide_eq r _ _ hC hR,
    proposal_eq r _ _ _ hL,proposal_eq r _ _ _ hR,
    near_eq r _ _ _ hC hL,near_eq r _ _ _ hC hR]
  simp [rootEVal,minVal_eq,Bool.and_assoc]

set_option linter.unusedSimpArgs false in
/-- Raw increment eligibility is not an increment when an earlier
sanitation guard wins. These are the actual S10/S13 winner bits. -/
theorem native_inc_iff (r : Nat) (L C R : NativeRecord)
    (hL : L.tick<modulus r) (hC : C.tick<modulus r) (hR : R.tick<modulus r) (t : Nat) :
    nativeClock (modulus r) L C R=.inc t ↔
      clockReset r L C R=false ∧ clockProp r L C R=false ∧ clockClear r L C R=false ∧
      clockInc r L C R=true ∧ successor (modulus r) C.tick=t := by
  rw [clock_spec r L C R hL hC hR]
  cases hs : clockReset r L C R <;> cases hp : clockProp r L C R <;>
    cases hc : clockClear r L C R <;> cases hi : clockInc r L C R <;>
    simp [hs,hp,hc,hi]

/-- Exactly the S0--S2 clock-facing registers. The other registers
are intentionally left unconstrained by this stage interface. -/
structure ClockInputs (r : Nat) (L C R : NativeRecord) (regs : List Value) : Prop where
  length : regs.length=98
  zero : readReg regs 0=.word 0
  one : readReg regs 1=.word 1
  half : readReg regs 2=.word (modulus r/2)
  max : readReg regs 4=.word (modulus r-1)
  ff : readReg regs 5=.boolean false
  tt : readReg regs 6=.boolean true
  eL : readReg regs 16=.boolean L.err
  tL : readReg regs 29=.word L.tick
  eC : readReg regs 45=.boolean C.err
  tC : readReg regs 58=.word C.tick
  eR : readReg regs 74=.boolean R.err
  tR : readReg regs 87=.word R.tick
  rawS : readReg regs 94=.word (rawSucc r C)
  succ : readReg regs 97=.word (successor (modulus r) C.tick)

def rootCodes := stageRoot 98 58 45 94 0 2 4 29 16 87 74
def propCodes := stageProp 138 58 1 2 29 16 87 74
def clearCodes := stageClear 161 58 45 94 1 29 16 87 74
def incCodes := stageInc 205 45 58 97 29 87
def prioCodes := stagePrio 218 137 160 204 217 45 0 5 6 158 58 97
def clockCodes := rootCodes ++ propCodes ++ clearCodes ++ incCodes ++ prioCodes

theorem clockCodes_literal : clockCodes=(literal.drop 98).take 128 := by decide

structure ClockFacts (r : Nat) (L C R : NativeRecord) (regs : List Value) : Prop where
  length : regs.length=226
  reset : readReg regs 137=.boolean (clockReset r L C R)
  least : readReg regs 158=.word (clockLeast r L C R)
  prop : readReg regs 160=.boolean (clockProp r L C R)
  clear : readReg regs 204=.boolean (clockClear r L C R)
  inc : readReg regs 217=.boolean (clockInc r L C R)
  err : ∀ δ, readReg regs 221=.boolean
    (finishNative (heightMod r) L C R (nativeClock (modulus r) L C R) δ).err
  tick : ∀ δ, readReg regs 225=.word
    (finishNative (heightMod r) L C R (nativeClock (modulus r) L C R) δ).tick

private theorem clockLeast_bound {r} {L C R : NativeRecord} (h : C.tick<modulus r) :
    clockLeast r L C R<modulus r := by
  have a (u : Nat) (b : Bool) : propVal r C.tick u b<modulus r := by
    unfold propVal
    split
    · exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    · exact h
  unfold clockLeast minVal
  split <;> apply a

set_option linter.unusedSimpArgs false in
theorem clock_finish {r : Nat} (hr : 3≤r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (L C R : NativeRecord) (regs : List Value) (init : ClockInputs r L C R regs)
    (hL : L.tick<modulus r) (hC : C.tick<modulus r) (hR : R.tick<modulus r) :
    ClockFacts r L C R (runCodes T bank regs clockCodes) := by
  let s1 := runCodes T bank regs rootCodes
  let s2 := runCodes T bank s1 propCodes
  let s3 := runCodes T bank s2 clearCodes
  let s4 := runCodes T bank s3 incCodes
  let s5 := runCodes T bank s4 prioCodes
  have len1 : s1.length=138 := by
    change (runCodes T bank regs rootCodes).length=_
    rw [runCodes_length,init.length]
    decide
  have k1 (i : Nat) (h : i<regs.length) : readReg s1 i=readReg regs i :=
    runCodes_prefix T bank regs rootCodes i h
  have len2 : s2.length=161 := by
    change (runCodes T bank s1 propCodes).length=_
    rw [runCodes_length,len1]
    decide
  have k2 (i : Nat) (h : i<s1.length) : readReg s2 i=readReg s1 i :=
    runCodes_prefix T bank s1 propCodes i h
  have len3 : s3.length=205 := by
    change (runCodes T bank s2 clearCodes).length=_
    rw [runCodes_length,len2]
    decide
  have k3 (i : Nat) (h : i<s2.length) : readReg s3 i=readReg s2 i :=
    runCodes_prefix T bank s2 clearCodes i h
  have len4 : s4.length=218 := by
    change (runCodes T bank s3 incCodes).length=_
    rw [runCodes_length,len3]
    decide
  have k4 (i : Nat) (h : i<s3.length) : readReg s4 i=readReg s3 i :=
    runCodes_prefix T bank s3 incCodes i h
  have len5 : s5.length=226 := by
    change (runCodes T bank s4 prioCodes).length=_
    rw [runCodes_length,len4]
    decide
  have k5 (i : Nat) (h : i<s4.length) : readReg s5 i=readReg s4 i :=
    runCodes_prefix T bank s4 prioCodes i h
  have s1spec := stageRoot_spec hr T bank hT regs 98 init.length
    58 45 94 0 2 4 29 16 87 74
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    C.tick (rawSucc r C) L.tick R.tick C.err L.err R.err
    init.tC init.eC init.rawS init.zero init.half init.max init.tL init.eL init.tR init.eR
    hC (Nat.mod_lt _ (Nat.pow_pos (by decide))) hL hR
  have rs : readReg s1 137=.boolean (clockReset r L C R) := s1spec.2.2
  have s2spec := stageProp_spec hr T bank hT s1 138 len1
    58 1 2 29 16 87 74
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    C.tick L.tick R.tick L.err R.err
    (by rw [k1 58 (by rw [init.length]; decide)]; exact init.tC)
    (by rw [k1 1 (by rw [init.length]; decide)]; exact init.one)
    (by rw [k1 2 (by rw [init.length]; decide)]; exact init.half)
    (by rw [k1 29 (by rw [init.length]; decide)]; exact init.tL)
    (by rw [k1 16 (by rw [init.length]; decide)]; exact init.eL)
    (by rw [k1 87 (by rw [init.length]; decide)]; exact init.tR)
    (by rw [k1 74 (by rw [init.length]; decide)]; exact init.eR)
    hC hL hR
  have s3spec := stageClear_spec hr T bank hT s2 161 len2
    58 45 94 1 29 16 87 74
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    C.tick (rawSucc r C) L.tick R.tick C.err L.err R.err
    (by rw [k2 58 (by rw [len1]; decide), k1 58 (by rw [init.length]; decide)]; exact init.tC)
    (by rw [k2 45 (by rw [len1]; decide), k1 45 (by rw [init.length]; decide)]; exact init.eC)
    (by rw [k2 94 (by rw [len1]; decide), k1 94 (by rw [init.length]; decide)]; exact init.rawS)
    (by rw [k2 1 (by rw [len1]; decide), k1 1 (by rw [init.length]; decide)]; exact init.one)
    (by rw [k2 29 (by rw [len1]; decide), k1 29 (by rw [init.length]; decide)]; exact init.tL)
    (by rw [k2 16 (by rw [len1]; decide), k1 16 (by rw [init.length]; decide)]; exact init.eL)
    (by rw [k2 87 (by rw [len1]; decide), k1 87 (by rw [init.length]; decide)]; exact init.tR)
    (by rw [k2 74 (by rw [len1]; decide), k1 74 (by rw [init.length]; decide)]; exact init.eR)
    hC (Nat.mod_lt _ (Nat.pow_pos (by decide))) hL hR
  have boundSucc : successor (modulus r) C.tick < modulus r := by
    have m : 0<modulus r := Nat.pow_pos (by decide)
    unfold successor
    split <;> omega
  have s4spec := stageInc_spec T bank hT s3 205 len3
    45 58 97 29 87
    (by decide) (by decide) (by decide) (by decide) (by decide)
    C.err C.tick (successor (modulus r) C.tick) L.tick R.tick
    (by rw [k3 45 (by rw [len2]; decide), k2 45 (by rw [len1]; decide), k1 45 (by rw [init.length]; decide)]; exact init.eC)
    (by rw [k3 58 (by rw [len2]; decide), k2 58 (by rw [len1]; decide), k1 58 (by rw [init.length]; decide)]; exact init.tC)
    (by rw [k3 97 (by rw [len2]; decide), k2 97 (by rw [len1]; decide), k1 97 (by rw [init.length]; decide)]; exact init.succ)
    (by rw [k3 29 (by rw [len2]; decide), k2 29 (by rw [len1]; decide), k1 29 (by rw [init.length]; decide)]; exact init.tL)
    (by rw [k3 87 (by rw [len2]; decide), k2 87 (by rw [len1]; decide), k1 87 (by rw [init.length]; decide)]; exact init.tR)
    hC boundSucc hL hR
  have lep : readReg s2 158=.word (clockLeast r L C R) := s2spec.2.2.1
  have prp : readReg s2 160=.boolean (clockProp r L C R) := s2spec.2.2.2
  have clr : readReg s3 204=.boolean (clockClear r L C R) := s3spec
  have inc : readReg s4 217=.boolean (clockInc r L C R) := s4spec
  have spec := stagePrio_spec T bank hT s4 218 len4
    137 160 204 217 45 0 5 6 158 58 97
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (clockReset r L C R) (clockProp r L C R) (clockClear r L C R) (clockInc r L C R) C.err
    (clockLeast r L C R) C.tick (successor (modulus r) C.tick)
    (by rw [k4 137 (by rw [len3]; decide),k3 137 (by rw [len2]; decide),k2 137 (by rw [len1]; decide)]; exact rs)
    (by rw [k4 160 (by rw [len3]; decide),k3 160 (by rw [len2]; decide)]; exact prp)
    (by rw [k4 204 (by rw [len3]; decide)]; exact clr)
    inc
    (by rw [k4 45 (by rw [len3]; decide), k3 45 (by rw [len2]; decide), k2 45 (by rw [len1]; decide), k1 45 (by rw [init.length]; decide)]; exact init.eC)
    (by rw [k4 0 (by rw [len3]; decide), k3 0 (by rw [len2]; decide), k2 0 (by rw [len1]; decide), k1 0 (by rw [init.length]; decide)]; exact init.zero)
    (by rw [k4 5 (by rw [len3]; decide), k3 5 (by rw [len2]; decide), k2 5 (by rw [len1]; decide), k1 5 (by rw [init.length]; decide)]; exact init.ff)
    (by rw [k4 6 (by rw [len3]; decide), k3 6 (by rw [len2]; decide), k2 6 (by rw [len1]; decide), k1 6 (by rw [init.length]; decide)]; exact init.tt)
    (by rw [k4 158 (by rw [len3]; decide),k3 158 (by rw [len2]; decide)]; exact lep)
    (by rw [k4 58 (by rw [len3]; decide), k3 58 (by rw [len2]; decide), k2 58 (by rw [len1]; decide), k1 58 (by rw [init.length]; decide)]; exact init.tC)
    (by rw [k4 97 (by rw [len3]; decide), k3 97 (by rw [len2]; decide), k2 97 (by rw [len1]; decide), k1 97 (by rw [init.length]; decide)]; exact init.succ)
    (clockLeast_bound hC) hC boundSucc
  have unfoldCodes : runCodes T bank regs clockCodes=s5 := by
    simp only [clockCodes,runCodes_append,s1,s2,s3,s4,s5]
  rw [unfoldCodes]
  refine ⟨len5,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [k5 137 (by rw [len4]; decide),k4 137 (by rw [len3]; decide),k3 137 (by rw [len2]; decide),k2 137 (by rw [len1]; decide)]
    exact rs
  · rw [k5 158 (by rw [len4]; decide),k4 158 (by rw [len3]; decide),k3 158 (by rw [len2]; decide)]
    exact lep
  · rw [k5 160 (by rw [len4]; decide),k4 160 (by rw [len3]; decide),k3 160 (by rw [len2]; decide)]
    exact prp
  · rw [k5 204 (by rw [len4]; decide),k4 204 (by rw [len3]; decide)]
    exact clr
  · rw [k5 217 (by rw [len4]; decide)]
    exact inc
  · intro δ
    rw [clock_spec r L C R hL hC hR]
    have h := spec.1
    change readReg s5 221=_ at h
    rw [h]
    cases hs : clockReset r L C R <;> cases hp : clockProp r L C R <;>
      cases hc : clockClear r L C R <;> cases hi : clockInc r L C R <;>
      simp only [hs,hp,hc,hi,finishNative,Bool.false_eq_true,if_false,if_true]
  · intro δ
    rw [clock_spec r L C R hL hC hR]
    have h := spec.2
    change readReg s5 225=_ at h
    rw [h]
    cases hs : clockReset r L C R <;> cases hp : clockProp r L C R <;>
      cases hc : clockClear r L C R <;> cases hi : clockInc r L C R <;>
      simp only [hs,hp,hc,hi,finishNative,Bool.false_eq_true,if_false,if_true]

theorem clock_inputs_of_load {r : Nat} {bank : Bank} {regs : List Value}
    (h : LoadFacts r bank regs) :
    ClockInputs r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2) regs :=
  ⟨h.length,h.zero,h.one,h.half,h.max,h.ff,h.tt,h.bit 0 0,h.word 0 0,
    h.bit 1 0,h.word 1 0,h.bit 2 0,h.word 2 0,h.succRaw,h.succ⟩

def loadClockCodes := loadCodes ++ clockCodes

set_option maxRecDepth 4096 in
theorem loadClockCodes_literal : loadClockCodes=literal.take 226 := by decide

theorem decode_tick_bound (r : Nat) (bank : Bank) (q : Fin 3) :
    (decodeBank r bank q).tick < modulus r := by
  unfold decodeBank
  dsimp only
  split
  · exact pow16_pos' _
  · exact Nat.mod_lt _ (pow16_pos' _)

theorem clock_run {r : Nat} (hr : 3≤r) (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank) :
    ClockFacts r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2)
      (runCodes T bank [] (literal.take 226)) := by
  rw [←loadClockCodes_literal,loadClockCodes,runCodes_append]
  exact clock_finish hr T bank hT _ _ _ _ (clock_inputs_of_load (load_spec hr T bank hT))
    (decode_tick_bound r bank 0) (decode_tick_bound r bank 1) (decode_tick_bound r bank 2)

end L4.Compiler.Native
