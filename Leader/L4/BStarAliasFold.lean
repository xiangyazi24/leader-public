import Leader.L4.BStarCmpReceipt

/-! Exact receipt-local pending fold for the accepted compiler alias
subsequence. Prior arithmetic receipt semantics are premises. -/
namespace L4.BStarAliasFold
open AllSizeProtocol BStarTrace BStarLongArithmetic BStarLongLayout
open L4.Compiler.Native L4.Compiler.Interp

def BoolRep (x : BitVec LW) (xs : Pending) (regs : List Value) (i : Nat) : Prop :=
  ∀ b, readReg regs i=.boolean b → newest x xs i=b.toNat

def CmpRep (x : BitVec LW) (xs : Pending) (regs : List Value) (i : Nat) : Prop :=
  newest x xs i/2=((readReg regs i).asWord == 1).toNat ∧
    newest x xs i%2=((readReg regs i).asWord == 2).toNat

def WellRep (x : BitVec LW) (xs : Pending) (regs : List Value) (cmp : Nat → Prop) : Prop :=
  ∀ i<regs.length, BoolRep x xs regs i ∧ (cmp i → CmpRep x xs regs i)

inductive AliasOK (bank : Bank) (old : BitVec LW) (cmp : Nat → Prop) (j : Nat) : Code → Prop
  | header (q : Fin 3) (i : Fin 9) (h : ((capturedHeader q i).read old).toNat=(bank.hdr q i).toNat) :
    AliasOK bank old cmp j (.header q i)
  | literal (b : Bool) : AliasOK bank old cmp j (.bconst b)
  | eq (i : Nat) (h : i<j) (t : cmp i) : AliasOK bank old cmp j (.cmpEq i)
  | lt (i : Nat) (h : i<j) (t : cmp i) : AliasOK bank old cmp j (.cmpLt i)

theorem exact_alias {r : Nat} (T : PrimTable r) (bank : Bank) (old : BitVec LW)
    (xs : Pending) (regs : List Value) (cmp : Nat → Prop) (c : Code)
    (R : WellRep old xs regs cmp) (C : AliasOK bank old cmp regs.length c) :
    ∃ b, aliasValue old xs c=some b.toNat ∧
      evalInstr (toInstr T bank c) regs=.boolean b := by
  cases C with
  | header q i H => exact ⟨bank.hdr q i,congrArg some H,rfl⟩
  | literal b => exact ⟨b,rfl,rfl⟩
  | eq i h t => exact ⟨_,congrArg some ((R i h).2 t).1,rfl⟩
  | lt i h t => exact ⟨_,congrArg some ((R i h).2 t).2,rfl⟩

theorem extend_rep (old : BitVec LW) (xs : Pending) (regs : List Value)
    (cmp : Nat → Prop) (b : Bool) (R : WellRep old xs regs cmp) (N : ¬cmp regs.length) :
    WellRep old ((regs.length,b.toNat)::xs) (regs++[.boolean b]) cmp := by
  intro i H
  rw [List.length_append,List.length_singleton] at H
  by_cases E : i=regs.length
  · subst i
    refine ⟨?_,fun h => (N h).elim⟩
    intro v V
    have P : readReg (regs++[Value.boolean b]) regs.length=.boolean b := by
      simp [readReg]
    rw [P] at V
    cases V
    simp [newest]
  · have I : i<regs.length := by omega
    have L := readReg_append_left regs [Value.boolean b] i I
    have M : newest old ((regs.length,b.toNat)::xs) i=newest old xs i := by
      simp [newest,show regs.length≠i from Ne.symm E]
    obtain ⟨A,B⟩ := R i I
    exact ⟨fun _ h => M.trans (A _ (L.symm ▸ h)),fun z => by simpa only [CmpRep,L,M] using B z⟩

inductive Segment (bank : Bank) (old : BitVec LW) (cmp : Nat → Prop) :
    Nat → List Code → Prop
  | nil (j : Nat) : Segment bank old cmp j []
  | cons {j c cs} (type : AliasOK bank old cmp j c) (new : ¬cmp j)
      (tail : Segment bank old cmp (j+1) cs) : Segment bank old cmp j (c::cs)

/-- Exact accepted evalProgramAux on a contiguous captured-header /
Boolean-literal / CMP projection subsequence, using newest pending
writes, not old packed register readback for an alias's operand. -/
theorem alias_fold {r : Nat} (T : PrimTable r) (bank : Bank) (old : BitVec LW)
    (cmp : Nat → Prop) (cs : List Code) (j : Nat) (regs : List Value) (xs : Pending)
    (H : Segment bank old cmp j cs) (L : regs.length=j) (R : WellRep old xs regs cmp) :
    WellRep old (aliases old j cs xs) (runCodes T bank regs cs) cmp := by
  induction H generalizing regs xs with
  | nil => exact R
  | @cons j c cs K N H ih =>
    have K' : AliasOK bank old cmp regs.length c := L ▸ K
    obtain ⟨b,A,B⟩ := exact_alias T bank old xs regs cmp c R K'
    change WellRep old (aliases old j (c::cs) xs)
      (evalProgramAux (regs++[evalInstr (toInstr T bank c) regs]) (cs.map (toInstr T bank))) cmp
    rw [aliases,A,B]
    have R' := extend_rep old xs regs cmp b R (L.symm ▸ N)
    rw [L] at R'
    exact ih _ _ (by simp [L]) R'

def OldBool (old : BitVec LW) (regs : List Value) (i : Nat) : Prop :=
  source old i=((readReg regs i).asBool).toNat

inductive HeadOK (old : BitVec LW) (regs : List Value) : Code → Prop
  | neg (a : Nat) : OldBool old regs a → HeadOK old regs (.not a)
  | and (a b : Nat) : OldBool old regs a → OldBool old regs b → HeadOK old regs (.and a b)
  | or (a b : Nat) : OldBool old regs a → OldBool old regs b → HeadOK old regs (.or a b)
  | mux (q a b : Nat) : OldBool old regs q → OldBool old regs a → OldBool old regs b →
      HeadOK old regs (.bmux q a b)
  | phase (a j : Nat) : source old a=(readReg regs a).asWord → HeadOK old regs (.phaseEq a j)

theorem exact_boolean_head {r : Nat} (T : PrimTable r) (bank : Bank) (old : BitVec LW)
    (regs : List Value) (c : Code) (payload : Nat) (H : HeadOK old regs c) :
    ∃ b, nodeResult old payload c=some b.toNat ∧ evalInstr (toInstr T bank c) regs=.boolean b := by
  cases H with
  | neg a A =>
    unfold OldBool at A
    refine ⟨_,?_,rfl⟩
    cases e : (readReg regs a).asBool <;> simp [nodeResult,A,e,evalBoolOp]
  | and a b A B =>
    unfold OldBool at A B
    refine ⟨_,?_,rfl⟩
    cases e : (readReg regs a).asBool <;> cases f : (readReg regs b).asBool <;>
      simp [nodeResult,A,B,e,f,evalBoolOp]
  | or a b A B =>
    unfold OldBool at A B
    refine ⟨_,?_,rfl⟩
    cases e : (readReg regs a).asBool <;> cases f : (readReg regs b).asBool <;>
      simp [nodeResult,A,B,e,f,evalBoolOp]
  | mux q a b Q A B =>
    unfold OldBool at Q A B
    refine ⟨_,?_,rfl⟩
    cases e : (readReg regs q).asBool <;>
      simp [nodeResult,Q,A,B,e,evalBoolOp]
  | phase a j A =>
    exact ⟨_,by simp [nodeResult,A,evalBoolOp],rfl⟩

/-- The pending expression used by acceptFile, for a Boolean head and
its accepted alias suffix. OldFile inputs are read before any pending
write; CMP aliases in the suffix read the accumulated overlay. -/
theorem receipt_boolean_segment {r : Nat} (T : PrimTable r) (bank : Bank)
    (old : BitVec LW) (regs : List Value) (cmp : Nat → Prop) (c : Code) (cs : List Code)
    (n : Nat) (H : HeadOK old regs c) (N : ¬cmp regs.length)
    (S : Segment bank old cmp (regs.length+1) cs) (R : WellRep old [] regs cmp) :
    let pending := (nodeResult old n c).toList.map (fun v => (regs.length,v))
    WellRep old (aliases old (regs.length+1) cs pending)
      (runCodes T bank regs (c::cs)) cmp := by
  dsimp only
  obtain ⟨b,A,B⟩ := exact_boolean_head T bank old regs c n H
  change WellRep old (aliases old (regs.length+1) cs
      ((nodeResult old n c).toList.map (fun v => (regs.length,v))))
    (runCodes T bank (regs++[evalInstr (toInstr T bank c) regs]) cs) cmp
  rw [A,B]
  exact alias_fold T bank old cmp cs _ _ _ S (by simp) (extend_rep old [] regs cmp b R N)

open BStarPhysicalDigitSem in
theorem extend_cmp (old : BitVec LW) (xs : Pending) (regs : List Value)
    (cmp : Nat → Prop) (a b : Nat) (R : WellRep old xs regs cmp) :
    WellRep old
      ((regs.length,cmpPack (decide (a=b)) (decide (a<b)))::xs)
      (regs++[.word (cmpCode a b)]) cmp := by
  intro i H
  rw [List.length_append,List.length_singleton] at H
  by_cases E : i=regs.length
  · subst i
    have P : readReg (regs++[Value.word (cmpCode a b)]) regs.length=.word (cmpCode a b) := by
      simp [readReg]
    constructor
    · intro v V
      rw [P] at V
      contradiction
    · intro _
      unfold CmpRep
      rw [P,BStarCmpReceipt.pending_head]
      have H (k : Nat) : (cmpCode a b==k)=decide (cmpCode a b=k) := by by_cases E : cmpCode a b=k <;> simp [E]
      simpa only [Value.asWord,H] using BStarCmpReceipt.projections a b
  · have I : i<regs.length := by omega
    have L := readReg_append_left regs [Value.word (cmpCode a b)] i I
    have M : newest old ((regs.length,cmpPack (decide (a=b)) (decide (a<b)))::xs) i=newest old xs i := by
      simp [newest,show regs.length≠i from Ne.symm E]
    obtain ⟨A,B⟩ := R i I
    exact ⟨fun _ h => M.trans (A _ (L.symm ▸ h)),fun z => by simpa only [CmpRep,L,M] using B z⟩

open BStarPhysicalDigitSem in
theorem receipt_cmp_segment {r : Nat} (T : PrimTable r) (bank : Bank)
    (sem : PrimSem T bank) (old : BitVec LW) (regs : List Value) (cmp : Nat → Prop)
    (i j : Nat) (cs : List Code) (a b q : Nat)
    (A : argW r (readArgs regs [i,j]) 0=a)
    (B : argW r (readArgs regs [i,j]) 1=b)
    (Q : q=cmpPack (decide (a=b)) (decide (a<b)))
    (S : Segment bank old cmp (regs.length+1) cs) (R : WellRep old [] regs cmp) :
    let pending := (nodeResult old q (.cmp i j)).toList.map (fun v => (regs.length,v))
    WellRep old (aliases old (regs.length+1) cs pending)
      (runCodes T bank regs (.cmp i j::cs)) cmp := by
  dsimp only
  have E : evalInstr (toInstr T bank (.cmp i j)) regs=.word (cmpCode a b) := by
    change Value.word (den T.cmp (readArgs regs [i,j]))=_
    rw [sem.cmp,A,B]
  change WellRep old (aliases old (regs.length+1) cs [(regs.length,q)])
    (runCodes T bank (regs++[evalInstr (toInstr T bank (.cmp i j)) regs]) cs) cmp
  rw [E,Q]
  exact alias_fold T bank old cmp cs _ _ _ S (by simp) (extend_cmp old [] regs cmp a b R)

/-- The refinement's pending overlay is literally the one lowered by
nonterminal acceptFile. This equality retains the actual write order
and control update, including named idempotent scalar writes. -/
theorem accept_nonfinal (old : BitVec LW) (op : Nat) (p : BStarLongToken.Payload)
    (i : Nat) (c : Code) (N : nodeOf op=some i) (G : get i=some c) (H : op<407) :
    let pending := (nodeResult old p.argument.toNat c).toList.map (fun v => (i,v))
    let xs := aliases old (i+1) (literal.drop (i+1)) pending
    acceptFile old op p =
      (BStarLongOutgoing.fuse (xs.reverse.map fun (a,v) => writeScalar a v)).compose
        (BStarLongDoor.schedule (op+1)) := by
  simp [acceptFile,N,G,H]

#print axioms exact_alias
#print axioms alias_fold
#print axioms receipt_boolean_segment
#print axioms receipt_cmp_segment
#print axioms accept_nonfinal
end L4.BStarAliasFold
