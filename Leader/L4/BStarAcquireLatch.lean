import Leader.L4.BStarLongGrant

/-! The packed ACQUIRE success latch is bit 33. Valid successful captures
write only below it; any losing capture clears it irreversibly. -/
namespace L4.BStarAcquireLatch
open BStarLongGrant BStarLongCommand BStarLongToken

theorem replace_div (u v lo wi : Nat) :
    replaceLane u v lo wi / 2^(lo+wi) = u / 2^(lo+wi) := by
  have L : 0<2^lo := Nat.two_pow_pos lo
  have W : 0<2^wi := Nat.two_pow_pos wi
  have h₁ := Nat.mod_lt u L
  have h₂ := Nat.succ_le_of_lt (Nat.mod_lt v W)
  have h₃ := Nat.mul_le_mul_right (2^lo) h₂
  change (v%2^wi+1)*2^lo ≤ _ at h₃
  rw [Nat.add_mul, Nat.one_mul] at h₃
  have h : (v%2^wi)*2^lo + u%2^lo < 2^(lo+wi) := by
    rw [Nat.pow_add, Nat.mul_comm (2^lo)]
    omega
  unfold replaceLane
  rw [Nat.add_assoc, Nat.mul_comm (u / 2^(lo+wi)), Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt h, Nat.add_zero]

theorem replace_div_high (u v lo wi top : Nat) (h : lo+wi≤top) :
    replaceLane u v lo wi / 2^top = u / 2^top := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,replace_div]

private theorem replace_lt (u v lo wi top : Nat) (h : lo+wi≤top) (hu : u<2^top) :
    replaceLane u v lo wi < 2^top := by
  have A := replace_div_high u v lo wi top h
  have B : replaceLane u v lo wi / 2^top < 1 := by rw [A,Nat.div_eq_of_lt hu]; decide
  simpa using (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos top)).mp B

def latch (p : Payload) : Bool := p.argument.toNat / 2^33 % 2 == 1

theorem capture_latch (s : Fin 3) (h : BitVec 9) (j : Fin 3) (p : Payload) (wins : Bool) :
    latch (captureFields s h j p wins) = (latch p && wins) := by
  have H : 31-2*j.val+2≤33 := by omega
  have J : 18-9*j.val+9≤33 := by omega
  cases wins with
  | false =>
    have A : p.argument.toNat % 2^33 < 2^33 := Nat.mod_lt _ (Nat.two_pow_pos _)
    have B : p.argument.toNat % 2^33 < 2^34 :=
      Nat.lt_of_lt_of_le A (Nat.pow_le_pow_right (by decide) (by decide))
    change ((BitVec.ofNat 34 (p.argument.toNat%2^33)).toNat/2^33%2==1) = (latch p && false)
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt B,Nat.div_eq_of_lt A,Bool.and_false]
    decide
  | true =>
    simp only [captureFields,if_true,latch,BitVec.toNat_ofNat,Bool.and_true]
    rw [Nat.mod_eq_of_lt (replace_lt _ _ _ _ 34 (Nat.le_trans J (by decide))
      (replace_lt _ _ _ _ 34 (Nat.le_trans H (by decide)) p.argument.isLt)),
      replace_div_high _ _ _ _ _ J, replace_div_high _ _ _ _ _ H]

theorem finish_success (p : Payload) (hf : p.fault=0) (ho : p.opcode.toNat=acquire)
    (hl : latch p=true) :
    finish p=.reply {p with race:=0,argument:=BitVec.ofNat 34 (p.argument.toNat%2^33)} := by
  unfold finish
  change (if p.fault != 0 then fault true else if p.opcode.toNat==acquire then
    if latch p then _ else _ else _) = _
  simp [hf,ho,hl,low]

theorem finish_failure (p : Payload) (hf : p.fault=0) (ho : p.opcode.toNat=acquire)
    (hl : latch p=false) :
    finish p=.reply {p with race:=0,outcome:=1,argument:=0} := by
  unfold finish
  change (if p.fault != 0 then fault true else if p.opcode.toNat==acquire then
    if latch p then _ else _ else _) = _
  simp [hf,ho,hl]

structure Visit where
  selector : Fin 3
  headers : BitVec 9
  incidence : Fin 3
  wins : Bool

def Visit.apply (v : Visit) (p : Payload) : Payload :=
  captureFields v.selector v.headers v.incidence p v.wins

theorem fold_latch (vs : List Visit) (p : Payload) :
    latch (vs.foldl (fun x v => v.apply x) p) = (latch p && vs.all Visit.wins) := by
  induction vs generalizing p with
  | nil => simp
  | cons v vs ih => rw [List.foldl_cons,ih,Visit.apply,capture_latch,List.all_cons,Bool.and_assoc]

private theorem fold_fault_opcode (vs : List Visit) (p : Payload) :
    ((vs.foldl (fun x v => v.apply x) p).fault,
     (vs.foldl (fun x v => v.apply x) p).opcode) = (p.fault,p.opcode) := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    rw [List.foldl_cons,ih]
    cases H : v.wins <;> simp [Visit.apply,captureFields,H]

/-- Exact terminal projection after any finite itinerary (even with repeated
visits). A dirty false latch cannot recover; successful terminal projection
retains the existing outcome tag, rather than synthesizing it. -/
theorem finish_itinerary (vs : List Visit) (p : Payload) (hf : p.fault=0)
    (ho : p.opcode.toNat=acquire) :
    let q := vs.foldl (fun x v => v.apply x) p
    finish q =
      if latch p && vs.all Visit.wins then
        .reply {q with race:=0,argument:=BitVec.ofNat 34 (q.argument.toNat%2^33)}
      else .reply {q with race:=0,outcome:=1,argument:=0} := by
  let q := vs.foldl (fun x v => v.apply x) p
  have fields := fold_fault_opcode vs p
  have F : q.fault=0 := (congrArg Prod.fst fields).trans hf
  have O : q.opcode.toNat=acquire := (congrArg (fun x => x.2.toNat) fields).trans ho
  dsimp only
  rw [← fold_latch vs p]
  cases L : latch q
  · exact finish_failure q F O L
  · exact finish_success q F O L

#print axioms finish_itinerary
#print axioms capture_latch
#print axioms finish_success
#print axioms finish_failure
end L4.BStarAcquireLatch
