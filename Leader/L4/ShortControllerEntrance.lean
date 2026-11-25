import Leader.L4.MISByteCodec

namespace L4.ShortControllerEntrance
open AllSizeProtocol MISByteCodec

/-- The controller-only arbitrary WAIT-exit classification. WAIT holds only
on F/T. Every other exit either returns directly to RESET0 or advances
exactly one opcode. In particular a valid COMMIT reply cannot bypass RESET0. -/
theorem wait_exit (raw : BitVec 96) (t : Token) (op : Nat)
    (hp : get raw 81 2 (by decide)=2) (ho : get raw 78 3 (by decide)=op)
    (lt : op<7) (hf : t.tag≠1) (ht : t.tag≠2) :
    source raw t = (resetSource,some E) ∨
      op<6 ∧ source raw t =
        (if op=3 then
          (((phaseOp 1 (op+1)).compose (put 72 6 (by decide) t.payload)).compose
            (put 68 4 (by decide) 0),some E)
        else (phaseOp 1 (op+1),some E)) := by
  have H7 : op≠7 := by omega
  by_cases bad : (t.tag != 3 || t.opcode != op || t.fault || t.outcome==1)=true
  · exact Or.inl (by simp [source,hp,ho,H7,hf,ht,bad])
  have good : (t.tag != 3 || t.opcode != op || t.fault || t.outcome==1)=false :=
    Bool.eq_false_iff.mpr bad
  have ops : op=0 ∨ op=1 ∨ op=2 ∨ op=3 ∨ op=4 ∨ op=5 ∨ op=6 := by omega
  rcases ops with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inr ⟨by decide,by simp [source,hp,ho,hf,ht,good]⟩
  · exact Or.inr ⟨by decide,by simp [source,hp,ho,hf,ht,good]⟩
  · by_cases H : t.payload=1
    · exact Or.inr ⟨by decide,by simp [source,hp,ho,hf,ht,H,good]⟩
    · exact Or.inl (by simp [source,hp,ho,hf,ht,H,good])
  · exact Or.inr ⟨by decide,by simp [source,hp,ho,hf,ht,good]⟩
  · exact Or.inr ⟨by decide,by simp [source,hp,ho,hf,ht,good]⟩
  · exact Or.inr ⟨by decide,by simp [source,hp,ho,hf,ht,good]⟩
  · exact Or.inl (by simp [source,hp,ho,hf,ht,good])

/-- The source does not inspect the old K0 byte to select a launch once
it is in a valid ISSUE phase. -/
theorem issue_fresh (raw : BitVec 96) (t : Token) (op : Nat)
    (hp : get raw 81 2 (by decide)=1) (ho : get raw 78 3 (by decide)=op)
    (lt : op<7) :
    source raw t =
      ((if op=0 then resetSource else .empty 96).compose (put 81 2 (by decide) 2),
        some {tag:=2,opcode:=op,payload:=if op=3 then 64 else if 4≤op then issuedDescriptor raw else 0}) := by
  have H7 : op≠7 := by omega
  simp [source,hp,ho,H7]

theorem invalid_controller_resets (raw : BitVec 96) (t : Token)
    (h : get raw 81 2 (by decide)=0 ∨ get raw 81 2 (by decide)=3 ∨
      get raw 78 3 (by decide)=7) :
    source raw t=(resetSource,some E) := by
  rcases h with h|h|h <;> simp [source,h]

/-- The five-bit source word records ISSUE with opcode 0 as 8. -/
def pc (x : BitVec 96) : Nat := get x 78 5 (by decide)

private theorem reset_pc (x : BitVec 96) : pc (resetSource.apply x)=8 := by
  let a : Field 96 5 := lane 78 5 (by decide)
  let b : Field 96 26 := lane 57 26 (by decide)
  let v : BitVec 26 := BitVec.ofNat 26 (2^24)
  have read_zero : a.read ((b.assign v).apply x)=a.read ((b.assign v).apply 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := (b.inMask v (a.offset+i)).mpr
      (show b.offset≤a.offset+i ∧ a.offset+i<b.offset+26 from by
        change 57≤78+i ∧ 78+i<57+26
        omega)
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    rw [Patch.write _ _ _ hh,Patch.write _ _ _ hh]
  exact (congrArg BitVec.toNat read_zero).trans (by decide)

private theorem phase_pc (x : BitVec 96) (op : Nat) (lt : op<8) :
    pc ((phaseOp 1 op).apply x)=8+op := by
  unfold pc MISByteCodec.get phaseOp put
  rw [Field.read_assign,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

private theorem read_phase_pc (x : BitVec 96) (reply : Token) :
    pc (((phaseOp 1 4).compose (put 72 6 (by decide) reply.payload)).compose
      (put 68 4 (by decide) 0) |>.apply x)=12 := by
  let a : Field 96 5 := lane 78 5 (by decide)
  let b : Field 96 6 := lane 72 6 (by decide)
  let c : Field 96 4 := lane 68 4 (by decide)
  rw [Patch.compose_apply,Patch.compose_apply]
  change (a.read ((c.assign 0).apply ((b.assign (BitVec.ofNat 6 reply.payload)).apply
    ((phaseOp 1 4).apply x)))).toNat=12
  rw [Field.read_other_assign a c _ _ (.inr (by decide)),
    Field.read_other_assign a b _ _ (.inr (by decide))]
  exact phase_pc x 4 (by decide)

/-- Exact post-WAIT transition on controller bits, even when an arbitrary
other old-pair patch precedes the controller patch. -/
theorem wait_exit_next_pc (raw base : BitVec 96) (t : Token) (op : Nat)
    (hp : get raw 81 2 (by decide)=2) (ho : get raw 78 3 (by decide)=op)
    (lt : op<7) (hf : t.tag≠1) (ht : t.tag≠2) :
    pc ((source raw t).1.apply base)=8 ∨
      op<6 ∧ pc ((source raw t).1.apply base)=8+(op+1) := by
  rcases wait_exit raw t op hp ho lt hf ht with H|⟨L,H⟩
  · exact Or.inl (by rw [H]; exact reset_pc base)
  · right
    refine ⟨L,?_⟩
    by_cases T : op=3
    · rw [H,if_pos T,T]
      exact read_phase_pc base t
    · rw [H,if_neg T]
      exact phase_pc base (op+1) (by omega)

/-- For each nonreset exiting door, the remaining number of such exits
strictly decreases. There are at most 6-op before the reset, not seven
nonreset exits. Holds (waiting on F/T) are intentionally not charged. -/
theorem wait_exit_debt (raw base : BitVec 96) (t : Token) (op : Nat)
    (hp : get raw 81 2 (by decide)=2) (ho : get raw 78 3 (by decide)=op)
    (lt : op<7) (hf : t.tag≠1) (ht : t.tag≠2)
    (noReset : pc ((source raw t).1.apply base)≠8) :
    op<6 ∧ 6-(pc ((source raw t).1.apply base)-8)<6-op := by
  rcases wait_exit_next_pc raw base t op hp ho lt hf ht with H|⟨L,H⟩
  · exact (noReset H).elim
  · rw [H]
    omega

#print axioms wait_exit_next_pc
#print axioms wait_exit_debt
#print axioms wait_exit
#print axioms issue_fresh
#print axioms invalid_controller_resets
end L4.ShortControllerEntrance
