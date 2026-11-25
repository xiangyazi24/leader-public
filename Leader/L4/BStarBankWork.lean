import Leader.L4.BStarBankCapture

/-! Protocol work below the bank slab cannot alter an operand.
The source door writes K0 as well as file fields but neither reaches
the bank/selector, even on malformed raw data and idempotent writes. -/
namespace L4.BStarBankWork
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongClaims

def Frame (p : Patch LW) : Prop := ∀ i, 2222 ≤ i → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i h
  simp [Patch.compose,hp i h,hq i h]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2222) : Frame (f.assign b) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  omega

theorem of_beforeBank {q : Patch LW} (h : Frame q) (b : Fin 3) :
    BStarBankCapture.Protected b q := by
  exact ⟨fun i lo _ => h i (by unfold bankBase at lo; omega), fun i lo _ => h i (by omega)⟩

theorem fuse_loop (l : List (Patch LW)) (p : Patch LW) (hp : Frame p)
    (h : ∀ q∈l, Frame q) : Frame (l.foldl Patch.compose p) := by
  induction l generalizing p with
  | nil => exact hp
  | cons a l ih =>
    exact ih _ (compose hp (h a List.mem_cons_self)) (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem fuse (l : List (Patch LW)) (h : ∀ q∈l, Frame q) :
    Frame (BStarLongOutgoing.fuse l) := fuse_loop l _ zero h

theorem number (j n : Nat) : Frame (BStarLongArithmetic.writeNum j n) := by
  apply assign
  have h := BStarLongRegisters.range_bound BStarLongRegisters.wordWidths j
  rw [BStarLongRegisters.manifest_registers.2.1] at h
  exact Nat.le_trans h (by decide)

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) := by
  apply assign
  exact Nat.le_trans (BStarLongRegisters.scalar_before_choice j) (by decide)

theorem numeric_visit (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (BStarLongArithmetic.visit g j x p).1 := by
  unfold BStarLongArithmetic.visit
  split
  · exact zero
  split
  · exact zero
  split
  · exact zero
  rename_i idx _ c _
  cases c <;> simp only [BStarLongArithmetic.physicalDigit]
  all_goals first | exact zero | exact number _ _ | (split <;> first | exact zero | exact number _ _)

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem schedule_frame (op : Nat) : Frame (schedule op) := by
  unfold schedule
  apply compose (compose (assign _ _ (by decide)) (assign _ _ (by decide)))
  exact assign _ _ (by decide)

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (by decide)) (assign _ _ (by decide)))
  exact compose (assign _ _ (by decide)) (assign _ _ (by decide))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (by decide)) (assign _ _ (by decide))
  unfold issued
  split
  · exact compose (assign _ _ (by decide)) h
  · exact h

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (by decide)
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (by decide)
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (by decide)
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (by decide)
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (by decide)
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (by decide)
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (by decide)
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (by decide)
  unfold afterReply
  dsimp only
  repeat first
    | split
    | with_reducible exact repair_frame
    | with_reducible exact schedule_frame _
    | with_reducible apply compose
    | with_reducible exact ca _
    | with_reducible exact ch _
    | with_reducible exact sh _
    | with_reducible exact sd _
    | with_reducible exact co _
    | with_reducible exact nd _
    | with_reducible exact de _
    | with_reducible exact fl _

set_option maxHeartbeats 1200000 in
open BStarLongDoor BStarLongArithmetic in
theorem accept_frame (x : BitVec LW) (op : Nat) (p : Payload) :
    Frame (acceptFile x op p) := by
  unfold acceptFile
  split
  · exact repair_frame
  split
  · exact repair_frame
  rename_i i _ c _
  dsimp only
  have sc : ∀ ys : Pending, Frame (BStarLongOutgoing.fuse
      (ys.reverse.map fun (i,y) => writeScalar i y)) := by
    intro ys
    apply fuse
    intro q hq
    obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hq
    exact scalar a b
  split
  · exact compose (sc _) (schedule_frame _)
  split
  · exact compose (compose (sc _) (compose (compose (assign _ _ (by decide))
      (assign _ _ (by decide))) (assign _ _ (by decide)))) (schedule_frame _)
  · exact repair_frame

open BStarLongDoor in
theorem door_frame (x : BitVec LW) (t : Token) (q : Patch LW)
    (h : oldDoor x t=.write q) : Frame q := by
  unfold oldDoor at h
  dsimp only at h
  repeat first
    | contradiction
    | (injection h with e; rw [←e]; exact repair_frame)
    | (injection h with e; rw [←e]; exact issue_frame _ _)
    | (injection h with e; rw [←e]; exact reply_frame _ _ _)
    | split at h

end L4.BStarBankWork
