import Leader.L4.BStarLongWork

/-! All non-routing work frames K1..K10, including padding. K0 is
excluded: source-door issue and repair do assign it. -/
namespace L4.BStarLongRoutingFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims

def Frame (p : Patch LW) : Prop :=
  ∀ i, 1192 ≤ i → i < 1712 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤1192 ∨ 1712≤f.offset) : Frame (f.assign b) := by
  intro i lo hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  rcases h with h|h <;> omega

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
  left
  have h := BStarLongRegisters.range_bound BStarLongRegisters.wordWidths j
  rw [BStarLongRegisters.manifest_registers.2.1] at h
  exact Nat.le_trans h (by decide)

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) :=
  assign _ _ (.inr (Nat.le_add_right 1712 _ |> fun h =>
    Nat.le_trans h (Nat.add_le_add_right (by decide : 1712≤1764) _)))

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
  apply compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
  exact assign _ _ (.inr (by decide))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
  exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  unfold issued
  split
  · exact compose (assign _ _ (.inr (by decide))) h
  · exact h

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (.inr (by decide))
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (.inr (by decide))
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (.inr (by decide))
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (.inr (by decide))
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (.inr (by decide))
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (.inr (by decide))
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (.inr (by decide))
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (.inr (by decide))
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
  · exact compose (compose (sc _) (compose (compose (assign _ _ (.inr (by decide)))
      (assign _ _ (.inr (by decide)))) (assign _ _ (.inr (by decide))))) (schedule_frame _)
  · exact repair_frame

open BStarLongOutgoing BStarLongPublication in
theorem stage_frame (head inside : Bool) (x : BitVec LW) (d : Descriptor) (n : Nat) :
    Frame (stagePatch head inside x d n) := by
  have hd (b : Bool) (bank : Fin 3) :
      ∀ q∈dimDigits x b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inr (by simp [bankDigit,bankPart,bankBase]; omega))
  have hh (b : Bool) (bank : Fin 3) :
      ∀ q∈dimHeaders n b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inr (by simp [bankHeader,bankPart,bankBase]; omega))
  unfold stagePatch
  apply fuse
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with hi|he
  · cases inside <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
        if_true,List.mem_append] at hi
    exact hi.elim (hd false d.b0 q) (hd true d.b1 q)
  · cases head <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
        if_true,List.mem_append,List.mem_singleton] at he
    rcases he with (he|he)|rfl
    · exact hh false d.b0 q he
    · exact hh true d.b1 q he
    · exact assign _ _ (.inr (by decide))

open BStarLongOutgoing BStarLongPublication in
theorem execute_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (execute g j x p).row := by
  have dc : Frame descriptorClear :=
    compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  have sf (d : Descriptor) : Frame (sealField.assign (packOptional (some d))) :=
    assign _ _ (.inr (by decide))
  have setterF (b : Fin 3) : Frame (setter b) :=
    compose (compose (assign _ _ (.inr (by decide)))
      (assign _ _ (.inr (by decide)))) (assign _ _ (.inr (by decide)))
  have cf (head : Bool) (d : Descriptor) (b : Fin 3) :
      Frame (commit head j x d b).1 := by
    unfold commit
    split
    · exact setterF _
    · exact zero
  simp only [execute,hold,refuse]
  split
  · exact zero
  split
  · exact dc
  split
  · split
    · exact zero
    · split
      · exact zero
      · exact stage_frame _ _ _ _ _
  split
  · split
    · exact zero
    · split
      · exact sf _
      · exact zero
  split
  · split
    · exact zero
    · split
      · split
        · exact cf _ _ _
        · exact zero
      · exact zero
  · exact zero

end L4.BStarLongRoutingFrame
