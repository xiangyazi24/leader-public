import Leader.L4.BStarBitNoAbort
import Leader.L4.BStarStageCandidateRetention
import Leader.L4.BStarLongLandingFrame

namespace L4.BStarSealPackedFrame
set_option maxRecDepth 4096
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongClaims

def Frame (p : Patch LW) : Prop := ∀ i, 2206 ≤ i → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i h
  simp [Patch.compose,hp i h,hq i h]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2206) : Frame (f.assign b) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  omega

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

open BStarLongLandingFrame (publicationBit readPublication read_of_frame assign_frame)
open BStarBankTrace (sideFlag beforeOutgoing)
open BStarLongTransport BStarLongEvents BStarLongOutgoing BStarLongCommand

private abbrev PubFrame := BStarLongLandingFrame.Frame

private theorem lift_frame {q : Patch LW} (h : Frame q) : PubFrame q := by
  intro j J
  unfold publicationBit at J
  rcases J with J|J <;> exact h j (by omega)

private theorem join_frame {p q : Patch LW} (P : PubFrame p) (Q : PubFrame q) : PubFrame (p.compose q) := by
  intro i hi
  simp [Patch.compose,P i hi,Q i hi]

def NoLatch (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (s : Side) : Prop :=
  ∀ C p, (C,.advance p)∈actualOffers g raw → C.source.side=s → C.source.occurrence.val=1 →
    let q := (beforeOutgoing g raw C p).2
    q.fault=0 →
      q.opcode.toNat≠1 ∧ q.opcode.toNat≠stageOp ∧ q.opcode.toNat≠sealOp ∧ q.opcode.toNat≠commitOp

private theorem execute_frame (g : LongGeometry) (j : Fin 11) (raw : BitVec LW) (q : Payload)
    (N : j.val=1 → q.fault=0 →
      q.opcode.toNat≠1 ∧ q.opcode.toNat≠stageOp ∧ q.opcode.toNat≠sealOp ∧ q.opcode.toNat≠commitOp) :
    PubFrame (execute g j raw q).row := by
  by_cases K : j.val=1
  · by_cases H : q.fault=0
    · obtain ⟨R,T,E,C⟩ := N K H
      have none : (execute g j raw q).row=.empty LW := by
        simp [execute,K,H,R,T,E,C,hold]
      rw [none]
      exact lift_frame zero
    · rw [faulty_hold _ _ _ _ H]
      exact lift_frame zero
  · rw [noncenter_hold _ _ _ _ K]
    exact lift_frame zero

private def SideFrame (s : Side) (w : Bool × Patch LW) : Prop :=
  w.1=sideFlag s → PubFrame w.2

private theorem selected_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (H : NoLatch g raw s) (o : CmdOffer) (M : o∈actualOffers g raw) :
    ∀ w∈(selected g raw o).work, SideFrame s w := by
  obtain ⟨c,t⟩ := o
  cases t <;> simp only [selected]
  all_goals try (intro w hw; simp at hw; done)
  · split
    · intro w hw; simp at hw
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact lift_frame (door_frame _ _ _ ‹_›)
    · intro w hw _
      obtain rfl := List.mem_singleton.mp hw
      exact lift_frame (accept_frame _ _ _)
  · rename_i p
    intro w hw eq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl
    · exact lift_frame (numeric_visit _ _ _ _)
    · have hs : c.source.side=s := by
        cases h : c.source.side <;> cases s <;> simp_all [sideFlag]
      exact execute_frame _ _ _ _ (H c p M hs)

private theorem selected_fold (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (s : Side) (H : NoLatch g raw s) (os : List CmdOffer)
    (sub : ∀ o∈os,o∈actualOffers g raw) (acc : Selected)
    (ini : ∀ w∈acc.work,SideFrame s w) :
    ∀ w∈(os.foldl (fun a o => Selected.append a (selected g raw o)) acc).work,SideFrame s w := by
  induction os generalizing acc with
  | nil => exact ini
  | cons o os ih =>
    apply ih (fun a ha => sub a (List.mem_cons_of_mem _ ha))
    intro w hw
    exact (List.mem_append.mp hw).elim (ini w)
      (selected_frame g raw s H o (sub o List.mem_cons_self) w)

private theorem grant_all (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, PubFrame t.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t ht
  have T (s : Side) (H : t∈(BStarLongGrant.siteWrites g x os s).map Write.patch) : PubFrame t.2 := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp H
    obtain ⟨j,_,G⟩ := List.mem_filterMap.mp hw
    split at G
    · cases G
      exact BStarLongLandingFrame.grant_field_frame j _
    · contradiction
  exact ht.elim (T .left) (T .right)

theorem work_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (head : (geometry g s).axes.h6=true) (H : NoLatch g x s) :
    PubFrame (lane (sideFlag s) (longWork g x)) := by
  have atSide : ∀ w∈(longTrace g x).assignments, SideFrame s w := by
    intro w hw
    unfold longTrace at hw
    simp only [List.mem_append] at hw
    rcases hw with (((((hf|hc)|hg)|hd)|hw)|hl)
    · obtain ⟨q,_,rfl⟩ := List.mem_map.mp hf
      exact fun _ => BStarLongLandingFrame.k_frame q
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · cases s
        · exact fun _ => by simp [nonheader,geometry] at head ⊢; rw [if_pos head]; exact lift_frame zero
        · intro E; contradiction
      · cases s
        · intro E; contradiction
        · exact fun _ => by simp [nonheader,geometry] at head ⊢; rw [if_pos head]; exact lift_frame zero
    · exact fun _ => grant_all g x _ w hg
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
      obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hq
      exact fun _ => BStarLongLandingFrame.writeAt_frame a u
    · exact selected_fold g x s H _ (fun _ e => e) _ (by simp) w hw
    · obtain ⟨q,_,rfl⟩ := List.mem_map.mp hl
      exact fun _ => BStarLongLandingFrame.k_frame q
  intro i hi
  rw [exact_assignment_mask]
  apply Bool.eq_false_iff.mpr
  intro M
  obtain ⟨w,hw,hf⟩ := List.any_eq_true.mp M
  obtain ⟨hs,hm⟩ := Bool.and_eq_true_iff.mp hf
  have F := atSide w hw (beq_iff_eq.mp hs) i hi
  simp [F] at hm

open BStarCaptureInterval (joinedPatch joinedRead joined_read)

private theorem frame_pair (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (w q : Pair (Patch LW))
    (W : PubFrame (lane (sideFlag s) w))
    (Q : PubFrame (lane (sideFlag s) q)) :
    PubFrame (lane (sideFlag s) (LongDoorGuard.pairGuard manifest g x
      (w.1.compose q.1,w.2.compose q.2))) := by
  cases s
  · exact join_frame W Q
  · change PubFrame (LongDoorGuard.guard manifest g.2.axes.h6 x.2 (w.2.compose q.2))
    unfold LongDoorGuard.guard
    split
    · exact join_frame (join_frame W Q) (lift_frame repair_frame)
    · exact join_frame W Q

theorem joined_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (head : (geometry g s).axes.h6=true) (H : NoLatch g x s) :
    PubFrame (lane (sideFlag s) (joinedPatch g x)) := by
  have W := work_frame g x s head H
  have Q : PubFrame (lane (sideFlag s) (longScratch g x)) := by
    intro i hi
    unfold publicationBit at hi
    have I := longScratch_mask g x i
    cases s
    · exact Bool.eq_false_iff.mpr (fun m => by have J := I.1.mp m; omega)
    · exact Bool.eq_false_iff.mpr (fun m => by have J := I.2.mp m; omega)
  unfold joinedPatch
  exact frame_pair g x s _ _ W Q

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def RingNoLatch (x : X) (e i : Fin n) : Prop :=
  ∀ s, i=site e s →
    NoLatch (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) s

theorem ring_frame (x : X) (e i : Fin n) (sep : e≠rightNeighbor e)
    (head : oldH6 B x i=true) (H : RingNoLatch hp x e i) :
    readPublication (step x e i).long=readPublication (x i).long := by
  by_cases A : i=e
  · subst i
    simp only [AllSizeS1Geometry.step,if_true]
    rw [show (largePair B (x e,x (rightNeighbor e))).1.long =
        joinedRead (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) .left from
          joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp _ .left]
    exact read_of_frame _ _ (joined_frame _ _ .left head (H .left rfl))
  · by_cases U : i=rightNeighbor e
    · subst i
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true]
      rw [show (largePair B (x e,x (rightNeighbor e))).2.long =
          joinedRead (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) .right from
            joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp _ .right]
      exact read_of_frame _ _ (joined_frame _ _ .right head (H .right rfl))
    · simp [AllSizeS1Geometry.step,A,U]

/-- Whole-word latch and selector preservation. This excludes
a competing selected latch writer on the old pair and does not assume
any later mark publishes. Actual grant custody remains a separate input. -/
theorem word_frame (x : X) (w : List (Fin n)) (i : Fin n)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (safe : ∀ u e v,w=u++e::v →
      oldH6 B (run x u) i=true ∧ RingNoLatch hp (run x u) e i) :
    readPublication (run x w i).long=readPublication (x i).long := by
  induction w generalizing x with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨head,H⟩ := safe [] e es rfl
    exact (ih (step x e) (fun u a v E => safe (e::u) a v (congrArg (List.cons e) E))).trans
      (ring_frame hp x e i (sep e) head H)

end L4.BStarSealPackedFrame
