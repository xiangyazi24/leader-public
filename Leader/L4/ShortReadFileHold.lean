import Leader.L4.ShortReadResult
import Leader.L4.ShortResetCycle

namespace L4.ShortReadFileHold
open AllSizeProtocol MISByteCodec PhysicalCustody ShortReadResult
open ShortResetMIS1Ring (header pairHeader pairIn)
set_option maxHeartbeats 1200000

private def ph (raw : BitVec 96) := get raw 81 2 (by decide)
private def op (raw : BitVec 96) := get raw 78 3 (by decide)

/-- Any valid non-RESET issue, held wait, or successful STAGE/SEAL
reply leaves the committed READ file alone. A failed operation may
reset it, and an accepted READ replaces it. -/
def FileSafe (raw : BitVec 96) (t : Token) : Prop :=
    (ph raw=1 ∧ 0<op raw ∧ op raw<7) ∨
    (ph raw=2 ∧ op raw<7 ∧
      ((t.tag=1 ∨ t.tag=2) ∨
        ((op raw=4 ∨ op raw=5) ∧ t.tag=3 ∧ t.opcode=op raw ∧
          t.fault=false ∧ t.outcome≠1)))

private theorem empty_file (b : BitVec 96) : fileField.read ((Patch.empty 96).apply b)=fileField.read b := by
  have H : (Patch.empty 96).apply b=b := by
    change b &&& BitVec.allOnes 96 ||| 0=b
    rw [BitVec.and_allOnes]
    exact BitVec.or_zero
  rw [H]

theorem safe_source_patch (raw : BitVec 96) (t : Token) (b : BitVec 96)
    (H : FileSafe raw t) :
    fileField.read ((source raw t).1.apply b)=fileField.read b := by
  rcases H with ⟨P,O,L⟩|⟨P,L,H⟩
  · change get raw 81 2 (by decide)=1 at P
    change 0<get raw 78 3 (by decide) at O
    change get raw 78 3 (by decide)<7 at L
    have A : get raw 78 3 (by decide)≠0 := by omega
    have B : get raw 78 3 (by decide)≠7 := by omega
    have F : (source raw t).1=(Patch.empty 96).compose (put 81 2 (by decide) 2) := by
      simp [source,P,A,B]
    rw [F,Patch.compose_apply]
    exact (Field.read_other_assign fileField (lane 81 2 (by decide)) (2 : BitVec 2)
      ((Patch.empty 96).apply b) (.inl (by decide))).trans (empty_file b)
  · rcases H with H|⟨L,T,U,V,W⟩
    · rw [source_wait_holds raw t P L H]
      exact empty_file b
    · have hp : get raw 81 2 (by decide)=2 := P
      have HT : get raw 78 3 (by decide)=4 ∨ get raw 78 3 (by decide)=5 := L
      have F : ∃ k : Nat, (source raw t).1=phaseOp 1 k := by
        rcases HT with O|O
        · exact ⟨5,by simp [source,hp,O,T,show t.opcode=4 from U.trans O,V,W]⟩
        · exact ⟨6,by simp [source,hp,O,T,show t.opcode=5 from U.trans O,V,W]⟩
      obtain ⟨k,F⟩ := F
      rw [F]
      exact Field.read_other_assign fileField (lane 78 5 (by decide))
        (BitVec.ofNat 5 (8+k)) b (.inl (by decide))

theorem safe_door_retains_file {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (H : FileSafe (x (rightNeighbor e)).mis1 (oldK true (x (rightNeighbor e)).mis1 0)) :
    fileField.read (rawNext s x e (rightNeighbor e)).mis1 =
      fileField.read (x (rightNeighbor e)).mis1 := by
  obtain ⟨b,B,A⟩ := ShortControllerMIS1.source_door_raw x e sep eligible
  have U := A fileField (by decide)
  rw [U]
  split
  · exact (safe_source_patch _ _ b H).trans (B fileField (by decide) (by decide))
  · rename_i t E
    rw [show putK 0 t=(kField 0).assign (encode t) from rfl,
      Field.read_other_assign fileField (kField 0) _ _ (.inr (by decide))]
    exact (safe_source_patch _ _ b H).trans (B fileField (by decide) (by decide))

theorem outgoing_retains_file {s n : Nat} (x : Raw s n) (e : Fin n)
    (head : header x e=true) :
    fileField.read (rawNext s x e e).mis1 = fileField.read (x e).mis1 := by
  let h := pairHeader x e
  let old := pairIn x e
  have work : fileField.read (rawNext s x e e).mis1 =
      fileField.read ((MISByteRows.row h old).1.apply old.1) := by
    rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
      simp [rawNext,AllSizeS1Geometry.step]]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have no : ¬ShortGeo.mis.owned (72+i) := by
      intro O
      have L := O.1
      change 93≤72+i at L
      omega
    simp only [fileField,lane,Field.read,BitVec.getLsbD_extractLsb',hi,
      decide_true,Bool.true_and]
    exact ((ShortGeo.work_agrees_outside _ 3 h old (BStarShort.shortMIS h old) _ no).1).trans
      (BStarShort.mis_apply_outside h old (72+i) (.inl (by omega)))
  refine work.trans ?_
  exact (show fileField.read ((MISByteRows.row (true,header x (rightNeighbor e))
      ((x e).mis1,(x (rightNeighbor e)).mis1)).1.apply (x e).mis1)=
        fileField.read (x e).mis1 by
    exact ShortResetRow.source_field_outgoing_pair fileField (by decide) (by decide) _ _ _) |>.trans rfl
    |> fun Q => by simpa only [h,old,pairHeader,pairIn,head] using Q

/-- Every mark before the next stage is retained. Only the actual owner
door needs a safe source branch; other marks cannot modify this file. -/
def FileSafeBefore {s n : Nat} (i : Fin n) : Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w =>
    (rightNeighbor e=i → FileSafe (x i).mis1 (oldK true (x i).mis1 0)) ∧
    FileSafeBefore i (rawNext s x e) w

theorem safe_fileTrace {s n : Nat} (N : 5≤n) (x : Raw s n) (i : Fin n)
    (Q : H2Ready x) (H : header x i=true) (w : List (Fin n))
    (S : FileSafeBefore i x w) :
    fileField.read (rawRun x w i).mis1=fileField.read (x i).mis1 := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have keep : fileField.read (rawNext s x e i).mis1=fileField.read (x i).mis1 := by
      by_cases A : i=e
      · subst i
        exact outgoing_retains_file x e H
      · by_cases B : rightNeighbor e=i
        · subst i
          exact safe_door_retains_file x e (Ne.symm A) H (S.1 rfl)
        · rw [ShortResetMIS1Ring.reset_remote_frame_raw x e i A (Ne.symm B)]
    have H' : header (rawNext s x e) i=true :=
      (PhysicalCustody.H1.raw_h1_selected_frozen N x e i Q.1).trans H
    exact (ih (rawNext s x e) (h2_ready_closed N x e Q) H' S.2).trans keep

end L4.ShortReadFileHold
