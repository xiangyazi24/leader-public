import Leader.L4.BStarLongWork

/-! Local capture stability lemmas for the physical history. A
per-digit selected bank uses its owner's captured selector, not the
digit site's irrelevant local selector. -/
namespace L4.BStarBankCapture
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongPublication
open BStarLongOutgoing BStarLongToken

def BankFrame (b : Fin 3) (p : Patch LW) : Prop :=
  ∀ i, bankBase b≤i → i<bankBase b+45 → p.mask.getLsbD i=false

def SelFrame (p : Patch LW) : Prop :=
  ∀ i, 2360≤i → i<2362 → p.mask.getLsbD i=false

def Protected (b : Fin 3) (p : Patch LW) : Prop := BankFrame b p ∧ SelFrame p

theorem frame_empty (b : Fin 3) : Protected b (.empty LW) := by
  simp [Protected,BankFrame,SelFrame,Patch.empty]

theorem frame_compose {b : Fin 3} {p q : Patch LW} (hp : Protected b p) (hq : Protected b q) :
    Protected b (p.compose q) := by
  constructor
  · intro i l r
    simp [Patch.compose,hp.1 i l r,hq.1 i l r]
  · intro i l r
    simp [Patch.compose,hp.2 i l r,hq.2 i l r]

theorem frame_assign {n : Nat} (b : Fin 3) (f : Field LW n) (v : BitVec n)
    (h : f.offset+n≤bankBase b ∨ bankBase b+45≤f.offset)
    (s : f.offset+n≤2360 ∨ 2362≤f.offset) : Protected b (f.assign v) := by
  constructor
  · intro i lo hi
    apply Bool.eq_false_iff.mpr
    intro hmask
    have := (Field.inMask f v i).mp hmask
    rcases h with h|h <;> omega
  · intro i lo hi
    apply Bool.eq_false_iff.mpr
    intro hmask
    have := (Field.inMask f v i).mp hmask
    rcases s with s|s <;> omega

theorem frame_bankPart {n : Nat} {a b : Fin 3} (ne : a≠b)
    (lo : Nat) (h : lo+n≤45) (v : BitVec n) : Protected a ((bankPart b lo n h).assign v) := by
  have df : a.val≠b.val := fun e => ne (Fin.ext e)
  have ha := a.isLt
  have hb := b.isLt
  apply frame_assign
  · simp only [bankPart,bankBase]
    omega
  · left
    simp only [bankPart,bankBase]
    omega

theorem frame_stage_field (b : Fin 3) (v : BitVec 8) :
    Protected b (stage.assign v) := by
  apply frame_assign
  · left; simp only [stage,bankBase]; omega
  · left; decide

theorem frame_seal_field (b : Fin 3) (v : BitVec 8) :
    Protected b (sealField.assign v) := by
  apply frame_assign
  · left; simp only [sealField,bankBase]; omega
  · left; decide

theorem frame_fuse_loop (b : Fin 3) (ps : List (Patch LW)) (start : Patch LW)
    (hstart : Protected b start) (hps : ∀ p∈ps, Protected b p) :
    Protected b (ps.foldl Patch.compose start) := by
  induction ps generalizing start with
  | nil => exact hstart
  | cons p ps ih =>
    exact ih _ (frame_compose hstart (hps p List.mem_cons_self))
      (fun q hq => hps q (List.mem_cons_of_mem _ hq))

theorem frame_fuse (b : Fin 3) (ps : List (Patch LW)) (h : ∀ p∈ps, Protected b p) :
    Protected b (fuse ps) := frame_fuse_loop b ps _ (frame_empty b) h

theorem decode_valid {v : BitVec 7} {d : Descriptor} (h : BStarLongPublication.decode v=some d) :
    d.valid=true := by
  unfold BStarLongPublication.decode at h
  dsimp only at h
  repeat first | contradiction | split at h
  all_goals try contradiction
  injection h with he
  rw [←he]
  assumption

theorem complement_ne (d : Descriptor) (h : d.valid=true) :
    d.old≠d.b0 ∧ d.old≠d.b1 := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  have ba := beq_iff_eq.mp a
  have ca := beq_iff_eq.mp b
  have hv := d.old.isLt
  constructor <;> intro e <;> have ee := congrArg Fin.val e <;> omega

theorem stage_frames (d : Descriptor) (head inside : Bool) (x : BitVec LW) (n : Nat)
    (b : Fin 3) (h0 : b≠d.b0) (h1 : b≠d.b1) :
    Protected b (stagePatch head inside x d n) := by
  have digits (c : Bool) (a : Fin 3) (ne : b≠a) :
      ∀ q∈dimDigits x c a, Protected b q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    apply frame_bankPart ne
  have headers (c : Bool) (a : Fin 3) (ne : b≠a) :
      ∀ q∈dimHeaders n c a, Protected b q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    apply frame_bankPart ne
  unfold stagePatch
  apply frame_fuse
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with hi|he
  · cases inside <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
      if_true,List.mem_append] at hi
    exact hi.elim (digits false d.b0 h0 q) (digits true d.b1 h1 q)
  · cases head <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
      if_true,List.mem_append,List.mem_singleton] at he
    rcases he with (he|he)|rfl
    · exact headers false d.b0 h0 q he
    · exact headers true d.b1 h1 q he
    · exact frame_stage_field _ _

theorem selector_read {b : Fin 3} {q : Patch LW} (h : Protected b q) (x : BitVec LW) :
    selector.read (q.apply x)=selector.read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,selector]
  exact Patch.hold _ _ _ (h.2 _ (by omega) (by omega))

theorem digit_read {b : Fin 3} {q : Patch LW} (h : Protected b q) (x : BitVec LW)
    (f : Fin 9) : (bankDigit b f).read (q.apply x)=(bankDigit b f).read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,bankDigit,bankPart]
  exact Patch.hold _ _ _ (h.1 _ (by omega) (by omega))

theorem header_read {b : Fin 3} {q : Patch LW} (h : Protected b q) (x : BitVec LW)
    (f : Fin 9) : (bankHeader b f).read (q.apply x)=(bankHeader b f).read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,bankHeader,bankPart]
  exact Patch.hold _ _ _ (h.1 _ (by omega) (by omega))

theorem selected_header_bits {q : Patch LW} (x : BitVec LW) (h : Protected (readSel x) q) :
    BStarLongGrant.headerBits (q.apply x)=BStarLongGrant.headerBits x := by
  have hs : readSel (q.apply x)=readSel x := by
    unfold readSel
    rw [selector_read h x]
  unfold BStarLongGrant.headerBits
  rw [hs]
  simp only [header_read h x]

/-- The captured header bits and selector in the returned payload are
invariant under any protected patch, even with dormant garbage bits. -/
theorem capture_preserved {q : Patch LW} (x : BitVec LW) (h : Protected (readSel x) q)
    (j : Fin 3) (p : Payload) (won : Bool) :
    BStarLongGrant.capture (q.apply x) j p won = BStarLongGrant.capture x j p won := by
  have hs : readSel (q.apply x)=readSel x := by
    unfold readSel
    rw [selector_read h x]
  simp only [BStarLongGrant.capture,hs,selected_header_bits x h]

/-- The only departing opcode that could modify the bank without a
publication is STAGE. Every admissible STAGE for a live cycle uses the
captured selector of that same owner, even at nonheader digits. -/
def StageOwned (b : Fin 3) (p : Payload) : Prop :=
  p.opcode.toNat=BStarLongCommand.stageOp →
    ∀ d, BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d → d.old=b

theorem outgoing_protects (g : LongGeometry) (j : Fin 11) (x : BitVec LW)
    (p : Payload) (b : Fin 3) (H : StageOwned b p)
    (no : (execute g j x p).published=none) :
    Protected b (execute g j x p).row := by
  simp only [execute,hold,refuse] at no ⊢
  split
  · exact frame_empty _
  split
  · exact frame_compose (frame_stage_field _ _) (frame_seal_field _ _)
  split
  · rename_i hop
    split
    · exact frame_empty _
    · rename_i d hd
      split
      · exact frame_empty _
      · have E := H (beq_iff_eq.mp hop) d hd
        have ⟨n0,n1⟩ := complement_ne d (decode_valid hd)
        rw [← E]
        exact stage_frames d g.axes.h6 g.inside x p.argument.toNat d.old n0 n1
  split
  · split
    · exact frame_empty _
    · split
      · exact frame_seal_field _ _
      · exact frame_empty _
  split
  · split
    · exact frame_empty _
    · split
      · rename_i d hd hlo
        split
        · rename_i yes
          have Hc : (commit g.axes.h6 j x d ⟨p.argument.toNat%4,hlo⟩).2=none := by
            simp_all only [Bool.false_eq_true,if_true,if_false,dif_pos]
          simp [Hc] at yes
        · exact frame_empty _
      · exact frame_empty _
  · exact frame_empty _

end L4.BStarBankCapture
