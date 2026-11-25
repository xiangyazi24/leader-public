import Leader.L4.BStarBankTrace

namespace L4.BStarStageCandidateWrite
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongPublication BStarLongOutgoing
open BStarLongWork BStarLongCommand BStarLongToken BStarLongClaims BStarBankCapture

private def Keeps {n : Nat} (f : Field LW n) (q : Patch LW) : Prop :=
  ∀ raw, f.read (q.apply raw)=f.read raw

private theorem fused_holds {n : Nat} (f : Field LW n) (qs : List (Patch LW))
    (H : ∀ q∈qs,Keeps f q) (start : Patch LW) (raw : BitVec LW) :
    f.read ((qs.foldl Patch.compose start).apply raw)=f.read (start.apply raw) := by
  induction qs generalizing start with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons,ih (fun w hw => H w (List.mem_cons_of_mem _ hw))]
    rw [Patch.compose_apply]
    exact H q List.mem_cons_self _

private theorem fused_copies {n : Nat} (f : Field LW n) (v : BitVec n)
    (qs : List (Patch LW)) (hit : f.assign v∈qs)
    (H : ∀ q∈qs,q=f.assign v ∨ Keeps f q) (start : Patch LW) (raw : BitVec LW) :
    f.read ((qs.foldl Patch.compose start).apply raw)=v := by
  induction qs generalizing start with
  | nil => contradiction
  | cons q qs ih =>
    rw [List.foldl_cons]
    have tail w (hw : w∈qs) := H w (List.mem_cons_of_mem _ hw)
    by_cases T : f.assign v∈qs
    · exact ih T tail _
    · have E : q=f.assign v := (List.mem_cons.mp hit).resolve_right T |>.symm
      have keeps w (hw : w∈qs) : Keeps f w :=
        (tail w hw).resolve_left (fun E => T (E ▸ hw))
      rw [fused_holds f qs keeps,Patch.compose_apply,E]
      exact Field.read_assign _ _ _

private theorem digit_other (b a : Fin 3) (i j : Fin 9) (v : BitVec 4)
    (N : b≠a ∨ i≠j) : Keeps (bankDigit b i) ((bankDigit a j).assign v) := by
  intro raw
  apply Field.read_other_assign
  rcases N with B|J
  · have H : b.val≠a.val := fun E => B (Fin.ext E)
    have hb := b.isLt
    have ha := a.isLt
    have hi := i.isLt
    have hj := j.isLt
    simp only [bankDigit,bankPart,bankBase]
    omega
  · have H : i.val≠j.val := fun E => J (Fin.ext E)
    have hi := i.isLt
    have hj := j.isLt
    by_cases E : b=a
    · subst a
      simp only [bankDigit,bankPart,bankBase]
      omega
    · have H : b.val≠a.val := fun Z => E (Fin.ext Z)
      have hb := b.isLt
      have ha := a.isLt
      simp only [bankDigit,bankPart,bankBase]
      omega

private theorem header_other (b a : Fin 3) (i j : Fin 9) (v : BitVec 1)
    (N : b≠a ∨ i≠j) : Keeps (bankHeader b i) ((bankHeader a j).assign v) := by
  intro raw
  apply Field.read_other_assign
  rcases N with B|J
  · have H : b.val≠a.val := fun E => B (Fin.ext E)
    have hb := b.isLt
    have ha := a.isLt
    have hi := i.isLt
    have hj := j.isLt
    simp only [bankHeader,bankPart,bankBase]
    omega
  · have H : i.val≠j.val := fun E => J (Fin.ext E)
    have hi := i.isLt
    have hj := j.isLt
    by_cases E : b=a
    · subst a
      simp only [bankHeader,bankPart,bankBase]
      omega
    · have H : b.val≠a.val := fun Z => E (Fin.ext Z)
      have hb := b.isLt
      have ha := a.isLt
      simp only [bankHeader,bankPart,bankBase]
      omega

private theorem digit_header_range (b a : Fin 3) (i j : Fin 9) :
    (bankDigit b i).offset+4≤(bankHeader a j).offset ∨
      (bankHeader a j).offset+1≤(bankDigit b i).offset := by
  have hb := b.isLt
  have ha := a.isLt
  have hi := i.isLt
  have hj := j.isLt
  rcases Nat.lt_trichotomy b.val a.val with H|H|H
  all_goals simp only [bankDigit,bankHeader,bankPart,bankBase]; omega


def candidate (d : Descriptor) (which : Bool) : Fin 3 := if which then d.b1 else d.b0

theorem candidates_distinct (d : Descriptor) (h : d.valid=true) : d.b0≠d.b1 := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  have A := beq_iff_eq.mp a
  have B := beq_iff_eq.mp b
  have L := d.old.isLt
  intro E
  have F := congrArg Fin.val E
  omega

/-- Actual outgoing STAGE bank digit readback. `raw` is arbitrary: the
candidate bytes are sourced from the immutable old `old` registers,
not from bytes installed by earlier components of the same mark. -/
theorem stage_digit (old raw : BitVec LW) (d : Descriptor) (h : d.valid=true)
    (head which : Bool) (arg : Nat) (i : Fin 9) :
    (bankDigit (candidate d which) i).read ((stagePatch head true old d arg).apply raw)=
      readDigit old which i := by
  let f := bankDigit (candidate d which) i
  let v := readDigit old which i
  let ds := dimDigits old false d.b0 ++ dimDigits old true d.b1
  let hs := if head then dimHeaders arg false d.b0 ++ dimHeaders arg true d.b1 ++
      [stage.assign (packOptional (some d))] else []
  have hit : f.assign v∈ds := by
    cases which
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
  change f.read (((ds++hs).foldl Patch.compose (.empty _)).apply raw)=v
  apply fused_copies f v _ (List.mem_append_left _ hit)
  intro q hq
  rcases List.mem_append.mp hq with D|H
  · have one (other : Bool) (q : Patch LW)
        (D : q∈dimDigits old other (candidate d other)) :
        q=f.assign v ∨ Keeps f q := by
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp D
      by_cases C : which=other
      · subst other
        by_cases J : i=j
        · subst j; exact .inl rfl
        · exact .inr (digit_other _ _ _ _ _ (.inr J))
      · have ne : candidate d which≠candidate d other := by
          cases which <;> cases other <;> simp_all [candidate,candidates_distinct d h,
            Ne.symm (candidates_distinct d h)]
        exact .inr (digit_other _ _ _ _ _ (.inl ne))
    exact (List.mem_append.mp D).elim (one false q) (one true q)
  · right
    cases head <;> simp only [hs,Bool.false_eq_true,if_false,List.not_mem_nil,if_true,
      List.mem_append,List.mem_singleton] at H
    rcases H with (H|H)|rfl
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp H
      intro x
      exact Field.read_other_assign f _ _ x (digit_header_range _ _ _ _)
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp H
      intro x
      exact Field.read_other_assign f _ _ x (digit_header_range _ _ _ _)
    · intro x
      apply Field.read_other_assign
      right
      simp only [f,stage,bankDigit,bankPart,bankBase]
      omega


def argumentHeader (arg : Nat) (which : Bool) (i : Fin 9) : BitVec 1 :=
  BitVec.ofNat 1 (arg / 2^(9*(if which then 0 else 1)+(8-i.val)))

/-- The eighteen physical header bits come from the old outgoing
STAGE argument, not from today's selected header. -/
theorem stage_header (old raw : BitVec LW) (d : Descriptor) (h : d.valid=true)
    (inside which : Bool) (arg : Nat) (i : Fin 9) :
    (bankHeader (candidate d which) i).read ((stagePatch true inside old d arg).apply raw)=
      argumentHeader arg which i := by
  let f := bankHeader (candidate d which) i
  let v := argumentHeader arg which i
  let ds := if inside then dimDigits old false d.b0 ++ dimDigits old true d.b1 else []
  let heads := dimHeaders arg false d.b0 ++ dimHeaders arg true d.b1
  let last := stage.assign (packOptional (some d))
  have hit : f.assign v∈heads := by
    cases which
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
  have patchEq : stagePatch true inside old d arg=fuse (ds++(heads++[last])) := by
    simp only [stagePatch,if_true,ds,heads,last,List.append_assoc]
  rw [patchEq]
  change f.read (((ds++(heads++[last])).foldl Patch.compose (.empty _)).apply raw)=v
  apply fused_copies f v _ (List.mem_append_right _ (List.mem_append_left _ hit))
  intro q hq
  rcases List.mem_append.mp hq with D|H
  · right
    cases inside <;> simp only [ds,Bool.false_eq_true,if_false,List.not_mem_nil,if_true,
      List.mem_append] at D
    rcases D with D|D
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp D
      intro x
      exact Field.read_other_assign f _ _ x ((digit_header_range _ _ _ _).elim Or.inr Or.inl)
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp D
      intro x
      exact Field.read_other_assign f _ _ x ((digit_header_range _ _ _ _).elim Or.inr Or.inl)
  · rcases List.mem_append.mp H with H|H
    · have one (other : Bool) (q : Patch LW)
          (D : q∈dimHeaders arg other (candidate d other)) :
          q=f.assign v ∨ Keeps f q := by
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp D
        by_cases C : which=other
        · subst other
          by_cases J : i=j
          · subst j; exact .inl rfl
          · exact .inr (header_other _ _ _ _ _ (.inr J))
        · have ne : candidate d which≠candidate d other := by
            cases which <;> cases other <;> simp_all [candidate,candidates_distinct d h,
              Ne.symm (candidates_distinct d h)]
          exact .inr (header_other _ _ _ _ _ (.inl ne))
      exact (List.mem_append.mp H).elim (one false q) (one true q)
    · have E : q=last := List.mem_singleton.mp H
      subst q
      right
      intro x
      apply Field.read_other_assign
      right
      simp only [f,stage,bankHeader,bankPart,bankBase]
      omega

/-- Exact authorization-to-patch bridge on the real outgoing handler. -/
theorem execute_stage (g : LongGeometry) (old : BitVec LW) (j : Fin 11)
    (p : Payload) (d : Descriptor)
    (center : j.val=1) (healthy : p.fault=0) (opcode : p.opcode.toNat=stageOp)
    (decodeDesc : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d)
    (auth : g.axes.h6=true → actual old d=true) :
    execute g j old p=⟨stagePatch g.axes.h6 g.inside old d p.argument.toNat,.forward p,none⟩ := by
  unfold execute
  dsimp only
  cases H : g.axes.h6
  · simp [center,healthy,opcode,decodeDesc]
  · simp [center,healthy,opcode,show stageOp≠1 by decide,decodeDesc,auth H]

#print axioms stage_digit
#print axioms stage_header
#print axioms execute_stage
end L4.BStarStageCandidateWrite
