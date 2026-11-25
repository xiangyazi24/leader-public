import Leader.L4.BStarShort

/-! Independent typed semantics for the WIDTH source doorway, and its
local padded-row comparison. K is stored syntax: an untouched K keeps
its raw bits even if the decoder ignores some parts. -/
namespace L4.BStarWidthTransfer
open AllSizeProtocol

structure Source where
  phase : BitVec 2
  op : BitVec 3
  flags : BitVec 2
  token : BitVec 16
  deriving DecidableEq, Repr

def phaseF (c : Nat) : Field (WidthByteRows.W c) 2 := WidthByteRows.suffixField c 7 2 (by decide)
def opF (c : Nat) : Field (WidthByteRows.W c) 3 := WidthByteRows.suffixField c 9 3 (by decide)
def flagsF (c : Nat) : Field (WidthByteRows.W c) 2 := WidthByteRows.suffixField c 12 2 (by decide)
def tokF (c : Nat) : Field (WidthByteRows.W c) 16 := WidthByteRows.suffixField c 14 16 (by decide)
def phaseOpF (c : Nat) : Field (WidthByteRows.W c) 5 := WidthByteRows.suffixField c 7 5 (by decide)

def readSource {c : Nat} (x : BitVec (WidthByteRows.W c)) : Source :=
  ⟨(phaseF c).read x,(opF c).read x,(flagsF c).read x,(tokF c).read x⟩

private def issueCmd (s : Source) : Source :=
  let op := s.op.toNat
  let a := if op==3 then s.flags.toNat else if op==4 then 1 else 0
  {s with phase := 2, token := WidthByteRows.encode ⟨2,op,a,false⟩}

private def restart : Source := ⟨1,0,0,0⟩

private def accept (s : Source) (next : Nat) : Source :=
  {s with phase := 1, op := BitVec.ofNat 3 next, token := 0}

/-- Old source syntax determines the door. No patched working fields or
neighbor state are consulted, even during simultaneous terminal return. -/
def door (s : Source) : Source :=
  let p := s.phase.toNat
  let o := s.op.toNat
  let d := WidthByteRows.decode s.token
  if o>5 || p==0 || p==3 then restart
  else if p==1 then issueCmd s
  else if d.tag==1 || d.tag==2 then s
  else if d.tag != 3 || d.op != o || d.fault then restart
  else match o with
    | 0 => accept s 1
    | 1 => accept s (if d.arg==1 then 2 else 5)
    | 2 => {accept s 3 with flags := BitVec.ofNat 2 d.arg}
    | 3 => accept s 4
    | 4 => accept s 1
    | _ => accept s 0

/-- Semantic successful WAIT predicate, independent of mask application. -/
def holdFlags (s : Source) : Bool :=
  let d := WidthByteRows.decode s.token
  s.phase.toNat==2 && decide (s.op.toNat≤5) && d.tag==3 && !d.fault &&
    d.op==s.op.toNat && s.op.toNat != 2

theorem holdFlags_eq {c : Nat} (header : Bool) (x : BitVec (WidthByteRows.W c)) :
    BStarShort.widthHoldFlags (c:=c) header x = (header && holdFlags (readSource (c:=c) x)) := by
  cases header <;> rfl

/-- Applying a meaningful assignment on another disjoint lane leaves the
actual source field unchanged. -/
private theorem read_token_write {c : Nat} (x : BitVec (WidthByteRows.W c)) (t : BitVec 16) :
    readSource (c:=c) (((tokF c).assign t).apply x) =
      {readSource (c:=c) x with token := t} := by
  unfold readSource
  rw [Field.read_assign]
  rw [Field.read_other_assign (phaseF c) (tokF c) _ _ (Or.inr (by simp [phaseF,tokF,WidthByteRows.suffixField])),
    Field.read_other_assign (opF c) (tokF c) _ _ (Or.inr (by simp [opF,tokF,WidthByteRows.suffixField])),
    Field.read_other_assign (flagsF c) (tokF c) _ _ (Or.inr (by simp [flagsF,tokF,WidthByteRows.suffixField]))]

private theorem read_phase_write {c : Nat} (x : BitVec (WidthByteRows.W c)) (p : BitVec 2) :
    readSource (c:=c) (((phaseF c).assign p).apply x) =
      {readSource (c:=c) x with phase := p} := by
  unfold readSource
  rw [Field.read_assign]
  rw [Field.read_other_assign (opF c) (phaseF c) _ _ (Or.inl (by simp [phaseF,opF,WidthByteRows.suffixField])),
    Field.read_other_assign (flagsF c) (phaseF c) _ _ (Or.inl (by simp [phaseF,flagsF,WidthByteRows.suffixField])),
    Field.read_other_assign (tokF c) (phaseF c) _ _ (Or.inl (by simp [phaseF,tokF,WidthByteRows.suffixField]))]

def controlF (c : Nat) : Field (WidthByteRows.W c) 7 := WidthByteRows.suffixField c 7 7 (by decide)

private theorem read_sub_assign {w n k : Nat} (f : Field w n) (g : Field w k)
    (lo : Nat) (value : BitVec k) (raw : BitVec w) (h₁ : f.offset=g.offset+lo) (h₂ : lo+n≤k) :
    f.read ((g.assign value).apply raw)=value.extractLsb' lo n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have inside := (g.inMask value (f.offset+j)).mpr (by omega)
  have addr : f.offset+j < w := by have := f.fits; omega
  simp only [Field.read,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
  rw [Patch.write _ _ _ inside]
  simp [Field.assign,addr,show ¬ f.offset+j<g.offset by omega,
    show f.offset+j-g.offset=lo+j by omega]

private theorem read_ctrl {c : Nat} (x : BitVec (WidthByteRows.W c)) (o a : Nat)
    (ho : o<8) (ha : a<4) :
    readSource (c:=c) ((WidthByteRows.control c 1 o a).apply x) =
    {readSource (c:=c) x with phase:=1,op:=BitVec.ofNat 3 o,flags:=BitVec.ofNat 2 a} := by
  let v : BitVec 7 := BitVec.ofNat 7 (32+4*o+a)
  change readSource (c:=c) (((controlF c).assign v).apply x) = _
  unfold readSource
  rw [read_sub_assign (phaseF c) (controlF c) 5 v x rfl (by decide),
      read_sub_assign (opF c) (controlF c) 2 v x rfl (by decide),
      read_sub_assign (flagsF c) (controlF c) 0 v x rfl (by decide),
      Field.read_other_assign (tokF c) (controlF c) v x (Or.inl (by simp [tokF,controlF,WidthByteRows.suffixField]))]
  have A : (v.extractLsb' 5 2)=(1 : BitVec 2) := by
    apply BitVec.eq_of_toNat_eq
    simp [v]
    omega
  have B : (v.extractLsb' 2 3)=BitVec.ofNat 3 o := by
    apply BitVec.eq_of_toNat_eq
    simp [v]
    omega
  have C : (v.extractLsb' 0 2)=BitVec.ofNat 2 a := by
    apply BitVec.eq_of_toNat_eq
    simp [v]
    omega
  rw [A,B,C]

private theorem empty_apply {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  simp [Patch.empty,Patch.apply]

private theorem read_go {c : Nat} (x : BitVec (WidthByteRows.W c)) (o a : Nat)
    (ho : o<8) (ha : a<4) :
    readSource (c:=c) (((WidthByteRows.control c 1 o a).compose
      (WidthByteRows.tokenPatch c WidthByteRows.emptyToken)).apply x) =
    ⟨1,BitVec.ofNat 3 o,BitVec.ofNat 2 a,0⟩ := by
  rw [Patch.compose_apply]
  change readSource (c:=c) (((tokF c).assign (0 : BitVec 16)).apply
    ((WidthByteRows.control c 1 o a).apply x)) = _
  rw [read_token_write,read_ctrl x o a ho ha]

private theorem read_issue {c : Nat} (x : BitVec (WidthByteRows.W c)) (t : WidthByteRows.Token) :
    readSource (c:=c) (((WidthByteRows.put c 7 2 (by decide) 2).compose
      (WidthByteRows.tokenPatch c t)).apply x) =
    {readSource (c:=c) x with phase:=2, token:=WidthByteRows.encode t} := by
  rw [Patch.compose_apply]
  change readSource (c:=c) (((tokF c).assign (WidthByteRows.encode t)).apply
    (((phaseF c).assign (2 : BitVec 2)).apply x)) = _
  rw [read_token_write,read_phase_write]

private def doorPlain (s : Source) : Source :=
  if holdFlags s then {door s with flags:=0} else door s

private theorem phase_eq_two (p : BitVec 2) (h0 : p.toNat ≠ 0) (h1 : p.toNat ≠ 1)
    (h3 : p.toNat ≠ 3) : p.toNat=2 := by
  have := p.isLt
  omega

private theorem cmp_arg_bound (raw : BitVec 16) (ht : (WidthByteRows.decode raw).tag=3)
    (ho : (WidthByteRows.decode raw).op=2) : (WidthByteRows.decode raw).arg<4 := by
  unfold WidthByteRows.decode at ht ho ⊢
  dsimp only at ht ho ⊢
  split at ht
  · change (raw.extractLsb' 14 2).toNat=3 at ht
    omega
  · rename_i H
    simp only [if_neg H] at ho ⊢
    split at ho
    · contradiction
    · rename_i H'
      simp only [if_neg H'] at ht ⊢
      change (raw.extractLsb' 14 2).toNat=3 at ht
      change (raw.extractLsb' 10 3).toNat=2 at ho
      simp only [ht,ho]
      exact Nat.mod_lt _ (by decide)

/-- Original doorway decoder, before the BStar mask narrowing.
Successful non-COMPARE clears only the raw argument lane here. -/
theorem plain_door_transfer {c : Nat} (x : BitVec (WidthByteRows.W c)) :
    readSource (c:=c) ((WidthByteRows.doorPatch (c:=c) x
      (WidthByteRows.decode (readSource (c:=c) x).token)).apply x) =
    doorPlain (readSource (c:=c) x) := by
  let s := readSource (c:=c) x
  let t := WidthByteRows.decode s.token
  change readSource (c:=c) ((WidthByteRows.doorPatch (c:=c) x t).apply x) = doorPlain s
  let go := fun o a => (WidthByteRows.control c 1 o a).compose
    (WidthByteRows.tokenPatch c WidthByteRows.emptyToken)
  change readSource (c:=c) ((if s.op.toNat>5 || s.phase.toNat==0 || s.phase.toNat==3 then go 0 0
    else if s.phase.toNat==1 then _ else if t.tag==1 || t.tag==2 then _
    else if t.tag != 3 || t.op != s.op.toNat || t.fault then go 0 0
    else match s.op.toNat with
    | 0 => go 1 0 | 1 => go (if t.arg==1 then 2 else 5) 0 | 2 => go 3 t.arg
    | 3 => go 4 0 | 4 => go 1 0 | _ => go 0 0).apply x) = doorPlain s
  unfold doorPlain holdFlags door
  dsimp only
  split
  · rename_i invalid
    have N : ((s.phase.toNat == 2) && decide (s.op.toNat≤5) && (t.tag == 3) &&
      !t.fault && (t.op == s.op.toNat) && (s.op.toNat != 2))=false := by
      simp only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at invalid
      rcases invalid with (h|h)|h
      · have hN : ¬s.op.toNat≤5 := by omega
        simp [hN]
      · simp [h]
      · simp [h]
    have NN := N
    dsimp only [t] at NN
    simp only [NN,Bool.false_eq_true,if_false]
    exact read_go x 0 0 (by decide) (by decide)
  · rename_i valid
    have V : s.op.toNat≤5 ∧ s.phase.toNat≠0 ∧ s.phase.toNat≠3 := by
      simpa only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,not_or,Nat.not_lt,and_assoc] using valid
    try simp only [valid,if_false]
    split
    · rename_i issue
      have H : s.phase.toNat=1 := beq_iff_eq.mp issue
      simp only [H]
      exact read_issue x ⟨2,s.op.toNat,
        if s.op.toNat==3 then s.flags.toNat else if s.op.toNat==4 then 1 else 0,false⟩
    · rename_i wait
      have W := phase_eq_two s.phase V.2.1 (fun h => wait (beq_iff_eq.mpr h)) V.2.2
      try simp only [wait,if_false]
      split
      · rename_i occupied
        have N : t.tag≠3 := by
          simp only [Bool.or_eq_true,beq_iff_eq] at occupied
          rcases occupied with h|h <;> omega
        dsimp only [t] at N
        simp [N,empty_apply]
        rfl
      · rename_i unoccupied
        try simp only [unoccupied,if_false]
        split
        · rename_i reject
          have N : ((t.tag == 3) && !t.fault && (t.op == s.op.toNat))=false := by
            simp only [Bool.or_eq_true,bne_iff_ne] at reject
            rcases reject with (h|h)|h <;> simp [h]
          dsimp only [t] at N
          by_cases htag : (WidthByteRows.decode s.token).tag = 3
          · cases hf : (WidthByteRows.decode s.token).fault
            · have hop : (WidthByteRows.decode s.token).op ≠ s.op.toNat := by
                simpa [htag,hf] using N
              simp [hop]
              exact read_go x 0 0 (by decide) (by decide)
            · simp
              exact read_go x 0 0 (by decide) (by decide)
          · simp [htag]
            exact read_go x 0 0 (by decide) (by decide)
        · rename_i success
          have S : t.tag=3 ∧ t.op=s.op.toNat ∧ t.fault=false := by
            simp at success
            exact ⟨success.1.1,success.1.2,success.2⟩
          have Ht := S.1
          have Ho := S.2.1
          have Hf := S.2.2
          dsimp only [t] at Ht Ho Hf
          try simp only [success,if_false]
          split <;> rename_i H
          · simpa [Ht,Ho,Hf,W,H,accept] using read_go x 1 0 (by decide) (by decide)
          · have O : (if t.arg == 1 then 2 else 5) < 8 := by split <;> decide
            simpa [Ht,Ho,Hf,W,H,accept] using read_go x (if t.arg==1 then 2 else 5) 0 O (by decide)
          · have Ar := cmp_arg_bound s.token Ht (Ho.trans H)
            simpa [Ht,Ho,Hf,W,H,accept] using read_go x 3 t.arg (by decide) Ar
          · simpa [Ht,Ho,Hf,W,H,accept] using read_go x 4 0 (by decide) (by decide)
          · simpa [Ht,Ho,Hf,W,H,accept] using read_go x 1 0 (by decide) (by decide)
          · have O : s.op.toNat≠2 := by assumption
            simpa [Ht,Ho,Hf,W,V.1,O,accept] using read_go x 0 0 (by decide) (by decide)

private theorem erase_outside {w : Nat} (q : Patch w) (m x : BitVec w)
    (i : Nat) (h : m.getLsbD i=false) :
    ((BStarShort.erase q m).apply x).getLsbD i=(q.apply x).getLsbD i := by
  have E : (BStarShort.erase q m).mask.getLsbD i=q.mask.getLsbD i := by
    simp [BStarShort.erase_mask,h]
  cases e : q.mask.getLsbD i
  · rw [Patch.hold _ _ _ (E.trans e),Patch.hold _ _ _ e]
  · rw [Patch.write _ _ _ (E.trans e),Patch.write _ _ _ e]
    rfl

private theorem read_erase_other {c l : Nat} (f : Field (WidthByteRows.W c) l)
    (q : Patch (WidthByteRows.W c)) (x : BitVec (WidthByteRows.W c))
    (H : f.offset+l≤16 ∨ 18≤f.offset) :
    f.read ((BStarShort.erase q ((flagsF c).assign 0).mask).apply x)=f.read (q.apply x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  apply erase_outside
  apply Bool.eq_false_iff.mpr
  intro e
  have P := (Field.inMask _ _ _).mp e
  change 16≤f.offset+i ∧ f.offset+i<18 at P
  omega

private theorem read_erase_flags {c : Nat} (q : Patch (WidthByteRows.W c))
    (x : BitVec (WidthByteRows.W c)) :
    (flagsF c).read ((BStarShort.erase q ((flagsF c).assign 0).mask).apply x)=(flagsF c).read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  apply Patch.hold
  have H := (Field.inMask (flagsF c) (0 : BitVec 2) ((flagsF c).offset+i)).mpr (by omega)
  rw [BStarShort.erase_mask,H]
  exact Bool.and_false _

private theorem read_erased {c : Nat} (q : Patch (WidthByteRows.W c)) (x : BitVec (WidthByteRows.W c)) :
    readSource (c:=c) ((BStarShort.erase q ((flagsF c).assign 0).mask).apply x) =
      {readSource (c:=c) (q.apply x) with flags:=(readSource (c:=c) x).flags} := by
  unfold readSource
  rw [read_erase_other (phaseF c) q x (Or.inr (by simp [phaseF,WidthByteRows.suffixField])),
      read_erase_other (opF c) q x (Or.inr (by simp [opF,WidthByteRows.suffixField])),
      read_erase_other (tokF c) q x (Or.inl (by simp [tokF,WidthByteRows.suffixField])),
      read_erase_flags]

/-- Exact all-raw standalone b* door transfer. Paired transport has
additional old-token routing and is not included in this endpoint. -/
theorem door_transfer {c : Nat} (x : BitVec (WidthByteRows.W c)) :
    let s := readSource (c:=c) x
    let q := WidthByteRows.doorPatch (c:=c) x (WidthByteRows.decode s.token)
    let p := if BStarShort.widthHoldFlags (c:=c) true x then
      BStarShort.erase q ((flagsF c).assign 0).mask else q
    readSource (c:=c) (p.apply x)=door s := by
  dsimp only
  rw [holdFlags_eq]
  simp only [Bool.true_and]
  by_cases H : holdFlags (readSource (c:=c) x)=true
  · rw [if_pos H,read_erased,plain_door_transfer]
    simp only [doorPlain,H,if_true]
    have F : (door (readSource (c:=c) x)).flags=(readSource (c:=c) x).flags := by
      let s := readSource (c:=c) x
      change (door s).flags=s.flags
      change holdFlags s=true at H
      simp [holdFlags] at H
      rcases H with ⟨⟨⟨⟨⟨hp,ho⟩,ht⟩,hf⟩,hop⟩,hne⟩
      unfold door
      dsimp only
      simp only [hp,ht,hf,hop,show ¬s.op.toNat>5 by omega,decide_false,
        Nat.reduceBEq,Bool.or_false,Bool.false_eq_true,if_false,bne_self_eq_false]
      split <;> first | rfl | contradiction
    cases E : door (readSource (c:=c) x)
    simp only [E] at F ⊢
    rw [←F]
  · rw [if_neg H,plain_door_transfer]
    simp [doorPlain,H]

end L4.BStarWidthTransfer

