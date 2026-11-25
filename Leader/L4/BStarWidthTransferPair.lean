import Leader.L4.BStarWidthTransfer

/-! The actual right-header pair projection, including dirty occupied
WAIT and canonicalization before the door. -/
namespace L4.BStarWidthTransferPair
open AllSizeProtocol BStarWidthTransfer

private def canon {c : Nat} (t : WidthByteRows.Token) : Patch (WidthByteRows.W c) :=
  (Patch.empty _).compose (if t.fault then WidthByteRows.tokenPatch c t else Patch.empty _)

private theorem right_header_row {c : Nat} (r : Nat) (h : Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    (WidthByteRows.row (c:=c) r (h,true) x).2 =
    let t := WidthByteRows.decode (readSource (c:=c) x.2).token
    (canon (c:=c) t).compose (WidthByteRows.doorPatch (c:=c) x.2 t) := by
  unfold WidthByteRows.row
  dsimp only
  simp only [if_true,Bool.true_and,Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false]
  split
  · rfl
  · split <;> rfl

private theorem empty_apply {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  simp [Patch.empty,Patch.apply]

private theorem tok_mask {c : Nat} (t : WidthByteRows.Token) (i : Nat) :
    (WidthByteRows.tokenPatch c t).mask.getLsbD i=true ↔ i<16 := by
  change (((tokF c).assign (WidthByteRows.encode t)).mask.getLsbD i=true) ↔ _
  rw [Field.inMask]
  change (0≤i ∧ i<16) ↔ _
  omega

private theorem canon_outside {c : Nat} (t : WidthByteRows.Token) (i : Nat) (hi : 16≤i) :
    (canon (c:=c) t).mask.getLsbD i=false := by
  unfold canon
  change ((Patch.empty _).mask ||| _).getLsbD i = false
  rw [BitVec.getLsbD_or]
  simp only [Patch.empty]
  split
  · apply Bool.eq_false_iff.mpr
    intro H
    have U : (WidthByteRows.tokenPatch c t).mask.getLsbD i=true := by simpa using H
    have := (tok_mask t i).mp U
    omega
  · simp

def holds (s : BStarWidthTransfer.Source) : Bool :=
  let t := WidthByteRows.decode s.token
  !(s.op.toNat>5 || s.phase.toNat==0 || s.phase.toNat==3) && !(s.phase.toNat==1) &&
    (t.tag==1 || t.tag==2)

private theorem right_empty_or_overwrites {c : Nat} (x : BitVec (WidthByteRows.W c)) :
    let s := readSource (c:=c) x
    let t := WidthByteRows.decode s.token
    let q := WidthByteRows.doorPatch (c:=c) x t
    (q=Patch.empty _ ∧ BStarShort.widthHoldFlags (c:=c) true x=false ∧ door s=s ∧ holds s=true) ∨
      (holds s=false ∧ ∀ i, i<16 → q.mask.getLsbD i=true) := by
  dsimp only
  let s := readSource (c:=c) x
  let t := WidthByteRows.decode s.token
  rw [holdFlags_eq]
  change _ ∨ (holds s=false ∧ ∀ i, i<16 → (WidthByteRows.doorPatch (c:=c) x t).mask.getLsbD i=true)
  have asgn (p : Patch (WidthByteRows.W c)) (d : WidthByteRows.Token) :
      ∀ i, i<16 → (p.compose (WidthByteRows.tokenPatch c d)).mask.getLsbD i=true := by
    intro i hi
    change (p.mask ||| (WidthByteRows.tokenPatch c d).mask).getLsbD i=true
    rw [BitVec.getLsbD_or,(tok_mask d i).mpr hi,Bool.or_true]
  unfold WidthByteRows.doorPatch
  dsimp only
  split
  · rename_i E
    have E' : (decide (s.op.toNat > 5) || s.phase.toNat == 0 || s.phase.toNat == 3)=true := E
    exact Or.inr ⟨by simp only [holds,E',Bool.not_true,Bool.false_and],asgn _ _⟩
  · rename_i hvalid
    have V : ¬(decide (s.op.toNat > 5) || s.phase.toNat == 0 || s.phase.toNat == 3)=true := hvalid
    split
    · rename_i E
      have E' : (s.phase.toNat==1)=true := E
      exact Or.inr ⟨by simp [holds,E'],asgn _ _⟩
    · rename_i hp
      have P : ¬(s.phase.toNat==1)=true := hp
      split
      · rename_i ht
        have T : (t.tag==1 || t.tag==2)=true := ht
        have TN := Bool.eq_false_iff.mpr V
        have PN := Bool.eq_false_iff.mpr P
        have tn : (WidthByteRows.decode s.token).tag≠3 := by
          simp only [t,Bool.or_eq_true,beq_iff_eq] at T
          rcases T with e|e <;> omega
        left
        refine ⟨rfl,?_,?_,?_⟩
        · simp [holdFlags,show (WidthByteRows.decode (readSource (c:=c) x).token).tag≠3 from tn]
        · change door s=s
          unfold door
          dsimp only
          rw [if_neg V,if_neg P]
          exact if_pos T
        · unfold holds
          dsimp only
          rw [TN,PN]
          exact T
      · rename_i E
        have E' : (t.tag==1 || t.tag==2)=false := Bool.eq_false_iff.mpr E
        have H : holds s=false := by
          unfold holds
          dsimp only
          rw [E']
          exact Bool.and_false _
        split
        · exact Or.inr ⟨H,asgn _ _⟩
        · split <;> exact Or.inr ⟨H,asgn _ _⟩

private theorem erase_overwrite {c : Nat} (x : BitVec (WidthByteRows.W c)) (t : WidthByteRows.Token)
    (q : Patch (WidthByteRows.W c)) (H : ∀ i, i<16 → q.mask.getLsbD i=true)
    (narrow : Bool) :
    let N := fun z => if narrow then BStarShort.erase z ((flagsF c).assign 0).mask else z
    (N ((canon (c:=c) t).compose q)).apply x=(N q).apply x := by
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have c0 : 16≤i → (canon (c:=c) t).mask.getLsbD i=false := canon_outside t i
  have C : ((canon (c:=c) t).compose q).apply x =
      q.apply ((canon (c:=c) t).apply x) := Patch.compose_apply _ _ _
  have val : (((canon (c:=c) t).compose q).apply x).getLsbD i=(q.apply x).getLsbD i := by
    rw [C]
    by_cases lt : i<16
    · rw [Patch.write _ _ _ (H i lt),Patch.write _ _ _ (H i lt)]
    · cases Q : q.mask.getLsbD i
      · rw [Patch.hold _ _ _ Q,Patch.hold _ _ _ Q,Patch.hold _ _ _ (c0 (by omega))]
      · rw [Patch.write _ _ _ Q,Patch.write _ _ _ Q]
  cases narrow
  · exact val
  · let m := ((flagsF c).assign (0 : BitVec 2)).mask
    change ((BStarShort.erase ((canon (c:=c) t).compose q) m).apply x).getLsbD i =
      ((BStarShort.erase q m).apply x).getLsbD i
    by_cases hm : m.getLsbD i=true
    · have A : (BStarShort.erase ((canon (c:=c) t).compose q) m).mask.getLsbD i=false := by
        rw [BStarShort.erase_mask,hm]
        exact Bool.and_false _
      have B : (BStarShort.erase q m).mask.getLsbD i=false := by
        rw [BStarShort.erase_mask,hm]
        exact Bool.and_false _
      rw [Patch.hold _ _ _ A,Patch.hold _ _ _ B]
    · have M := Bool.eq_false_iff.mpr hm
      have step (z : Patch (WidthByteRows.W c)) : ((BStarShort.erase z m).apply x).getLsbD i =
          (z.apply x).getLsbD i := by
        have E : (BStarShort.erase z m).mask.getLsbD i=z.mask.getLsbD i := by
          rw [BStarShort.erase_mask,M]
          exact Bool.and_true _
        cases Z : z.mask.getLsbD i
        · rw [Patch.hold _ _ _ (E.trans Z),Patch.hold _ _ _ Z]
        · rw [Patch.write _ _ _ (E.trans Z),Patch.write _ _ _ Z]
          rfl
      exact (step _).trans (val.trans (step _).symm)

/-- Exact source projection on the responder at an old header.
A malformed old occupied F and a valid WAIT leave the canonical
fault syntax, not its dirty predecessor. Every other source decision
uses precisely the old responder fields. -/
def rightSource (s : BStarWidthTransfer.Source) : BStarWidthTransfer.Source :=
  let t := WidthByteRows.decode s.token
  if holds s && t.fault then
    {s with token:=WidthByteRows.encode t}
  else door s

private theorem read_canon {c : Nat} (x : BitVec (WidthByteRows.W c)) (t : WidthByteRows.Token) :
    readSource (c:=c) ((canon (c:=c) t).apply x) =
      if t.fault then {readSource (c:=c) x with token:=WidthByteRows.encode t}
      else readSource (c:=c) x := by
  unfold canon
  rw [Patch.compose_apply,empty_apply]
  split
  · change readSource (c:=c) (((tokF c).assign (WidthByteRows.encode t)).apply x) = _
    unfold readSource
    rw [Field.read_assign,
      Field.read_other_assign (phaseF c) (tokF c) _ _ (Or.inr (by simp [phaseF,tokF,WidthByteRows.suffixField])),
      Field.read_other_assign (opF c) (tokF c) _ _ (Or.inr (by simp [opF,tokF,WidthByteRows.suffixField])),
      Field.read_other_assign (flagsF c) (tokF c) _ _ (Or.inr (by simp [flagsF,tokF,WidthByteRows.suffixField]))]
  · rw [empty_apply]

/-- Literal paired-row source transfer at a right header, all left
bytes and both left-header values. Untouched malformed syntax in an
occupied WAIT is replaced exactly by the preliminary canonical write. -/
theorem header_source_transfer {c : Nat} (r : Nat) (h : Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    readSource (c:=c) ((patchPair (BStarShort.widthWork (c:=c) r (h,true) x) x).2) =
      rightSource (readSource (c:=c) x.2) := by
  let s := readSource (c:=c) x.2
  let t := WidthByteRows.decode s.token
  let q := WidthByteRows.doorPatch (c:=c) x.2 t
  let b := BStarShort.widthHoldFlags (c:=c) true x.2
  let m := ((flagsF c).assign (0 : BitVec 2)).mask
  change readSource (c:=c) ((if b then
      BStarShort.erase (WidthByteRows.row (c:=c) r (h,true) x).2 m
      else (WidthByteRows.row (c:=c) r (h,true) x).2).apply x.2) = rightSource s
  rw [right_header_row]
  change readSource (c:=c) ((if b then BStarShort.erase ((canon (c:=c) t).compose q) m
      else (canon (c:=c) t).compose q).apply x.2) = rightSource s
  rcases right_empty_or_overwrites (c:=c) x.2 with ⟨Q,B,D,H⟩|⟨H,full⟩
  · change q=Patch.empty _ at Q
    change b=false at B
    change door s=s at D
    change holds s=true at H
    rw [Q,B]
    simp only [Bool.false_eq_true,if_false,Patch.compose_apply,empty_apply]
    rw [read_canon]
    unfold rightSource
    rw [H,D]
    rfl
  · change holds s=false at H
    change ∀ i, i<16 → q.mask.getLsbD i=true at full
    rw [erase_overwrite x.2 t q full b]
    have D := door_transfer (c:=c) x.2
    change readSource (c:=c) ((if b then BStarShort.erase q m else q).apply x.2)=door s at D
    rw [D]
    unfold rightSource
    rw [H]
    rfl

/-- On one raw seam the left BEGIN departs while the right occupied WAIT
ignores its malformed old F for progress but canonicalizes its syntax. -/
theorem dirty_wait_seam_fixture :
    let u : BitVec (WidthByteRows.W 5) := 32768
    let v : BitVec (WidthByteRows.W 5) := BitVec.ofNat _ (2^22+32768+32)
    let q := BStarShort.widthWork (c:=5) 3 (true,true) (u,v)
    (q.1.apply u).toNat=49152 ∧ (q.2.apply v).toNat=2^22+40960 ∧
      q.2.mask.toNat=65535 := by decide

end L4.BStarWidthTransferPair

