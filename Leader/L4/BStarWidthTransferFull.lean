import Leader.L4.BStarWidthTransferDepart

namespace L4.BStarWidthTransferFull
open AllSizeProtocol BStarWidthTransferDepart
open BStarWidthTransfer (readSource phaseF opF flagsF tokF controlF)

structure Cell where
  source : BStarWidthTransfer.Source
  data : Data

def read {c : Nat} (x : BitVec (WidthByteRows.W c)) : Cell :=
  ⟨readSource (c:=c) x, readData (c:=c) x⟩

private def canon (s : BStarWidthTransfer.Source) (t : WidthByteRows.Token) :
    BStarWidthTransfer.Source :=
  if t.fault then {s with token:=WidthByteRows.encode t} else s

private def prep (h : Bool) (s : BStarWidthTransfer.Source) (t : WidthByteRows.Token) :
    BStarWidthTransfer.Source :=
  canon (if h then s else {s with phase:=1,op:=0,flags:=0}) t

/-- Old values on both ends determine every branch. This typed work
step calls no packed row or patch application. Raw K is held unless
transport, canonicalization or an actual source command assigns it. -/
def step (c r i : Nat) (h : Pair Bool) (x : Pair Cell) : Pair Cell :=
  let f := WidthByteRows.decode x.1.source.token
  let d := WidthByteRows.decode x.2.source.token
  let u := prep h.1 x.1.source f
  let v := prep h.2 x.2.source d
  let right := BStarWidthTransferPair.rightSource x.2.source
  if f.tag==2 then
    let (dat,t) := execute c r i x.1.data f
    if h.2 then
      (⟨{u with token:=WidthByteRows.encode (WidthByteRows.finish t)},dat⟩,⟨right,x.2.data⟩)
    else
      (⟨{u with token:=16384},dat⟩,⟨{v with token:=WidthByteRows.encode t},x.2.data⟩)
  else if h.2 then
    (⟨if f.tag==1 then {u with token:=0} else u,x.1.data⟩,⟨right,x.2.data⟩)
  else if d.tag==3 then
    (⟨{u with token:=WidthByteRows.encode d},x.1.data⟩,⟨{v with token:=0},x.2.data⟩)
  else if f.tag==1 && d.tag==0 then
    (⟨{u with token:=0},x.1.data⟩,⟨v,x.2.data⟩)
  else (⟨u,x.1.data⟩,⟨v,x.2.data⟩)

private theorem empty_apply {w : Nat} (x : BitVec w) : (Patch.empty w).apply x=x := by
  simp [Patch.empty,Patch.apply]

private theorem frame {w l : Nat} (f : Field w l) (q : Patch w) (a : BitVec w)
    (H : ∀ i, f.offset≤i → i<f.offset+l → q.mask.getLsbD i=false) :
    f.read (q.apply a)=f.read a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  exact Patch.hold _ _ _ (H _ (by omega) (by omega))

private theorem data_frame {c : Nat} (q : Patch (WidthByteRows.W c)) (a : BitVec (WidthByteRows.W c))
    (H : ∀ i, 23≤i → i<29 → q.mask.getLsbD i=false) :
    readData (c:=c) (q.apply a)=readData (c:=c) a := by
  unfold readData
  have fl (j : Nat) (h : j≤6) (hh : 1≤j) :
      (lane c j h).read (q.apply a)=(lane c j h).read a := by
    apply frame
    intro i hl hr
    change 30-j-1≤i at hl
    change i<30-j-1+1 at hr
    exact H i (by omega) (by omega)
  rw [fl 1 (by decide) (by decide),fl 2 (by decide) (by decide),
      fl 3 (by decide) (by decide),fl 4 (by decide) (by decide),
      fl 5 (by decide) (by decide),fl 6 (by decide) (by decide)]

private theorem source_frame {c : Nat} (q : Patch (WidthByteRows.W c)) (a : BitVec (WidthByteRows.W c))
    (H : ∀ i, i<23 → q.mask.getLsbD i=false) :
    readSource (c:=c) (q.apply a)=readSource (c:=c) a := by
  unfold readSource
  rw [frame (phaseF c) q a (fun i _ hi => H i hi),
    frame (opF c) q a (fun i _ hi => H i (by change i<21 at hi; omega)),
    frame (flagsF c) q a (fun i _ hi => H i (by change i<18 at hi; omega)),
    frame (tokF c) q a (fun i _ hi => H i (by change i<16 at hi; omega))]

private theorem assign_outside {w l : Nat} (f : Field w l) (v : BitVec l) (i : Nat)
    (H : i<f.offset ∨ f.offset+l≤i) : (f.assign v).mask.getLsbD i=false := by
  apply Bool.eq_false_iff.mpr
  intro C
  have := (f.inMask v i).mp C
  omega

private theorem token_read {c : Nat} (x : BitVec (WidthByteRows.W c)) (t : WidthByteRows.Token) :
    read (c:=c) ((WidthByteRows.tokenPatch c t).apply x) =
      {read (c:=c) x with source:={(read (c:=c) x).source with token:=WidthByteRows.encode t}} := by
  change read (c:=c) (((tokF c).assign (WidthByteRows.encode t)).apply x)=_
  unfold read readSource
  rw [Field.read_assign,
    Field.read_other_assign (phaseF c) (tokF c) _ _ (Or.inr (by simp [phaseF,tokF,WidthByteRows.suffixField])),
    Field.read_other_assign (opF c) (tokF c) _ _ (Or.inr (by simp [opF,tokF,WidthByteRows.suffixField])),
    Field.read_other_assign (flagsF c) (tokF c) _ _ (Or.inr (by simp [flagsF,tokF,WidthByteRows.suffixField])),
    data_frame _ _ (fun i h _ => assign_outside _ _ i (Or.inr (by change 16≤i; omega)))]

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

private theorem reset_read {c : Nat} (x : BitVec (WidthByteRows.W c)) :
    read (c:=c) ((WidthByteRows.control c 1 0 0).apply x) =
      {read (c:=c) x with source:={readSource (c:=c) x with phase:=1,op:=0,flags:=0}} := by
  let f := controlF c
  let v : BitVec 7 := 32
  change read (c:=c) ((f.assign v).apply x)=_
  unfold read readSource
  rw [read_sub_assign (phaseF c) f 5 v x rfl (by decide),
      read_sub_assign (opF c) f 2 v x rfl (by decide),
      read_sub_assign (flagsF c) f 0 v x rfl (by decide),
      Field.read_other_assign (tokF c) f v x (Or.inl (by change 16≤16; omega)),
      data_frame _ _ (fun i h _ => assign_outside _ _ i (Or.inr h))]
  rw [show v.extractLsb' 5 2=(1 : BitVec 2) by decide,
      show v.extractLsb' 2 3=(0 : BitVec 3) by decide,
      show v.extractLsb' 0 2=(0 : BitVec 2) by decide]

private def prepPatch {c : Nat} (h : Bool) (t : WidthByteRows.Token) : Patch (WidthByteRows.W c) :=
  (if h then Patch.empty _ else WidthByteRows.control c 1 0 0).compose
    (if t.fault then WidthByteRows.tokenPatch c t else Patch.empty _)

private theorem prep_read {c : Nat} (h : Bool) (t : WidthByteRows.Token)
    (x : BitVec (WidthByteRows.W c)) :
    read (c:=c) ((prepPatch (c:=c) h t).apply x)=
      {read (c:=c) x with source:=prep h (readSource (c:=c) x) t} := by
  unfold prepPatch prep canon
  rw [Patch.compose_apply]
  cases h <;> cases F : t.fault
  · simp only [Bool.false_eq_true,if_false,empty_apply,reset_read]
  · simp only [Bool.false_eq_true,if_false,if_true,token_read,reset_read]
  · simp only [ if_true,Bool.false_eq_true,if_false,empty_apply] <;> rfl
  · simp only [ if_true,empty_apply,token_read] <;> rfl

private theorem execute_prepared {c : Nat} (r i : Nat) (h : Bool)
    (x : BitVec (WidthByteRows.W c)) (t : WidthByteRows.Token) :
    let q := WidthByteRows.departing (c:=c) r i x t
    read (c:=c) ((prepPatch (c:=c) h t |>.compose q.1).apply x) =
      ⟨prep h (readSource (c:=c) x) t,(execute c r i (readData (c:=c) x) t).1⟩ := by
  dsimp only
  let q := (WidthByteRows.departing (c:=c) r i x t).1
  let y := (prepPatch (c:=c) h t).apply x
  have R := prep_read h t x
  have RD : readData (c:=c) y=readData (c:=c) x := congrArg Cell.data R
  have RS : readSource (c:=c) y=prep h (readSource (c:=c) x) t := congrArg Cell.source R
  have q0 (b : Nat) (hb : b<23) : q.mask.getLsbD b=false := by
    apply Bool.eq_false_iff.mpr
    intro T
    obtain ⟨j,H,eq⟩ := (execute_support r i x t b).mp T
    have B : j≤6 := by
      unfold assigns at H
      obtain ⟨_,H⟩ := H
      split at H <;> first | omega | (rcases H with ⟨_,J⟩ <;> omega)
    omega
  have OUT : readData (c:=c) (q.apply y)=readData (c:=c) (q.apply x) := by
    have D (j : Nat) (hj : j≤6) (h0 : 1≤j) :
        (lane c j hj).read (q.apply y)=(lane c j hj).read (q.apply x) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
      cases H : q.mask.getLsbD ((lane c j hj).offset+i)
      · rw [Patch.hold _ _ _ H,Patch.hold _ _ _ H]
        have E : (lane c j hj).read y=(lane c j hj).read x := by
          have N : j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
          rcases N with z|z|z|z|z|z <;> subst j
          · exact congrArg Data.done RD
          · exact congrArg Data.pick RD
          · exact congrArg Data.inside RD
          · exact congrArg Data.last RD
          · exact congrArg Data.count RD
          · exact congrArg Data.width RD
        have L := congrArg (fun v : BitVec 1 => v.getLsbD i) E
        simpa only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and] using L
      · rw [Patch.write _ _ _ H,Patch.write _ _ _ H]
    unfold readData
    rw [D 1 (by decide) (by decide),D 2 (by decide) (by decide),
      D 3 (by decide) (by decide),D 4 (by decide) (by decide),
      D 5 (by decide) (by decide),D 6 (by decide) (by decide)]
  rw [Patch.compose_apply]
  change read (c:=c) (q.apply y)=_
  unfold read
  rw [source_frame _ _ q0,RS,OUT]
  exact congrArg (fun p => Cell.mk (prep h (readSource (c:=c) x) t) p.1)
    (execute_transfer r i x t)

private def Below {w : Nat} (q : Patch w) (cap : Nat) : Prop :=
  ∀ i, cap≤i → q.mask.getLsbD i=false

private theorem below_comp {w cap : Nat} (q p : Patch w) (Q : Below q cap) (P : Below p cap) :
    Below (q.compose p) cap := by
  intro i hi
  change ((q.mask ||| p.mask).getLsbD i)=false
  simp only [BitVec.getLsbD_or,Q i hi,P i hi,Bool.or_false]

private theorem below_empty (w cap : Nat) : Below (Patch.empty w) cap := by
  intro i _
  simp [Patch.empty]

private theorem below_put {c j l : Nat} (H : j+l≤30) (v : Nat) (C : 30-j≤23) :
    Below (WidthByteRows.put c j l H v) 23 := by
  intro i hi
  apply assign_outside
  right
  change 30-j-l+l≤i
  omega

private theorem below_token (c : Nat) (t : WidthByteRows.Token) :
    Below (WidthByteRows.tokenPatch c t) 23 := below_put (by decide) _ (by decide)

private theorem below_control (c p o f : Nat) :
    Below (WidthByteRows.control c p o f) 23 := below_put (by decide) _ (by decide)

private theorem below_prep {c : Nat} (h : Bool) (t : WidthByteRows.Token) :
    Below (prepPatch (c:=c) h t) 23 := by
  unfold prepPatch
  apply below_comp
  · cases h
    · exact below_control _ _ _ _
    · exact below_empty _ _
  · split
    · exact below_token _ _
    · exact below_empty _ _

private theorem below_door {c : Nat} (x : BitVec (WidthByteRows.W c)) (t : WidthByteRows.Token) :
    Below (WidthByteRows.doorPatch (c:=c) x t) 23 := by
  have go (o a : Nat) :
      Below ((WidthByteRows.control c 1 o a).compose (WidthByteRows.tokenPatch c WidthByteRows.emptyToken)) 23 :=
    below_comp _ _ (below_control _ _ _ _) (below_token _ _)
  unfold WidthByteRows.doorPatch
  dsimp only
  split
  · exact go _ _
  · split
    · exact below_comp _ _ (below_put (by decide) _ (by decide)) (below_token _ _)
    · split
      · exact below_empty _ _
      · split
        · exact go _ _
        · split <;> exact go _ _

private def rawRight {c : Nat} (r : Nat) (h : Pair Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) : Patch (WidthByteRows.W c) :=
  let f := WidthByteRows.decode (readSource (c:=c) x.1).token
  let d := WidthByteRows.decode (readSource (c:=c) x.2).token
  let b := prepPatch (c:=c) h.2 d
  let y := if f.tag==2 then
    if h.2 then b else b.compose (WidthByteRows.tokenPatch c
      (WidthByteRows.departing (c:=c) r (WidthByteRows.offset h.1 x.1) x.1 f).2)
    else if h.2 && f.tag==1 then b
    else if !h.2 && d.tag==3 then b.compose (WidthByteRows.tokenPatch c WidthByteRows.emptyToken)
    else b
  if h.2 then y.compose (WidthByteRows.doorPatch (c:=c) x.2 d) else y

private theorem raw_right_eq {c : Nat} (r : Nat) (h : Pair Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    (WidthByteRows.row (c:=c) r h x).2=rawRight (c:=c) r h x := by
  obtain ⟨l,k⟩ := h
  cases k
  · simp only [WidthByteRows.row,rawRight,readSource,tokF,Bool.false_eq_true,if_false,
      Bool.false_and,Bool.not_false,Bool.true_and]
    split <;> simp_all <;> (first | rfl | (split <;> (try simp_all) <;> (first | rfl | split <;> rfl)))
  · simp only [WidthByteRows.row,rawRight,readSource,tokF,if_true,
      Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false]
    split <;> simp_all <;> (first | rfl | (split <;> (try simp_all) <;> (first | rfl | split <;> rfl)))

private theorem below_right {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c))) :
    Below (WidthByteRows.row (c:=c) r h x).2 23 := by
  rw [raw_right_eq]
  obtain ⟨l,k⟩ := h
  let d := WidthByteRows.decode (readSource (c:=c) x.2).token
  cases k
  · simp only [rawRight,Bool.false_eq_true,if_false,Bool.false_and,Bool.not_false,Bool.true_and]
    have B := below_prep (c:=c) false d
    split
    · exact below_comp _ _ B (below_token _ _)
    · split
      · exact below_comp _ _ B (below_token _ _)
      · exact B
  · simp only [rawRight,if_true,Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false,Bool.true_and]
    have B := below_prep (c:=c) true d
    apply below_comp _ _ _ (below_door _ _)
    split
    · exact B
    · split <;> exact B

/-- The responder data never changes, on a seam or in the interior. -/
theorem right_data_hold {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c))) :
    readData (c:=c) ((patchPair (BStarShort.widthWork (c:=c) r h x) x).2) =
      readData (c:=c) x.2 := by
  apply data_frame
  intro i hi _
  rw [BStarShort.widthWork_mask,below_right (c:=c) r h x i hi]
  rfl

private theorem left_raw_eq {c : Nat} (r : Nat) (l k : Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    (BStarShort.widthWork (c:=c) r (l,k) x).1 =
    let f := WidthByteRows.decode (readSource (c:=c) x.1).token
    let d := WidthByteRows.decode (readSource (c:=c) x.2).token
    let a := prepPatch (c:=c) l f
    let work := WidthByteRows.departing (c:=c) r (WidthByteRows.offset l x.1) x.1 f
    if f.tag==2 then (a.compose work.1).compose (WidthByteRows.tokenPatch c
      (if k then WidthByteRows.finish work.2 else WidthByteRows.trailToken))
    else if (k && f.tag==1) then a.compose (WidthByteRows.tokenPatch c WidthByteRows.emptyToken)
    else if (!k && d.tag==3) then a.compose (WidthByteRows.tokenPatch c d)
    else if (!k && f.tag==1 && d.tag==0) then a.compose (WidthByteRows.tokenPatch c WidthByteRows.emptyToken)
    else a := by
  cases k
  · simp only [BStarShort.widthWork_initiator,WidthByteRows.row,readSource,tokF,
      Bool.false_eq_true,if_false,Bool.false_and,Bool.not_false,Bool.true_and]
    split <;> simp_all <;> (first | rfl | (split <;> (try simp_all) <;> (first | rfl | split <;> rfl)))
  · simp only [BStarShort.widthWork_initiator,WidthByteRows.row,readSource,tokF,
      if_true,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false]
    split <;> simp_all <;> (first | rfl | (split <;> (try simp_all) <;> (first | rfl | split <;> rfl)))

@[simp] private theorem read_source {c : Nat} (x : BitVec (WidthByteRows.W c)) :
    (read (c:=c) x).source=readSource (c:=c) x := rfl
@[simp] private theorem read_data {c : Nat} (x : BitVec (WidthByteRows.W c)) :
    (read (c:=c) x).data=readData (c:=c) x := rfl

private theorem left_transfer {c : Nat} (r : Nat) (l k : Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    read (c:=c) ((patchPair (BStarShort.widthWork (c:=c) r (l,k) x) x).1) =
      (step c r (WidthByteRows.offset l x.1) (l,k) (Pair.map (read (c:=c)) x)).1 := by
  change read (c:=c) (((BStarShort.widthWork (c:=c) r (l,k) x).1).apply x.1)=_
  rw [left_raw_eq]
  let f := WidthByteRows.decode (readSource (c:=c) x.1).token
  let d := WidthByteRows.decode (readSource (c:=c) x.2).token
  let a := prepPatch (c:=c) l f
  let i := WidthByteRows.offset l x.1
  have W := execute_prepared (c:=c) r i l x.1 f
  have V := congrArg Prod.snd (execute_transfer (c:=c) r i x.1 f)
  change _ = (step c r i (l,k) (⟨readSource (c:=c) x.1,readData (c:=c) x.1⟩,
    ⟨readSource (c:=c) x.2,readData (c:=c) x.2⟩)).1
  cases k
  · simp only [step,Bool.false_eq_true,if_false,Bool.false_and,Bool.not_false,Bool.true_and]
    split
    · rename_i F
      have F' : (f.tag==2)=true := F
      have H : ((WidthByteRows.decode (readSource (c:=c) x.1).token).tag == 2)=true := F'
      simp only [Patch.compose_apply,token_read]
      have Q := W
      dsimp only at Q
      rw [Patch.compose_apply] at Q
      rw [Q]
      rfl
    · rename_i F
      have H : ¬((WidthByteRows.decode (readSource (c:=c) x.1).token).tag==2)=true := F
      split
      · rename_i D
        have D' : (d.tag==3)=true := D
        have HD : ((WidthByteRows.decode (readSource (c:=c) x.2).token).tag==3)=true := D'
        simp only [Patch.compose_apply,token_read,prep_read] <;> rfl
      · rename_i D
        have HD : ¬((WidthByteRows.decode (readSource (c:=c) x.2).token).tag==3)=true := D
        split
        · rename_i E
          simp only [Patch.compose_apply,token_read,prep_read] <;> rfl
        · rename_i E
          simp only [prep_read] <;> rfl
  · simp only [step,if_true,Bool.not_true,Bool.false_and,Bool.true_and,
      Bool.false_eq_true,if_false]
    split
    · rename_i F
      have H : ((WidthByteRows.decode (readSource (c:=c) x.1).token).tag == 2)=true := F
      simp only [Patch.compose_apply,token_read]
      have Q := W
      dsimp only at Q
      rw [Patch.compose_apply] at Q
      rw [Q,V]
    · rename_i F
      have H : ¬((WidthByteRows.decode (readSource (c:=c) x.1).token).tag==2)=true := F
      split
      · rename_i E
        simp only [Patch.compose_apply,token_read,prep_read] <;> rfl
      · rename_i E
        simp only [prep_read] <;> rfl

private theorem right_transfer {c : Nat} (r : Nat) (l k : Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    read (c:=c) ((patchPair (BStarShort.widthWork (c:=c) r (l,k) x) x).2) =
      (step c r (WidthByteRows.offset l x.1) (l,k) (Pair.map (read (c:=c)) x)).2 := by
  cases k
  · change read (c:=c) (((WidthByteRows.row (c:=c) r (l,false) x).2).apply x.2)=_
    rw [raw_right_eq]
    let f := WidthByteRows.decode (readSource (c:=c) x.1).token
    let i := WidthByteRows.offset l x.1
    have V := congrArg Prod.snd (execute_transfer (c:=c) r i x.1 f)
    change _ = (step c r i (l,false) (⟨readSource (c:=c) x.1,readData (c:=c) x.1⟩,
      ⟨readSource (c:=c) x.2,readData (c:=c) x.2⟩)).2
    simp only [step,rawRight,Bool.false_eq_true,if_false,Bool.false_and,Bool.not_false,Bool.true_and]
    split
    · simp only [Patch.compose_apply,token_read,prep_read]
      rw [V]
      rfl
    · split
      · simp only [Patch.compose_apply,token_read,prep_read] <;> rfl
      · split <;> (rw [prep_read] <;> rfl)
  · let y := (patchPair (BStarShort.widthWork (c:=c) r (l,true) x) x).2
    have E : read (c:=c) y =
      ⟨BStarWidthTransferPair.rightSource (readSource (c:=c) x.2), readData (c:=c) x.2⟩ := by
      unfold read
      rw [BStarWidthTransferPair.header_source_transfer r l x,right_data_hold r (l,true) x]
    rw [E]
    change _ = (step c r (WidthByteRows.offset l x.1) (l,true)
      (⟨readSource (c:=c) x.1,readData (c:=c) x.1⟩,⟨readSource (c:=c) x.2,readData (c:=c) x.2⟩)).2
    simp only [step,if_true]
    split <;> rfl

/-- Exact all-byte width work transfer on both endpoints, before the
wrapper's successor-header and offset assignments. Both geometry
arguments are read from the old pair, and the old K bytes are syntax. -/
theorem work_transfer {c : Nat} (r : Nat) (h : Pair Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) :
    Pair.map (read (c:=c)) (patchPair (BStarShort.widthWork (c:=c) r h x) x) =
      step c r (WidthByteRows.offset h.1 x.1) h (Pair.map (read (c:=c)) x) := by
  obtain ⟨l,k⟩ := h
  apply Prod.ext
  · exact left_transfer r l k x
  · exact right_transfer r l k x

end L4.BStarWidthTransferFull

