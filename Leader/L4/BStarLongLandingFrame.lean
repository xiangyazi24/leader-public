import Leader.L4.BStarLongWork

/-! The K, COPY and grant stages frame the literal publication fields.
The mask assertions include idempotent writes. -/
namespace L4.BStarLongLandingFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongTransport

def publicationBit (i : Nat) : Prop :=
  (2206 ≤ i ∧ i < 2222) ∨ (2360 ≤ i ∧ i < 2362)

def Frame (p : Patch LW) : Prop :=
  ∀ i, publicationBit i → p.mask.getLsbD i=false

def readPublication (x : BitVec LW) : BitVec 2 × BitVec 8 × BitVec 8 :=
  (selector.read x,stage.read x,sealField.read x)

theorem read_of_frame (p : Patch LW) (x : BitVec LW) (h : Frame p) :
    readPublication (p.apply x)=readPublication x := by
  have F {k : Nat} (f : Field LW k)
      (hi : ∀ j, j<k → publicationBit (f.offset+j)) :
      f.read (p.apply x)=f.read x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [Field.read,BitVec.getLsbD_extractLsb',hj,decide_true,Bool.true_and]
    exact Patch.hold _ _ _ (h _ (hi j hj))
  unfold readPublication
  rw [F selector (by intro j hj; change publicationBit (2360+j); unfold publicationBit; omega),
      F stage (by intro j hj; change publicationBit (2214+j); unfold publicationBit; omega),
      F sealField (by intro j hj; change publicationBit (2206+j); unfold publicationBit; omega)]

/-- A field assignment is safe if its half-open interval lies in a gap
between publication fields. -/
theorem assign_frame {k : Nat} (f : Field LW k) (u : BitVec k)
    (hf : f.offset+k ≤ 2206 ∨ (2222 ≤ f.offset ∧ f.offset+k ≤ 2360) ∨
      2362 ≤ f.offset) : Frame (f.assign u) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨ha,hb⟩ := (Field.inMask f u i).mp h
  rcases hf with h0|⟨h1,h2⟩|h3 <;> rcases hi with ⟨a,b⟩|⟨a,b⟩ <;> omega

def LeftFrame (t : Bool × Patch LW) : Prop := t.1=false → Frame t.2

theorem run_left_frame (t : Bool × Patch LW) (x : Pair (BitVec LW))
    (h : LeftFrame t) : readPublication (runWrite x t).1 = readPublication x.1 := by
  rcases t with ⟨flag,p⟩
  cases flag
  · exact read_of_frame p x.1 (h rfl)
  · rfl

theorem fold_left_frame (ts : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (h : ∀ t∈ts, LeftFrame t) :
    readPublication (ts.foldl runWrite x).1=readPublication x.1 := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons,ih _ (fun u hm => h u (List.mem_cons_of_mem _ hm))]
    exact run_left_frame t x (h t List.mem_cons_self)

theorem k_frame (t : KWrite) : Frame (lowerOne t).2 := by
  unfold lowerOne
  apply assign_frame
  exact .inl (by
    have h := BStarLongLayout.k_before_file t.1.occurrence
    exact Nat.le_trans h (by decide))

theorem k_left_frames (ks : List KWrite) :
    ∀ t∈ks.map lowerOne, LeftFrame t := by
  intro t ht _
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  exact k_frame u

theorem copy_leaf_frame (a : BStarLongPackets.Leaf) (s : Fin 4) :
    Frame (a.assign s) := by
  unfold BStarLongPackets.Leaf.assign
  apply assign_frame
  left
  have hh := a.fits
  change 728+116*(3-s.val)+a.offset+a.width≤2206
  omega

theorem writeAt_frame (s : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt s a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  exact copy_leaf_frame a _

theorem grant_field_frame (j : Fin 3) (b : Bool) :
    Frame ((grant j).assign (BitVec.ofBool b)) := by
  apply assign_frame
  right; left
  change 2222≤2359-j.val ∧ 2359-j.val+1≤2360
  have hj := j.isLt
  omega


theorem data_left_frames (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (ps : List BStarLongPrep.Offer) :
    ∀ t∈(BStarLongPrep.writes g old ps).map Write.patch, LeftFrame t := by
  intro t ht _
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  unfold BStarLongPrep.writes at hw
  obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hw
  exact writeAt_frame a u

theorem grant_site_left_frames (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (s : Side) :
    ∀ t∈(BStarLongGrant.siteWrites g x os s).map Write.patch, LeftFrame t := by
  intro t ht _
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  unfold BStarLongGrant.siteWrites at hw
  obtain ⟨j,_,H⟩ := List.mem_filterMap.mp hw
  split at H
  · cases H
    exact grant_field_frame j _
  · contradiction

theorem grant_left_frames (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, LeftFrame t := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t h
  exact h.elim (grant_site_left_frames g x os .left t) (grant_site_left_frames g x os .right t)

/-- Framing statements for the actual ordered K, grant, and COPY stages.
The stages can start from any intermediate pair, not only their old snapshot. -/
theorem routine_frames (g : Pair LongGeometry) (old : Pair (BitVec LW))
    (first last : List KWrite) (mid : Pair (BitVec LW)) :
    let d := BStarLongCommandData.round g old
    let a := BStarLongGrant.run g old d.offered
    let ts := first.map lowerOne ++ a.writes.map Write.patch ++
      d.writes.map Write.patch ++ last.map lowerOne
    readPublication (ts.foldl runWrite mid).1=readPublication mid.1 := by
  apply fold_left_frame
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ((ht|ht)|ht)|ht
  · exact k_left_frames first t ht
  · exact grant_left_frames g old _ t ht
  · exact data_left_frames g _ _ t ht
  · exact k_left_frames last t ht

#print axioms read_of_frame
#print axioms fold_left_frame
#print axioms k_frame
#print axioms data_left_frames
#print axioms grant_left_frames
#print axioms routine_frames
end L4.BStarLongLandingFrame
