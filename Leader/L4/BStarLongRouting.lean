import Leader.L4.BStarLongRoutingFrame

/-! Exact raw transit-slot projection of the concrete long row. Source
K0 can be written by the source door and is intentionally separate. -/
namespace L4.BStarLongRouting
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport
open BStarLongClaims BStarLongLayout BStarLongToken BStarLongRoutingFrame

abbrev RawK := AtK → BitVec 52

def readRaw (x : Pair (BitVec LW)) : RawK :=
  fun a => (kField a.occurrence).read (lane (a.side==.right) x)

def putRaw (k : BitVec 52) (a : AtK) (w : KWrite) : BitVec 52 :=
  if a=w.1 then encode w.2 else k

theorem k_ranges (j : Fin 11) (hj : j.val≠0) {i : Nat} (hi : i<52) :
    1192 ≤ (kField j).offset+i ∧ (kField j).offset+i<1712 := by
  simp only [kField,kBase]
  have := j.isLt
  omega

theorem read_frame (x : Pair (BitVec LW)) (a : AtK) (h : a.occurrence.val≠0)
    (t : Bool × Patch LW) (F : Frame t.2) :
    readRaw (runWrite x t) a=readRaw x a := by
  obtain ⟨s,j⟩ := a
  obtain ⟨b,q⟩ := t
  have E (z : BitVec LW) : (kField j).read (q.apply z)=(kField j).read z := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact Patch.hold _ _ _ (F _ (k_ranges j h hi).1 (k_ranges j h hi).2)
  cases s <;> cases b <;> simp [readRaw,lane,runWrite,E]

theorem fold_frame (ls : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (a : AtK) (h : a.occurrence.val≠0) (F : ∀ t∈ls, Frame t.2) :
    readRaw (ls.foldl runWrite x) a=readRaw x a := by
  induction ls generalizing x with
  | nil => rfl
  | cons t ls ih =>
    rw [List.foldl_cons,ih _ (fun u hu => F u (List.mem_cons_of_mem _ hu)),
      read_frame _ _ h _ (F _ List.mem_cons_self)]

theorem read_put (x : Pair (BitVec LW)) (a : AtK) (w : KWrite) :
    readRaw (runWrite x (lowerOne w)) a=putRaw (readRaw x a) a w := by
  obtain ⟨⟨s,j⟩,t⟩ := w
  obtain ⟨r,i⟩ := a
  cases s <;> cases r
  all_goals
    by_cases h : i=j
    · subst j
      simp [readRaw,runWrite,lowerOne,lane,putRaw,setToken,Field.read_assign]
    · simp [readRaw,runWrite,lowerOne,lane,putRaw,h,other_token_raw_holds]

theorem fold_put (ls : List KWrite) (x : Pair (BitVec LW)) (a : AtK) :
    readRaw ((ls.map lowerOne).foldl runWrite x) a =
      ls.foldl (fun k t => putRaw k a t) (readRaw x a) := by
  induction ls generalizing x with
  | nil => rfl
  | cons t ls ih => simp only [List.map_cons,List.foldl_cons,ih,read_put]

theorem selected_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : CmdOffer) :
    ∀ t∈(selected g x o).work, Frame t.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · split
    · intro t ht; simp at ht
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      rename_i s p hp
      unfold BStarLongDoor.oldDoor at hp
      dsimp only at hp
      repeat first
        | contradiction
        | (injection hp with hp'; rw [← hp']; exact repair_frame)
        | (injection hp with hp'; rw [← hp']; exact issue_frame _ _)
        | (injection hp with hp'; rw [← hp']; exact reply_frame _ _ _)
        | split at hp
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      exact accept_frame _ _ _
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact numeric_visit _ _ _ _
    · exact execute_frame _ _ _ _

theorem selected_fold_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) (H : ∀ t∈acc.work, Frame t.2) :
    ∀ t∈(os.foldl (fun acc o => Selected.append acc (selected g x o)) acc).work,
      Frame t.2 := by
  induction os generalizing acc with
  | nil => exact H
  | cons o os ih =>
    apply ih
    intro t ht
    exact (List.mem_append.mp ht).elim (H t) (selected_frame g x o t)

theorem clear_frame (g : LongGeometry) : Frame (nonheader g) := by
  unfold nonheader
  split
  · exact zero
  · unfold BStarLongOutgoing.descriptorClear BStarLongDoor.clearFile
    exact compose (compose (compose (BStarLongRoutingFrame.assign _ _ (.inr (by decide)))
      (BStarLongRoutingFrame.assign _ _ (.inr (by decide))))
      (BStarLongRoutingFrame.assign _ _ (.inr (by decide))))
      (compose (BStarLongRoutingFrame.assign _ _ (.inr (by decide)))
        (BStarLongRoutingFrame.assign _ _ (.inr (by decide))))

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply BStarLongRoutingFrame.assign
  left
  have := a.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset+a.width ≤1192
  omega

theorem copy_frame (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (os : List BStarLongPrep.Offer) :
    ∀ t∈(BStarLongPrep.writes g old os).map Write.patch, Frame t.2 := by
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hw
  exact packet_frame a u

theorem grant_site_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (s : Side) :
    ∀ t∈(BStarLongGrant.siteWrites g x os s).map Write.patch, Frame t.2 := by
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  obtain ⟨j,_,H⟩ := List.mem_filterMap.mp hw
  split at H
  · cases H
    apply BStarLongRoutingFrame.assign
    right
    change 1712≤2359-j.val
    have := j.isLt
    omega
  · contradiction

theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, Frame t.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t h
  exact h.elim (grant_site_frame g x os .left t) (grant_site_frame g x os .right t)

def routing (g : Pair LongGeometry) (x : Pair (BitVec LW)) : List KWrite :=
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let s : Selected := u.departures.foldl
    (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let ks := normalization g (readK x) ++ s.k
  ks ++ observations g (readK x) ks

theorem raw_transit (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : AtK) (h : a.occurrence.val≠0) :
    readRaw (patchPair (longWork g x) x) a =
      (routing g x).foldl (fun k t => putRaw k a t) (readRaw x a) := by
  rw [long_exec]
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let s : Selected := u.departures.foldl
    (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let start := normalization g (readK x)
  let finish := observations g (readK x) (start++s.k)
  let hold := [(false,nonheader g.1),(true,nonheader g.2)] ++
    u.writes.map Write.patch ++ d.writes.map Write.patch ++ s.work
  simp only [longTrace,routing]
  rw [show (start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
      u.writes.map Write.patch ++ d.writes.map Write.patch ++ s.work ++
      (s.k++finish).map lowerOne) =
      start.map lowerOne ++ hold ++ (s.k++finish).map lowerOne by
    simp only [hold,List.append_assoc]]
  change readRaw ((start.map lowerOne ++ hold ++ (s.k++finish).map lowerOne).foldl runWrite x) a =
    ((start++s.k)++finish).foldl (fun k t => putRaw k a t) (readRaw x a)
  have F : ∀ t∈hold, Frame t.2 := by
    intro t ht
    simp only [hold,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with (((rfl|rfl)|ht)|ht)|ht
    · exact clear_frame _
    · exact clear_frame _
    · exact grant_frame g x d.offered t ht
    · exact copy_frame g _ _ t ht
    · exact selected_fold_frame g x _ _ (by simp) t ht
  rw [List.foldl_append,List.foldl_append,fold_put,fold_frame hold _ a h F,fold_put]
  simp only [List.foldl_append]

theorem untouched_raw (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (a : AtK) (h : a.occurrence.val≠0) (H : ∀ w∈routing g x, w.1≠a) :
    readRaw (patchPair (longWork g x) x) a = readRaw x a := by
  rw [raw_transit g x a h]
  generalize routing g x=ls at H ⊢
  generalize readRaw x a=k
  induction ls generalizing k with
  | nil => rfl
  | cons t ls ih =>
    simp only [List.foldl_cons,putRaw,Ne.symm (H t List.mem_cons_self),if_false]
    exact ih (fun w hw => H w (List.mem_cons_of_mem _ hw)) k

#print axioms raw_transit
#print axioms untouched_raw
end L4.BStarLongRouting
