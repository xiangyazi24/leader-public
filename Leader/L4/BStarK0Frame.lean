import Leader.L4.BStarLongRouting
import Leader.L4.BStarDoorUnique

/-! Raw K0 preservation when no routing write touches the target and
the sole possible overlapping source door holds. -/
namespace L4.BStarK0Frame
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongClaims
open BStarLongToken BStarLongLayout BStarLongRouting BStarLongDoor
open BStarLongEvents BStarDoorUnique BStarCommitIssue BStarLongCommandData BStarLongCommand

def Frame (p : Patch LW) : Prop :=
  ∀ i, 1712 ≤ i → i < 1764 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤1712 ∨ 1764≤f.offset) : Frame (f.assign b) := by
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
  assign _ _ (.inr (Nat.le_add_right 1764 _))

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

theorem clear_frame (g : LongGeometry) : Frame (nonheader g) := by
  unfold nonheader
  split
  · exact zero
  · unfold BStarLongOutgoing.descriptorClear BStarLongDoor.clearFile
    exact compose (compose (compose (BStarK0Frame.assign _ _ (.inr (by decide)))
      (BStarK0Frame.assign _ _ (.inr (by decide))))
      (BStarK0Frame.assign _ _ (.inr (by decide))))
      (compose (BStarK0Frame.assign _ _ (.inr (by decide)))
        (BStarK0Frame.assign _ _ (.inr (by decide))))

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply BStarK0Frame.assign
  left
  have := a.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset+a.width ≤1712
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
    apply BStarK0Frame.assign
    right
    change 1764≤2359-j.val
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

private theorem update_isDoor (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (O : BStarLongGrant.Offers) (o : CommandClaim × Offer) :
    doorAction (BStarLongGrant.update g x O o)=doorAction o := by
  obtain ⟨c,q⟩ := o
  cases q <;> try (unfold BStarLongGrant.update; dsimp only; split <;> rfl)
  unfold BStarLongGrant.update
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem cancel_isDoor (f : List (At (Fin 11))) (o : CommandClaim × Offer) :
    doorAction (cancel f o)=doorAction o := by
  obtain ⟨c,q⟩ := o
  cases q <;> try rfl
  unfold cancel
  dsimp only
  split <;> rfl

private theorem check_isDoor (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (o : CommandClaim × Offer) :
    doorAction (o.1,checkOffer g old o)=doorAction o := by
  obtain ⟨c,q⟩ := o
  cases q <;> try rfl
  unfold checkOffer
  dsimp only
  split <;> rfl

private theorem classify_isDoor (c : CommandClaim) (g : LongGeometry) (s t : Token) :
    isDoor (classify c g s t)=doorKind c := by
  unfold classify doorKind
  split
  · simp_all [isDoor]
  · rename_i H
    have H' : (c.kind==.door)=false := by cases E : c.kind==.door <;> simp_all
    rw [H']
    repeat' first | rfl | split

private theorem classify_action (c : CommandClaim) (g : LongGeometry) (s t : Token) :
    doorAction (c,classify c g s t)=doorKind c := classify_isDoor c g s t

private theorem noDoor (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (h : g.2.axes.h6=false) : (actualOffers g x).filter doorAction=[] := by
  unfold actualOffers BStarLongGrant.run BStarLongCommandData.round gated offersOn
  simp only [List.filter_map,Function.comp_def,update_isDoor,cancel_isDoor,
    check_isDoor,classify_action]
  have E : (orderedCommands g).filter doorKind=[] := by
    obtain ⟨x,y⟩ := g
    change y.axes.h6=false at h
    simp only [orderedCommands,commandClaims,ends,h,Bool.false_eq_true,if_false]
    by_cases A : (x.inside && y.inside && !(x.inside && x.last))=true
    · erw [if_pos A]
      by_cases B : (x.inside && x.last)=true
      · erw [if_pos B]; decide +kernel
      · erw [if_neg B]; decide +kernel
    · erw [if_neg A]
      by_cases B : (x.inside && x.last)=true
      · erw [if_pos B]; decide +kernel
      · erw [if_neg B]; decide +kernel
  rw [E]
  rfl

theorem door_eq (g : Pair LongGeometry) (x : Pair (BitVec LW)) (c : CommandClaim)
    (k : Token) (h : (c,.door k)∈actualOffers g x) :
    c=doorClaim ∧ k=bind g.2 0 (atSite x.2 0) := by
  have H : (c,.door k)∈(actualOffers g x).filter doorAction :=
    List.mem_filter.mpr ⟨h,rfl⟩
  cases E : g.2.axes.h6
  · rw [noDoor g x E] at H
    exact (List.not_mem_nil H).elim
  · rw [actual_door_singleton g x E] at H
    have F := List.mem_singleton.mp H
    exact ⟨congrArg Prod.fst F, Offer.door.inj (congrArg Prod.snd F)⟩

private theorem waitHold (x : BitVec LW) (k : Token)
    (valid : LongDoorGuard.valid manifest x=true) (wait : (ctrlPhase.read x).toNat=2)
    (inFlight : k=.trail ∨ ∃ p, k=.forward p) :
    oldDoor x k=.hold := by
  rcases inFlight with rfl|⟨p,rfl⟩ <;> simp [oldDoor,valid,wait]

private theorem selected_at (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : CmdOffer)
    (s : Side)
    (hold : ∀ c k, o=(c,.door k) → c.source.side=s → oldDoor (BStarLongWork.atOld x c.source) k=.hold) :
    ∀ t∈(selected g x o).work, t.1=(s==.right) → Frame t.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · rename_i k
    intro t ht hs
    have hc : c.source.side=s := by
      have G : t.1=(c.source.side==.right) := by
        split at ht
        · simp at ht
        · exact congrArg Prod.fst (List.mem_singleton.mp ht)
        · exact congrArg Prod.fst (List.mem_singleton.mp ht)
      have E := G.symm.trans hs
      have injectiveSide (a b : Side) : (a==.right)=(b==.right) → a=b := by
        cases a <;> cases b <;> decide
      exact injectiveSide _ _ E
    rw [hold c k rfl hc] at ht
    simp at ht
  · intro t ht _
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact numeric_visit _ _ _ _
    · exact execute_frame _ _ _ _

private theorem selected_fold_at (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) (s : Side)
    (ha : ∀ w∈acc.work, w.1=(s==.right) → Frame w.2)
    (ho : ∀ o∈os, ∀ w∈(selected g x o).work, w.1=(s==.right) → Frame w.2) :
    ∀ w∈(os.foldl (fun a o => Selected.append a (selected g x o)) acc).work,
        w.1=(s==.right) → Frame w.2 := by
  induction os generalizing acc with
  | nil => exact ha
  | cons a os ih =>
    apply ih
    · intro w hw
      exact (List.mem_append.mp hw).elim (ha w) (ho a List.mem_cons_self w)
    · exact fun o h => ho o (List.mem_cons_of_mem _ h)

private theorem read_frame (x : Pair (BitVec LW)) (s : Side)
    (t : Bool × Patch LW) (F : t.1=(s==.right) → Frame t.2) :
    readRaw (runWrite x t) ⟨s,0⟩=readRaw x ⟨s,0⟩ := by
  obtain ⟨b,q⟩ := t
  have E (z : BitVec LW) (h : b=(s==.right)) :
      (kField 0).read (q.apply z)=(kField 0).read z := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact Patch.hold _ _ _ (F h (1712+i) (by omega) (by omega))
  cases s <;> cases b <;> simp [readRaw,lane,runWrite,E]

private theorem fold_frame (ls : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (s : Side) (F : ∀ t∈ls, t.1=(s==.right) → Frame t.2) :
    readRaw (ls.foldl runWrite x) ⟨s,0⟩=readRaw x ⟨s,0⟩ := by
  induction ls generalizing x with
  | nil => rfl
  | cons t ls ih =>
    rw [List.foldl_cons,ih _ (fun u hu => F u (List.mem_cons_of_mem _ hu)),
      read_frame _ _ _ (F _ List.mem_cons_self)]

theorem k0_routing_only (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (side : Side) (hold : ∀ c k, (c,.door k)∈actualOffers g x →
      c.source.side=side → oldDoor (BStarLongWork.atOld x c.source) k=.hold) :
    readRaw (patchPair (longWork g x) x) ⟨side,0⟩ =
      (routing g x).foldl (fun k t => putRaw k ⟨side,0⟩ t) (readRaw x ⟨side,0⟩) := by
  rw [long_exec]
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let s : Selected := u.departures.foldl
    (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let start := normalization g (readK x)
  let finish := observations g (readK x) (start++s.k)
  let work := [(false,nonheader g.1),(true,nonheader g.2)] ++
    u.writes.map Write.patch ++ d.writes.map Write.patch ++ s.work
  simp only [longTrace,routing]
  rw [show (start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
      u.writes.map Write.patch ++ d.writes.map Write.patch ++ s.work ++
      (s.k++finish).map lowerOne) =
      start.map lowerOne ++ work ++ (s.k++finish).map lowerOne by
    simp only [work,List.append_assoc]]
  change readRaw ((start.map lowerOne ++ work ++ (s.k++finish).map lowerOne).foldl runWrite x) ⟨side,0⟩ =
    ((start++s.k)++finish).foldl (fun k t => putRaw k ⟨side,0⟩ t) (readRaw x ⟨side,0⟩)
  have F : ∀ t∈work, t.1=(side==.right) → Frame t.2 := by
    intro t ht H
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with (((rfl|rfl)|ht)|ht)|ht
    · exact clear_frame _
    · exact clear_frame _
    · exact grant_frame g x d.offered t ht
    · exact copy_frame g _ _ t ht
    · apply selected_fold_at g x _ _ side (by simp) _ t ht H
      intro o ho
      exact selected_at g x o side (fun c k h hc => hold c k (h ▸ ho) hc)
  rw [List.foldl_append,List.foldl_append,fold_put,fold_frame work _ side F,fold_put]
  simp only [List.foldl_append]

private theorem no_target_fold (a : AtK) (rs : List KWrite) (k : BitVec 52)
    (h : ∀ w∈rs, w.1≠a) :
    rs.foldl (fun k t => putRaw k a t) k = k := by
  induction rs generalizing k with
  | nil => rfl
  | cons t rs ih =>
    simp only [List.foldl_cons,putRaw,Ne.symm (h t List.mem_cons_self),if_false]
    exact ih _ (fun w hw => h w (List.mem_cons_of_mem _ hw))

theorem left_k0 (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (h : ∀ w∈routing g x, w.1≠L 0) :
    readRaw (patchPair (longWork g x) x) (L 0) = readRaw x (L 0) := by
  change readRaw (patchPair (longWork g x) x) ⟨.left,0⟩ = readRaw x ⟨.left,0⟩
  rw [k0_routing_only g x .left]
  · exact no_target_fold _ _ _ h
  · intro c k hmem H
    rw [(door_eq g x c k hmem).1] at H
    contradiction

theorem right_wait_k0 (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (valid : LongDoorGuard.valid manifest x.2=true) (wait : (ctrlPhase.read x.2).toNat=2)
    (bound : bind g.2 0 (atSite x.2 0)=.trail ∨
      ∃ p, bind g.2 0 (atSite x.2 0)=.forward p)
    (h : ∀ w∈routing g x, w.1≠R 0) :
    readRaw (patchPair (longWork g x) x) (R 0) = readRaw x (R 0) := by
  change readRaw (patchPair (longWork g x) x) ⟨.right,0⟩ = readRaw x ⟨.right,0⟩
  rw [k0_routing_only g x .right]
  · exact no_target_fold _ _ _ h
  · intro c k hmem _
    obtain ⟨rfl,rfl⟩ := door_eq g x c k hmem
    exact waitHold x.2 _ valid wait bound

#print axioms left_k0
#print axioms right_wait_k0

end L4.BStarK0Frame
