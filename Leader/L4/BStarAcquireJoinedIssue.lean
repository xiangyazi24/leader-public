import Leader.L4.BStarDoorUnique
import Leader.L4.BStarAcquireSource
import Leader.L4.BStarAcquireLandingHop

/-! The actual joined ISSUE writes at the unique old right ACQUIRE door. -/
namespace L4.BStarAcquireJoinedIssue
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims BStarLongCommand BStarLongDoor
open BStarCommitIssue BStarAcquireSource BStarLongEvents

def Frame (p : Patch LW) : Prop :=
  ∀ i, ((1712 ≤ i ∧ i < 1764) ∨ (2195 ≤ i ∧ i < 2206)) → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i hi
  simp [Patch.compose,hp i hi,hq i hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤1712 ∨ (1764≤f.offset ∧ f.offset+n≤2195) ∨ 2206≤f.offset) : Frame (f.assign b) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  rcases h with h|⟨h,h'⟩|h <;> rcases hi with hi|hi <;> omega

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
    exact assign _ _ (.inr (.inr (by simp [bankDigit,bankPart,bankBase]; omega)))
  have hh (b : Bool) (bank : Fin 3) :
      ∀ q∈dimHeaders n b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inr (.inr (by simp [bankHeader,bankPart,bankBase]; omega)))
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
    · exact assign _ _ (.inr (.inr (by decide)))

open BStarLongOutgoing BStarLongPublication in
theorem execute_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (execute g j x p).row := by
  have dc : Frame descriptorClear :=
    compose (assign _ _ (.inr (.inr (by decide)))) (assign _ _ (.inr (.inr (by decide))))
  have sf (d : Descriptor) : Frame (sealField.assign (packOptional (some d))) :=
    assign _ _ (.inr (.inr (by decide)))
  have setterF (b : Fin 3) : Frame (setter b) :=
    compose (compose (assign _ _ (.inr (.inr (by decide))))
      (assign _ _ (.inr (.inr (by decide))))) (assign _ _ (.inr (.inr (by decide))))
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

private def Keeps (t : Bool × Patch LW) : Prop := t.1=false ∨ Frame t.2

private theorem read_frame {w : Nat} (f : Field LW w) (q : Patch LW) (x : BitVec LW)
    (h : ∀ k<w, (1712≤f.offset+k ∧ f.offset+k<1764) ∨ (2195≤f.offset+k ∧ f.offset+k<2206))
    (H : Frame q) : f.read (q.apply x)=f.read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simpa only [Field.read,BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and] using
    Patch.hold q x (f.offset+k) (H _ (h k hk))

private theorem kFrame (q : Patch LW) (x : BitVec LW) (H : Frame q) :
    atSite (q.apply x) 0=atSite x 0 := by
  unfold atSite
  rw [read_frame (kField 0) _ _ (fun k hk => .inl (by change 1712≤1712+k ∧ 1712+k<1764; omega)) H]

private theorem phaseFrame (q : Patch LW) (x : BitVec LW) (H : Frame q) :
    ctrlPhase.read (q.apply x)=ctrlPhase.read x :=
  read_frame ctrlPhase _ _ (fun k hk => .inr (by change 2195≤2204+k ∧ 2204+k<2206; omega)) H

def view (x : BitVec LW) := (atSite x 0,ctrlPhase.read x)

private theorem view_frame (t : Bool × Patch LW) (x : Pair (BitVec LW)) (H : Keeps t) :
    view (runWrite x t).2=view x.2 := by
  rcases H with H|H
  · simp [runWrite,H]
  · obtain ⟨s,q⟩ := t
    cases s
    · rfl
    · exact Prod.ext (kFrame q x.2 H) (phaseFrame q x.2 H)

private theorem view_fold (ws : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (H : ∀ t∈ws,Keeps t) : view (ws.foldl runWrite x).2=view x.2 := by
  induction ws generalizing x with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons,ih _ (fun u hu => H u (List.mem_cons_of_mem _ hu)),
      view_frame _ _ (H t List.mem_cons_self)]

private theorem stage_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (h : ∀ t : Token,o.2≠.door t) :
    ∀ w∈(selected g x o).work,Keeps w := by
  rcases o with ⟨c,a⟩
  cases a <;> simp only [selected]
  all_goals try (intro _ E; exact (List.not_mem_nil E).elim)
  · exact (h _ rfl).elim
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact .inr (numeric_visit _ _ _ _)
    · exact .inr (execute_frame _ _ _ _)

private theorem away_write (w : KWrite) (h : w.1≠R 0) : Keeps (lowerOne w) := by
  rcases w with ⟨⟨s,j⟩,t⟩
  cases s
  · exact .inl rfl
  · apply Or.inr
    change Frame (setToken j t)
    unfold setToken
    apply assign
    left
    have J : j.val≠0 := fun E => h (by have Z : j=(0:Fin 11) := Fin.ext E; cases Z; rfl)
    change 1192+52*(10-j.val)+52≤1712
    omega

private theorem observer_away (g : Pair LongGeometry) (x : ReadK) (ks : List KWrite) :
    ∀ w∈observations g x ks, w.1≠R 0 := by
  intro w h he
  unfold observations at h
  obtain ⟨a,_,H⟩ := List.mem_filterMap.mp h
  split at H
  · contradiction
  · split at H
    · rename_i p hp
      obtain ⟨q,_,hq⟩ := Option.map_eq_some_iff.mp H
      have E : a=R 0 := (congrArg Prod.fst hq).trans he
      subst a
      simp [observe,gate,R] at *
    · contradiction

private theorem row_folds (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    let z := os.foldl (fun acc o => acc.append (selected g x o)) a
    z.work=a.work++os.flatMap (fun o => (selected g x o).work) ∧
      z.k=a.k++os.flatMap (fun o => (selected g x o).k) := by
  induction os generalizing a with
  | nil => simp
  | cons h t ih =>
    simpa [Selected.append,List.append_assoc] using ih (a.append (selected g x h))

private theorem issued_view (x : BitVec LW) :
    view ((issued acquire (2^33)).apply x)=(.forward initPayload,2) := by
  refine Prod.ext (acquire_issued_token x) ?_
  simp only [view,issued,acquire,show (5==1)=false by decide,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  unfold setToken
  rw [Field.read_other_assign _ _ _ _ (.inr (by decide)),Field.read_assign]

/-- Any one literal door write with a constant K0/phase view survives all
post-door assignments, including simultaneous terminal and race rows. -/
theorem long_door_view (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (w : Patch LW) (out : Token × BitVec 2)
    (H : oldDoor x.2 (bind g.2 0 (atSite x.2 0))=.write w)
    (Hw : ∀ old, view (w.apply old)=out) :
    view (patchPair (longWork g x) x).2=out := by
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let O := actualOffers g x
  let door : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
  obtain ⟨pre,post,E,NP,NQ⟩ := BStarDoorUnique.actual_door_split g x hh
  change O=pre++door::post at E
  have D : (selected g x door).work=[(true,w)] ∧
      (selected g x door).k=[] := by
    simp [selected,door,doorClaim,atOld,R,lane,H]
  have P : (O.map Prod.fst).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) := by
    rw [show O.map Prod.fst=orderedCommands g from actualOffers_claims g x]
    exact select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
  rw [E,List.map_append,List.map_cons] at P
  have own : R 0∈door.1.slots := by change R 0∈doorClaim.slots; decide
  have away (o : CmdOffer) (ho : o∈pre ∨ o∈post) (w : KWrite)
      (hw : w∈(selected g x o).k) : w.1≠R 0 := by
    intro B
    have F := BStarAcquireLandingHop.selected_slot g x o w hw
    rw [B] at F
    rcases ho with h|h
    · exact (List.pairwise_append.mp P).2.2 o.1 (List.mem_map.mpr ⟨o,h,rfl⟩)
        door.1 List.mem_cons_self _ own F
    · exact (List.pairwise_cons.mp (List.pairwise_append.mp P).2.1).1 o.1
        (List.mem_map.mpr ⟨o,h,rfl⟩) _ F own
  let sr : Selected := O.foldl (fun acc o => acc.append (selected g x o)) ⟨[],[],[]⟩
  have Q := row_folds g x O ⟨[],[],[]⟩
  change sr.work=[]++O.flatMap _ ∧ sr.k=[]++O.flatMap _ at Q
  have Z : sr.k=pre.flatMap (fun o => (selected g x o).k) ++
      post.flatMap (fun o => (selected g x o).k) := by
    simpa [E,D.2] using Q.2
  have W : sr.work=pre.flatMap (fun o => (selected g x o).work) ++
      [(true,w)] ++ post.flatMap (fun o => (selected g x o).work) := by
    simpa [E,D.1,List.append_assoc] using Q.1
  let start := normalization g (readK x)
  let final := observations g (readK x) (start++sr.k)
  let before := start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    u.writes.map Write.patch ++ d.writes.map Write.patch ++ pre.flatMap (fun o => (selected g x o).work)
  let after := post.flatMap (fun o => (selected g x o).work) ++ (sr.k++final).map lowerOne
  have A (t) (ht : t∈after) : Keeps t := by
    rcases List.mem_append.mp ht with h|h
    · obtain ⟨o,ho,ht⟩ := List.mem_flatMap.mp h
      exact stage_work g x o (NQ o ho) t ht
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
      apply away_write
      rcases List.mem_append.mp hw with hw|hw
      · rw [Z] at hw
        rcases List.mem_append.mp hw with h|h <;>
          obtain ⟨o,ho,hm⟩ := List.mem_flatMap.mp h
        · exact away o (.inl ho) w hm
        · exact away o (.inr ho) w hm
      · exact observer_away g _ _ w hw
  have X : (longTrace g x).assignments=before++[(true,w)]++after := by
    change start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
      u.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work ++ (sr.k++final).map lowerOne=_
    rw [W]
    simp only [before,after,List.append_assoc]
  rw [long_exec,X,List.foldl_append,view_fold _ _ A,List.foldl_append]
  exact Hw _

theorem long_issue (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true)
    (ph : (ctrlPhase.read x.2).toNat=1) (op : (ctrlOp.read x.2).toNat=acquire) :
    view (patchPair (longWork g x) x).2=(.forward initPayload,2) :=
  long_door_view g x hh _ _ (acquire_issue _ _ ph op) issued_view

/-- Fully joined source door view for a valid old header. Scratch and
every other composed field frame the old-header door's K0/phase. -/
theorem joined_door_view (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (write : Patch LW) (out : Token × BitVec 2) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    (oldHeaders b x.2).h6=true →
    LongDoorGuard.valid manifest x.2.long=true →
    oldDoor x.2.long (bind g.2 0 (atSite x.2.long 0))=.write write →
    (∀ old, view (write.apply old)=out) →
    view (largePair b x).2.long=out := by
  dsimp only
  intro hh hv hwrite hout
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have E : (largePair b x).2.long=q.2.apply (w.2.apply raw.2) := by
    change (LongDoorGuard.guard manifest g.2.axes.h6 raw.2 (w.2.compose q.2)).apply raw.2=_
    rw [show g.2.axes.h6=true from hh,LongDoorGuard.valid_no_override _ _ _ (show LongDoorGuard.valid manifest raw.2=true from hv)]
    exact Patch.compose_apply _ _ _
  have F : Frame q.2 := assign BStarTrace.offField _ (.inr (.inr (by decide)))
  rw [E,show view (q.2.apply (w.2.apply raw.2))=view (w.2.apply raw.2) from
    Prod.ext (kFrame _ _ F) (phaseFrame _ _ F)]
  exact long_door_view g raw hh write out hwrite hout

theorem joined_issue (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true →
    (ctrlPhase.read x.2.long).toNat=1 →
    (ctrlOp.read x.2.long).toNat=acquire →
    atSite (largePair b x).2.long 0=.forward initPayload ∧
      ctrlPhase.read (largePair b x).2.long=2 := by
  dsimp only
  intro hh ph op
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have hv : LongDoorGuard.valid manifest raw.2=true := by
    change ((((ctrlPhase.read x.2.long).toNat==1) || ((ctrlPhase.read x.2.long).toNat==2)) &&
      decide ((ctrlOp.read x.2.long).toNat<manifest.opcodes))=true
    simp [ph,op]
    decide
  have V := joined_door_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x _ _ hh hv
    (acquire_issue _ _ ph op) issued_view
  exact ⟨congrArg Prod.fst V,congrArg Prod.snd V⟩

end L4.BStarAcquireJoinedIssue
