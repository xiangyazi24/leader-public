import Leader.L4.BStarArithmeticControllerReturn
import Leader.L4.BStarResetControllerProgress
import Leader.L4.BStarAcquireRingFrame

namespace L4.BStarJoinedControllerReturn
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims BStarLongCommand BStarLongDoor
open BStarCommitIssue BStarLongEvents BStarAcquireJoinedIssue BStarResetControllerEntry

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

private theorem opFrame (q : Patch LW) (x : BitVec LW) (H : Frame q) :
    ctrlOp.read (q.apply x)=ctrlOp.read x :=
  read_frame ctrlOp _ _ (fun k hk => .inr (by change 2195≤2195+k ∧ 2195+k<2206 at ⊢; change k<9 at hk; omega)) H

private theorem view_frame (t : Bool × Patch LW) (x : Pair (BitVec LW)) (H : Keeps t) :
    snapshot (runWrite x t).2=snapshot x.2 := by
  rcases H with H|H
  · simp [runWrite,H]
  · obtain ⟨s,q⟩ := t
    cases s
    · rfl
    · exact Prod.ext (Prod.ext (kFrame q x.2 H) (phaseFrame q x.2 H)) (opFrame q x.2 H)

private theorem view_fold (ws : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (H : ∀ t∈ws,Keeps t) : snapshot (ws.foldl runWrite x).2=snapshot x.2 := by
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
    apply BStarAcquireJoinedIssue.assign
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

theorem long_snapshot (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (w : Patch LW) (out : (Token × BitVec 2) × BitVec 9)
    (S : let door : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
      (selected g x door).work=[(true,w)] ∧ (selected g x door).k=[])
    (Hw : ∀ old, snapshot (w.apply old)=out) :
    snapshot (patchPair (longWork g x) x).2=out := by
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let O := actualOffers g x
  let door : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
  obtain ⟨pre,post,E,NP,NQ⟩ := BStarDoorUnique.actual_door_split g x hh
  change O=pre++door::post at E
  have D : (selected g x door).work=[(true,w)] ∧
      (selected g x door).k=[] := S
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

theorem joined_snapshot (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (write : Patch LW) (out : (Token × BitVec 2) × BitVec 9) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    (oldHeaders b x.2).h6=true →
    LongDoorGuard.valid manifest x.2.long=true →
    (let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
     let door : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))
     (selected g raw door).work=[(true,write)] ∧ (selected g raw door).k=[]) →
    (∀ old, snapshot (write.apply old)=out) →
    snapshot (largePair b x).2.long=out := by
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
  rw [E,show snapshot (q.2.apply (w.2.apply raw.2))=snapshot (w.2.apply raw.2) from
    Prod.ext (Prod.ext (kFrame _ _ F) (phaseFrame _ _ F)) (opFrame _ _ F)]
  exact long_snapshot g raw hh write out hwrite hout

open BStarResetControllerProgress BStarArithmeticControllerReturn BStarLongArithmetic

private theorem snapshot_frame (q : Patch LW) (x : BitVec LW) (H : Frame q) :
    snapshot (q.apply x)=snapshot x :=
  Prod.ext (Prod.ext (kFrame q x H) (phaseFrame q x H)) (opFrame q x H)

theorem snapshot_schedule (op : Nat) (x : BitVec LW) :
    snapshot ((schedule op).apply x)=((.empty,1),BitVec.ofNat 9 op) :=
  Prod.ext (BStarResetDoor.schedule_view op x)
    (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) (schedule_control op x))

theorem snapshot_restart (x : BitVec LW) :
    snapshot (faultRestart.apply x)=((.empty,1),0) :=
  Prod.ext (BStarResetDoor.restart_view x)
    (congrArg (fun q : BitVec 2 × BitVec 9 => q.2) (restart_control x))

theorem arithmetic_snapshot (old y : BitVec LW) (op : Nat) (f : Payload) :
    snapshot ((acceptFile old op f).apply y)=((.empty,1),BitVec.ofNat 9 (successor old op)) := by
  cases H : nodeOf op with
  | none =>
    simp only [acceptFile,successor,H]
    exact snapshot_restart y
  | some i =>
    cases I : get i with
    | none =>
      simp only [acceptFile,successor,H,I]
      exact snapshot_restart y
    | some c =>
      by_cases O : op<407
      · simp only [acceptFile,successor,H,I,if_pos O,Patch.compose_apply,snapshot_schedule]
      · by_cases V : ((capturedSelector 1).read old).toNat<3
        · simp only [acceptFile,successor,H,I,if_neg O,dif_pos V,if_pos V,Patch.compose_apply,snapshot_schedule]
        · simp only [acceptFile,successor,H,I,if_neg O,dif_neg V,if_neg V]
          exact snapshot_restart y

private theorem assignment_after_snapshot {n : Nat} (f : Field LW n) (v : BitVec n)
    (q : Patch LW) (x : BitVec LW) (H : Frame (f.assign v)) :
    snapshot ((q.compose (f.assign v)).apply x)=snapshot (q.apply x) := by
  rw [Patch.compose_apply,snapshot_frame _ _ H]

set_option linter.unusedSimpArgs false in
theorem ordinary_snapshot (old y : BitVec LW) (op : Nat) (f : Payload) :
    snapshot ((afterReply op f old).apply y)=((.empty,1),BitVec.ofNat 9 (nextOrdinary old op f)) := by
  unfold afterReply nextOrdinary
  simp only [admit,acquire,sealOp,bitOp,commitOp,beq_iff_eq,Bool.or_eq_true]
  have cp (v : BitVec 6) : Frame (captures.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have ch (v : BitVec 27) : Frame (capturedHeaders.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have sd (v : BitVec _) : Frame (sourceDescriptor.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have cc (v : BitVec 2) : Frame (choice.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have hc (v : BitVec _) : Frame (candidateHeaders.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have sc (v : BitVec _) : Frame (scalarFile.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have nd (v : BitVec _) : Frame (need.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have dl (v : BitVec 1) : Frame (delta.assign v) := BStarAcquireJoinedIssue.assign _ _ (.inr (.inl (by decide)))
  have F (q : Patch LW) (z : BitVec LW) (a : Frame q) := snapshot_frame q z a
  by_cases H : op=4
  · simp [H,snapshot_schedule]
  by_cases J : op=5
  · rw [if_neg H,if_neg H,if_pos J,if_pos J]
    by_cases T : f.outcome=1
    · simp [T,snapshot_schedule]
    · simp only [T,if_false,Patch.compose_apply]
      rw [F _ _ (ch _), F _ _ (cp _), snapshot_schedule]
  by_cases I : op=1
  · simp [H,J,I,Patch.compose_apply]
    rw [F _ _ (hc _),F _ _ (cc _),F _ _ (sd _),snapshot_schedule] <;> rfl
  by_cases K : op=12
  · simp [H,J,I,K,Patch.compose_apply]
    rw [F _ _ (nd _),F _ _ (sc _),snapshot_schedule] <;> rfl
  simp only [H,J,I,K,if_false]
  by_cases P : op=409 ∨ op=410
  · simp only [P,if_true]
    cases D : BStarLongPublication.decode (sourceDescriptor.read old) with
    | none => exact snapshot_restart y
    | some d =>
      by_cases S : op=409
      · cases dn : d.need <;> by_cases B : f.argument.toNat%2=1 <;>
          simp [D,S,dn,B,Patch.compose_apply,F _ _ (cc _),snapshot_schedule,snapshot_restart]
      · cases dn : d.need <;>
          simp [D,S,dn,Patch.compose_apply,F _ _ (cc _),F _ _ (dl _),snapshot_schedule,snapshot_restart]
  · simp [P,snapshot_schedule]

theorem joined_reply (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (f : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let v : BitVec LW := x.2.long
    let op := (ctrlOp.read v).toNat
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=2 → bind g.2 0 (atSite v 0)=.reply f →
    ∃ a, (a=0 ∨ (op<a ∧ a<413)) ∧
      snapshot (largePair b x).2.long=((.empty,1),BitVec.ofNat 9 a) := by
  dsimp only
  intro hh V ph R
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let op := (ctrlOp.read raw.2).toNat
  have R' : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have S := wait_reply_selected g raw f hh V ph R'
  have J : op<413 := by
    change ((((ctrlPhase.read raw.2).toNat==1)||((ctrlPhase.read raw.2).toNat==2)) &&
      decide (op<413))=true at V
    have F := (Bool.and_eq_true_iff.mp V).2
    exact of_decide_eq_true F
  have apply_write (w : Patch LW) (a : Nat)
      (W : (selected g raw (doorClaim,.door (.reply f))).work=[(true,w)])
      (P : ∀ y, snapshot (w.apply y)=((.empty,1),BitVec.ofNat 9 a)) :
      snapshot (largePair b x).2.long=((.empty,1),BitVec.ofNat 9 a) := by
    apply joined_snapshot k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x w _ hh V _ P
    dsimp only
    rw [R']
    exact ⟨W,S.2.1⟩
  have W := S.2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at W
  by_cases B : (f.fault != 0 || f.opcode.toNat != op)=true
  · rw [if_pos B] at W
    exact ⟨0,.inl rfl,apply_write _ 0 W snapshot_restart⟩
  · rw [if_neg B] at W
    by_cases A : (arithKind op).isSome=true
    · rw [if_pos A] at W
      have h := (arithmetic_range op A).2
      refine ⟨successor raw.2 op,?_,apply_write _ _ W (fun y => arithmetic_snapshot raw.2 y op f)⟩
      rcases successor_order raw.2 op h with H|H
      · exact .inl H
      · right; change op<successor raw.2 op ∧ successor raw.2 op<413; omega
    · rw [if_neg A] at W
      exact ⟨nextOrdinary raw.2 op f,ordinary_progress _ _ _ J,
        apply_write _ _ W (fun y => ordinary_snapshot raw.2 y op f)⟩

open BStarLongRouting

private theorem trail_routing_away (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (T : atSite x.2 0=.trail) :
    ∀ w∈routing g x,w.1≠R 0 := by
  intro w H
  let O := actualOffers g x
  let sel : Selected := O.foldl (fun a o => Selected.append a (selected g x o)) ⟨[],[],[]⟩
  let ks := normalization g (readK x) ++ sel.k
  change w∈ks++observations g (readK x) ks at H
  rcases List.mem_append.mp H with H|H
  · rcases List.mem_append.mp H with hn|hm
    · intro E
      unfold normalization at hn
      rcases List.mem_append.mp hn with h|h
      · obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp h
        dsimp only at ha
        split at ha
        · rename_i B
          obtain rfl := Option.some.inj ha
          change a=R 0 at E
          subst a
          change isFault (bind g.2 0 (atSite x.2 0))=true at B
          rw [T] at B
          contradiction
        · contradiction
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
        change a=R 0 at E
        subst a
        unfold discarded at ha
        cases h₁ : g.1.inside <;> cases h₂ : g.2.inside <;> simp [h₁,h₂,L,R] at ha
    · have Q := (row_folds g x O ⟨[],[],[]⟩).2
      change sel.k=[]++O.flatMap _ at Q
      rw [Q,List.nil_append] at hm
      obtain ⟨o,ho,hw⟩ := List.mem_flatMap.mp hm
      obtain ⟨pre,post,E,_,_⟩ := BStarDoorUnique.actual_door_split g x hh
      let door : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
      change O=pre++door::post at E
      have P : (O.map Prod.fst).Pairwise (fun a b => ∀ s∈b.slots,s∉a.slots) := by
        rw [show O.map Prod.fst=orderedCommands g from actualOffers_claims g x]
        exact select_pairwise Claim.slots [] (offers commandKey (commandClaims g))
      rw [E,List.map_append,List.map_cons] at P
      change o∈O at ho
      rw [E] at ho
      have own : R 0∈door.1.slots := by change R 0∈doorClaim.slots; decide
      intro B
      have F := BStarAcquireLandingHop.selected_slot g x o w hw
      rw [B] at F
      rcases List.mem_append.mp ho with h|h
      · exact (List.pairwise_append.mp P).2.2 o.1 (List.mem_map.mpr ⟨o,h,rfl⟩)
          door.1 List.mem_cons_self _ own F
      · rcases List.mem_cons.mp h with he|h
        · subst o
          unfold door selected at hw
          dsimp only at hw
          split at hw <;> cases hw
        · exact (List.pairwise_cons.mp (List.pairwise_append.mp P).2.1).1 o.1
            (List.mem_map.mpr ⟨o,h,rfl⟩) _ F own
  · exact observer_away g _ ks w H

/-- At a valid WAIT door no new source forward token can appear.
The T branch holds exactly, the E branch repairs, and the already
bound D branch always consumes its reply. Old F is excluded only
because this is a no-rise assertion. -/
theorem wait_k0_no_rise (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let v : BitVec LW := x.2.long
    (oldHeaders b x.2).h6=true → LongDoorGuard.valid manifest v=true →
    (ctrlPhase.read v).toNat=2 →
    (∀ pay, atSite v 0≠.forward pay) →
    ∀ pay, atSite (largePair b x).2.long 0≠.forward pay := by
  dsimp only
  intro hh V ph NF pay
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have read (t : Token) (H : snapshot (largePair b x).2.long=((t,1),0)) :
      atSite (largePair b x).2.long 0=t := congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.1) H
  cases E : atSite raw.2 0 with
  | forward f => exact (NF f E).elim
  | empty =>
    have H : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.write faultRestart := by
      rw [E]
      exact wait_empty_repairs _ V ph
    have frame := read _ (selected_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh V H)
    exact fun X => Token.noConfusion (frame.symm.trans X)
  | trail =>
    have B : bind g.2 0 (atSite raw.2 0)=.trail := by rw [E]; rfl
    have H := BStarAcquireRingFrame.joined_right k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x
      ⟨V,ph,.inl B⟩ (trail_routing_away g raw hh E)
    have H' : atSite (largePair b x).2.long 0=.trail := (congrArg decode H).trans E
    exact fun X => Token.noConfusion (H'.symm.trans X)
  | reply f =>
    have B : ∃ f', bind g.2 0 (atSite raw.2 0)=.reply f' := by
      rw [E]
      simp only [BStarLongCommand.bind]
      split
      · exact ⟨_,rfl⟩
      · split <;> exact ⟨_,rfl⟩
    obtain ⟨f',H⟩ := B
    obtain ⟨a,_,J⟩ := joined_reply k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x f' hh V ph H
    have F : atSite (largePair b x).2.long 0=.empty :=
      congrArg (fun s : (Token × BitVec 2) × BitVec 9 => s.1.1) J
    exact fun X => Token.noConfusion (F.symm.trans X)

end L4.BStarJoinedControllerReturn
