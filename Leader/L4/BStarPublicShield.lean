import Leader.L4.BStarPublicStock

namespace L4.BStarPublicShield
open AllSizeProtocol BStarPublicCodec BStarPublic BStarPublicFrame BStarPublicStock

private theorem lane_off {w k} (f : Field w k) (i : Nat)
    (h : i<f.offset ∨ f.offset+k≤i) :
    (BitVec.ofNat w ((2^k-1)*2^f.offset)).getLsbD i=false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨a,b⟩ := (lane_support f i).mp ht
  omega

private theorem bit_ite {w : Nat} (P : Prop) [Decidable P] (x y : BitVec w) (i : Nat) :
    (if P then x else y).getLsbD i=(if P then x.getLsbD i else y.getLsbD i) := by
  by_cases h : P <;> simp [h]

private theorem fst_ite {A B : Type} (P : Prop) [Decidable P] (x y : A × B) :
    (if P then x else y).1=(if P then x.1 else y.1) := by
  by_cases h : P <;> simp [h]

private theorem snd_ite {A B : Type} (P : Prop) [Decidable P] (x y : A × B) :
    (if P then x else y).2=(if P then x.2 else y.2) := by
  by_cases h : P <;> simp [h]

def fires {p c} (u : Site p c) := u.leader && !(u.signal == .zero)

def arrival {p c} (a b : Site p c) : Patrol (2*c) :=
  arrivals (b.leader || a.mark) (pinned a b) b.leader
    (sourceGuard (pinned a b) ⟨b.source,a.rail,b.rail,false⟩)

def p5 {p c} (u v : Site p c) : Bool :=
  let a := (stepPrefix u v).1
  let b := (stepPrefix u v).2
  (arrival a b).fire && pinned a b

private theorem launch_fire {Q} (p : Patrol Q) : (launch p).fire=p.fire := by
  cases p with
  | mk s l r f => cases s <;> rfl

private theorem turn_fire {Q} (root : Bool) (p : Patrol Q) : (turn root p).fire=p.fire := by
  cases p with
  | mk s l r f => cases root <;> cases r <;> rfl

private theorem move_fire {Q} (root : Bool) (p : Patrol Q) : (move root p).fire=p.fire := by
  cases p with
  | mk s l r f => cases root <;> cases r <;> cases l <;> rfl

theorem patrol_fire {p c} (a b : Site p c) :
    (patrol (b.leader || a.mark) (pinned a b) b.leader b.source a.rail b.rail).fire =
      (arrival a b).fire := by
  simp only [patrol,move_fire,turn_fire,launch_fire,arrival]

theorem shield_suffix {p c} (u v : Site p c) :
    ((pairStep u v).1.shield,(pairStep u v).2.shield)=
      ((stepPrefix u v).1.shield,if p5 u v then true else (stepPrefix u v).2.shield) := by
  unfold pairStep p5
  generalize stepPrefix u v = a
  rcases a with ⟨l,r⟩
  dsimp only
  rw [patrol_fire]
  unfold patrolWrite finishBirth pinned
  split <;> rfl

private theorem shield_prefix {p c} (u v : Site p c) :
    ((stepPrefix u v).1.shield,(stepPrefix u v).2.shield) =
      ((fireInitiator (materialize u v)).shield,(fireResponder v).shield) := by
  have imp (a b : Site p c) :
      (impact a b).1.shield=a.shield ∧ (impact a b).2.shield=b.shield := by
    unfold impact
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have fan (g : Bool) (a b : Site p c) :
      (followerBullet g a b).1.shield=a.shield ∧ (followerBullet g a b).2.shield=b.shield := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have pay (a b : Site p c) :
      (payment a b).1.shield=a.shield ∧ (payment a b).2.shield=b.shield := by
    unfold payment
    split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩
  simp only [stepPrefix,(pay _ _).1,(pay _ _).2,native,
    (fan _ _ _).1,(fan _ _ _).2,(imp _ _).1,(imp _ _).2]

/-- The literal N0, N1 and P5 shield writes. No hypothesis about
cover, complete rows, or raw canonicalization is needed. -/
theorem shield_typed {p c} (u v : Site p c) :
    ((pairStep u v).1.shield,(pairStep u v).2.shield)=
    (if fires u then true else u.shield,
      if p5 u v then true else if fires v then v.signal != .one else v.shield) := by
  have pref := shield_prefix u v
  have pf := congrArg Prod.fst pref
  have ps := congrArg Prod.snd pref
  dsimp only at pf ps
  rw [shield_suffix,pf,ps]
  have hM : (materialize u v).shield=u.shield ∧ (materialize u v).leader=u.leader ∧
    (materialize u v).signal=u.signal := by
    unfold materialize; split <;> exact ⟨rfl,rfl,rfl⟩
  congr 1
  · simp only [fireInitiator,hM.2.1,hM.2.2,fires]
    split
    · rename_i h; simp only [h,if_true]
    · rename_i h; simpa only [h,Bool.false_eq_true,if_false] using hM.1
  · have R : (fireResponder v).shield=(if fires v then v.signal != .one else v.shield) := by
      cases hL : v.leader <;> cases hS : v.signal <;>
        simp only [fireResponder,fires,hL,hS] <;> rfl
    rw [R]

set_option linter.unusedSimpArgs false in
theorem left_shield_mask {p c : Nat} (u v : Site p c) :
    full (shieldF p c) (pubMask (u,v)).1 (fires u) := by
  intro j hj
  change j<1 at hj
  have j0 : j=0 := by omega
  subst j
  let i := 6+q c
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have shield : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(6+q c))).getLsbD i=true :=
    (lane_support (shieldF p c) i).mpr (by change i≤i ∧ i<i+1; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤6+q c
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤6+q c
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤6+q c
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤6+q c
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change 6+q c<(7+q c)
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change 6+q c<(9+q c)
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change 6+q c<(10+q c)
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 6+q c<(11+q c)
    omega
  change (pubMask (u,v)).1.getLsbD i=(fires u)
  let a := stepPrefix u v
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=(oldNative u v).2 := rfl
  have payment_eq : payment (oldNative u v).1 (oldNative u v).2=a := rfl
  unfold pubMask
  dsimp only
  simp only [rhs,payment_eq]
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,fst_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,fst_ite,bit_ite,rail,source,z,fires]

set_option linter.unusedSimpArgs false in
theorem right_shield_mask {p c : Nat} (u v : Site p c) :
    full (shieldF p c) (pubMask (u,v)).2 (fires v || p5 u v) := by
  intro j hj
  change j<1 at hj
  have j0 : j=0 := by omega
  subst j
  let i := 6+q c
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have shield : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(6+q c))).getLsbD i=true :=
    (lane_support (shieldF p c) i).mpr (by change i≤i ∧ i<i+1; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤6+q c
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤6+q c
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤6+q c
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤6+q c
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change 6+q c<(7+q c)
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change 6+q c<(9+q c)
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change 6+q c<(10+q c)
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 6+q c<(11+q c)
    omega
  change (pubMask (u,v)).2.getLsbD i=(fires v || p5 u v)
  let a := stepPrefix u v
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=(oldNative u v).2 := rfl
  have payment_eq : payment (oldNative u v).1 (oldNative u v).2=a := rfl
  unfold pubMask
  dsimp only
  simp only [rhs,payment_eq]
  change _=(fires v || (arrival a.1 a.2).fire && pinned a.1 a.2)
  unfold arrival
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,fires]
theorem shield_frame {p c : Nat} (u v : Site p c) :
    FieldCase (shieldF p c) (pubMask (u,v)).1 (u.shield=(pairStep u v).1.shield) ∧
    FieldCase (shieldF p c) (pubMask (u,v)).2 (v.shield=(pairStep u v).2.shield) := by
  obtain row := shield_typed u v
  constructor
  · have mask := left_shield_mask u v
    cases h : fires u
    · have frame := congrArg Prod.fst row
      dsimp only at frame
      rw [h] at mask frame
      exact .inr ⟨mask,frame.symm⟩
    · exact .inl (h ▸ mask)
  · have mask := right_shield_mask u v
    by_cases b : fires v || p5 u v
    · exact .inl (b ▸ mask)
    · have h : fires v=false ∧ p5 u v=false := by
        cases hV : fires v <;> cases h5 : p5 u v <;> simp_all
      have frame := congrArg Prod.snd row
      dsimp only at frame
      simp only [h.1,h.2,Bool.false_or,Bool.false_eq_true,if_false] at mask frame
      exact .inr ⟨mask,frame.symm⟩

theorem raw_shields {p c : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c))) :
    let old := Pair.map (readPub hp) x
    let new := pairStep old.1 old.2
    let y := Pair.map (readPub hp) (patchPair (publicWork hp x) x)
    y.1.shield=new.1.shield ∧ y.2.shield=new.2.shield := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let t := pairStep u v
  have h := shield_frame u v
  exact ⟨decoded_field (fun s => s.getLsbD 0) (shieldF p c) (publicWork hp x).1 x.1 t.1.shield
      (congrArg Site.shield (read_pack hp t.1)) h.1,
    decoded_field (fun s => s.getLsbD 0) (shieldF p c) (publicWork hp x).2 x.2 t.2.shield
      (congrArg Site.shield (read_pack hp t.2)) h.2⟩

end L4.BStarPublicShield

