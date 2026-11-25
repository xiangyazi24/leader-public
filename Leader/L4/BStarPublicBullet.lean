import Leader.L4.BStarPublicShield

namespace L4.BStarPublicBullet
open AllSizeProtocol BStarPublicCodec BStarPublic BStarPublicFrame BStarPublicStock BStarPublicShield

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

abbrev f {p c} (u v : Site p c) := fireInitiator (materialize u v)
abbrev g {p c} (v : Site p c) := fireResponder v
abbrev impacted {p c} (u v : Site p c) := impact (f u v) (g v)
def hit {p c} (a b : Site p c) := !(a.bullet == .none) && b.leader
def send {p c} (l r : Site p c) := !(l.bullet == .none) && !r.leader
def deliver {p c} (l r : Site p c) := send l r && !pinned l r && r.bullet == .none

def leftIssue {p c} (u v : Site p c) :=
  fires u || (hit (f u v) (g v) || send (impacted u v).1 (impacted u v).2)
def rightIssue {p c} (u v : Site p c) :=
  fires v || deliver (impacted u v).1 (impacted u v).2 || p5 u v

private theorem no_or {a b : Bool} (h : (a || b)=false) : a=false ∧ b=false := by
  cases a <;> cases b <;> simp_all

private theorem prefix_bullets {p c} (u v : Site p c) :
    let t := impacted u v
    ((stepPrefix u v).1.bullet,(stepPrefix u v).2.bullet)=
    ((followerBullet (pinned t.1 t.2) t.1 t.2).1.bullet,
     (followerBullet (pinned t.1 t.2) t.1 t.2).2.bullet) := by
  have pay (a b : Site p c) :
      (payment a b).1.bullet=a.bullet ∧ (payment a b).2.bullet=b.bullet := by
    unfold payment
    split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩
  simp only [stepPrefix,(pay _ _).1,(pay _ _).2,native]

theorem bullet_suffix {p c} (u v : Site p c) :
    ((pairStep u v).1.bullet,(pairStep u v).2.bullet)=
      ((stepPrefix u v).1.bullet,if p5 u v then .none else (stepPrefix u v).2.bullet) := by
  unfold pairStep p5
  generalize stepPrefix u v = a
  rcases a with ⟨l,r⟩
  dsimp only
  rw [patrol_fire]
  unfold patrolWrite finishBirth pinned
  split <;> rfl

theorem left_bullet_hold {p c} (u v : Site p c) (h : leftIssue u v=false) :
    (pairStep u v).1.bullet=u.bullet := by
  have guards := no_or h
  have hits := no_or guards.2
  have pf := congrArg Prod.fst (prefix_bullets u v)
  have ps := congrArg Prod.fst (bullet_suffix u v)
  dsimp only at pf ps
  rw [ps,pf]
  unfold followerBullet
  have nx : send (impacted u v).1 (impacted u v).2=false := hits.2
  rw [show (!(impacted u v).1.bullet == .none && !(impacted u v).2.leader)=false from nx]
  simp only [Bool.false_eq_true,if_false]
  have ni : hit (f u v) (g v)=false := hits.1
  have left : (impacted u v).1.bullet=(f u v).bullet := by
    change (impact (f u v) (g v)).1.bullet=_
    unfold impact
    rw [show (!(f u v).bullet == .none && (g v).leader)=false from ni]
    rfl
  rw [left]
  have mat : (materialize u v).leader=u.leader ∧ (materialize u v).signal=u.signal ∧
      (materialize u v).bullet=u.bullet := by unfold materialize; split <;> exact ⟨rfl,rfl,rfl⟩
  change (fireInitiator (materialize u v)).bullet=_
  unfold fireInitiator
  simp only [mat.1,mat.2.1,show (u.leader && !u.signal == .zero)=false from guards.1,
    Bool.false_eq_true,if_false,mat.2.2]

theorem right_bullet_hold {p c} (u v : Site p c) (h : rightIssue u v=false) :
    (pairStep u v).2.bullet=v.bullet := by
  have guards := no_or h
  have older := no_or guards.1
  have pf := congrArg Prod.snd (prefix_bullets u v)
  have ps := congrArg Prod.snd (bullet_suffix u v)
  dsimp only at pf ps
  rw [ps,guards.2]
  simp only [Bool.false_eq_true,if_false]
  rw [pf]
  have transport (l r : Site p c) (h : deliver l r=false) :
      (followerBullet (pinned l r) l r).2.bullet=r.bullet := by
    unfold followerBullet
    split
    · rename_i hSend
      split
      · rfl
      · rename_i hPin
        have hs : send l r=true := hSend
        have hp : pinned l r=false := Bool.eq_false_iff.mpr hPin
        simp only [deliver,hs,hp,Bool.not_false,Bool.true_and] at h
        dsimp only
        rw [h]
        rfl
    · rfl
  rw [transport _ _ older.2]
  have ri : (impacted u v).2.bullet=(g v).bullet := by
    change (impact (f u v) (g v)).2.bullet=_
    unfold impact
    split
    · split <;> rfl
    · rfl
  rw [ri]
  have hF : fires v=false := older.1
  change (fireResponder v).bullet=v.bullet
  cases hL : v.leader <;> cases hS : v.signal <;>
    simp only [fireResponder,fires,hL,hS] at hF ⊢ <;> first | rfl | cases hF

set_option linter.unusedSimpArgs false in
theorem left_bullet_mask {p c : Nat} (u v : Site p c) :
    full (bulletF p c) (pubMask (u,v)).1 (leftIssue u v) := by
  intro j hj
  let i := 7+q c+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^2-1)*2^(7+q c))).getLsbD i=true :=
    (lane_support (bulletF p c) i).mpr (by change 7+q c≤i ∧ i<7+q c+2; dsimp [i]; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤7+q c+j
    change j<2 at hj
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤7+q c+j
    change j<2 at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤7+q c+j
    change j<2 at hj
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤7+q c+j
    change j<2 at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    right
    change (6+q c)+(1)≤7+q c+j
    change j<2 at hj
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change 7+q c+j<(9+q c)
    change j<2 at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change 7+q c+j<(10+q c)
    change j<2 at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 7+q c+j<(11+q c)
    change j<2 at hj
    omega
  change (pubMask (u,v)).1.getLsbD i=(leftIssue u v)
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
    simp [hS,hL,fst_ite,bit_ite,rail,source,z,leftIssue,hit,send,fires]

set_option linter.unusedSimpArgs false in
theorem right_bullet_mask {p c : Nat} (u v : Site p c) :
    full (bulletF p c) (pubMask (u,v)).2 (rightIssue u v) := by
  intro j hj
  let i := 7+q c+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^2-1)*2^(7+q c))).getLsbD i=true :=
    (lane_support (bulletF p c) i).mpr (by change 7+q c≤i ∧ i<7+q c+2; dsimp [i]; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤7+q c+j
    change j<2 at hj
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤7+q c+j
    change j<2 at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤7+q c+j
    change j<2 at hj
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤7+q c+j
    change j<2 at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    right
    change (6+q c)+(1)≤7+q c+j
    change j<2 at hj
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change 7+q c+j<(9+q c)
    change j<2 at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change 7+q c+j<(10+q c)
    change j<2 at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 7+q c+j<(11+q c)
    change j<2 at hj
    omega
  change (pubMask (u,v)).2.getLsbD i=(rightIssue u v)
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
  change _=(fires v || deliver (impacted u v).1 (impacted u v).2 ||
    (arrival a.1 a.2).fire && pinned a.1 a.2)
  unfold arrival
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,deliver,send,fires]
theorem bullet_frame {p c : Nat} (u v : Site p c) :
    FieldCase (bulletF p c) (pubMask (u,v)).1 (u.bullet=(pairStep u v).1.bullet) ∧
    FieldCase (bulletF p c) (pubMask (u,v)).2 (v.bullet=(pairStep u v).2.bullet) := by
  constructor
  · have mask := left_bullet_mask u v
    cases h : leftIssue u v
    · exact .inr ⟨h ▸ mask,(left_bullet_hold u v h).symm⟩
    · exact .inl (h ▸ mask)
  · have mask := right_bullet_mask u v
    cases h : rightIssue u v
    · exact .inr ⟨h ▸ mask,(right_bullet_hold u v h).symm⟩
    · exact .inl (h ▸ mask)

theorem raw_bullets {p c : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c))) :
    let old := Pair.map (readPub hp) x
    let new := pairStep old.1 old.2
    let y := Pair.map (readPub hp) (patchPair (publicWork hp x) x)
    y.1.bullet=new.1.bullet ∧ y.2.bullet=new.2.bullet := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let t := pairStep u v
  have h := bullet_frame u v
  exact ⟨decoded_field bulletDecode (bulletF p c) (publicWork hp x).1 x.1 t.1.bullet
      (congrArg Site.bullet (read_pack hp t.1)) h.1,
    decoded_field bulletDecode (bulletF p c) (publicWork hp x).2 x.2 t.2.bullet
      (congrArg Site.bullet (read_pack hp t.2)) h.2⟩

end L4.BStarPublicBullet

