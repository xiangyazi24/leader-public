import Leader.L4.BStarPublicBullet

namespace L4.BStarPublicNativeRight
open AllSizeProtocol BStarPublicCodec BStarPublic BStarPublicFrame BStarPublicStock
  BStarPublicShield BStarPublicBullet

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

def kill {p c} (a b : Site p c) := hit a b && a.bullet == .live && !b.shield
def signalSend {p c} (a b : Site p c) := send a b && !pinned a b

def leaderIssue {p c} (u v : Site p c) := kill (f u v) (g v) || p5 u v
def signalIssue {p c} (u v : Site p c) :=
  fires v || signalSend (impacted u v).1 (impacted u v).2 || p5 u v

private theorem no_or {a b : Bool} (h : (a || b)=false) : a=false ∧ b=false := by
  cases a <;> cases b <;> simp_all

theorem suffix {p c} (u v : Site p c) :
    ((pairStep u v).2.leader,(pairStep u v).2.signal)=
      (if p5 u v then true else (stepPrefix u v).2.leader,
        if p5 u v then .zero else (stepPrefix u v).2.signal) := by
  unfold pairStep p5
  generalize stepPrefix u v = a
  rcases a with ⟨l,r⟩
  dsimp only
  rw [patrol_fire]
  unfold patrolWrite finishBirth pinned
  split <;> rfl

private theorem native_prefix {p c} (u v : Site p c) :
    let t := impacted u v
    ((stepPrefix u v).2.leader,(stepPrefix u v).2.signal)=
    ((followerBullet (pinned t.1 t.2) t.1 t.2).2.leader,
     (followerBullet (pinned t.1 t.2) t.1 t.2).2.signal) := by
  have pay (a b : Site p c) :
      (payment a b).2.leader=b.leader ∧ (payment a b).2.signal=b.signal := by
    unfold payment
    split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩
  simp only [stepPrefix,(pay _ _).1,(pay _ _).2,native]

theorem leader_hold {p c} (u v : Site p c) (h : leaderIssue u v=false) :
    (pairStep u v).2.leader=v.leader := by
  have guards := no_or h
  have pf := congrArg Prod.fst (native_prefix u v)
  have ps := congrArg Prod.fst (suffix u v)
  dsimp only at pf ps
  rw [ps,guards.2]
  simp only [Bool.false_eq_true,if_false]
  rw [pf]
  have H (a b : Site p c) : (followerBullet (pinned a b) a b).2.leader=b.leader := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  rw [H]
  have I (a b : Site p c) (h : kill a b=false) : (impact a b).2.leader=b.leader := by
    unfold impact
    split
    · rename_i hh
      have hh' : hit a b=true := hh
      simp only [kill,hh',Bool.true_and] at h
      rw [h]
      rfl
    · rfl
  rw [I _ _ guards.1]
  change (fireResponder v).leader=v.leader
  unfold fireResponder
  split
  · cases v.signal <;> rfl
  · rfl

theorem signal_hold {p c} (u v : Site p c) (h : signalIssue u v=false) :
    (pairStep u v).2.signal=v.signal := by
  have guards := no_or h
  have older := no_or guards.1
  have pf := congrArg Prod.snd (native_prefix u v)
  have ps := congrArg Prod.snd (suffix u v)
  dsimp only at pf ps
  rw [ps,guards.2]
  simp only [Bool.false_eq_true,if_false]
  rw [pf]
  have H (a b : Site p c) (h : signalSend a b=false) :
      (followerBullet (pinned a b) a b).2.signal=b.signal := by
    unfold followerBullet
    split
    · rename_i hs
      split
      · rfl
      · rename_i hp
        have q : send a b=true := hs
        have r : pinned a b=false := Bool.eq_false_iff.mpr hp
        simp [signalSend,q,r] at h
    · rfl
  rw [H _ _ older.2]
  have I (a b : Site p c) : (impact a b).2.signal=b.signal := by
    unfold impact
    split
    · split <;> rfl
    · rfl
  rw [I]
  have hF : fires v=false := older.1
  change (fireResponder v).signal=v.signal
  cases hL : v.leader <;> cases hS : v.signal <;>
    simp [fireResponder,hL,hS]
  all_goals simp only [fires,hL,hS] at hF; cases hF


set_option linter.unusedSimpArgs false in
theorem leader_mask {p c : Nat} (u v : Site p c) :
    full (leaderF p c) (pubMask (u,v)).2 (leaderIssue u v) := by
  intro j hj
  let i := 9+q c+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have leader : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(9+q c))).getLsbD i=true :=
    (lane_support (leaderF p c) i).mpr (by change 9+q c≤i ∧ i<(9+q c)+1; dsimp [i]; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤(9+q c)+j
    change j<1 at hj
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤(9+q c)+j
    change j<1 at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤(9+q c)+j
    change j<1 at hj
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤(9+q c)+j
    change j<1 at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    right
    change (6+q c)+(1)≤(9+q c)+j
    change j<1 at hj
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    right
    change (7+q c)+(2)≤(9+q c)+j
    change j<1 at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change (9+q c)+j<(10+q c)
    change j<1 at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change (9+q c)+j<(11+q c)
    change j<1 at hj
    omega
  change (pubMask (u,v)).2.getLsbD i=(leaderIssue u v)
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
  change _=(kill (f u v) (g v) || (arrival a.1 a.2).fire && pinned a.1 a.2)
  unfold arrival
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,signalSend,send,kill,hit,fires]

set_option linter.unusedSimpArgs false in
theorem signal_mask {p c : Nat} (u v : Site p c) :
    full (signalF p c) (pubMask (u,v)).2 (signalIssue u v) := by
  intro j hj
  let i := 4+q c+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have signal : (BitVec.ofNat (publicWidth p c) ((2^2-1)*2^(4+q c))).getLsbD i=true :=
    (lane_support (signalF p c) i).mpr (by change 4+q c≤i ∧ i<(4+q c)+2; dsimp [i]; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤(4+q c)+j
    change j<2 at hj
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤(4+q c)+j
    change j<2 at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤(4+q c)+j
    change j<2 at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    left
    change (4+q c)+j<(6+q c)
    change j<2 at hj
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change (4+q c)+j<(7+q c)
    change j<2 at hj
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change (4+q c)+j<(9+q c)
    change j<2 at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change (4+q c)+j<(10+q c)
    change j<2 at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change (4+q c)+j<(11+q c)
    change j<2 at hj
    omega
  change (pubMask (u,v)).2.getLsbD i=(signalIssue u v)
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
  change _=(fires v || signalSend (impacted u v).1 (impacted u v).2 || (arrival a.1 a.2).fire && pinned a.1 a.2)
  unfold arrival
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,signalSend,send,kill,hit,fires]
theorem leader_frame {p c : Nat} (u v : Site p c) :
    FieldCase (leaderF p c) (pubMask (u,v)).2 (v.leader=(pairStep u v).2.leader) := by
  have mask := leader_mask u v
  cases h : leaderIssue u v
  · exact .inr ⟨h ▸ mask,(leader_hold u v h).symm⟩
  · exact .inl (h ▸ mask)

theorem raw_right_leader {p c : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c))) :
    (readPub hp ((publicWork hp x).2.apply x.2)).leader =
      (pairStep (readPub hp x.1) (readPub hp x.2)).2.leader := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let y := (pairStep u v).2
  exact decoded_field (fun a => a.getLsbD 0) (leaderF p c) (publicWork hp x).2 x.2 y.leader
    (congrArg Site.leader (read_pack hp y)) (leader_frame u v)

#print axioms raw_right_leader

theorem signal_frame {p c : Nat} (u v : Site p c) :
    FieldCase (signalF p c) (pubMask (u,v)).2 (v.signal=(pairStep u v).2.signal) := by
  have mask := signal_mask u v
  cases h : signalIssue u v
  · exact .inr ⟨h ▸ mask,(signal_hold u v h).symm⟩
  · exact .inl (h ▸ mask)

theorem raw_right_signal {p c : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c))) :
    (readPub hp ((publicWork hp x).2.apply x.2)).signal =
      (pairStep (readPub hp x.1) (readPub hp x.2)).2.signal := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let y := (pairStep u v).2
  exact decoded_field (signalDecode) (signalF p c) (publicWork hp x).2 x.2 y.signal
    (congrArg Site.signal (read_pack hp y)) (signal_frame u v)

#print axioms raw_right_signal

end L4.BStarPublicNativeRight

