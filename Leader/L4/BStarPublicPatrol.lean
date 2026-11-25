import Leader.L4.BStarPublicNativeRight
import Leader.L4.BStarPublicMark
import Leader.L4.FixedResidual

namespace L4.BStarPublicPatrol
open AllSizeProtocol BStarPublicCodec BStarPublic BStarPublicFrame BStarPublicShield BStarPublicStock

def arrivalsIssue {Q} (root pg leader : Bool) (s : Patrol Q) : Bool × Bool :=
  if s.left == .x && pg then (true,true)
  else if s.left == .x && leader then (true,false)
  else if s.source == .i1 && s.left == .di then (true,true)
  else match s.source,s.left with
    | .await _,.dc => (true,true)
    | _,_ => if root && returning s.left then (true,false)
             else (false,waiting s.source && s.left == .e)

def launchIssue {Q} (a : Patrol Q) : Bool :=
  match a.source with | .i0 | .count _ => true | _ => false

def turnIssue {Q} (root : Bool) (a : Patrol Q) :=
  root && (a.right == .ui || a.right == .uc || a.right == .t)
def bothIssue {Q} (root : Bool) (a : Patrol Q) :=
  !root && (a.right == .ui || a.right == .uc || returning a.left || a.left == .x)
def extraRightIssue {Q} (root : Bool) (a : Patrol Q) :=
  !root && a.left == .e && a.right == .t

private theorem no_or {a b : Bool} (h : (a || b)=false) : a=false ∧ b=false := by
  cases a <;> cases b <;> simp_all

private theorem s_frame {Q} (pg : Bool) (s : Patrol Q) :
    (sourceGuard pg s).left=s.left ∧
    ((!pg && !(s.source == .off))=false → (sourceGuard pg s).right=s.right) ∧
    ((!pg || s.source == .off)=false → (sourceGuard pg s).source=s.source) := by
  cases pg <;> cases h : (s.source == .off) <;> simp [sourceGuard,h]

set_option linter.unusedSimpArgs false in
private theorem a_frame {Q} (root pg leader : Bool) (s : Patrol Q) :
    let a := arrivals root pg leader s
    let m := arrivalsIssue root pg leader s
    a.right=s.right ∧ (m.1=false → a.left=s.left) ∧ (m.2=false → a.source=s.source) := by
  dsimp only
  unfold arrivals arrivalsIssue
  split
  · rename_i h; simp [h]
  · rename_i h₀
    try simp only [h₀,if_false]
    split
    · rename_i h; simp [h]
    · rename_i h₁
      try simp only [h₁,if_false]
      split
      · rename_i h; simp [h]
      · rename_i h₂
        try simp only [h₂,if_false]
        split
        · rename_i k hs hl
          simp only [hs,hl]
          split <;> simp
        · rename_i h
          split
          · rename_i ht
            simp [ht,h]
          · rename_i ht
            simp only [ht,if_false,h]
            split <;> simp_all

private theorem launch_frame {Q} (a : Patrol Q) :
    (launch a).right=a.right ∧
    (launchIssue a=false → (launch a).left=a.left ∧ (launch a).source=a.source) := by
  cases a with
  | mk src l r f => cases src <;> simp [launch,launchIssue]

private theorem move_frame {Q} (root : Bool) (a : Patrol Q) :
    (move root (turn root a)).source=a.source ∧
    (bothIssue root a=false → (move root (turn root a)).left=a.left) ∧
    ((turnIssue root a || bothIssue root a || extraRightIssue root a)=false →
      (move root (turn root a)).right=a.right) := by
  cases a with
  | mk src l r f =>
    cases root <;> cases l <;> cases r <;>
      exact ⟨rfl,fun h => by repeat first | rfl | contradiction,
        fun h => by repeat first | rfl | contradiction⟩

def issue {p c} (u v : Site p c) : Bool × Bool × Bool :=
  let l := (stepPrefix u v).1
  let r := (stepPrefix u v).2
  let root := r.leader || l.mark
  let pg := pinned l r
  let t : Patrol (2*c) := ⟨r.source,l.rail,r.rail,false⟩
  let s := sourceGuard pg t
  let m := arrivalsIssue root pg r.leader s
  let ar := arrivals root pg r.leader s
  let a := launch ar
  (m.1 || (launchIssue ar || bothIssue root a),
   (!pg && !(t.source == .off)) ||
      (turnIssue root a || bothIssue root a || extraRightIssue root a),
   (!pg || t.source == .off) || m.2 || launchIssue ar || p5 u v)

private theorem pair_patrol {p c} (u v : Site p c) :
    let l := (stepPrefix u v).1
    let r := (stepPrefix u v).2
    let m := patrol (r.leader || l.mark) (pinned l r) r.leader r.source l.rail r.rail
    ((pairStep u v).1.rail,(pairStep u v).2.rail,(pairStep u v).2.source)=
      (m.left,m.right,if p5 u v then .off else m.source) := by
  unfold pairStep p5
  generalize stepPrefix u v = a
  rcases a with ⟨l,r⟩
  dsimp only
  rw [patrol_fire]
  unfold patrolWrite finishBirth pinned
  split <;> rfl

theorem holds {p c} (u v : Site p c) :
    (issue u v).1=false → (pairStep u v).1.rail=u.rail := by
  intro h
  let l := (stepPrefix u v).1
  let r := (stepPrefix u v).2
  let root := r.leader || l.mark
  let pg := pinned l r
  let t : Patrol (2*c) := ⟨r.source,l.rail,r.rail,false⟩
  let s := sourceGuard pg t
  let ar := arrivals root pg r.leader s
  let a := launch ar
  change ((arrivalsIssue root pg r.leader s).1 || (launchIssue ar || bothIssue root a))=false at h
  obtain ⟨ha,other⟩ := no_or h
  obtain ⟨hl,hm⟩ := no_or other
  have exactPair := congrArg Prod.fst (pair_patrol u v)
  change (pairStep u v).1.rail=(move root (turn root a)).left at exactPair
  rw [exactPair,(move_frame root a).2.1 hm,(launch_frame ar).2 hl |>.1,
    (a_frame root pg r.leader s).2.1 ha]
  exact (s_frame pg t).1.trans (FixedResidual.prefix_ports u v).1

theorem holds_right {p c} (u v : Site p c) :
    (issue u v).2.1=false → (pairStep u v).2.rail=v.rail := by
  intro h
  let l := (stepPrefix u v).1
  let r := (stepPrefix u v).2
  let root := r.leader || l.mark
  let pg := pinned l r
  let t : Patrol (2*c) := ⟨r.source,l.rail,r.rail,false⟩
  let s := sourceGuard pg t
  let ar := arrivals root pg r.leader s
  let a := launch ar
  change ((!pg && !(t.source == .off)) ||
    (turnIssue root a || bothIssue root a || extraRightIssue root a))=false at h
  obtain ⟨hs,hm⟩ := no_or h
  have exactPair := congrArg (fun y => y.2.1) (pair_patrol u v)
  change (pairStep u v).2.rail=(move root (turn root a)).right at exactPair
  rw [exactPair,(move_frame root a).2.2 hm,(launch_frame ar).1,(a_frame root pg r.leader s).1]
  exact ((s_frame pg t).2.1 hs).trans (FixedResidual.prefix_ports u v).2.1

theorem holds_source {p c} (u v : Site p c) :
    (issue u v).2.2=false → (pairStep u v).2.source=v.source := by
  intro h
  let l := (stepPrefix u v).1
  let r := (stepPrefix u v).2
  let root := r.leader || l.mark
  let pg := pinned l r
  let t : Patrol (2*c) := ⟨r.source,l.rail,r.rail,false⟩
  let s := sourceGuard pg t
  let ar := arrivals root pg r.leader s
  let a := launch ar
  change ((!pg || t.source == .off) || (arrivalsIssue root pg r.leader s).2 ||
    launchIssue ar || p5 u v)=false at h
  obtain ⟨old,hf⟩ := no_or h
  obtain ⟨old,hl⟩ := no_or old
  obtain ⟨hs,ha⟩ := no_or old
  have exactPair := congrArg (fun y => y.2.2) (pair_patrol u v)
  change (pairStep u v).2.source=(if p5 u v then .off else (move root (turn root a)).source) at exactPair
  simp only [hf,Bool.false_eq_true,if_false] at exactPair
  rw [exactPair,(move_frame root a).1,(launch_frame ar).2 hl |>.2,
    (a_frame root pg r.leader s).2.2 ha]
  exact ((s_frame pg t).2.2 hs).trans (FixedResidual.prefix_ports u v).2.2

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

set_option linter.unusedSimpArgs false in
theorem left_rail_mask {p c : Nat} (u v : Site p c) :
    full (railF p c) (pubMask (u,v)).1 (issue u v).1 := by
  intro j hj
  let i := 0+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=true :=
    (lane_support (railF p c) i).mpr (by change 0≤i ∧ i<(0)+(3); dsimp [i]; omega)
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    left
    change (0)+j<(3)
    change j<(3) at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    left
    change (0)+j<(3+q c)
    change j<(3) at hj
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    left
    change (0)+j<(4+q c)
    change j<(3) at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    left
    change (0)+j<(6+q c)
    change j<(3) at hj
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change (0)+j<(7+q c)
    change j<(3) at hj
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change (0)+j<(9+q c)
    change j<(3) at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change (0)+j<(10+q c)
    change j<(3) at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change (0)+j<(11+q c)
    change j<(3) at hj
    omega
  change (pubMask (u,v)).1.getLsbD i=(issue u v).1
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=(oldNative u v).2 := rfl
  have payment_eq : payment (oldNative u v).1 (oldNative u v).2=stepPrefix u v := rfl
  unfold pubMask issue p5 arrival
  dsimp only
  simp only [rhs,payment_eq]
  generalize stepPrefix u v = a
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,fst_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,fst_ite,bit_ite,rail,source,z,arrivalsIssue,launchIssue,turnIssue,
      bothIssue,extraRightIssue]
  all_goals
    generalize (arrivals _ _ _ _).source = sr
    cases sr <;> rfl

set_option linter.unusedSimpArgs false in
theorem right_rail_mask {p c : Nat} (u v : Site p c) :
    full (railF p c) (pubMask (u,v)).2 (issue u v).2.1 := by
  intro j hj
  let i := 0+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=true :=
    (lane_support (railF p c) i).mpr (by change 0≤i ∧ i<(0)+(3); dsimp [i]; omega)
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    left
    change (0)+j<(3)
    change j<(3) at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    left
    change (0)+j<(3+q c)
    change j<(3) at hj
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    left
    change (0)+j<(4+q c)
    change j<(3) at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    left
    change (0)+j<(6+q c)
    change j<(3) at hj
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change (0)+j<(7+q c)
    change j<(3) at hj
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change (0)+j<(9+q c)
    change j<(3) at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change (0)+j<(10+q c)
    change j<(3) at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change (0)+j<(11+q c)
    change j<(3) at hj
    omega
  change (pubMask (u,v)).2.getLsbD i=(issue u v).2.1
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=(oldNative u v).2 := rfl
  have payment_eq : payment (oldNative u v).1 (oldNative u v).2=stepPrefix u v := rfl
  unfold pubMask issue p5 arrival
  dsimp only
  simp only [rhs,payment_eq]
  generalize stepPrefix u v = a
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,arrivalsIssue,launchIssue,turnIssue,
      bothIssue,extraRightIssue]
  all_goals
    generalize (arrivals _ _ _ _).source = sr
    cases sr <;> rfl

set_option linter.unusedSimpArgs false in
theorem right_source_mask {p c : Nat} (u v : Site p c) :
    full (sourceF p c) (pubMask (u,v)).2 (issue u v).2.2 := by
  intro j hj
  let i := 3+j
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=true :=
    (lane_support (sourceF p c) i).mpr (by change 3≤i ∧ i<(3)+(q c); dsimp [i]; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤(3)+j
    change j<(q c) at hj
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    left
    change (3)+j<(3+q c)
    change j<(q c) at hj
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    left
    change (3)+j<(4+q c)
    change j<(q c) at hj
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    left
    change (3)+j<(6+q c)
    change j<(q c) at hj
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change (3)+j<(7+q c)
    change j<(q c) at hj
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change (3)+j<(9+q c)
    change j<(q c) at hj
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change (3)+j<(10+q c)
    change j<(q c) at hj
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change (3)+j<(11+q c)
    change j<(q c) at hj
    omega
  change (pubMask (u,v)).2.getLsbD i=(issue u v).2.2
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=(oldNative u v).2 := rfl
  have payment_eq : payment (oldNative u v).1 (oldNative u v).2=stepPrefix u v := rfl
  unfold pubMask issue p5 arrival
  dsimp only
  simp only [rhs,payment_eq]
  generalize stepPrefix u v = a
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,arrivalsIssue,launchIssue,turnIssue,
      bothIssue,extraRightIssue]
  all_goals
    generalize (arrivals _ _ _ _).source = sr
    cases sr <;> rfl

theorem rails_source_frames {p c : Nat} (u v : Site p c) :
    FieldCase (railF p c) (pubMask (u,v)).1 (u.rail=(pairStep u v).1.rail) ∧
    FieldCase (railF p c) (pubMask (u,v)).2 (v.rail=(pairStep u v).2.rail) ∧
    FieldCase (sourceF p c) (pubMask (u,v)).2 (v.source=(pairStep u v).2.source) := by
  constructor
  · have M := left_rail_mask u v
    cases h : (issue u v).1
    · exact .inr ⟨h ▸ M,(holds u v h).symm⟩
    · exact .inl (h ▸ M)
  constructor
  · have M := right_rail_mask u v
    cases h : (issue u v).2.1
    · exact .inr ⟨h ▸ M,(holds_right u v h).symm⟩
    · exact .inl (h ▸ M)
  · have M := right_source_mask u v
    cases h : (issue u v).2.2
    · exact .inr ⟨h ▸ M,(holds_source u v h).symm⟩
    · exact .inl (h ▸ M)

/-- Complete literal frame for every decoded input; no reachability,
cover, or raw canonicalization premises. -/
theorem actual_frames {p c : Nat} (u v : Site p c) :
    EndpointFrame (pubMask (u,v)).1 u (pairStep u v).1 ∧
    EndpointFrame (pubMask (u,v)).2 v (pairStep u v).2 := by
  have m := BStarPublicMark.marks_frame u v
  have bu := BStarPublicBullet.bullet_frame u v
  have sh := shield_frame u v
  have st := stocks_frame u v
  have pr := rails_source_frames u v
  exact ⟨⟨BStarPublicFieldRows.left_residue_frame u v,m.1,
    BStarPublicFieldRows.left_leader_frame u v,bu.1,sh.1,.inl (left_signal_mask u v),st.1,
    BStarPublicFieldRows.left_source_frame u v,pr.1⟩,
    ⟨BStarPublicFieldRows.right_residue_frame u v,m.2,
    BStarPublicNativeRight.leader_frame u v,bu.2,sh.2,
    BStarPublicNativeRight.signal_frame u v,st.2,pr.2.2,pr.2.1⟩⟩

/-- Ordinary public producer exact all-byte transfer. This
is the ordinary row before the separate downstream marker injection. -/
theorem public_transfer {p c : Nat} (hp : 0<p)
    (x : Pair (BitVec (publicWidth p c))) :
    Pair.map (readPub hp) (patchPair (publicWork hp x) x) =
      pairStep (readPub hp x.1) (readPub hp x.2) :=
  pair_transfer_of_frame hp x (actual_frames (readPub hp x.1) (readPub hp x.2))

end L4.BStarPublicPatrol

