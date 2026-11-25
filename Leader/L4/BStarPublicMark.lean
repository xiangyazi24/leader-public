import Leader.L4.BStarPublicStock

namespace L4.BStarPublicMark
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


def shouldMark {p c : Nat} (u v : Site p c) := v.leader || u.mark || defect u v

private theorem native_marks {p c : Nat} (u v : Site p c) :
    (native u v).1.mark=u.mark ∧ (native u v).2.mark=v.mark := by
  have i (a : Site p c) : (fireInitiator a).mark=a.mark := by
    unfold fireInitiator; split <;> rfl
  have r (a : Site p c) : (fireResponder a).mark=a.mark := by
    unfold fireResponder; split; · cases a.signal <;> rfl
    · rfl
  have imp (a b : Site p c) :
      (impact a b).1.mark=a.mark ∧ (impact a b).2.mark=b.mark := by
    unfold impact
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have fb (g : Bool) (a b : Site p c) :
      (followerBullet g a b).1.mark=a.mark ∧ (followerBullet g a b).2.mark=b.mark := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  simp only [native,(imp _ _).1,(imp _ _).2,(fb _ _ _).1,(fb _ _ _).2,i,r,and_self]

private theorem prefix_pair_marks {p c : Nat} (u v : Site p c) :
    ((pairStep u v).1.mark,(pairStep u v).2.mark) =
      ((stepPrefix u v).1.mark,(stepPrefix u v).2.mark) := by
  unfold pairStep
  generalize stepPrefix u v = z
  rcases z with ⟨a,b⟩
  dsimp [patrolWrite]
  unfold finishBirth
  split <;> rfl

/-- The actual R0/native/payment pipeline on arbitrary typed sites;
no mark-cover or source-cover hypothesis is used. -/
theorem marks_typed {p c : Nat} (u v : Site p c) :
    let a := oldNative u v
    ((pairStep u v).1.mark,(pairStep u v).2.mark) =
      (if geometricPay u v then false else (a.2.leader || shouldMark u v || u.mark),
        if geometricPay u v then true else v.mark) := by
  have rule (l r : Site p c) :
      ((payment l r).1.mark,(payment l r).2.mark)=
      (if !r.leader && l.mark && payer l then false else (r.leader || l.mark),
       if !r.leader && l.mark && payer l then true else r.mark) := by
    cases hL : r.leader <;> cases hm : l.mark <;> cases hs : r.stock <;> cases hp : payer l <;>
      simp [payment,hL,hm,hs,hp]
  let a := oldNative u v
  have old := native_marks (materialize u v) v
  have hL : a.1.mark=(shouldMark u v || u.mark) := by
    rw [show a.1.mark=(materialize u v).mark from old.1]
    unfold materialize shouldMark
    split <;> simp_all
  have hR : a.2.mark=v.mark := old.2
  rw [prefix_pair_marks]
  change ((payment a.1 a.2).1.mark,(payment a.1 a.2).2.mark)=
    (if !a.2.leader && a.1.mark && payer a.1 then false
      else (a.2.leader || shouldMark u v || u.mark),
      if !a.2.leader && a.1.mark && payer a.1 then true else v.mark)
  rw [rule]
  rw [hL,hR]
  simp [Bool.or_assoc]

set_option linter.unusedSimpArgs false in
theorem left_mark_mask {p c : Nat} (u v : Site p c) :
    full (markF p c) (pubMask (u,v)).1 (shouldMark u v || (oldNative u v).2.leader || geometricPay u v) := by
  intro j hj
  change j<1 at hj
  have j0 : j=0 := by omega
  subst j
  let i := 10+q c
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have mark : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(10+q c))).getLsbD i=true :=
    (lane_support (markF p c) i).mpr (by change i≤i ∧ i<i+1; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤10+q c
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤10+q c
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤10+q c
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤10+q c
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    right
    change (6+q c)+(1)≤10+q c
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    right
    change (7+q c)+(2)≤10+q c
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    right
    change (9+q c)+(1)≤10+q c
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 10+q c<(11+q c)
    omega
  change (pubMask (u,v)).1.getLsbD i=(shouldMark u v || (oldNative u v).2.leader || geometricPay u v)
  let a := oldNative u v
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=a.2 := rfl
  unfold pubMask
  dsimp only
  generalize sourceGuard _ _ = s
  simp only [rhs,BitVec.getLsbD_or,fst_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  change _=(shouldMark u v || a.2.leader || geometricPay u v)
  have same : (native (materialize u v) v).1=a.1 := rfl
  simp only [same]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,fst_ite,bit_ite,rail,source,z,shouldMark,geometricPay,
      show native (materialize u v) v=a from rfl]

set_option linter.unusedSimpArgs false in
theorem right_mark_mask {p c : Nat} (u v : Site p c) :
    full (markF p c) (pubMask (u,v)).2 (geometricPay u v) := by
  intro j hj
  change j<1 at hj
  have j0 : j=0 := by omega
  subst j
  let i := 10+q c
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have mark : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(10+q c))).getLsbD i=true :=
    (lane_support (markF p c) i).mpr (by change i≤i ∧ i<i+1; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤10+q c
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤10+q c
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤10+q c
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤10+q c
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    right
    change (6+q c)+(1)≤10+q c
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    right
    change (7+q c)+(2)≤10+q c
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    right
    change (9+q c)+(1)≤10+q c
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 10+q c<(11+q c)
    omega
  change (pubMask (u,v)).2.getLsbD i=(geometricPay u v)
  let a := oldNative u v
  have rhs : (followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2=a.2 := rfl
  unfold pubMask
  dsimp only
  generalize sourceGuard _ _ = s
  simp only [rhs,BitVec.getLsbD_or,snd_ite,bit_ite,rail,source,stock,signal,shield,bullet,
    leader,mark,residue,z,Bool.or_false,Bool.false_or,ite_self]
  change _=(geometricPay u v)
  have same : (native (materialize u v) v).1=a.1 := rfl
  simp only [same]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,shouldMark,geometricPay,
      show native (materialize u v) v=a from rfl]

theorem marks_frame {p c : Nat} (u v : Site p c) :
    FieldCase (markF p c) (pubMask (u,v)).1 (u.mark=(pairStep u v).1.mark) ∧
    FieldCase (markF p c) (pubMask (u,v)).2 (v.mark=(pairStep u v).2.mark) := by
  let a := oldNative u v
  have typed := marks_typed u v
  dsimp only at typed
  constructor
  · let b := shouldMark u v || a.2.leader || geometricPay u v
    have mask : full (markF p c) (pubMask (u,v)).1 b := left_mark_mask u v
    cases h : b
    · have frame := congrArg Prod.fst typed
      change (pairStep u v).1.mark=(if geometricPay u v then false else
        a.2.leader || shouldMark u v || u.mark) at frame
      have hc : shouldMark u v=false ∧ a.2.leader=false ∧ geometricPay u v=false := by
        cases hR : shouldMark u v <;> cases hN : a.2.leader <;>
          cases hG : geometricPay u v <;> simp_all [b]
      rw [h] at mask
      exact .inr ⟨mask,by simpa [hc.1,hc.2.1,hc.2.2] using frame.symm⟩
    · exact .inl (h ▸ mask)
  · have mask := right_mark_mask u v
    cases h : geometricPay u v
    · have frame := congrArg Prod.snd typed
      change (pairStep u v).2.mark=(if geometricPay u v then true else v.mark) at frame
      rw [h] at mask frame
      exact .inr ⟨mask,frame.symm⟩
    · exact .inl (h ▸ mask)

theorem raw_marks {p c : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c))) :
    let old := Pair.map (readPub hp) x
    let new := pairStep old.1 old.2
    let y := Pair.map (readPub hp) (patchPair (publicWork hp x) x)
    y.1.mark=new.1.mark ∧ y.2.mark=new.2.mark := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let t := pairStep u v
  have h := marks_frame u v
  exact ⟨decoded_field (fun s => s.getLsbD 0) (markF p c) (publicWork hp x).1 x.1 t.1.mark
      (congrArg Site.mark (read_pack hp t.1)) h.1,
    decoded_field (fun s => s.getLsbD 0) (markF p c) (publicWork hp x).2 x.2 t.2.mark
      (congrArg Site.mark (read_pack hp t.2)) h.2⟩

#print axioms raw_marks

end L4.BStarPublicMark

