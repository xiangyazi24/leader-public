import Leader.L4.BStarPublicFieldRows
import Leader.L4.BarrierRows

namespace L4.BStarPublicStock
open AllSizeProtocol BStarPublicCodec BStarPublic BStarPublicFrame

abbrev oldNative {p c : Nat} (u v : Site p c) := native (materialize u v) v

def p2 {p c : Nat} (a b : Site p c) : Bool :=
  !b.leader && !a.mark && !b.stock && payer a

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

private theorem native_stocks {p c : Nat} (u v : Site p c) :
    (oldNative u v).1.stock=u.stock ∧ (oldNative u v).2.stock=v.stock := by
  have rm : (materialize u v).stock=u.stock := by unfold materialize; split <;> rfl
  have i (a : Site p c) : (fireInitiator a).stock=a.stock := by
    unfold fireInitiator; split <;> rfl
  have r (a : Site p c) : (fireResponder a).stock=a.stock := by
    unfold fireResponder; split; · cases a.signal <;> rfl
    · rfl
  have imp (a b : Site p c) :
      (impact a b).1.stock=a.stock ∧ (impact a b).2.stock=b.stock := by
    unfold impact
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  have fb (g : Bool) (a b : Site p c) :
      (followerBullet g a b).1.stock=a.stock ∧ (followerBullet g a b).2.stock=b.stock := by
    unfold followerBullet
    split
    · split <;> exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  simp only [oldNative,native,(imp _ _).1,(imp _ _).2,(fb _ _ _).1,(fb _ _ _).2,i,r,rm,and_self]

/-- Literal payment stages supply the stock frame independently of
the packed mask, and patrol and P5 preserve both stock bytes. -/
theorem stocks_typed {p c : Nat} (u v : Site p c) :
    let a := oldNative u v
    ((pairStep u v).1.stock,(pairStep u v).2.stock) =
      (if a.2.leader || p2 a.1 a.2 || geometricPay u v then false else u.stock,
        if p2 a.1 a.2 then true else v.stock) := by
  have rule (l r : Site p c) :
      ((payment l r).1.stock,(payment l r).2.stock)=
      (if r.leader || p2 l r || (!r.leader && l.mark && payer l)
        then false else l.stock, if p2 l r then true else r.stock) := by
    cases hL : r.leader <;> cases hm : l.mark <;> cases hs : r.stock <;> cases hp : payer l <;>
      simp [payment,p2,hL,hm,hs,hp]
  have old := native_stocks u v
  rw [pairStep_stocks_eq_prefix]
  let a := oldNative u v
  change ((payment a.1 a.2).1.stock,(payment a.1 a.2).2.stock)=
    (if a.2.leader || p2 a.1 a.2 || (!a.2.leader && a.1.mark && payer a.1) then false else u.stock,
      if p2 a.1 a.2 then true else v.stock)
  calc
    _ = (if a.2.leader || p2 a.1 a.2 || (!a.2.leader && a.1.mark && payer a.1) then false else a.1.stock,
      if p2 a.1 a.2 then true else a.2.stock) := rule _ _
    _ = _ := by
      have hL : a.1.stock=u.stock := old.1
      have hR : a.2.stock=v.stock := old.2
      rw [hL,hR]

set_option linter.unusedSimpArgs false in
theorem left_stock_mask {p c : Nat} (u v : Site p c) :
    full (stockF p c) (pubMask (u,v)).1
      ((oldNative u v).2.leader || p2 (oldNative u v).1 (oldNative u v).2 || geometricPay u v) := by
  intro j hj
  change j<1 at hj
  have j0 : j=0 := by omega
  subst j
  let i := 3+q c
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have stock : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(3+q c))).getLsbD i=true :=
    (lane_support (stockF p c) i).mpr (by change i≤i ∧ i<i+1; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤3+q c
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤3+q c
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    left
    change 3+q c<(4+q c)
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    left
    change 3+q c<(6+q c)
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change 3+q c<(7+q c)
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change 3+q c<(9+q c)
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change 3+q c<(10+q c)
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 3+q c<(11+q c)
    omega
  change (pubMask (u,v)).1.getLsbD i=((oldNative u v).2.leader || p2 (oldNative u v).1 (oldNative u v).2 || geometricPay u v)
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
  change _=(a.2.leader || p2 a.1 a.2 || geometricPay u v)
  have same : (native (materialize u v) v).1=a.1 := rfl
  simp only [same] 
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,fst_ite,bit_ite,rail,source,z,p2,geometricPay,
      show native (materialize u v) v=a from rfl]

set_option linter.unusedSimpArgs false in
theorem right_stock_mask {p c : Nat} (u v : Site p c) :
    full (stockF p c) (pubMask (u,v)).2
      (p2 (oldNative u v).1 (oldNative u v).2) := by
  intro j hj
  change j<1 at hj
  have j0 : j=0 := by omega
  subst j
  let i := 3+q c
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have stock : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(3+q c))).getLsbD i=true :=
    (lane_support (stockF p c) i).mpr (by change i≤i ∧ i<i+1; omega)
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤3+q c
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤3+q c
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    left
    change 3+q c<(4+q c)
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    left
    change 3+q c<(6+q c)
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    left
    change 3+q c<(7+q c)
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    left
    change 3+q c<(9+q c)
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    left
    change 3+q c<(10+q c)
    omega
  have residue : (BitVec.ofNat (publicWidth p c) ((2^(ell p)-1)*2^(11+q c))).getLsbD i=false := by
    apply lane_off (residueF p c)
    left
    change 3+q c<(11+q c)
    omega
  change (pubMask (u,v)).2.getLsbD i=(p2 (oldNative u v).1 (oldNative u v).2)
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
  change _=(p2 a.1 a.2)
  have same : (native (materialize u v) v).1=a.1 := rfl
  simp only [same] 
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,snd_ite,bit_ite,rail,source,z,p2,geometricPay,
      show native (materialize u v) v=a from rfl]

theorem stocks_frame {p c : Nat} (u v : Site p c) :
    FieldCase (stockF p c) (pubMask (u,v)).1 (u.stock=(pairStep u v).1.stock) ∧
    FieldCase (stockF p c) (pubMask (u,v)).2 (v.stock=(pairStep u v).2.stock) := by
  let a := oldNative u v
  have typed := stocks_typed u v
  dsimp only at typed
  constructor
  · let b := a.2.leader || p2 a.1 a.2 || geometricPay u v
    have mask : full (stockF p c) (pubMask (u,v)).1 b := left_stock_mask u v
    cases h : b
    · have frame := congrArg Prod.fst typed
      change (pairStep u v).1.stock=(if b then false else u.stock) at frame
      rw [h] at mask frame
      exact .inr ⟨mask,frame.symm⟩
    · exact .inl (h ▸ mask)
  · let b := p2 a.1 a.2
    have mask : full (stockF p c) (pubMask (u,v)).2 b := right_stock_mask u v
    cases h : b
    · have frame := congrArg Prod.snd typed
      change (pairStep u v).2.stock=(if b then true else v.stock) at frame
      rw [h] at mask frame
      exact .inr ⟨mask,frame.symm⟩
    · exact .inl (h ▸ mask)

theorem raw_stocks {p c : Nat} (hp : 0<p) (x : Pair (BitVec (publicWidth p c))) :
    let old := Pair.map (readPub hp) x
    let new := pairStep old.1 old.2
    let y := Pair.map (readPub hp) (patchPair (publicWork hp x) x)
    y.1.stock=new.1.stock ∧ y.2.stock=new.2.stock := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let t := pairStep u v
  have h := stocks_frame u v
  exact ⟨decoded_field (fun s => s.getLsbD 0) (stockF p c) (publicWork hp x).1 x.1 t.1.stock
      (congrArg Site.stock (read_pack hp t.1)) h.1,
    decoded_field (fun s => s.getLsbD 0) (stockF p c) (publicWork hp x).2 x.2 t.2.stock
      (congrArg Site.stock (read_pack hp t.2)) h.2⟩

end L4.BStarPublicStock

