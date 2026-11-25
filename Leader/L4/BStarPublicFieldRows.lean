import Leader.L4.BStarPublicFrame
import Leader.L4.TaggedGeometry

namespace L4.BStarPublicFieldRows
open AllSizeProtocol BStarPublicCodec BStarPublic BStarPublicFrame

private theorem bit_ite {w : Nat} (P : Prop) [Decidable P] (x y : BitVec w) (i : Nat) :
    (if P then x else y).getLsbD i=(if P then x.getLsbD i else y.getLsbD i) := by
  by_cases h : P <;> simp [h]

private theorem fst_ite {A B : Type} (P : Prop) [Decidable P] (x y : A × B) :
    (if P then x else y).1=(if P then x.1 else y.1) := by
  by_cases h : P <;> simp [h]

set_option linter.unusedSimpArgs false in
private theorem left_bit_off {p c : Nat} (u v : Site p c) (i : Nat)
    (hRail : (BitVec.ofNat (publicWidth p c) ((2^3-1)*2^0)).getLsbD i=false)
    (hStock : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(3+q c))).getLsbD i=false)
    (hSignal : (BitVec.ofNat (publicWidth p c) ((2^2-1)*2^(4+q c))).getLsbD i=false)
    (hShield : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(6+q c))).getLsbD i=false)
    (hBullet : (BitVec.ofNat (publicWidth p c) ((2^2-1)*2^(7+q c))).getLsbD i=false)
    (hMark : (BitVec.ofNat (publicWidth p c) ((2^1-1)*2^(10+q c))).getLsbD i=false) :
    (pubMask (u,v)).1.getLsbD i=false := by
  have hZero : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  unfold pubMask
  dsimp only
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,fst_ite,bit_ite,hMark,hRail,hStock,hSignal,hShield,hBullet,
    hZero,Bool.or_false,Bool.false_or,ite_self]
  cases hS : s.source <;> cases hL : s.left <;>
    simp [hS,hL,fst_ite,bit_ite,hRail,hZero]

private theorem lane_off {w k} (f : Field w k) (i : Nat)
    (h : i<f.offset ∨ f.offset+k≤i) :
    (BitVec.ofNat w ((2^k-1)*2^f.offset)).getLsbD i=false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨a,b⟩ := (lane_support f i).mp ht
  omega

theorem left_residue_mask {p c : Nat} (u v : Site p c) :
    full (residueF p c) (pubMask (u,v)).1 false := by
  intro j hj
  change j<ell p at hj
  apply left_bit_off
  · apply lane_off (railF p c)
    change (11+q c)+j<(0) ∨ (0)+(3)≤(11+q c)+j
    omega
  · apply lane_off (stockF p c)
    change (11+q c)+j<(3+q c) ∨ (3+q c)+(1)≤(11+q c)+j
    omega
  · apply lane_off (signalF p c)
    change (11+q c)+j<(4+q c) ∨ (4+q c)+(2)≤(11+q c)+j
    omega
  · apply lane_off (shieldF p c)
    change (11+q c)+j<(6+q c) ∨ (6+q c)+(1)≤(11+q c)+j
    omega
  · apply lane_off (bulletF p c)
    change (11+q c)+j<(7+q c) ∨ (7+q c)+(2)≤(11+q c)+j
    omega
  · apply lane_off (markF p c)
    change (11+q c)+j<(10+q c) ∨ (10+q c)+(1)≤(11+q c)+j
    omega

theorem left_residue_frame {p c : Nat} (u v : Site p c) :
    FieldCase (residueF p c) (pubMask (u,v)).1 (u.residue=(pairStep u v).1.residue) :=
  .inr ⟨left_residue_mask u v,(left_static u v).1.symm⟩

theorem left_leader_mask {p c : Nat} (u v : Site p c) :
    full (leaderF p c) (pubMask (u,v)).1 false := by
  intro j hj
  change j<1 at hj
  apply left_bit_off
  · apply lane_off (railF p c)
    change (9+q c)+j<(0) ∨ (0)+(3)≤(9+q c)+j
    omega
  · apply lane_off (stockF p c)
    change (9+q c)+j<(3+q c) ∨ (3+q c)+(1)≤(9+q c)+j
    omega
  · apply lane_off (signalF p c)
    change (9+q c)+j<(4+q c) ∨ (4+q c)+(2)≤(9+q c)+j
    omega
  · apply lane_off (shieldF p c)
    change (9+q c)+j<(6+q c) ∨ (6+q c)+(1)≤(9+q c)+j
    omega
  · apply lane_off (bulletF p c)
    change (9+q c)+j<(7+q c) ∨ (7+q c)+(2)≤(9+q c)+j
    omega
  · apply lane_off (markF p c)
    change (9+q c)+j<(10+q c) ∨ (10+q c)+(1)≤(9+q c)+j
    omega

theorem left_leader_frame {p c : Nat} (u v : Site p c) :
    FieldCase (leaderF p c) (pubMask (u,v)).1 (u.leader=(pairStep u v).1.leader) :=
  .inr ⟨left_leader_mask u v,(left_static u v).2.1.symm⟩

theorem left_source_mask {p c : Nat} (u v : Site p c) :
    full (sourceF p c) (pubMask (u,v)).1 false := by
  intro j hj
  change j<q c at hj
  apply left_bit_off
  · apply lane_off (railF p c)
    change (3)+j<(0) ∨ (0)+(3)≤(3)+j
    omega
  · apply lane_off (stockF p c)
    change (3)+j<(3+q c) ∨ (3+q c)+(1)≤(3)+j
    omega
  · apply lane_off (signalF p c)
    change (3)+j<(4+q c) ∨ (4+q c)+(2)≤(3)+j
    omega
  · apply lane_off (shieldF p c)
    change (3)+j<(6+q c) ∨ (6+q c)+(1)≤(3)+j
    omega
  · apply lane_off (bulletF p c)
    change (3)+j<(7+q c) ∨ (7+q c)+(2)≤(3)+j
    omega
  · apply lane_off (markF p c)
    change (3)+j<(10+q c) ∨ (10+q c)+(1)≤(3)+j
    omega

theorem left_source_frame {p c : Nat} (u v : Site p c) :
    FieldCase (sourceF p c) (pubMask (u,v)).1 (u.source=(pairStep u v).1.source) :=
  .inr ⟨left_source_mask u v,(left_static u v).2.2.symm⟩

/-- The three never-written left byte fields are retained even if
the incoming source or residue uses a spare raw encoding. -/
theorem left_static_raw {p c : Nat} (hp : 0<p)
    (x : Pair (BitVec (publicWidth p c))) :
    let out := ((publicWork hp x).1.apply x.1)
    (residueF p c).read out=(residueF p c).read x.1 ∧
    (leaderF p c).read out=(leaderF p c).read x.1 ∧
    (sourceF p c).read out=(sourceF p c).read x.1 :=
  ⟨read_patch_hold _ _ _ (left_residue_mask (readPub hp x.1) (readPub hp x.2)),
   read_patch_hold _ _ _ (left_leader_mask (readPub hp x.1) (readPub hp x.2)),
   read_patch_hold _ _ _ (left_source_mask (readPub hp x.1) (readPub hp x.2))⟩

private theorem snd_ite {A B : Type} (P : Prop) [Decidable P] (x y : A × B) :
    (if P then x else y).2=(if P then x.2 else y.2) := by
  by_cases h : P <;> simp [h]

set_option linter.unusedSimpArgs false in
/-- The responder residue is written exactly on P3. No other
substage, including the terminal P5, touches its raw lane. -/
theorem right_residue_mask {p c : Nat} (u v : Site p c) :
    full (residueF p c) (pubMask (u,v)).2 (geometricPay u v) := by
  intro j hj
  let i := 11+q c+j
  have one : (BitVec.ofNat (publicWidth p c) ((2^ell p-1)*2^(11+q c))).getLsbD i=true :=
    (lane_support (residueF p c) i).mpr (by change 11+q c≤i ∧ i<11+q c+ell p; dsimp [i]; omega)
  have z : (0 : BitVec (publicWidth p c)).getLsbD i=false := BitVec.getLsbD_zero
  have rail : (BitVec.ofNat (publicWidth p c) ((2^(3)-1)*2^(0))).getLsbD i=false := by
    apply lane_off (railF p c)
    right
    change (0)+(3)≤11+q c+j
    omega
  have source : (BitVec.ofNat (publicWidth p c) ((2^(q c)-1)*2^(3))).getLsbD i=false := by
    apply lane_off (sourceF p c)
    right
    change (3)+(q c)≤11+q c+j
    omega
  have stock : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(3+q c))).getLsbD i=false := by
    apply lane_off (stockF p c)
    right
    change (3+q c)+(1)≤11+q c+j
    omega
  have signal : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(4+q c))).getLsbD i=false := by
    apply lane_off (signalF p c)
    right
    change (4+q c)+(2)≤11+q c+j
    omega
  have shield : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(6+q c))).getLsbD i=false := by
    apply lane_off (shieldF p c)
    right
    change (6+q c)+(1)≤11+q c+j
    omega
  have bullet : (BitVec.ofNat (publicWidth p c) ((2^(2)-1)*2^(7+q c))).getLsbD i=false := by
    apply lane_off (bulletF p c)
    right
    change (7+q c)+(2)≤11+q c+j
    omega
  have leader : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(9+q c))).getLsbD i=false := by
    apply lane_off (leaderF p c)
    right
    change (9+q c)+(1)≤11+q c+j
    omega
  have mark : (BitVec.ofNat (publicWidth p c) ((2^(1)-1)*2^(10+q c))).getLsbD i=false := by
    apply lane_off (markF p c)
    right
    change (10+q c)+(1)≤11+q c+j
    omega
  change (pubMask (u,v)).2.getLsbD i=geometricPay u v
  have pay_iff : (!((followerBullet
      (pinned (impact (fireInitiator (materialize u v)) (fireResponder v)).1
        (impact (fireInitiator (materialize u v)) (fireResponder v)).2)
      (impact (fireInitiator (materialize u v)) (fireResponder v)).1
      (impact (fireInitiator (materialize u v)) (fireResponder v)).2).2.leader) &&
       (native (materialize u v) v).1.mark && payer (native (materialize u v) v).1)
      = geometricPay u v := rfl
  unfold pubMask
  dsimp only
  generalize sourceGuard _ _ = s
  simp only [BitVec.getLsbD_or,snd_ite,bit_ite,one,rail,source,stock,signal,shield,bullet,leader,
    mark,z,Bool.or_false,Bool.false_or,ite_self,pay_iff]
  cases hS : s.source <;> cases hL : s.left <;> cases hb : geometricPay u v <;>
    simp [hS,hL,hb,snd_ite,bit_ite,source,z]

theorem right_residue_frame {p c : Nat} (u v : Site p c) :
    FieldCase (residueF p c) (pubMask (u,v)).2 (v.residue=(pairStep u v).2.residue) := by
  cases h : geometricPay u v
  · apply Or.inr
    refine ⟨h ▸ right_residue_mask u v,?_⟩
    have eq := (pair_geometric_fields u v).2.2
    rw [h] at eq
    exact eq.symm
  · exact .inl (h ▸ right_residue_mask u v)

theorem raw_right_residue {p c : Nat} (hp : 0<p)
    (x : Pair (BitVec (publicWidth p c))) :
    (readPub hp ((publicWork hp x).2.apply x.2)).residue =
      (pairStep (readPub hp x.1) (readPub hp x.2)).2.residue := by
  let u := readPub hp x.1
  let v := readPub hp x.2
  let y := (pairStep u v).2
  let patch := (publicWork hp x).2
  change residueDecode hp ((residueF p c).read (patch.apply x.2))=y.residue
  exact decoded_field (residueDecode hp) (residueF p c) patch x.2 y.residue
    (congrArg Site.residue (read_pack hp y)) (right_residue_frame u v)

#print axioms left_static_raw
#print axioms raw_right_residue

end L4.BStarPublicFieldRows

