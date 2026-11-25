import Leader.L4.AllSizeProtocol

/-! Total public read and canonical pack of the literal
modular protocol.  Low numerical offsets do not follow record order. -/
namespace L4.BStarPublicCodec
open AllSizeProtocol

abbrev q (c : Nat) := ell (4*c+3)

def railF (p c : Nat) : Field (publicWidth p c) 3 := ⟨0,by unfold publicWidth; dsimp [q]; omega⟩
def sourceF (p c : Nat) : Field (publicWidth p c) (q c) := ⟨3,by unfold publicWidth; dsimp [q]; omega⟩
def stockF (p c : Nat) : Field (publicWidth p c) 1 := ⟨3+q c,by unfold publicWidth; dsimp [q]; omega⟩
def signalF (p c : Nat) : Field (publicWidth p c) 2 := ⟨4+q c,by unfold publicWidth; dsimp [q]; omega⟩
def shieldF (p c : Nat) : Field (publicWidth p c) 1 := ⟨6+q c,by unfold publicWidth; dsimp [q]; omega⟩
def bulletF (p c : Nat) : Field (publicWidth p c) 2 := ⟨7+q c,by unfold publicWidth; dsimp [q]; omega⟩
def leaderF (p c : Nat) : Field (publicWidth p c) 1 := ⟨9+q c,by unfold publicWidth; dsimp [q]; omega⟩
def markF (p c : Nat) : Field (publicWidth p c) 1 := ⟨10+q c,by unfold publicWidth; dsimp [q]; omega⟩
def residueF (p c : Nat) : Field (publicWidth p c) (ell p) :=
  ⟨11+q c,by unfold publicWidth; dsimp [q]; omega⟩

def sourceEncode {Q : Nat} : Source Q → Nat
  | .off => 0
  | .i0 => 1
  | .i1 => 2
  | .count k => 3+k.val
  | .await k => 3+Q+k.val

def sourceDecode (Q k : Nat) : Source Q :=
  if k = 1 then .i0
  else if k = 2 then .i1
  else if hc : 3≤k ∧ k<3+Q then .count ⟨k-3,by omega⟩
  else if ha : 3+Q≤k ∧ k<3+2*Q then .await ⟨k-(3+Q),by omega⟩
  else .off

theorem source_bound {Q : Nat} (s : Source Q) : sourceEncode s < 2*Q+3 := by
  cases s with
  | count k | await k => have H := k.isLt; simp [sourceEncode]; omega
  | off | i0 | i1 => simp [sourceEncode] <;> omega

@[simp] theorem source_section {Q : Nat} (s : Source Q) : sourceDecode Q (sourceEncode s)=s := by
  cases s with
  | off | i0 | i1 => simp [sourceEncode,sourceDecode]
  | count k =>
    have h := k.isLt
    simp [sourceEncode,sourceDecode,show 3+k.val≠1 by omega,show 3+k.val≠2 by omega,h]
  | await k =>
    have h := k.isLt
    simp [sourceEncode,sourceDecode,show 3+Q+k.val≠1 by omega,show 3+Q+k.val≠2 by omega,
      show ¬3+Q+k.val<3+Q by omega,show 3+Q≤3+Q+k.val by omega,
      show 3+Q+k.val<3+2*Q by omega,show 3+Q+k.val-(3+Q)=k.val by omega]

def railEncode : Rail → BitVec 3
  | .e => 0 | .t => 1 | .ui => 2 | .uc => 3 | .di => 4 | .dc => 5 | .x => 6
def railDecode (x : BitVec 3) : Rail :=
  match x.toNat with
  | 1 => .t | 2 => .ui | 3 => .uc | 4 => .di | 5 => .dc | 6 => .x | _ => .e

def bulletEncode : Bullet → BitVec 2
  | .none => 0 | .dummy => 1 | .live => 2
def bulletDecode (x : BitVec 2) : Bullet :=
  match x.toNat with
  | 1 => .dummy | 2 => .live | _ => .none

def signalEncode : Signal → BitVec 2
  | .zero => 0 | .one => 1 | .two => 2
def signalDecode (x : BitVec 2) : Signal :=
  match x.toNat with
  | 1 => .one | 2 => .two | _ => .zero

def residueDecode {p : Nat} (hp : 0<p) (x : BitVec (ell p)) : Fin p :=
  if hx : x.toNat<p then ⟨x.toNat,hx⟩ else ⟨0,hp⟩

def readPub {p c : Nat} (hp : 0<p) (x : BitVec (publicWidth p c)) : Site p c :=
  ⟨residueDecode hp ((residueF p c).read x),
   ((markF p c).read x).getLsbD 0,
   ((leaderF p c).read x).getLsbD 0,
   bulletDecode ((bulletF p c).read x),
   ((shieldF p c).read x).getLsbD 0,
   signalDecode ((signalF p c).read x),
   ((stockF p c).read x).getLsbD 0,
   sourceDecode (2*c) ((sourceF p c).read x).toNat,
   railDecode ((railF p c).read x)⟩

def packPub {p c : Nat} (s : Site p c) : BitVec (publicWidth p c) :=
  let b0 := ((railF p c).assign (railEncode s.rail)).apply 0
  let b1 := ((sourceF p c).assign (BitVec.ofNat _ (sourceEncode s.source))).apply b0
  let b2 := ((stockF p c).assign (BitVec.ofBool s.stock)).apply b1
  let b3 := ((signalF p c).assign (signalEncode s.signal)).apply b2
  let b4 := ((shieldF p c).assign (BitVec.ofBool s.shield)).apply b3
  let b5 := ((bulletF p c).assign (bulletEncode s.bullet)).apply b4
  let b6 := ((leaderF p c).assign (BitVec.ofBool s.leader)).apply b5
  let b7 := ((markF p c).assign (BitVec.ofBool s.mark)).apply b6
  ((residueF p c).assign (BitVec.ofNat _ s.residue.val)).apply b7

@[simp] theorem read_pack_rail {p c : Nat} (s : Site p c) :
    (railF p c).read (packPub s)=railEncode s.rail := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (railF p c) (residueF p c) _ _ (Or.inl (by change (0)+(3)≤(11+q c); omega))]
  rw [Field.read_other_assign (railF p c) (markF p c) _ _ (Or.inl (by change (0)+(3)≤(10+q c); omega))]
  rw [Field.read_other_assign (railF p c) (leaderF p c) _ _ (Or.inl (by change (0)+(3)≤(9+q c); omega))]
  rw [Field.read_other_assign (railF p c) (bulletF p c) _ _ (Or.inl (by change (0)+(3)≤(7+q c); omega))]
  rw [Field.read_other_assign (railF p c) (shieldF p c) _ _ (Or.inl (by change (0)+(3)≤(6+q c); omega))]
  rw [Field.read_other_assign (railF p c) (signalF p c) _ _ (Or.inl (by change (0)+(3)≤(4+q c); omega))]
  rw [Field.read_other_assign (railF p c) (stockF p c) _ _ (Or.inl (by change (0)+(3)≤(3+q c); omega))]
  rw [Field.read_other_assign (railF p c) (sourceF p c) _ _ (Or.inl (by change (0)+(3)≤(3); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_source {p c : Nat} (s : Site p c) :
    (sourceF p c).read (packPub s)=BitVec.ofNat _ (sourceEncode s.source) := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (sourceF p c) (residueF p c) _ _ (Or.inl (by change (3)+(q c)≤(11+q c); omega))]
  rw [Field.read_other_assign (sourceF p c) (markF p c) _ _ (Or.inl (by change (3)+(q c)≤(10+q c); omega))]
  rw [Field.read_other_assign (sourceF p c) (leaderF p c) _ _ (Or.inl (by change (3)+(q c)≤(9+q c); omega))]
  rw [Field.read_other_assign (sourceF p c) (bulletF p c) _ _ (Or.inl (by change (3)+(q c)≤(7+q c); omega))]
  rw [Field.read_other_assign (sourceF p c) (shieldF p c) _ _ (Or.inl (by change (3)+(q c)≤(6+q c); omega))]
  rw [Field.read_other_assign (sourceF p c) (signalF p c) _ _ (Or.inl (by change (3)+(q c)≤(4+q c); omega))]
  rw [Field.read_other_assign (sourceF p c) (stockF p c) _ _ (Or.inl (by change (3)+(q c)≤(3+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_stock {p c : Nat} (s : Site p c) :
    (stockF p c).read (packPub s)=BitVec.ofBool s.stock := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (stockF p c) (residueF p c) _ _ (Or.inl (by change (3+q c)+(1)≤(11+q c); omega))]
  rw [Field.read_other_assign (stockF p c) (markF p c) _ _ (Or.inl (by change (3+q c)+(1)≤(10+q c); omega))]
  rw [Field.read_other_assign (stockF p c) (leaderF p c) _ _ (Or.inl (by change (3+q c)+(1)≤(9+q c); omega))]
  rw [Field.read_other_assign (stockF p c) (bulletF p c) _ _ (Or.inl (by change (3+q c)+(1)≤(7+q c); omega))]
  rw [Field.read_other_assign (stockF p c) (shieldF p c) _ _ (Or.inl (by change (3+q c)+(1)≤(6+q c); omega))]
  rw [Field.read_other_assign (stockF p c) (signalF p c) _ _ (Or.inl (by change (3+q c)+(1)≤(4+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_signal {p c : Nat} (s : Site p c) :
    (signalF p c).read (packPub s)=signalEncode s.signal := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (signalF p c) (residueF p c) _ _ (Or.inl (by change (4+q c)+(2)≤(11+q c); omega))]
  rw [Field.read_other_assign (signalF p c) (markF p c) _ _ (Or.inl (by change (4+q c)+(2)≤(10+q c); omega))]
  rw [Field.read_other_assign (signalF p c) (leaderF p c) _ _ (Or.inl (by change (4+q c)+(2)≤(9+q c); omega))]
  rw [Field.read_other_assign (signalF p c) (bulletF p c) _ _ (Or.inl (by change (4+q c)+(2)≤(7+q c); omega))]
  rw [Field.read_other_assign (signalF p c) (shieldF p c) _ _ (Or.inl (by change (4+q c)+(2)≤(6+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_shield {p c : Nat} (s : Site p c) :
    (shieldF p c).read (packPub s)=BitVec.ofBool s.shield := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (shieldF p c) (residueF p c) _ _ (Or.inl (by change (6+q c)+(1)≤(11+q c); omega))]
  rw [Field.read_other_assign (shieldF p c) (markF p c) _ _ (Or.inl (by change (6+q c)+(1)≤(10+q c); omega))]
  rw [Field.read_other_assign (shieldF p c) (leaderF p c) _ _ (Or.inl (by change (6+q c)+(1)≤(9+q c); omega))]
  rw [Field.read_other_assign (shieldF p c) (bulletF p c) _ _ (Or.inl (by change (6+q c)+(1)≤(7+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_bullet {p c : Nat} (s : Site p c) :
    (bulletF p c).read (packPub s)=bulletEncode s.bullet := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (bulletF p c) (residueF p c) _ _ (Or.inl (by change (7+q c)+(2)≤(11+q c); omega))]
  rw [Field.read_other_assign (bulletF p c) (markF p c) _ _ (Or.inl (by change (7+q c)+(2)≤(10+q c); omega))]
  rw [Field.read_other_assign (bulletF p c) (leaderF p c) _ _ (Or.inl (by change (7+q c)+(2)≤(9+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_leader {p c : Nat} (s : Site p c) :
    (leaderF p c).read (packPub s)=BitVec.ofBool s.leader := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (leaderF p c) (residueF p c) _ _ (Or.inl (by change (9+q c)+(1)≤(11+q c); omega))]
  rw [Field.read_other_assign (leaderF p c) (markF p c) _ _ (Or.inl (by change (9+q c)+(1)≤(10+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_mark {p c : Nat} (s : Site p c) :
    (markF p c).read (packPub s)=BitVec.ofBool s.mark := by
  unfold packPub
  dsimp only
  rw [Field.read_other_assign (markF p c) (residueF p c) _ _ (Or.inl (by change (10+q c)+(1)≤(11+q c); omega))]
  rw [Field.read_assign]

@[simp] theorem read_pack_residue {p c : Nat} (s : Site p c) :
    (residueF p c).read (packPub s)=BitVec.ofNat _ s.residue.val := by
  unfold packPub
  dsimp only
  rw [Field.read_assign]

private theorem source_raw {c : Nat} (s : Source (2*c)) :
    (BitVec.ofNat (q c) (sourceEncode s)).toNat=sourceEncode s := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (source_bound s)
    (by rw [show 2*(2*c)+3=4*c+3 by omega]; exact power_of_ell (4*c+3))

private theorem residue_section {p : Nat} (hp : 0<p) (s : Fin p) :
    residueDecode hp (BitVec.ofNat (ell p) s.val)=s := by
  have h : (BitVec.ofNat (ell p) s.val).toNat=s.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le s.isLt (power_of_ell p))]
  unfold residueDecode
  rw [dif_pos (by rw [h]; exact s.isLt)]
  exact Fin.ext h

@[simp] theorem read_pack {p c : Nat} (hp : 0<p) (s : Site p c) :
    readPub hp (packPub s)=s := by
  cases s with
  | mk residue mark leader bullet shield signal stock source rail =>
    simp only [readPub,read_pack_rail,read_pack_source,read_pack_stock,read_pack_signal,
      read_pack_shield,read_pack_bullet,read_pack_leader,read_pack_mark,read_pack_residue,
      source_raw,source_section,residue_section]
    cases mark <;> cases leader <;> cases bullet <;> cases shield <;> cases signal <;>
      cases stock <;> cases rail <;> rfl

theorem source_spare {Q k : Nat} (h : 2*Q+3≤k) : sourceDecode Q k=.off := by
  simp [sourceDecode,show k≠1 by omega,show k≠2 by omega,show ¬k<3+Q by omega,
    show ¬k<3+2*Q by omega]

theorem residue_spare {p : Nat} (hp : 0<p) (raw : BitVec (ell p)) (h : p≤raw.toNat) :
    (residueDecode hp raw).val=0 := by
  simp [residueDecode,Nat.not_lt_of_ge h]

/-- Last COUNT and first AWAIT are adjacent bytes, not interleaved. -/
example : sourceDecode 4 6 = .count 3 ∧ sourceDecode 4 7 = .await 0 ∧
    sourceDecode 4 10 = .await 3 ∧ sourceDecode 4 11 = .off := by decide

/-- A single deliberately dirty raw vector mixes all five spare
numeric fields with true one-bit flags. -/
example : readPub (p:=3) (c:=2) (by decide) (BitVec.allOnes 17) =
    ⟨0,true,true,.none,true,.zero,true,.off,.e⟩ := by decide

/-- The degenerate Q=0 extension includes no Count/Await bytes. -/
example : sourceDecode 0 0=.off ∧ sourceDecode 0 1=.i0 ∧
    sourceDecode 0 2=.i1 ∧ sourceDecode 0 3=.off := by decide

end L4.BStarPublicCodec
