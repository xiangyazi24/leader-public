import Leader.L4.ReportByteRows
import Leader.L4.ReportPulseAdapter

namespace L4.ReportPulseDecode
open AllSizeProtocol ReportByteRows ReportPulseWait

def get {w : Nat} (x : BitVec w) (i k : Nat) : Nat := (x.extractLsb' i k).toNat

def phase (p : Params) (x : BitVec p.w) : Phase :=
  let r:=get x (ell p.streak) 2
  if r=1 then .incoming else if r=2 then .outgoing else .empty

def count (p : Params) (x : BitVec p.w) : Nat := get x 0 (ell p.streak)

def state (p : Params) (x : BitVec p.w) (h : Bool) : ReportPulseWait.State := ⟨phase p x,count p x,h⟩

theorem state_congr (p : Params) (x y : BitVec p.w) (h : Bool)
    (I : ∀ i, i<tail p → x.getLsbD i=y.getLsbD i) :
    state p x h=state p y h := by
  have E (k b : Nat) (B : k+b≤tail p) : get x k b=get y k b := by
    unfold get
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi,I (k+i) (by omega)]
  have L := E (ell p.streak) 2 (by unfold tail; omega)
  have R := E 0 (ell p.streak) (by unfold tail; omega)
  simp [state,phase,count,L,R]

private def field (p : Params) (k b v : Nat) : Patch (workW p) :=
  ⟨(BitVec.allOnes b).setWidth (workW p) <<< k, (BitVec.ofNat b v).setWidth (workW p) <<< k⟩
private def widen (p : Params) (q : Patch (workW p)) : Patch p.w :=
  ⟨q.mask.setWidth p.w,q.value.setWidth p.w⟩

def standaloneApply (p : Params) (h : Bool) (s : Nat) (x : BitVec p.w) :=
  (widen p (pulse p h s x)).apply x

private theorem widen_comp (p : Params) (a b : Patch (workW p)) (x : BitVec p.w) :
    ((widen p (a.compose b)).apply x)=((widen p b).apply ((widen p a).apply x)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  by_cases L : i<workW p
  · simp only [widen,Patch.compose,Patch.apply,BitVec.getLsbD_or,
      BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_setWidth,I,L,
      decide_true,Bool.true_and]
    cases a.mask.getLsbD i <;> cases b.mask.getLsbD i <;> simp
  · have H : workW p≤i := by omega
    have P (q : Patch (workW p)) : (widen p q).mask.getLsbD i=false := by
      simp [widen,BitVec.getLsbD_of_ge _ i H]
    rw [Patch.hold _ _ _ (P _),Patch.hold _ _ _ (P _),Patch.hold _ _ _ (P _)]

private theorem get_write (p : Params) (k b v : Nat) (B : k+b≤workW p) (x : BitVec p.w) :
    get ((widen p (field p k b v)).apply x) k b = v%2^b := by
  have W := layout_size p
  have H : (((widen p (field p k b v)).apply x).extractLsb' k b)=BitVec.ofNat b v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have K : k+i<p.w := by omega
    have L : k+i<workW p := by omega
    have M : (widen p (field p k b v)).mask.getLsbD (k+i)=true := by
      simp [widen,field,K,L,I]
    simp only [BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and]
    rw [Patch.write _ _ _ M]
    simp [widen,field,K,L,I]
  simp [get,H]

private theorem get_frame (p : Params) (k b v j w : Nat) (x : BitVec p.w)
    (B : j+w≤k ∨ k+b≤j) :
    get ((widen p (field p k b v)).apply x) j w = get x j w := by
  unfold get
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have M : (widen p (field p k b v)).mask.getLsbD (j+i)=false := by
    rcases B with A|A
    · simp [widen,field,BitVec.getLsbD_shiftLeft,show ¬k≤j+i by omega]
    · have D : b≤j+i-k := by omega
      simp [widen,field,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_of_ge _ _ D]
  simp [I,Patch.hold _ _ _ M]

private theorem get_r_lt4 (p : Params) (x : BitVec p.w) : get x (ell p.streak) 2<4 :=
  (x.extractLsb' (ell p.streak) 2).isLt

private theorem pulse_eq (p : Params) (side : Nat) (x : BitVec p.w) :
    pulse p true side x =
    let w := ell p.streak
    let r := get x w 2
    let r := if r=3 then 0 else r
    let k := effective p.streak (count p x)
    if r=0 then field p w 2 side else if r=side then .empty _ else
      let paint := r==2 && k+1==p.streak
      let nr := if r==1 || paint then 0 else k+1
      let pad := (field p w 2 0).compose (field p 0 w nr)
      if paint then pad.compose (field p (w+2) 1
        ((publicationPair p x (publicationSelector p x)==0).toNat))
      else pad := by
  unfold pulse
  simp only [get,field,count,effective,beq_iff_eq,Bool.not_true]
  rfl

set_option linter.unusedSimpArgs false in
/-- Pulse alone computes precisely the counted normalized clock obtained
from the old bytes. The event bit counts idempotent paints as well. -/
theorem clock_eq (p : Params) (P : 0<p.streak) (x : BitVec p.w) (b h : Bool) :
    let s := if b then 2 else 1
    state p (standaloneApply p true s x) (h || paints p true s x) =
      side p.streak b (state p x h) := by
  let w := ell p.streak
  let r := get x w 2
  let k := count p x
  have R : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by have := get_r_lt4 p x; dsimp [r,w]; omega
  have W : w+2≤workW p := by unfold w workW grantBase sealBase sourceBase tail; omega
  have K : effective p.streak k <p.streak := effective_lt P
  have B : p.streak≤2^w := power_of_ell _
  have rf (z : BitVec p.w) (val : Nat) :
      get ((widen p (field p w 2 val)).apply z) w 2=val%4 := get_write p w 2 val W z
  have kf (z : BitVec p.w) (val : Nat) :
      count p ((widen p (field p 0 w val)).apply z)=val%2^w :=
    get_write p 0 w val (by omega) z
  have holdk (z : BitVec p.w) (val : Nat) :
      count p ((widen p (field p w 2 val)).apply z)=count p z :=
    get_frame p w 2 val 0 w z (.inl (by omega))
  have holdr (z : BitVec p.w) (val : Nat) :
      get ((widen p (field p 0 w val)).apply z) w 2=get z w 2 :=
    get_frame p 0 w val w 2 z (.inr (by omega))
  have holdkr (z : BitVec p.w) (val : Nat) :
      count p ((widen p (field p (w+2) 1 val)).apply z)=count p z :=
    get_frame p (w+2) 1 val 0 w z (.inl (by omega))
  have holdrr (z : BitVec p.w) (val : Nat) :
      get ((widen p (field p (w+2) 1 val)).apply z) w 2=get z w 2 :=
    get_frame p (w+2) 1 val w 2 z (.inl (by omega))
  have idle : ((widen p (.empty _)).apply x)=x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    apply Patch.hold
    simp [widen,Patch.empty]
  simp only
  unfold standaloneApply
  change state p ((widen p (pulse p true (if b then 2 else 1) x)).apply x) _ = _
  rw [pulse_eq]
  unfold paints
  change state p _ (h || (true && (if r==3 then 0 else r)==2 &&
    (if r==3 then 0 else r) != (if b then 2 else 1) && effective p.streak k+1==p.streak)) = _
  have phase_old : phase p x=(if r=1 then .incoming else if r=2 then .outgoing else .empty) := rfl
  unfold state
  rw [phase_old]
  change (⟨phase p _,count p _,_⟩ : ReportPulseWait.State) =
    side p.streak b ⟨(if r=1 then .incoming else if r=2 then .outgoing else .empty),k,h⟩
  unfold phase
  have erase : ∀ (val : Nat), val <2^w → val%2^w=val := fun _ V=>Nat.mod_eq_of_lt V
  have zero : 0%2^w=0 := Nat.zero_mod _
  dsimp [w] at rf kf holdr holdk holdkr holdrr erase zero
  rcases R with R|R|R|R <;> cases b <;>
    simp [show get x (ell p.streak) 2=r from rfl,show count p x=k from rfl, R,side,
      widen_comp,rf,kf,holdr,holdk,holdkr,holdrr,idle,zero]
  by_cases A : effective p.streak k+1=p.streak
  · simp [A,widen_comp,rf,kf,holdr,holdrr,holdkr,zero]
  · have N : effective p.streak k+1<2^w := by omega
    simp [A,widen_comp,rf,kf,holdr,erase _ N]

end L4.ReportPulseDecode
