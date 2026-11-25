import Leader.L4.ShortDirtySweep
import Leader.L4.ShortResetWatch
import Leader.Core.PredictableTwoTargetFiniteTree

namespace L4.ShortForwardRank
open MISByteCodec ShortResetCycle PhysicalCustody ShortResetForwardH2 ShortResetChart
open ShortResetWatch FiniteUniformStoppingTree

/-- The remaining observations of a decoded ADMIT token. -/
def raceDebt (t : Token) : Nat :=
  if t.opcode = 2 ∧ t.fault = false then
    if t.race = 1 then 2 else if t.race = 2 ∨ t.race = 3 then 1 else 0
  else 0

theorem raceDebt_bound (t : Token) : raceDebt t≤2 := by
  unfold raceDebt
  split
  · split
    · decide
    · split <;> decide
  · decide

theorem raceDebt_obs (t u : Token) (ot : t.opcode=2) (ou : u.opcode=2)
    (ft : t.fault=false) (fu : u.fault=false)
    (step : (t.race=1 ∧ (u.race=2 ∨ u.race=3)) ∨
      ((t.race=2 ∨ t.race=3) ∧ (u.race=4 ∨ u.race=5))) :
    raceDebt u < raceDebt t := by
  rcases step with ⟨r,a|a⟩ | ⟨a|a,b|b⟩ <;> simp [raceDebt, *]

/-- Four units per remaining hop dominate the possible two observations
newly assigned at the next position. -/
def localScore (L i : Nat) (t : Token) : Nat :=
  if t.tag=2 then 4*(L-i)+raceDebt t else 0

theorem localScore_nonforward {L i : Nat} {t : Token} (H : t.tag≠2) :
    localScore L i t=0 := if_neg H

theorem localScore_forward_pos {L i : Nat} {t : Token} (H : t.tag=2) (I : i<L) :
    0<localScore L i t := by simp only [localScore,H,if_true]; omega

theorem localScore_bound (L i : Nat) (t : Token) :
    localScore L i t≤4*L+2 := by
  have D := raceDebt_bound t
  unfold localScore
  split <;> omega

def score {L : Nat} (ts : Fin L → Token) : Nat :=
  (List.ofFn (fun i => localScore L i.val (ts i))).sum

/-- Depends only on the observed chart bytes and its frozen headers. -/
def byteScore {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (b : Fin C.L → BitVec 96) : Nat :=
  score (fun i => oldK (h (nextAt C.root i.val)) (b i) (C.route.port i.val))

def physicalScore {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) : Nat := byteScore C (projection C x)

theorem physicalScore_eq {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (head : ∀ q, ShortResetMIS1Ring.header x q=h q) :
    physicalScore C x = score (fun i : Fin C.L => slot C.route x i.val) := by
  unfold physicalScore byteScore score
  apply ofFn_sum_eq
  intro i
  simp only [slot, projection, head]
  rfl

theorem score_bound {L : Nat} (ts : Fin L → Token) :
    score ts ≤ L*(4*L+2) := by
  unfold score
  rw [←ofFn_sum_const]
  exact ofFn_sum_le _ _ (fun i => localScore_bound L i.val (ts i))

theorem byteScore_bound {n : Nat} {h : Fin n → Bool} (C : Chart h)
    (b : Fin C.L → BitVec 96) (L : C.L≤9) : byteScore C b≤342 := by
  have P := score_bound (fun i : Fin C.L =>
    oldK (h (nextAt C.root i.val)) (b i) (C.route.port i.val))
  exact Nat.le_trans P (Nat.mul_le_mul L (show 4*C.L+2≤38 by omega))

theorem sum_split_one {L : Nat} (f : Fin L → Nat) (a : Fin L) :
    (List.ofFn f).sum = f a + (List.ofFn (fun i => if i=a then 0 else f i)).sum := by
  let p : Fin L → Nat := fun i => if i=a then f a else 0
  have H : ∀ i, f i = p i + (if i=a then 0 else f i) := by
    intro i
    by_cases E : i=a
    · subst i; simp [p]
    · simp [p,E]
  rw [ofFn_sum_eq f _ H,ofFn_sum_add]
  have P : (List.ofFn p).sum = f a := by
    have X := PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const a p 0
      (fun e H => if_neg H)
    simpa [p] using X
  rw [P]

theorem sum_split_two {L : Nat} (f : Fin L → Nat) (a b : Fin L) (AB : a≠b) :
    (List.ofFn f).sum = f a + f b +
      (List.ofFn (fun i => if i=a then 0 else if i=b then 0 else f i)).sum := by
  let p : Fin L → Nat := fun i => if i=a then f a else if i=b then f b else 0
  have H : ∀ i, f i = p i + (if i=a then 0 else if i=b then 0 else f i) := by
    intro i
    by_cases E : i=a
    · subst i; simp [p]
    by_cases F : i=b
    · subst i; simp [p,E]
    · simp [p,E,F]
  rw [ofFn_sum_eq f _ H,ofFn_sum_add]
  have P : (List.ofFn p).sum = f a + f b := by
    have X := PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const a b p 0 AB
      (fun e H J => by simp [p,H,J])
    simpa [p,Ne.symm AB] using X
  rw [P]

theorem score_zero_iff {L : Nat} (ts : Fin L → Token) :
    score ts=0 ↔ ∀ i, (ts i).tag≠2 := by
  constructor
  · intro H i T
    have E := sum_split_one (fun j : Fin L => localScore L j.val (ts j)) i
    have P := localScore_forward_pos T i.isLt
    unfold score at H
    omega
  · intro H
    unfold score
    rw [ofFn_sum_eq _ (fun _ => 0) (fun i => localScore_nonforward (H i))]
    simp [ofFn_sum_const]

theorem physicalScore_zero_iff {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (head : ∀ q, ShortResetMIS1Ring.header x q=h q) :
    physicalScore C x=0 ↔ ShortDirtySweep.NoForward C x := by
  rw [physicalScore_eq C x head, score_zero_iff]
  constructor
  · intro H j J
    exact H ⟨j,J⟩
  · intro H j
    exact H j.val j.isLt

theorem score_lt_of_one {L : Nat} {ts us : Fin L → Token} (a : Fin L)
    (lt : localScore L a.val (us a) < localScore L a.val (ts a))
    (other : ∀ i, i≠a → localScore L i.val (us i)=localScore L i.val (ts i)) :
    score us<score ts := by
  unfold score
  rw [sum_split_one (fun i : Fin L => localScore L i.val (us i)) a,
    sum_split_one (fun i : Fin L => localScore L i.val (ts i)) a]
  have E := ofFn_sum_eq
    (fun i => if i=a then 0 else localScore L i.val (us i))
    (fun i => if i=a then 0 else localScore L i.val (ts i)) (fun i => by
      by_cases H : i=a
      · simp [H]
      · simp [H,other i H])
  omega

theorem score_lt_of_two {L : Nat} {ts us : Fin L → Token} (a b : Fin L) (AB : a≠b)
    (lt : localScore L a.val (us a)+localScore L b.val (us b) <
       localScore L a.val (ts a)+localScore L b.val (ts b))
    (other : ∀ i, i≠a → i≠b → localScore L i.val (us i)=localScore L i.val (ts i)) :
    score us<score ts := by
  unfold score
  rw [sum_split_two (fun i : Fin L => localScore L i.val (us i)) a b AB,
    sum_split_two (fun i : Fin L => localScore L i.val (ts i)) a b AB]
  have E := ofFn_sum_eq
    (fun i => if i=a then 0 else if i=b then 0 else localScore L i.val (us i))
    (fun i => if i=a then 0 else if i=b then 0 else localScore L i.val (ts i)) (fun i => by
      by_cases H : i=a
      · simp [H]
      by_cases J : i=b
      · simp [J]
      · simp [H,J,other i H J])
  omega

/-- Arrivals may overwrite arbitrary debt and independently gain a legal
two-unit parked debt. -/
theorem transport_lt {L : Nat} {ts us : Fin L → Token} (a b : Fin L)
    (AB : b.val = a.val+1)
    (oldF : (ts a).tag=2) (leftNonF : (us a).tag≠2)
    (other : ∀ i, i≠a → i≠b → localScore L i.val (us i)=localScore L i.val (ts i)) :
    score us<score ts := by
  apply score_lt_of_two a b (by intro H; subst b; omega) _ other
  have H : localScore L b.val (us b) ≤ 4*(L-b.val)+2 := by
    have R := raceDebt_bound (us b)
    unfold localScore
    split <;> omega
  have F : 4*(L-a.val) ≤ localScore L a.val (ts a) := by simp [localScore,oldF]
  rw [localScore_nonforward leftNonF]
  have J := b.isLt
  omega

theorem turn_lt {L : Nat} {ts us : Fin L → Token} (a : Fin L)
    (oldF : (ts a).tag=2) (newNonF : (us a).tag≠2)
    (other : ∀ i, i≠a → localScore L i.val (us i)=localScore L i.val (ts i)) :
    score us<score ts := by
  apply score_lt_of_one a _ other
  rw [localScore_nonforward newNonF]
  exact localScore_forward_pos oldF a.isLt

theorem observe_lt {L : Nat} {ts us : Fin L → Token} (a b : Fin L) (AB : a≠b)
    (oldF : (ts a).tag=2) (newF : (us a).tag=2)
    (debt : raceDebt (us a)<raceDebt (ts a))
    (conserve : localScore L b.val (us b)=localScore L b.val (ts b))
    (other : ∀ i, i≠a → i≠b → localScore L i.val (us i)=localScore L i.val (ts i)) :
    score us<score ts := by
  apply score_lt_of_two a b AB _ other
  rw [conserve]
  simp only [localScore,newF,oldF,if_true]
  omega

end L4.ShortForwardRank
