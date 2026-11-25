import Leader.L4.Statement
import Leader.Core.FiniteUniformStoppingTree

namespace L4.ReportPulseWait

inductive Phase where
  | empty | incoming | outgoing
  deriving DecidableEq

/-- Normalized race read; invalid stored counts are kept until a round ends. -/
structure State where
  phase : Phase
  count : Nat
  hit : Bool
  deriving DecidableEq

def effective (J k : Nat) : Nat := if k<J then k else 0

def side (J : Nat) (outgoing : Bool) (x : State) : State :=
  match x.phase with
  | .empty => {x with phase := if outgoing then .outgoing else .incoming}
  | .incoming => if outgoing then ⟨.empty,0,x.hit⟩ else x
  | .outgoing =>
    if outgoing then x
    else if effective J x.count+1=J then ⟨.empty,0,true⟩
    else ⟨.empty,effective J x.count+1,x.hit⟩

def step {n : Nat} (J : Nat) (a b e : Fin n) (x : State) : State :=
  if e=a then side J false x else if e=b then side J true x else x

def potential0 (n J k : Nat) : Nat := 3*n*(2^J-2^k)

def potential (n J : Nat) (x : State) : Nat :=
  if x.hit then 0 else
  let k:=effective J x.count
  match x.phase with
  | .empty => potential0 n J k
  | .incoming => n+potential0 n J 0
  | .outgoing => n+potential0 n J (k+1)

theorem effective_lt {J k : Nat} (P : 0<J) : effective J k<J := by
  unfold effective
  split <;> omega

theorem potential0_double {n J k : Nat} (K : k<J) :
    potential0 n J k + potential0 n J k =
      3*n + potential0 n J 0 + potential0 n J (k+1) := by
  have P : 2^(k+1) ≤ 2^J := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.pow_succ] at P
  unfold potential0
  rw [Nat.pow_zero,Nat.pow_succ,←Nat.mul_add]
  rw [show 3*n+3*n*(2^J-1)+3*n*(2^J-2^k*2)=3*n*(1+(2^J-1)+(2^J-2^k*2)) by rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]]
  congr 1
  have A : 2^k*2=2^k+2^k := by omega
  rw [A] at P ⊢
  have Q : 1 ≤ 2^J := Nat.pow_pos (by decide)
  omega

theorem drift_two {n J : Nat} (P : 0<J) (x : State) (H : x.hit=false) :
    n + potential n J (side J false x) + potential n J (side J true x)
      ≤ potential n J x + potential n J x := by
  rcases x with ⟨ph,k,h⟩
  change h=false at H
  subst h
  cases ph with
  | empty =>
    simp [side,potential]
    have V := potential0_double (n:=n) (effective_lt (k:=k) P)
    rw [show 3*n=n+n+n by omega] at V
    omega
  | incoming =>
    simp [side,potential,effective,P]
    omega
  | outgoing =>
    have L := effective_lt (k:=k) P
    unfold side
    simp only [Bool.false_eq_true,if_false,if_true]
    split
    · rename_i E
      simp [potential,E,potential0]
    · rename_i E
      simp only [potential,Bool.false_eq_true,if_false]
      have F : effective J (effective J k+1)=effective J k+1 := by
        unfold effective
        by_cases K : k<J
        · rw [if_pos K,if_pos (by unfold effective at E L; simp only [if_pos K] at E L; omega)]
        · rw [if_neg K,if_pos (by unfold effective at E L; simp only [if_neg K] at E L; omega)]
      rw [F]
      omega

private theorem sum_two {n : Nat} (a b : Fin n) (D : a≠b) (u v w : Nat)
    (xs : List (Fin n)) :
    (xs.map (fun e => if e=a then u else if e=b then v else w)).sum =
      xs.count a*u+xs.count b*v+(xs.length-xs.count a-xs.count b)*w := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    have S : xs.count a + xs.count b ≤ xs.length := by
      clear ih
      induction xs with
      | nil => simp
      | cons f xs ih =>
        by_cases Fa : f=a
        · subst f; simp [D]; omega
        · by_cases Fb : f=b
          · subst f; simp [D.symm]; omega
          · simp [Fa,Fb]; omega
    by_cases A : e=a
    · subst e; simp [D,ih,Nat.add_mul]; omega
    · by_cases B : e=b
      · subst e
        simp [D.symm,ih,Nat.add_mul]
        rw [show xs.length+1-xs.count a-(xs.count b+1)=xs.length-xs.count a-xs.count b by omega]
        omega
      · simp [A,B,ih]
        rw [show xs.length+1-xs.count a-xs.count b=xs.length-xs.count a-xs.count b+1 by omega,
          Nat.add_mul,Nat.one_mul]
        omega

theorem drift {n J : Nat} (P : 0<J) (a b : Fin n) (D : a≠b) (x : State)
    (H : x.hit=false) :
    n+(List.ofFn (fun e => potential n J (step J a b e x))).sum ≤ n*potential n J x := by
  rw [show List.ofFn (fun e => potential n J (step J a b e x)) =
      (List.finRange n).map (fun e => if e=a then potential n J (side J false x)
         else if e=b then potential n J (side J true x) else potential n J x) by
       rw [List.finRange,List.map_ofFn]
       congr 1
       funext e
       by_cases A : e=a <;> by_cases B : e=b <;> simp [step,A,B,D.symm]]
  rw [sum_two a b D]
  rw [(List.nodup_finRange n).count (a:=a),(List.nodup_finRange n).count (a:=b)]
  simp only [List.mem_finRange,if_true,Nat.one_mul,List.length_finRange]
  have N : 2≤n := by
    have A:=a.isLt
    have B:=b.isLt
    by_cases H : 2≤n
    · exact H
    · exact False.elim (D (Fin.ext (by omega)))
  have K : 2+(n-1-1)=n := by omega
  have E := congrArg (fun i : Nat => i*potential n J x) K
  rw [Nat.add_mul,show 2*potential n J x = potential n J x+potential n J x by omega] at E
  have L := drift_two P x H (n:=n)
  omega

theorem truncated {n J : Nat} (P : 0<J) (a b : Fin n) (D : a≠b) (x : State) (t : Nat) :
    L4.iidHitCost (fun y e => step J a b e y) (fun y => y.hit=true) t x ≤
      potential n J x*n^t := by
  classical
  induction t generalizing x with
  | zero => simp [L4.iidHitCost]
  | succ t ih =>
    by_cases H : x.hit=true
    · simp [L4.iidHitCost,H]
    · rw [L4.iidHitCost,if_neg H]
      have L := FiniteUniformStoppingTree.ofFn_sum_le
        (fun e => L4.iidHitCost (fun y e => step J a b e y) (fun y => y.hit=true) t (step J a b e x))
        (fun e => n^t*potential n J (step J a b e x))
        (fun e => by rw [Nat.mul_comm]; exact ih _)
      rw [FiniteUniformStoppingTree.ofFn_sum_mul_left] at L
      rw [Nat.pow_succ,show potential n J x*(n^t*n)=n^t*(n*potential n J x) by ac_rfl]
      refine Nat.le_trans (Nat.add_le_add_left L _) ?_
      rw [←Nat.mul_add]
      exact Nat.mul_le_mul_left _ (drift P a b D x (Bool.eq_false_iff.mpr H))

theorem arbitrary_clock_mean {n J : Nat} (P : 0<J) (a b : Fin n) (D : a≠b) (x : State) :
    L4.IIDExpectedHittingTimeAtMost (fun y e => step J a b e y) (fun y => y.hit=true)
      x (4*n*2^J) := by
  intro t
  refine Nat.le_trans (truncated P a b D x t) (Nat.mul_le_mul_right _ ?_)
  have F (k : Nat) : potential0 n J k ≤ 3*n*2^J :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have Q : 1 ≤ 2^J := Nat.pow_pos (by omega)
  have E : n≤n*2^J := by simpa using Nat.mul_le_mul_left n Q
  have R : 4*n*2^J = 3*n*2^J + n*2^J := by rw [show 4*n=3*n+n by omega,Nat.add_mul]
  rw [R]
  rcases x with ⟨ph,k,h⟩
  cases h <;> cases ph <;> simp [potential] <;> have := F 0 <;> have := F (effective J k) <;>
    have := F (effective J k+1) <;> omega

#print axioms drift_two
#print axioms arbitrary_clock_mean
end L4.ReportPulseWait
