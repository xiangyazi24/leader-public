import Leader.L4.Height.FenceFixedPathEnvelope

namespace L4.Height.FenceTwoLineMean
open FenceFixedPathEnvelope

theorem maxWait_append {n : Nat} (xs ys : List (Thru.Word n→Nat)) (w : Thru.Word n) :
    Thru.maxWait (xs++ys) w=max (Thru.maxWait xs w) (Thru.maxWait ys w) := by
  induction xs with
  | nil => simp [Thru.maxWait]
  | cons f xs ih => simp only [List.cons_append,Thru.maxWait,ih,Nat.max_assoc]

/-- A deterministic same-word certificate can give a single
witness path rather than compare directly against a list maximum. -/
theorem le_maxWait_of_mem {n : Nat} {xs : List (Thru.Word n→Nat)}
    {f : Thru.Word n→Nat} (mem : f∈xs) (w : Thru.Word n) :
    f w≤Thru.maxWait xs w := by
  induction xs with
  | nil => cases mem
  | cons g xs ih =>
    rcases List.mem_cons.mp mem with rfl|later
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

/-- The two line clocks and the actual FENCE wait are measured on
one raw word. No independence or extra conditioning is used to
combine the left and right dependency families. -/
theorem two_line_mean {n : Nat} (hl hr horizon : Nat) (hn : 0<n)
    (lpos : 0<hl) (rpos : 0<hr)
    (left right : List (List (Fin n))) (lne : left≠[]) (_rne : right≠[])
    (lcount : left.length≤2^(2*hl-1)) (rcount : right.length≤2^(2*hr-1))
    (llen : ∀ p,p∈left→p.length≤2*(2*hl-1))
    (rlen : ∀ p,p∈right→p.length≤2*(2*hr-1))
    (cl cr actual : Thru.Word n→Nat)
    (leftBound : ∀ w,cl w≤Thru.maxWait (left.map pathWait) w)
    (rightBound : ∀ w,cr w≤Thru.maxWait (right.map pathWait) w)
    (both : ∀ w,actual w≤max (cl w) (cr w))
    (censored : ∀ w,actual w≤horizon) :
    Thru.wordSum actual horizon≤92*n*max hl hr*n^horizon := by
  let H := max hl hr
  let k := 2^(2*H-1)
  have hH : 0<H := Nat.lt_of_lt_of_le lpos (Nat.le_max_left _ _)
  have rightH : 0<H := Nat.lt_of_lt_of_le rpos (Nat.le_max_right _ _)
  have lpow : 2^(2*hl-1)≤k := by
    apply Nat.pow_le_pow_right (by decide : 0<2)
    have := Nat.le_max_left hl hr
    dsimp only [H]
    omega
  have rpow : 2^(2*hr-1)≤k := by
    apply Nat.pow_le_pow_right (by decide : 0<2)
    have := Nat.le_max_right hl hr
    dsimp only [H]
    omega
  have count : (left++right).length≤2*H*H*k := by
    rw [List.length_append]
    calc
      _ ≤ k+k := Nat.add_le_add (Nat.le_trans lcount lpow) (Nat.le_trans rcount rpow)
      _ = 2*k := (Nat.two_mul k).symm
      _ ≤ 2*H*H*k := by
        have L : 1≤H := hH
        have R : 1≤H := rightH
        exact Nat.mul_le_mul_right _ (by
          have e := Nat.mul_le_mul (Nat.mul_le_mul_left 2 L) R
          simpa only [Nat.mul_one] using e)
  have bound : ∀ p,p∈left++right→p.length≤2*(2*H-1) := by
    intro p mem
    rcases List.mem_append.mp mem with L|R
    · have h := llen p L
      have q := Nat.le_max_left hl hr
      dsimp only [H]
      omega
    · have h := rlen p R
      have q := Nat.le_max_right hl hr
      dsimp only [H]
      omega
  refine fixed_paths_mean H horizon hn hH (left++right) (fun eq=>lne (List.append_eq_nil_iff.mp eq).1)
    count bound actual ?_
  intro w
  rw [List.map_append,maxWait_append]
  exact Nat.le_min.mpr ⟨Nat.le_trans (both w) (Nat.max_le.mpr
    ⟨Nat.le_trans (leftBound w) (Nat.le_max_left _ _),
     Nat.le_trans (rightBound w) (Nat.le_max_right _ _)⟩),censored w⟩

#print axioms maxWait_append
#print axioms le_maxWait_of_mem
#print axioms two_line_mean
end L4.Height.FenceTwoLineMean
