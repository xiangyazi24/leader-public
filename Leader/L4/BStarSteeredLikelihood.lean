import Leader.L4.BStarSteeringSupport
import Leader.L4.BStarRawBlockDrift

namespace L4.BStarSteeredLikelihood
open Height Classical
abbrev Word (n : Nat) := List (Fin n)

def emit {n : Nat} (choose : Word n → Fin n → Fin n) :
    Word n → Word n → Word n
  | _, [] => []
  | a, e::w => let k := choose a e; k::emit choose (a++[k]) w

def density {n : Nat} (multiplicity : Word n → Fin n → Nat) :
    Word n → Word n → Nat
  | _, [] => 1
  | a, e::w => multiplicity a e * density multiplicity (a++[e]) w

def decisions {n : Nat} (prescribed : Word n → Fin n → Nat) :
    Word n → Word n → Nat
  | _, [] => 0
  | a, e::w => prescribed a e + decisions prescribed (a++[e]) w

private theorem sum_swap {n m : Nat} (f : Fin n → Fin m → Nat) :
    (List.ofFn (fun e => (List.ofFn (f e)).sum)).sum =
    (List.ofFn (fun k => (List.ofFn (fun e => f e k)).sum)).sum := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero,List.sum_nil]
    have z := wordSum_const (n := m) 0 1
    simpa [wordSum] using z.symm
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons] -- outer left and inner right
    rw [ih (fun e k => f e.succ k),sum_ofFn_add]

def fiber {n : Nat} (choose : Word n → Fin n → Fin n) (a : Word n)
    (k : Fin n) : Nat :=
  (List.ofFn (fun e => if choose a e=k then 1 else 0)).sum

private theorem sum_single {n : Nat} (i : Fin n) (f : Fin n → Nat) :
      (List.ofFn (fun k => if i=k then f k else 0)).sum=f i := by
  induction n with
    | zero => exact i.elim0
    | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · have z := wordSum_const (n := n) 0 1
        simp only [wordSum,Nat.mul_zero] at z
        simpa [List.ofFn_succ,Ne.symm (Fin.succ_ne_zero _)] using
          (show f 0 + (List.ofFn (fun _ : Fin n => 0)).sum=f 0 by rw [z,Nat.add_zero])
      · simpa [List.ofFn_succ,Fin.succ_ne_zero,Fin.succ_inj] using ih j (fun k=>f k.succ)

private theorem sum_pullback {n : Nat} (choose : Word n → Fin n → Fin n)
    (a : Word n) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (choose a e))).sum =
    (List.ofFn (fun k => fiber choose a k*f k)).sum := by
  calc
    _ = (List.ofFn (fun e => (List.ofFn (fun k =>
      if choose a e=k then f k else 0)).sum)).sum :=
      sum_ofFn_eq _ _ (fun e => (sum_single (choose a e) f).symm)
    _ = (List.ofFn (fun k => (List.ofFn (fun e =>
      if choose a e=k then f k else 0)).sum)).sum := sum_swap _
    _ = _ := by
      apply sum_ofFn_eq
      intro k
      unfold fiber
      rw [Nat.mul_comm _ (f k),←sum_ofFn_mul_left]
      apply sum_ofFn_eq
      intro e
      split <;> simp_all

/-- Exact counting law. The steering decisions depend on the emitted
prefix, so the fiber weight belongs to the original raw word, not to
arbitrary hidden candidate histories. -/
theorem steered_mass {n : Nat} (choose : Word n → Fin n → Fin n)
    (a : Word n) (f : Word n → Nat) (t : Nat) :
    wordSum (fun w => f (emit choose a w)) t =
      wordSum (fun w => density (fiber choose) a w * f w) t := by
  induction t generalizing a f with
  | zero => simp [wordSum,emit,density]
  | succ t ih =>
    simp only [wordSum,emit]
    let F := fun k : Fin n => wordSum (fun v => f (k::emit choose (a++[k]) v)) t
    change (List.ofFn (fun e => F (choose a e))).sum = _
    rw [sum_pullback]
    apply sum_ofFn_eq
    intro k
    unfold F
    rw [ih (a++[k]) (fun v=>f (k::v)),←wordSum_mul_left]
    apply wordSum_congr_fun
    intro w
    simp only [density,Nat.mul_assoc]

theorem density_le {n : Nat} (choose : Word n → Fin n → Fin n)
    (cost : Word n → Fin n → Nat)
    (cap : ∀ a e, fiber choose a e ≤ 2^(cost a e)) (a w : Word n) :
    density (fiber choose) a w ≤ 2^(decisions cost a w) := by
  induction w generalizing a with
  | nil => simp [density,decisions]
  | cons e w ih =>
    simp only [density,decisions,Nat.pow_add]
    exact Nat.mul_le_mul (cap a e) (ih (a++[e]))

/-- Restore the actual raw law after any bounded number of steered
decisions. Count favorable prescribed decisions too by using a cost
indicator on the emitted word. -/
theorem restore {n : Nat} (choose : Word n → Fin n → Fin n)
    (cost : Word n → Fin n → Nat)
    (cap : ∀ a e, fiber choose a e ≤ 2^(cost a e))
    (a : Word n) (A : Word n → Prop) (t budget : Nat) :
    wordSum (fun w => BStarRawBlockDrift.massInd
      (fun v => A v ∧ decisions cost a v≤budget) (emit choose a w)) t ≤
      2^budget*wordSum (BStarRawBlockDrift.massInd A) t := by
  rw [steered_mass,←wordSum_mul_left]
  apply wordSum_mono
  intro w
  by_cases h : A w ∧ decisions cost a w≤budget
  · simp only [BStarRawBlockDrift.massInd,if_pos h,if_pos h.1,Nat.mul_one]
    exact Nat.le_trans (density_le choose cost cap a w) (Nat.pow_le_pow_right (by decide) h.2)
  · simp [BStarRawBlockDrift.massInd,h]

def chooseBy {n : Nat} (redirect : Word n → Fin n → Option (Fin n))
    (a : Word n) (e : Fin n) : Fin n := (redirect a e).getD e

/-- Charge a decision at the emitted prescribed side, even when the
candidate already picked that side. The opposite candidate is the
unique possible extra preimage under ADMIT-only steering. -/
noncomputable def prescribed {n : Nat} (redirect : Word n → Fin n → Option (Fin n))
    (a : Word n) (k : Fin n) : Nat :=
  if ∃ e, redirect a e=some k then 1 else 0

theorem supported_fiber {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (redirect : Word n → Fin n → Option (Fin n))
    (support : ∀ a, BStarSteeringSupport.Supported h hh (redirect a))
    (a : Word n) (k : Fin n) :
    fiber (chooseBy redirect) a k ≤ 2^(prescribed redirect a k) := by
  classical
  unfold prescribed fiber
  by_cases ex : ∃ e, redirect a e=some k
  · rw [if_pos ex]
    obtain ⟨j,J⟩ := ex
    have E (e : Fin n) (H : chooseBy redirect a e=k) : e=k ∨ e=j := by
      cases X : redirect a e with
      | none => exact .inl (by simpa [chooseBy,X] using H)
      | some b =>
        have same : b=k := by simpa [chooseBy,X] using H
        exact .inr (BStarSteeringSupport.partial_injective (support a) e j k (same ▸ X) J)
    have bound := sum_ofFn_le (fun e => if chooseBy redirect a e=k then 1 else 0)
      (fun e => (if k=e then 1 else 0)+(if j=e then 1 else 0)) (fun e => by
        by_cases H : chooseBy redirect a e=k
        · rcases E e H with rfl|rfl <;> simp [H]
        · simp [H])
    rw [sum_ofFn_add,sum_single,sum_single] at bound
    exact bound
  · rw [if_neg ex]
    have E (e : Fin n) (H : chooseBy redirect a e=k) : e=k := by
      cases X : redirect a e with
      | none => simpa [chooseBy,X] using H
      | some b =>
        have same : b=k := by simpa [chooseBy,X] using H
        exact (ex ⟨e,same ▸ X⟩).elim
    have bound := sum_ofFn_le (fun e => if chooseBy redirect a e=k then 1 else 0)
      (fun e => if k=e then 1 else 0) (fun e => by
        by_cases H : chooseBy redirect a e=k
        · have eq := E e H
          subst e
          simp [H]
        · simp [H])
    rw [sum_single] at bound
    exact bound

theorem restore_admit {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (redirect : Word n → Fin n → Option (Fin n))
    (support : ∀ a, BStarSteeringSupport.Supported h hh (redirect a))
    (a : Word n) (A : Word n → Prop) (t budget : Nat) :
    wordSum (fun w => BStarRawBlockDrift.massInd
      (fun v => A v ∧ decisions (prescribed redirect) a v≤budget)
      (emit (chooseBy redirect) a w)) t ≤
      2^budget*wordSum (BStarRawBlockDrift.massInd A) t :=
  restore (chooseBy redirect) (prescribed redirect) (supported_fiber h hh redirect support) a A t budget

/-- Close the likelihood half of the physical service proof: a steered
success mass of at least half after discarding over-budget tapes restores
the original raw block coefficient. No steered service or timing is assumed
except the displayed half-mass premise. -/
theorem raw_block_of_steered_half {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (redirect : Word n → Fin n → Option (Fin n))
    (support : ∀ a, BStarSteeringSupport.Supported h hh (redirect a))
    (a : Word n) (A : Word n → Prop) (t budget : Nat)
    (half : n^t ≤ 2 * wordSum (fun w => BStarRawBlockDrift.massInd
      (fun v => A v ∧ decisions (prescribed redirect) a v≤budget)
      (emit (chooseBy redirect) a w)) t) :
    n^t ≤ 2^(budget+1)*wordSum (BStarRawBlockDrift.massInd A) t := by
  have R := restore_admit h hh redirect support a A t budget
  refine Nat.le_trans half (Nat.le_trans (Nat.mul_le_mul_left 2 R) ?_)
  rw [Nat.pow_succ]
  exact Nat.le_of_eq (by ac_rfl)

/-- The paper's 3/16 time-failure and 1/8 decision-overflow bounds imply
half success under the steered law. Applies to the whole original raw block
and does not require the failure events to be independent or disjoint. -/
theorem raw_block_of_separate_failures {n : Nat} (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (redirect : Word n → Fin n → Option (Fin n))
    (support : ∀ a, BStarSteeringSupport.Supported h hh (redirect a))
    (a : Word n) (A : Word n → Prop) (t budget : Nat)
    (time : 16 * wordSum (fun w => BStarRawBlockDrift.massInd (fun v => ¬A v)
      (emit (chooseBy redirect) a w)) t ≤ 3*n^t)
    (overflow : 8 * wordSum (fun w => BStarRawBlockDrift.massInd
      (fun v => budget<decisions (prescribed redirect) a v)
      (emit (chooseBy redirect) a w)) t ≤ n^t) :
    n^t ≤ 2^(budget+1)*wordSum (BStarRawBlockDrift.massInd A) t := by
  let out := emit (chooseBy redirect) a
  let over := fun v => budget<decisions (prescribed redirect) a v
  let good := fun v => A v ∧ decisions (prescribed redirect) a v≤budget
  let ind := @BStarRawBlockDrift.massInd n
  have C := wordSum_mono (fun _ : Word n => 1)
    (fun w => ind good (out w) + (ind (fun v => ¬A v) (out w) + ind over (out w)))
    (fun w => by
      by_cases S : A (out w)
      · by_cases P : decisions (prescribed redirect) a (out w)≤budget
        · simp [ind,BStarRawBlockDrift.massInd,good,S,P]
        · have Q : over (out w) := Nat.lt_of_not_ge P
          simp [ind,BStarRawBlockDrift.massInd,good,S,P,if_pos Q]
      · simp [ind,BStarRawBlockDrift.massInd,S,good]) t
  rw [wordSum_const_one,wordSum_add_fun,wordSum_add_fun] at C
  change 16 * wordSum (fun w => ind (fun v => ¬A v) (out w)) t ≤ 3*n^t at time
  change 8 * wordSum (fun w => ind over (out w)) t ≤ n^t at overflow
  apply raw_block_of_steered_half h hh redirect support a A t budget
  change n^t ≤ 2 * wordSum (fun w => ind good (out w)) t
  omega

#print axioms raw_block_of_separate_failures
#print axioms raw_block_of_steered_half
#print axioms restore_admit
#print axioms steered_mass
#print axioms restore
end L4.BStarSteeredLikelihood
