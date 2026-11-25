import Leader.L4.Height.ResidualPotential
import Leader.L4.Height.FencePathPotential

namespace L4.Height.FenceComparison
open FencePathPotential

def dropMark {n : Nat} (e : Fin n) : List (Fin n) → List (Fin n)
  | [] => []
  | f::w => if e=f then w else f::w

def unpaid {n : Nat} (word tape : List (Fin n)) := tape.foldl (fun w e => dropMark e w) word

private theorem remaining_step {n : Nat} (p a : List (Fin n)) (e : Fin n) :
    unpaid p (a++[e]) = dropMark e (unpaid p a) := by simp [unpaid,List.foldl_append]

private theorem drop_le {n : Nat} (p : List (Fin n)) (e : Fin n) :
    (dropMark e p).length ≤ p.length := by
  cases p with
  | nil => simp [dropMark]
  | cons f w => by_cases eq : e=f <;> simp [dropMark,eq]

private theorem unpaid_le {n : Nat} (p a : List (Fin n)) : (unpaid p a).length ≤ p.length := by
  induction a generalizing p with
  | nil => exact Nat.le_refl _
  | cons e a ih => exact Nat.le_trans (ih (dropMark e p)) (drop_le p e)

def debts {n : Nat} (paths : List (List (Fin n))) :=
  paths.map (fun p => fun a => (unpaid p a).length)

def load {n : Nat} (paths : List (List (Fin n))) (tape : List (Fin n)) :=
  mass (debts paths) tape

theorem comparison_step {n : Nat} (paths : List (List (Fin n))) (a : List (Fin n)) :
    (∀ e, load paths (a++[e]) ≤ load paths a) ∧
    load paths a ≤ 2 * total (fun e => load paths a - load paths (a++[e])) := by
  apply mass_step
  · intro q h e
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp h
    dsimp only
    rw [remaining_step]
    exact drop_le _ _
  · intro q h pos
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp h
    dsimp only at pos ⊢
    cases hy : unpaid p a with
    | nil => simp [hy] at pos
    | cons e w => exact ⟨e,by simp [remaining_step,hy,dropMark]⟩

private theorem load_cap {n : Nat} (paths : List (List (Fin n))) (a : List (Fin n)) (D : Nat)
    (hlen : ∀ p ∈ paths, p.length ≤ D) : load paths a ≤ paths.length*2^D := by
  induction paths with
  | nil => simp [load,mass,debts]
  | cons p ps ih =>
    have bound := Nat.pow_le_pow_right (n:=2) (by decide)
      (Nat.le_trans (unpaid_le p a) (hlen p List.mem_cons_self))
    have small : weight (unpaid p a).length ≤ 2^D := by
      unfold weight
      split
      next => exact Nat.zero_le _
      next => exact bound
    change weight (unpaid p a).length + load ps a ≤ (ps.length+1)*2^D
    rw [Nat.succ_mul,Nat.add_comm (ps.length * 2^D)]
    exact Nat.add_le_add small (ih (fun q h => hlen q (List.mem_cons_of_mem _ h)))

/-- Counts for two full lines with at most H sites each. A word uses two
candidate occurrences for every crossing on a prerequisite path. -/
theorem capacity {n H : Nat} (hh : 0<H) (paths : List (List (Fin n))) (a : List (Fin n))
    (count : paths.length ≤ 2*H^2*2^(2*H+1))
    (hlen : ∀ p ∈ paths, p.length ≤ 4*H+2) : load paths a < 2^(16*H-1) := by
  have hp : H ≤ 2^H := Nat.le_of_lt (Nat.lt_two_pow_self)
  have sq := Nat.mul_le_mul hp hp
  calc
    load paths a ≤ (2*H^2*2^(2*H+1))*2^(4*H+2) :=
      Nat.le_trans (load_cap paths a _ hlen) (Nat.mul_le_mul_right _ count)
    _ ≤ (2*((2^H)*(2^H))*2^(2*H+1))*2^(4*H+2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
        (by simpa only [Nat.pow_two] using sq)))
    _ = 2^(1+H+H+(2*H+1)+(4*H+2)) := by
      simp only [Nat.pow_add,Nat.pow_one]
      ac_rfl
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

def mark {n : Nat} (a : List (Fin n)) (e : Fin n) := a++[e]

private theorem mark_word {n : Nat} (a w : List (Fin n)) :
    runWord mark a w = a++w := by
  induction w generalizing a with
  | nil => simp [runWord]
  | cons e w ih =>
    change runWord mark (a++[e]) w = _
    rw [ih,List.append_assoc,List.singleton_append]

private theorem clear_stays {n : Nat} (paths : List (List (Fin n))) (a v : List (Fin n))
    (h : load paths a=0) : load paths (a++v)=0 := by
  induction v generalizing a with
  | nil => simpa using h
  | cons e v ih =>
    have weak := (comparison_step paths a).1 e
    have zero : load paths (a++[e])=0 := by omega
    simpa only [List.append_assoc,List.singleton_append] using ih (a++[e]) zero

private theorem reserve_empty (n b : Nat) : reserve n b 0=0 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [reserve,band,ih]

/-- The stop is exhaustion of all the prescribed path words on one common tape. -/
def comparisonResidual {n H : Nat} (hh : 0<H) (paths : List (List (Fin n)))
    (count : paths.length ≤ 2*H^2*2^(2*H+1))
    (hlen : ∀ p ∈ paths, p.length ≤ 4*H+2) :
    ResidualPotentialData (S:=List (Fin n)) (n:=n) where
  next := mark
  Q := fun _ => True
  P := fun a => load paths a=0
  inFence := fun a => load paths a≠0
  Rserial := fun _ => 0
  EF := fun a => reserve n (16*H) (load paths a)
  K := n
  hweight := Nat.le_refl _
  closed := fun _ _ _ => True.intro
  hserial := fun _ _ off outside => False.elim (outside off)
  hfence := fun a _ off _ => reserve_drift _ (Nat.pos_of_ne_zero off)
    (capacity hh paths a count hlen) (comparison_step paths a).1 (comparison_step paths a).2
  otherSerial := fun _ _ _ off outside _ => False.elim (outside off)
  otherFence := fun _ _ _ _ _ _ => Nat.le_refl _
  entryEscrow := fun _ _ _ off outside _ => False.elim (outside off)
  exitEscrow := by
    intro a e _ _ _ out
    change ¬ load paths (mark a e)≠0 at out
    have z := Classical.not_not.mp out
    exact ⟨Nat.le_refl _,by rw [z,reserve_empty]⟩
  oneFence := by
    intro y before gap tail _ _ exited _ active
    change ¬ load paths (runWord mark y (before++gap))≠0 at exited
    have z := Classical.not_not.mp exited
    apply active
    simp only [mark_word] at z ⊢
    simpa only [List.append_assoc] using clear_stays paths _ tail z

theorem candidate_clearance_cost {n H : Nat} (hh : 0<H)
    (paths : List (List (Fin n))) (count : paths.length ≤ 2*H^2*2^(2*H+1))
    (hlen : ∀ p ∈ paths, p.length ≤ 4*H+2) (a : List (Fin n)) :
    IIDExpectedHittingTimeAtMost mark (fun v => load paths v=0) a (128*n*H) := by
  let D := comparisonResidual hh paths count hlen
  apply residual_expected_le D a True.intro
  have h := reserve_cap n (16*H) (load paths a)
  change n*0 + reserve n (16*H) (load paths a) ≤ _
  rw [Nat.mul_zero,Nat.zero_add]
  calc
    _ ≤ _ := h
    _ = (16*8)*n*H := by ac_rfl
    _ = _ := rfl

end L4.Height.FenceComparison
