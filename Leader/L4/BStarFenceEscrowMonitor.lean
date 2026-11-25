import Leader.L4.BStarFenceSweepClock
import Leader.L4.Height.ResidualFencePhase

namespace L4.BStarFenceEscrowMonitor
open L4.Height ResidualFencePhase BStarFenceSweepClock BStarFenceShadow

variable {S : Type} {n l r : Nat}

structure State (S : Type) where
  physical : S
  phase : Phase

def eligible (pc : S→Nat) (ended : S→Bool) (s : S) : Bool :=
  pc s == 11 && !ended s

noncomputable def phaseUpdate (active entry ended : S→Bool) (phys : S→Two (l:=l) (r:=r))
    (p : Phase) (s : S) : Phase := by
  classical
  exact match p with
  | .spent => .spent
  | .active => if Done active phys s ∨ ended s=true then .spent else .active
  | .reserve => if ended s then .spent else
      if entry s then if Done active phys s then .spent else .active
      else .reserve

noncomputable def lift (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (x : State S) (e : Fin n) : State S :=
  let y := next x.physical e
  ⟨y,phaseUpdate active entry ended phys x.phase y⟩

def Hit (ended : S→Bool) (x : State S) : Prop :=
  x.phase≠.active ∨ ended x.physical=true

def Well (active ended : S→Bool) (phys : S→Two (l:=l) (r:=r)) (x : State S) : Prop :=
  x.phase=.active → ¬Done active phys x.physical ∧ ended x.physical=false

theorem active_no_refund (active entry ended : S→Bool) (phys : S→Two (l:=l) (r:=r))
    (s : S) : phaseUpdate active entry ended phys .active s≠.reserve := by
  classical
  by_cases H : Done active phys s ∨ ended s=true <;> simp [phaseUpdate,H]

theorem spent_sticky (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (x : State S) (e : Fin n)
    (H : x.phase=.spent) : (lift next active entry ended phys x e).phase=.spent := by
  simp [lift,H,phaseUpdate]

theorem lift_well (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (x : State S) (e : Fin n) :
    Well active ended phys (lift next active entry ended phys x e) := by
  classical
  let y := next x.physical e
  change phaseUpdate active entry ended phys x.phase y=.active →
    ¬Done active phys y ∧ ended y=false
  cases P : x.phase with
  | spent => simp [phaseUpdate]
  | active =>
    by_cases D : Done active phys y
    · simp [phaseUpdate,D]
    · cases E : ended y <;> simp [phaseUpdate,D,E]
  | reserve =>
    cases E : ended y
    · by_cases D : Done active phys y <;> cases N : entry y <;> simp [phaseUpdate,E,D,N]
    · simp [phaseUpdate,E]

theorem lift_run (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (x : State S) (w : Thru.Word n) :
    (Thru.runWord (lift next active entry ended phys) x w).physical=
      Thru.runWord next x.physical w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih (lift next active entry ended phys x e)

theorem lift_emitted (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (emit : S→Fin n→Fin n)
    (x : State S) (w : Thru.Word n) :
    emitted (lift next active entry ended phys) (fun z e=>emit z.physical e) x w=
      emitted next emit x.physical w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    exact congrArg (List.cons (emit x.physical e)) (ih (lift next active entry ended phys x e))

/-- From an already armed monitor, the recorded stop is exactly
physical emptiness, phase exit, or attempt termination. No assumption
about the future of an ended attempt is needed. -/
theorem armed_wait (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r))
    (x : State S) (w : Thru.Word n) (H : x.phase=.active)
    (W : Well active ended phys x) :
    Thru.wait (lift next active entry ended phys) (Hit ended) x w =
      Thru.wait next (fun y=>Done active phys y ∨ ended y=true) x.physical w := by
  classical
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have notHit : ¬Hit ended x := by
      intro Q
      exact Q.elim (fun e=>e H) (fun E=>by rw [(W H).2] at E; contradiction)
    have notDone : ¬(Done active phys x.physical ∨ ended x.physical=true) := by
      intro Q
      exact Q.elim (W H).1 (fun E=>by rw [(W H).2] at E; contradiction)
    rw [Thru.wait_cons_of_not _ _ _ notHit,Thru.wait_cons_of_not next (fun y=>Done active phys y ∨ ended y=true) _ notDone]
    let y := next x.physical e
    let z := lift next active entry ended phys x e
    change Nat.succ (Thru.wait _ _ z w)=Nat.succ (Thru.wait _ _ y w)
    by_cases Q : Done active phys y ∨ ended y=true
    · have P : z.phase=.spent := by simp [z,lift,H,phaseUpdate,y,Q]
      have hit : Hit ended z := .inl (by rw [P]; decide)
      rw [Thru.wait_of_hit _ _ _ hit, Thru.wait_of_hit next (fun y=>Done active phys y ∨ ended y=true) _ Q]
    · have P : z.phase=.active := by simp [z,lift,H,phaseUpdate,y,Q]
      exact congrArg Nat.succ (ih z P (lift_well next active entry ended phys x e))

/-- Physical opcode-11 exit already includes attempt termination
when the supplied activity test is the literal conjunction. -/
theorem eligible_done {x : S} (pc : S→Nat) (ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) :
    (Done (eligible pc ended) phys x ∨ ended x=true) ↔
      (pc x≠11 ∨ ended x=true ∨ Empty (phys x)) := by
  unfold Done eligible
  cases ended x <;> by_cases P : pc x=11 <;> simp [P]

theorem reserve_arms (active entry ended : S→Bool) (phys : S→Two (l:=l) (r:=r))
    (s : S) :
    phaseUpdate active entry ended phys .reserve s=.active ↔
      ended s=false ∧ entry s=true ∧ ¬Done active phys s := by
  classical
  cases E : ended s <;> cases A : entry s <;> by_cases D : Done active phys s <;>
    simp [phaseUpdate,E,A,D]

theorem spent_word (next : S→Fin n→S) (active entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (s : State S) (w : Thru.Word n) (spent : s.phase=.spent) :
    (Thru.runWord (lift next active entry ended phys) s w).phase=.spent := by
  induction w generalizing s with
  | nil => exact spent
  | cons e w ih => exact ih _ (spent_sticky next active entry ended phys s e spent)

theorem cost_eq_wordSum (next : S→Fin n→S) (D : S→Prop) (x : S) (t : Nat) :
    Height.iidHitCost next D t x = Thru.wordSum (Thru.wait next D x) t := by
  classical
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : D x
    · rw [Height.iidHitCost_of_target _ _ _ H]
      have T : Thru.wordSum (Thru.wait next D x) (t+1)=
          Thru.wordSum (n:=n) (fun _=>0) (t+1) :=
        Thru.wordSum_congr _ _ (fun w=>Thru.wait_of_hit next D x H w) _
      rw [T,Thru.wordSum_const,Nat.zero_mul]
    · simp only [Height.iidHitCost,if_neg H,Thru.wordSum]
      have E (e : Fin n) : Thru.wordSum (fun w=>Thru.wait next D x (e::w)) t =
          1*n^t + Height.iidHitCost next D t (next x e) := by
        have eq : Thru.wordSum (fun w=>Thru.wait next D x (e::w)) t =
            Thru.wordSum (fun w=>1+Thru.wait next D (next x e) w) t :=
          Thru.wordSum_congr _ _ (fun w=>by rw [Thru.wait_cons_of_not next D x H]; omega) _
        rw [eq,Thru.wordSum_add_fun,Thru.wordSum_const,←ih]
      have T : (List.ofFn (fun e : Fin n=>Thru.wordSum
          (fun w=>Thru.wait next D x (e::w)) t)).sum =
          (List.ofFn (fun e : Fin n=>1*n^t + Height.iidHitCost next D t (next x e))).sum :=
        congrArg (fun f : Fin n→Nat=>(List.ofFn f).sum) (funext E)
      rw [T,sum_ofFn_add,sum_ofFn_const]
      simp [Nat.pow_succ,Nat.mul_comm]

theorem armed_wordSum (next : S→Fin n→S) (pc : S→Nat) (entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (s : State S) (t : Nat)
    (H : s.phase=.active) (W : Well (eligible pc ended) ended phys s) :
    Height.iidHitCost (lift next (eligible pc ended) entry ended phys) (Hit ended) t s =
      Thru.wordSum (actual next (eligible pc ended) phys s.physical t) t := by
  rw [cost_eq_wordSum]
  apply Thru.wordSum_congr_length
  intro w len
  rw [armed_wait _ _ _ _ _ _ w H W]
  have eq : (fun y=>Done (eligible pc ended) phys y ∨ ended y=true)=
      Done (eligible pc ended) phys := by
    funext y
    apply propext
    constructor
    · intro A
      exact A.elim id (fun F=>.inl (by simp [eligible,F]))
    · exact Or.inl
  rw [eq]
  unfold actual
  rw [Nat.min_eq_right (by rw [←len]; exact Thru.wait_le_length next _ _ _)]

/-- Instantiate the residual escrow from the physical censored mean.
The history component is initialized at the start of the tracked
attempt; this proof does not identify the concrete entry predicate. -/
theorem exists_actual_escrow (hn : 0<n)
    (next : S→Fin n→S) (pc : S→Nat) (entry ended : S→Bool)
    (phys : S→Two (l:=l) (r:=r)) (Q : S→Prop) (F : Nat)
    (closed : ∀ y e,Q y→Q (next y e))
    (mean : ∀ y,Q y→¬Done (eligible pc ended) phys y→∀ t,
      Thru.wordSum (actual next (eligible pc ended) phys y t) t≤F*n^t) :
    let N := lift next (eligible pc ended) entry ended phys
    let Q' := fun s=>Q s.physical ∧ Well (eligible pc ended) ended phys s
    let E' := fun s : State S=>ended s.physical=true
    ∃ E : State S→Nat,
      (∀ y,E y≤2*F) ∧ (∀ y,E' y→E y=0) ∧
      (∀ y,Q' y→¬E' y→y.phase=.active →
        n+(List.ofFn (fun e : Fin n=>E (N y e))).sum≤n*E y) ∧
      (∀ y e,Q' y→¬E' y→y.phase≠.active→E (N y e)≤E y) ∧
      (∀ y e,Q' y→¬E' y→y.phase=.active→(N y e).phase≠.active→E (N y e)=0) := by
  dsimp only
  refine exists_fence_fields hn _ _ _ State.phase F ?_ ?_ ?_ ?_
  · intro y e P
    exact ⟨closed _ e P.1,lift_well next (eligible pc ended) entry ended phys y e⟩
  · intro y e _ _ _ A
    change phaseUpdate (eligible pc ended) entry ended phys y.phase (next y.physical e)≠.reserve
    rw [A]
    exact active_no_refund (eligible pc ended) entry ended phys (next y.physical e)
  · intro y e _ _ _ A
    exact spent_sticky _ _ _ _ _ _ _ A
  · intro y G t
    change Height.iidHitCost (lift next (eligible pc ended) entry ended phys) (Hit ended) t y≤_ 
    by_cases A : y.phase=.active
    · rw [armed_wordSum _ _ _ _ _ _ _ A G.2]
      exact mean _ G.1 (G.2 A).1 t
    · rw [Height.iidHitCost_of_target _ (Hit ended) y (Or.inl A)]
      exact Nat.zero_le _

end L4.BStarFenceEscrowMonitor
