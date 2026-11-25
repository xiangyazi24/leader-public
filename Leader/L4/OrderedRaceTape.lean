import Leader.L4.StoppedDoorRaceIID
import Leader.L4.ControllerTapeIID

namespace L4.OrderedRaceTape
open BStarResetSchedule ResetReturnIID StoppedDoorRaceIID
open PhysicalCustody

/-- A wait reads only the marks it has seen. A raced state keeps its
immutable arrival cut and the subsequent literal marks separately. -/
inductive State (n : Nat) where
  | waiting (w : List (Fin n))
  | racing (pre trail : List (Fin n)) (q : Decision)

def word {n : Nat} : State n→List (Fin n)
  | .waiting w => w
  | .racing w v _ => w++v

def cut {n : Nat} (A : List (Fin n)→Prop) (w : List (Fin n)) : Prop :=
  A w ∧ ∀ pre post,w=pre++post→post≠[]→¬A pre

noncomputable def enter {n : Nat} (A : List (Fin n)→Prop) (k : Nat) (w : List (Fin n)) : State n := by
  classical
  exact if A w then .racing w [] (.live k) else .waiting w

noncomputable def tick {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) :
    State n → Fin n → State n
  | .waiting w,e => enter A k (appendTape w e)
  | .racing w v q,e => .racing w (appendTape v e) (next d q e)

def arrived {n : Nat} : State n→Prop
  | .waiting _ => False
  | .racing .. => True

def done {n : Nat} : State n→Prop
  | .waiting _ => False
  | .racing _ _ q => target q

def rejected {n : Nat} : State n→Prop
  | .racing _ _ .reject => True
  | _ => False

def reserve {n : Nat} (later k : Nat) : State n→Nat
  | .waiting _ => score later (.live k)
  | .racing _ _ q => score later q

theorem word_enter {n : Nat} (A : List (Fin n)→Prop) (k : Nat) (w : List (Fin n)) :
    word (enter A k w)=w := by
  classical
  unfold enter
  split <;> simp [word]

theorem word_tick {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat)
    (x : State n) (e : Fin n) : word (tick A d k x e)=appendTape (word x) e := by
  cases x with
  | waiting w => exact word_enter A k _
  | racing w v q => simp [word,tick,appendTape,List.append_assoc]

theorem reserve_enter {n : Nat} (A : List (Fin n)→Prop) (k later : Nat) (w : List (Fin n)) :
    reserve later k (enter A k w)=score later (.live k) := by
  classical
  unfold enter
  split <;> rfl

theorem awake_iff {n : Nat} (A : List (Fin n)→Prop) (k : Nat) (w : List (Fin n)) :
    arrived (enter A k w) ↔ A w := by
  classical
  unfold enter
  split <;> simp_all [arrived]

private theorem entered_le {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) :
    ∀ t w, Height.iidHitCost (tick A d k) arrived t (enter A k w) ≤
      Height.iidHitCost appendTape A t w := by
  classical
  intro t
  induction t with
  | zero => intro w; exact Nat.zero_le _
  | succ t ih =>
    intro w
    by_cases a : A w
    · have E := (awake_iff A k w).2 a
      rw [Height.iidHitCost_of_target _ _ _ E]
      exact Nat.zero_le _
    · have E : ¬arrived (enter A k w) := fun H=>(a ((awake_iff A k w).1 H))
      simp only [Height.iidHitCost,if_neg E,if_neg a]
      apply Nat.add_le_add_left
      apply ControllerTapeIID.sum_mono
      intro e
      have eq : tick A d k (enter A k w) e=enter A k (appendTape w e) := by simp [enter,a,tick]
      rw [eq]
      exact ih _

private theorem racing_le {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) :
    ∀ t pre v q, Height.iidHitCost (tick A d k) done t (.racing pre v q) ≤
      Height.iidHitCost (next d) target t q := by
  classical
  intro t
  induction t with
  | zero => intro pre v q; exact Nat.le_refl _
  | succ t ih =>
    intro pre v q
    by_cases D : target q
    · rw [Height.iidHitCost_of_target _ _ _ (show done (.racing pre v q) from D)]
      exact Nat.zero_le _
    · have N : ¬done (State.racing pre v q) := D
      simp only [Height.iidHitCost,if_neg N,if_neg D,tick]
      apply Nat.add_le_add_left
      apply ControllerTapeIID.sum_mono
      intro e
      exact ih _ _ _

private theorem cost_mono {α : Type} {n : Nat} (next₀ : α→Fin n→α)
    {A B : α→Prop} (imp : ∀ x,A x→B x) (t : Nat) (x : α) :
    Height.iidHitCost next₀ B t x≤Height.iidHitCost next₀ A t x := by
  classical
  induction t generalizing x with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases H : B x
    · rw [Height.iidHitCost_of_target _ _ _ H]; exact Nat.zero_le _
    · have N : ¬ A x := fun h=>H (imp _ h)
      simp only [Height.iidHitCost,if_neg H,if_neg N]
      exact Nat.add_le_add_left (ControllerTapeIID.sum_mono (fun e=>ih (next₀ x e))) _

def initialized {n : Nat} (k : Nat) : State n→Prop
  | .racing _ [] q => q=.live k
  | _ => False

private theorem initialized_cost {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat)
    (B : Nat) (E : Height.IIDExpectedHittingTimeAtMost appendTape A [] B) :
    Height.IIDExpectedHittingTimeAtMost (tick A d k) (fun x=> initialized k x∨done x)
      (enter A k []) B := by
  classical
  have C (t : Nat) (w : List (Fin n)) :
      Height.iidHitCost (tick A d k) (fun x=>initialized k x∨done x) t (enter A k w) ≤
        Height.iidHitCost appendTape A t w := by
    induction t generalizing w with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      by_cases H : A w
      · have G : initialized k (enter A k w)∨done (enter A k w) := by
          exact .inl (by simp [enter,H,initialized])
        rw [Height.iidHitCost_of_target _ (fun x=>initialized k x∨done x) _ G]
        exact Nat.zero_le _
      · have N : ¬(initialized k (enter A k w)∨done (enter A k w)) := by
          simp [enter,H,initialized,done]
        simp only [Height.iidHitCost,if_neg N,if_neg H]
        apply Nat.add_le_add_left
        apply ControllerTapeIID.sum_mono
        intro e
        rw [show tick A d k (enter A k w) e=enter A k (appendTape w e) by simp [enter,H,tick]]
        exact ih _
  intro t
  exact Nat.le_trans (C t []) (E t)

/-- Starts the race at the first arrival, with no intervening raw mark.
The mean is arrival mean plus the bounded local race clock. -/
theorem combined_expected {n : Nat} (hn : 0<n) (A : List (Fin n)→Prop)
    (d : Fin n) (k : Nat) (K : 0<k) (B : Nat)
    (E : Height.IIDExpectedHittingTimeAtMost appendTape A [] B) :
    Height.IIDExpectedHittingTimeAtMost (tick A d k) done (enter A k []) (B+n*k) := by
  apply Height.iid_stage_le (tick A d k) hn _ (initialized k) done B (n*k)
    (initialized_cost A d k B E)
  intro x I
  cases x with
  | waiting w => exact False.elim I
  | racing pre v q =>
    cases v with
    | nil =>
      change q=.live k at I
      subst q
      intro t
      exact Nat.le_trans (racing_le A d k t pre [] _) (race_expected d k K t)
    | cons e rest => exact False.elim I

def valid {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) : State n→Prop
  | .waiting w => ∀ pre post,w=pre++post→¬A pre
  | .racing pre suffix q => cut A pre ∧ q=BStarResetSchedule.run (next d) (.live k) suffix

theorem valid_start {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) :
    valid A d k (enter A k []) := by
  classical
  unfold enter
  split
  · rename_i good
    refine ⟨⟨good,?_⟩,rfl⟩
    intro a b E N
    have B := congrArg List.length E
    simp only [List.length_append,List.length_nil] at B
    exact (N (List.length_eq_zero_iff.mp (by omega))).elim
  · rename_i bad
    intro a b E
    have B := congrArg List.length E
    simp only [List.length_append,List.length_nil] at B
    rwa [List.length_eq_zero_iff.mp (show a.length=0 by omega)]

private theorem earlier_snoc {n : Nat} {w pre post : List (Fin n)} {e : Fin n}
    (H : w++[e]=pre++post) (N : post≠[]) : ∃ rem,w=pre++rem := by
  rcases List.append_eq_append_iff.mp H with ⟨a,E,J⟩|⟨a,E,_⟩
  · have la := congrArg List.length J
    have np := List.length_pos_iff.mpr N
    simp only [List.length_cons,List.length_nil,List.length_append] at la
    have Z := List.length_eq_zero_iff.mp (show a.length=0 by omega)
    exact ⟨[],by simpa [Z] using E.symm⟩
  · exact ⟨a,E⟩

theorem valid_step {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) (x : State n)
    (e : Fin n) (H : valid A d k x) : valid A d k (tick A d k x e) := by
  classical
  cases x with
  | waiting w =>
    change valid A d k (enter A k (appendTape w e))
    unfold enter
    split
    · rename_i G
      refine ⟨⟨G,?_⟩,rfl⟩
      intro a b E N
      obtain ⟨r,R⟩:=earlier_snoc E N
      exact H a r R
    · rename_i G
      intro a b E
      by_cases N : b=[]
      · subst b
        simp only [List.append_nil] at E
        exact E ▸ G
      · obtain ⟨r,R⟩:=earlier_snoc E N
        exact H a r R
  | racing p v q =>
    obtain ⟨H,R⟩ := H
    refine ⟨H,?_⟩
    rw [appendTape, BStarResetSchedule.run_append]
    exact congrArg (fun q=>next d q e) R

theorem accepted_split {n : Nat} (A : List (Fin n)→Prop) (d : Fin n) (k : Nat) (K : 0<k)
    (w v : List (Fin n)) (H : valid A d k (.racing w v .accept)) :
    cut A w ∧ PhysicalDoorRace.accepted d k v=1 := by
  exact ⟨H.1,(reaches_accept_iff d k K v).1 H.2.symm⟩

theorem reserve_localLaw {n : Nat} (hn : 4≤n) (A : List (Fin n)→Prop)
    (d : Fin n) (later k : Nat) (cap : later+k≤6)
    (x : State n) (L : ¬done x)
    (V : ∀ pre v j, x=.racing pre v (.live j) → 0<j ∧ j≤k) :
    AdaptiveDoorCredit.LocalLaw (tick A d k) (reserve later k) x := by
  cases x with
  | waiting w =>
    left
    intro e
    change score later (.live k) ≤ reserve later k (enter A k (appendTape w e))
    rw [reserve_enter]
    exact Nat.le_refl _
  | racing pre v q =>
    cases q with
    | accept => exact (L trivial).elim
    | reject => exact (L trivial).elim
    | live j =>
      obtain ⟨pos, J⟩ := V _ _ _ rfl
      exact active_race_credit hn d later j pos (by omega)


theorem remaining_bounded {n : Nat} (d : Fin n) (k : Nat) (K : 0<k)
    (v : List (Fin n)) (j : Nat)
    (R : BStarResetSchedule.run (next d) (.live k) v=.live j) : 0<j ∧ j≤k := by
  have absorb (q : Decision) (t : List (Fin n)) (h : q=.accept ∨ q=.reject) :
      BStarResetSchedule.run (next d) q t=q := by
    induction t with
    | nil => rfl
    | cons e t ih =>
      rcases h with rfl|rfl
      · exact ih
      · exact ih
  induction v generalizing k with
  | nil => cases R; exact ⟨K,Nat.le_refl _⟩
  | cons e v ih =>
    cases k with
    | zero => exact (Nat.not_lt_zero _ K).elim
    | succ k =>
      change BStarResetSchedule.run (next d) (next d (.live (k+1)) e) v=.live j at R
      change BStarResetSchedule.run (next d)
        (if DisjointMarks d e then .live (k+1)
         else if e=d then if k=0 then .accept else .live k else .reject) v=.live j at R
      by_cases D : DisjointMarks d e
      · rw [if_pos D] at R; exact ih _ K R
      · rw [if_neg D] at R
        by_cases E : e=d
        · rw [if_pos E] at R
          by_cases H : k=0
          · rw [if_pos H,absorb _ _ (.inl rfl)] at R
            cases R
          · rw [if_neg H] at R
            obtain ⟨h,L⟩ := ih k (Nat.pos_of_ne_zero H) R
            exact ⟨h,Nat.le_trans L (Nat.le_succ _)⟩
        · rw [if_neg E,absorb _ _ (.inr rfl)] at R
          cases R

/-- No continuation or physical assumption is needed for the local
failure accounting; the ready-time maximum remains a separate clock. -/
theorem failed_mass_bound {n : Nat} (hn : 4≤n) (A : List (Fin n)→Prop)
    (d : Fin n) (later k : Nat) (K : 0<k) (cap : later+k≤6) (t : Nat) :
    729*TripleRenewal.terminalMass (tick A d k) done rejected t (enter A k []) +
      score later (.live k)*n^t ≤ 729*n^t := by
  rw [←reserve_enter A k later ([] : List (Fin n))]
  apply AdaptiveDoorCredit.terminal_credit (tick A d k) (valid A d k) done rejected 729
    (reserve later k) (valid_step A d k)
  · intro x _
    cases x with
    | waiting w => exact AdaptiveDoorCredit.score_cap (.live (later+k))
    | racing pre v q =>
      cases q with
      | live j => exact AdaptiveDoorCredit.score_cap (.live (later+j))
      | accept => exact AdaptiveDoorCredit.score_cap (.live later)
      | reject => exact Nat.zero_le _
  · intro x _ _ F
    cases x with
    | waiting w => cases F
    | racing pre v q =>
      cases q with
      | live j => cases F
      | accept => cases F
      | reject => rfl
  · intro x hx live
    obtain mono|⟨win,l₁,l₂,D₁,D₂,D₃,paid,rest⟩ :=
      reserve_localLaw hn A d later k cap x live (by
        intro pre v j E
        subst x
        exact remaining_bounded d k K v j hx.2.symm)
    · have B := ControllerTapeIID.sum_mono (a:=fun _ : Fin n=>reserve later k x) mono
      have S (m c : Nat) : (List.ofFn (fun _ : Fin m=>c)).sum=m*c := by
        induction m with
        | zero => simp [List.ofFn_zero]
        | succ m ih => rw [List.ofFn_succ,List.sum_cons,ih,Nat.succ_mul,Nat.add_comm]
      rw [S] at B
      exact B
    · exact AdaptiveDoorCredit.triple_drift _ _ win l₁ l₂ D₁ D₂ D₃ paid rest
  · exact valid_start A d k

#print axioms word_tick
#print axioms combined_expected
#print axioms valid_step
#print axioms accepted_split
#print axioms reserve_localLaw
#print axioms failed_mass_bound
end L4.OrderedRaceTape
