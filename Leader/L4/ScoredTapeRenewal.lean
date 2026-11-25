import Leader.L4.ScoredTapeSerial

namespace L4.ScoredTapeRenewal
open ResetReturnIID ScoredTapeSerial

/-- A non-race phase uses a fixed score on its literal sampled word.
On entry to the next phase no mark is spent to change phase. -/
def wait {n : Nat} (P : Word n→Prop) (a A : Nat) (cap : a≤729)
    (mean : Height.IIDExpectedHittingTimeAtMost appendTape P [] A) : Reader n a a A where
  State := Word n
  start := []
  tick := appendTape
  word := id
  word_start := rfl
  word_step := fun _ _=>rfl
  valid := fun _=>True
  valid_start := trivial
  valid_step := fun _ _ _ _=>trivial
  done := P
  reject := fun _=>False
  credit := fun _=>a
  initial_credit := rfl
  cap := fun _ _=>cap
  lost := fun _ _ _ h=>h.elim
  paid := fun _ _ _ _=>rfl
  localLaw := fun _ _ _=>.inl fun _=>Nat.le_refl _
  mean := mean

variable {n a b A : Nat} (R : Reader n a b A)

abbrev Padded := R.State × Word n

def paddingValid (q : Padded R) : Prop :=
  R.valid q.1 ∧ (q.2=[] ∨ R.done q.1)

noncomputable def paddedTick (q : Padded R) (e : Fin n) : Padded R := by
  classical
  exact if R.done q.1 then (q.1,appendTape q.2 e) else (R.tick q.1 e,[])

def locWord (q : Padded R) : Word n := R.word q.1++q.2

theorem padded_valid (q : Padded R) (e : Fin n) (H : paddingValid R q) :
    paddingValid R (paddedTick R q e) := by
  classical
  unfold paddedTick
  split
  · rename_i d; exact ⟨H.1,.inr d⟩
  · rename_i d; exact ⟨R.valid_step _ e H.1 d,.inl rfl⟩

theorem padding_step (q : Padded R) (e : Fin n) (H : paddingValid R q) :
    locWord R (paddedTick R q e)=appendTape (locWord R q) e := by
  classical
  unfold paddedTick
  split
  · simp only [locWord,appendTape,List.append_assoc]
  · rename_i N
    have E := H.2.resolve_right N
    change R.word (R.tick q.1 e)++[]= (R.word q.1++q.2)++[e]
    rw [E,List.append_nil,List.append_nil,R.word_step]
    rfl

/-- Use a subtype so every state of the renewal projection satisfies
the padded invariant, not only the distinguished start. -/
abbrev Trail := {q : Padded R // paddingValid R q}

noncomputable def onTrail (q : Trail R) (e : Fin n) : Trail R :=
  ⟨paddedTick R q.1 e,padded_valid R q.1 e q.2⟩

def first : Trail R :=
  ⟨(R.start,[]), R.valid_start, .inl rfl⟩

def atEnd (q : Trail R) : Prop := R.done q.1.1
def isLoss (q : Trail R) : Prop := R.reject q.1.1
def value (q : Trail R) : Nat := R.credit q.1.1

noncomputable def stage (pre : Word n) : TripleRenewal.Stage appendTape pre where
  State := Trail R
  start := first R
  next := onTrail R
  project := fun q=>pre++locWord R q.1
  ready := atEnd R
  reachable := fun _=>True
  projInit := by
    change pre++(R.word R.start++[])=pre
    rw [R.word_start]; simp
  projStep := by
    intro q e
    change pre++locWord R (paddedTick R q.1 e)=appendTape (pre++locWord R q.1) e
    rw [padding_step R q.1 e q.2]
    simp only [appendTape,List.append_assoc]
  reachStart := trivial
  reachStep := fun _ _ _=>trivial

theorem padded_mean :
    Height.IIDExpectedHittingTimeAtMost (onTrail R) (atEnd R) (first R) A := by
  classical
  have H (t : Nat) (q : Trail R) :
      Height.iidHitCost (onTrail R) (atEnd R) t q≤Height.iidHitCost R.tick R.done t q.1.1 := by
    induction t generalizing q with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      by_cases D : R.done q.1.1
      · rw [Height.iidHitCost_of_target _ _ _ (show atEnd R q from D)]
        exact Nat.zero_le _
      · have ND : ¬atEnd R q := D
        simp only [Height.iidHitCost,if_neg D,if_neg ND]
        apply Nat.add_le_add_left
        apply ControllerTapeIID.sum_mono
        intro e
        have E : (onTrail R q e).1.1=R.tick q.1.1 e := by simp [onTrail,paddedTick,D]
        rw [←E]
        exact ih _
  intro t
  exact Nat.le_trans (H t (first R)) (R.mean t)

/-- Attaching a clock to a growing tape does not condition on favorable
labels. The local score is unchanged by terminal padding. -/
theorem padded_failed_mass (aPos : 0<a) (t : Nat) :
    729*TripleRenewal.terminalMass (onTrail R) (atEnd R) (isLoss R) t (first R)≤728*n^t := by
  have law : ∀ q : Trail R, True → ¬atEnd R q →
      AdaptiveDoorCredit.LocalLaw (onTrail R) (value R) q := by
    intro q _ D
    have N : ¬R.done q.1.1 := D
    have E (e : Fin n) : value R (onTrail R q e) = R.credit (R.tick q.1.1 e) := by
      simp [value,onTrail,paddedTick,N]
    rcases R.localLaw q.1.1 q.2.1 N with mono|⟨win,l₁,l₂,H₁,H₂,H₃,pay,stay⟩
    · exact .inl (fun e=>by rw [E]; exact mono e)
    · refine .inr ⟨win,l₁,l₂,H₁,H₂,H₃,?_,?_⟩
      · rw [E]; exact pay
      · intro e w u v; rw [E]; exact stay e w u v
  have pos : 0<value R (first R) := by
    change 0<R.credit R.start
    rw [R.initial_credit]
    exact aPos
  exact AdaptiveDoorCredit.six_race_failure (onTrail R) (fun _=>True) (atEnd R) (isLoss R)
    (value R) (fun _ _ _=>trivial) (fun q _=>R.cap _ q.2.1)
    (fun q _ d f=>R.lost _ q.2.1 d f) law t (first R) trivial pos

private theorem terminal_mono {α : Type} {n : Nat} (next : α→Fin n→α)
    (done F G : α→Prop) (imp : ∀ x,done x→F x→G x) (t : Nat) (x : α) :
    TripleRenewal.terminalMass next done F t x ≤ TripleRenewal.terminalMass next done G t x := by
  classical
  induction t generalizing x with
  | zero =>
    by_cases T : done x
    · by_cases H : F x
      · simp [TripleRenewal.terminalMass,T,H,imp x T H]
      · simp [TripleRenewal.terminalMass,T,H]
    · simp [TripleRenewal.terminalMass,T]
  | succ t ih =>
    by_cases T : done x
    · by_cases H : F x
      · simp [TripleRenewal.terminalMass,T,H,imp x T H]
      · simp [TripleRenewal.terminalMass,T,H]
    · simp only [TripleRenewal.terminalMass,if_neg T,TaggedTail.sumEdge]
      exact ControllerTapeIID.sum_mono (fun e=>ih (next x e))

theorem height_cost {X : Type} {n : Nat} (step : X→Fin n→X)
    (P : X→Prop) (t : Nat) (x : X) :
    L4.iidHitCost step P t x=Height.iidHitCost step P t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : P x
    · simp only [L4.iidHitCost,Height.iidHitCost,if_pos H]
    · simp only [L4.iidHitCost,Height.iidHitCost,if_neg H]
      congr 1
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e=>ih (step x e))

/-- Close renewal on the original accumulated tape. A success certificate
may use commutation; the projection still advances only real marks. -/
noncomputable def uniformAttempt (pre : Word n) (goal adm : Word n→Prop)
    (startLive : ¬R.done R.start) (aPos : 0<a)
    (restart : ∀ w,adm (pre++w))
    (success : ∀ y,R.valid y→R.done y→¬R.reject y→∀ pad,goal (pre++(R.word y++pad))) :
    TripleRenewal.UniformAttempt appendTape goal adm A 729 pre where
  stage := stage R pre
  properStart := startLive
  restart := fun y _ _ _=>restart (locWord R y.1)
  mean := by
    intro t
    rw [height_cost]
    exact padded_mean R t
  failBound := by
    intro t
    have H := padded_failed_mass R aPos t
    have C := terminal_mono (onTrail R) (atEnd R)
      (fun y=>¬goal (pre++locWord R y.1)) (isLoss R)
      (fun y d f=>Classical.byContradiction (fun N=>f (success y.1.1 y.2.1 d N y.1.2))) t (first R)
    exact Nat.le_trans (Nat.mul_le_mul_left 729 C) H

end L4.ScoredTapeRenewal
