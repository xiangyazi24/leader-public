import Leader.L4.RankAttempt

/-! Finite-word renewal and preparation bounds for the consecutive-root
clock. All bounds refer to the original IID raw marks; rounds can end
at adapted, history-dependent times. -/
namespace L4.TripleRenewal
open TaggedTail Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    rw [sSucc,sSucc]
    exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e) = sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e) = a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

/-- Count words whose first done-state is reached by the horizon and
satisfies the indicated terminal event. The arbitrary suffix of a word
of length t is still counted, even after the auxiliary observer stops. -/
noncomputable def terminalMass {β : Type} {n : Nat} (next : β → Fin n → β)
    (done event : β → Prop) : Nat → β → Nat
  | 0, x => if done x ∧ event x then 1 else 0
  | t+1, x =>
    if done x then (if event x then n^(t+1) else 0)
    else sumEdge (fun e => terminalMass next done event t (next x e))

theorem terminalMass_le_total {β : Type} {n : Nat} (next : β → Fin n → β)
    (done event : β → Prop) (t : Nat) (x : β) : terminalMass next done event t x ≤ n^t := by
  induction t generalizing x with
  | zero =>
    simp only [terminalMass,Nat.pow_zero]
    split <;> omega
  | succ t ih =>
    by_cases hd : done x
    · simp [terminalMass,hd]
      split <;> omega
    · simp only [terminalMass,hd,if_false]
      have hb := sMono (g := fun _ : Fin n => n^t) (fun e => ih (next x e))
      rw [sConst] at hb
      simpa only [Nat.pow_succ'] using hb

/-- A variable-duration stopped observation over the actual raw pair
transition. Its terminal condition need not be absorbing, since all
statistic definitions stop at its first occurrence. -/
structure Stage {α : Type} {n : Nat} (step : α → Fin n → α) (x : α) where
  State : Type
  start : State
  next : State → Fin n → State
  project : State → α
  ready : State → Prop
  reachable : State → Prop
  projInit : project start = x
  projStep : ∀ y e, project (next y e) = step (project y) e
  reachStart : reachable start
  reachStep : ∀ y e, reachable y → reachable (next y e)

/-- One-time observation: charge raw marks until its stop, then charge
at most B on a failed terminal observation. Only continuation horizons
up to the original horizon may contribute. -/
theorem glue_until_stop {α β : Type} {n : Nat} (step : α → Fin n → α)
    (next : β → Fin n → β) (project : β → α)
    (projectStep : ∀ y e, project (next y e) = step (project y) e)
    (goal : α → Prop) (done valid : β → Prop) (keep : ∀ y e, valid y → valid (next y e))
    (B T : Nat)
    (cont : ∀ y t, valid y → done y → ¬ goal (project y) → t≤T →
      iidHitCost step goal t (project y) ≤ B*n^t)
    (t : Nat) (ht : t≤T) (x : β) (hx : valid x) :
    iidHitCost step goal t (project x) ≤ iidHitCost next done t x +
      B*terminalMass next done (fun y => ¬ goal (project y)) t x := by
  induction t generalizing x with
  | zero => simp [iidHitCost]
  | succ t ih =>
    by_cases hg : goal (project x)
    · rw [iidHitCost_of_target _ _ _ hg]
      exact Nat.zero_le _
    · by_cases hd : done x
      · simpa only [terminalMass,hd,if_true,hg,not_false_eq_true,
          iidHitCost_of_target _ _ _ hd,Nat.zero_add] using cont x (t+1) hx hd hg ht
      · rw [iidHitCost,if_neg hg,iidHitCost,if_neg hd,terminalMass,if_neg hd,←sScale]
        change n^(t+1)+sumEdge (fun e => iidHitCost step goal t (step (project x) e)) ≤
          n^(t+1)+sumEdge (fun e => iidHitCost next done t (next x e))+
          sumEdge (fun e => B*terminalMass next done (fun y => ¬goal (project y)) t (next x e))
        have hs := sMono (fun e => ih (by omega) (next x e) (keep x e hx))
        simp only [projectStep,sAdd] at hs
        omega

/-- A single observation that begins strictly before its stop can only
charge continuation at a strictly shorter remaining horizon. -/
theorem glue_after_one_mark {α : Type} {n : Nat} {step : α → Fin n → α}
    {x : α} (s : Stage step x) (goal : α → Prop) (B t : Nat)
    (hstart : ¬ s.ready s.start)
    (cont : ∀ y u, s.reachable y → s.ready y → ¬ goal (s.project y) → u≤t →
      iidHitCost step goal u (s.project y) ≤ B*n^u) :
    iidHitCost step goal (t+1) x ≤ iidHitCost s.next s.ready (t+1) s.start +
      B*terminalMass s.next s.ready (fun y => ¬ goal (s.project y)) (t+1) s.start := by
  refine Nat.le_trans (Nat.le_of_eq (congrArg (iidHitCost step goal (t+1)) s.projInit).symm) ?_
  by_cases hg : goal (s.project s.start)
  · rw [iidHitCost_of_target _ _ _ hg]
    exact Nat.zero_le _
  · rw [iidHitCost,if_neg hg,iidHitCost,if_neg hstart,terminalMass,if_neg hstart,←sScale]
    change n^(t+1) + sumEdge (fun e => iidHitCost step goal t (step (s.project s.start) e)) ≤
        n^(t+1)+sumEdge (fun e => iidHitCost s.next s.ready t (s.next s.start e))+
        sumEdge (fun e => B*terminalMass s.next s.ready (fun y => ¬goal (s.project y)) t (s.next s.start e))
    have hs := sMono (fun e =>
      glue_until_stop step s.next s.project s.projStep goal s.ready s.reachable s.reachStep
        B t cont t (Nat.le_refl _) (s.next s.start e) (s.reachStep _ _ s.reachStart))
    simp only [s.projStep,sAdd] at hs
    omega

/-- A restartable trial: its conditional mean is A and every finite
horizon contains failed first-stop mass at most (D−1)/D. A failed stop
returns an admissible physical state, with no assumption of independence. -/
structure UniformAttempt {α : Type} {n : Nat} (step : α → Fin n → α)
    (goal admissible : α → Prop) (A D : Nat) (x : α) where
  stage : Stage step x
  properStart : ¬ stage.ready stage.start
  restart : ∀ y, stage.reachable y → stage.ready y → ¬ goal (stage.project y) →
    admissible (stage.project y)
  mean : IIDExpectedHittingTimeAtMost stage.next stage.ready stage.start A
  failBound : ∀ t, D * terminalMass stage.next stage.ready
      (fun y => ¬ goal (stage.project y)) t stage.start ≤ (D-1)*n^t

/-- Variable-duration restart lemma for uniform conditional trials. -/
theorem expected_of_uniform_attempts {α : Type} {n : Nat} (step : α → Fin n → α)
    (goal admissible : α → Prop) (A D : Nat) (hD : 0<D)
    (attempt : ∀ x, admissible x → ¬ goal x → Nonempty (UniformAttempt step goal admissible A D x))
    (x : α) (hx : admissible x) :
    IIDExpectedHittingTimeAtMost step goal x (D*A) := by
  intro t
  induction t using Nat.strongRecOn generalizing x with
  | ind t ih =>
    cases t with
    | zero => simp [iidHitCost]
    | succ t =>
      by_cases hg : goal x
      · rw [iidHitCost_of_target _ _ _ hg]
        exact Nat.zero_le _
      · obtain ⟨s⟩ := attempt x hx hg
        have hGlue := glue_after_one_mark s.stage goal (D*A) t s.properStart
          (fun y u hy hd hng hu => ih u (by omega) (s.stage.project y) (s.restart y hy hd hng))
        have hFail := Nat.mul_le_mul_left A (s.failBound (t+1))
        have hEq : (D*A)*n^(t+1) = A*n^(t+1)+A*((D-1)*n^(t+1)) := by
          have he : D*A=A+A*(D-1) := by
            calc
              _ = A*(1+(D-1)) := by rw [show 1+(D-1)=D by omega,Nat.mul_comm]
              _ = _ := by rw [Nat.mul_add,Nat.mul_one]
          rw [he,Nat.add_mul,Nat.mul_assoc]
        rw [←Nat.mul_assoc,Nat.mul_comm A D] at hFail
        rw [hEq]
        have hm := s.mean (t+1)
        omega

/-- Add a one-time preparation stage to a uniform post-preparation
bound; stopping during preparation is already a success. -/
theorem expected_with_preparation {α : Type} {n : Nat} {step : α → Fin n → α}
    {x : α} (s : Stage step x) (goal : α → Prop) (P B : Nat)
    (prep : IIDExpectedHittingTimeAtMost s.next s.ready s.start P)
    (after : ∀ y, s.reachable y → s.ready y → ¬ goal (s.project y) →
      IIDExpectedHittingTimeAtMost step goal (s.project y) B) :
    IIDExpectedHittingTimeAtMost step goal x (P+B) := by
  intro t
  rw [←s.projInit]
  have hGlue := glue_until_stop step s.next s.project s.projStep goal s.ready s.reachable
    s.reachStep B t (fun y u hy hd hn _ => after y hy hd hn u)
    t (Nat.le_refl _) s.start s.reachStart
  have hm := prep t
  have hf := Nat.mul_le_mul_left B (terminalMass_le_total s.next s.ready
    (fun y => ¬ goal (s.project y)) t s.start)
  rw [Nat.add_mul]
  omega


/-- Weakening a natural-valued expected clock bound. -/
theorem expected_mono {α : Type} {n : Nat} {step : α → Fin n → α}
    {goal : α → Prop} {x : α} {A B : Nat}
    (h : IIDExpectedHittingTimeAtMost step goal x A) (hle : A≤B) :
    IIDExpectedHittingTimeAtMost step goal x B :=
  fun t => Nat.le_trans (h t) (Nat.mul_le_mul_right _ hle)

/-- Exact numerical assembly of the paper's consecutive-root deletion
clock. Here `admissible` represents the sealed phases at the same three
root identities, and any early retirement must belong to `goal`.
This theorem does not assert the physical preparation or attempt premises. -/
theorem consecutiveRootClock_of_interfaces {α : Type} {n : Nat} {step : α → Fin n → α}
    {x : α} (s : Stage step x) (goal admissible : α → Prop)
    (a b : Nat) (hb : 0<b)
    (prep : IIDExpectedHittingTimeAtMost s.next s.ready s.start (6*n*(a+b)))
    (prepared : ∀ y, s.reachable y → s.ready y → ¬ goal (s.project y) →
      admissible (s.project y))
    (oneEdge : b=1 → ∀ y, admissible y →
      IIDExpectedHittingTimeAtMost step goal y (6*n*(a+1)))
    (moderate : 2≤b → a≤2*b → ∀ y, admissible y → ¬goal y →
      Nonempty (UniformAttempt step goal admissible (n*(5*a+4*b)) 64 y))
    (long : 2≤b → 2*b<a → ∀ y, admissible y → ¬goal y →
      Nonempty (UniformAttempt step goal admissible (10*n*(a+b)) 256 y)) :
    IIDExpectedHittingTimeAtMost step goal x (4096*n*(a+b)) := by
  have hpost (y : α) (hy : admissible y) :
      IIDExpectedHittingTimeAtMost step goal y (2560*n*(a+b)) := by
    by_cases hb1 : b=1
    · refine expected_mono (oneEdge hb1 y hy) ?_
      have hcoeff : 6*n≤2560*n := Nat.mul_le_mul_right _ (by decide)
      rw [hb1]
      exact Nat.mul_le_mul_right _ hcoeff
    · have hb2 : 2≤b := by omega
      by_cases ha : a≤2*b
      · refine expected_mono (expected_of_uniform_attempts step goal admissible _ 64
          (by decide) (moderate hb2 ha) y hy) ?_
        have hbase : 5*a+4*b≤40*(a+b) := by omega
        calc
          _ = (64*n)*(5*a+4*b) := by ac_rfl
          _ ≤ (64*n)*(40*(a+b)) := Nat.mul_le_mul_left _ hbase
          _ = (64*40)*(n*(a+b)) := by ac_rfl
          _ = _ := (Nat.mul_assoc 2560 n (a+b)).symm
      · refine expected_mono (expected_of_uniform_attempts step goal admissible _ 256
          (by decide) (long hb2 (by omega)) y hy) ?_
        calc
          _ = (256*10)*(n*(a+b)) := by ac_rfl
          _ = 2560*n*(a+b) := (Nat.mul_assoc 2560 n (a+b)).symm
          _ ≤ _ := Nat.le_refl _
  refine expected_mono (expected_with_preparation s goal (6*n*(a+b)) (2560*n*(a+b))
    prep (fun y hr hd hng => hpost (s.project y) (prepared y hr hd hng))) ?_
  calc
    _ = (6+2560)*(n*(a+b)) := by rw [Nat.add_mul]; ac_rfl
    _ ≤ 4096*(n*(a+b)) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := (Nat.mul_assoc ..).symm

/-- A caller can turn any positive mean bound into a quarter-overrun
budget on the fixed raw horizon four times that bound. -/
theorem quarter_overrun {α : Type} {n : Nat} {step : α → Fin n → α}
    {goal : α → Prop} {x : α} (B : Nat) (hB : 0<B)
    (h : IIDExpectedHittingTimeAtMost step goal x B) :
    4*survival step (fun y => ¬goal y) (4*B) x ≤ n^(4*B) := by
  have hh := Nat.le_trans (RankPhysical.horizon_mul_survival_le_cost step goal _ x) (h (4*B))
  rw [show 4*B*survival step (fun y => ¬goal y) (4*B) x =
    B*(4*survival step (fun y => ¬goal y) (4*B) x) by ac_rfl] at hh
  exact Nat.le_of_mul_le_mul_left hh hB


/-- The event "failed at the first stop by time t" persists under
arbitrary word extensions, regardless of what auxiliary state does later. -/
theorem terminalMass_pad_lower {β : Type} {n : Nat} (next : β → Fin n → β)
    (done event : β → Prop) (t u : Nat) (x : β) :
    n^u*terminalMass next done event t x ≤ terminalMass next done event (t+u) x := by
  induction t generalizing x with
  | zero =>
    by_cases hd : done x
    · by_cases he : event x
      · cases u <;> simp [terminalMass,hd,he]
      · cases u <;> simp [terminalMass,hd,he]
    · simp [terminalMass,hd]
  | succ t ih =>
    have hh : (t+1)+u = (t+u)+1 := by omega
    by_cases hd : done x
    · by_cases he : event x
      · simp only [hh,terminalMass,hd,he,if_true]
        rw [show t+u+1=u+(t+1) by omega]
        rw [←Nat.pow_add]
        exact Nat.le_refl _
      · simp [hh,terminalMass,hd,he]
    · rw [hh]
      simp only [terminalMass,hd,if_false,←sScale]
      exact sMono (fun e => ih (next x e))

/-- Remove a controlled-proof remainder proportional to a controlled
attempt's unfinished mass. A finite horizon contradiction suffices:
a violated prefix mass has at least one integer unit of excess, whereas
the mean bound makes the remainder smaller after a long enough extension. -/
theorem failure_bound_of_vanishing_remainder {β γ : Type} {n : Nat}
    (next : β → Fin n → β) (done event : β → Prop) (x : β)
    (other : γ → Fin n → γ) (otherDone : γ → Prop) (z : γ)
    (hn : 0<n) (D A C : Nat) (mean : IIDExpectedHittingTimeAtMost other otherDone z A)
    (approx : ∀ u, D*terminalMass next done event u x ≤
      (D-1)*n^u + C*survival other (fun y => ¬otherDone y) u z) :
    ∀ t, D*terminalMass next done event t x ≤ (D-1)*n^t := by
  intro t
  by_cases hgood : D*terminalMass next done event t x ≤ (D-1)*n^t
  · exact hgood
  exfalso
  let k := C*A*n^t+1
  let u := t+k
  let M := (D-1)*n^u
  let S := survival other (fun y => ¬otherDone y) u z
  have hpos : 0<n^k := Nat.pow_pos hn
  have hpow : n^u = n^k*n^t := by rw [show u = k+t by dsimp [u]; omega,Nat.pow_add]
  have h1 : M+n^k ≤ D*terminalMass next done event u x := by
    calc
      _ = n^k*((D-1)*n^t+1) := by
        dsimp [M]; rw [hpow,Nat.mul_add,Nat.mul_one]; congr 1; ac_rfl
      _ ≤ n^k*(D*terminalMass next done event t x) := Nat.mul_le_mul_left _ (by omega)
      _ = D*(n^k*terminalMass next done event t x) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (terminalMass_pad_lower next done event t k x)
  have h2 : n^k ≤ C*S := by
    have hh : D*terminalMass next done event u x ≤ M+C*S := approx u
    omega
  have hh : u*S ≤ A*n^u := Nat.le_trans (RankPhysical.horizon_mul_survival_le_cost other otherDone u z) (mean u)
  have h3 : n^k*u ≤ n^k*(C*A*n^t) := by
    calc
      _ ≤ (C*S)*u := Nat.mul_le_mul_right _ h2
      _ = C*(u*S) := by ac_rfl
      _ ≤ C*(A*n^u) := Nat.mul_le_mul_left _ hh
      _ = _ := by rw [hpow]; ac_rfl
  have hu := Nat.le_of_mul_le_mul_left h3 hpos
  dsimp [u,k] at hu
  omega

private theorem pow_two_tangent_base (d : Nat) : d+2 ≤ (2:Nat)^(d+1) := by
  induction d with
  | zero => decide
  | succ d ih => rw [Nat.pow_succ]; omega

private theorem pow_two_tangent (m q : Nat) :
    (m+2)*2^q ≤ 2^(m+1)+q*2^q := by
  by_cases hy : q≤m
  · let d := m-q
    have hq : m+1 = (d+1)+q := by dsimp [d]; omega
    have hm : m+2 = (d+2)+q := by dsimp [d]; omega
    calc
      _ = (d+2)*2^q+q*2^q := by rw [hm,Nat.add_mul]
      _ ≤ 2^(d+1)*2^q+q*2^q := Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (pow_two_tangent_base d)) _
      _ = _ := by rw [←Nat.pow_add,←hq]
  · by_cases hq : q=m+1
    · subst q
      rw [show m+2=1+(m+1) by omega,Nat.add_mul,Nat.one_mul]
      exact Nat.le_refl _
    · exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega : m+2≤q)) (Nat.le_add_left ..)

/-- Likelihood numerator of a list of complete effective paths with
exactly `q` doubled labels on the path with list entry `q`. -/
def likelihoodMass (charges : List Nat) : Nat :=
  (charges.map (fun q => (2:Nat)^q)).sum

/-- First moment of the doubled-label count in the same numerator. -/
def chargeMass (charges : List Nat) : Nat :=
  (charges.map (fun q => q*(2:Nat)^q)).sum

private theorem summed_tangent (m : Nat) (qs : List Nat) :
    (m+2)*likelihoodMass qs ≤ 2^(m+1)*qs.length+chargeMass qs := by
  induction qs with
  | nil => simp [likelihoodMass,chargeMass]
  | cons q qs ih =>
    change (m+2)*(2^q+likelihoodMass qs) ≤
      2^(m+1)*(qs.length+1)+(q*2^q+chargeMass qs)
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
    have hs := Nat.add_le_add (pow_two_tangent m q) ih
    omega

/-- Exact finite Jensen substitute. Distinct successful effective words
count once in the original scheduler and with multiplicity `2^q` in
the controlled scheduler. A mean charge upper bound of `m` gives
success at least `2⁻ᵐ`, up to a linear unfinished-mass correction. -/
theorem controlled_success_of_charge_bound (m denominator residual originalSuccess : Nat)
    (qs : List Nat) (full : denominator ≤ likelihoodMass qs + residual)
    (charge : chargeMass qs ≤ m*denominator) (inject : qs.length ≤ originalSuccess) :
    denominator ≤ 2^m*originalSuccess + (m+2)*residual := by
  have hs := summed_tangent m qs
  have hS := Nat.mul_le_mul_left (2^(m+1)) inject
  have hfull := Nat.mul_le_mul_left (m+2) full
  rw [Nat.mul_add,Nat.add_mul] at hfull
  have he : 2^(m+1)*originalSuccess = 2*(2^m*originalSuccess) := by
    rw [Nat.pow_succ]; ac_rfl
  have hS' : (m+2)*likelihoodMass qs ≤ 2^(m+1)*originalSuccess + chargeMass qs := by omega
  rw [he] at hS'
  omega

/-- The first-stop endpoint partitions into success, failure and
no stop by the fixed horizon, even without post-stop absorption. -/
theorem partition_terminalMass {β : Type} {n : Nat} (next : β → Fin n → β)
    (done event : β → Prop) (x : β) (t : Nat) :
    terminalMass next done event t x + terminalMass next done (fun y => ¬event y) t x +
      survival next (fun y => ¬done y) t x = n^t := by
  induction t generalizing x with
  | zero =>
    by_cases hd : done x <;> by_cases he : event x <;>
      simp [terminalMass,survival,weightedSurvival,hd,he]
  | succ t ih =>
    by_cases hd : done x
    · by_cases he : event x <;> simp [terminalMass,survival,weightedSurvival,hd,he]
    · simp only [terminalMass,survival,weightedSurvival,hd,if_false,not_false_eq_true,if_true]
      rw [←sAdd,←sAdd]
      have hh : (fun e => terminalMass next done event t (next x e) +
          terminalMass next done (fun y => ¬event y) t (next x e) +
          weightedSurvival next (fun y => ¬done y) (fun _ => 1) t (next x e)) =
          (fun _ : Fin n => n^t) := funext (fun e => ih (next x e))
      rw [hh,sConst,Nat.pow_succ']

/-- Interface for controlled first-stop likelihood: at each finite
horizon provide the charges of distinct successful effective words,
including arbitrary suffixes after stopping. Their powers of two are
the controlled raw preimage counts. This result removes the controlled
unfinished mass and gives the all-horizon *original* failure bound
needed by `UniformAttempt`. No independence of repeated trials. -/
theorem failure_of_controlled_words {β γ : Type} {n : Nat}
    (original : β → Fin n → β) (done goal : β → Prop) (x : β)
    (control : γ → Fin n → γ) (controlDone : γ → Prop) (z : γ)
    (hn : 0<n) (m A : Nat)
    (mean : IIDExpectedHittingTimeAtMost control controlDone z A)
    (words : ∀ t : Nat, ∃ qs : List Nat,
      n^t ≤ likelihoodMass qs + survival control (fun y => ¬controlDone y) t z ∧
      chargeMass qs ≤ m*n^t ∧ qs.length ≤ terminalMass original done goal t x) :
    ∀ t, 2^m*terminalMass original done (fun y => ¬goal y) t x ≤ (2^m-1)*n^t := by
  apply failure_bound_of_vanishing_remainder original done _ x control controlDone z hn
    (2^m) A (m+2) mean
  intro t
  obtain ⟨qs,hfull,hcharge,hinj⟩ := words t
  have hs := controlled_success_of_charge_bound m (n^t) _ _ qs hfull hcharge hinj
  have hp := Nat.mul_le_mul_left (2^m) (show terminalMass original done goal t x +
      terminalMass original done (fun y => ¬goal y) t x ≤ n^t by
    rw [←partition_terminalMass original done goal x t]
    exact Nat.le_add_right ..)
  rw [Nat.mul_add] at hp
  have hpow : 0 < (2:Nat)^m := Nat.pow_pos (by decide)
  have he : (2^m-1)*n^t+n^t = 2^m*n^t := by
    have heq : ((2:Nat)^m-1).succ=(2:Nat)^m := by omega
    rw [←Nat.succ_mul,heq]
  omega

end L4.TripleRenewal
#print axioms L4.TripleRenewal.expected_of_uniform_attempts
#print axioms L4.TripleRenewal.expected_with_preparation
#print axioms L4.TripleRenewal.consecutiveRootClock_of_interfaces
#print axioms L4.TripleRenewal.quarter_overrun
#print axioms L4.TripleRenewal.failure_bound_of_vanishing_remainder

#print axioms L4.TripleRenewal.controlled_success_of_charge_bound

#print axioms L4.TripleRenewal.failure_of_controlled_words
