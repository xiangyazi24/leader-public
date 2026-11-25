import Leader.L4.RankEndpoint

/-! # From stopped attempts to uniform raw blocks -/
namespace L4.RankPhysical
open TaggedTail RankRenewal Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun j : Fin n => f j.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc, ih, Nat.succ_mul, Nat.add_comm]

private theorem sMono {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sSucc f, sSucc g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc, sSucc f, sSucc g, ih]; omega

private theorem sSelector {n : Nat} (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz, sConst]
      simp
    · rw [sSucc, if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then a else 0) =
          (fun e : Fin n => if e = j then a else 0) := by funext e; simp
      rw [hc, ih, Nat.zero_add]

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e) = a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]


/-- Finite-word Markov inequality with no real-valued probability or
limiting argument. A word which is still live pays all its marks. -/
theorem horizon_mul_survival_le_cost {α : Type} {n : Nat} (next : α → Fin n → α)
    (target : α → Prop) (t : Nat) (x : α) :
    t * survival next (fun y => ¬ target y) t x ≤ iidHitCost next target t x := by
  have hm : ∀ u x, survival next (fun y => ¬ target y) u x ≤ n^u := by
    intro u
    induction u with
    | zero =>
      intro x
      by_cases h : target x <;> simp [survival,weightedSurvival,h]
    | succ u ih =>
      intro x
      by_cases h : target x
      · simp [survival,weightedSurvival,h]
      · simp only [survival,weightedSurvival,h,not_false_eq_true,if_true] at *
        have hh := sMono (fun e => weightedSurvival next (fun y => ¬ target y) (fun _ => 1) u (next x e))
          (fun _ => n^u) (fun e => ih (next x e))
        rw [sConst] at hh
        simpa only [Nat.pow_succ',Nat.mul_comm] using hh
  induction t generalizing x with
  | zero => simp [iidHitCost]
  | succ t ih =>
    by_cases h : target x
    · simp [iidHitCost,survival,weightedSurvival,h]
    · rw [iidHitCost,if_neg h]
      let z := survival next (fun y => ¬ target y) (t+1) x
      have hz : z = sumEdge (fun e => survival next (fun y => ¬ target y) t (next x e)) := by
        simp [z,survival,weightedSurvival,h]
      have hstep : t*z ≤ sumEdge (fun e => iidHitCost next target t (next x e)) := by
        rw [hz,← sScale]
        exact sMono _ _ (fun e => ih (next x e))
      have hprob : z ≤ n^(t+1) := hm (t+1) x
      change (t+1)*z ≤ n^(t+1) + sumEdge (fun e => iidHitCost next target t (next x e))
      rw [Nat.add_mul,Nat.one_mul]
      omega

private noncomputable def indicator {α : Type} (test : α → Prop) (x : α) : Nat :=
  if test x then 1 else 0

private theorem endpoint_zero_if {α : Type} {n : Nat} (next : α → Fin n → α)
    (live : α → Prop) (habsorb : ∀ x e, live (next x e) → live x)
    (t : Nat) (x : α) (hx : ¬ live x) :
    endpointSum next (indicator live) t x = 0 := by
  induction t generalizing x with
  | zero => simp [endpointSum,indicator,hx]
  | succ t ih =>
    simp only [endpointSum]
    have hh : (fun e => endpointSum next (indicator live) t (next x e)) = fun _ : Fin n => 0 :=
      funext fun e => ih (next x e) (fun h => hx (habsorb x e h))
    rw [hh,sConst,Nat.mul_zero]

private theorem endpoint_live_eq_survival {α : Type} {n : Nat} (next : α → Fin n → α)
    (live : α → Prop) (habsorb : ∀ x e, live (next x e) → live x)
    (t : Nat) (x : α) :
    endpointSum next (indicator live) t x = survival next live t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hx : live x
    · simp only [endpointSum,survival,weightedSurvival,if_pos hx]
      exact congrArg sumEdge (funext (fun e => ih (next x e)))
    · rw [endpoint_zero_if next live habsorb _ x hx]
      simp [survival,weightedSurvival,hx]

private theorem endpoint_union_budget {α : Type} {n : Nat} (next : α → Fin n → α)
    (a b c : α → Prop) (h : ∀ x, a x → b x ∨ c x)
    (t : Nat) (x : α) :
    endpointSum next (indicator a) t x ≤ endpointSum next (indicator b) t x +
      endpointSum next (indicator c) t x := by
  induction t generalizing x with
  | zero =>
    by_cases ha : a x
    · obtain hb | hc := h x ha
      · simp [endpointSum,indicator,ha,hb]
      · simp [endpointSum,indicator,ha,hc]
    · simp [endpointSum,indicator,ha]
  | succ t ih =>
    simp only [endpointSum,← sAdd]
    exact sMono _ _ (fun e => ih (next x e))

/-- A stopped attempt with uniform mean K and failure mass at most 1/4
supplies probability at least 1/2 of physical success within 4K raw
marks. This is the truncation needed before renewing, not independence
between attempts. -/
theorem halfBlock_of_stopped_attempt {α : Type} {n : Nat} (next : α → Fin n → α)
    (live done failed : α → Prop)
    (hLive : ∀ x e, live (next x e) → live x)
    (hDone : ∀ x e, done x → done (next x e))
    (hFailure : ∀ x, live x → done x → failed x)
    (K : Nat) (hK : 0<K) (x : α)
    (hCost : IIDExpectedHittingTimeAtMost next done x K)
    (hBad : 4 * endpointSum next (indicator failed) (4*K) x ≤ n^(4*K)) :
    2 * survival next live (4*K) x ≤ n^(4*K) := by
  have hsplit := endpoint_union_budget next live (fun y => ¬done y) failed
    (fun y h => by by_cases h' : done y; exact Or.inr (hFailure _ h h'); exact Or.inl h')
    (4*K) x
  rw [endpoint_live_eq_survival next live hLive,
    endpoint_live_eq_survival next (fun y => ¬done y) (fun y e h' hy => h' (hDone y e hy))] at hsplit
  have hMean := Nat.le_trans (horizon_mul_survival_le_cost next done (4*K) x) (hCost (4*K))
  have hTail : 4 * survival next (fun y => ¬ done y) (4*K) x ≤ n^(4*K) := by
    rw [show 4*K*survival next (fun y => ¬done y) (4*K) x =
      K*(4*survival next (fun y => ¬done y) (4*K) x) by ac_rfl] at hMean
    exact Nat.le_of_mul_le_mul_left hMean hK
  omega

/-- One stopped attempt projected onto literal raw scheduler marks.
The finite failure numerator is counting endpoints of one length-four-K
experiment; the attempt's failure bit can remain frozen while the
physical rows continue. No abstract repeated-attempt law is required. -/
structure RestartTrial {p c n : Nat} (x : Config p c n) (K : Nat) where
  State : Type
  start : State
  next : State → Fin n → State
  project : State → Config p c n
  done : State → Prop
  failed : State → Prop
  initial : project start = x
  projectStep : ∀ y e, project (next y e) = step (project y) e
  quiet : ∀ y, QuietEntrance (project y)
  doneAbsorbs : ∀ y e, done y → done (next y e)
  terminalFailure : ∀ y, rank x ≤ rank (project y) → done y → failed y
  mean : IIDExpectedHittingTimeAtMost next done start K
  failureMass : 4 * endpointSum next (indicator failed) (4*K) start ≤ n^(4*K)

/-- Exact remaining stopped-attempt premise for the proof route:
compose rootless activation, at most two stale supplier pushes, native
kill and one protected fresh push, with uniform mean coefficient and
one-attempt premature-birth numerator. -/
def ConcreteRestartTrial : Prop :=
  ∀ c : Nat, 12 ≤ c → ∃ A : Nat, 0 < A ∧
    ∀ {p n : Nat} (x : Config p c n),
      2 ≤ p → 4 ≤ n → (¬ p ∣ n) → QuietEntrance x → 2 ≤ rank x →
        Nonempty (RestartTrial x (A*n^2))

theorem block_of_restartTrial (h : ConcreteRestartTrial) : ConcreteRetirementBlock := by
  intro c hc
  obtain ⟨A,hA,hcert⟩ := h c hc
  refine ⟨4*A,by omega,?_⟩
  intro p n x hp hn hnd hx hr
  obtain ⟨C⟩ := hcert x hp hn hnd hx hr
  let live := fun y : C.State => rank x ≤ rank (C.project y)
  have hLive (y : C.State) (e : Fin n) (h : live (C.next y e)) : live y := by
    unfold live at h ⊢
    rw [C.projectStep] at h
    exact Nat.le_trans h (rank_step_le hn _ e (C.quiet y).1)
  have hK : 0<A*n^2 := Nat.mul_pos hA (Nat.pow_pos (by omega))
  have hh := halfBlock_of_stopped_attempt C.next live C.done C.failed hLive
    C.doneAbsorbs C.terminalFailure (A*n^2) hK C.start C.mean C.failureMass
  unfold live at hh
  rw [equal_survival_of_projection step C.next (fun y => rank x ≤ rank y)
    C.project C.projectStep, C.initial] at hh
  simpa only [Nat.mul_assoc] using hh

theorem boundedRank_of_restartTrial (h : ConcreteRestartTrial) : ConcreteBoundedRank :=
  boundedRank_of_block (block_of_restartTrial h)

end L4.RankPhysical

#print axioms L4.RankPhysical.horizon_mul_survival_le_cost
#print axioms L4.RankPhysical.halfBlock_of_stopped_attempt

#print axioms L4.RankPhysical.block_of_restartTrial
#print axioms L4.RankPhysical.boundedRank_of_restartTrial
