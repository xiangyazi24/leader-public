import Leader.L4.TripleDummyWait

namespace L4.TripleModerate
open TripleResidual TriplePhase TripleVulnerable TripleCycleCount TripleRenewal
open TripleCylinder TaggedTail Classical

private theorem sum_le {n} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h _) (ih _ _ fun e => h e.succ)

private theorem sum_const (n z : Nat) : sumEdge (fun _ : Fin n => z) = n*z := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    change (List.ofFn (fun _ : Fin (n+1) => z)).sum = _
    rw [List.ofFn_succ,List.sum_cons]
    change z + sumEdge (fun _ : Fin n => z) = _
    rw [ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_scale {n} (d : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => d*f e) = d*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    change d*f 0 + sumEdge (fun e : Fin n => d*f e.succ) =
      d*(f 0+sumEdge (fun e : Fin n => f e.succ))
    rw [ih,Nat.mul_add]

/-- Once auxiliary monitoring stops, the physical process still takes every raw mark. -/
def literalTrialNext {p c n} (s : Fin n) (a b : Nat) (z : Trial p c n) (e : Fin n) :
    Trial p c n :=
  ⟨effectiveNext s a b z.phys e,
    z.leave || !(allowed (fun x => x.right.isReady) (liftedSite s (a+1)) z.phys e)⟩

private theorem literal_keep {p c n} (hn : 4≤n) (s : Fin n) (a b : Nat)
    (x : Physical p c n) (e : Fin n) (h : TripleDummyWait.Admitted s a b x) :
    TripleDummyWait.Admitted s a b (effectiveNext s a b x e) := by
  rcases h with hs|⟨hm,hc,hp⟩
  · left; simp [effectiveNext,advance,hs]
  by_cases hs : x.obs.stopped=true
  · left; simp [effectiveNext,advance,hs]
  have hf := Bool.eq_false_iff.mpr hs
  by_cases he : event x.obs.config e=true
  · left; simp [effectiveNext,advance,hf,he]
  have he' := Bool.eq_false_iff.mpr he
  have H := paired_tick_literal hn x.obs.config s e hm hc x.left x.right hp he'
  have C := EntranceCover.cover_closed hn x.obs.config e ⟨hm,hc⟩
  right
  simpa [effectiveNext,advance,hf] using And.intro C.1 (And.intro C.2 H)

private theorem coupled_step {p c n} (s : Fin n) (a b : Nat) (z : Trial p c n)
    (e : Fin n) (hz : ¬ trialHit z) :
    literalTrialNext s a b z e = trialNext s a b z e := by
  have hl := Bool.eq_false_iff.mpr (fun h => hz (Or.inr h))
  have hs := Bool.eq_false_iff.mpr (fun h => hz (Or.inl h))
  simp [literalTrialNext,trialNext,hl,hs]

private theorem cost_eq {p c n} (s : Fin n) (a b : Nat) (t : Nat) (z : Trial p c n) :
    iidHitCost (literalTrialNext s a b) trialHit t z =
    iidHitCost (trialNext s a b) trialHit t z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    by_cases h : trialHit z <;> simp [iidHitCost,h,coupled_step,ih]

private theorem mass_eq {p c n} (s : Fin n) (a b : Nat) (t : Nat) (z : Trial p c n) :
    terminalMass (literalTrialNext s a b) trialHit (fun y => y.phys.obs.stopped≠true) t z =
    terminalMass (trialNext s a b) trialHit (fun y => y.phys.obs.stopped≠true) t z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    by_cases h : trialHit z
    · simp only [terminalMass,h,if_true]
    · simp only [terminalMass,h,if_false,coupled_step s a b z _ h,ih]

/-- A waiting or running literal trial, with no reset or change of raw marks. -/
inductive State (p c n : Nat) where
  | waiting : Physical p c n → State p c n
  | attack : Trial p c n → State p c n

def physical {p c n} : State p c n → Physical p c n
  | .waiting x => x
  | .attack z => z.phys

noncomputable def enter {p c n} (x : Physical p c n) : State p c n :=
  if TripleDummyWait.entered x then .attack ⟨x,false⟩ else .waiting x

noncomputable def next {p c n} (s : Fin n) (a b : Nat) : State p c n → Fin n → State p c n
  | .waiting x,e => enter (effectiveNext s a b x e)
  | .attack z,e => .attack (literalTrialNext s a b z e)

def done {p c n} : State p c n → Prop
  | .waiting _ => False
  | .attack z => trialHit z

private theorem enter_physical {p c n} (x : Physical p c n) : physical (enter x)=x := by
  unfold enter
  split <;> rfl

private theorem step_project {p c n} (s : Fin n) (a b : Nat) (z : State p c n) (e : Fin n) :
    (physical (next s a b z e)).obs=advance (physical z).obs e := by
  cases z with
  | waiting x => exact congrArg Physical.obs (enter_physical _)
  | attack x => rfl

private theorem attack_cost {p c n} (s : Fin n) (a b t : Nat) (z : Trial p c n) :
    iidHitCost (next s a b) done t (.attack z)=iidHitCost (trialNext s a b) trialHit t z := by
  rw [←cost_eq]
  induction t generalizing z with
  | zero => rfl
  | succ t ih => simp [iidHitCost,next,done,ih]

private theorem attack_mass {p c n} (s : Fin n) (a b t : Nat) (z : Trial p c n) :
    terminalMass (next s a b) done (fun y => (physical y).obs.stopped≠true) t (.attack z)=
      terminalMass (trialNext s a b) trialHit (fun y => y.phys.obs.stopped≠true) t z := by
  rw [←mass_eq]
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    by_cases h : trialHit z
    · simp only [terminalMass,done,h,if_true,physical]
      rfl
    · simp only [terminalMass,done,h,if_false,next,ih]

private theorem fresh_good {p c n} (s : Fin n) (a b : Nat) (x : Physical p c n)
    (hg : TripleDummyWait.Admitted s a b x) (hs : x.obs.stopped=false)
    (hp : x.right=.forward .dummy 0) : Good s a b x := by
  obtain ⟨hm,hc,hpair⟩ := hg.resolve_left (by simp [hs])
  exact Or.inr ⟨hm,hc,hpair,by simp [DummyCycle,hp]⟩

private theorem moderate_failure {p c n} (hn : 4≤n) (s : Fin n) (a b : Nat)
    (hb : 1≤b) (ha : a+1≤2*(b+1)) :
    ∀ t (x : Physical p c n), TripleDummyWait.Admitted s a b x →
      64*terminalMass (next s a b) done (fun y => (physical y).obs.stopped≠true) t
        (enter x) ≤ 63*n^t := by
  intro t
  induction t with
  | zero =>
    intro x hx
    by_cases he : TripleDummyWait.entered x
    · rcases he with hs|hp
      · simp [enter,TripleDummyWait.entered,hs,terminalMass,physical]
      · by_cases hs : x.obs.stopped=true
        · simp [enter,TripleDummyWait.entered,hs,terminalMass,physical]
        · have hf := Bool.eq_false_iff.mpr hs
          simp [enter,TripleDummyWait.entered,hp,terminalMass,done,trialHit,physical,hf]
    · simp [enter,he,terminalMass,done]
  | succ t ih =>
    intro x hx
    by_cases he : TripleDummyWait.entered x
    · rw [enter,if_pos he]
      by_cases hs : x.obs.stopped=true
      · simp [terminalMass,done,trialHit,physical,hs]
      · have hf := Bool.eq_false_iff.mpr hs
        have hp := he.resolve_left hs
        rw [attack_mass]
        exact (moderate_trial_from_fresh_dummy hn s a b hb ha x
          (fresh_good s a b x hx hf hp) hf hp).2 _
    · rw [enter,if_neg he,terminalMass]
      rw [if_neg (show ¬done (.waiting x) from id),←sum_scale]
      simp only [next]
      have H := sum_le _ (fun _ : Fin n => 63*n^t)
        (fun e => ih _ (literal_keep hn s a b x e hx))
      rw [sum_const,Nat.mul_comm n,Nat.mul_assoc,←Nat.pow_succ] at H
      exact H

/-- A sealed pair in moderate geometry admits an original-scheduler restart
attempt. A suppressed outgoing-edge observation ends the attempt, but does
not suppress that physical transition or any later raw mark. -/
noncomputable def moderateAttempt {p c n} (hn : 4≤n) (s : Fin n) (a b : Nat)
    (hb : 1≤b) (ha : a+1≤2*(b+1)) (x : Obs p c n)
    (hx : MCOV x.config ∧ COV x.config ∧ ∃ l r, Paired x.config s a b l r)
    (hs : x.stopped≠true) :
    UniformAttempt advance (fun u => u.stopped=true)
      (fun u => MCOV u.config ∧ COV u.config ∧ ∃ l r, Paired u.config s a b l r)
      (n*(5*(a+1)+4*(b+1))) 64 x := by
  let z : Physical p c n := ⟨x,hx.2.2.choose,hx.2.2.choose_spec.choose⟩
  have hA : TripleDummyWait.Admitted s a b z :=
    Or.inr ⟨hx.1,hx.2.1,hx.2.2.choose_spec.choose_spec⟩
  refine ⟨⟨State p c n,enter z,next s a b,fun y => (physical y).obs,done,
    fun y => TripleDummyWait.Admitted s a b (physical y),?_,step_project s a b,?_,?_⟩,
    ?_,?_,?_,?_⟩
  · rw [enter_physical]
  · simpa only [enter_physical] using hA
  · intro y e hy
    have h : physical (next s a b y e)=effectiveNext s a b (physical y) e := by
      cases y with
      | waiting y => exact enter_physical _
      | attack y => rfl
    rw [h]
    exact literal_keep hn s a b _ _ hy
  · change ¬ done (enter z)
    unfold enter
    split
    · simpa [done,trialHit,z] using hs
    · exact id
  · intro y hy _ h
    obtain ⟨hm,hc,hp⟩ := hy.resolve_left h
    exact ⟨hm,hc,_,_,hp⟩
  · have before := TripleDummyWait.wait_fresh_dummy_mean hn s a b (by omega) z hA
    have H := RestartSerial.stage_mean (next s a b) (effectiveNext s a b) enter done
      TripleDummyWait.entered (TripleDummyWait.Admitted s a b)
      (by intro u e _ hu; simp [enter,hu,next])
      (fun u e h _ => literal_keep hn s a b u e h)
      (n*(4*b+3)) (n*(5*(a+1)-2)) z hA before
      (by
        intro u hU he t
        rw [enter,if_pos he,attack_cost]
        by_cases ht : u.obs.stopped=true
        · rw [iidHitCost_of_target _ trialHit _ (Or.inl ht : trialHit ⟨u,false⟩)]
          exact Nat.zero_le _
        · have hf := Bool.eq_false_iff.mpr ht
          have hp := he.resolve_left ht
          exact (moderate_trial_from_fresh_dummy hn s a b hb ha u
            (fresh_good s a b u hU hf hp) hf hp).1 t)
    apply expected_mono H
    rw [←Nat.mul_add]
    apply Nat.mul_le_mul_left
    omega
  · exact fun t => moderate_failure hn s a b hb ha t z hA

end L4.TripleModerate

#print axioms L4.TripleModerate.moderateAttempt
