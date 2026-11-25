import Leader.L4.WindowScopedModerate

namespace L4.WindowScopedModerateRestart
open WindowScopedModerate WindowScopedRace TripleVulnerable TriplePhase TripleRenewal
open TripleCylinder TaggedTail Classical
variable {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
  {s : Fin n} {a b : Nat}
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
def literalTrialNext (C : Context initial group cert s a b) (z : Trial p c n) (e : Fin n) :
    Trial p c n :=
  ⟨physicalStep C z.phys e,
    z.leave || !(allowed (fun x => x.right.isReady) (liftedSite s (a+1)) z.phys e)⟩

private theorem coupled_step (C : Context initial group cert s a b) (z : Trial p c n)
    (e : Fin n) (hz : ¬ trialHit z) :
    literalTrialNext C z e = trialNext C z e := by
  have hl := Bool.eq_false_iff.mpr (fun h => hz (Or.inr h))
  have hs := Bool.eq_false_iff.mpr (fun h => hz (Or.inl h))
  simp [literalTrialNext,trialNext,hl,hs]

private theorem cost_eq (C : Context initial group cert s a b) (t : Nat) (z : Trial p c n) :
    iidHitCost (literalTrialNext C) trialHit t z =
    iidHitCost (trialNext C) trialHit t z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    by_cases h : trialHit z <;> simp [iidHitCost,h,coupled_step,ih]

private theorem mass_eq (C : Context initial group cert s a b) (t : Nat) (z : Trial p c n) :
    terminalMass (literalTrialNext C) trialHit (fun y => y.phys.exited≠true) t z =
    terminalMass (trialNext C) trialHit (fun y => y.phys.exited≠true) t z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    by_cases h : trialHit z
    · simp only [terminalMass,h,if_true]
    · simp only [terminalMass,h,if_false,coupled_step C z _ h,ih]

/-- A waiting or running literal trial, with no reset or change of raw marks. -/
inductive RState (p c n : Nat) where
  | waiting : WindowScopedRace.State p c n → RState p c n
  | attack : Trial p c n → RState p c n

def physical {p c n} : RState p c n → WindowScopedRace.State p c n
  | .waiting x => x
  | .attack z => z.phys

noncomputable def enter {p c n} (x : WindowScopedRace.State p c n) : RState p c n :=
  if WindowScopedDummy.entered x then .attack ⟨x,false⟩ else .waiting x

noncomputable def runNext (C : Context initial group cert s a b) : RState p c n → Fin n → RState p c n
  | .waiting x,e => enter (physicalStep C x e)
  | .attack z,e => .attack (literalTrialNext C z e)

def done {p c n} : RState p c n → Prop
  | .waiting _ => False
  | .attack z => trialHit z

private theorem enter_physical {p c n} (x : WindowScopedRace.State p c n) : physical (enter x)=x := by
  unfold enter
  split <;> rfl

private theorem step_project (C : Context initial group cert s a b) (z : RState p c n) (e : Fin n) :
    project (physical (runNext C z e))=cursorNext group cert (project (physical z)) e := by
  cases z with
  | waiting x => exact congrArg project (enter_physical _)
  | attack x => rfl

private theorem attack_cost (C : Context initial group cert s a b) (t : Nat) (z : Trial p c n) :
    iidHitCost (runNext C) done t (.attack z)=iidHitCost (trialNext C) trialHit t z := by
  rw [←cost_eq]
  induction t generalizing z with
  | zero => rfl
  | succ t ih => simp [iidHitCost,runNext,done,ih]

private theorem attack_mass (C : Context initial group cert s a b) (t : Nat) (z : Trial p c n) :
    terminalMass (runNext C) done (fun y => (physical y).exited≠true) t (.attack z)=
      terminalMass (trialNext C) trialHit (fun y => y.phys.exited≠true) t z := by
  rw [←mass_eq]
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    by_cases h : trialHit z
    · simp only [terminalMass,done,h,if_true,physical]
      rfl
    · simp only [terminalMass,done,h,if_false,runNext,ih]

private theorem fresh_good (C : Context initial group cert s a b) (x : WindowScopedRace.State p c n)
    (hg : C.Good x) (hs : x.exited=false)
    (hp : x.right=.forward .dummy 0) : WindowScopedModerate.Good C x := by
  exact .inr ⟨hg.resolve_left (by simp [hs]),by simp [DummyCycle,hp]⟩

private theorem moderate_failure (C : Context initial group cert s a b)
    (hb : 1≤b) (ha : a+1≤2*(b+1)) :
    ∀ t (x : WindowScopedRace.State p c n), C.Good x →
      64*terminalMass (runNext C) done (fun y => (physical y).exited≠true) t
        (enter x) ≤ 63*n^t := by
  intro t
  induction t with
  | zero =>
    intro x hx
    by_cases he : WindowScopedDummy.entered x
    · rcases he with hs|hp
      · simp [enter,WindowScopedDummy.entered,hs,terminalMass,physical]
      · by_cases hs : x.exited=true
        · simp [enter,WindowScopedDummy.entered,hs,terminalMass,physical]
        · have hf := Bool.eq_false_iff.mpr hs
          simp [enter,WindowScopedDummy.entered,hp,terminalMass,done,trialHit,physical,hf]
    · simp [enter,he,terminalMass,done]
  | succ t ih =>
    intro x hx
    by_cases he : WindowScopedDummy.entered x
    · rw [enter,if_pos he]
      by_cases hs : x.exited=true
      · simp [terminalMass,done,trialHit,physical,hs]
      · have hf := Bool.eq_false_iff.mpr hs
        have hp := he.resolve_left hs
        rw [attack_mass C]
        exact (moderate_trial_from_fresh_dummy C hb ha x
          (fresh_good C x hx hf hp) hf hp).2 _
    · rw [enter,if_neg he,terminalMass]
      rw [if_neg (show ¬done (.waiting x) from id),←sum_scale]
      simp only [runNext]
      have H := sum_le _ (fun _ : Fin n => 63*n^t)
        (fun e => ih _ (C.good_step x e hx))
      rw [sum_const,Nat.mul_comm n,Nat.mul_assoc,←Nat.pow_succ] at H
      exact H



/-- Scope-preserving moderate trial. A redirected comparison word
only provides the bound; the executable trial always applies the
actual next pair, including the failed mark and its successors. -/
noncomputable def moderateAttempt (C : Context initial group cert s a b)
    (hb : 1≤b) (ha : a+1≤2*(b+1)) (z : Cursor p c n)
    (x : WindowScopedRace.State p c n) (h : C.Holds x)
    (hP : project x=z) (hs : ¬Cursor.exit z) :
    UniformAttempt (cursorNext group cert) Cursor.exit C.Certified
      (n*(5*(a+1)+4*(b+1))) 64 z := by
  have hA : C.Good x := Or.inr h
  have hex : x.exited≠true := by
    intro he; apply hs
    rw [←hP]; exact he
  refine ⟨⟨RState p c n,enter x,runNext C,fun y => project (physical y),done,
    fun y => C.Good (physical y),?_,step_project C,?_,?_⟩,?_,?_,?_,?_⟩
  · rwa [enter_physical]
  · simpa only [enter_physical] using hA
  · intro y e hy
    have h' : physical (runNext C y e)=physicalStep C (physical y) e := by
      cases y with
      | waiting y => exact enter_physical _
      | attack y => rfl
    rw [h']
    exact C.good_step _ _ hy
  · change ¬done (enter x)
    unfold enter
    split
    · simpa [done,trialHit] using hex
    · exact id
  · intro y hy _ hz
    have H := hy.resolve_left hz
    exact ⟨(physical y).left,(physical y).right,H.1,⟨H.2.base,H.2.left,H.2.right,H.2.leftPhase,H.2.rightPhase⟩⟩
  · have before : IIDExpectedHittingTimeAtMost (physicalStep C) WindowScopedDummy.entered
      x (n*(4*b+3)) := WindowScopedDummy.mean C (by omega) x hA
    have H := RestartSerial.stage_mean (runNext C) (physicalStep C) enter done
      WindowScopedDummy.entered C.Good
      (by intro u e _ hu; simp [enter,hu,runNext])
      (fun u e h _ => C.good_step u e h)
      (n*(4*b+3)) (n*(5*(a+1)-2)) x hA before
      (by
        intro u hU he t
        rw [enter,if_pos he,attack_cost C]
        by_cases ht : u.exited=true
        · rw [iidHitCost_of_target _ trialHit _ (Or.inl ht : trialHit ⟨u,false⟩)]
          exact Nat.zero_le _
        · have hf := Bool.eq_false_iff.mpr ht
          have hp := he.resolve_left ht
          exact (moderate_trial_from_fresh_dummy C hb ha u
            (fresh_good C u hU hf hp) hf hp).1 t)
    apply expected_mono H
    rw [←Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  · intro t
    exact moderate_failure C hb ha t x hA

/-- Moderate clock on the actual cursor with no local-success premise. -/
theorem mean (C : Context initial group cert s a b)
    (hb : 1≤b) (ha : a+1≤2*(b+1)) (z : Cursor p c n) (hz : C.Certified z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) Cursor.exit z
      (64*(n*(5*(a+1)+4*(b+1)))) := by
  apply expected_of_uniform_attempts _ _ C.Certified _ 64 (by decide) _ z hz
  intro u hu he
  obtain ⟨l,r,h⟩ := hu
  exact ⟨moderateAttempt C hb ha u ⟨u.1,l,r,.seek,u.2⟩ h rfl he⟩

end L4.WindowScopedModerateRestart

#print axioms L4.WindowScopedModerateRestart.mean
