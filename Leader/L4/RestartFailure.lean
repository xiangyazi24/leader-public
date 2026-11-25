import Leader.L4.RestartMachine
import Leader.L4.FreshFailure

namespace L4.RestartFailure
open RestartMachine RankPhysical RankSupplier FreshEpochEarly TaggedTail TripleResidual Classical

abbrev Obs (p c n r : Nat) := {s : RestartMachine.State p c n r // rank s.config≤r}

/-- A stage boundary is valid before the single fresh epoch, or on
its authentic post-kill entry. Interior fresh states are handled by
the physical coupling, not by reinitializing the budget. -/
def BoundaryGood {p c n r : Nat} {x : Config p c n} : Mode r x → Prop
  | .protect v d _ => freshInit x v d
  | .failed => False
  | _ => True

def PreFresh {p c n r : Nat} {x : Config p c n} : Mode r x → Prop
  | .protect .. => False
  | .failed => False
  | _ => True

noncomputable def failScore {p c n r : Nat} (s : Obs p c n r) : Nat :=
  if failedMode s.val.mode then 1 else 0

theorem fromKill_good {p c n r : Nat} (hn : 4≤n)
    (x : Config p c n) (e : Fin n) (hq : QuietEntrance x)
    (hd : death x e=true) (hr : retirement x e=false) :
    BoundaryGood (fromKill (r:=r) hn x e hq hd hr) := by
  unfold fromKill
  dsimp only [BoundaryGood]
  have h := Classical.choose_spec (Classical.choose_spec (RestartRouting.transition_after_kill hn x e hq hd hr))
  exact Eq.mp (congrArg (fun y => freshInit y _ _) h.1) h.2.2

theorem fromEntry_good {p c n r : Nat} {x : Config p c n}
    (m : RestartRouting.NativeEntry x) : BoundaryGood (fromEntry (r:=r) m) := by
  cases m <;> trivial

theorem stepActive_boundary {p c n r : Nat} (P : Params p c n r)
    (x : Config p c n) (e : Fin n) (hq : QuietEntrance x)
    (hx : rank x≤r) (hy : ¬rank (step x e)<r)
    (mode : Mode r x) (h : PreFresh mode) :
    BoundaryGood (stepActive P x e hq hx hy mode) := by
  cases mode <;> simp only [PreFresh] at h
  all_goals simp only [stepActive]
  · split
    · trivial
    · apply fromEntry_good
  · rename_i v d hL
    split
    · apply fromKill_good
    · split
      · trivial
      · apply fromEntry_good
  · split
    · apply fromKill_good
    · split <;> trivial
  · split
    · apply fromKill_good
    · trivial
  · trivial

theorem next_boundary {p c n r : Nat} (P : Params p c n r)
    (s : Obs p c n r) (e : Fin n) (h : PreFresh s.val.mode) :
    BoundaryGood (next P s e).val.mode := by
  have hf : failedMode s.val.mode=false := by
    rcases s with ⟨⟨x,hq,mode⟩,hs⟩
    cases mode <;> simp_all [PreFresh,failedMode]
  simp only [next,hf,Bool.false_eq_true,if_false]
  split
  · trivial
  · exact stepActive_boundary P _ e _ _ _ s.val.mode h

open RankRenewal in
/-- Glue a single, adapted entry to a uniformly budgeted continuation.
Pre-entry branches may take arbitrarily many raw marks. -/
theorem failure_at_boundary {α : Type} {n : Nat} (step : α → Fin n → α)
    (score : α → Nat) (pre good : α → Prop)
    (hzero : ∀ x, pre x → score x=0)
    (hkeep : ∀ x e, pre x → good (step x e))
    (hcont : ∀ x, good x → ¬pre x → ∀ t, 1000*endpointSum step score t x≤11*n^t)
    (x : α) (t : Nat) (hx : good x) :
    1000*endpointSum step score t x≤11*n^t := by
  have cres {m : Nat} (f : Fin m → Nat) (a : Nat) :
      (∀ e,1000*f e≤a) → 1000*sumEdge f≤m*a := by
    induction m with
    | zero => simp [sumEdge]
    | succ m ih =>
      intro h
      have hS : sumEdge f=f 0+sumEdge (fun i : Fin m => f i.succ) := by simp [sumEdge,List.ofFn_succ]
      rw [hS,Nat.mul_add]
      have hR : (m+1)*a=a+m*a := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
      rw [hR]
      exact Nat.add_le_add (h 0) (ih _ fun i => h i.succ)
  induction t generalizing x with
  | zero =>
    by_cases hp : pre x
    · simp [endpointSum,hzero x hp]
    · exact hcont x hx hp 0
  | succ t ih =>
    by_cases hp : pre x
    · simp only [endpointSum]
      rw [Nat.pow_succ',← Nat.mul_assoc,Nat.mul_comm 11 n,Nat.mul_assoc]
      exact cres _ _ (fun e => ih _ (hkeep x e hp))
    · exact hcont x hx hp (t+1)

/-- A physical retired state may ignore the pure fresh observer; otherwise
the tracked live pair agrees exactly, or both observers have failed. -/
def Coupled {p c n r : Nat} (v : Fin n) (s : Obs p c n r)
    (z : FreshFailure.Phase p c n) : Prop :=
  match s.val.mode, z with
  | .retired _, _ => True
  | .failed, .failed _ => True
  | .protect u d _, .live z => u=v ∧ z=RankSupplier.init s.val.config d
  | _, _ => False

theorem coupled_score {p c n r : Nat} (v : Fin n) (s : Obs p c n r)
    (z : FreshFailure.Phase p c n) (h : Coupled v s z) :
    failScore s ≤ if FreshFailure.Failure z then 1 else 0 := by
  rcases s with ⟨⟨x,hq,mode⟩,hx⟩
  cases mode <;> cases z <;> simp_all [Coupled,failScore,failedMode,FreshFailure.Failure]

theorem protect_bound_of_step {p c n r : Nat} (P : Params p c n r)
    (hs : ∀ v (s : Obs p c n r) z e, Coupled v s z →
      Coupled v (next P s e) (FreshFailure.freshNext v z e))
    (v : Fin n) (d : Nat) (x : Config p c n) (hq : QuietEntrance x) (hx : rank x≤r)
    (hp : Protected v (RankSupplier.init x d)) (hi : freshInit x v d) (t : Nat) :
    1000*RankRenewal.endpointSum (next P) failScore t ⟨⟨x,hq,.protect v d hp⟩,hx⟩≤11*n^t := by
  let s : Obs p c n r := ⟨⟨x,hq,.protect v d hp⟩,hx⟩
  let z := FreshFailure.Phase.live (RankSupplier.init x d)
  have lift (w : List (Fin n)) (s' : Obs p c n r) (z' : FreshFailure.Phase p c n)
      (hh : Coupled v s' z') :
      Coupled v (GGTiming.runMarks (next P) s' w) (GGTiming.runMarks (FreshFailure.freshNext v) z' w) := by
    induction w generalizing s' z' with
    | nil => exact hh
    | cons e w ih => exact ih _ _ (hs _ _ _ _ hh)
  refine Nat.le_trans (Nat.mul_le_mul_left _ ?_) (FreshFailure.fresh_failure_mass
    P.size P.calibration v (RankSupplier.init x d) hp hq.2.1 hi t)
  exact RankRace.endpointSum_le_of_common_words _ _ _ _ s z
    (fun w => coupled_score _ _ _ (lift w s z ⟨rfl,rfl⟩)) t

/-- The literal outer observer and the fresh observer share the same
marked pairs. The outer rank test can end the trial earlier, but cannot
add a failure. -/
theorem coupled_step {p c n r : Nat} (P : Params p c n r) (v : Fin n)
    (s : Obs p c n r) (z : FreshFailure.Phase p c n) (e : Fin n)
    (h : Coupled v s z) :
    Coupled v (next P s e) (FreshFailure.freshNext v z e) := by
  rcases s with ⟨⟨x,hq,mode⟩,hx⟩
  cases mode with
  | retired hr =>
    have hR := Nat.lt_of_le_of_lt (rank_step_le P.size x e hq.1) hr
    simp only [next,failedMode,Bool.false_eq_true,if_false,dif_pos hR]
    cases FreshFailure.freshNext v z e <;> trivial
  | failed =>
    cases z <;> simp_all [Coupled, next, failedMode, FreshFailure.freshNext]
  | search _ => cases z <;> exact False.elim h
  | first _ _ _ => cases z <;> exact False.elim h
  | second _ _ _ _ _ _ _ => cases z <;> exact False.elim h
  | deletion _ _ _ _ => cases z <;> exact False.elim h
  | protect u d hp =>
    cases z with
    | retired | failed _ => exact False.elim h
    | live z =>
      change u=v ∧ z=RankSupplier.init x d at h
      rcases h with ⟨rfl,rfl⟩
      simp only [next,failedMode,Bool.false_eq_true,if_false]
      split
      · cases FreshFailure.freshNext u (.live (RankSupplier.init x d)) e <;> trivial
      · rename_i hY
        have hR := no_local_retirement P x e hq.1 hx hY
        change retirement (RankSupplier.init x d).config e=false at hR
        simp only [stepActive,FreshFailure.freshNext]
        by_cases hS : (advance u (RankSupplier.init x d) e).stopped=false
        · have hpj := (RankSupplierPhysical.unstopped_fields u e (RankSupplier.init x d) rfl hS).1
          have hEq : advance u (RankSupplier.init x d) e =
              RankSupplier.init (step x e) (advance u (RankSupplier.init x d) e).donor := by
            generalize advance u (RankSupplier.init x d) e = zz at hpj hS ⊢
            cases zz
            cases hpj
            cases hS
            rfl
          simp only [hR,hS,Bool.false_eq_true,if_false,dif_pos trivial,Coupled]
          exact ⟨trivial,hEq⟩
        · have hT : (advance u (RankSupplier.init x d) e).stopped=true := by simpa using hS
          simp only [hR,hT,Bool.false_eq_true,Bool.true_eq_false,if_false,dif_neg (not_false),if_true,Coupled]

theorem preFresh_zero {p c n r : Nat} (s : Obs p c n r)
    (h : PreFresh s.val.mode) : failScore s=0 := by
  rcases s with ⟨⟨x,hq,mode⟩,hx⟩
  cases mode <;> simp_all [PreFresh,failScore,failedMode]

open RankRenewal in
/-- Every horizon of the literal trial has failure probability at most
eleven per thousand, including the arbitrary random pre-fresh prefix. -/
theorem trial_failure_bound {p c n r : Nat} (P : Params p c n r)
    (s : Obs p c n r) (h : BoundaryGood s.val.mode) (t : Nat) :
    1000*endpointSum (next P) failScore t s≤11*n^t := by
  apply failure_at_boundary (next P) failScore
    (fun s => PreFresh s.val.mode) (fun s => BoundaryGood s.val.mode)
    preFresh_zero (next_boundary P) _ s t h
  intro z hz hnot k
  rcases z with ⟨⟨x,hq,mode⟩,hx⟩
  cases mode <;> simp only [PreFresh,BoundaryGood,not_true_eq_false] at hz hnot
  case protect v d hp =>
    exact protect_bound_of_step P (coupled_step P) v d x hq hx hp hz k

theorem start_preFresh {p c n : Nat} (x : Config p c n)
    (hq : QuietEntrance x) (hr : 2≤rank x) :
    PreFresh (start x hq hr).mode := by
  simp only [start]
  split
  · trivial
  · rename_i h
    generalize RestartRouting.afterActivation x hq.1 hr h = m
    cases m <;> trivial

theorem boundaryGood_of_preFresh {p c n r : Nat} {x : Config p c n}
    {m : Mode r x} (h : PreFresh m) : BoundaryGood m := by
  cases m <;> simp_all [PreFresh,BoundaryGood]

open RankRenewal in
/-- Ready-to-install failure field for RestartAttemptBudget.Observer at the
literal initial cut, at every raw horizon. -/
theorem start_failure_bound {p c n : Nat} (x : Config p c n)
    (hq : QuietEntrance x) (hr : 2≤rank x) (P : Params p c n (rank x))
    (t : Nat) :
    1000*endpointSum (next P) (fun s => if failedMode s.val.mode=true then 1 else 0)
      t ⟨start x hq hr,Nat.le_refl _⟩≤11*n^t :=
  trial_failure_bound P _ (boundaryGood_of_preFresh (start_preFresh x hq hr)) t

end L4.RestartFailure

