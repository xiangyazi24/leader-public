import Leader.L4.Height.SyncAlt

namespace L4.Height

open L4.Compiler.Native

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

/-! ## Prefix states and monotonicity of the lifted counters -/

private theorem levelRunWord_append {m B M : Nat} (hm : 0 < m)
    (xs ys : List (Activation m)) (s : WordState m) :
    syncRun B M hm (xs ++ ys) s =
      syncRun B M hm ys (syncRun B M hm xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih =>
      change
        syncRun B M hm (xs ++ ys)
            (activate B M hm s e.1 e.2) =
          syncRun B M hm ys
            (syncRun B M hm xs (activate B M hm s e.1 e.2))
      exact ih (activate B M hm s e.1 e.2)

/-- State after exactly the activations with indices `0, ..., t-1`. -/
def levelStreamState {m : Nat} (B M : Nat) (hm : 0 < m)
    (szero : WordState m) (w : Nat → Activation m)
    (t : Nat) : WordState m :=
  syncRun B M hm ((List.range t).map w) szero

/-- Activation `w t` carries state index `t` to state index `t+1`. -/
theorem levelStreamState_succ {m : Nat} (B M : Nat) (hm : 0 < m)
    (szero : WordState m) (w : Nat → Activation m)
    (t : Nat) :
    levelStreamState B M hm szero w (Nat.succ t) =
      activate B M hm (levelStreamState B M hm szero w t)
        (w t).1 (w t).2 := by
  unfold levelStreamState
  rw [List.range_succ, List.map_append, levelRunWord_append]
  rfl

private theorem activate_lift_mono {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (owner : Fin m) (delta : Bool) (j : Fin m) :
    s.lift j ≤ (activate B M hm s owner delta).lift j := by
  by_cases hjo : j = owner
  · subst j
    cases hact : clockAction M hm s owner <;>
      simp [activate, hact, advanceLift] <;> omega
  · simp [activate, hjo]

/-- Lifted counters never decrease along any activation stream. This does not
need legitimacy: `advanceLift` either keeps the old value or adds one. -/
theorem lift_mono {m B M : Nat} (hm : 0 < m)
    (szero : WordState m) (w : Nat → Activation m) (j : Fin m) :
    ∀ {t t' : Nat}, t ≤ t' →
      (levelStreamState B M hm szero w t).lift j ≤
        (levelStreamState B M hm szero w t').lift j := by
  intro t t' htt
  induction t' generalizing t with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      exact Nat.le_refl _
  | succ n ih =>
      by_cases ht : t = Nat.succ n
      · subst t
        exact Nat.le_refl _
      · have htn : t ≤ n := by omega
        have hprev := ih htn
        have hstep :
            (levelStreamState B M hm szero w n).lift j ≤
              (levelStreamState B M hm szero w (Nat.succ n)).lift j := by
          rw [levelStreamState_succ B M hm szero w n]
          exact activate_lift_mono (B := B) (M := M) hm
            (levelStreamState B M hm szero w n)
            (w n).1 (w n).2 j
        exact Nat.le_trans hprev hstep

/-- Every prefix state of a legitimate stream is legitimate. -/
theorem levelStreamState_legit {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (t : Nat) :
    Legit M hm (levelStreamState B M hm szero w t) := by
  unfold levelStreamState
  exact syncRun_legit (B := B) hM hm ((List.range t).map w) szero hleg

/-! ## Core-only leftmost bounded search -/

/-- Least true Boolean at or below a finite bound. If none is true, the
function returns the bound; every use below supplies a proof that the bound
itself is true. -/
private def leastTrueUpToLevel (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let k := leastTrueUpToLevel p n
      if p k = true then k else n + 1

private theorem leastTrueUpToLevel_le (p : Nat → Bool) :
    ∀ n, leastTrueUpToLevel p n ≤ n := by
  intro n
  induction n with
  | zero =>
      simp [leastTrueUpToLevel]
  | succ n ih =>
      simp only [leastTrueUpToLevel]
      split
      · omega
      · omega

private theorem leastTrueUpToLevel_true_of_true_at (p : Nat → Bool) :
    ∀ n, p n = true → p (leastTrueUpToLevel p n) = true := by
  intro n hn
  cases n with
  | zero =>
      simpa only [leastTrueUpToLevel] using hn
  | succ n =>
      simp only [leastTrueUpToLevel]
      split
      next hprev => exact hprev
      next _ => exact hn

private theorem leastTrueUpToLevel_true_of_exists (p : Nat → Bool) :
    ∀ n, (∃ j, j ≤ n ∧ p j = true) →
      p (leastTrueUpToLevel p n) = true := by
  intro n
  induction n with
  | zero =>
      intro hex
      obtain ⟨j, hj, hpj⟩ := hex
      have hjzero : j = 0 := by omega
      subst j
      simpa only [leastTrueUpToLevel] using hpj
  | succ n ih =>
      intro hex
      simp only [leastTrueUpToLevel]
      split
      next hprev => exact hprev
      next hprev =>
        obtain ⟨j, hj, hpj⟩ := hex
        by_cases hjn : j ≤ n
        · have hfound := ih ⟨j, hjn, hpj⟩
          exact False.elim (hprev hfound)
        · have heq : j = n + 1 := by omega
          rw [← heq]
          exact hpj

private theorem leastTrueUpToLevel_min (p : Nat → Bool) :
    ∀ n j, j ≤ n → p j = true → leastTrueUpToLevel p n ≤ j := by
  intro n
  induction n with
  | zero =>
      intro j hj hpj
      simp only [leastTrueUpToLevel]
      omega
  | succ n ih =>
      intro j hj hpj
      simp only [leastTrueUpToLevel]
      split
      next hprev =>
        by_cases hjn : j ≤ n
        · exact ih j hjn hpj
        · have hk := leastTrueUpToLevel_le p n
          omega
      next hprev =>
        have hjnot : ¬ j ≤ n := by
          intro hjn
          have hfound := leastTrueUpToLevel_true_of_exists p n
            ⟨j, hjn, hpj⟩
          exact hprev hfound
        omega

/-! ## The next service at or after a state index -/

/-- Every site is activated again strictly after every index. This stronger
usual fairness form in particular supplies an activation at or after `t`. -/
abbrev FairActivationStream {m : Nat}
    (w : Nat → Activation m) : Prop :=
  ∀ i t, ∃ q, t < q ∧ (w q).1 = i

private def levelServiceTest {m : Nat}
    (w : Nat → Activation m) (i : Fin m)
    (t q : Nat) : Bool :=
  decide (t ≤ q ∧ (w q).1 = i)

private noncomputable def levelServiceUpper {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t : Nat) : Nat :=
  Classical.choose (hinf i t)

private theorem levelServiceUpper_spec {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t : Nat) :
    t < levelServiceUpper w hinf i t ∧
      (w (levelServiceUpper w hinf i t)).1 = i := by
  unfold levelServiceUpper
  exact Classical.choose_spec (hinf i t)

/-- Least activation index `q ≥ t` whose owner is `i`. -/
noncomputable def levelServiceIndex {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t : Nat) : Nat :=
  leastTrueUpToLevel (levelServiceTest w i t)
    (levelServiceUpper w hinf i t)

theorem levelServiceIndex_spec {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t : Nat) :
    t ≤ levelServiceIndex w hinf i t ∧
      (w (levelServiceIndex w hinf i t)).1 = i := by
  unfold levelServiceIndex
  have hu := levelServiceUpper_spec w hinf i t
  have hle : t ≤ levelServiceUpper w hinf i t := Nat.le_of_lt hu.1
  have htest :
      levelServiceTest w i t (levelServiceUpper w hinf i t) = true := by
    simp [levelServiceTest, hle, hu.2]
  have hfound := leastTrueUpToLevel_true_of_true_at
    (levelServiceTest w i t) (levelServiceUpper w hinf i t) htest
  unfold levelServiceTest at hfound
  exact of_decide_eq_true hfound

theorem levelServiceIndex_min {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t q : Nat)
    (hq : t ≤ q ∧ (w q).1 = i) :
    levelServiceIndex w hinf i t ≤ q := by
  unfold levelServiceIndex
  have hqtest : levelServiceTest w i t q = true := by
    simp [levelServiceTest, hq.1, hq.2]
  rcases Nat.le_total q (levelServiceUpper w hinf i t) with hqu | huq
  · exact leastTrueUpToLevel_min (levelServiceTest w i t)
      (levelServiceUpper w hinf i t) q hqu hqtest
  · exact Nat.le_trans
      (leastTrueUpToLevel_le (levelServiceTest w i t)
        (levelServiceUpper w hinf i t)) huq

/-- `S i t`: the state index immediately after the least activation of `i`
whose activation index is at least `t`. -/
noncomputable def levelServiceTime {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t : Nat) : Nat :=
  Nat.succ (levelServiceIndex w hinf i t)

/-- The compulsory activation makes `S i t` strictly later than state `t`. -/
theorem S_after {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t : Nat) :
    t < levelServiceTime w hinf i t := by
  have hs := (levelServiceIndex_spec w hinf i t).1
  unfold levelServiceTime
  omega

/-- Delaying the requested starting state cannot make the least service time
earlier. -/
theorem S_mono {m : Nat}
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (t t' : Nat) (htt : t ≤ t') :
    levelServiceTime w hinf i t ≤ levelServiceTime w hinf i t' := by
  have hs := levelServiceIndex_spec w hinf i t'
  have hcand : t ≤ levelServiceIndex w hinf i t' ∧
      (w (levelServiceIndex w hinf i t')).1 = i := by
    exact ⟨Nat.le_trans htt hs.1, hs.2⟩
  have hmin := levelServiceIndex_min w hinf i t
    (levelServiceIndex w hinf i t') hcand
  unfold levelServiceTime
  omega

/-! ## One service raises a locally attained level -/

private theorem next_level_after_service {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell t : Nat)
    (hleft :
      ell ≤ (levelStreamState B M hm szero w t).lift (left hm i))
    (hcenter : ell ≤ (levelStreamState B M hm szero w t).lift i)
    (hright :
      ell ≤ (levelStreamState B M hm szero w t).lift (right hm i)) :
    ell + 1 ≤
      (levelStreamState B M hm szero w
        (levelServiceTime w hinf i t)).lift i := by
  let q := levelServiceIndex w hinf i t
  have hqspec : t ≤ q ∧ (w q).1 = i := by
    dsimp [q]
    exact levelServiceIndex_spec w hinf i t
  have htime : levelServiceTime w hinf i t = Nat.succ q := by
    rfl
  have hleftq :
      ell ≤ (levelStreamState B M hm szero w q).lift (left hm i) :=
    Nat.le_trans hleft
      (lift_mono (B := B) (M := M) hm szero w (left hm i) hqspec.1)
  have hcenterq :
      ell ≤ (levelStreamState B M hm szero w q).lift i :=
    Nat.le_trans hcenter
      (lift_mono (B := B) (M := M) hm szero w i hqspec.1)
  have hrightq :
      ell ≤ (levelStreamState B M hm szero w q).lift (right hm i) :=
    Nat.le_trans hright
      (lift_mono (B := B) (M := M) hm szero w (right hm i) hqspec.1)
  have hlegq : Legit M hm (levelStreamState B M hm szero w q) :=
    levelStreamState_legit (B := B) hM hm szero hleg w q
  rw [htime]
  by_cases hdone :
      ell + 1 ≤ (levelStreamState B M hm szero w q).lift i
  · have hstep :
        (levelStreamState B M hm szero w q).lift i ≤
          (levelStreamState B M hm szero w (Nat.succ q)).lift i :=
      lift_mono (B := B) (M := M) hm szero w i (Nat.le_succ q)
    exact Nat.le_trans hdone hstep
  · have hcenterEq :
        (levelStreamState B M hm szero w q).lift i = ell := by
      omega
    have hnleft :
        Near
          ((levelStreamState B M hm szero w q).lift i)
          ((levelStreamState B M hm szero w q).lift (left hm i)) :=
      hlegq.2.2 (i := i) (j := left hm i) (Or.inl rfl)
    have hnright :
        Near
          ((levelStreamState B M hm szero w q).lift i)
          ((levelStreamState B M hm szero w q).lift (right hm i)) :=
      hlegq.2.2 (i := i) (j := right hm i) (Or.inr rfl)
    have hleftFront :
        (levelStreamState B M hm szero w q).lift (left hm i) =
            (levelStreamState B M hm szero w q).lift i ∨
          (levelStreamState B M hm szero w q).lift (left hm i) =
            (levelStreamState B M hm szero w q).lift i + 1 := by
      unfold Near at hnleft
      omega
    have hrightFront :
        (levelStreamState B M hm szero w q).lift (right hm i) =
            (levelStreamState B M hm szero w q).lift i ∨
          (levelStreamState B M hm szero w q).lift (right hm i) =
            (levelStreamState B M hm szero w q).lift i + 1 := by
      unfold Near at hnright
      omega
    have hcan :
        CanAdvance hm (levelStreamState B M hm szero w q).lift i :=
      ⟨hleftFront, hrightFront⟩
    have hact :
        clockAction M hm (levelStreamState B M hm szero w q) i =
          ClockAction.inc
            (clockOf M
              ((levelStreamState B M hm szero w q).lift i + 1)) :=
      (action_inc_iff hM hm
        (levelStreamState B M hm szero w q) hlegq i).2 hcan
    rw [levelStreamState_succ B M hm szero w q, hqspec.2]
    simp [activate, hact, advanceLift, hcenterEq]

/-! ## Eventual reachability and least level times -/

/-- Under fairness, every site eventually reaches every natural lifted level.
The induction step is precisely the local three-site service argument above. -/
theorem level_reached {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w) :
    ∀ ell (i : Fin m),
      ∃ t, ell ≤ (levelStreamState B M hm szero w t).lift i := by
  intro ell
  induction ell with
  | zero =>
      intro i
      exact ⟨0, Nat.zero_le _⟩
  | succ ell ih =>
      intro i
      obtain ⟨tleft, hleft⟩ := ih (left hm i)
      obtain ⟨tcenter, hcenter⟩ := ih i
      obtain ⟨tright, hright⟩ := ih (right hm i)
      let tstar := max (max tleft tcenter) tright
      have htleft : tleft ≤ tstar := by
        dsimp [tstar]
        exact Nat.le_trans (Nat.le_max_left tleft tcenter)
          (Nat.le_max_left (max tleft tcenter) tright)
      have htcenter : tcenter ≤ tstar := by
        dsimp [tstar]
        exact Nat.le_trans (Nat.le_max_right tleft tcenter)
          (Nat.le_max_left (max tleft tcenter) tright)
      have htright : tright ≤ tstar := by
        dsimp [tstar]
        exact Nat.le_max_right (max tleft tcenter) tright
      have hleftStar :
          ell ≤ (levelStreamState B M hm szero w tstar).lift (left hm i) :=
        Nat.le_trans hleft
          (lift_mono (B := B) (M := M) hm szero w
            (left hm i) htleft)
      have hcenterStar :
          ell ≤ (levelStreamState B M hm szero w tstar).lift i :=
        Nat.le_trans hcenter
          (lift_mono (B := B) (M := M) hm szero w i htcenter)
      have hrightStar :
          ell ≤ (levelStreamState B M hm szero w tstar).lift (right hm i) :=
        Nat.le_trans hright
          (lift_mono (B := B) (M := M) hm szero w
            (right hm i) htright)
      refine ⟨levelServiceTime w hinf i tstar, ?_⟩
      simpa only [Nat.succ_eq_add_one] using
        (next_level_after_service hM hm szero hleg w hinf
          i ell tstar hleftStar hcenterStar hrightStar)

private def levelReachedTest {m : Nat} (B M : Nat) (hm : 0 < m)
    (szero : WordState m) (w : Nat → Activation m)
    (i : Fin m) (ell t : Nat) : Bool :=
  decide (ell ≤ (levelStreamState B M hm szero w t).lift i)

private noncomputable def levelUpper {m : Nat} (B M : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell : Nat) : Nat :=
  Classical.choose
    (level_reached (B := B) (M := M)
      hM hm szero hleg w hinf ell i)

private theorem levelUpper_spec {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell : Nat) :
    ell ≤
      (levelStreamState B M hm szero w
        (levelUpper B M hM hm szero hleg w hinf i ell)).lift i := by
  unfold levelUpper
  exact Classical.choose_spec
    (level_reached (B := B) (M := M)
      hM hm szero hleg w hinf ell i)

/-- `T i ell`: the least state index at which site `i` has lift at least
`ell`. In particular it is zero whenever the initial state already has that
level. -/
noncomputable def levelTime {m : Nat} (B M : Nat)
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell : Nat) : Nat :=
  leastTrueUpToLevel (levelReachedTest B M hm szero w i ell)
    (levelUpper B M hM hm szero hleg w hinf i ell)

theorem levelTime_spec {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell : Nat) :
    ell ≤
      (levelStreamState B M hm szero w
        (levelTime B M hM hm szero hleg w hinf i ell)).lift i := by
  unfold levelTime
  have hu := levelUpper_spec (B := B) (M := M)
    hM hm szero hleg w hinf i ell
  have htest :
      levelReachedTest B M hm szero w i ell
        (levelUpper B M hM hm szero hleg w hinf i ell) = true := by
    simp [levelReachedTest, hu]
  have hfound := leastTrueUpToLevel_true_of_true_at
    (levelReachedTest B M hm szero w i ell)
    (levelUpper B M hM hm szero hleg w hinf i ell) htest
  unfold levelReachedTest at hfound
  exact of_decide_eq_true hfound

theorem levelTime_min {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell q : Nat)
    (hq : ell ≤ (levelStreamState B M hm szero w q).lift i) :
    levelTime B M hM hm szero hleg w hinf i ell ≤ q := by
  unfold levelTime
  have hqtest : levelReachedTest B M hm szero w i ell q = true := by
    simp [levelReachedTest, hq]
  rcases Nat.le_total q
      (levelUpper B M hM hm szero hleg w hinf i ell) with hqu | huq
  · exact leastTrueUpToLevel_min
      (levelReachedTest B M hm szero w i ell)
      (levelUpper B M hM hm szero hleg w hinf i ell) q hqu hqtest
  · exact Nat.le_trans
      (leastTrueUpToLevel_le (levelReachedTest B M hm szero w i ell)
        (levelUpper B M hM hm szero hleg w hinf i ell)) huq

/-- The explicit “already reached” convention for the least level time. -/
theorem levelTime_eq_zero_of_initial {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell : Nat) (hinit : ell ≤ szero.lift i) :
    levelTime B M hM hm szero hleg w hinf i ell = 0 := by
  have hzero :
      ell ≤ (levelStreamState B M hm szero w 0).lift i := by
    change ell ≤ szero.lift i
    exact hinit
  exact Nat.eq_zero_of_le_zero
    (levelTime_min (B := B) (M := M)
      hM hm szero hleg w hinf i ell 0 hzero)

/-- The floor condition used beside the clock recursion. -/
theorem level_floor {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) :
    levelTime B M hM hm szero hleg w hinf i 0 ≤ 0 := by
  rw [levelTime_eq_zero_of_initial (B := B) (M := M)
    hM hm szero hleg w hinf i 0 (Nat.zero_le _)]
  exact Nat.le_refl 0

/-! ## The three-neighbour level recursion -/

/-- Once level `ell` has been reached at the center and both neighbors, the
next service of the center reaches `ell+1`. Taking the three least hitting
times gives the requested recursion. -/
theorem level_rec {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w)
    (i : Fin m) (ell : Nat) :
    levelTime B M hM hm szero hleg w hinf i (ell + 1) ≤
      levelServiceTime w hinf i
        (max
          (max
            (levelTime B M hM hm szero hleg w hinf (left hm i) ell)
            (levelTime B M hM hm szero hleg w hinf i ell))
          (levelTime B M hM hm szero hleg w hinf (right hm i) ell)) := by
  let tleft := levelTime B M hM hm szero hleg w hinf (left hm i) ell
  let tcenter := levelTime B M hM hm szero hleg w hinf i ell
  let tright := levelTime B M hM hm szero hleg w hinf (right hm i) ell
  let tstar := max (max tleft tcenter) tright
  have hleft :
      ell ≤ (levelStreamState B M hm szero w tleft).lift (left hm i) := by
    dsimp [tleft]
    exact levelTime_spec (B := B) (M := M)
      hM hm szero hleg w hinf (left hm i) ell
  have hcenter :
      ell ≤ (levelStreamState B M hm szero w tcenter).lift i := by
    dsimp [tcenter]
    exact levelTime_spec (B := B) (M := M)
      hM hm szero hleg w hinf i ell
  have hright :
      ell ≤ (levelStreamState B M hm szero w tright).lift (right hm i) := by
    dsimp [tright]
    exact levelTime_spec (B := B) (M := M)
      hM hm szero hleg w hinf (right hm i) ell
  have htleft : tleft ≤ tstar := by
    dsimp [tstar]
    exact Nat.le_trans (Nat.le_max_left tleft tcenter)
      (Nat.le_max_left (max tleft tcenter) tright)
  have htcenter : tcenter ≤ tstar := by
    dsimp [tstar]
    exact Nat.le_trans (Nat.le_max_right tleft tcenter)
      (Nat.le_max_left (max tleft tcenter) tright)
  have htright : tright ≤ tstar := by
    dsimp [tstar]
    exact Nat.le_max_right (max tleft tcenter) tright
  have hleftStar :
      ell ≤ (levelStreamState B M hm szero w tstar).lift (left hm i) :=
    Nat.le_trans hleft
      (lift_mono (B := B) (M := M) hm szero w
        (left hm i) htleft)
  have hcenterStar :
      ell ≤ (levelStreamState B M hm szero w tstar).lift i :=
    Nat.le_trans hcenter
      (lift_mono (B := B) (M := M) hm szero w i htcenter)
  have hrightStar :
      ell ≤ (levelStreamState B M hm szero w tstar).lift (right hm i) :=
    Nat.le_trans hright
      (lift_mono (B := B) (M := M) hm szero w
        (right hm i) htright)
  have hreach := next_level_after_service hM hm szero hleg w hinf
    i ell tstar hleftStar hcenterStar hrightStar
  have hmin := levelTime_min (B := B) (M := M)
    hM hm szero hleg w hinf i (ell + 1)
    (levelServiceTime w hinf i tstar) hreach
  simpa only [tstar, tleft, tcenter, tright] using hmin

/-- Stream form of the `hrec` hypothesis of `ClockMeanAlt.clock_mean`. -/
theorem clock_rec_form {m B M : Nat}
    (hM : ClockParams M) (hm : 0 < m)
    (szero : WordState m) (hleg : Legit M hm szero)
    (w : Nat → Activation m) (hinf : FairActivationStream w) :
    ∀ i ell,
      levelTime B M hM hm szero hleg w hinf i (ell + 1) ≤
        levelServiceTime w hinf i
          (max
            (max
              (levelTime B M hM hm szero hleg w hinf (left hm i) ell)
              (levelTime B M hM hm szero hleg w hinf i ell))
            (levelTime B M hM hm szero hleg w hinf (right hm i) ell)) := by
  intro i ell
  exact level_rec (B := B) (M := M)
    hM hm szero hleg w hinf i ell

#print axioms lift_mono
#print axioms S_after
#print axioms S_mono
#print axioms level_reached
#print axioms levelTime_spec
#print axioms level_rec
#print axioms clock_rec_form

end L4.Height
