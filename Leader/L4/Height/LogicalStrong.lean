import Leader.L4.Height.LogicalBAlt
import Leader.L4.Height.LogicalAssembly

namespace L4.Height

open Classical
open L4.Compiler.Native


/-! ## Choice-free warm starts -/

/-- A fixed total choice table used only to state the initial condition. -/
def falseChoices {m : Nat} : Nat → Fin m → Bool :=
  fun _ _ => false

private theorem syncLevels_one_choice_free {m : Nat}
    (B M ellzero : Nat) (hm : 0 < m)
    (choices choices' : Nat → Fin m → Bool)
    (start : Fin m → Snapshot)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0) :
    syncLevels B M ellzero hm choices start 1 =
      syncLevels B M ellzero hm choices' start 1 := by
  have hphase : clockOf M ellzero % 32 = 0 := by
    have h := clockOf_mod_phase (M := M) (ellzero := ellzero)
      (n := 0) hdiv hzero
    simpa using h
  simp only [syncLevels, Nat.add_zero]
  rw [hphase]
  exact phaseStep_bits_irrelevant (B := B) (j := 0)
    (by omega) hm (choices ellzero) (choices' ellzero) start

/-- The warm-start predicate only consults synchronous level one.  At a
phase-zero base level, that entry is independent of the supplied bit table. -/
theorem startConsistent_choice_free {m : Nat}
    (B M ellzero : Nat) (hm : 0 < m)
    (choices choices' : Nat → Fin m → Bool)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0) :
    StartConsistent B M ellzero hm choices start s0 ↔
      StartConsistent B M ellzero hm choices' start s0 := by
  have hsync := syncLevels_one_choice_free B M ellzero hm
    choices choices' start hdiv hzero
  unfold StartConsistent
  constructor
  · intro h i
    rcases h i with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.1, h.2.1, ?_⟩
      exact h.2.2.trans (congrFun hsync i)
  · intro h i
    rcases h i with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h.1, h.2.1, ?_⟩
      exact h.2.2.trans (congrFun hsync.symm i)

/-! ## Stability of the first observed level -/

/-- Once `levelCurr` has returned a snapshot, extending the history cannot
change that first observation. -/
theorem levelCurr_stable {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (h h' : List (Activation m)) (s0 : WordState m)
    (i : Fin m) (ell : Nat) (v : Snapshot)
    (hv : levelCurr B M hm h s0 i ell = some v) :
    levelCurr B M hm (h ++ h') s0 i ell = some v := by
  induction h generalizing s0 with
  | nil =>
      by_cases hnow : s0.lift i = ell
      · have hval : (s0.cfg i).curr = v := by
          simpa [levelCurr, hnow] using hv
        cases h' with
        | nil =>
            simp [levelCurr, hnow, hval]
        | cons e h' =>
            simp [levelCurr, hnow, hval]
      · simp [levelCurr, hnow] at hv
  | cons e h ih =>
      by_cases hnow : s0.lift i = ell
      · have hval : (s0.cfg i).curr = v := by
          simpa [levelCurr, hnow] using hv
        simp [levelCurr, hnow, hval]
      · have htail :
            levelCurr B M hm h
              (activate B M hm s0 e.1 e.2) i ell = some v := by
          simpa [levelCurr, hnow] using hv
        have hs := ih (s0 := activate B M hm s0 e.1 e.2) htail
        simpa [levelCurr, hnow] using hs

/-! ## A total choice table for overrun histories -/

private theorem phaseRound_some_strong
    (ellzero Q ell : Nat) (r : Fin Q) :
    phaseRound? ellzero Q ell = some r ↔
      ell = ellzero + 32 * r.val + 1 := by
  unfold phaseRound?
  by_cases h : ∃ q : Fin Q, ell = ellzero + 32 * q.val + 1
  · rw [dif_pos h]
    constructor
    · intro he
      have hc : Classical.choose h = r := Option.some.inj he
      rw [← hc]
      exact Classical.choose_spec h
    · intro hr
      have hc : Classical.choose h = r := by
        apply Fin.ext
        have hs := Classical.choose_spec h
        omega
      rw [hc]
  · rw [dif_neg h]
    constructor
    · intro he
      cases he
    · intro hr
      exact False.elim (h ⟨r, hr⟩)

/-- On indexed phase-one levels use the paired-source read vector.  Outside
that finite window use the first actual increment bit of the full history.
This makes an arbitrarily long overrun history honored without changing the
first `Q` logical rounds. -/
noncomputable def strongChoices {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m))) :
    Nat → Fin m → Bool :=
  fun ell i =>
    match phaseRound? ellzero Q ell with
    | some r =>
        Couple.readVector (physSource B M ellzero Q hm) s0 u
          (phaseIndex r i)
    | none =>
        (levelBit B M hm (u.map physicalActivation) s0 i ell).getD false

@[simp] theorem strongChoices_target {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m)))
    (r : Fin Q) (i : Fin m) :
    strongChoices B M ellzero Q hm s0 u
        (ellzero + 32 * r.val + 1) i =
      Couple.readVector (physSource B M ellzero Q hm) s0 u
        (phaseIndex r i) := by
  unfold strongChoices
  rw [(phaseRound_some_strong ellzero Q
    (ellzero + 32 * r.val + 1) r).2 rfl]

private theorem physicalRun_append_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u v : List (Fin (2 * m))) :
    physicalRun B M hm s (u ++ v) =
      physicalRun B M hm (physicalRun B M hm s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      exact ih (physicalNext B M hm s e)

private theorem physicalNext_lift_step_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) (i : Fin m) :
    (physicalNext B M hm s e).lift i = s.lift i ∨
      (physicalNext B M hm s e).lift i = s.lift i + 1 := by
  by_cases hi : i = physicalSite e
  · subst i
    cases hact : clockAction M hm s (physicalSite e) <;>
      simp [physicalNext, activate, hact, advanceLift]
  · left
    simp [physicalNext, activate, hi]

private theorem physicalNext_lift_mono_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) (i : Fin m) :
    s.lift i ≤ (physicalNext B M hm s e).lift i := by
  rcases physicalNext_lift_step_strong B M hm s e i with h | h
  · rw [h]
    exact Nat.le_refl _
  · rw [h]
    omega

private theorem physicalNext_lift_succ_data_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) (i : Fin m)
    (hsucc : (physicalNext B M hm s e).lift i = s.lift i + 1) :
    physicalSite e = i ∧
      ∃ tick, clockAction M hm s i = ClockAction.inc tick := by
  by_cases hi : i = physicalSite e
  · subst i
    refine ⟨rfl, ?_⟩
    cases hact : clockAction M hm s (physicalSite e) with
    | reset =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
    | propagate tick =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
    | clear =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
    | inc tick => exact ⟨tick, rfl⟩
    | hold =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
  · have heq : (physicalNext B M hm s e).lift i = s.lift i := by
      simp [physicalNext, activate, hi]
    omega

private theorem physicalRun_lift_mono_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m))) (i : Fin m) :
    s.lift i ≤ (physicalRun B M hm s u).lift i := by
  induction u generalizing s with
  | nil => exact Nat.le_refl _
  | cons e u ih =>
      exact Nat.le_trans
        (physicalNext_lift_mono_strong B M hm s e i)
        (ih (physicalNext B M hm s e))

private theorem firstReveal_eq_of_reveal_strong {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (pre : List (Fin (2 * m)))
    (e : Fin (2 * m)) (post : List (Fin (2 * m)))
    (r : Fin Q) (i : Fin m) (v : Bool)
    (h : (physSource B M ellzero Q hm).bitOf
      (physicalRun B M hm s pre) e = some (phaseIndex r i, v)) :
    Couple.firstReveal (physSource B M ellzero Q hm)
      (phaseIndex r i) s (pre ++ e :: post) = some v := by
  induction pre generalizing s with
  | nil =>
      have h0 : (physSource B M ellzero Q hm).bitOf s e =
          some (phaseIndex r i, v) := by
        simpa [physicalRun] using h
      rw [List.nil_append, Couple.firstReveal]
      simp only [h0, if_pos]
  | cons a pre ih =>
      have htail := ih (s := physicalNext B M hm s a) (by
        simpa [physicalRun] using h)
      rw [List.cons_append, Couple.firstReveal]
      cases hb : (physSource B M ellzero Q hm).bitOf s a with
      | none =>
          simp only
          simpa only [physSource_next] using htail
      | some p =>
          rcases p with ⟨k, b⟩
          simp only
          by_cases hk : k = phaseIndex r i
          · subst k
            have hnone := reveal_once B M ellzero Q hm s a r i b hb
              (pre ++ e :: post)
            have htail' :
                Couple.firstReveal (physSource B M ellzero Q hm)
                  (phaseIndex r i)
                  ((physSource B M ellzero Q hm).next s a)
                  (pre ++ e :: post) = some v := by
              simpa only [physSource_next] using htail
            rw [hnone] at htail'
            cases htail'
          · rw [if_neg hk]
            simpa only [physSource_next] using htail

private theorem levelBit_eq_of_increment_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (pre : List (Fin (2 * m)))
    (e : Fin (2 * m)) (post : List (Fin (2 * m)))
    (tick : Nat)
    (hact : clockAction M hm (physicalRun B M hm s pre)
      (physicalSite e) = ClockAction.inc tick) :
    levelBit B M hm ((pre ++ e :: post).map physicalActivation) s
        (physicalSite e)
        ((physicalRun B M hm s pre).lift (physicalSite e)) =
      some (physicalBit e) := by
  induction pre generalizing s with
  | nil =>
      change clockAction M hm s (physicalSite e) = .inc tick at hact
      simp [physicalRun, levelBit, physicalActivation, hact]
  | cons a pre ih =>
      let s' := physicalNext B M hm s a
      let i := physicalSite e
      let ell := (physicalRun B M hm s' pre).lift i
      have htail := ih (s := s') hact
      change (if physicalSite a = i then
          if s.lift i = ell then
            match clockAction M hm s (physicalSite a) with
            | .inc _ => some (physicalBit a)
            | _ => levelBit B M hm ((pre ++ e :: post).map physicalActivation) s' i ell
          else levelBit B M hm ((pre ++ e :: post).map physicalActivation) s' i ell
        else levelBit B M hm ((pre ++ e :: post).map physicalActivation) s' i ell) = _
      split
      next hsite =>
        split
        next hlevel =>
          cases ha : clockAction M hm s (physicalSite a) with
          | inc t =>
            have hstep : s'.lift i = s.lift i + 1 := by
              rw [← hsite]
              simp [s', physicalNext, activate, ha, advanceLift]
            have hmono : s'.lift i ≤ ell :=
              physicalRun_lift_mono_strong B M hm s' pre i
            omega
          | _ => exact htail
        next => exact htail
      next => exact htail

private theorem honors_strongChoices_aux {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s0 : WordState m) (whole : List (Fin (2 * m))) :
    ∀ (pre rest : List (Fin (2 * m))),
      whole = pre ++ rest →
      Honors B M hm
        (strongChoices B M ellzero Q hm s0 whole)
        (physicalRun B M hm s0 pre)
        (rest.map physicalActivation) := by
  intro pre rest hsplit
  induction rest generalizing pre with
  | nil =>
      simp [Honors]
  | cons e rest ih =>
      let cur := physicalRun B M hm s0 pre
      change
        (match clockAction M hm cur (physicalSite e) with
         | .inc _ =>
             clockOf M (cur.lift (physicalSite e)) % 32 ≠ 1 ∨
               physicalBit e =
                 strongChoices B M ellzero Q hm s0 whole
                   (cur.lift (physicalSite e)) (physicalSite e)
         | _ => True) ∧
        Honors B M hm
          (strongChoices B M ellzero Q hm s0 whole)
          (activate B M hm cur (physicalSite e) (physicalBit e))
          (rest.map physicalActivation)
      constructor
      · cases hact : clockAction M hm cur (physicalSite e) with
        | reset => trivial
        | propagate tick => trivial
        | clear => trivial
        | hold => trivial
        | inc tick =>
            by_cases hp :
                clockOf M (cur.lift (physicalSite e)) % 32 = 1
            · right
              cases hrnd : phaseRound? ellzero Q
                (cur.lift (physicalSite e)) with
              | none =>
                  have hbit0 := levelBit_eq_of_increment_strong
                    B M hm s0 pre e rest tick hact
                  have hbit :
                      levelBit B M hm (whole.map physicalActivation) s0
                          (physicalSite e)
                          (cur.lift (physicalSite e)) =
                        some (physicalBit e) := by
                    rw [hsplit]
                    simpa [cur] using hbit0
                  unfold strongChoices
                  rw [hrnd, hbit]
                  rfl
              | some r =>
                  have hb0 :
                      physicalBitOf M ellzero Q hm cur e =
                        some (phaseIndex r (physicalSite e), physicalBit e) := by
                    unfold physicalBitOf phaseRevealIndex?
                    simp [hact, hp, hrnd]
                  have hb :
                      (physSource B M ellzero Q hm).bitOf cur e =
                        some (phaseIndex r (physicalSite e), physicalBit e) := by
                    simpa only [physSource_bitOf] using hb0
                  have hfirst0 := firstReveal_eq_of_reveal_strong
                    B M ellzero Q hm s0 pre e rest r
                    (physicalSite e) (physicalBit e) hb
                  have hfirst :
                      Couple.firstReveal (physSource B M ellzero Q hm)
                        (phaseIndex r (physicalSite e)) s0 whole =
                          some (physicalBit e) := by
                    rw [hsplit]
                    exact hfirst0
                  have hread :
                      Couple.readVector (physSource B M ellzero Q hm)
                          s0 whole (phaseIndex r (physicalSite e)) =
                        physicalBit e := by
                    unfold Couple.readVector
                    rw [hfirst]
                    rfl
                  unfold strongChoices
                  rw [hrnd]
                  exact hread.symm
            · left
              exact hp
      · have hsplitTail :
            whole = (pre ++ [e]) ++ rest := by
          rw [hsplit]
          simp [List.append_assoc]
        have htail := ih (pre ++ [e]) hsplitTail
        have hstate :
            physicalRun B M hm s0 (pre ++ [e]) =
              activate B M hm cur (physicalSite e) (physicalBit e) := by
          rw [physicalRun_append_strong]
          simp [physicalRun, physicalNext, cur]
        rw [← hstate]
        exact htail

/-- Every raw history honors the total choice table `strongChoices`. -/
theorem honors_strongChoices {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m))) :
    Honors B M hm (strongChoices B M ellzero Q hm s0 u) s0
      (u.map physicalActivation) := by
  exact honors_strongChoices_aux B M ellzero Q hm s0 u [] u (by simp)

private theorem levelCurr_exists_of_physical_reach {m : Nat}
    (B M : Nat) (hm : 0 < m) :
    ∀ (u : List (Fin (2 * m))) (s : WordState m)
      (i : Fin m) (ell : Nat),
      s.lift i ≤ ell →
      ell ≤ (physicalRun B M hm s u).lift i →
      ∃ value,
        levelCurr B M hm (u.map physicalActivation) s i ell = some value := by
  intro u
  induction u with
  | nil =>
      intro s i ell hstart hend
      have hfinal : ell ≤ s.lift i := by
        simpa [physicalRun] using hend
      have heq : s.lift i = ell := by omega
      refine ⟨(s.cfg i).curr, ?_⟩
      simp [levelCurr, heq]
  | cons e u ih =>
      intro s i ell hstart hend
      by_cases hnow : s.lift i = ell
      · refine ⟨(s.cfg i).curr, ?_⟩
        simp [levelCurr, hnow]
      · have hslt : s.lift i < ell := by omega
        have hstep := physicalNext_lift_step_strong B M hm s e i
        have hnext : (physicalNext B M hm s e).lift i ≤ ell := by
          rcases hstep with h | h <;> omega
        have hend' :
            ell ≤ (physicalRun B M hm (physicalNext B M hm s e) u).lift i := by
          simpa [physicalRun] using hend
        obtain ⟨value, hv⟩ :=
          ih (physicalNext B M hm s e) i ell hnext hend'
        refine ⟨value, ?_⟩
        simpa [levelCurr, hnow, physicalActivation, physicalNext] using hv

private theorem roundBits_congr_strong {m : Nat}
    (f g : Nat → Fin m → Bool) (ellzero : Nat) :
    ∀ Q,
      (∀ k, k < Q →
        f (ellzero + 32 * k + 1) = g (ellzero + 32 * k + 1)) →
      roundBits f ellzero Q = roundBits g ellzero Q := by
  intro Q
  induction Q with
  | zero =>
      intro h
      rfl
  | succ Q ih =>
      intro h
      have hprev : ∀ k, k < Q →
          f (ellzero + 32 * k + 1) =
            g (ellzero + 32 * k + 1) := by
        intro k hk
        exact h k (by omega)
      calc
        roundBits f ellzero (Q + 1) =
            roundBits f ellzero Q ++ [f (ellzero + 32 * Q + 1)] := rfl
        _ = roundBits g ellzero Q ++ [f (ellzero + 32 * Q + 1)] := by
          rw [ih hprev]
        _ = roundBits g ellzero Q ++ [g (ellzero + 32 * Q + 1)] := by
          rw [h Q (by omega)]
        _ = roundBits g ellzero (Q + 1) := rfl

/-! ## Observing a target level along a history -/

private theorem exists_increment_split_strong {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m)))
    (i : Fin m) (ell : Nat)
    (hstart : s.lift i ≤ ell)
    (hend : ell < (physicalRun B M hm s u).lift i) :
    ∃ pre e post tick,
      u = pre ++ e :: post ∧
      physicalSite e = i ∧
      (physicalRun B M hm s pre).lift i = ell ∧
      clockAction M hm (physicalRun B M hm s pre) i =
        ClockAction.inc tick := by
  induction u generalizing s with
  | nil =>
      change ell < s.lift i at hend
      omega
  | cons e u ih =>
      let s' := physicalNext B M hm s e
      have hstep : s'.lift i = s.lift i ∨
          s'.lift i = s.lift i + 1 := by
        simpa [s'] using physicalNext_lift_step_strong B M hm s e i
      by_cases hcross : ell < s'.lift i
      · have hold : s.lift i = ell := by
          rcases hstep with h | h <;> omega
        have hsucc : s'.lift i = s.lift i + 1 := by
          rcases hstep with h | h
          · omega
          · exact h
        have hdata := physicalNext_lift_succ_data_strong B M hm s e i
          (by simpa [s'] using hsucc)
        rcases hdata with ⟨hsite, ⟨tick, hact⟩⟩
        refine ⟨[], e, u, tick, rfl, hsite, ?_, ?_⟩
        · simpa [physicalRun] using hold
        · simpa [physicalRun] using hact
      · have hsle : s'.lift i ≤ ell := Nat.le_of_not_gt hcross
        have hend' : ell < (physicalRun B M hm s' u).lift i := by
          simpa [physicalRun, s'] using hend
        obtain ⟨pre, a, post, tick, hu, hsite, hlift, hact⟩ :=
          ih s' hsle hend'
        refine ⟨e :: pre, a, post, tick, ?_, hsite, ?_, hact⟩
        · simp only [List.cons_append]
          rw [hu]
        · simpa [physicalRun, s'] using hlift

private theorem firstReveal_covered_strong {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (s : WordState m) (u : List (Fin (2 * m)))
    (r : Fin Q) (i : Fin m)
    (hstart : s.lift i ≤ ellzero + 32 * r.val + 1)
    (hend : ellzero + 32 * r.val + 1 <
      (physicalRun B M hm s u).lift i) :
    ∃ v,
      Couple.firstReveal (physSource B M ellzero Q hm)
        (phaseIndex r i) s u = some v := by
  obtain ⟨pre, e, post, tick, hu, hsite, hlift, hact⟩ :=
    exists_increment_split_strong B M hm s u i
      (ellzero + 32 * r.val + 1) hstart hend
  have hp0 := clockOf_mod_phase (M := M) (ellzero := ellzero)
    (n := 32 * r.val + 1) hdiv hzero
  have hp :
      clockOf M (ellzero + 32 * r.val + 1) % 32 = 1 := by
    calc
      clockOf M (ellzero + 32 * r.val + 1) % 32 =
          (32 * r.val + 1) % 32 := hp0
      _ = 1 := by omega
  have hpstate :
      clockOf M ((physicalRun B M hm s pre).lift i) % 32 = 1 := by
    rw [hlift]
    exact hp
  have hrnd :
      phaseRound? ellzero Q ((physicalRun B M hm s pre).lift i) = some r :=
    (phaseRound_some_strong ellzero Q
      ((physicalRun B M hm s pre).lift i) r).2 hlift
  have hb0 :
      physicalBitOf M ellzero Q hm (physicalRun B M hm s pre) e =
        some (phaseIndex r i, physicalBit e) := by
    unfold physicalBitOf phaseRevealIndex?
    simp [hsite, hact, hpstate, hrnd]
  have hb :
      (physSource B M ellzero Q hm).bitOf
          (physicalRun B M hm s pre) e =
        some (phaseIndex r i, physicalBit e) := by
    simpa only [physSource_bitOf] using hb0
  refine ⟨physicalBit e, ?_⟩
  rw [hu]
  exact firstReveal_eq_of_reveal_strong B M ellzero Q hm s pre e post
    r i (physicalBit e) hb

private theorem all_phase_revealed_reach_strong {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (u : List (Fin (2 * m)))
    (hstart : StartConsistent B M ellzero hm falseChoices start s0)
    (hreach : ∀ i,
      ellzero + 32 * Q ≤ (physicalRun B M hm s0 u).lift i) :
    ∀ r : Fin Q, ∀ i : Fin m,
      ∃ v,
        Couple.firstReveal (physSource B M ellzero Q hm)
          (phaseIndex r i) s0 u = some v := by
  intro r i
  have hinitial : s0.lift i ≤ ellzero + 32 * r.val + 1 := by
    rcases hstart i with h | h <;> rw [h.1] <;> omega
  have htarget :
      ellzero + 32 * r.val + 1 < ellzero + 32 * Q := by
    have hr := r.isLt
    omega
  have hend : ellzero + 32 * r.val + 1 <
      (physicalRun B M hm s0 u).lift i :=
    Nat.lt_of_lt_of_le htarget (hreach i)
  exact firstReveal_covered_strong B M ellzero Q hm hdiv hzero s0 u
    r i hinitial hend

/-- A target lying between each initial and final lift is observed, including at zero rounds. -/
theorem physical_snapshot_reach_from_below {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (u : List (Fin (2 * m)))
    (hleg : Legit M hm s0)
    (hstart : StartConsistent B M ellzero hm falseChoices start s0)
    (hstartBelow : ∀ i, s0.lift i ≤ ellzero + 32 * Q)
    (hreach : ∀ i,
      ellzero + 32 * Q ≤ (physicalRun B M hm s0 u).lift i) :
    (∀ i,
      levelCurr B M hm (u.map physicalActivation) s0 i
          (ellzero + 32 * Q) =
        some
          (runRounds B hm
            (roundBits
              (physicalChoices B M ellzero Q hm s0 u) ellzero Q)
            start i)) ∧
    (∀ r : Fin Q, ∀ i : Fin m,
      ∃ v,
        Couple.firstReveal (physSource B M ellzero Q hm)
          (phaseIndex r i) s0 u = some v) := by
  let choices := strongChoices B M ellzero Q hm s0 u
  have hstartChoices :
      StartConsistent B M ellzero hm choices start s0 :=
    (startConsistent_choice_free B M ellzero hm
      falseChoices choices start s0 hdiv hzero).1 hstart
  have hhonor :
      Honors B M hm choices s0 (u.map physicalActivation) := by
    dsimp [choices]
    exact honors_strongChoices B M ellzero Q hm s0 u
  have hrep : Represents B M ellzero hm choices start s0 :=
    startConsistent_represents hm choices start s0 hstartChoices
  have hphase : ∀ n,
      clockOf M (ellzero + n) % 32 = n % 32 := by
    intro n
    exact clockOf_mod_phase hdiv hzero
  have htargets : ∀ k, k < Q →
      choices (ellzero + 32 * k + 1) =
        physicalChoices B M ellzero Q hm s0 u
          (ellzero + 32 * k + 1) := by
    intro k hk
    funext i
    let r : Fin Q := ⟨k, hk⟩
    have hs := strongChoices_target B M ellzero Q hm s0 u r i
    have hp := physicalChoices_target B M ellzero Q hm s0 u r i
    change strongChoices B M ellzero Q hm s0 u
        (ellzero + 32 * k + 1) i =
      physicalChoices B M ellzero Q hm s0 u
        (ellzero + 32 * k + 1) i
    simpa [r] using hs.trans hp.symm
  have hround :
      roundBits choices ellzero Q =
        roundBits (physicalChoices B M ellzero Q hm s0 u) ellzero Q :=
    roundBits_congr_strong choices
      (physicalChoices B M ellzero Q hm s0 u) ellzero Q htargets
  constructor
  · intro i
    obtain ⟨value, hvalue⟩ :=
      levelCurr_exists_of_physical_reach B M hm u s0 i
        (ellzero + 32 * Q) (hstartBelow i) (hreach i)
    have hv := levelCurr_eq_sync hM hm choices start
      (u.map physicalActivation) s0 hleg hrep hhonor
      i (32 * Q) value hvalue
    have hsync := syncLevels_runRounds
      (B := B) (M := M) (ellzero := ellzero) (k := Q)
      hm choices start hphase
    have hv' : value =
        runRounds B hm
          (roundBits (physicalChoices B M ellzero Q hm s0 u) ellzero Q)
          start i := by
      calc
        value = syncLevels B M ellzero hm choices start (32 * Q) i := hv
        _ = runRounds B hm (roundBits choices ellzero Q) start i :=
          congrFun hsync i
        _ = runRounds B hm
            (roundBits (physicalChoices B M ellzero Q hm s0 u) ellzero Q)
            start i := by rw [hround]
    rw [hv'] at hvalue
    exact hvalue
  · exact all_phase_revealed_reach_strong B M ellzero Q hm hdiv hzero
      start s0 u hstart hreach

/-- Reach is sufficient for every positive number of logical rounds.  Positivity
is necessary only to ensure a warm start at `ellzero + 1` has not already
passed the requested observation level. -/
theorem physical_snapshot_reach {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (hQ : 0 < Q)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (u : List (Fin (2 * m)))
    (hleg : Legit M hm s0)
    (hstart : StartConsistent B M ellzero hm falseChoices start s0)
    (hreach : ∀ i,
      ellzero + 32 * Q ≤ (physicalRun B M hm s0 u).lift i) :
    (∀ i,
      levelCurr B M hm (u.map physicalActivation) s0 i
          (ellzero + 32 * Q) =
        some
          (runRounds B hm
            (roundBits
              (physicalChoices B M ellzero Q hm s0 u) ellzero Q)
            start i)) ∧
    (∀ r : Fin Q, ∀ i : Fin m,
      ∃ v,
        Couple.firstReveal (physSource B M ellzero Q hm)
          (phaseIndex r i) s0 u = some v) := by
  have hstartBelow : ∀ i, s0.lift i ≤ ellzero + 32 * Q := by
    intro i
    rcases hstart i with h | h
    · rw [h.1]
      omega
    · rw [h.1]
      omega
  exact physical_snapshot_reach_from_below B M ellzero Q hm hM hdiv hzero
    start s0 u hleg hstart hstartBelow hreach

/-! ## Vector form for adaptive transfer -/

/-- Defaulted observed snapshot at one lifted level.  Under reach the default
branch is eliminated by `physical_snapshot_reach`. -/
noncomputable def observedSnapshot {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m))) (ell : Nat) :
    Fin m → Snapshot :=
  fun i =>
    (levelCurr B M hm (u.map physicalActivation) s0 i ell).getD
      ({} : Snapshot)

/-- Adaptive-transfer interface.  A physical word that reaches the target and
has a non-single-anchor observed snapshot covers every logical bit and maps to
a non-single-anchor logical assignment. -/
theorem physical_event {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (hQ : 0 < Q)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (hleg : Legit M hm s0)
    (hstart : StartConsistent B M ellzero hm falseChoices start s0)
    (u : List (Fin (2 * m)))
    (hE :
      (∀ i, ellzero + 32 * Q ≤ (physicalRun B M hm s0 u).lift i) ∧
      anchorCount hm
        (observedSnapshot B M hm s0 u (ellzero + 32 * Q)) ≠ 1) :
    (∀ k : Fin (Q * m),
      Couple.firstReveal (physSource B M ellzero Q hm) k s0 u ≠ none) ∧
    anchorCount hm
      (runRounds B hm
        (vecRounds Q m
          (Couple.readVector (physSource B M ellzero Q hm) s0 u))
        start) ≠ 1 := by
  have hs := physical_snapshot_reach B M ellzero Q hm hM hdiv hzero hQ
    start s0 u hleg hstart hE.1
  rcases hs with ⟨hsnap, hcover⟩
  constructor
  · intro k
    rcases phaseIndex_surjective (Q := Q) hm k with ⟨r, i, hk⟩
    subst k
    obtain ⟨v, hv⟩ := hcover r i
    intro hnone
    rw [hv] at hnone
    cases hnone
  · have hround := roundBits_readVector (Q := Q) B M ellzero hm s0 u
    have hobs :
        observedSnapshot B M hm s0 u (ellzero + 32 * Q) =
          runRounds B hm
            (vecRounds Q m
              (Couple.readVector (physSource B M ellzero Q hm) s0 u))
            start := by
      funext i
      simp [observedSnapshot, hsnap i, hround]
    have hbad := hE.2
    rw [hobs] at hbad
    exact hbad

/-! ## Observation at the starting level -/

private theorem zeroRound_siteCount_pos : 0 < (4 : Nat) := by omega

private def zeroRound_start (i : Fin 4) : Snapshot :=
  { x := i.val }

private def zeroRound_warmStart : WordState 4 where
  cfg i :=
    { tick := clockOf 4096 1
      err := false
      prior := zeroRound_start i
      curr := syncLevels 16 4096 0 zeroRound_siteCount_pos
        falseChoices zeroRound_start 1 i }
  lift _ := 1

private theorem zeroRound_legit :
    Legit 4096 zeroRound_siteCount_pos zeroRound_warmStart := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i j _
  change Near 1 1
  unfold Near
  omega

private theorem zeroRound_consistent :
    StartConsistent 16 4096 0 zeroRound_siteCount_pos
      falseChoices zeroRound_start zeroRound_warmStart := by
  intro i
  exact Or.inr ⟨rfl, rfl, rfl⟩

private theorem zeroRound_reach :
    ∀ i, 0 + 32 * 0 ≤
      (physicalRun 16 4096 zeroRound_siteCount_pos zeroRound_warmStart []).lift i := by
  intro i
  exact Nat.zero_le _

/-- The empty word meets reach for zero rounds although every site started one
level after the requested current-snapshot observation. -/
theorem physical_snapshot_reach_zero_counterexample :
    ∃ (hm : 0 < (4 : Nat)) (start : Fin 4 → Snapshot) (s : WordState 4),
      ClockParams 4096 ∧ 32 ∣ 4096 / 2 ∧ (0 : Nat) % 32 = 0 ∧
      Legit 4096 hm s ∧ StartConsistent 16 4096 0 hm falseChoices start s ∧
      (∀ i, 0 + 32 * 0 ≤ (physicalRun 16 4096 hm s []).lift i) ∧
      ¬ ((∀ i, levelCurr 16 4096 hm (([] : List (Fin (2 * 4))).map physicalActivation)
            s i (0 + 32 * 0) =
          some (runRounds 16 hm
            (roundBits (physicalChoices 16 4096 0 0 hm s []) 0 0) start i)) ∧
        (∀ r : Fin 0, ∀ i : Fin 4,
          ∃ v, Couple.firstReveal (physSource 16 4096 0 0 hm)
            (phaseIndex r i) s [] = some v)) := by
  refine ⟨zeroRound_siteCount_pos, zeroRound_start, zeroRound_warmStart,
    ?_, ⟨64, rfl⟩, rfl, zeroRound_legit, zeroRound_consistent, zeroRound_reach, ?_⟩
  · exact ⟨by omega, rfl⟩
  · intro h
    have hzero := h.1 (⟨0, zeroRound_siteCount_pos⟩ : Fin 4)
    change none = some (zeroRound_start ⟨0, zeroRound_siteCount_pos⟩) at hzero
    cases hzero

/-- Defaulting the missing observations can turn a single-anchor warm start
into a non-single-anchor event, so the implication fails at zero rounds. -/
theorem physical_event_zero_counterexample :
    ∃ (hm : 0 < (4 : Nat)) (start : Fin 4 → Snapshot) (s : WordState 4),
      ClockParams 4096 ∧ 32 ∣ 4096 / 2 ∧ (0 : Nat) % 32 = 0 ∧
      Legit 4096 hm s ∧ StartConsistent 16 4096 0 hm falseChoices start s ∧
      ((∀ i, 0 + 32 * 0 ≤ (physicalRun 16 4096 hm s []).lift i) ∧
        anchorCount hm (observedSnapshot 16 4096 hm s [] (0 + 32 * 0)) ≠ 1) ∧
      ¬ ((∀ k : Fin (0 * 4),
          Couple.firstReveal (physSource 16 4096 0 0 hm) k s [] ≠ none) ∧
        anchorCount hm
          (runRounds 16 hm
            (vecRounds 0 4 (Couple.readVector (physSource 16 4096 0 0 hm) s []))
            start) ≠ 1) := by
  refine ⟨zeroRound_siteCount_pos, zeroRound_start, zeroRound_warmStart,
    ?_, ⟨64, rfl⟩, rfl, zeroRound_legit, zeroRound_consistent,
    ⟨zeroRound_reach, ?_⟩, ?_⟩
  · exact ⟨by omega, rfl⟩
  · change (4 : Nat) ≠ 1
    omega
  · intro h
    apply h.2
    change anchorCount zeroRound_siteCount_pos zeroRound_start = 1
    rfl

#print axioms L4.Height.startConsistent_choice_free
#print axioms L4.Height.levelCurr_stable
#print axioms L4.Height.physical_snapshot_reach
#print axioms L4.Height.physical_event

end L4.Height

