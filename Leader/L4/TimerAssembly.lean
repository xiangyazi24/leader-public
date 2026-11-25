import Leader.L4.OwnedWorker
import Leader.L4.AliasSweep

/-! Pure episode assembly: dirty phases, then the genuine owned itinerary. -/
namespace L4.ResidualSweep
open FixedResidual

theorem await_no_exit {Q : Nat} (k : Fin Q) (r : Rail)
    (hL : ¬ launches (.await k) r)
    (hF : (serviceDoor (.await k) r).fire ≠ true) :
    (serviceDoor (.await k) r).source = .await k := by
  cases r with
  | e => exact (hL (empty_door_launch _)).elim
  | x => exact (hL (Or.inl rfl)).elim
  | t | ui | uc | di => rfl
  | dc =>
    by_cases hk : k.val+1<Q
    · apply False.elim
      apply hL
      right
      refine ⟨⟨k.val+1,hk⟩,?_⟩
      have h₁ : (Source.await k == Source.off) = false := rfl
      have h₂ : (Source.await k == Source.i1) = false := rfl
      have h₃ : (Rail.dc == Rail.x) = false := rfl
      simp [doorArrivals,sourceGuard,arrivals,h₁,h₂,h₃,hk]
    · exact (hF (congrArg Patrol.fire (door_terminal_accept k hk))).elim

/-- Nomination budget per dirty pass; restart passes start at the
smaller upBack reserve because X stays absent forever. -/
def dirtyUnit (d : Nat) : Nat := 3*(d+1)+1

def dirtyIndex {Q : Nat} : Option (Fin Q) → Nat
  | none => 0
  | some z => z.val+1

def ownedReserve (Q d : Nat) : Nat := 2*(d+1)*(Q+1)

/-- The current phase of one pure timer episode, retaining the latest
COUNT launch during dirty normalization if observed. -/
inductive TimerPhase (Q d : Nat) where
  | dirty (seen : Option (Fin Q)) (pass : Pass d)
  | owned (phase : OwnedPhase Q d)
  | stop

def TimerPhase.budget {Q d : Nat} : TimerPhase Q d → Nat
  | .dirty seen pass => dirtyUnit d * (Q-dirtyIndex seen) + pass.remaining + ownedReserve Q d
  | .owned phase => phase.budget
  | .stop => 0

def TimerPhase.nominate {Q d : Nat} : TimerPhase Q d → Port d
  | .dirty _ pass => pass.nominate
  | .owned phase => phase.nominate
  | .stop => .idle

def TimerPhase.Good {Q d : Nat} (s : Line Q d) : TimerPhase Q d → Prop
  | .dirty seen pass =>
    pass ≠ .done ∧ pass.WellFormed s ∧ s.fired = false ∧
      match seen with
      | none => True
      | some k => s.source = .await k ∧ ∀ j, pass ≠ .breakOut j
  | .owned phase => phase ≠ .done ∧ phase.Good s ∧ s.fired = false
  | .stop => s.fired = true

private theorem dirty_pos {d : Nat} (p : Pass d) (h : p ≠ .done) : 0<p.remaining := by
  cases p with
  | done => exact (h rfl).elim
  | extraDoor => exact Nat.zero_lt_one
  | breakOut k | upBack k | returnOut k =>
    have hk := k.isLt
    simp only [Pass.remaining]
    omega

/-- A rank of 1+index is charged only on real COUNT launches. -/
theorem next_launch_index {Q : Nat} (k k' : Fin Q) (r : Rail)
    (h : (doorArrivals (.await k) r).source = .count k') :
    k.val<k'.val := by
  cases r with
  | e | t | ui | uc | di | x => cases h
  | dc =>
    by_cases hk : k.val+1<Q
    · have h₁ : (Source.await k == Source.off) = false := rfl
      have h₂ : (Source.await k == Source.i1) = false := rfl
      have h₃ : (Rail.dc == Rail.x) = false := rfl
      simp [doorArrivals,sourceGuard,arrivals,h₁,h₂,h₃,hk] at h
      have H := congrArg Fin.val h
      change k.val+1=k'.val at H
      omega
    · have h₁ : (Source.await k == Source.off) = false := rfl
      have h₂ : (Source.await k == Source.i1) = false := rfl
      have h₃ : (Rail.dc == Rail.x) = false := rfl
      simp [doorArrivals,sourceGuard,arrivals,h₁,h₂,h₃,hk] at h

/-- Newly owned leg has the full (and exact) owned-work reserve. -/
theorem initial_owned_budget (Q d : Nat) :
    (OwnedPhase.initialOut (Q := Q) (doorSlot d)).budget = ownedReserve Q d := by
  change 2*(d+1)*Q + (d+1+d+1) = 2*(d+1)*(Q+1)
  rw [Nat.mul_succ (2*(d+1)) Q]
  omega

/-- Initial reserve stays below the published loose constant. -/
theorem timer_initial_budget (Q d : Nat) :
    (TimerPhase.dirty (Q := Q) none (.breakOut (0 : Fin (d+1)))).budget ≤
      32*(Q+1)*(d+2) := by
  change (3*(d+1)+1)*Q + (3*(d+1)+1-0) + 2*(d+1)*(Q+1) ≤ 32*(Q+1)*(d+2)
  rw [Nat.sub_zero,← Nat.mul_succ]
  rw [← Nat.add_mul,Nat.mul_comm 32 (Q+1),Nat.mul_assoc,Nat.mul_comm _ Q.succ]
  apply Nat.mul_le_mul_left
  omega

/-- A sharper arithmetic reading of the very same dirty/owned reserve. -/
theorem timer_initial_budget_eight (Q d : Nat) :
    (TimerPhase.dirty (Q := Q) none (.breakOut (0 : Fin (d+1)))).budget ≤
      8*(Q+1)*(d+2) := by
  change (3*(d+1)+1)*Q + (3*(d+1)+1-0) + 2*(d+1)*(Q+1) ≤ 8*(Q+1)*(d+2)
  rw [Nat.sub_zero,← Nat.mul_succ]
  rw [← Nat.add_mul,Nat.mul_comm 8 (Q+1),Nat.mul_assoc,Nat.mul_comm _ Q.succ]
  apply Nat.mul_le_mul_left
  omega

/-- At an actual dirty-pass exit the raw selected port carries the
pre-launch controller value; this is not inferred from an orphan U. -/
theorem dirty_exit_launch {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d)
    (hp : p ≠ .done) (hw : p.WellFormed s) (hx : p.step s m = .done)
    (hf : (lineStep s m).fired = false) :
    m = .door ∧ BreakFreePrefix s (d+1) ∧ launches s.source (s.rail (doorSlot d)) := by
  have he := (Pass.done_has_exit s p m hw hp hx).resolve_left (by simp [hf])
  have H : BreakFreePrefix s (d+1) ∧ PhaseExit s m := by
    cases p with
    | done | breakOut => exact he.elim
    | upBack k => exact ⟨hw.1,he⟩
    | returnOut k => exact ⟨hw.1,he⟩
    | extraDoor => exact ⟨fun j _ => by rw [hw j]; decide,he⟩
  cases m with
  | door => exact ⟨rfl,H.1,H.2.resolve_right (by simp [hf])⟩
  | _ => exact H.2.elim

private theorem pass_no_exit {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d)
    (hp : p.step s m ≠ .done) : ¬ p.IsExit s m := by
  classical
  intro h
  apply hp
  cases p <;> simp [Pass.step,h]

private theorem pass_no_new_break {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d)
    (old : ∀ j, p ≠ .breakOut j) (j : Fin (d+1)) : p.step s m ≠ .breakOut j := by
  classical
  cases p with
  | breakOut k => exact (old k rfl).elim
  | done => intro h; cases h
  | upBack k | returnOut k | extraDoor =>
    simp only [Pass.step]
    split
    · intro h; cases h
    · split
      · simp only [Pass.afterNomination]
        first | (intro h; cases h) | (split <;> intro h <;> cases h)
      · exact old j

/-- The initial pure observer. The source and rail are completely
arbitrary; only an already fired physical process is excluded. -/
def timerInit (Q d : Nat) : TimerPhase Q d := .dirty none (.breakOut 0)

theorem timer_init_good {Q d : Nat} (s : Line Q d) (hf : s.fired = false) :
    (timerInit Q d).Good s := by
  refine ⟨?_,?_,hf,True.intro⟩
  · intro h
    cases h
  · intro j hj
    exact (Nat.not_lt_zero j.val hj).elim

/-- Completion of a dirty pass checks the actual L1/L2 source event.
Seeing a dirty COUNT launches a fresh U/return sweep without repeating
the already permanent X sweep. -/
noncomputable def TimerPhase.step {Q d : Nat} (hQ : 0<Q) (s : Line Q d)
    (p : TimerPhase Q d) (m : Port d) : TimerPhase Q d := by
  classical
  exact if (lineStep s m).fired then .stop else
    match p with
    | .stop => .stop
    | .owned q => .owned (q.step hQ m)
    | .dirty old pass =>
      let p' := pass.step s m
      match p' with
      | .done =>
        match (doorArrivals s.source (s.rail (doorSlot d))).source with
        | .i0 => .owned (.initialOut (doorSlot d))
        | .count k => .dirty (some k) (.upBack (Fin.last d))
        | _ => .stop
      | _ => .dirty old p'

private theorem dirty_next_nom_budget {Q d : Nat} (seen : Option (Fin Q))
    (k : Fin Q) (p : Pass d) (hp : p ≠ .done)
    (hi : dirtyIndex seen < k.val+1) :
    (TimerPhase.dirty (some k) (.upBack (Fin.last d))).budget + 1 ≤
      (TimerPhase.dirty seen p).budget := by
  have hI : Q-(k.val+1)+1 ≤ Q-dirtyIndex seen := by have ht := k.isLt; omega
  have hM := Nat.mul_le_mul_left (dirtyUnit d) hI
  rw [Nat.mul_add,Nat.mul_one] at hM
  have hp := dirty_pos p hp
  change dirtyUnit d * (Q-(k.val+1)) + (d+3+d) + ownedReserve Q d + 1 ≤
    dirtyUnit d * (Q-dirtyIndex seen) + p.remaining + ownedReserve Q d
  have hu : d+3+d ≤ dirtyUnit d := by unfold dirtyUnit; omega
  omega

private theorem remaining_le_of_dirty {Q d : Nat} (seen : Option (Fin Q)) (p : Pass d)
    (hp : p ≠ .done) :
    ownedReserve Q d + 1 ≤ (TimerPhase.dirty seen p).budget := by
  have H := dirty_pos p hp
  simp only [TimerPhase.budget]
  omega

private theorem owned_budget_positive {Q d : Nat} (q : OwnedPhase Q d) (hQ : 0<Q)
    (hq : q ≠ .done) : 0<q.budget := by
  have H := owned_advance_budget q hQ hq
  omega

private theorem continuing_source {Q d : Nat} (s : Line Q d) (m : Port d) (p : Pass d)
    (k : Fin Q) (hs : s.source=.await k) (hr : p.step s m ≠ .done)
    (h : ∀ j, p ≠ .breakOut j) (hf : (lineStep s m).fired=false) :
    (lineStep s m).source=.await k := by
  cases m with
  | idle | body | top => exact hs
  | door =>
    have no := pass_no_exit s p .door hr
    have hL : ¬ launches s.source (s.rail (doorSlot d)) := by
      intro H
      apply no
      right
      cases p with
      | done => exact (hr rfl).elim
      | breakOut j => exact (h j rfl).elim
      | upBack | returnOut | extraDoor => exact .inl H
    change (serviceDoor s.source (s.rail (doorSlot d))).source = .await k
    change (serviceDoor s.source (s.rail (doorSlot d))).fire = false at hf
    rw [hs] at hf hL ⊢
    exact await_no_exit _ _ hL (by simp [hf])

private theorem bonus_le (P : Prop) [Decidable P] : (if P then 1 else 0) ≤ 1 := by
  split <;> decide

/-- Every literal single-port step preserves the aggregate timer
invariant and pays the next nominal unit when selected. Terminal
classifiers are actual A2, not clock timeouts. -/
theorem timer_local_step {Q d : Nat} (hQ : 0<Q) (s : Line Q d) (p : TimerPhase Q d)
    (m : Port d) (h : p.Good s) (hl : s.fired=false) :
    let p' := p.step hQ s m
    p'.Good (lineStep s m) ∧
      p'.budget + (if m=p.nominate then 1 else 0) ≤ p.budget := by
  classical
  by_cases hf : (lineStep s m).fired = true
  · have hpos : 0<p.budget := by
      cases p with
      | stop =>
        have H : s.fired=true := h
        exact Bool.noConfusion (H.symm.trans hl)
      | owned q => exact owned_budget_positive q hQ h.1
      | dirty seen pass =>
        have H := dirty_pos pass h.1
        simp only [TimerPhase.budget]
        omega
    have E : p.step hQ s m = .stop := by
      simp [TimerPhase.step,hf]
    simp only [E,TimerPhase.Good,TimerPhase.budget,hf,true_and]
    exact Nat.le_trans (Nat.add_le_add_left (bonus_le _) 0) hpos
  · have ff : (lineStep s m).fired = false := Bool.eq_false_iff.mpr hf
    cases p with
    | stop =>
      have H : s.fired=true := h
      exact Bool.noConfusion (H.symm.trans hl)
    | owned q =>
      have X := owned_good_step hQ s q m h.1 h.2.1
      have hn : q.step hQ m ≠ .done := by
        intro H
        rw [H] at X
        have xx : (lineStep s m).fired=true := X
        exact Bool.noConfusion (xx.symm.trans ff)
      have E : (TimerPhase.owned q).step hQ s m = .owned (q.step hQ m) := by
        simp [TimerPhase.step,hf]
      simp only [E,TimerPhase.Good,TimerPhase.budget]
      refine ⟨⟨hn,X,ff⟩,?_⟩
      change (q.step hQ m).budget+(if m=q.nominate then 1 else 0)≤q.budget
      by_cases H : m=q.nominate
      · rw [show q.step hQ m = q.advance hQ from if_pos H,if_pos H]
        exact Nat.le_of_eq (owned_advance_budget q hQ h.1)
      · rw [show q.step hQ m = q from if_neg H,if_neg H,Nat.add_zero]
        exact Nat.le_refl _
    | dirty seen pass =>
      have hp : pass ≠ .done := h.1
      have hw : pass.WellFormed s := h.2.1
      by_cases hx : pass.step s m = .done
      · obtain ⟨he,hb,hL⟩ := dirty_exit_launch s pass m hp hw hx ff
        subst m
        rcases hL with hI|⟨k,hK⟩
        · have E : (TimerPhase.dirty seen pass).step hQ s .door =
              .owned (.initialOut (doorSlot d)) := by
            simp [TimerPhase.step,hf,hx,hI]
          simp only [E,TimerPhase.Good,TimerPhase.budget,initial_owned_budget]
          refine ⟨⟨?_,owned_ui_launch s hb hI,ff⟩,?_⟩
          · intro hh
            cases hh
          · exact Nat.le_trans (Nat.add_le_add_left (bonus_le _) _) (remaining_le_of_dirty seen pass hp)
        · have E : (TimerPhase.dirty seen pass).step hQ s .door =
              .dirty (some k) (.upBack (Fin.last d)) := by
            simp [TimerPhase.step,hf,hx,hK]
          have hi : dirtyIndex seen < k.val+1 := by
            cases seen with
            | none => exact Nat.zero_lt_succ _
            | some z =>
              have hz := h.2.2.2.1
              rw [hz] at hK
              have L := next_launch_index z k _ hK
              exact Nat.succ_lt_succ L
          have hb' := break_prefix_hold s _ .door hb
          have hs := (count_launch_exact _ _ k hK).1
          have H := dirty_next_nom_budget seen k pass hp hi
          simp only [E,TimerPhase.Good]
          refine ⟨⟨?_,?_,ff,hs,?_⟩,?_⟩
          · intro hh
            cases hh
          · exact ⟨hb',fun j hj => (Nat.not_le_of_gt j.isLt hj).elim⟩
          · intro j h'
            cases h'
          · exact Nat.le_trans (Nat.add_le_add_left (bonus_le _) _) H
      · have E : (TimerPhase.dirty seen pass).step hQ s m = .dirty seen (pass.step s m) := by
          simp only [TimerPhase.step,hf]
          cases hx' : pass.step s m with
          | done => exact (hx hx').elim
          | _ => rfl
        have hw' := Pass.step_wellFormed s pass m hw
        have H := Pass.step_budget s pass m (Nat.ne_of_gt (dirty_pos pass hp))
        rw [E]
        refine ⟨⟨hx,hw',ff,?_⟩,?_⟩
        · cases seen with
          | none => trivial
          | some k =>
            have hK := h.2.2.2
            exact ⟨continuing_source s m pass k hK.1 hx hK.2 ff,
              pass_no_new_break s pass m hK.2⟩
        · change dirtyUnit d*(Q-dirtyIndex seen)+(pass.step s m).remaining+ownedReserve Q d+
            (if m=pass.nominate then 1 else 0) ≤
            dirtyUnit d*(Q-dirtyIndex seen)+pass.remaining+ownedReserve Q d
          omega

/-- The nonnominated top (which changes no controller and cannot fire)
stutters the timer's observer phase even though some rail bytes change. -/
theorem timer_top_stall {Q d : Nat} (hQ : 0<Q) (s : Line Q d) (p : TimerPhase Q d)
    (h : p.Good s) (hl : s.fired=false) (hn : Port.top ≠ p.nominate) :
    p.step hQ s .top = p := by
  classical
  have hf : (lineStep s .top).fired=false := hl
  cases p with
  | stop => simp [TimerPhase.step,hf]
  | owned q =>
    have hn' : Port.top ≠ q.nominate := hn
    simp only [TimerPhase.step,hf,Bool.false_eq_true,if_false]
    rw [show q.step hQ .top = q from if_neg hn']
  | dirty z q =>
    have hx : ¬ q.IsExit s .top := by
      intro H
      rcases H with HH|HH
      · rw [hf] at HH
        cases HH
      · cases q <;> exact HH
    have eq : q.step s .top=q := by
      have hn' : Port.top ≠ q.nominate := hn
      cases q <;> simp [Pass.step,hx,hn']
    have hp : q ≠ .done := h.1
    simp only [TimerPhase.step,hf,Bool.false_eq_true,if_false,eq]

/-- One raw mark may have a single port or the aliased top/door seam. -/
inductive RawPort (d : Nat) where
  | single (p : Port d)
  | seam

def RawPort.contains {d : Nat} : RawPort d → Port d → Prop
  | .single p, q => p=q
  | .seam, q => q=.top ∨ q=.door

structure TimerObs (Q d : Nat) where
  line : Line Q d
  phase : TimerPhase Q d

noncomputable def timerPortNext {Q d : Nat} (hQ : 0<Q)
    (s : TimerObs Q d) (m : Port d) : TimerObs Q d :=
  if s.line.fired then s else ⟨lineStep s.line m,s.phase.step hQ s.line m⟩

/-- On the shared raw label, evaluate the projections from their old
respective ports. They commute (top_door_commute) when the slots are
distinct. The observer can see launch/fire only in the door projection. -/
noncomputable def timerRawNext {Q d : Nat} (hQ : 0<Q)
    (s : TimerObs Q d) : RawPort d → TimerObs Q d
  | .single p => timerPortNext hQ s p
  | .seam => timerPortNext hQ (timerPortNext hQ s .top) .door

private theorem timer_port_budget {Q d : Nat} (hQ : 0<Q)
    (s : TimerObs Q d) (m : Port d) (h : s.phase.Good s.line) :
    let o := timerPortNext hQ s m
    o.phase.Good o.line ∧ o.phase.budget ≤ s.phase.budget ∧
      (s.line.fired=false → m=s.phase.nominate → o.phase.budget<s.phase.budget) := by
  cases he : s.line.fired
  · have H := timer_local_step hQ s.line s.phase m h he
    simp only [timerPortNext,he,Bool.false_eq_true,if_false]
    refine ⟨H.1,Nat.le_trans (Nat.le_add_right ..) H.2,?_⟩
    intro _ hm
    have hh := H.2
    rw [if_pos hm] at hh
    exact hh
  · simp [timerPortNext,he,h]

theorem timer_raw_budget {Q d : Nat} (hQ : 0<Q)
    (s : TimerObs Q d) (m : RawPort d) (h : s.phase.Good s.line) :
    let o := timerRawNext hQ s m
    o.phase.Good o.line ∧ o.phase.budget ≤ s.phase.budget ∧
      (s.line.fired=false → m.contains s.phase.nominate → o.phase.budget<s.phase.budget) := by
  cases m with
  | single p => exact timer_port_budget hQ s p h
  | seam =>
    let mid := timerPortNext hQ s .top
    have H := timer_port_budget hQ s .top h
    have J := timer_port_budget hQ mid .door H.1
    refine ⟨J.1,Nat.le_trans J.2.1 H.2.1,?_⟩
    intro hf hk
    rcases hk with hT|hD
    · exact Nat.lt_of_le_of_lt J.2.1 (H.2.2 hf hT.symm)
    · have ht : Port.top ≠ s.phase.nominate := by rw [hD]; intro h; cases h
      have hm : mid.phase = s.phase := by
        change (timerPortNext hQ s .top).phase = _
        simp only [timerPortNext,hf,Bool.false_eq_true,if_false]
        exact timer_top_stall hQ s.line s.phase h hf ht
      have hm' : mid.line.fired=false := by
        change (timerPortNext hQ s .top).line.fired=false
        simp [timerPortNext,hf,lineStep]
      have hh : .door=mid.phase.nominate := by rw [hm,hD]
      exact Nat.lt_of_lt_of_le (J.2.2 hm' hh) H.2.1

/-- The raw-step ABI for the purely rail/controller clock. -/
noncomputable def timerNext {Q d n : Nat} (hQ : 0<Q) (table : Fin n → RawPort d)
    (s : TimerObs Q d) (e : Fin n) : TimerObs Q d := timerRawNext hQ s (table e)

def timerObsInit {Q d : Nat} (s : Line Q d) : TimerObs Q d := ⟨s,timerInit Q d⟩

private theorem timer_word_good {Q d n : Nat} (hQ : 0<Q) (table : Fin n → RawPort d)
    (s : TimerObs Q d) (hs : s.phase.Good s.line) (w : List (Fin n)) :
    let y := GGTiming.runMarks (timerNext hQ table) s w
    y.phase.Good y.line := by
  induction w generalizing s with
  | nil => exact hs
  | cons e w ih => exact ih _ (timer_raw_budget hQ s (table e) hs).1

/-- Complete arbitrary-residual pure clock using the actual row
projections. Nomination chooses one raw scheduler index, including
when top and door are the same index. -/
noncomputable def pureTimerCountdown {Q d n : Nat} (hQ : 0<Q) (table : Fin n → RawPort d)
    (pick : TimerPhase Q d → Fin n)
    (real : ∀ p x, p.Good x → x.fired = false → (table (pick p)).contains p.nominate)
    (s : Line Q d) (hs : s.fired=false) :
    Countdown (timerNext hQ table) (fun y => y.line.fired=true) (timerObsInit s) where
  budget w := (GGTiming.runMarks (timerNext hQ table) (timerObsInit s) w).phase.budget
  nominate w := pick (GGTiming.runMarks (timerNext hQ table) (timerObsInit s) w).phase
  decrease := by
    intro w hl e
    rw [GGTiming.runMarks_append]
    let o := GGTiming.runMarks (timerNext hQ table) (timerObsInit s) w
    change (timerNext hQ table o e).phase.budget+(if e=pick o.phase then 1 else 0) ≤ o.phase.budget
    have good : o.phase.Good o.line :=
      timer_word_good hQ table (timerObsInit s) (timer_init_good s hs) w
    have H := timer_raw_budget hQ o (table e) good
    by_cases he : e=pick o.phase
    · rw [if_pos he]
      exact H.2.2 (Bool.eq_false_iff.mpr hl) (he.symm ▸ real _ _ good (Bool.eq_false_iff.mpr hl))
    · rw [if_neg he,Nat.add_zero]
      exact H.2.1

end L4.ResidualSweep
