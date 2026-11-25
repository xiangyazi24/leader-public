import Leader.L4.ResidualSweep

/-! An aliased seam has two timer projections but is one scheduler mark. -/
namespace L4.ResidualSweep
open FixedResidual

noncomputable def passPort {Q d : Nat} (s : PassObs Q d) (m : Port d) : PassObs Q d :=
  passNext (fun _ : Fin 1 => m) s 0

private theorem budget_port {Q d : Nat} (s : PassObs Q d) (m : Port d) :
    (passPort s m).phase.remaining ≤ s.phase.remaining ∧
    (s.phase ≠ .done → m = s.phase.nominate →
      (passPort s m).phase.remaining < s.phase.remaining) := by
  classical
  have ru (p : Pass d) (h : p ≠ .done) : p.remaining ≠ 0 := by
    cases p with
    | done => exact (h rfl).elim
    | extraDoor => exact Nat.one_ne_zero
    | breakOut k | returnOut k | upBack k =>
      have h := k.isLt
      simp only [Pass.remaining]
      omega
  by_cases hD : s.phase = .done
  · simp [passPort,passNext,hD]
  · have E : (passPort s m).phase = s.phase.step s.line m := by
      cases h : s.phase with
      | done => exact (hD h).elim
      | _ => simp only [passPort,passNext,h]
    rw [E]
    have hb := Pass.step_budget s.line s.phase m (ru _ hD)
    constructor
    · exact Nat.le_trans (Nat.le_add_right ..) hb
    · intro _ hm
      rw [if_pos hm] at hb
      exact hb

private theorem same_phase_of_no_drop {Q d : Nat} (s : PassObs Q d) (m : Port d)
    (h : s.phase.remaining ≤ (passPort s m).phase.remaining) :
    (passPort s m).phase = s.phase := by
  classical
  by_cases hD : s.phase = .done
  · simp only [passPort,passNext,hD]
  · by_cases hN : m = s.phase.nominate
    · exact (Nat.not_lt_of_ge h ((budget_port s m).2 hD hN)).elim
    · have E : (passPort s m).phase =
          if s.phase.IsExit s.line m then .done else s.phase := by
        cases hp : s.phase with
        | done => exact (hD hp).elim
        | _ =>
          simp only [hp,passPort,passNext,Pass.step]
          have hn : ¬ m = _ := hp ▸ hN
          simp only [if_neg hn]
      rw [E]
      split
      · rename_i hx
        have hh : s.phase.remaining ≤ 0 := by
          rw [E,if_pos hx] at h
          exact h
        cases hp : s.phase with
        | done => exact (hD hp).elim
        | extraDoor => rw [hp] at hh; exact (Nat.not_succ_le_zero 0 hh).elim
        | breakOut k | upBack k | returnOut k =>
          have hk := k.isLt
          rw [hp] at hh
          simp only [Pass.remaining] at hh
          omega
      · rfl

/-- All projections belonging to one raw label. Singleton lists encode
ordinary ports; the aliased label contains top and door. -/
noncomputable def multiplePassNext {Q d n : Nat} (ports : Fin n → List (Port d))
    (s : PassObs Q d) (e : Fin n) : PassObs Q d := (ports e).foldl passPort s

private theorem list_budget {Q d : Nat} (s : PassObs Q d) (ms : List (Port d)) :
    (ms.foldl passPort s).phase.remaining ≤ s.phase.remaining ∧
    (s.phase ≠ .done → s.phase.nominate ∈ ms →
      (ms.foldl passPort s).phase.remaining < s.phase.remaining) := by
  induction ms generalizing s with
  | nil => exact ⟨Nat.le_refl _, fun _ h => (List.not_mem_nil h).elim⟩
  | cons m ms ih =>
    let q := passPort s m
    have hb := budget_port s m
    have h := ih q
    refine ⟨Nat.le_trans h.1 hb.1,?_⟩
    intro hs hm
    rcases List.mem_cons.mp hm with hm|hm
    · exact Nat.lt_of_le_of_lt h.1 (hb.2 hs hm.symm)
    · by_cases H : q.phase.remaining < s.phase.remaining
      · exact Nat.lt_of_le_of_lt h.1 H
      · have hsame := same_phase_of_no_drop s m (by exact Nat.le_of_not_gt H)
        have hq : q.phase ≠ .done := by rw [show q.phase = s.phase from hsame]; exact hs
        have hnom : q.phase.nominate ∈ ms := by
          rw [show q.phase = s.phase from hsame]; exact hm
        exact Nat.lt_of_lt_of_le (h.2 hq hnom) hb.1

/-- One selected raw label is charged at most once, regardless of the
number of projected operations it contains. -/
noncomputable def multiplePassCountdown {Q d n : Nat} (ports : Fin n → List (Port d))
    (pick : Pass d → Fin n)
    (real : ∀ p : Pass d, p ≠ .done → p.nominate ∈ ports (pick p))
    (s : Line Q d) :
    Countdown (multiplePassNext ports) (fun y => y.phase = .done) (passInit s) where
  budget w := (GGTiming.runMarks (multiplePassNext ports) (passInit s) w).phase.remaining
  nominate w := pick (GGTiming.runMarks (multiplePassNext ports) (passInit s) w).phase
  decrease := by
    intro w hl e
    rw [GGTiming.runMarks_append]
    let o := GGTiming.runMarks (multiplePassNext ports) (passInit s) w
    change ((ports e).foldl passPort o).phase.remaining +
      (if e=pick o.phase then 1 else 0) ≤ o.phase.remaining
    have h := list_budget o (ports e)
    by_cases he : e=pick o.phase
    · rw [if_pos he]
      exact h.2 hl (he.symm ▸ real _ hl)
    · rw [if_neg he,Nat.add_zero]
      exact h.1

/-- The two rail writes at the shared seam commute since the top and
door slots are distinct. Their local inputs are the old pair. -/
theorem top_door_commute {Q d : Nat} (hd : 0<d) (s : Line Q d) :
    lineStep (lineStep s .top) .door = lineStep (lineStep s .door) .top := by
  have hne : topSlot d ≠ doorSlot d := by
    intro h
    have H := congrArg Fin.val h
    change 0=d at H
    omega
  have hne' := Ne.symm hne
  simp only [lineStep,if_neg hne']
  congr 1
  funext j
  by_cases ht : j=topSlot d
  · subst j
    simp [hne]
  · by_cases hb : j=doorSlot d <;> simp [ht,hb,hne']

#print axioms multiplePassCountdown
#print axioms top_door_commute

end L4.ResidualSweep
