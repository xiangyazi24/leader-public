import Leader.L3.Bank.RepairDigitPacketRelease

/-!
# Lemma e-packet: the reached-state invariant (repair.tex 1300-1326), target shapes

The paper's packet-order invariant on the target cells of one complete pair:

* (a) every moving packet lies left of every settled operand, front and live carry;
* (b) a live carry has an empty own input, and strictly behind it every input is empty or
  moving (no carry): in particular there is at most one live carry.

On the T22 lane (`L3.CohortDomination.cohortEdge`, literal rows) this is the existence of a cut
`m` (`OrderAt`): the cells `[R, m)` are carry-free and hold `E` or `P`; no cell at or after `m`
holds a moving packet; no cell after `m` carries; a carry at `m` has an empty input.
`orderStep` proves that every edge of the pair, including the export into a free border with
either tail bit, preserves it; `orderPaper` recovers (a) and (b); `orderMobileFree` starts it at
every mobile-free cut (only empty and settled inputs, no carry), which is where the paper starts
it, after the inherited mobile work. All claims are insensitive to operand values.
Model check (research/lean-l3/wip/r10c-mc/release_mc.py, the paper's (a)+(b) directly):
closed for R = 2..5 (37, 175, 781, 3367 states), no violation.

The fourth clause of the paper (the pending queue is a consecutive suffix of the accepted serial
stream) is a ghost statement and is not part of this shape invariant.
-/

namespace L3.DigitPacketOrder

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.DigitPacketRelease

/-- A carry-free cell holding nothing or a moving packet. Consumer: `OrderAt`. -/
def CleanT (i : BankRepairDigitInSh) (l : Bool) : Prop := l = false ∧ (i = .E ∨ ∃ T, i = .P T)

/-- A cell input that is not a moving packet. Consumer: `OrderAt`. -/
def NotPT (i : BankRepairDigitInSh) : Prop := ∀ T, i ≠ .P T

/-- **The packet-order invariant with cut `m`.** Consumer: `orderStep`, `orderPaper`, and the
settled-empty and renewal-trial phases of Lemma e-packet. -/
def OrderAt (R : Nat) (s : CohortLane) (m : Nat) : Prop :=
  R ≤ m ∧ m ≤ 2 * R ∧ (∀ q, R ≤ q → q < m → CleanT (s.inp q) (s.live q)) ∧
    (∀ q, m ≤ q → q < 2 * R → NotPT (s.inp q)) ∧
    (∀ q, m < q → q < 2 * R → s.live q = false) ∧
    (m < 2 * R → s.live m = true → s.inp m = .E)

/-- The invariant. Consumer: the phases of Lemma e-packet after the inherited mobile work. -/
def PacketOrder (R : Nat) (s : CohortLane) : Prop := ∃ m, OrderAt R s m

/-! ### Local rows -/

/-- Input motion between two clean cells stays clean. Consumer: `orderStep`. -/
theorem finA (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (hx : CleanT ix kx) (hy : CleanT iy ky) :
    CleanT (bankRepairDigitFinStep bx ix kx iy ky).1 (bankRepairDigitFinStep bx ix kx iy ky).2.1 ∧
      CleanT (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, CleanT] at hx hy ⊢

/-- Input motion from a clean cell into the cut cell. Consumer: `orderStep`. -/
theorem finB (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (hx : CleanT ix kx) (hy : NotPT iy) (hk : ky = true → iy = .E) :
    (CleanT (bankRepairDigitFinStep bx ix kx iy ky).1 (bankRepairDigitFinStep bx ix kx iy ky).2.1 ∧
      NotPT (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 ∧
      ((bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = true →
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = .E)) ∨
    (CleanT (bankRepairDigitFinStep bx ix kx iy ky).1 (bankRepairDigitFinStep bx ix kx iy ky).2.1 ∧
      CleanT (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2) ∨
    (NotPT (bankRepairDigitFinStep bx ix kx iy ky).1 ∧
      (bankRepairDigitFinStep bx ix kx iy ky).2.1 = false ∧
      NotPT (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 ∧
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = false) := by
  cases bx <;> cases kx <;> cases ky <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, CleanT, NotPT] at hx hy hk ⊢

/-- Input motion inside the packet-free suffix. Consumer: `orderStep`. -/
theorem finC (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (hx : NotPT ix) (hy : NotPT iy) (hky : ky = false) (hk : kx = true → ix = .E) :
    (NotPT (bankRepairDigitFinStep bx ix kx iy ky).1 ∧
      NotPT (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 ∧
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = false ∧
      ((bankRepairDigitFinStep bx ix kx iy ky).2.1 = true →
        (bankRepairDigitFinStep bx ix kx iy ky).1 = .E ∧ (kx = true ∨ bx = true))) ∨
    (kx = true ∧
      CleanT (bankRepairDigitFinStep bx ix kx iy ky).1 (bankRepairDigitFinStep bx ix kx iy ky).2.1 ∧
      NotPT (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 ∧
      ((bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = true →
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = .E)) := by
  subst hky
  cases bx <;> cases kx <;>
    rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitFinStep, CleanT, NotPT] at hx hy hk ⊢

/-- The terminal row on a clean last cell. Consumer: `orderStep`. -/
theorem termClean (ix : BankRepairDigitInSh) (kx : Bool) (h : CleanT ix kx) :
    CleanT (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 ∨
      (NotPT (cohortTermStep ix kx).1 ∧ (cohortTermStep ix kx).2 = false) := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [cohortTermStep, CleanT, NotPT] at h ⊢

/-- The terminal row on a packet-free last cell. Consumer: `orderStep`. -/
theorem termNotP (ix : BankRepairDigitInSh) (kx : Bool) (h : NotPT ix) :
    NotPT (cohortTermStep ix kx).1 ∧ (cohortTermStep ix kx).2 = false := by
  cases kx <;> rcases ix with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [cohortTermStep, NotPT] at h ⊢

/-- Delivery into a clean border. Consumer: `orderStep`. -/
theorem delClean (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (h : CleanT iy ky) :
    CleanT (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, CleanT] at h ⊢

/-- Delivery into the border when the cut is at the border: export makes it clean.
Consumer: `orderStep`. -/
theorem delCut (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (h : NotPT iy) (hk : ky = true → iy = .E) :
    (NotPT (bankRepairDigitDelStep ox iy ky).2.1 ∧
      ((bankRepairDigitDelStep ox iy ky).2.2 = true → (bankRepairDigitDelStep ox iy ky).2.1 = .E)) ∨
    CleanT (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 := by
  rcases ox with _ | _ | ⟨_ | _⟩ <;> cases ky <;> rcases iy with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    simp [bankRepairDigitDelStep, CleanT, NotPT] at h hk ⊢

/-! ### The frame -/

/-- The invariant at a new cut from the old one and the changed spots. Consumer: `orderStep`. -/
theorem orderFrame (R m m' : Nat) (Sp : Nat → Prop) (s s' : CohortLane) (h : OrderAt R s m)
    (hsame : ∀ i, ¬ Sp i → s'.inp i = s.inp i ∧ s'.live i = s.live i)
    (hm1 : R ≤ m') (hm2 : m' ≤ 2 * R)
    (hpre : ∀ q, ¬ Sp q → q < m' → q < m)
    (hsuf : ∀ q, ¬ Sp q → m' ≤ q → m ≤ q)
    (hlv : ∀ q, ¬ Sp q → m' < q → q < 2 * R → m < q)
    (hlm : ¬ Sp m' → m' < 2 * R → m < m' ∨ m' = m)
    (sp1 : ∀ q, Sp q → R ≤ q → q < m' → CleanT (s'.inp q) (s'.live q))
    (sp2 : ∀ q, Sp q → m' ≤ q → q < 2 * R → NotPT (s'.inp q))
    (sp3 : ∀ q, Sp q → m' < q → q < 2 * R → s'.live q = false)
    (sp4 : Sp m' → m' < 2 * R → s'.live m' = true → s'.inp m' = .E) :
    OrderAt R s' m' := by
  obtain ⟨_, _, h3, h4, h5, h6⟩ := h
  refine ⟨hm1, hm2, ?_, ?_, ?_, ?_⟩
  · intro q hq1 hq2
    by_cases hs : Sp q
    · exact sp1 q hs hq1 hq2
    · obtain ⟨a, b⟩ := hsame q hs
      rw [a, b]
      exact h3 q hq1 (hpre q hs hq2)
  · intro q hq1 hq2
    by_cases hs : Sp q
    · exact sp2 q hs hq1 hq2
    · rw [(hsame q hs).1]
      exact h4 q (hsuf q hs hq1) hq2
  · intro q hq1 hq2
    by_cases hs : Sp q
    · exact sp3 q hs hq1 hq2
    · rw [(hsame q hs).2]
      exact h5 q (hlv q hs hq1 hq2) hq2
  · intro hm hl
    by_cases hs : Sp m'
    · exact sp4 hs hm hl
    · obtain ⟨a, b⟩ := hsame m' hs
      rw [b] at hl
      rw [a]
      rcases hlm hs hm with hlt | heq
      · rw [h5 m' hlt hm] at hl
        exact absurd hl (by decide)
      · subst heq
        exact h6 hm hl

/-! ### Cell values after one edge -/

/-- Cells of the input-motion row. Consumer: `orderStep`. -/
theorem finCells (R k : Nat) (s : CohortLane) (h1 : R ≤ k) (h2 : k + 1 < 2 * R) :
    ((cohortEdge R s k).inp k = (finOf R s k).1 ∧ (cohortEdge R s k).live k = (finOf R s k).2.1) ∧
    ((cohortEdge R s k).inp (k + 1) = (finOf R s k).2.2.1 ∧
      (cohortEdge R s k).live (k + 1) = (finOf R s k).2.2.2) ∧
    (∀ i, ¬ (i = k ∨ i = k + 1) →
      (cohortEdge R s k).inp i = s.inp i ∧ (cohortEdge R s k).live i = s.live i) := by
  obtain ⟨hi, hl⟩ := edgeFin R k s h1 h2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun i hi' => ?_⟩
  · rw [hi]; simp [cohortUpd]
  · rw [hl]; simp [cohortUpd]
  · rw [hi]; simp [cohortUpd]
  · rw [hl]; simp [cohortUpd]
  · have e1 : i ≠ k := fun e => hi' (Or.inl e)
    have e2 : i ≠ k + 1 := fun e => hi' (Or.inr e)
    rw [hi, hl]
    simp [cohortUpd, e1, e2]

/-- **Closure.** Every edge of the pair preserves the packet-order invariant, including the
export into a free border. Consumer: the settled-empty and renewal-trial phases of Lemma
e-packet (`PacketOrder` is their class). -/
theorem orderStep (R m k : Nat) (s : CohortLane) (hR : 2 ≤ R) (h : OrderAt R s m) :
    PacketOrder R (cohortEdge R s k) := by
  have h0 := h
  obtain ⟨hm1, hm2, h3, h4, h5, h6⟩ := h
  by_cases e1 : k + 1 < R
  · obtain ⟨hi, hl⟩ := edgePipe R k s e1
    refine ⟨m, ?_⟩
    unfold OrderAt
    rw [hi, hl]
    exact h0
  by_cases e2 : k + 1 = R
  · obtain ⟨hi, hl⟩ := edgeDel R k s e2
    have hR' : (cohortEdge R s k).inp R =
        (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.1 ∧
        (cohortEdge R s k).live R = (bankRepairDigitDelStep (s.out k) (s.inp R) (s.live R)).2.2 := by
      rw [hi, hl, e2]
      simp [cohortUpd]
    have hoff : ∀ i, ¬ (i = R) →
        (cohortEdge R s k).inp i = s.inp i ∧ (cohortEdge R s k).live i = s.live i := by
      intro i hi'
      rw [hi, hl, e2]
      simp [cohortUpd, hi']
    by_cases hmR : R < m
    · -- the border is clean
      have hc := delClean (s.out k) (s.inp R) (s.live R) (h3 R (Nat.le_refl R) hmR)
      refine ⟨m, orderFrame R m m (fun i => i = R) s _ h0 hoff hm1 hm2
        (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
        ?_ ?_ ?_ ?_⟩
      · intro q hq _ _
        rw [hq, hR'.1, hR'.2]
        exact hc
      · intro q hq hq1 _
        omega
      · intro q hq hq1 _
        omega
      · intro hq
        omega
    · have hm : m = R := by omega
      subst hm
      rcases delCut (s.out k) (s.inp m) (s.live m) (h4 m (Nat.le_refl m) (by omega))
          (h6 (by omega)) with hc | hc
      · refine ⟨m, orderFrame m m m (fun i => i = m) s _ h0 hoff hm1 hm2
          (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
          ?_ ?_ ?_ ?_⟩
        · intro q _ _ hq
          omega
        · intro q hq _ _
          rw [hq, hR'.1]
          exact hc.1
        · intro q hq hq1 _
          omega
        · intro _ _ hl'
          rw [hR'.2] at hl'
          rw [hR'.1]
          exact hc.2 hl'
      · refine ⟨m + 1, orderFrame m m (m + 1) (fun i => i = m) s _ h0 hoff (by omega) (by omega)
          (fun q hq h => by omega) (fun q _ h => by omega) (fun q _ h _ => by omega)
          (fun _ _ => Or.inl (by omega)) ?_ ?_ ?_ ?_⟩
        · intro q hq _ _
          rw [hq, hR'.1, hR'.2]
          exact hc
        · intro q hq hq1 _
          omega
        · intro q hq hq1 _
          omega
        · intro hq
          omega
  by_cases e3 : k + 1 < 2 * R
  · have hk : R ≤ k := by omega
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hoff⟩ := finCells R k s hk e3
    unfold finOf at hx1 hx2 hy1 hy2
    by_cases c1 : k + 1 < m
    · -- both cells in the clean prefix
      have hc := finA (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
        (h3 k hk (by omega)) (h3 (k + 1) (by omega) c1)
      refine ⟨m, orderFrame R m m (fun i => i = k ∨ i = k + 1) s _ h0 hoff hm1 hm2
        (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
        ?_ ?_ ?_ ?_⟩
      · intro q hq _ _
        rcases hq with hq | hq <;> subst hq
        · rw [hx1, hx2]; exact hc.1
        · rw [hy1, hy2]; exact hc.2
      · intro q hq hq1 _
        omega
      · intro q hq hq1 _
        omega
      · intro hq
        omega
    by_cases c2 : k + 1 = m
    · -- the right cell is the cut
      rcases finB (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
          (h3 k hk (by omega)) (h4 (k + 1) (by omega) e3) (by rw [c2]; exact h6 (by omega))
          with hc | hc | hc
      · refine ⟨m, orderFrame R m m (fun i => i = k ∨ i = k + 1) s _ h0 hoff hm1 hm2
          (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
          ?_ ?_ ?_ ?_⟩
        · intro q hq _ hq2
          rcases hq with hq | hq <;> subst hq
          · rw [hx1, hx2]; exact hc.1
          · omega
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq
          · omega
          · rw [hy1]; exact hc.2.1
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq <;> omega
        · intro _ _ hl'
          rw [← c2, hy2] at hl'
          rw [← c2, hy1]
          exact hc.2.2 hl'
      · refine ⟨m + 1, orderFrame R m (m + 1) (fun i => i = k ∨ i = k + 1) s _ h0 hoff
          (by omega) (by omega)
          (fun q hq h => by omega) (fun q _ h => by omega) (fun q _ h _ => by omega)
          (fun _ _ => Or.inl (by omega)) ?_ ?_ ?_ ?_⟩
        · intro q hq _ _
          rcases hq with hq | hq <;> subst hq
          · rw [hx1, hx2]; exact hc.1
          · rw [hy1, hy2]; exact hc.2
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq <;> omega
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq <;> omega
        · intro hq
          omega
      · refine ⟨k, orderFrame R m k (fun i => i = k ∨ i = k + 1) s _ h0 hoff
          hk (by omega)
          (fun q _ h => by omega) (fun q hq h => by
            have : q ≠ k := fun e => hq (Or.inl e)
            have : q ≠ k + 1 := fun e => hq (Or.inr e)
            omega)
          (fun q hq h _ => by
            have : q ≠ k + 1 := fun e => hq (Or.inr e)
            omega)
          (fun hq _ => absurd (Or.inl rfl) hq) ?_ ?_ ?_ ?_⟩
        · intro q _ _ hq2
          omega
        · intro q hq _ _
          rcases hq with hq | hq <;> subst hq
          · rw [hx1]; exact hc.1
          · rw [hy1]; exact hc.2.2.1
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq
          · omega
          · rw [hy2]; exact hc.2.2.2
        · intro _ _ hl'
          rw [hx2, hc.2.1] at hl'
          exact absurd hl' (by decide)
    · -- both cells in the packet-free suffix
      have hmk : m ≤ k := by omega
      have hxl : s.live k = true → s.inp k = .E := by
        intro hl'
        rcases Nat.lt_or_ge m k with hlt | hge
        · rw [h5 k hlt (by omega)] at hl'
          exact absurd hl' (by decide)
        · have : k = m := by omega
          subst this
          exact h6 (by omega) hl'
      rcases finC (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
          (h4 k hmk (by omega)) (h4 (k + 1) (by omega) e3) (h5 (k + 1) (by omega) e3) hxl
          with hc | hc
      · refine ⟨m, orderFrame R m m (fun i => i = k ∨ i = k + 1) s _ h0 hoff hm1 hm2
          (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
          ?_ ?_ ?_ ?_⟩
        · intro q hq _ hq2
          rcases hq with hq | hq <;> subst hq <;> omega
        · intro q hq _ _
          rcases hq with hq | hq <;> subst hq
          · rw [hx1]; exact hc.1
          · rw [hy1]; exact hc.2.1
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq
          · rw [hx2]
            cases hb : (bankRepairDigitFinStep (decide (q = R)) (s.inp q) (s.live q)
              (s.inp (q + 1)) (s.live (q + 1))).2.1
            · rfl
            · exfalso
              rcases (hc.2.2.2 hb).2 with hk' | hb'
              · rw [h5 q hq1 (by omega)] at hk'
                exact absurd hk' (by decide)
              · have : q = R := of_decide_eq_true hb'
                omega
          · rw [hy2]; exact hc.2.2.1
        · intro hq _ hl'
          rcases hq with hq | hq
          · rw [hq, hx2] at hl'
            rw [hq, hx1]
            exact (hc.2.2.2 hl').1
          · omega
      · have hkm : k = m := by
          rcases Nat.lt_or_ge m k with hlt | hge
          · rw [h5 k hlt (by omega)] at hc
            exact absurd hc.1 (by decide)
          · omega
        subst hkm
        refine ⟨k + 1, orderFrame R k (k + 1) (fun i => i = k ∨ i = k + 1) s _ h0 hoff
          (by omega) (by omega)
          (fun q hq h => by
            have : q ≠ k := fun e => hq (Or.inl e)
            omega)
          (fun q _ h => by omega) (fun q _ h _ => by omega)
          (fun hq _ => absurd (Or.inr rfl) hq) ?_ ?_ ?_ ?_⟩
        · intro q hq _ _
          rcases hq with hq | hq <;> subst hq
          · rw [hx1, hx2]; exact hc.2.1
          · omega
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq
          · omega
          · rw [hy1]; exact hc.2.2.1
        · intro q hq hq1 _
          rcases hq with hq | hq <;> subst hq <;> omega
        · intro _ _ hl'
          rw [hy2] at hl'
          rw [hy1]
          exact hc.2.2.2 hl'
  by_cases e4 : k + 1 = 2 * R
  · obtain ⟨hi, hl⟩ := edgeTerm R k s e4
    have hK : (cohortEdge R s k).inp k = (cohortTermStep (s.inp k) (s.live k)).1 ∧
        (cohortEdge R s k).live k = (cohortTermStep (s.inp k) (s.live k)).2 := by
      rw [hi, hl]
      simp [cohortUpd]
    have hoff : ∀ i, ¬ (i = k) →
        (cohortEdge R s k).inp i = s.inp i ∧ (cohortEdge R s k).live i = s.live i := by
      intro i hi'
      rw [hi, hl]
      simp [cohortUpd, hi']
    by_cases c : k < m
    · rcases termClean (s.inp k) (s.live k) (h3 k (by omega) c) with hc | hc
      · refine ⟨m, orderFrame R m m (fun i => i = k) s _ h0 hoff hm1 hm2
          (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
          ?_ ?_ ?_ ?_⟩
        · intro q hq _ _
          rw [hq, hK.1, hK.2]; exact hc
        · intro q hq hq1 _
          omega
        · intro q hq hq1 _
          omega
        · intro hq
          omega
      · refine ⟨k, orderFrame R m k (fun i => i = k) s _ h0 hoff (by omega) (by omega)
          (fun q hq h => by omega) (fun q hq h => by omega) (fun q hq h _ => by omega)
          (fun hq _ => absurd rfl hq) ?_ ?_ ?_ ?_⟩
        · intro q _ _ hq2
          omega
        · intro q hq _ _
          rw [hq, hK.1]; exact hc.1
        · intro q hq hq1 _
          omega
        · intro _ _ hl'
          rw [hK.2, hc.2] at hl'
          exact absurd hl' (by decide)
    · have hc := termNotP (s.inp k) (s.live k) (h4 k (by omega) (by omega))
      refine ⟨m, orderFrame R m m (fun i => i = k) s _ h0 hoff hm1 hm2
        (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h _ => h) (fun _ _ => Or.inr rfl)
        ?_ ?_ ?_ ?_⟩
      · intro q hq _ hq2
        omega
      · intro q hq _ _
        rw [hq, hK.1]; exact hc.1
      · intro q hq _ _
        rw [hq, hK.2]; exact hc.2
      · intro hq _ hl'
        rw [hq, hK.2, hc.2] at hl'
        exact absurd hl' (by decide)
  · rw [cohortEdgeFar R k s (by omega)]
    exact ⟨m, h0⟩

/-- **The paper's clauses.** (a) no settled operand, front or carry lies left of a moving packet;
(b) a live carry has an empty input and only carry-free empty or moving cells behind it.
Consumer: the settled-empty phase of Lemma e-packet (charges `A`, `D`, `X`). -/
theorem orderPaper (R m : Nat) (s : CohortLane) (h : OrderAt R s m) :
    (∀ q q', R ≤ q' → q' < q → q < 2 * R → (∃ T, s.inp q = .P T) →
      s.live q' = false ∧ s.inp q' ≠ .X ∧ ∀ T, s.inp q' ≠ .S T) ∧
    (∀ q, R ≤ q → q < 2 * R → s.live q = true → s.inp q = .E ∧
      ∀ q', R ≤ q' → q' < q → s.live q' = false ∧ (s.inp q' = .E ∨ ∃ T, s.inp q' = .P T)) := by
  obtain ⟨hm1, _, h3, h4, h5, h6⟩ := h
  refine ⟨fun q q' hq' hlt hq hp => ?_, fun q hq1 hq2 hl => ?_⟩
  · have hqm : q < m := by
      rcases Nat.lt_or_ge q m with h' | h'
      · exact h'
      · obtain ⟨T, hT⟩ := hp
        exact absurd hT (h4 q h' hq T)
    obtain ⟨hl, hi⟩ := h3 q' hq' (by omega)
    refine ⟨hl, ?_, fun T hT => ?_⟩
    · intro hX
      rw [hX] at hi
      rcases hi with hi | ⟨_, hi⟩ <;> cases hi
    · rw [hT] at hi
      rcases hi with hi | ⟨_, hi⟩ <;> cases hi
  · have hqm : q = m := by
      rcases Nat.lt_or_ge q m with h' | h'
      · rw [(h3 q hq1 h').1] at hl
        exact absurd hl (by decide)
      · rcases Nat.lt_or_ge m q with h'' | h''
        · rw [h5 q h'' hq2] at hl
          exact absurd hl (by decide)
        · omega
    subst hqm
    exact ⟨h6 hq2 hl, fun q' hq' hlt => h3 q' hq' hlt⟩

/-- **Start.** Every mobile-free cut (no carry, only empty or settled inputs) satisfies the
invariant with cut `R`. Consumer: the e-packet composition, at the end of the inherited
mobile work phase. -/
theorem orderMobileFree (R : Nat) (s : CohortLane)
    (h : ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (s.inp q = .E ∨ ∃ T, s.inp q = .S T)) :
    OrderAt R s R := by
  refine ⟨Nat.le_refl R, by omega, fun q h1 h2 => absurd h2 (by omega), ?_, ?_, ?_⟩
  · intro q h1 h2 T hT
    rcases (h q h1 h2).2 with hi | ⟨T', hi⟩ <;> rw [hi] at hT <;> cases hT
  · intro q h1 h2
    exact (h q (by omega) h2).1
  · intro h2 hl
    rw [(h R (Nat.le_refl R) h2).1] at hl
    exact absurd hl (by decide)

end L3.DigitPacketOrder

#print axioms L3.DigitPacketOrder.finA
#print axioms L3.DigitPacketOrder.finB
#print axioms L3.DigitPacketOrder.finC
#print axioms L3.DigitPacketOrder.termClean
#print axioms L3.DigitPacketOrder.termNotP
#print axioms L3.DigitPacketOrder.delClean
#print axioms L3.DigitPacketOrder.delCut
#print axioms L3.DigitPacketOrder.orderFrame
#print axioms L3.DigitPacketOrder.finCells
#print axioms L3.DigitPacketOrder.orderStep
#print axioms L3.DigitPacketOrder.orderPaper
#print axioms L3.DigitPacketOrder.orderMobileFree
