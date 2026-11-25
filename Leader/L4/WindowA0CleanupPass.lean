import Leader.L4.WindowA0ForwardSweep

/-! One real cleanup pass on tagged I_H: X (ignore launches), reverse
U, forward seed/return sweep. At a phase boundary the previous mark
has already been taken, and the next phase does not replay it. -/
namespace L4.WindowA0CleanupPass
open WindowA0ClosedEntry

inductive State (p c n : Nat) where
  | x (s : WindowA0XSweep.SweepState p c n)
  | reverse (s : WindowA0ReverseSweep.RevState p c n)
  | forward (s : WindowA0ForwardSweep.State p c n)
  | done (s : WindowA0ClosedEntry.State p c n) (launch : Bool)

def State.physical {p c n : Nat} : State p c n → WindowA0ClosedEntry.State p c n
  | .x z => z.physical
  | .reverse z => z.physical
  | .forward z => z.physical
  | .done z _ => z

def ready {p c n : Nat} : State p c n → Prop
  | .done _ _ => True
  | _ => False

noncomputable def afterX {p c n : Nat} (x : WindowA0XSweep.SweepState p c n) : State p c n := by
  classical
  exact if WindowA0Ledger.done x.physical.tag then .done x.physical false
    else if WindowA0XSweep.goal x then .reverse ⟨x.physical,x.physical.gap,false⟩ else .x x

noncomputable def afterReverse {p c n : Nat} (x : WindowA0ReverseSweep.RevState p c n) :
    State p c n := by
  classical
  exact if WindowA0Ledger.done x.physical.tag then .done x.physical false
    else if x.launched then .done x.physical true
    else if x.left=0 then .forward (WindowA0ForwardSweep.init x.physical) else .reverse x

noncomputable def afterForward {p c n : Nat} (x : WindowA0ForwardSweep.State p c n) :
    State p c n := by
  classical
  exact if WindowA0Ledger.done x.physical.tag then .done x.physical false
    else if x.launched then .done x.physical true else .forward x

noncomputable def init {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) : State p c n :=
  afterX ⟨z,0⟩

noncomputable def next {p c n : Nat} (S : WindowA0Ledger.Scope n) (x : State p c n)
    (e : Fin n) : State p c n :=
  match x with
  | .x z => afterX (WindowA0XSweep.sweepNext S z e)
  | .reverse z => afterReverse (WindowA0ReverseSweep.revNext S z e)
  | .forward z => afterForward (WindowA0ForwardSweep.next S z e)
  | .done z b => .done (WindowA0ClosedEntry.next S z e) b

@[simp] theorem afterX_project {p c n : Nat} (x : WindowA0XSweep.SweepState p c n) :
    (afterX x).physical=x.physical := by
  unfold afterX
  split
  · rfl
  · split <;> rfl

@[simp] theorem afterReverse_project {p c n : Nat} (x : WindowA0ReverseSweep.RevState p c n) :
    (afterReverse x).physical=x.physical := by
  unfold afterReverse
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

@[simp] theorem afterForward_project {p c n : Nat} (x : WindowA0ForwardSweep.State p c n) :
    (afterForward x).physical=x.physical := by
  unfold afterForward
  split
  · rfl
  · split <;> rfl

theorem projects {p c n : Nat} (S : WindowA0Ledger.Scope n) (x : State p c n) (e : Fin n) :
    (next S x e).physical=WindowA0ClosedEntry.next S x.physical e := by
  cases x <;> simp only [next,afterX_project,afterReverse_project,afterForward_project,
    WindowA0ForwardSweep.project] <;> rfl

def Good {p c n : Nat} (initial : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H : Nat) : State p c n → Prop
  | .x x => WindowA0XSweep.Valid initial S J H x ∧ ¬WindowA0XSweep.goal x
  | .reverse x => WindowA0ReverseSweep.Good initial S J H x ∧
      ¬WindowA0ReverseSweep.done x ∧ WindowA0CleanupChain.XFree x.physical
  | .forward x => WindowA0ForwardSweep.Good initial S J H x ∧ ¬WindowA0ForwardSweep.ready x
  | .done z b => Admitted initial S J H z ∧ (b=true ∨ WindowA0Ledger.done z.tag)

noncomputable def reserve {p c n : Nat} (H : Nat) : State p c n → Nat
  | .x x => WindowA0XSweep.reserve x + H+(2*H+2)
  | .reverse x => x.left+(2*H+2)
  | .forward x => WindowA0ForwardSweep.budget x
  | .done _ _ => 0

def nominate {p c n : Nat} (x : State p c n) : Fin n :=
  match x with
  | .x z => liftedSite (cut z.physical).top z.cleaned
  | .reverse z => WindowA0ReverseSweep.nominate z
  | .forward z => WindowA0ForwardSweep.nominate z
  | .done z _ => z.tag.iSlot

variable {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
  {J : Fin n} {H : Nat}

theorem afterX_good (z : WindowA0XSweep.SweepState p c n)
    (h : WindowA0XSweep.Valid initial S J H z) :
    Good initial S J H (afterX z) := by
  classical
  by_cases hd : WindowA0Ledger.done z.physical.tag
  · simpa only [afterX,if_pos hd,Good] using ⟨h.1,Or.inr hd⟩
  · by_cases hg : WindowA0XSweep.goal z
    · have hc := (WindowA0XSweep.sweep_sound h hg).resolve_left hd
      have gap : 0<z.physical.gap := (h.1.resolve_left hd).1.gapPos
      simp only [afterX,if_neg hd,if_pos hg,Good]
      refine ⟨⟨h.1,.inr (.inr ⟨Nat.le_refl _,fun j hj hj' => (Nat.not_lt_of_ge hj hj').elim⟩)⟩,
        ?_,⟨Nat.le_refl _,hc⟩⟩
      intro bad
      rcases bad with k|k|k
      · exact hd k
      · contradiction
      · exact (Nat.ne_of_gt gap) k
    · exact by simpa only [afterX,if_neg hd,if_neg hg,Good] using (And.intro h hg)

theorem afterReverse_good (z : WindowA0ReverseSweep.RevState p c n)
    (h : WindowA0ReverseSweep.Good initial S J H z)
    (hx : WindowA0Ledger.done z.physical.tag ∨ WindowA0CleanupChain.XFree z.physical) :
    Good initial S J H (afterReverse z) := by
  classical
  by_cases hd : WindowA0Ledger.done z.physical.tag
  · simpa only [afterReverse,if_pos hd,Good] using ⟨h.1,Or.inr hd⟩
  by_cases hl : z.launched=true
  · simp only [afterReverse,if_neg hd,if_pos hl,Good]
    exact ⟨h.1,.inl trivial⟩
  by_cases hz : z.left=0
  · have hu := ((WindowA0ReverseSweep.reverse_sound h (.inr (.inr hz))).resolve_left hd).resolve_left hl
    simp only [afterReverse,if_neg hd,if_neg hl,if_pos hz,Good]
    refine ⟨⟨h.1,.inr ⟨⟨Nat.zero_le _,fun _ => rfl,fun f => Bool.noConfusion f⟩,
      hx.resolve_left hd,hu⟩⟩,?_⟩
    rintro (q|q)
    · exact hd q
    · contradiction
  · simp only [afterReverse,if_neg hd,if_neg hl,if_neg hz,Good]
    exact ⟨h,fun bad => bad.elim hd (fun k => k.elim hl hz),hx.resolve_left hd⟩

theorem afterForward_good (z : WindowA0ForwardSweep.State p c n)
    (h : WindowA0ForwardSweep.Good initial S J H z) :
    Good initial S J H (afterForward z) := by
  classical
  by_cases hd : WindowA0Ledger.done z.physical.tag
  · simpa only [afterForward,if_pos hd,Good] using ⟨h.1,Or.inr hd⟩
  by_cases hl : z.launched=true
  · simp only [afterForward,if_neg hd,if_pos hl,Good]
    exact ⟨h.1,.inl trivial⟩
  · simp only [afterForward,if_neg hd,if_neg hl,Good]
    exact ⟨h,fun bad => bad.elim hd hl⟩

theorem good_init (z : WindowA0ClosedEntry.State p c n)
    (h : Admitted initial S J H z) : Good initial S J H (init z) :=
  afterX_good _ ⟨h,.inr ⟨Nat.zero_le _,fun j hj => (Nat.not_lt_zero j hj).elim⟩⟩

theorem good_next (hn : 4≤n) (z : State p c n) (e : Fin n)
    (h : Good initial S J H z) : Good initial S J H (next S z e) := by
  cases z with
  | x x => exact afterX_good _ (WindowA0XSweep.sweep_keep hn S J H _ _ h.1 h.2)
  | reverse x =>
    have hh := WindowA0ReverseSweep.rev_keep hn S J H x e h.1 h.2.1
    refine afterReverse_good _ hh ?_
    by_cases hd : WindowA0Ledger.done (WindowA0ClosedEntry.next S x.physical e).tag
    · exact .inl hd
    · exact .inr (WindowA0CleanupChain.xfree_next hn S J H _ _ h.1.1 h.2.2 hd)
  | forward x =>
    apply afterForward_good
    let y := WindowA0ForwardSweep.next S x e
    have HA : Admitted initial S J H y.physical := by
      simpa only [y,WindowA0ForwardSweep.project] using
        (WindowA0ClosedEntry.close hn S J H x.physical e h.1.1)
    refine ⟨HA,?_⟩
    by_cases hy : WindowA0ForwardSweep.ready y
    · exact .inl hy
    · have H' := WindowA0ForwardSweep.shapeTransport hn S J H x e h.1 h.2 hy
      have hd : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S x.physical e).tag := by
        intro d
        apply hy
        left
        change WindowA0Ledger.done (WindowA0ForwardSweep.next S x e).physical.tag
        rwa [WindowA0ForwardSweep.project]
      have hc := WindowA0CleanupChain.xfree_next hn S J H _ _ h.1.1
        ((h.1.2.resolve_left h.2).2.1) hd
      exact .inr ⟨H'.1,by simpa only [y,WindowA0ForwardSweep.project] using hc,H'.2⟩
  | done x b =>
    refine ⟨WindowA0ClosedEntry.close hn S J H x e h.1,?_⟩
    rcases h.2 with H|H
    · exact .inl H
    · right
      change (WindowA0Ledger.next S x.tag e).reason.isSome=true
      rw [WindowA0Ledger.terminal_sticky S x.tag e H]
      exact H

theorem afterX_bound (z : WindowA0XSweep.SweepState p c n)
    (h : WindowA0XSweep.Valid initial S J H z) :
    reserve H (afterX z)≤WindowA0XSweep.reserve z+H+(2*H+2) := by
  classical
  by_cases hd : WindowA0Ledger.done z.physical.tag
  · simp only [afterX,if_pos hd,reserve,Nat.zero_le]
  · by_cases hg : WindowA0XSweep.goal z
    · simp only [afterX,if_neg hd,if_pos hg,reserve]
      have g : z.physical.gap≤H := (h.1.resolve_left hd).1.bounded
      omega
    · simp only [afterX,if_neg hd,if_neg hg,reserve,Nat.le_refl]

theorem afterReverse_bound (z : WindowA0ReverseSweep.RevState p c n) :
    reserve H (afterReverse z)≤z.left+(2*H+2) ∨
      ((WindowA0ForwardSweep.init z.physical).physical.gap>H) := by
  classical
  by_cases hg : z.physical.gap≤H
  · left
    unfold afterReverse
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · split
        · change WindowA0ForwardSweep.budget (WindowA0ForwardSweep.init z.physical)≤_
          have h := WindowA0ForwardSweep.initial_budget z.physical
          omega
        · exact Nat.le_refl _
  · exact .inr (Nat.lt_of_not_ge hg)

theorem afterForward_bound (z : WindowA0ForwardSweep.State p c n) :
    reserve H (afterForward z)≤WindowA0ForwardSweep.budget z := by
  unfold afterForward
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _


theorem reserve_next (hn : 4≤n) (z : State p c n) (e : Fin n)
    (h : Good initial S J H z) (hLive : ¬ready z) :
    reserve H (next S z e)+(if e=nominate z then 1 else 0)≤reserve H z := by
  cases z with
  | x x =>
    let y := WindowA0XSweep.sweepNext S x e
    have hg := WindowA0XSweep.sweep_keep hn S J H x e h.1 h.2
    have ha := afterX_bound y hg
    have hb := WindowA0XSweep.sweep_reserve S x e h.2
    change reserve H (afterX y)+(if e=liftedSite (cut x.physical).top x.cleaned then 1 else 0) ≤ _
    change WindowA0XSweep.reserve y+(if e=liftedSite (cut x.physical).top x.cleaned then 1 else 0)
      ≤ WindowA0XSweep.reserve x at hb
    change _ ≤ WindowA0XSweep.reserve x+H+(2*H+2)
    omega
  | reverse x =>
    let y := WindowA0ReverseSweep.revNext S x e
    have hY := WindowA0ReverseSweep.rev_keep hn S J H x e h.1 h.2.1
    have hBound : reserve H (afterReverse y)≤y.left+(2*H+2) := by
      by_cases hd : WindowA0Ledger.done y.physical.tag
      · classical
        simp only [afterReverse,if_pos hd,reserve,Nat.zero_le]
      · have g : y.physical.gap≤H := (hY.1.resolve_left hd).1.bounded
        exact (afterReverse_bound (H:=H) y).resolve_right
          (fun h => (Nat.not_lt_of_ge g) h)
    have hDecr := WindowA0ReverseSweep.rev_charge S x e h.2.1
    change y.left+(if e=WindowA0ReverseSweep.nominate x then 1 else 0)≤x.left at hDecr
    change reserve H (afterReverse y)+(if e=WindowA0ReverseSweep.nominate x then 1 else 0)
      ≤x.left+(2*H+2)
    omega
  | forward x =>
    have hF := WindowA0ForwardSweep.budget_step S x e h.1.1 (h.1.2.resolve_left h.2).1 h.2
    exact Nat.le_trans (Nat.add_le_add_right (afterForward_bound _) _) hF
  | done _ _ => exact (hLive trivial).elim

theorem mean (hn : 4≤n) (z : WindowA0ClosedEntry.State p c n)
    (hz : Admitted initial S J H z) :
    IIDExpectedHittingTimeAtMost (next S) ready (init z) (n*(4*H+2)) := by
  have M := TripleControlled.mean_of_potential (next S) ready (Good initial S J H)
    (reserve H) (fun x e h _ => good_next hn x e h)
    (fun x h hd => by
      have H' (e : Fin n) := reserve_next hn x e h hd
      exact TripleControlled.progress_raw_drift _ (nominate x) _
        (by simpa only [if_true] using H' (nominate x))
        (fun e => Nat.le_trans (Nat.le_add_right _ _) (H' e)))
    (init z) (good_init z hz)
  apply TripleRenewal.expected_mono M
  apply Nat.mul_le_mul_left
  have H' := afterX_bound (S:=S) (J:=J) (H:=H) (⟨z,0⟩ : WindowA0XSweep.SweepState p c n)
    (⟨hz,.inr ⟨Nat.zero_le _,fun j hj => (Nat.not_lt_zero j hj).elim⟩⟩ :
      WindowA0XSweep.Valid initial S J H _)
  apply Nat.le_trans H'
  classical
  by_cases hd : WindowA0XSweep.goal (⟨z,0⟩ : WindowA0XSweep.SweepState p c n)
  · rw [WindowA0XSweep.reserve,if_pos hd]
    omega
  · rw [WindowA0XSweep.reserve,if_neg hd]
    have hG : z.gap≤H := (hz.resolve_left (fun h => hd (.inl h))).1.bounded
    change z.gap-0+H+(2*H+2)≤_
    omega

noncomputable def stage (hn : 4≤n) (z : WindowA0ClosedEntry.State p c n)
    (hz : Admitted initial S J H z) : TripleRenewal.Stage (WindowA0ClosedEntry.next S) z where
  State := State p c n
  start := init z
  next := next S
  project := State.physical
  ready := ready
  reachable := Good initial S J H
  projInit := afterX_project _
  projStep := projects S
  reachStart := good_init z hz
  reachStep := good_next hn

theorem ready_sticky (z : State p c n) (e : Fin n) (h : ready z) :
    ready (next S z e) := by
  cases z <;> first | exact trivial | exact False.elim h

theorem outcome (z : State p c n) (hz : Good initial S J H z) (h : ready z) :
    WindowA0Ledger.done z.physical.tag ∨ ∃ x, z=State.done x true := by
  cases z with
  | done d b =>
    rcases hz.2 with hb|hd
    · subst b
      exact .inr ⟨d,rfl⟩
    · exact .inl hd
  | x _ | reverse _ | forward _ => exact False.elim h

#print axioms projects
#print axioms good_next
#print axioms reserve_next
#print axioms mean
#print axioms stage

def launchDecision {p c n : Nat} : State p c n → Prop
  | .done _ b => b=true
  | _ => False

def launchEnabled {p c n : Nat} : State p c n → Prop
  | .reverse _ | .forward _ => True
  | _ => False

/-- Exact reason on the first decision mark: only reverse/forward can
credit a fresh selected door launch, and simultaneous routed D wins. -/
theorem first_launch_iff (z : State p c n) (e : Fin n)
    (h : Good initial S J H z) (hLive : ¬ready z) :
    launchDecision (next S z e) ↔
      launchEnabled z ∧ WindowA0ReverseSweep.freshDoor z.physical e ∧
        ¬WindowA0Ledger.done (next S z e).physical.tag := by
  classical
  cases z with
  | x x =>
    simp only [next,launchEnabled,false_and]
    unfold afterX
    split
    · simp [launchDecision]
    · split <;> rfl
  | reverse x =>
    have hl : x.launched=false := Bool.eq_false_iff.mpr (fun hL => h.2.1 (.inr (.inl hL)))
    have em : (WindowA0ReverseSweep.revNext S x e).launched=true ↔
        WindowA0ReverseSweep.freshDoor x.physical e := by simp [WindowA0ReverseSweep.revNext,hl]
    simp only [next,launchEnabled,true_and,State.physical]
    unfold afterReverse
    by_cases hd : WindowA0Ledger.done (WindowA0ReverseSweep.revNext S x e).physical.tag
    · simp [launchDecision,hd]
    · rw [if_neg hd]
      by_cases hL : (WindowA0ReverseSweep.revNext S x e).launched=true
      · simp [hL,launchDecision,hd,em.mp hL]
      · rw [if_neg hL]
        have hF : ¬WindowA0ReverseSweep.freshDoor x.physical e := fun hF => hL (em.mpr hF)
        split <;> simp [launchDecision,hF]
  | forward x =>
    have hl : x.launched≠true := fun hL => h.2 (.inr hL)
    have em : (WindowA0ForwardSweep.next S x e).launched=true ↔
        WindowA0ReverseSweep.freshDoor x.physical e :=
      (WindowA0ForwardSweep.raw_launch S x e).trans ⟨fun h => h.resolve_left hl,Or.inr⟩
    simp only [next,launchEnabled,true_and,State.physical]
    unfold afterForward
    by_cases hd : WindowA0Ledger.done (WindowA0ForwardSweep.next S x e).physical.tag
    · simp [launchDecision,hd]
    · rw [if_neg hd]
      by_cases hL : (WindowA0ForwardSweep.next S x e).launched=true
      · simp [hL,launchDecision,hd,em.mp hL]
      · rw [if_neg hL]
        have hF : ¬WindowA0ReverseSweep.freshDoor x.physical e := fun hF => hL (em.mpr hF)
        simp [launchDecision,hF]
  | done z b => exact (hLive trivial).elim

#print axioms first_launch_iff
end L4.WindowA0CleanupPass
