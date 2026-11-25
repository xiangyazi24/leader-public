import Leader.L4.WindowA0DirtyRank

/-! Repeat dirty COUNT passes until a real fresh INIT launch or the
physical scoped exit. A repeat starts from already X-free state. -/
namespace L4.WindowA0DirtyRepeat
open WindowA0ClosedEntry Classical
abbrev Pass := WindowA0CleanupPass.State

structure State (p c n : Nat) where
  pass : Pass p c n
  seen : Option (Fin (2*c))

def idx {Q : Nat} : Option (Fin Q) → Nat
  | none => 0
  | some k => k.val+1

def done {p c n : Nat} (z : State p c n) : Prop := WindowA0CleanupPass.ready z.pass

noncomputable def next {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : State p c n)
    (e : Fin n) : State p c n :=
  let y := WindowA0CleanupPass.next S z.pass e
  if done z then ⟨y,z.seen⟩
  else if WindowA0CleanupPass.launchDecision y ∧ ¬WindowA0DirtyRank.L1 z.pass.physical e then
    match (y.physical.tag.ledger.config (rightNeighbor y.physical.tag.jSlot)).source with
    | .await k => ⟨WindowA0CleanupPass.afterX ⟨y.physical,y.physical.gap⟩,some k⟩
    | _ => ⟨y,z.seen⟩
  else ⟨y,z.seen⟩

theorem project {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : State p c n) (e : Fin n) :
    (next S z e).pass.physical=WindowA0ClosedEntry.next S z.pass.physical e := by
  unfold next
  dsimp only
  split
  · exact WindowA0CleanupPass.projects S _ _
  · split
    · split <;> simpa only [WindowA0CleanupPass.afterX_project] using
        WindowA0CleanupPass.projects S z.pass e
    · exact WindowA0CleanupPass.projects S _ _

def Good {p c n : Nat} (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (z : State p c n) : Prop :=
  WindowA0CleanupPass.Good initial S J H z.pass ∧
    match z.seen with
    | none => True
    | some k => done z ∨ (z.pass.physical.tag.ledger.config J).source=.await k ∧
        WindowA0CleanupPass.launchEnabled z.pass

noncomputable def reserve {p c n : Nat} (H : Nat) (z : State p c n) : Nat :=
  if done z then 0 else (3*H+2)*(2*c-idx z.seen)+WindowA0CleanupPass.reserve H z.pass

private theorem idx_le {Q : Nat} (q : Option (Fin Q)) : idx q≤Q := by
  cases q with
  | none => exact Nat.zero_le _
  | some k => exact k.isLt

private theorem admitted {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {z : Pass p c n} (h : WindowA0CleanupPass.Good initial S J H z) :
    Admitted initial S J H z.physical := by
  cases z with
  | x _ => exact h.1.1
  | reverse _ => exact h.1.1
  | forward _ => exact h.1.1
  | done _ _ => exact h.1

private theorem pass_ready_of_physical {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H : Nat} {z : Pass p c n}
    (h : WindowA0CleanupPass.Good initial S J H z)
    (hp : WindowA0Ledger.done z.physical.tag) : WindowA0CleanupPass.ready z := by
  cases z with
  | x _ => exact (h.2 (.inl hp)).elim
  | reverse _ => exact (h.2.1 (.inl hp)).elim
  | forward _ => exact (h.2 (.inl hp)).elim
  | done _ _ => exact trivial

private theorem launch_ready {p c n : Nat} {z : Pass p c n}
    (h : WindowA0CleanupPass.launchDecision z) : WindowA0CleanupPass.ready z := by
  cases z <;> first | exact trivial | exact h

private theorem pos_pass {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {z : Pass p c n} (h : WindowA0CleanupPass.Good initial S J H z)
    (hr : ¬WindowA0CleanupPass.ready z) :
    0<WindowA0CleanupPass.reserve H z := by
  cases z with
  | x _ | reverse _ => simp only [WindowA0CleanupPass.reserve]; omega
  | forward _ =>
    simp only [WindowA0CleanupPass.reserve,WindowA0ForwardSweep.budget,if_neg h.2]
    omega
  | done _ _ => exact (hr trivial).elim

private theorem next_seen_lt {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : State p c n) (e : Fin n)
    (hz : Good initial S J H z) (ha : ¬done z)
    (hl : WindowA0CleanupPass.launchDecision (WindowA0CleanupPass.next S z.pass e))
    (h1 : ¬WindowA0DirtyRank.L1 z.pass.physical e) :
    ∃ k : Fin (2*c), idx z.seen<idx (some k) ∧
      ((WindowA0CleanupPass.next S z.pass e).physical.tag.ledger.config J).source=.await k := by
  have HH := (WindowA0CleanupPass.first_launch_iff z.pass e hz.1 ha).mp hl
  have hD : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.pass.physical e).tag :=
    by simpa only [WindowA0CleanupPass.projects] using HH.2.2
  cases he : z.seen with
  | none =>
    have h := WindowA0DirtyRank.birthless_launch_shape hn S J e H z.pass.physical
      (admitted hz.1) hD HH.2.1
    obtain ⟨_,k,hk⟩ := h.resolve_left (fun hh => h1 hh.1)
    exact ⟨k,by simp [idx],by simpa only [WindowA0CleanupPass.projects] using hk⟩
  | some j =>
    have HJ := hz.2
    rw [he] at HJ
    have h := WindowA0DirtyRank.await_step hn S J e H z.pass.physical
      (admitted hz.1) hD j (HJ.resolve_left ha).1
    rw [if_pos HH.2.1] at h
    obtain ⟨_,k,hk,hS⟩ := h.resolve_left (fun hh => h1 hh.1)
    exact ⟨k,Nat.succ_lt_succ hk,by simpa only [WindowA0CleanupPass.projects] using hS⟩


private theorem enabled_keep {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : Pass p c n) (e : Fin n) (h : WindowA0CleanupPass.launchEnabled z)
    (hn : ¬WindowA0CleanupPass.ready (WindowA0CleanupPass.next S z e)) :
    WindowA0CleanupPass.launchEnabled (WindowA0CleanupPass.next S z e) := by
  cases z with
  | x _ | done _ _ => exact False.elim h
  | reverse x =>
    simp only [WindowA0CleanupPass.next] at hn ⊢
    unfold WindowA0CleanupPass.afterReverse at hn ⊢
    split
    · rename_i H
      simp only [if_pos H] at hn
      exact (hn trivial).elim
    · rename_i H
      simp only [if_neg H] at hn
      split
      · rename_i K
        simp only [if_pos K] at hn
        exact (hn trivial).elim
      · split <;> trivial
  | forward x =>
    simp only [WindowA0CleanupPass.next] at hn ⊢
    unfold WindowA0CleanupPass.afterForward at hn ⊢
    split
    · rename_i H
      simp only [if_pos H] at hn
      exact (hn trivial).elim
    · rename_i H
      simp only [if_neg H] at hn
      split
      · rename_i K
        simp only [if_pos K] at hn
        exact (hn trivial).elim
      · trivial

private theorem restart_facts {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} (z : WindowA0ClosedEntry.State p c n)
    (hz : Admitted initial S J H z) (hd : ¬WindowA0Ledger.done z.tag)
    (hx : WindowA0CleanupChain.XFree z) :
    let y := WindowA0CleanupPass.afterX ⟨z,z.gap⟩
    WindowA0CleanupPass.Good initial S J H y ∧ ¬WindowA0CleanupPass.ready y ∧
      WindowA0CleanupPass.launchEnabled y ∧ WindowA0CleanupPass.reserve H y≤3*H+2 := by
  have G := WindowA0CleanupPass.afterX_good (⟨z,z.gap⟩ : WindowA0XSweep.SweepState p c n)
    (show WindowA0XSweep.Valid initial S J H _ from ⟨hz,.inr hx⟩)
  have hr : WindowA0XSweep.goal (⟨z,z.gap⟩ : WindowA0XSweep.SweepState p c n) :=
    .inr (Nat.le_refl _)
  refine ⟨G,?_⟩
  simp only [WindowA0CleanupPass.afterX,if_neg hd,if_pos hr,WindowA0CleanupPass.ready,
    WindowA0CleanupPass.launchEnabled,WindowA0CleanupPass.reserve,not_false_eq_true,true_and]
  have hh : z.gap≤H := (hz.resolve_left hd).1.bounded
  omega

theorem run_step {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : State p c n) (e : Fin n)
    (hz : Good initial S J H z) (ha : ¬done z) :
    Good initial S J H (next S z e) ∧
      reserve H (next S z e)+(if e=WindowA0CleanupPass.nominate z.pass then 1 else 0)
        ≤reserve H z := by
  let y := WindowA0CleanupPass.next S z.pass e
  let hit := if e=WindowA0CleanupPass.nominate z.pass then 1 else 0
  have hHit : hit≤1 := by dsimp [hit]; split <;> omega
  have hGood : WindowA0CleanupPass.Good initial S J H y :=
    WindowA0CleanupPass.good_next hn z.pass e hz.1
  have hPay : WindowA0CleanupPass.reserve H y+hit≤WindowA0CleanupPass.reserve H z.pass :=
    WindowA0CleanupPass.reserve_next hn z.pass e hz.1 ha
  by_cases hLoop : WindowA0CleanupPass.launchDecision y ∧ ¬WindowA0DirtyRank.L1 z.pass.physical e
  · obtain ⟨k,hK,hs⟩ := next_seen_lt hn S J H z e hz ha hLoop.1 hLoop.2
    have hD := ((WindowA0CleanupPass.first_launch_iff z.pass e hz.1 ha).mp hLoop.1).2.2
    have hJ : rightNeighbor y.physical.tag.jSlot=J := (admitted hGood |>.resolve_left hD).2.2
    have hv : (y.physical.tag.ledger.config (rightNeighbor y.physical.tag.jSlot)).source=.await k := by
      rwa [hJ]
    have E : next S z e=⟨WindowA0CleanupPass.afterX ⟨y.physical,y.physical.gap⟩,some k⟩ := by
      unfold next
      dsimp only
      rw [if_neg ha]
      change (if _ then _ else _) = _
      rw [if_pos hLoop,hv]
    have hx := WindowA0DirtyRank.launch_preserves_xfree hn S J H z.pass e hz.1 ha hLoop.1
    let R := WindowA0CleanupPass.afterX ⟨y.physical,y.physical.gap⟩
    obtain ⟨hR,hRd,hRe,hB⟩ := restart_facts y.physical (admitted hGood) hD hx
    rw [E]
    constructor
    · exact ⟨hR,.inr ⟨by simpa only [R,WindowA0CleanupPass.afterX_project] using hs,hRe⟩⟩
    · have hra : ¬done (⟨WindowA0CleanupPass.afterX ⟨y.physical,y.physical.gap⟩,some k⟩ : State p c n) := hRd
      simp only [reserve,if_neg ha,if_neg hra]
      change (3*H+2)*(2*c-idx (some k)) + WindowA0CleanupPass.reserve H R+hit ≤
        (3*H+2)*(2*c-idx z.seen)+WindowA0CleanupPass.reserve H z.pass
      have hC : (2*c-idx (some k))+1≤2*c-idx z.seen := by have := idx_le (some k); omega
      have hmul := Nat.mul_le_mul_left (3*H+2) hC
      rw [Nat.mul_add,Nat.mul_one] at hmul
      have hOld := pos_pass hz.1 ha
      change WindowA0CleanupPass.reserve H R≤3*H+2 at hB
      omega
  · have E : next S z e=⟨y,z.seen⟩ := by
      unfold next
      dsimp only
      rw [if_neg ha,if_neg hLoop]
    rw [E]
    by_cases hy : WindowA0CleanupPass.ready y
    · constructor
      · refine ⟨hGood,?_⟩
        cases z.seen <;> first | exact trivial | exact Or.inl hy
      · have hd' : done (⟨y,z.seen⟩ : State p c n) := hy
        simp only [reserve,if_pos hd',if_neg ha,Nat.zero_add]
        have hOld := pos_pass hz.1 ha
        omega
    · have hd' : ¬done (⟨y,z.seen⟩ : State p c n) := hy
      constructor
      · refine ⟨hGood,?_⟩
        cases he : z.seen with
        | none => trivial
        | some k =>
          have HH := hz.2
          rw [he] at HH
          obtain ⟨hk,hE⟩ := HH.resolve_left ha
          have hD := fun h => hy (pass_ready_of_physical hGood h)
          have hD' : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.pass.physical e).tag :=
            by simpa only [y,WindowA0CleanupPass.projects] using hD
          have hNo : ¬WindowA0ReverseSweep.freshDoor z.pass.physical e := by
            intro hh
            exact hy (launch_ready ((WindowA0CleanupPass.first_launch_iff z.pass e hz.1 ha).mpr
              ⟨hE,hh,hD⟩))
          have hP := WindowA0DirtyRank.await_step hn S J e H z.pass.physical
            (admitted hz.1) hD' k hk
          rw [if_neg hNo] at hP
          exact .inr ⟨by simpa only [y,WindowA0CleanupPass.projects] using hP,
            enabled_keep S z.pass e hE hy⟩
      · simp only [reserve,if_neg ha,if_neg hd']
        simpa only [Nat.add_assoc] using Nat.add_le_add_left hPay ((3*H+2)*(2*c-idx z.seen))


noncomputable def init {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) : State p c n :=
  ⟨WindowA0CleanupPass.init z,none⟩

theorem mean {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : WindowA0ClosedEntry.State p c n)
    (hz : Admitted initial S J H z) :
    IIDExpectedHittingTimeAtMost (next S) done (init z)
      (n*((3*H+2)*(2*c)+(4*H+2))) := by
  have hI : Good initial S J H (init z) :=
    ⟨WindowA0CleanupPass.good_init z hz,trivial⟩
  have M := TripleControlled.mean_of_potential (next S) done (Good initial S J H)
    (reserve H) (fun u e h hd => (run_step hn S J H u e h hd).1)
    (fun u hu hd => by
      have H (e : Fin n) := (run_step hn S J H u e hu hd).2
      exact TripleControlled.progress_raw_drift _ (WindowA0CleanupPass.nominate u.pass) _
        (by simpa only [if_true] using H (WindowA0CleanupPass.nominate u.pass))
        (fun e => Nat.le_trans (Nat.le_add_right _ _) (H e))) (init z) hI
  apply TripleRenewal.expected_mono M
  apply Nat.mul_le_mul_left
  by_cases hR : done (init z)
  · simp [reserve,hR]
  · rw [reserve,if_neg hR]
    change (3*H+2)*(2*c-0)+WindowA0CleanupPass.reserve H (WindowA0CleanupPass.afterX ⟨z,0⟩)≤_
    have B := WindowA0CleanupPass.afterX_bound (⟨z,0⟩ : WindowA0XSweep.SweepState p c n)
      (show WindowA0XSweep.Valid initial S J H _ from
        ⟨hz,.inr ⟨Nat.zero_le _,fun j h => (Nat.not_lt_zero j h).elim⟩⟩)
    have A : WindowA0XSweep.reserve (⟨z,0⟩ : WindowA0XSweep.SweepState p c n)≤H := by
      unfold WindowA0XSweep.reserve
      split
      · exact Nat.zero_le _
      · rename_i hh
        have hn := hz.resolve_left (fun hd => hh (.inl hd))
        exact Nat.le_trans (Nat.sub_le _ _) hn.1.bounded
    have E : WindowA0CleanupPass.reserve H (WindowA0CleanupPass.afterX ⟨z,0⟩)≤4*H+2 := by omega
    exact Nat.add_le_add_left E _

/-- The launch terminal originates at a fresh L1 on this exact input
mark. The result records post-pair I1 at J; later padding is not used
to re-identify the originating launch. -/
theorem first_terminal {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : State p c n) (e : Fin n)
    (hz : Good initial S J H z) (ha : ¬done z) (hd : done (next S z e)) :
    WindowA0Ledger.done (next S z e).pass.physical.tag ∨
      (WindowA0DirtyRank.L1 z.pass.physical e ∧
        ((next S z e).pass.physical.tag.ledger.config J).source=.i1) := by
  let y := WindowA0CleanupPass.next S z.pass e
  have hGood : WindowA0CleanupPass.Good initial S J H y :=
    WindowA0CleanupPass.good_next hn z.pass e hz.1
  by_cases hLoop : WindowA0CleanupPass.launchDecision y ∧ ¬WindowA0DirtyRank.L1 z.pass.physical e
  · obtain ⟨k,_,hs⟩ := next_seen_lt hn S J H z e hz ha hLoop.1 hLoop.2
    have hD := ((WindowA0CleanupPass.first_launch_iff z.pass e hz.1 ha).mp hLoop.1).2.2
    have hJ : rightNeighbor y.physical.tag.jSlot=J := (admitted hGood |>.resolve_left hD).2.2
    have hv : (y.physical.tag.ledger.config (rightNeighbor y.physical.tag.jSlot)).source=.await k := by rwa [hJ]
    have E : next S z e=⟨WindowA0CleanupPass.afterX ⟨y.physical,y.physical.gap⟩,some k⟩ := by
      unfold next
      dsimp only
      rw [if_neg ha]
      change (if _ then _ else _) = _
      rw [if_pos hLoop,hv]
    have hx := WindowA0DirtyRank.launch_preserves_xfree hn S J H z.pass e hz.1 ha hLoop.1
    have hr := (restart_facts y.physical (admitted hGood) hD hx).2.1
    rw [E] at hd
    exact (hr hd).elim
  · have E : next S z e=⟨y,z.seen⟩ := by
      unfold next
      dsimp only
      rw [if_neg ha,if_neg hLoop]
    rw [E] at hd ⊢
    rcases WindowA0CleanupPass.outcome y hGood hd with h|⟨p,h⟩
    · exact .inl h
    · have hl : WindowA0CleanupPass.launchDecision y := by rw [h]; rfl
      have H' := (WindowA0CleanupPass.first_launch_iff z.pass e hz.1 ha).mp hl
      have h1 : WindowA0DirtyRank.L1 z.pass.physical e := by
        apply Classical.byContradiction
        exact fun h1 => hLoop ⟨hl,h1⟩
      have hD : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.pass.physical e).tag := by
        simpa only [WindowA0CleanupPass.projects] using H'.2.2
      have hS := WindowA0DirtyRank.birthless_launch_shape hn S J e H z.pass.physical
        (admitted hz.1) hD H'.2.1
      exact .inr ⟨h1,by
        have H := (hS.resolve_right (fun h => h.1 h1)).2
        simpa only [y,WindowA0CleanupPass.projects] using H⟩

/-- The first continuing terminal hands off a particular freshly written
worker at the post-mark gap coordinate. Stale U on other rails cannot
satisfy the identity of this occurrence. -/
theorem first_terminal_worker {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : State p c n) (e : Fin n)
    (hz : Good initial S J H z) (ha : ¬done z) (hd : done (next S z e))
    (hkeep : ¬WindowA0Ledger.done (next S z e).pass.physical.tag) :
    let out := (next S z e).pass.physical
    e = liftedSite (cut out).top (out.gap-1) ∧
      (out.tag.ledger.config e).rail=.ui ∧
      (out.tag.ledger.config J).source=.i1 ∧ WindowA0CleanupChain.XFree out := by
  obtain ⟨hL,hsrc⟩ := (first_terminal hn S J H z e hz ha hd).resolve_left hkeep
  let out := (next S z e).pass.physical
  have eq := project S z e
  have hk : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S z.pass.physical e).tag := by
    rw [←eq]
    exact hkeep
  have hOld : ¬WindowA0Ledger.done z.pass.physical.tag := by
    intro hp
    apply hk
    change (WindowA0Ledger.next S z.pass.physical.tag e).reason.isSome=true
    rw [WindowA0Ledger.terminal_sticky S z.pass.physical.tag e hp]
    exact hp
  have old := (admitted hz.1).resolve_left hOld
  have post' := (close hn S J H z.pass.physical e (admitted hz.1)).resolve_left hk
  have post : WindowA0IH.Live J H (cut out) := by
    change WindowA0IH.Live J H (cut (next S z e).pass.physical)
    rw [eq]
    exact post'.1
  have eJ := (congrArg rightNeighbor hL.1).trans old.2.2
  have he : e=liftedSite (cut out).top (out.gap-1) := by
    apply FreshSeparation.succ_inj
    rw [eJ,←liftedSite_succ]
    have hh := post.gapPos
    change 0<out.gap at hh
    rw [show out.gap-1+1=out.gap by omega]
    exact post.fixedRight.symm
  have hw := WindowA0DirtyRank.actual_l1_worker hn S J e H z.pass.physical
    (admitted hz.1) hk hL
  have E : next S z e=⟨WindowA0CleanupPass.next S z.pass e,z.seen⟩ := by
    unfold next
    dsimp only
    rw [if_neg ha,if_neg (fun h => h.2 hL)]
  have dy : WindowA0CleanupPass.ready (WindowA0CleanupPass.next S z.pass e) := by
    rw [E] at hd
    exact hd
  have fy := WindowA0CleanupPass.good_next hn z.pass e hz.1
  have hy : ¬WindowA0Ledger.done (WindowA0CleanupPass.next S z.pass e).physical.tag := by
    rwa [E] at hkeep
  obtain ⟨q,hq⟩ := (WindowA0CleanupPass.outcome _ fy dy).resolve_left hy
  have hl : WindowA0CleanupPass.launchDecision (WindowA0CleanupPass.next S z.pass e) := by
    rw [hq]
    rfl
  have hX := WindowA0DirtyRank.launch_preserves_xfree hn S J H z.pass e hz.1 ha hl
  change e=liftedSite (cut out).top (out.gap-1) ∧
    (out.tag.ledger.config e).rail=.ui ∧
    (out.tag.ledger.config J).source=.i1 ∧ WindowA0CleanupChain.XFree out
  refine ⟨he,?_,hsrc,?_⟩
  · change ((next S z e).pass.physical.tag.ledger.config e).rail=.ui
    rwa [eq]
  · change WindowA0CleanupChain.XFree (next S z e).pass.physical
    rw [E]
    exact hX

#print axioms first_terminal_worker

#print axioms project
#print axioms run_step
#print axioms mean
#print axioms first_terminal

theorem terminal_closed {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : State p c n) (e : Fin n) (h : done z) : done (next S z e) := by
  unfold next
  dsimp only
  rw [if_pos h]
  exact WindowA0CleanupPass.ready_sticky z.pass e h

theorem good_next {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : State p c n) (e : Fin n)
    (hz : Good initial S J H z) : Good initial S J H (next S z e) := by
  by_cases hd : done z
  ·
    unfold next
    dsimp only
    rw [if_pos hd]
    refine ⟨WindowA0CleanupPass.good_next hn z.pass e hz.1,?_⟩
    cases z.seen <;> first | exact trivial | exact .inl (WindowA0CleanupPass.ready_sticky z.pass e hd)
  · exact (run_step hn S J H z e hz hd).1

noncomputable def stage {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (z : WindowA0ClosedEntry.State p c n)
    (hz : Admitted initial S J H z) : TripleRenewal.Stage (WindowA0ClosedEntry.next S) z where
  State := State p c n
  start := init z
  next := next S
  ready := done
  project w := w.pass.physical
  reachable := Good initial S J H
  projInit := WindowA0CleanupPass.afterX_project _
  projStep := project S
  reachStart := ⟨WindowA0CleanupPass.good_init z hz,trivial⟩
  reachStep := fun z e h => good_next hn S J H z e h

#print axioms stage
end L4.WindowA0DirtyRepeat
