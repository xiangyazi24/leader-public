import Leader.L4.WindowTransactions
import Leader.L4.WindowFrontDone
import Leader.L4.WindowProtectedWindow
import Leader.L4.WindowNoLoss

/-! The precise five-slot interface for the physical fold. Substage
proofs refer to the same done and fresh-bad predicates on original words. -/
namespace L4.WindowPlan

open WindowFiveStages WindowOwnership WindowTransactions
open SevenTagCharge WindowLatch RootedAssembly WindowRoster WindowA0Join

variable {p c n : Nat}
variable (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
variable (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))

noncomputable def current (w : Word n) :=
  fold hp hc hn hq (scope x i) w

def done (w : Word n) : Prop := WindowFrontDone.done (current hp hc hn x hq i w)

def freshBad (w : Word n) : Prop := WindowProtectedOuter.bad (current hp hc hn x hq i w)

def atOwned (l : Nat) (w : Word n) : Prop :=
  ∃ s P, current hp hc hn x hq i w=.inl s ∧ s.mode=.owned P ∧ l≤P.cert.length

def atProtected (w : Word n) : Prop :=
  ∃ (en : WindowProtectedOuter.Entry x (window7 (roster x) i)) (d : Nat), current hp hc hn x hq i w=.inr (WindowProtectedOuter.startRunning en) ∧
    0<d ∧ d+2<7 ∧ en.victim=WindowRosterTrace.labels x i d

/-- Unused ordinary stages are zero-time skips. A protected cursor
bypasses any remaining ordinary slot; no phase consumes an extra mark
to notice that it has already been entered. -/
def Allow : Nat → Word n → Nat → Prop
  | 0,w,_ => done hp hc hn x hq i w
  | 5,w,h => w=[] ∧ h=WindowSpan.span x i
  | j+1,w,h =>
    done hp hc hn x hq i w ∨
      physical x i w≤h ∧ (atProtected hp hc hn x hq i w ∨
        (2≤j+1 ∧ atOwned hp hc hn x hq i (5-(j+1)) w))

def Slot (j : Nat) : Prop :=
  ∀ w h, Allow hp hc hn x hq i (j+1) w h → ¬done hp hc hn x hq i w →
    Allow hp hc hn x hq i j w h ∨ ∃ T : Transaction (coefficient c) w h,
      ∀ u, FirstExit T.hit u → ¬done hp hc hn x hq i (w++u) →
        Allow hp hc hn x hq i j (w++u) (T.span u)

private theorem next_at_entry {g : List (Fin n)} (A : EntryScope g)
    (s : Front x g) (hs : s.mode=.entry A) (e : Fin n) :
    let y := WindowProtectedOuter.joinedNext (WindowLatch.front hn (decide hp hc hn)) (.inl s) e
    WindowFrontDone.done y ∨ AtEntry A y ∨
      ∃ t P, y=.inl t ∧ t.mode=.owned P := by
  rcases s with ⟨z,hv,hq',mode⟩
  change mode=.entry A at hs
  subst mode
  unfold WindowProtectedOuter.joinedNext WindowLatch.front WindowOwnership.decide
  dsimp only
  split
  · rename_i t hEq
    split at hEq
    · cases hEq
      exact .inr (.inl ⟨_,rfl,rfl⟩)
    · cases hEq
      exact .inl trivial
    · cases hEq
      exact .inr (.inr ⟨_,_,rfl,rfl⟩)
    · rename_i a loc H
      exact (no_entry_death z g A.first A.second e a loc H).elim
  · rename_i k hEq
    split at hEq
    · cases hEq
    · cases hEq
    · cases hEq
    · rename_i a loc H
      exact (no_entry_death z g A.first A.second e a loc H).elim

private theorem snoc_or_nil {α : Type} (w : List α) :
    w=[] ∨ ∃ u e, w=u++[e] := by
  cases r : w.reverse with
  | nil =>
    left
    have h := congrArg List.reverse r
    simpa using h
  | cons e u =>
    right
    have h := congrArg List.reverse r
    exact ⟨u.reverse,e,by simpa using h⟩

theorem entry_handoff
    (he : (Front.initial x hq (scope x i)).mode=.entry (scope x i))
    (u : Word n) (hu : FirstExit (WindowA0FirstExit.done x i) u)
    (nd : ¬done hp hc hn x hq i u) :
    atOwned hp hc hn x hq i 1 u := by
  obtain rfl|⟨a,e,rfl⟩ := snoc_or_nil u
  · have f := front_first_exit hp hc hn x hq i he [] hu
    exact (f.2 ⟨_,rfl,he⟩).elim
  · have f := front_first_exit hp hc hn x hq i he (wordNext a e) hu
    have before : InEntry hp hc hn x hq i a :=
      Classical.byContradiction ((clean_child _ a e).mp f.1).2
    obtain ⟨s,hs,hm⟩ := before
    have T := next_at_entry hp hc hn x (scope x i) s hm e
    have R : current hp hc hn x hq i (wordNext a e)=
        WindowProtectedOuter.joinedNext (WindowLatch.front hn (decide hp hc hn)) (.inl s) e := by
      unfold current fold wordNext
      rw [WindowLatch.replay_append]
      have Z : fold hp hc hn hq (scope x i) a=.inl s := hs
      exact congrArg (fun y => WindowProtectedOuter.joinedNext (WindowLatch.front hn (decide hp hc hn)) y e) Z
    rw [←R] at T
    obtain H|H|⟨t,P,eq,md⟩ := T
    · exact (nd H).elim
    · exact (f.2 H).elim
    · exact ⟨t,P,eq,md,P.positive⟩

theorem entry_slot (h5 : 5≤n) (h7 : 7≤RankPhysical.rank x)
    (short : 2*WindowSpan.span x i+2<n) :
    Slot hp hc hn x hq i 4 := by
  intro w h hInit _
  change w=[] ∧ h=WindowSpan.span x i at hInit
  obtain ⟨rfl,rfl⟩ := hInit
  cases E : startMode (z:=SevenTagCharge.initial x) (scope x i) with
  | some P =>
    apply Or.inl
    apply Or.inr
    refine ⟨(by simp only [physical,WindowSpanTrace.selected_start x i h7,Nat.le_refl]),.inr ⟨by decide,?_⟩⟩
    refine ⟨Front.initial x hq (scope x i), P.normalize,rfl,?_,(P.normalize).positive⟩
    simp [Front.initial,E]
  | none =>
    have he : (Front.initial x hq (scope x i)).mode=.entry (scope x i) := by simp [Front.initial,E]
    let T := entry h5 hc x i hq h7 short he
    apply Or.inr
    refine ⟨T,?_⟩
    intro u hu nd
    change ¬done hp hc hn x hq i u at nd
    have HU : FirstExit (WindowA0FirstExit.done x i) u := hu
    apply Or.inr
    refine ⟨?_,.inr ⟨by decide,entry_handoff hp hc hn x hq i he u HU nd⟩⟩
    unfold T entry
    rw [geometric_stamp _ _ _ _ _ _ _ _ _ _ HU]
    exact Nat.le_refl _

theorem replay_run {α : Type} {n : Nat} (step : α → Fin n → α) (z : α) (w : Word n) :
    WindowLatch.replay step z w=GGTiming.runMarks step z w := by
  induction w generalizing z with
  | nil => rfl
  | cons e es ih => exact ih (step z e)

theorem protected_slot (h7 : 7≤RankPhysical.rank x) :
    Slot hp hc hn x hq i 0 := by
  intro w h aw nd
  change done hp hc hn x hq i w ∨
    (physical x i w≤h ∧ (atProtected hp hc hn x hq i w ∨
      (2≤1 ∧ atOwned hp hc hn x hq i 4 w))) at aw
  obtain ⟨spanBound,E⟩ := aw.resolve_left nd
  have atLatch := E.resolve_right (by omega)
  obtain ⟨en,d,he,hd,hr,tag⟩ := atLatch
  have hL := fold_ledger hp hc hn hq (scope x i) w
  change WindowLatch.project Front.ledger (current hp hc hn x hq i w)=_ at hL
  rw [he] at hL
  change en.ledger=observe (initial x) w at hL
  have hQuiet : QuietEntrance en.ledger.config := by
    rw [hL,observe_config]
    exact RootedFresh.quiet_run x w hp hc hn hq
  have keep := WindowNoLoss.not_done_no_loss hp hc hn hq (scope x i) w nd
  have clock := WindowProtectedWindow.clock hp hc hn x hq i h7 w h spanBound keep en hL hQuiet d hd hr tag
  let T := WindowProtectedSlot.protected_transaction en w clock
  refine .inr ⟨T,?_⟩
  intro u hu nd'
  exfalso
  apply nd'
  unfold current fold at he
  rw [replay_run] at he
  have A := WindowProtectedSlot.joined_hit_after_latch
    (WindowLatch.front hn (decide hp hc hn)) (Front.initial x hq (scope x i)) en w u he
  unfold done current fold
  rw [replay_run,A]
  exact hu.2

/-- A typed three-field cut list for the remaining ordinary slots.
The entry and final protected slot are already concrete. -/
structure Middle where
  singleton : Slot hp hc hn x hq i 3
  pair : Slot hp hc hn x hq i 2
  triple : Slot hp hc hn x hq i 1

noncomputable def assemble
    (h5 : 5≤n) (h7 : 7≤RankPhysical.rank x) (short : 2*WindowSpan.span x i+2<n)
    (M : Middle hp hc hn x hq i) :
    FivePlan (done hp hc hn x hq i) (coefficient c) where
  allow := Allow hp hc hn x hq i
  terminal := fun _ _ h => h
  localStage := by
    intro j w h hj
    have T : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    rcases T with rfl|rfl|rfl|rfl|rfl
    · exact protected_slot hp hc hn x hq i h7 w h
    · exact M.triple w h
    · exact M.pair w h
    · exact M.singleton w h
    · exact entry_slot hp hc hn x hq i h5 h7 short w h

theorem physical_plan_of_middle
    (M : ∀ {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
      (x : Config p c n) (hq : QuietEntrance x) (_h7 : 7≤RankPhysical.rank x)
      (i : Fin (RankPhysical.rank x)), 2*WindowSpan.span x i+2<n →
      Middle hp hc hn x hq i) :
    WindowFiveStages.PhysicalPlan := by
  intro c hc
  refine ⟨coefficient c, Nat.lt_of_lt_of_le (by decide : 0<4096) (Nat.le_max_right _ _),?_⟩
  intro p n x hp hn hq h7 i short
  have h5 : 5≤n := by
    have cap : RankPhysical.rank x≤n := by
      rw [←count_eq_rank x]
      simpa [addresses] using (List.length_filter_le (p:=fun i : Fin n => (x i).mark) (List.finRange n))
    omega
  refine ⟨done hp hc hn x hq i,freshBad hp hc hn x hq i,
    assemble hp hc hn x hq i h5 h7 short (M hp hc hn x hq h7 i short),⟨rfl,rfl⟩,
    WindowFrontDone.fold_closed hp hc hn hq (scope x i),
    WindowFrontDone.fold_cover hp hc hn hq (scope x i),?_⟩
  exact fold_fresh_mass hp hc hn hq (scope x i)

end L4.WindowPlan
