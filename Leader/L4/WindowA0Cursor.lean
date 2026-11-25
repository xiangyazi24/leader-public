import Leader.L4.WindowA0CleanupLaunch

/-! Bounded-depth online cursor for the A0 trial. A continuation receives
the completed prefix, not the mark's old state or a freshly sampled word.
This permits zero-time and same-mark stage changes. The cursor does not
alter the underlying physical scheduler projection. -/
namespace L4.WindowA0Cursor

open RootedAssembly WindowA0Trial Classical TripleRenewal WindowFiveStages

/-- A live cut tests scheduler prefixes. A good stop hands its exact
prefix to the next phase, which can freeze a new physical snapshot. -/
inductive Plan (n : Nat) : Nat → Type where
  | spent : Plan n 0
  | cut {k : Nat} (stop bad : Word n → Prop) (pass : Word n → Plan n k) :
      Plan n (k+1)

inductive Cursor (n : Nat) : Type where
  | running {k : Nat} (plan : Plan n (k+1)) : Cursor n
  | accepted : Cursor n
  | rejected : Cursor n

/-- Physical exit has priority over a simultaneous local spoiler.
Exhausting the plan without a physical exit is a rejection. -/
noncomputable def settle {n k : Nat} (goal : Word n → Prop) (w : Word n) :
    Plan n k → Cursor n
  | .spent => if goal w then .accepted else .rejected
  | plan@(.cut stop bad pass) =>
      if goal w then .accepted
      else if stop w then
        if bad w then .rejected else settle goal w (pass w)
      else .running plan

theorem settle_exit {n k : Nat} (goal : Word n → Prop) (w : Word n)
    (p : Plan n k) (h : goal w) : settle goal w p = .accepted := by
  cases p <;> simp [settle,h]

theorem settle_wait {n k : Nat} (goal : Word n → Prop) (w : Word n)
    (stop bad : Word n → Prop) (pass : Word n → Plan n k)
    (hg : ¬goal w) (hs : ¬stop w) :
    settle goal w (.cut stop bad pass) = .running (.cut stop bad pass) := by
  simp [settle,hg,hs]

theorem settle_pass {n k : Nat} (goal : Word n → Prop) (w : Word n)
    (stop bad : Word n → Prop) (pass : Word n → Plan n k)
    (hg : ¬goal w) (hs : stop w) (hb : ¬bad w) :
    settle goal w (.cut stop bad pass) = settle goal w (pass w) := by
  simp [settle,hg,hs,hb]

theorem settle_accepted_iff {n k : Nat} (goal : Word n → Prop) (w : Word n)
    (p : Plan n k) : settle goal w p = .accepted ↔ goal w := by
  induction p with
  | spent => by_cases h : goal w <;> simp [settle,h]
  | cut stop bad pass ih =>
    by_cases h : goal w
    · simp [settle,h]
    · by_cases hs : stop w <;> by_cases hb : bad w <;> simp [settle,h,hs,hb,ih]

/-- Once decided, padding does not change the first decision. -/
noncomputable def advance {n : Nat} (goal : Word n → Prop) (w : Word n) :
    Cursor n → Cursor n
  | .running p => settle goal w p
  | .accepted => .accepted
  | .rejected => .rejected

private noncomputable def push {n : Nat} (goal : Word n → Prop)
    (s : Word n × Cursor n) (e : Fin n) : Word n × Cursor n :=
  (wordNext s.1 e, advance goal (wordNext s.1 e) s.2)

/-- Replay the same suffix marks from a completed prefix. -/
noncomputable def resume {n : Nat} (goal : Word n → Prop)
    (base : Word n) (cursor : Cursor n) (suffix : Word n) :
    Cursor n :=
  (suffix.foldl (push goal) (base,cursor)).2

noncomputable def fold {n k : Nat} (goal : Word n → Prop) (p : Plan n k)
    (w : Word n) : Cursor n :=
  resume goal [] (settle goal [] p) w

private theorem prefix_after {n : Nat} (goal : Word n → Prop)
    (v : Word n) (s : Word n × Cursor n) :
    (v.foldl (push goal) s).1 = s.1 ++ v := by
  induction v generalizing s with
  | nil => simp
  | cons f fs ih =>
    rw [List.foldl_cons,ih]
    simp [push,wordNext,List.append_assoc]

theorem fold_append {n k : Nat} (goal : Word n → Prop) (p : Plan n k)
    (w u : Word n) :
    fold goal p (w++u) = resume goal w (fold goal p w) u := by
  unfold fold resume
  rw [List.foldl_append]
  congr 2
  exact Prod.ext (by simpa using prefix_after goal w ([],settle goal [] p)) rfl

theorem fold_snoc {n k : Nat} (goal : Word n → Prop) (p : Plan n k)
    (w : Word n) (e : Fin n) :
    fold goal p (wordNext w e) = advance goal (wordNext w e) (fold goal p w) := by
  exact fold_append goal p w [e]

def ready {n : Nat} : Cursor n → Prop
  | .running _ => False
  | _ => True

theorem ready_pad {n k : Nat} (goal : Word n → Prop) (p : Plan n k)
    (w : Word n) (e : Fin n) (h : ready (fold goal p w)) :
    fold goal p (wordNext w e) = fold goal p w := by
  rw [fold_snoc]
  cases hf : fold goal p w
  · simp [hf,ready] at h
  · rfl
  · rfl

/-- A first ready prefix is classified by its actual post-mark state.
This statement deliberately does not reclassify a padded rejection. -/
theorem first_accepted_iff {n k : Nat} (goal : Word n → Prop) (p : Plan n k)
    (w : Word n) (e : Fin n) (h : ¬ready (fold goal p w)) :
    fold goal p (wordNext w e) = .accepted ↔ goal (wordNext w e) := by
  rw [fold_snoc]
  cases hf : fold goal p w with
  | running q => exact settle_accepted_iff goal _ q
  | accepted => exact (h (by simp [hf,ready])).elim
  | rejected => exact (h (by simp [hf,ready])).elim

theorem proper_at_cleanup {n k : Nat} (goal stop bad : Word n → Prop)
    (pass : Word n → Plan n k) (hg : ¬goal []) (hs : ¬stop []) :
    ¬ready (fold goal (.cut stop bad pass) []) := by
  change ¬ready (settle goal [] (.cut stop bad pass))
  rw [settle_wait goal [] stop bad pass hg hs]
  simp [ready]

/-- The wire-up gives one physical projection at every prefix,
independently of the online readiness decision. -/
noncomputable def onlineStage {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) {k : Nat} (plan : Plan n k) :
    TripleRenewal.Stage (WindowA0ClosedEntry.next S) x :=
  trialStage S x (fun w =>
    ready (fold (fun v => WindowA0Ledger.done
      (GGTiming.runMarks (WindowA0ClosedEntry.next S) x v).tag) plan w))

/-- On any clean prefix strictly before the first local cut, the
online controller is still in that cut. -/
theorem fold_before_cut {n k : Nat} (goal stop bad : Word n → Prop)
    (pass : Word n → Plan n k) (impliesStop : ∀ w, goal w → stop w)
    (w : Word n) (h : Clean stop w) (hn : ¬stop w) :
    fold goal (.cut stop bad pass) w = .running (.cut stop bad pass) := by
  suffices H : ∀ u : Word n, Clean stop u.reverse → ¬stop u.reverse →
      fold goal (.cut stop bad pass) u.reverse = .running (.cut stop bad pass) by
    simpa using H w.reverse (by simpa) (by simpa)
  intro u
  induction u with
  | nil => intro _ hs; exact settle_wait goal [] stop bad pass (hs ∘ impliesStop []) hs
  | cons e u ih =>
    rw [List.reverse_cons]
    change Clean stop (wordNext u.reverse e) → ¬stop (wordNext u.reverse e) → _
    intro hc hs
    obtain ⟨hu,hd⟩ := (clean_child stop _ e).mp hc
    change fold goal (.cut stop bad pass) (wordNext u.reverse e) = _
    rw [fold_snoc,ih hu hd]
    exact settle_wait goal _ stop bad pass (hs ∘ impliesStop _) hs

/-- At a favorable first cut the continuation starts at that exact
prefix, and every padded suffix is the original scheduler suffix. -/
theorem first_cut_resume {n k : Nat} (goal stop bad : Word n → Prop)
    (pass : Word n → Plan n k) (impliesStop : ∀ w, goal w → stop w)
    (w u : Word n) (h : FirstExit stop w) (hg : ¬goal w) (hb : ¬bad w) :
    fold goal (.cut stop bad pass) (w++u) =
      resume goal w (settle goal w (pass w)) u := by
  rw [fold_append]
  suffices he : fold goal (.cut stop bad pass) w = settle goal w (.cut stop bad pass) by
    rw [he,settle_pass goal w stop bad pass hg h.2 hb]
  cases hrev : w.reverse with
  | nil =>
    have hnil : w=[] := by
      have E := congrArg List.reverse hrev
      simpa using E
    subst w
    rfl
  | cons e v =>
    have hw : w=wordNext v.reverse e := by
      have E := congrArg List.reverse hrev
      simpa [wordNext] using E
    rw [hw] at h ⊢
    obtain ⟨hprev,hs⟩ := (clean_child stop _ e).mp h.1
    rw [fold_snoc,fold_before_cut goal stop bad pass impliesStop _ hprev hs]
    rfl

theorem cleanup_goal_implies_stop {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (x : WindowA0ClosedEntry.State p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) :
    ∀ w, WindowA0Ledger.done (WindowA0CleanupLaunch.actual S x w).tag →
      WindowA0CleanupLaunch.hit S x w := by
  intro w hw
  exact WindowA0CleanupLaunch.done_of_good_exit _ (WindowA0CleanupLaunch.observe_good hn S J H x hx w)
    (by rwa [WindowA0CleanupLaunch.observe_project])

/-- The existing literal cleanup admissibility and credit now attach
to the cursor without a caller-supplied no-early-readiness hypothesis. -/
noncomputable def onlineCleanup {p c n k : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (x : WindowA0ClosedEntry.State p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x)
    (hl : ¬WindowA0Ledger.done x.tag) (tail : Word n → Plan n k) :
    WindowA0AttemptCredit.Layer wordNext
      (onlineStage S x (.cut (WindowA0CleanupLaunch.hit S x) (fun _ => False) tail)).ready
      (fun w => w=[]) (WindowA0CleanupLaunch.startZero S J x) 1 :=
  WindowA0CleanupLaunch.cleanupLayer hn S J H x hx hl _ (by
    intro w hw hr
    apply Classical.byContradiction
    intro hs
    have eq := fold_before_cut _ (WindowA0CleanupLaunch.hit S x) (fun _ => False) tail
      (cleanup_goal_implies_stop hn S J H x hx) w hw hs
    change ready (fold (fun v => WindowA0Ledger.done (WindowA0CleanupLaunch.actual S x v).tag) (.cut (WindowA0CleanupLaunch.hit S x) (fun _ => False) tail) w) at hr
    rw [eq] at hr
    exact hr)

/-- Per-visit predicates may close over the actual release/return
entry word. Their internal physical guarantees are separate lemmas. -/
structure Cuts (n : Nat) where
  releaseStop : Nat → Word n → Word n → Prop
  releaseBad : Nat → Word n → Word n → Prop
  returnStop : Nat → Word n → Word n → Prop
  returnBad : Nat → Word n → Word n → Prop

/-- Starting at ordinal j, freeze the release entry at launch and the
return entry at the actual completed arena release. The next leg
inherits the exact return acceptance word. -/
def legs {n : Nat} (C : Cuts n) (j : Nat) (launch : Word n) :
    (remaining : Nat) → Plan n (2*remaining)
  | 0 => .spent
  | m+1 => .cut (C.releaseStop j launch) (C.releaseBad j launch)
      (fun r => .cut (C.returnStop j r) (C.returnBad j r)
        (fun a => legs C (j+1) a m))

/-- The (2c+1)-trip phase shape from A0: one cleanup, then at most two
online decision cuts per trip. Physical rows instantiate `C`. -/
noncomputable def cleanupAndLegs {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (C : Cuts n) : Plan n (2*(2*c+1)+1) :=
  .cut (WindowA0CleanupLaunch.hit S x) (fun _ => False) (fun w => legs C 0 w (2*c+1))

/-- A release that itself accepts the return makes the complete
two-stage transition on that one completed word. -/
theorem same_mark_acceptance {n m j : Nat} (C : Cuts n)
    (goal : Word n → Prop) (l w : Word n) (hg : ¬goal w)
    (hr : C.releaseStop j l w) (hnr : ¬C.releaseBad j l w)
    (ht : C.returnStop j w w) (hnt : ¬C.returnBad j w w) :
    settle goal w (legs C j l (m+1)) = settle goal w (legs C (j+1) w m) := by
  simp only [legs]
  rw [settle_pass _ _ _ _ _ hg hr hnr, settle_pass _ _ _ _ _ hg ht hnt]

/-- The empty physical word is undecided for every live drained start,
independent of the leg cuts (which cannot run before cleanup). -/
theorem proper_online_attempt {p c n : Nat} {initial : Config p c n}
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (x : WindowA0ClosedEntry.State p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x)
    (hl : ¬WindowA0Ledger.done x.tag) (C : Cuts n) :
    ¬(onlineStage S x (cleanupAndLegs S x C)).ready [] :=
  proper_at_cleanup _ _ _ _ hl (WindowA0CleanupLaunch.properStart S J H x hx hl)

#print axioms same_mark_acceptance
#print axioms proper_online_attempt
#print axioms fold_append
#print axioms first_cut_resume
#print axioms fold_before_cut
#print axioms cleanup_goal_implies_stop
#print axioms onlineCleanup
#print axioms settle_accepted_iff
#print axioms fold_snoc
#print axioms ready_pad
#print axioms first_accepted_iff
#print axioms proper_at_cleanup
#print axioms onlineStage

end L4.WindowA0Cursor
