import Leader.L4.WindowA0Cleanup

/-! A0 moving cleanup and outward-approach countdowns. The raw observer
is a caller: the hypotheses naming its actual stage changes are explicit. -/
namespace L4.WindowA0Machine
open GGTiming FixedResidual

/-- Turn local progress bounds into the paper's same-raw-word clock.
No skipped competing mark is assumed to be inert. -/
theorem mean_of_reachable_budget {α : Type} {n : Nat} (next : α → Fin n → α)
    (exit good : α → Prop) (B : α → Nat) (nom : α → Fin n)
    (keep : ∀ x e, good x → ¬exit x → good (next x e))
    (drop : ∀ x e, good x → ¬exit x →
      B (next x e)+(if e=nom x then 1 else 0)≤B x)
    (x : α) (hx : good x)
    (sticky : ∀ x e, exit x → exit (next x e)) :
    IIDExpectedHittingTimeAtMost next exit x (n*B x) := by
  classical
  have obs (w : List (Fin n)) (s : α) (hs : good s ∨ exit s) :
      good (runMarks next s w) ∨ exit (runMarks next s w) := by
    induction w generalizing s with
    | nil => exact hs
    | cons e w ih =>
      apply ih (next s e)
      by_cases h : exit s
      · exact .inr (sticky _ _ h)
      · exact .inl (keep _ _ (hs.resolve_right h) h)
  have reach (w : List (Fin n)) (hn : ¬exit (runMarks next x w)) :
      good (runMarks next x w) := (obs w x (.inl hx)).resolve_right hn
  let C : Countdown next exit x :=
    ⟨fun w => B (runMarks next x w),fun w => nom (runMarks next x w),by
      intro w hw e
      rw [runMarks_append]
      exact drop _ e (reach w hw) hw⟩
  exact expected_of_countdown next exit x C

/-- The geometry of the unique authentic outward worker on the same
raw tape. top and worker are absolute lifts on the chosen retained arc. -/
structure Position where
  top : Nat
  worker : Nat

def approachBudget (x : Position) : Nat := x.worker-x.top

/-- Physical motion named by the actual selected label. At marked
first-adjacency termination, the same record can still be computed
before the observer starts the separate release experiment. -/
structure ApproachMark {n : Nat} (base e : Fin n) (x y : Position) where
  paid : Bool
  outward : Bool
  topExact : y.top=x.top+paid.toNat
  workerExact : y.worker=x.worker-outward.toNat
  paidLabel : paid=true → e=GGStage.incoming base x.top
  outwardLabel : outward=true → e=GGStage.incoming base x.worker

theorem approach_mark_drop {n : Nat} (base e : Fin n) (x y : Position)
    (h : x.top+2≤x.worker) (A : ApproachMark base e x y)
    (progress : e=GGStage.incoming base x.worker → A.outward=true) :
    approachBudget y+(if e=GGStage.incoming base x.worker then 1 else 0)
      ≤ approachBudget x := by
  rw [approachBudget,approachBudget,A.topExact,A.workerExact]
  by_cases he : e=GGStage.incoming base x.worker
  · simp only [he,if_true,progress he,Bool.toNat_true]
    have hp : A.paid.toNat≤1 := by cases A.paid <;> decide
    omega
  · simp only [he,if_false,Nat.add_zero]
    omega

theorem first_admission {n : Nat} (base e : Fin n) (x y : Position)
    (h : x.top+2≤x.worker) (hU : x.worker<n) (A : ApproachMark base e x y)
    (near : y.worker≤y.top+1) : y.worker=y.top+1 := by
  rw [A.workerExact,A.topExact] at near ⊢
  exact WindowA0Guard.first_adjacent_raw base e h hU A.paid A.outward
    A.paidLabel A.outwardLabel near

/-- Interface for an actual first-contact monitor. Failure, significant
birth, and selected retirement are not identified with a keep mark. Once
one is terminal the monitor must stay terminal. No physical evolution
is asserted for the projected position after a terminal transition. -/
structure ApproachFrame {α : Type} {n : Nat} (next : α → Fin n → α)
    (base : Fin n) (pos : α → Position) (good exit : α → Prop) where
  far : ∀ x, good x → ¬exit x → (pos x).top+2≤(pos x).worker
  sticky : ∀ x e, exit x → exit (next x e)
  keep : ∀ x e, good x → ¬exit x → good (next x e)
  motion : ∀ x e, good x → ¬exit x → ¬exit (next x e) →
    Nonempty (ApproachMark base e (pos x) (pos (next x e)))
  moves : ∀ x e, good x → ¬exit x → ¬exit (next x e) →
    ∀ A : ApproachMark base e (pos x) (pos (next x e)),
      e=GGStage.incoming base (pos x).worker → A.outward=true

/-- Once the clean first-contact frame is supplied, the literal
nominated worker mark gives a mean bound n times the remaining gap. -/
theorem approach_mean {α : Type} {n : Nat} (next : α → Fin n → α)
    (base : Fin n) (pos : α → Position) (good exit : α → Prop)
    (F : ApproachFrame next base pos good exit) (x : α) (hx : good x) :
    IIDExpectedHittingTimeAtMost next exit x (n*approachBudget (pos x)) := by
  classical
  let B := fun y => if exit y then 0 else approachBudget (pos y)
  let N := fun y => GGStage.incoming base (pos y).worker
  have H := mean_of_reachable_budget next exit good B N F.keep (by
    intro y e hy hnow
    by_cases ht : exit (next y e)
    · simp only [B,if_pos ht,if_neg hnow,Nat.zero_add]
      have h := F.far y hy hnow
      unfold approachBudget
      split <;> omega
    · rw [show B (next y e)=approachBudget (pos (next y e)) from if_neg ht,
          show B y=approachBudget (pos y) from if_neg hnow]
      obtain ⟨A⟩ := F.motion y e hy hnow ht
      exact approach_mark_drop base e _ _ (F.far y hy hnow) A (F.moves y e hy hnow ht A)
    ) x hx F.sticky
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by
    by_cases h : exit x <;> simp [B,h])))

/-- INIT overwrites arbitrary inherited non-X rails ahead; subsequent
authenticated COUNT legs only use a clean E/T receiver. -/
def Writable {Q : Nat} (q : Trip Q) (r : Rail) : Prop :=
  match q with
  | .init => r ≠ .x
  | .count _ => r = .e ∨ r = .t

theorem body_authentic_worker {Q : Nat} (q : Trip Q) (a : Rail)
    (h : Writable q a) : ResidualSweep.body a (outward q) = (outward q,.t) := by
  cases q with
  | init =>
    cases a <;> first | rfl | exact (h rfl).elim
  | count k =>
    rcases h with he|he <;> rw [he] <;> rfl

/-- Physical worker advance, including the INIT case where an inherited
upward or downward token ahead is overwritten by the authentic Ui. -/
theorem ordinary_worker {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hl : (stepPrefix u v).2.leader = false)
    (hm : (stepPrefix u v).1.mark = false)
    (hs : (stepPrefix u v).2.source = .off)
    (ha : Writable q (stepPrefix u v).1.rail)
    (hb : (stepPrefix u v).2.rail = outward q) :
    ((pairStep u v).1.rail,(pairStep u v).2.rail) = (outward q,.t) := by
  rw [WindowA0Cleanup.ordinary_rails u v hl hm hs,hb]
  exact body_authentic_worker q _ ha

/-- An outgoing service of the worker cannot detach it through its own
trail. An interior trail-trail service likewise changes no rail. -/
theorem ordinary_trail {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hl : (stepPrefix u v).2.leader = false)
    (hm : (stepPrefix u v).1.mark = false)
    (hs : (stepPrefix u v).2.source = .off)
    (ha : (stepPrefix u v).1.rail = outward q ∨ (stepPrefix u v).1.rail = .t)
    (hb : (stepPrefix u v).2.rail = .t) :
    ((pairStep u v).1.rail,(pairStep u v).2.rail) = ((stepPrefix u v).1.rail,.t) := by
  rw [WindowA0Cleanup.ordinary_rails u v hl hm hs,hb]
  rcases ha with ha|ha
  · rw [ha]
    cases q <;> rfl
  · rw [ha]; rfl

/-- At the pinned waiting door, even on a selected off-nomination mark
there is no birth, no new source phase, and no change to the worker
or trail at its old left endpoint. The right/top rail may turn. -/
theorem pinned_waiting_door {p c : Nat} (u v : Site p c) (q : Trip (2*c))
    (hl : (stepPrefix u v).2.leader = false)
    (hm : (stepPrefix u v).1.mark = true)
    (hs : (stepPrefix u v).2.source = waitingFor q)
    (ha : (stepPrefix u v).1.rail = outward q ∨ (stepPrefix u v).1.rail = .t) :
    (pairStep u v).1.rail = (stepPrefix u v).1.rail ∧
    (pairStep u v).2.source = waitingFor q ∧ (pairStep u v).2.leader=false := by
  let z := stepPrefix u v
  let a := patrol true true false (waitingFor q) z.1.rail z.2.rail
  have hrow : serviceDoor (waitingFor q) z.1.rail =
      ⟨waitingFor q,z.1.rail,.e,false⟩ := by
    rcases ha with h|h
    · change z.1.rail = outward q at h
      rw [h,door_wait_outward]
    · change z.1.rail = .t at h
      rw [h,door_wait_trail]
  obtain ⟨hsrc,hleft,hfire⟩ := door_exact (waitingFor q) z.1.rail z.2.rail
  rw [hrow] at hsrc hleft hfire
  change a.source = waitingFor q at hsrc
  change a.left = z.1.rail at hleft
  change a.fire = false at hfire
  simp only [pairStep,hl,hm,hs,pinned,Bool.false_or,Bool.not_false,Bool.true_and]
  change (finishBirth a.fire _ _).1.rail = _ ∧
    (finishBirth a.fire _ _).2.source=waitingFor q ∧
    (finishBirth a.fire _ _).2.leader=false
  rw [hfire]
  simpa [finishBirth,patrolWrite,hl] using And.intro hleft (And.intro hsrc hl)

end L4.WindowA0Machine
