import Leader.L4.WindowA0GapOne
import Leader.L4.WindowA0Machine
import Leader.L4.WindowA0Bridge
import Leader.L4.WindowA0Trial

namespace L4.WindowA0GapOneWord
open TripleRenewal RootedAssembly WindowA0ReleaseCredit WindowFiveStages
open Classical

def stopped {p c n : Nat} (z : WindowA0GapOne.State p c n) : Prop := done z.2
def failed {p c n : Nat} (z : WindowA0GapOne.State p c n) : Prop := z.2=.failed

def observe {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (i : Fin n) (z : WindowA0Ledger.State p c n) (w : List (Fin n)) :
    WindowA0GapOne.State p c n :=
  GGTiming.runMarks (WindowA0GapOne.next S i) (z,.waiting 0) w

theorem observe_step {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : WindowA0Ledger.State p c n) (w : List (Fin n)) (e : Fin n) :
    observe S i z (wordNext w e) = WindowA0GapOne.next S i (observe S i z w) e := by
  simp only [observe,wordNext,GGTiming.runMarks_append]
  rfl

theorem observe_actual {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (x : WindowA0ClosedEntry.State p c n) (w : List (Fin n)) :
    (observe S i x.tag w).1 = (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w).tag := by
  have run (z : WindowA0GapOne.State p c n) (y : WindowA0ClosedEntry.State p c n)
      (hy : z.1=y.tag) :
      (GGTiming.runMarks (WindowA0GapOne.next S i) z w).1 =
        (GGTiming.runMarks (WindowA0ClosedEntry.next S) y w).tag := by
    induction w generalizing z y with
    | nil => exact hy
    | cons e w ih =>
      apply ih
      change WindowA0Ledger.next S z.1 e=WindowA0Ledger.next S y.tag e
      rw [hy]
  exact run _ x rfl

theorem terminalMass_map {α β : Type} {n : Nat} (f : α → Fin n → α) (g : β → Fin n → β)
    (project : α → β) (h : ∀ x e, project (f x e)=g (project x) e)
    (d b : β → Prop) (t : Nat) (x : α) :
    terminalMass f (fun y => d (project y)) (fun y => b (project y)) t x =
      terminalMass g d b t (project x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hd : d (project x)
    · simp only [terminalMass,hd,if_true]
    · simp only [terminalMass,hd,if_false,ih,h]

def reserve : Phase → Nat
  | .waiting k => if k.val=0 then 2 else 1
  | _ => 0

def nominate {p c n : Nat} (i : Fin n) (z : WindowA0GapOne.State p c n) : Fin n :=
  match z.2 with
  | .waiting k => WindowA0GapOne.ask i k
  | _ => i

theorem stopped_next {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : WindowA0GapOne.State p c n) (e : Fin n) (h : stopped z) :
    stopped (WindowA0GapOne.next S i z e) := by
  cases hz : z.2 <;> simp_all [stopped, done,WindowA0GapOne.next]

theorem drop_step {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : WindowA0GapOne.State p c n) (e : Fin n) (h : ¬stopped z) :
    reserve (WindowA0GapOne.next S i z e).2+(if e=nominate i z then 1 else 0)≤reserve z.2 := by
  cases hz : z.2 with
  | success | failed => exact (h (by simp [stopped,done,hz])).elim
  | waiting k =>
    simp only [WindowA0GapOne.next, hz, nominate, reserve]
    by_cases he : e=WindowA0GapOne.ask i k
    · subst e
      by_cases hr : (WindowA0Ledger.next S z.1 (WindowA0GapOne.ask i k)).reason.isSome=true <;>
        by_cases hk : k.val=0 <;> simp [hr,hk]
    · by_cases hr : (WindowA0Ledger.next S z.1 e).reason.isSome=true <;>
        by_cases hmem : e∈labelsAt i <;> by_cases hk : k.val=0 <;>
        simp [hr,he,hmem,hk]

/-- Both successes and spoiling labels stop the local experiment.
The countdown uses only the two requested raw labels. -/
theorem physical_mean {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : WindowA0Ledger.State p c n) :
    IIDExpectedHittingTimeAtMost (WindowA0GapOne.next S i) stopped
      (z,.waiting 0) (n*2) := by
  apply WindowA0Machine.mean_of_reachable_budget (WindowA0GapOne.next S i)
    stopped (fun _ => True) (fun y => reserve y.2) (nominate i)
    (fun _ _ _ _ => trivial) (fun y e _ h => drop_step S i y e h)
    (z,.waiting 0) trivial (stopped_next S i)

theorem word_mean {p c n : Nat} (S : WindowA0Ledger.Scope n) (i : Fin n)
    (z : WindowA0Ledger.State p c n) :
    IIDExpectedHittingTimeAtMost wordNext (fun w => stopped (observe S i z w)) [] (n*2) := by
  intro t
  have C := WindowA0Bridge.word_cost_le (WindowA0GapOne.next S i)
    stopped (fun w => stopped (observe S i z w)) (observe S i z)
    (observe_step S i z) (fun _ h => h) t []
  exact Nat.le_trans C (physical_mean S i z t)

theorem word_failure {p c n : Nat} (hn : 4≤n) (S : WindowA0Ledger.Scope n)
    (i : Fin n) (z : WindowA0Ledger.State p c n) (t : Nat) :
    216*terminalMass wordNext (fun w => stopped (observe S i z w))
      (fun w => failed (observe S i z w)) t []≤215*n^t := by
  rw [terminalMass_map wordNext (WindowA0GapOne.next S i) (observe S i z)
    (observe_step S i z) stopped failed t []]
  exact WindowA0GapOne.short_release_mass hn S i z t

/-- A clean suffix reaches the actual first decision. Padding after
that decision is deliberately not a live continuation premise. -/
def creditLayer {p c n : Nat} (hn : 4≤n) (S : WindowA0Ledger.Scope n)
    (i : Fin n) (z : WindowA0Ledger.State p c n)
    (ready handoff : Word n → Prop)
    (early : ∀ w, Clean (fun v => stopped (observe S i z v)) w →
      ready w → stopped (observe S i z w))
    (good : ∀ w, FirstExit (fun v => stopped (observe S i z v)) w →
      (observe S i z w).2=.success → handoff w) :
    WindowA0AttemptCredit.Layer wordNext ready (fun w => w=[]) handoff 216 where
  localDone w := stopped (observe S i z w)
  localBad w := failed (observe S i z w)
  live := Clean (fun v => stopped (observe S i z v))
  enter _ h := h.symm ▸ clean_nil _
  keep _ e h h' := (clean_child _ _ e).mpr ⟨h,h'⟩
  notEarly := early
  pass w h h' hbad := by
    apply good w ⟨h,h'⟩
    cases hp : (observe S i z w).2
    · simp [stopped,done,hp] at h'
    · rfl
    · exact (hbad hp).elim
  budget _ h t := h.symm ▸ word_failure hn S i z t

def timingLayer {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (i : Fin n) (z : WindowA0Ledger.State p c n)
    (ready handoff : Word n → Prop)
    (fail_ready : ∀ w, FirstExit (fun v => stopped (observe S i z v)) w →
      failed (observe S i z w) → ready w)
    (good : ∀ w, FirstExit (fun v => stopped (observe S i z v)) w →
      (observe S i z w).2=.success → handoff w) :
    WindowA0Trial.TimedLayer wordNext ready (fun w => w=[]) handoff (n*2) where
  stop w := stopped (observe S i z w)
  live := Clean (fun v => stopped (observe S i z v))
  enter _ h := h.symm ▸ clean_nil _
  keep _ e h h' := (clean_child _ _ e).mpr ⟨h,h'⟩
  finish w h h' hn := by
    apply good w ⟨h,h'⟩
    cases hp : (observe S i z w).2
    · simp [stopped,done,hp] at h'
    · rfl
    · exact (hn (fail_ready w ⟨h,h'⟩ hp)).elim
  mean _ h := h.symm ▸ word_mean S i z

#print axioms creditLayer
#print axioms timingLayer
#print axioms observe_actual
#print axioms terminalMass_map
#print axioms physical_mean
#print axioms word_mean
#print axioms word_failure
end L4.WindowA0GapOneWord
