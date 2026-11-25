import Leader.L4.WindowA0ApproachOwned
import Leader.L4.WindowA0Trial

namespace L4.WindowA0CleanupLaunch
open TripleRenewal RootedAssembly WindowFiveStages WindowA0ClosedEntry

private theorem snoc_induction {α : Type} {P : List α → Prop}
    (w : List α) (nil : P []) (add : ∀ w e, P w → P (w++[e])) : P w := by
  have h (u : List α) : P u.reverse := by
    induction u with
    | nil => exact nil
    | cons e u ih => rw [List.reverse_cons]; exact add _ _ ih
  simpa using h w.reverse

noncomputable def observe {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (w : Word n) : WindowA0DirtyRepeat.State p c n :=
  GGTiming.runMarks (WindowA0DirtyRepeat.next S) (WindowA0DirtyRepeat.init x) w

theorem observe_step {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (w : Word n) (e : Fin n) :
    observe S x (wordNext w e)=WindowA0DirtyRepeat.next S (observe S x w) e := by
  rw [observe,wordNext,GGTiming.runMarks_append]
  rfl

def actual {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (w : Word n) : WindowA0ClosedEntry.State p c n :=
  GGTiming.runMarks (WindowA0ClosedEntry.next S) x w

theorem observe_project {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (w : Word n) :
    (observe S x w).pass.physical=actual S x w := by
  induction w using snoc_induction with
  | nil => exact WindowA0CleanupPass.afterX_project _
  | add u e ih =>
    change (observe S x (wordNext u e)).pass.physical=_
    rw [observe_step,WindowA0DirtyRepeat.project,ih]
    unfold actual
    rw [GGTiming.runMarks_append]
    rfl

open WindowA0DirtyRepeat in
theorem done_of_good_exit {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H : Nat}
    (z : WindowA0DirtyRepeat.State p c n) (h : Good initial S J H z)
    (hd : WindowA0Ledger.done z.pass.physical.tag) : done z := by
  rcases z with ⟨pass,k⟩
  cases pass with
  | x u => exact (h.1.2 (.inl hd)).elim
  | reverse u => exact (h.1.2.1 (.inl hd)).elim
  | forward u => exact (h.1.2 (.inl hd)).elim
  | done u b => trivial

theorem observe_good {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (hx : Admitted initial S J H x) (w : Word n) :
    WindowA0DirtyRepeat.Good initial S J H (observe S x w) := by
  induction w using snoc_induction with
  | nil => exact ⟨WindowA0CleanupPass.good_init x hx,trivial⟩
  | add u e ih =>
    change WindowA0DirtyRepeat.Good initial S J H (observe S x (wordNext u e))
    rw [observe_step]
    exact WindowA0DirtyRepeat.good_next hn S J H _ e ih

def hit {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (w : Word n) : Prop := WindowA0DirtyRepeat.done (observe S x w)

theorem properStart {p c n : Nat} {initial : Config p c n}
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (hx : Admitted initial S J H x) (hl : ¬ WindowA0Ledger.done x.tag) :
    ¬hit S x [] := by
  have hp := (hx.resolve_left hl).1.gapPos
  change 0<x.gap at hp
  have hg : ¬WindowA0XSweep.goal (⟨x,0⟩ : WindowA0XSweep.SweepState p c n) := by
    simp [WindowA0XSweep.goal,hl,show ¬x.gap≤0 by omega]
  simp [hit,observe,GGTiming.runMarks,WindowA0DirtyRepeat.done,WindowA0DirtyRepeat.init,
    WindowA0CleanupPass.init,WindowA0CleanupPass.afterX,hl,hg,WindowA0CleanupPass.ready]

/-- A continuing first cleanup cut is the actual L1 launch, not a
dirty L2 observation or the endpoint of a padded word. -/
theorem first_launch {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (hx : Admitted initial S J H x) (hl : ¬WindowA0Ledger.done x.tag)
    (w : Word n) (h : FirstExit (hit S x) w) (hw : ¬WindowA0Ledger.done (actual S x w).tag) :
    WindowA0ApproachOwned.Physical J .init (actual S x w) ((actual S x w).gap-1) := by
  induction w using snoc_induction with
  | nil => exact (properStart S J H x hx hl h.2).elim
  | add u e _ =>
    change FirstExit (hit S x) (wordNext u e) at h
    have hOld := ((clean_child _ u e).mp h.1).2
    have hnew := h.2
    change WindowA0DirtyRepeat.done (observe S x (wordNext u e)) at hnew
    rw [observe_step] at hnew
    have heq := observe_project S x (wordNext u e)
    rw [observe_step] at heq
    change ¬WindowA0Ledger.done (actual S x (wordNext u e)).tag at hw
    rw [←heq] at hw
    have H' := WindowA0ApproachOwned.init_after_first_terminal hn S J H (observe S x u) e
      (observe_good hn S J H x hx u) hOld hnew hw
    rw [heq] at H'
    exact H'

theorem word_mean {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (hx : Admitted initial S J H x) :
    IIDExpectedHittingTimeAtMost wordNext (hit S x) [] (n*((3*H+2)*(2*c)+4*H+2)) := by
  intro t
  have C := WindowA0Bridge.word_cost_le (WindowA0DirtyRepeat.next S) WindowA0DirtyRepeat.done
    (hit S x) (observe S x) (observe_step S x) (fun _ h => h) t []
  rw [show (3*H+2)*(2*c)+4*H+2=(3*H+2)*(2*c)+(4*H+2) by omega]
  exact Nat.le_trans C (WindowA0DirtyRepeat.mean hn S J H x hx t)

def startZero {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (J : Fin n) (x : WindowA0ClosedEntry.State p c n) (w : Word n) : Prop :=
  WindowA0Ledger.done (actual S x w).tag ∨
    WindowA0ApproachOwned.Physical J .init (actual S x w) ((actual S x w).gap-1)

private theorem no_failure {α : Type} {n : Nat} (next : α → Fin n → α)
    (stop : α → Prop) (t : Nat) (x : α) :
    terminalMass next stop (fun _ => False) t x=0 := by
  classical
  induction t generalizing x with
  | zero => simp [terminalMass]
  | succ t ih =>
    by_cases h : stop x
    · simp [terminalMass,h]
    · simp only [terminalMass,h,if_false,ih,TaggedTail.sumEdge]
      have z (m : Nat) : (List.ofFn (fun _ : Fin m => (0:Nat))).sum=0 := by
        induction m with
        | zero => rfl
        | succ m hz => simpa only [List.ofFn_succ,List.sum_cons,Nat.zero_add] using hz
      exact z n

/-- A literal failure-free cleanup layer. The caller's global trial
decision may be read here only when it cannot occur ahead of cleanup. -/
def cleanupLayer {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (hx : Admitted initial S J H x) (hl : ¬WindowA0Ledger.done x.tag)
    (ready : Word n → Prop) (early : ∀ w, Clean (hit S x) w → ready w → hit S x w) :
    WindowA0AttemptCredit.Layer wordNext ready (fun w => w=[]) (startZero S J x) 1 where
  localDone := hit S x
  localBad := fun _ => False
  live := Clean (hit S x)
  enter _ h := h.symm ▸ clean_nil _
  keep _ e h hd := (clean_child _ _ e).mpr ⟨h,hd⟩
  notEarly := early
  pass w h h' _ := by
    by_cases hd : WindowA0Ledger.done (actual S x w).tag
    · exact .inl hd
    · exact .inr (first_launch hn S J H x hx hl w ⟨h,h'⟩ hd)
  budget _ _ t := by simp [no_failure wordNext (hit S x)]

def cleanupTiming {p c n : Nat} {initial : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat) (x : WindowA0ClosedEntry.State p c n)
    (hx : Admitted initial S J H x) (hl : ¬WindowA0Ledger.done x.tag)
    (ready : Word n → Prop) :
    WindowA0Trial.TimedLayer wordNext ready (fun w => w=[]) (startZero S J x)
      (n*((3*H+2)*(2*c)+4*H+2)) where
  stop := hit S x
  live := Clean (hit S x)
  enter _ h := h.symm ▸ clean_nil _
  keep _ e h hd := (clean_child _ _ e).mpr ⟨h,hd⟩
  finish w h h' _ := by
    by_cases hd : WindowA0Ledger.done (actual S x w).tag
    · exact .inl hd
    · exact .inr (first_launch hn S J H x hx hl w ⟨h,h'⟩ hd)
  mean _ h := h.symm ▸ word_mean hn S J H x hx

#print axioms cleanupLayer
#print axioms cleanupTiming
#print axioms done_of_good_exit
#print axioms observe_good
#print axioms first_launch
#print axioms word_mean
end L4.WindowA0CleanupLaunch
