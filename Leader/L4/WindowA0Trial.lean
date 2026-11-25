import Leader.L4.WindowA0Bridge
import Leader.L4.WindowA0AttemptCredit

/-! The literal scheduler-word trial and the timing sum of its
decisions. Physical certificates for individual legs are separate. -/
namespace L4.WindowA0Trial
open TripleRenewal RootedAssembly WindowFiveStages WindowA0AttemptCredit TaggedTail
open Classical

def trialStage {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (x : WindowA0ClosedEntry.State p c n) (ready : Word n → Prop) :
    Stage (WindowA0ClosedEntry.next S) x where
  State := Word n
  start := []
  next := wordNext
  project := GGTiming.runMarks (WindowA0ClosedEntry.next S) x
  ready := ready
  reachable := fun _ => True
  projInit := rfl
  projStep u e := by rw [wordNext,GGTiming.runMarks_append]; rfl
  reachStart := trivial
  reachStep _ _ _ := trivial

theorem trial_restart {p c n : Nat} (hn : 4≤n)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (x : WindowA0ClosedEntry.State p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x)
    (ready : Word n → Prop) (w : Word n) :
    WindowA0ClosedEntry.Admitted initial S J H ((trialStage S x ready).project w) :=
  WindowA0ClosedEntry.close_word hn S J H x w hx

/-- Preserve the physical labels on every padded word; reading the
decision does not change the projection or what is restarted. -/
def attempt_of_layers {p c n : Nat} (hn : 4≤n)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (x : WindowA0ClosedEntry.State p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x)
    (ready : Word n → Prop) (proper : ¬ready []) (start : Nat → Word n → Prop)
    (cleanup : Layer wordNext ready (fun w => w=[]) (start 0) 1)
    (legs : GuardedLegs wordNext ready
      (fun w => ¬ WindowA0Ledger.done ((trialStage S x ready).project w).tag)
      (2*c+1) start)
    (clock : IIDExpectedHittingTimeAtMost wordNext ready [] (WindowA0Restart.attemptCost c n H)) :
    UniformAttempt (WindowA0ClosedEntry.next S) (fun y => WindowA0Ledger.done y.tag)
      (WindowA0ClosedEntry.Admitted initial S J H)
      (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) x :=
  assemble_attempt _ _ c H (trialStage S x ready) proper
    (fun w _ _ _ => trial_restart hn initial S J H x hx ready w)
    clock (fun w => w=[]) cleanup legs rfl

/-- A local timing cut. A bad local stop is already a ready trial;
a nonready stop instead hands off, including same-edge launches.
No local invariant is required past the first stop. -/
structure TimedLayer {α : Type} {n : Nat} (next : α → Fin n → α)
    (done entry handoff : α → Prop) (P : Nat) where
  stop : α → Prop
  live : α → Prop
  enter : ∀ x, entry x → live x
  keep : ∀ x e, live x → ¬stop x → live (next x e)
  finish : ∀ x, live x → stop x → ¬done x → handoff x
  mean : ∀ x, entry x → IIDExpectedHittingTimeAtMost next stop x P

private theorem sum_succ {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f=f 0+sumEdge (fun e => f e.succ) := by
  simp [sumEdge,List.ofFn_succ]

private theorem sum_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ e, f e≤g e) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ,sum_succ]; exact Nat.add_le_add (h _) (ih fun e => h e.succ)

private theorem sum_split {n : Nat} (f g : Fin n → Nat) (B : Nat) :
    sumEdge (fun e => f e+B*g e)=sumEdge f+B*sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_succ,sum_succ f,sum_succ g,ih,Nat.mul_add]; omega

theorem timed_compose {α : Type} {n : Nat} {next : α → Fin n → α}
    {done entry handoff : α → Prop} {P B : Nat} (L : TimedLayer next done entry handoff P)
    (tail : ∀ x, handoff x → IIDExpectedHittingTimeAtMost next done x B)
    (x : α) (hx : entry x) :
    IIDExpectedHittingTimeAtMost next done x (P+B) := by
  have path (t : Nat) (y : α) (hy : L.live y) :
      iidHitCost next done t y ≤ iidHitCost next L.stop t y +
        B*terminalMass next L.stop (fun z => ¬done z) t y := by
    induction t generalizing y with
    | zero => simp [iidHitCost]
    | succ t ih =>
      by_cases hd : done y
      · rw [iidHitCost_of_target _ _ _ hd]
        exact Nat.zero_le _
      · by_cases hs : L.stop y
        · simpa only [terminalMass,hs,if_true,hd,not_false_eq_true,
            iidHitCost_of_target next L.stop y hs,Nat.zero_add] using
            tail y (L.finish y hy hs hd) (t+1)
        · rw [iidHitCost,if_neg hd,iidHitCost,if_neg hs,terminalMass,if_neg hs]
          have H := sum_mono (fun e => ih (next y e) (L.keep y e hy hs))
          rw [sum_split] at H
          change n^(t+1)+sumEdge _≤n^(t+1)+sumEdge _+B*sumEdge _
          omega
  intro t
  have H := path t x (L.enter x hx)
  have M := L.mean x hx t
  have F := Nat.mul_le_mul_left B (terminalMass_le_total next L.stop
    (fun z => ¬done z) t x)
  rw [Nat.add_mul]
  omega

/-- Backward induction over the Q+1 physical legs. A leg packages its
approach, guarded release and return timing on the common state type.
There is no independent resampling of the release word. -/
theorem timed_legs {α : Type} {n K B : Nat} {next : α → Fin n → α}
    {done : α → Prop} {start : Nat → α → Prop}
    (legs : ∀ j, j<K → TimedLayer next done (start j) (start (j+1)) B)
    (last : ∀ x, start K x → done x) :
    ∀ j, j≤K → ∀ x, start j x →
      IIDExpectedHittingTimeAtMost next done x ((K-j)*B) := by
  suffices h : ∀ m j, j+m=K → ∀ x, start j x →
      IIDExpectedHittingTimeAtMost next done x (m*B) by
    exact fun j hj => h (K-j) j (by omega)
  intro m
  induction m with
  | zero =>
    intro j hj x hx t
    have he : j=K := by omega
    subst j
    rw [iidHitCost_of_target _ _ _ (last x hx)]
    exact Nat.zero_le _
  | succ m ih =>
    intro j hj x hx
    have hb := timed_compose (legs j (by omega))
      (fun y hy => ih (j+1) (by omega) y hy) x hx
    simpa only [Nat.succ_mul, Nat.add_comm] using hb

theorem clock_budget (c n H : Nat) :
    n*((3*H+2)*(2*c)+4*H+2)+(2*c+1)*(n*(2*(H+1)+3))
      ≤ WindowA0Restart.attemptCost c n H := by
  unfold WindowA0Restart.attemptCost
  let Q := 2*c
  calc
    _ = n*((3*H+2)*Q+4*H+2+(Q+1)*(2*(H+1)+3)) := by
      change n*((3*H+2)*Q+4*H+2)+(Q+1)*(n*(2*(H+1)+3))=_
      rw [Nat.mul_left_comm (Q+1) n,←Nat.mul_add]
    _ ≤ n*(16*(Q+3)*(H+1)) := by
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.one_mul,Nat.mul_one]
      rw [Nat.mul_comm H Q,Nat.mul_left_comm Q 2 H]
      omega
    _ = _ := by unfold Q; ac_rfl

/-- Target 6's clock assembly from literal local timing witnesses.
All physical timings remain premises until the local row folds exist. -/
theorem attempt_clock_of_timed_layers {c n H : Nat} {ready entry : Word n → Prop}
    {start : Nat → Word n → Prop}
    (clean : TimedLayer wordNext ready entry (start 0) (n*((3*H+2)*(2*c)+4*H+2)))
    (legs : ∀ j, j<2*c+1 →
      TimedLayer wordNext ready (start j) (start (j+1)) (n*(2*(H+1)+3)))
    (last : ∀ w, start (2*c+1) w → ready w) (he : entry []) :
    IIDExpectedHittingTimeAtMost wordNext ready [] (WindowA0Restart.attemptCost c n H) := by
  apply expected_mono _ (clock_budget c n H)
  exact timed_compose clean (fun y hy =>
    by simpa only [Nat.sub_zero] using timed_legs legs last 0 (Nat.zero_le _) y hy) [] he

#print axioms timed_compose
#print axioms timed_legs
#print axioms attempt_clock_of_timed_layers
#print axioms trial_restart
#print axioms attempt_of_layers
#print axioms clock_budget
end L4.WindowA0Trial
