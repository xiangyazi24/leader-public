import Leader.L4.WindowA0ReleaseRing
import Leader.L4.WindowA0Route

/-! Connect the six-label release monitor to literal seven-tag routing. -/
namespace L4.WindowA0RoutedRelease
open SevenTagCharge WindowA0Release WindowA0ReleaseCredit TripleRenewal

abbrev State (p c n : Nat) := Ledger p c n × Phase

/-- Test selected loss first, then either A0 ghost's birth, on old
tags and the *completed* physical pair. No exterior birth is a stop. -/
def early {p c n : Nat} (g : List (Fin n)) (a b : Fin n)
    (z : Ledger p c n) (e : Fin n) : Bool :=
  decide (WindowA0Route.routeTwo g a b z e ≠ .keep)

/-- Regardless of the monitor decision, the full seven-tag ledger takes
the actual step. Only its independent first-decision phase is sticky. -/
def next {p c n : Nat} (g : List (Fin n)) (a b base : Fin n) (s : Kind)
    (z : State p c n) (e : Fin n) : State p c n :=
  (advance z.1 e,
    (monitorNext base s (fun _ e' => early g a b z.1 e') (z.1.config,z.2) e).2)

theorem projection {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (z : State p c n) (e : Fin n) :
    (next g a b base s z e).1=advance z.1 e := rfl

theorem frame {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (z : State p c n) (k : Fin 3) (hk : z.2=.waiting k) :
    Nonempty (Frame (next g a b base s) Prod.snd (WindowA0Return.guardLabels base) z k) := by
  let H := release_frame base s (fun _ e' => early g a b z.1 e')
    (z.1.config,z.2) k hk
  exact ⟨⟨H.requested,H.inside,H.onRequest,H.outside⟩⟩

/-- Actual routed release, rather than arbitrary `early`, admits the
1/216 competing-mark credit at each finite horizon. This theorem acts
only after the outward monitor has certified admissible entry. -/
theorem failure_mass {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (z : Ledger p c n) (t : Nat) :
    216*terminalMass (next g a b base s)
      (fun y => done y.2) (fun y => y.2=.failed) t (z,.waiting 0)≤215*n^t := by
  classical
  let build (x : State p c n) (k : Fin 3) (h : x.2=.waiting k) :=
    Classical.choice (frame g a b base s x k h)
  have C := finite_credit (next g a b base s) Prod.snd (WindowA0Return.guardLabels base)
    (by simp [WindowA0Return.guardLabels]) (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun x k _ hk => build x k hk) t (z,.waiting 0) trivial
  change _ + 1*n^t ≤ 216*n^t at C
  rw [Nat.one_mul] at C
  omega

/-- If this mark physically exits A0, it is credited even when it
would otherwise spoil the local release order. -/
theorem exit_priority {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (z : State p c n) (e : Fin n) (k : Fin 3)
    (hk : z.2=.waiting k) (he : WindowA0Route.routeTwo g a b z.1 e≠.keep) :
    (next g a b base s z e).2=.success := by
  simp [next,monitorNext,hk,early,he]

/-- Successful first release decision on a raw keep can only be the
last requested script mark. Earlier successes are real routed exits. -/
theorem success_on_keep {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (z : State p c n) (e : Fin n) (k : Fin 3)
    (hk : z.2=.waiting k) (he : WindowA0Route.routeTwo g a b z.1 e=.keep)
    (hs : (next g a b base s z e).2=.success) :
    e=asked base s k ∧ k.val=2 := by
  unfold next at hs
  simp only [monitorNext,hk,early,he,ne_eq,not_true_eq_false,decide_false,
    Bool.false_eq_true,if_false] at hs
  split at hs
  · rename_i h
    refine ⟨h,?_⟩
    split at hs
    · cases hs
    · have := k.isLt; omega
  · split at hs <;> cases hs

/-- The isolated physical snapshot before each request. Off-guard
intervening marks can alter other fields of the ring without changing
agreement with this snapshot on its protected records. -/
def reference {p c n : Nat} (x : Config p c n) (base : Fin n) (s : Kind)
    (k : Fin 3) : Config p c n :=
  if k.val=0 then x else if k.val=1 then step x (asked base s 0)
  else step (step x (asked base s 0)) (asked base s 1)

private theorem reference_tick {p c n : Nat} (x : Config p c n) (base : Fin n) (s : Kind)
    (k : Fin 3) (h : k.val+1<3) :
    reference x base s ⟨k.val+1,h⟩=step (reference x base s k) (asked base s k) := by
  have ht : k.val=0 ∨ k.val=1 := by omega
  rcases ht with h0|h1
  · have he : k=0 := Fin.ext h0
    subst k
    rfl
  · have he : k=1 := Fin.ext h1
    subst k
    rfl

private theorem offsets {s : Kind} (k : Fin 3) : 1≤offset s k ∧ offset s k≤3 := by
  cases s with
  | paid => simp only [offset]; have := k.isLt; omega
  | unpaid => simp only [offset]; split <;> decide

/-- Induction invariant for the *continuing* actual routed attempt. -/
def View {p c n : Nat} (x : Config p c n) (base : Fin n) (s : Kind) (z : State p c n) : Prop :=
  ∀ k, z.2=.waiting k → Agree base z.1.config (reference x base s k)

theorem view_step {p c n : Nat} (g : List (Fin n)) (a b base : Fin n) (s : Kind)
    (x : Config p c n) (z : State p c n) (e : Fin n) (hv : View x base s z) :
    View x base s (next g a b base s z e) := by
  intro j hj
  have H := hj
  unfold next at H
  cases hz : z.2 with
  | success | failed => simp [monitorNext,hz] at H
  | waiting k =>
    have old := hv k hz
    by_cases exit : early g a b z.1 e=true
    · simp [monitorNext,hz,exit] at H
    · by_cases req : e=asked base s k
      · subst e
        by_cases hk : k.val+1<3
        · have eq : j=⟨k.val+1,hk⟩ := by simpa [monitorNext,hz,exit,hk] using H.symm
          subst j
          change Agree base (step z.1.config (asked base s k)) _
          rw [reference_tick]
          exact requested_agrees base (offset s k) (offsets k).1 (offsets k).2 old
        · simp [monitorNext,hz,exit,hk] at H
      · by_cases he : e∈WindowA0Return.guardLabels base
        · simp [monitorNext,hz,exit,req,he] at H
        · have E : j=k := by simpa [monitorNext,hz,exit,req,he] using H.symm
          subst j
          exact agree_trans (outside_agrees z.1.config base e he) old

theorem view_start {p c n : Nat} (base : Fin n) (s : Kind) (z : Ledger p c n) :
    View z.config base s (z,.waiting 0) := by
  intro k hk
  have E : k=0 := by simpa using congrArg id hk.symm
  subst k
  intro j hj hb
  rfl

/-- At the third mark, the true pair to be released has the same two
old records as in the isolated script, if no real routed exit already
occurred. This discharges the physical output transport independently
of any residual return-tracking invariant. -/
theorem last_pair_agrees {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (x : Config p c n) (z : State p c n) (e : Fin n) (k : Fin 3)
    (hv : View x base s z) (hk : z.2=.waiting k)
    (he : WindowA0Route.routeTwo g a b z.1 e=.keep)
    (hs : (next g a b base s z e).2=.success) :
    z.1.config e=reference x base s 2 e ∧
      z.1.config (rightNeighbor e)=reference x base s 2 (rightNeighbor e) := by
  obtain ⟨req,last⟩ := success_on_keep g a b base s z e k hk he hs
  have E : k=2 := Fin.ext last
  subst k
  rw [req]
  have H := hv 2 hk
  refine ⟨H (offset s 2) (offsets 2).1 (by have := (offsets (s:=s) 2).2; omega),?_⟩
  change z.1.config (rightNeighbor (liftedSite base (offset s 2)))=
    reference x base s 2 (rightNeighbor (liftedSite base (offset s 2)))
  rw [←liftedSite_succ]
  exact H (offset s 2+1) (by omega) (by have := (offsets (s:=s) 2).2; omega)

/-- The literal snapshot invariant applies to any raw word, not just
the nominal ordered tape. -/
theorem view_run {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (z : Ledger p c n) (w : List (Fin n)) :
    View z.config base s (GGTiming.runMarks (next g a b base s) (z,.waiting 0) w) := by
  have go (y : State p c n) (h : View z.config base s y) :
      View z.config base s (GGTiming.runMarks (next g a b base s) y w) := by
    induction w generalizing y with
    | nil => exact h
    | cons e w ih => exact ih _ (view_step g a b base s z.config y e h)
  exact go _ (view_start base s z)

/-- A credited keep really releases or accepts the actual pair, not a
race surrogate. The isolated reference-cut premise is precisely the
conclusion of a ring paid/unpaid script. If the reference certified an
early living top, the caller's live ghost invariant excludes that lane. -/
theorem credited_release_of_reference {p c n : Nat} (g : List (Fin n)) (a b base : Fin n)
    (s : Kind) (q : FixedResidual.Trip (2*c)) (x : Config p c n)
    (z : State p c n) (e : Fin n) (k : Fin 3)
    (hv : View x base s z) (hk : z.2=.waiting k)
    (he : WindowA0Route.routeTwo g a b z.1 e=.keep)
    (hs : (next g a b base s z e).2=.success)
    (ghost : (z.1.config e).leader=false)
    (isolated :
      let v := reference x base s 2
      let r := asked base s 2
      (v r).leader=true ∨ Released (v r) (v (rightNeighbor r)) q) :
    Released (z.1.config e) (z.1.config (rightNeighbor e)) q := by
  obtain ⟨H,J⟩ := last_pair_agrees g a b base s x z e k hv hk he hs
  obtain ⟨E,K⟩ := success_on_keep g a b base s z e k hk he hs
  have L : k=2 := Fin.ext K
  subst k
  rw [H,J,E]
  dsimp only at isolated
  rcases isolated with LL|LL
  · have C : (reference x base s 2 (asked base s 2)).leader=false := by
      exact (congrArg Site.leader (H.trans (congrArg (reference x base s 2) E))).symm.trans ghost
    rw [LL] at C
    cases C
  · exact LL

#print axioms failure_mass
#print axioms success_on_keep
end L4.WindowA0RoutedRelease
