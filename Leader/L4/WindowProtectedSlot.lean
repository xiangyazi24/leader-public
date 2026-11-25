import Leader.L4.WindowPushEntry

namespace L4.WindowProtectedSlot
open WindowA0Push WindowPushEntry WindowProtectedOuter
  WindowFiveStages RootedAssembly GGTiming RankRenewal

/-- The route in the birth-probability observer uses the actual named
supplier's old tag, not a freshly selected or censored label. -/
def certified {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : Entry initial g) : List (Fin n) :=
  (E.ledger.slots (RearTrace.predecessor E.supplier)).toList

/-- The clock observer and birth-mass observer agree on every ledger
and their terminal flags. Donors need agree only on retained cuts. -/
def Match {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : Entry initial g) (s : WindowA0Push.State p c n) (R : Running initial g) : Prop :=
  R.start=E ∧ s.cursor.ledger=R.q.ledger ∧ s.terminal=R.q.terminal ∧
    (s.terminal=false → s.donor=R.q.donor)

theorem match_step {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : Entry initial g) (s : WindowA0Push.State p c n) (R : Running initial g)
    (H : Match E s R) (e : Fin n) :
    Match E (WindowA0Push.next E.supplier g (certified E) E.victim s e)
      (pushNext R e) := by
  obtain ⟨hs,hl,ht,hd⟩ := H
  have hret : (pushNext R e).start=E := hs
  refine ⟨hret,?_,?_,?_⟩
  all_goals
    cases hT : s.terminal
    · have hT' : R.q.terminal=false := ht.symm.trans hT
      have hD := hd hT
      cases Hroute : WindowLocal.route g ((E.ledger.slots (RearTrace.predecessor E.supplier)).toList) (some E.victim) R.q.ledger e <;>
        simp [WindowA0Push.next, WindowFourHeadCut.tick, pushNext,
          WindowProtectedMass.next, pushNext.someSupplier, certified, hs, hl, hT, hT', hD,
          Hroute]
    · have hT' : R.q.terminal=true := ht.symm.trans hT
      simp [WindowA0Push.next, WindowFourHeadCut.tick, pushNext,
        WindowProtectedMass.next, hs, hl, hT, hT']

theorem match_run {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : Entry initial g) (s : WindowA0Push.State p c n) (R : Running initial g)
    (H : Match E s R) (u : List (Fin n)) :
    Match E (runMarks (WindowA0Push.next E.supplier g (certified E) E.victim) s u)
      (runMarks pushNext R u) := by
  induction u generalizing s R with
  | nil => exact H
  | cons e u ih => exact ih _ _ (match_step E s R H e)

/-- Exact finite-horizon equality compares the same raw alphabets. -/
theorem cost_eq {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : Entry initial g) (t : Nat) (s : WindowA0Push.State p c n) (R : Running initial g)
    (H : Match E s R) :
    iidHitCost (WindowA0Push.next E.supplier g (certified E) E.victim)
      (fun y => y.terminal=true) t s =
    iidHitCost pushNext (fun r : Running initial g => r.q.terminal=true) t R := by
  classical
  induction t generalizing s R with
  | zero => simp [iidHitCost]
  | succ t ih =>
    have hflags := H.2.2.1
    by_cases h : s.terminal=true
    · rw [iidHitCost_of_target _ (fun y : WindowA0Push.State p c n => y.terminal=true) _ h,
          iidHitCost_of_target _ (fun r : Running initial g => r.q.terminal=true) _ (hflags.symm.trans h)]
    · have h' : ¬R.q.terminal=true := fun hh => h (hflags.trans hh)
      rw [iidHitCost, if_neg h, iidHitCost, if_neg h']
      congr 1
      apply congrArg TaggedTail.sumEdge
      funext e
      exact ih _ _ (match_step E s R H e)

/-- The authentic protected observer itself has the push clock: the
comparison needs no restart or redraw after the named kill. -/
theorem protected_mean {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (E : Entry initial g) (j w k b cTag : Fin n) (bi ci h C : Nat)
    (hb : b∈g) (hk : cTag∈g) (hab : E.victim≠b)
    (hsub : certified E ⊆ g)
    (H : ValidCut initial E.supplier (certified E) E.victim b cTag
      (start E.ledger j w k E.donor bi ci))
    (hQuiet : QuietEntrance E.ledger.config)
    (hspan : E.donor+1+(bi+1)+(ci+1)≤h) (hC : 4096≤C) :
    IIDExpectedHittingTimeAtMost pushNext
      (fun r : Running initial g => r.q.terminal=true)
      (startRunning E) (C*n*(h+1)) := by
  let s := start E.ledger j w k E.donor bi ci
  let P := 2*(bi+1)+(ci+1)+1
  let m := min (n-2) (max 2 (E.donor+P))
  have K := push_mean hp hc hn E.supplier g (certified E) E.victim b cTag
    E.inGroup hb hk hab hsub s H hQuiet (bi+1) (ci+1) rfl (by
      change bi+1+ci+1=(bi+1)+(ci+1)
      omega)
  have HM : Match E s (startRunning E) := ⟨rfl,rfl,rfl,fun _ => rfl⟩
  have hm : m≤max 2 (E.donor+P) := Nat.min_le_right _ _
  have hm' : m≤2*h+2 := by
    have H₂ : 2≤2*h+2 := by omega
    have H₃ : E.donor+P≤2*h+2 := by dsimp [P]; omega
    exact Nat.le_trans hm (Nat.max_le.mpr ⟨H₂,H₃⟩)
  have hsmall : 4*(2*P+m+1)≤4096*(h+1) := by dsimp [P] at *; omega
  have hlarge := Nat.mul_le_mul_right (h+1) hC
  have hbnd : 4*n*(2*P+m+1)≤C*n*(h+1) := by
    have B := Nat.mul_le_mul_left n (Nat.le_trans hsmall hlarge)
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using B
  intro t
  rw [← cost_eq E t s (startRunning E) HM]
  exact Nat.le_trans (K t) (Nat.mul_le_mul_right _ hbnd)

/-- Same-word transaction for the final protected slot. There is no
following active slot, so its entry cap can stay frozen throughout. -/
def protected_transaction {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    {C h : Nat} (E : Entry initial g) (w : Word n)
    (H : IIDExpectedHittingTimeAtMost pushNext
      (fun r : Running initial g => r.q.terminal=true) (startRunning E) (C*n*(h+1))) :
    Transaction C w h where
  hit u := (runMarks pushNext (startRunning E) u).q.terminal=true
  span _ := h
  nom _ := E.supplier
  startSpan := Nat.le_refl _
  localStep := fun _ _ _ => Nat.le_add_right _ _
  mean := by
    intro t
    let f := runMarks pushNext (startRunning E)
    have Hstep (u : Word n) (e : Fin n) : f (wordNext u e)=pushNext (f u) e := by
      simp [f,wordNext,runMarks_append,runMarks]
    have HC (i : Nat) (u : Word n) :
        iidHitCost wordNext (fun u => (f u).q.terminal=true) i u =
        iidHitCost pushNext (fun r : Running initial g => r.q.terminal=true) i (f u) := by
      classical
      induction i generalizing u with
      | zero => simp [iidHitCost]
      | succ i ih =>
        by_cases h : (f u).q.terminal=true
        · rw [iidHitCost_of_target _ (fun u => (f u).q.terminal=true) _ h,
              iidHitCost_of_target _ (fun r : Running initial g => r.q.terminal=true) _ h]
        · rw [iidHitCost, if_neg h, iidHitCost, if_neg h]
          congr 1
          apply congrArg TaggedTail.sumEdge
          funext e
          rw [ih, Hstep]
    exact Nat.le_trans (Nat.le_of_eq (HC t [])) (H t)

/-- Eliminate the nonterminal continuation of a genuine protected exit. -/
theorem protected_phase {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    {C h : Nat} (E : Entry initial g) (w : Word n) (done : Word n → Prop)
    (H : IIDExpectedHittingTimeAtMost pushNext
      (fun r : Running initial g => r.q.terminal=true) (startRunning E) (C*n*(h+1)))
    (hafter : ∀ u : Word n, (runMarks pushNext (startRunning E) u).q.terminal=true → done (w++u)) :
    WindowClock.WindowStages wordNext done C 1 w h := by
  apply (protected_transaction E w H).phase
  intro u hx hnd
  exact (hnd (hafter u hx.2)).elim

/-- Exact joined replay after the once-only named latch. -/
theorem joined_replay_from_protected {α : Type} {p c n : Nat}
    {initial : Config p c n} {g : List (Fin n)}
    (front : α → Fin n → Sum α (Entry initial g)) (r : Running initial g)
    (u : Word n) :
    runMarks (joinedNext front) (.inr r) u = .inr (runMarks pushNext r u) := by
  induction u generalizing r with
  | nil => rfl
  | cons e u ih => exact ih (pushNext r e)

theorem joined_hit_after_latch {α : Type} {p c n : Nat}
    {initial : Config p c n} {g : List (Fin n)}
    (front : α → Fin n → Sum α (Entry initial g)) (x : α)
    (E : Entry initial g) (w u : Word n)
    (hlatch : runMarks (joinedNext front) (.inl x) w=.inr (startRunning E)) :
    runMarks (joinedNext front) (.inl x) (w++u) =
      .inr (runMarks pushNext (startRunning E) u) := by
  rw [runMarks_append,hlatch,joined_replay_from_protected]

end L4.WindowProtectedSlot
