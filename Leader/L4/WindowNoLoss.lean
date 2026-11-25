import Leader.L4.WindowFrontDone

namespace L4.WindowNoLoss
set_option maxHeartbeats 2000000
open SevenTagCharge WindowOwnership WindowFrontDone WindowLatch WindowProtectedOuter

/-- Every actual selected loss is consumed on its own raw edge.
No geometry condition, stage readiness, or freshness test postpones it. -/
theorem selected_done {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} (q : Cursor (Front x g) x g)
    (e a : Fin n) (h : WindowLocal.selectedGroupLoss g (project Front.ledger q) e=some a) :
    done (next hp hc hn q e) := by
  cases q with
  | inl s =>
    change WindowLocal.selectedGroupLoss g s.ledger e=some a at h
    have H (cert : List (Fin n)) (t : Option (Fin n)) :
        WindowLocal.route g cert t s.ledger e=.reward a := by
      unfold WindowLocal.route
      rw [h]
    cases m : s.mode with
    | reward b hb =>
      simp [next,joinedNext,front,WindowOwnership.decide,m,done]
    | entry A =>
      have route : WindowA0Route.routeTwo g A.first A.second s.ledger e=.reward a := by
        simp [WindowA0Route.routeTwo,H]
      simp only [next,joinedNext,front,WindowOwnership.decide,m]
      split
      · rename_i t ht hd
        split at hd
        · rename_i hr; rw [route] at hr; contradiction
        · injection hd with hT
          subst t
          trivial
        · rename_i _ _ hr; rw [route] at hr; contradiction
        · rename_i _ _ hr; rw [route] at hr; contradiction
      · rename_i k hd
        split at hd
        · rename_i hr; rw [route] at hr; contradiction
        · cases hd
        · rename_i _ _ hr; rw [route] at hr; contradiction
        · rename_i _ _ hr; rw [route] at hr; contradiction
    | owned P =>
      have route := H P.cert P.target
      simp only [next,joinedNext,front,WindowOwnership.decide,m]
      split
      · rename_i t ht hd
        split at hd
        · rename_i hr; rw [route] at hr; contradiction
        · injection hd with hT
          subst t
          trivial
        · rename_i _ _ hr; rw [route] at hr; contradiction
        · rename_i _ _ hr; rw [route] at hr; contradiction
      · rename_i k hd
        split at hd
        · rename_i hr; rw [route] at hr; contradiction
        · cases hd
        · rename_i _ _ hr; rw [route] at hr; contradiction
        · rename_i _ _ hr; rw [route] at hr; contradiction
  | inr r =>
    change WindowLocal.selectedGroupLoss g r.q.ledger e=some a at h
    change (pushNext r e).q.terminal=true
    have route : WindowLocal.route g (pushNext.someSupplier r.start) (some r.start.victim)
        r.q.ledger e=.reward a := by
      unfold WindowLocal.route
      rw [h]
    unfold pushNext WindowProtectedMass.next
    dsimp only
    split
    · rfl
    · rw [route]

theorem rewarded_done_step {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} (q : Cursor (Front x g) x g)
    (e : Fin n) (old : WindowLocal.rewarded g (project Front.ledger q) → done q)
    (r : WindowLocal.rewarded g (project Front.ledger (next hp hc hn q e))) :
    done (next hp hc hn q e) := by
  change WindowLocal.rewarded g (project Front.ledger
    (joinedNext (front hn (WindowOwnership.decide hp hc hn)) q e)) at r
  rw [step_projects] at r
  rcases (WindowLocal.rewarded_step_iff g (project Front.ledger q) e).mp r with h|⟨a,h⟩
  · exact done_sticky hp hc hn q e (old h)
  · exact selected_done hp hc hn q e a h

theorem rewarded_done_replay {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} {g : List (Fin n)} (q : Cursor (Front x g) x g)
    (w : List (Fin n)) (base : WindowLocal.rewarded g (project Front.ledger q) → done q) :
    WindowLocal.rewarded g (project Front.ledger (replay (next hp hc hn) q w)) →
      done (replay (next hp hc hn) q w) := by
  induction w generalizing q with
  | nil => exact base
  | cons e w ih => exact ih _ (rewarded_done_step hp hc hn q e base)

theorem physical_loss_done {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (hx : QuietEntrance x) {g : List (Fin n)} (A : EntryScope g)
    (w : List (Fin n)) (h : WindowFiveStages.LedgerReward x g w) :
    done (fold hp hc hn hx A w) := by
  have step := rewarded_done_replay hp hc hn (.inl (Front.initial x hx A)) w
    (by rintro ⟨_,hA,_⟩; cases hA)
  apply step
  change WindowLocal.rewarded g (project Front.ledger (fold hp hc hn hx A w))
  rw [fold_ledger]
  obtain ⟨a,ha,hm⟩ := List.any_eq_true.mp h
  exact ⟨a,ha,by simpa using hm⟩

theorem not_done_no_loss {p c n} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    {x : Config p c n} (hx : QuietEntrance x) {g : List (Fin n)} (A : EntryScope g)
    (w : List (Fin n)) (h : ¬done (fold hp hc hn hx A w)) :
    hit (observe (initial x) w).losses g=false :=
  Bool.eq_false_iff.mpr (fun hr => h (physical_loss_done hp hc hn hx A w hr))

end L4.WindowNoLoss
