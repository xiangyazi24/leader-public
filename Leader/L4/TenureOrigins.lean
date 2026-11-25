import Leader.L4.TaggedTenures
import Leader.L4.TaggedGeometry

namespace L4.TenureOrigins

/-- Exactly the N2 condition when the input responder is a leader. The
initiator may fire afresh; the responder can dummy-fire and unshield, or
live-fire and shield, before impact. -/
def nativeKill {p c1 : Nat} (u v : Site p c1) : Prop :=
  v.leader = true ∧ (fireInitiator u).bullet = .live ∧
    (fireResponder v).shield = false

private theorem native_leader_after_impact {p c1 : Nat} (u v : Site p c1) :
    (native u v).2.leader =
      (impact (fireInitiator u) (fireResponder v)).2.leader := by
  unfold native
  generalize impact (fireInitiator u) (fireResponder v) = uv
  obtain ⟨a,b⟩ := uv
  simp only
  unfold followerBullet
  split
  · split <;> rfl
  · rfl

private theorem fireResponder_leader {p c1 : Nat} (v : Site p c1) :
    (fireResponder v).leader = v.leader := by
  unfold fireResponder
  split
  · cases v.signal <;> rfl
  · rfl

private theorem fireInitiator_materialize_bullet {p c1 : Nat} (u v : Site p c1) :
    (fireInitiator (materialize u v)).bullet = (fireInitiator u).bullet := by
  unfold materialize
  split
  · by_cases hc : (u.leader && !(u.signal == .zero)) = true
    · simp only [fireInitiator, hc, if_true]
    · simp only [fireInitiator, hc, Bool.false_eq_true, if_false]
  · rfl

/-- On an old responder leader, a post-native loss is exactly the literal
live kill. Materialization changes only the incoming marker, not its cause. -/
theorem native_loses_leader_iff {p c1 : Nat} (u v : Site p c1)
    (hl : v.leader = true) :
    (native (materialize u v) v).2.leader = false ↔ nativeKill u v := by
  rw [native_leader_after_impact]
  have hr : (fireResponder v).leader = true := (fireResponder_leader v).trans hl
  have hh (a b : Site p c1) (hbl : b.leader = true) :
      (impact a b).2.leader = false ↔ a.bullet = .live ∧ b.shield = false := by
    cases hb : a.bullet <;> cases hs : b.shield <;>
      simp [impact, hb, hbl, hs,
        show (Bullet.none == Bullet.none) = true by rfl,
        show (Bullet.dummy == Bullet.none) = false by rfl,
        show (Bullet.live == Bullet.none) = false by rfl,
        show (Bullet.dummy == Bullet.live) = false by rfl,
        show (Bullet.live == Bullet.live) = true by rfl]
  rw [hh _ _ hr, fireInitiator_materialize_bullet]
  simp [nativeKill, hl]

private theorem initialSource_noPatrolFire {Q : Nat}
    (root ghost leader : Bool) (l r : Rail) :
    (patrol (Q := Q) root ghost leader .off l r).fire = false := by
  cases root <;> cases ghost <;> cases leader <;> cases l <;> cases r <;> rfl

private theorem prefix_source_responder {p c1 : Nat} (u v : Site p c1) :
    (stepPrefix u v).2.source = v.source := by
  unfold stepPrefix native
  generalize hgen : impact (fireInitiator (materialize u v)) (fireResponder v) = a
  obtain ⟨au,av⟩ := a
  have hp (x y : Site p c1) :
      (payment x y).2.source = y.source := by
    unfold payment
    split
    · rfl
    split
    · rfl
    split <;> rfl
  have hf (g : Bool) (x y : Site p c1) :
      (followerBullet g x y).2.source = y.source := by
    unfold followerBullet
    split
    · split <;> rfl
    · rfl
  have hv : av.source = v.source := by
    have he (x y : Site p c1) : (impact x y).2.source = y.source := by
      unfold impact
      split
      · split <;> rfl
      · rfl
    have hr : (fireResponder v).source = v.source := by
      unfold fireResponder
      split
      · cases v.signal <;> rfl
      · rfl
    exact (congrArg (fun z => z.2.source) hgen).symm.trans
      ((he _ _).trans hr)
  exact (hp _ _).trans ((hf _ _ _).trans hv)

private theorem prefix_leader_responder {p c1 : Nat} (u v : Site p c1) :
    (stepPrefix u v).2.leader = (native (materialize u v) v).2.leader := by
  unfold stepPrefix
  generalize native (materialize u v) v = q
  obtain ⟨a,b⟩ := q
  dsimp only
  unfold payment
  split
  · rfl
  split
  · rfl
  split <;> rfl

/-- On a covered old leader the source controller is OFF. It cannot
re-birth during its own native killing mark. Hence the full leader loss
on its incoming edge is exactly the native kill. -/
theorem covered_leader_loss_iff {p c1 : Nat} (u v : Site p c1)
    (hl : v.leader = true) (hoff : v.source = .off) :
    (pairStep u v).2.leader = false ↔ nativeKill u v := by
  rw [← native_loses_leader_iff u v hl]
  rw [← prefix_leader_responder]
  have hs : (stepPrefix u v).2.source = .off :=
    (prefix_source_responder u v).trans hoff
  unfold pairStep
  generalize stepPrefix u v = q at hs ⊢
  obtain ⟨a,b⟩ := q
  dsimp only at *
  simp [finishBirth, patrolWrite, hs, initialSource_noPatrolFire]

/-- If a killing bullet already has an original tag at the initiator, then
its tag is consumed on the selected edge, irrespective of timer results.
The stronger assertion that each nonfinal killer has such an original
tag belongs to the global protected-trail/first-barrier proof. -/
theorem kill_ends_initiator_tag {p c1 : Nat} {u v : Site p c1}
    (hk : nativeKill u v) : tagStep u v true false = (false,false) := by
  rw [tagStep_outgoing]
  simp [tagTransfer, hk.1]

/-- One old-original observer occupying the selected initiator is extinguished
by a kill on this mark, and can never be recruited for a later kill. -/
theorem original_kill_no_reuse {p c1 n : Nat}
    (s : TaggedTrace.Obs p c1 n) (e : Fin n)
    (hc : s.carrier = some e)
    (hk : nativeKill (s.config e) (s.config (rightNeighbor e)))
    (w : List (Fin n)) :
    TaggedTrace.ended (TaggedTrace.track (TaggedTrace.advance s e) w) := by
  have hs : TaggedTrace.ended (TaggedTrace.advance s e) := by
    unfold TaggedTrace.ended
    simp [TaggedTrace.advance, TaggedTrace.carrierStep, hc, tagTransfer, hk.1]
  exact TaggedTrace.ended_run (TaggedTrace.advance s e) w hs

/-- No old initiator firing means the moving live byte used by N2 really
is the pre-mark bullet, not a new shot replacing an old tag. -/
theorem killing_bullet_preexisting_if_no_refire {p c1 : Nat} {u v : Site p c1}
    (hk : nativeKill u v) (ho : tagOverwrite u = false) :
    u.bullet = .live := by
  have hf : (u.leader && !(u.signal == .zero)) = false := by
    simpa [tagOverwrite] using ho
  have hb := hk.2.1
  simpa [fireInitiator, hf] using hb

/-- On an actual selected ring mark, any old leader which disappears at
the responder was killed by the exact N2 guard. The selected distinctness
premise is automatic on the paper's n >= 4 rings. -/
theorem covered_ring_leader_loss_iff {p c1 n : Nat}
    (x : Config p c1 n) (e : Fin n) (hneq : rightNeighbor e ≠ e)
    (hc : COV x) (hl : (x (rightNeighbor e)).leader = true) :
    (step x e (rightNeighbor e)).leader = false ↔
      nativeKill (x e) (x (rightNeighbor e)) := by
  have ho : (x (rightNeighbor e)).source = .off := by
    by_cases h : (x (rightNeighbor e)).source = .off
    · exact h
    · have hf := (hc e h).1
      rw [hl] at hf
      contradiction
  simpa [step, hneq] using covered_leader_loss_iff
    (x e) (x (rightNeighbor e)) hl ho

/-- A first-barrier kill during which the observed carrier survives must
use an already present, non-refired live bullet. The kill donor is strictly
inside the root-free gap: equality with the tag donor would consume the
observed carrier. 'Already present' here means in the pre-mark state,
not necessarily at the original cover cut. -/
theorem surviving_firstBarrier_kill_uses_ordinary_donor {p c1 n d : Nat}
    (s : TaggedTrace.Obs p c1 n) (b : Fin n) (w : Option (Fin n))
    (hc : MCOV s.config) (hb : s.carrier = some b)
    (hf : FirstMark s.config b d)
    (hkill : nativeKill (s.config (liftedSite b d))
      (s.config (rightNeighbor (liftedSite b d))))
    (hsurv : (TaggedTrace.advance s (liftedSite b d)).carrier = w)
    (hw : w ≠ none) :
    (s.config (liftedSite b d)).leader = false ∧
      (s.config (liftedSite b d)).bullet = .live := by
  have hd : d ≠ 0 := by
    intro hz
    subst d
    rw [liftedSite_zero] at hkill hsurv
    have hEnd := original_kill_no_reuse s b hb hkill []
    change (TaggedTrace.advance s b).carrier = none at hEnd
    exact hw (hsurv.symm.trans hEnd)
  have hmark : (s.config (liftedSite b (d-1))).mark ≠ true :=
    hf.before (d-1) (by omega)
  have hh : rightNeighbor (liftedSite b (d-1)) = liftedSite b d := by
    rw [← liftedSite_succ]
    congr 1
    omega
  have hl : (s.config (liftedSite b d)).leader = false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    apply hmark
    apply hc _ (Or.inl ?_)
    rwa [hh]
  exact ⟨hl, killing_bullet_preexisting_if_no_refire hkill (by simp [tagOverwrite,hl])⟩

/-- If the first mark moves strictly closer to a stationary carrier on
one covered edge, it must become the carrier's very own outgoing mark.
No positive interior offset can suddenly acquire the first mark. -/
theorem earlier_firstMark_is_adjacent {p c1 n d d' : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (hc : MCOV x) (b e : Fin n)
    (h : FirstMark x b d) (h' : FirstMark (step x e) b d') (hlt : d' < d) :
    d' = 0 := by
  have hold : (x (liftedSite b d')).mark ≠ true := h.before d' hlt
  have hemark := h'.marked
  rw [covered_step_mark hn x hc] at hemark
  by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
  · have htarget : liftedSite b d' = rightNeighbor e := by
      by_cases ht : liftedSite b d' = rightNeighbor e
      · exact ht
      · by_cases hdonor : liftedSite b d' = e
        · simp [hp,hdonor] at hemark
        · simp [hp,hdonor,ht,hold] at hemark
    have hsource := covered_pair_marks (x e) (x (rightNeighbor e)) (hc e)
    simp only [hp, if_true] at hsource
    by_cases hz : d' = 0
    · exact hz
    exfalso
    have hsucc : rightNeighbor (liftedSite b (d'-1)) = liftedSite b d' := by
      rw [← liftedSite_succ]
      congr 1
      omega
    have hsite : liftedSite b (d'-1) = e := by
      apply Fin.ext
      have hEq := congrArg Fin.val (hsucc.trans htarget)
      change ((liftedSite b (d'-1)).val+1)%n = (e.val+1)%n at hEq
      have ha := (liftedSite b (d'-1)).isLt
      have hb := e.isLt
      by_cases hla : (liftedSite b (d'-1)).val+1 < n <;> by_cases hlb : e.val+1 < n
      · rw [Nat.mod_eq_of_lt hla, Nat.mod_eq_of_lt hlb] at hEq
        omega
      · have hbe : e.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt hla,hbe,Nat.mod_self] at hEq
        omega
      · have hae : (liftedSite b (d'-1)).val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt hlb,hae,Nat.mod_self] at hEq
        omega
      · omega
    have hbmark : (x (liftedSite b (d'-1))).mark = true := by rw [hsite]; exact hsource.1
    exact h.before (d'-1) (by omega) hbmark
  · simp [hp,hold] at hemark

/-- A strict preemption of a stationary observed carrier yields the actual
adjacent pinned ghost certificate used by the no-more-tenures theorem. -/
theorem earlier_firstMark_pinned_ghost {p c1 n d d' : Nat} (hn : 4 ≤ n)
    (x : Config p c1 n) (hc : MCOV x) (b e : Fin n)
    (h : FirstMark x b d) (h' : FirstMark (step x e) b d') (hlt : d' < d) :
    TaggedTenures.AdjacentGhost (step x e) b := by
  have hz := earlier_firstMark_is_adjacent hn x hc b e h h' hlt
  subst d'
  have hm := h'.marked
  rw [liftedSite_zero] at hm
  have hold := h.before 0 hlt
  rw [liftedSite_zero] at hold
  have hgeom := hm
  rw [covered_step_mark hn x hc] at hgeom
  have htarget : b = rightNeighbor e := by
    by_cases hp : geometricPay (x e) (x (rightNeighbor e)) = true
    · by_cases ht : b = rightNeighbor e
      · exact ht
      · by_cases he : b = e <;> simp [hp,ht,he,hold] at hgeom
    · simp [hp,hold] at hgeom
  have hs : rightNeighbor b ≠ b := by
    intro hall
    have hv := congrArg Fin.val hall
    change (b.val+1)%n = b.val at hv
    have hbl := b.isLt
    by_cases hb : b.val+1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbe : b.val+1 = n := by omega
      rw [hbe, Nat.mod_self] at hv
      omega
  have holdL : (x (rightNeighbor b)).leader = false := by
    apply Bool.eq_false_iff.mpr
    exact fun he => hold (hc b (Or.inl he))
  have hne : rightNeighbor b ≠ rightNeighbor e := by
    rw [← htarget]; exact hs
  refine ⟨hm, ?_⟩
  by_cases he : rightNeighbor b = e
  · rw [he] at holdL ⊢
    simpa [step, (pair_geometric_fields (x e) (x (rightNeighbor e))).2.1]
      using holdL
  · simp [step, he, hne, holdL]

end L4.TenureOrigins
