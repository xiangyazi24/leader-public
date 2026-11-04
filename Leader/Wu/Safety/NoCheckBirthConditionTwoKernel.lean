import Leader.Wu.Safety.NoCheckBirthConditionTwoGeometry

/-!
# Local Algorithm-15 contracts for corrected condition 2

These contracts isolate the live-bullet writers and the five physical fields
used by `isPeacefulBullet` in the no-collision Algorithm-15 repair.  They expose
origins, label frames, signal-zero preservation, shield frames, and the final
responder signal clamp without unfolding the complete repaired protocol.
-/

namespace PPLLNoCheckBirthConditionTwoKernel
open PPLL PPLLRepair PPLLNoCheckBirthLeaderFrames

private theorem fire_left_bullet (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.bullet =
      if l.leader = true ∧ l.signal_B = ⟨1, by omega⟩ then
        ⟨2, by omega⟩ else l.bullet := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  split <;> rfl

private theorem fire_right_bullet (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).2.bullet =
      if r.leader = true ∧ r.signal_B = ⟨1, by omega⟩ then
        ⟨1, by omega⟩ else r.bullet := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  split <;> rfl

private theorem fire_left_signal_zero_of_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hzero : l.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).1.signal_B =
      ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  by_cases hfire : l.leader = true ∧ l.signal_B = ⟨1, by omega⟩
  · rw [if_pos hfire]
  · rw [if_neg hfire]
    exact hzero

private theorem fire_right_signal_zero_of_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hzero : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).2.signal_B =
      ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  by_cases hfire : r.leader = true ∧ r.signal_B = ⟨1, by omega⟩
  · rw [if_pos hfire]
  · rw [if_neg hfire]
    exact hzero

private theorem fire_left_shield_of_signal_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hzero : l.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).1.shield = l.shield := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  by_cases hfire : l.leader = true ∧ l.signal_B = ⟨1, by omega⟩
  · have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hzero.symm.trans hfire.2
    simp at hbad
  · rw [if_neg hfire]

private theorem fire_right_shield_of_signal_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hzero : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionFire hψ l r).2.shield = r.shield := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  by_cases hfire : r.leader = true ∧ r.signal_B = ⟨1, by omega⟩
  · have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hzero.symm.trans hfire.2
    simp at hbad
  · rw [if_neg hfire]

private theorem fire_left_label (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.label = l.label := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  split <;> rfl

private theorem fire_right_label (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).2.label = r.label := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  split <;> rfl

private theorem fire_left_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  split <;> rfl

private theorem move_left_bullet (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove next l r).1.bullet =
      if r.bullet.val > 0 ∧ l.leader = true then l.bullet
      else if r.bullet.val > 0 ∧ l.leader = false then
        if r.label = next then r.bullet else l.bullet
      else l.bullet := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1]
    split <;> rfl
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split <;> rfl
    · rw [if_neg h2]
      simp [h1, h2]

private theorem move_right_bullet (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove next l r).2.bullet =
      if r.bullet.val > 0 ∧ l.leader = true then
        if r.bullet = ⟨2, by omega⟩ ∧ l.shield = false then
          ⟨1, by omega⟩ else r.bullet
      else if r.bullet.val > 0 ∧ l.leader = false then
        ⟨0, by omega⟩
      else r.bullet := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1]
    split <;> rfl
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split <;> rfl
    · rw [if_neg h2]
      simp [h1, h2]

private theorem move_left_signal_zero_of_zero
    (next : Fin ψ) (l r : AgentState ψ)
    (hzero : l.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollisionMove next l r).1.signal_B =
      ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1]
    split <;> exact hzero
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split
      · rfl
      · exact hzero
    · rw [if_neg h2]
      exact hzero

private theorem move_left_signal_zero_of_live_follower
    (next : Fin ψ) (l r : AgentState ψ)
    (hb : r.bullet = ⟨2, by omega⟩)
    (hl : l.leader = false) (hlabel : r.label = next) :
    (eliminateLeadersNoCollisionMove next l r).1.signal_B =
      ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollisionMove
  have hbpos : r.bullet.val > 0 := by
    rw [hb]
    decide
  rw [if_neg (by simp [hl]), if_pos ⟨hbpos, hl⟩, if_pos hlabel]

private theorem move_right_signal (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove next l r).2.signal_B = r.signal_B := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1]
    split <;> rfl
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split <;> rfl
    · rw [if_neg h2]

private theorem move_left_leader_of_false
    (next : Fin ψ) (l r : AgentState ψ) (hl : l.leader = false) :
    (eliminateLeadersNoCollisionMove next l r).1.leader = false := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · have hbad := h1.2
    rw [hl] at hbad
    simp at hbad
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split <;> exact hl
    · rw [if_neg h2]
      exact hl

private theorem move_shields (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove next l r).1.shield = l.shield ∧
      (eliminateLeadersNoCollisionMove next l r).2.shield = r.shield := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1]
    split <;> exact ⟨rfl, rfl⟩
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split <;> exact ⟨rfl, rfl⟩
    · rw [if_neg h2]
      exact ⟨rfl, rfl⟩

private theorem move_labels (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove next l r).1.label = l.label ∧
      (eliminateLeadersNoCollisionMove next l r).2.label = r.label := by
  unfold eliminateLeadersNoCollisionMove
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1]
    split <;> exact ⟨rfl, rfl⟩
  · rw [if_neg h1]
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2]
      split <;> exact ⟨rfl, rfl⟩
    · rw [if_neg h2]
      exact ⟨rfl, rfl⟩

private theorem signal_right_zero_of_zeros_follower
    (next : Fin ψ) (l r : AgentState ψ)
    (hl : l.signal_B = ⟨0, by omega⟩)
    (hr : r.signal_B = ⟨0, by omega⟩)
    (hlf : l.leader = false) :
    (eliminateLeadersNoCollisionSignal next l r).2.signal_B =
      ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  by_cases houter : r.label = next ∨ l.leader = true
  · rw [if_pos houter]
    by_cases hb : r.bullet = ⟨2, by omega⟩
    · rw [if_pos hb]
    · rw [if_neg hb]
      rw [hl, hr, hlf]
      rfl
  · rw [if_neg houter]
    exact hr

private theorem signal_shields (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal next l r).1.shield = l.shield ∧
      (eliminateLeadersNoCollisionSignal next l r).2.shield = r.shield := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  by_cases houter : r.label = next ∨ l.leader = true
  · rw [if_pos houter]
    split <;> exact ⟨rfl, rfl⟩
  · rw [if_neg houter]
    exact ⟨rfl, rfl⟩

private theorem signal_labels (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal next l r).1.label = l.label ∧
      (eliminateLeadersNoCollisionSignal next l r).2.label = r.label := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  by_cases houter : r.label = next ∨ l.leader = true
  · rw [if_pos houter]
    split <;> exact ⟨rfl, rfl⟩
  · rw [if_neg houter]
    exact ⟨rfl, rfl⟩

private theorem signal_left_signal (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal next l r).1.signal_B = l.signal_B := by
  rfl

/-- The initiator-leader fire branch creates a shielded live bullet and clears
its own absence signal. -/
theorem noCollision_left_fire_fields
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).1.shield = true ∧
      (eliminateLeadersNoCollision hψ l r).1.signal_B =
        ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollision
  dsimp only
  repeat split <;> simp_all

/-- A leader that fires its own bullet becomes shielded before collision
processing, so the same Algorithm-15 call cannot eliminate it. -/
theorem noCollision_left_fire_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).1.leader = true := by
  unfold eliminateLeadersNoCollision
  dsimp only
  repeat split <;> simp_all

/-- Exact certificate for the only Algorithm-15 event that kills an initiating
leader against a follower responder.  The source leader is unshielded with no
pending fire signal, the responder carries a live bullet, and the collision
consumes that live bullet by replacing it with the dummy value `1`. -/
structure InitiatorLeaderLiveHit
    (l r : AgentState ψ) (out : AgentState ψ × AgentState ψ) : Prop where
  sourceSignalZero : l.signal_B = ⟨0, by omega⟩
  sourceUnshielded : l.shield = false
  responderLive : r.bullet = ⟨2, by omega⟩
  outputInitiatorFollower : out.1.leader = false
  outputInitiatorBullet : out.1.bullet = l.bullet
  outputResponderFollower : out.2.leader = false
  outputResponderDummy : out.2.bullet = ⟨1, by omega⟩

/-- An initiating leader facing a follower either survives Algorithm 15, or
the exact live-hit certificate records its death and the strict `2 -> 1`
degradation of the killing responder bullet. -/
theorem noCollision_initiator_leader_survives_or_live_hit
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false) :
    let out := eliminateLeadersNoCollision hψ l r
    (out.1.leader = true ∧ out.2.leader = false) ∨
      InitiatorLeaderLiveHit l r out := by
  have hsignal : l.signal_B = ⟨0, by omega⟩ ∨
      l.signal_B = ⟨1, by omega⟩ := by
    rcases l.signal_B with ⟨v, hv⟩
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl <;> simp
  rcases hsignal with hsignalZero | hsignalOne
  · cases hshield : l.shield
    · by_cases hbullet : r.bullet = ⟨2, by omega⟩
      · right
        refine {
          sourceSignalZero := hsignalZero
          sourceUnshielded := hshield
          responderLive := hbullet
          outputInitiatorFollower := ?_
          outputInitiatorBullet := ?_
          outputResponderFollower := ?_
          outputResponderDummy := ?_ }
        all_goals
          simp [eliminateLeadersNoCollision, hl, hr,
            hsignalZero, hshield, hbullet]
      · left
        exact ⟨eliminateLeadersNoCollision_initiator_survives
              hψ l r hl (by
                intro hkill
                exact hbullet hkill.1),
          (eliminateLeadersNoCollision_responder_leader_eq
              hψ l r).trans hr⟩
    · left
      exact ⟨eliminateLeadersNoCollision_initiator_survives
            hψ l r hl (by
              intro hkill
              rw [hshield] at hkill
              simp at hkill),
        (eliminateLeadersNoCollision_responder_leader_eq
            hψ l r).trans hr⟩
  · left
    exact ⟨noCollision_left_fire_leader hψ l r hl hsignalOne,
      (eliminateLeadersNoCollision_responder_leader_eq
          hψ l r).trans hr⟩

/-- Extending the final signal guard by the responder-leader sink changes
neither branch of the initiating-leader dichotomy when the responder starts
as a follower. -/
theorem noCollisionLeaderSink_initiator_leader_survives_or_live_hit
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false) :
    let out := eliminateLeadersNoCollisionLeaderSink hψ l r
    (out.1.leader = true ∧ out.2.leader = false) ∨
      InitiatorLeaderLiveHit l r out := by
  rw [eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
    hψ l r hr]
  exact noCollision_initiator_leader_survives_or_live_hit hψ l r hl hr

/-- Indicator mass of a physical live bullet. -/
def bulletTwoMass (u : AgentState ψ) : Nat :=
  if u.bullet = (⟨2, by omega⟩ : Fin 3) then 1 else 0

/-- Live-bullet mass on one oriented pair. -/
def bulletTwoPairMass (l r : AgentState ψ) : Nat :=
  bulletTwoMass l + bulletTwoMass r

/-- Live-bullet mass depends only on the bullet field. -/
theorem bulletTwoMass_eq_of_bullet_eq
    {u v : AgentState ψ} (h : u.bullet = v.bullet) :
    bulletTwoMass u = bulletTwoMass v := by
  unfold bulletTwoMass
  rw [h]

/-- Pair live-bullet mass depends only on the two bullet fields. -/
theorem bulletTwoPairMass_eq_of_bullets_eq
    {l r l' r' : AgentState ψ}
    (hl : l.bullet = l'.bullet) (hr : r.bullet = r'.bullet) :
    bulletTwoPairMass l r = bulletTwoPairMass l' r' := by
  unfold bulletTwoPairMass bulletTwoMass
  rw [hl, hr]

/-- On a stable successor edge with an idle responder, either an initiator
leader or an incoming absence signal writes `signal_B = 1` at the responder.
The explicit responder-signal-zero premise excludes its own fire branch. -/
theorem noCollision_right_signal_one_of_aligned_source
    (hψ : ψ > 0) (l r : AgentState ψ)
    (halign :
      r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hrSignal : r.signal_B = ⟨0, by omega⟩)
    (hsource : l.leader = true ∨ l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨1, by omega⟩ := by
  let next : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.signal_B = _
  have hfireR : ¬(r.leader = true ∧ r.signal_B = ⟨1, by omega⟩) := by
    intro h
    have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hrSignal.symm.trans h.2
    simp at hbad
  have hqfRBullet : qf.2.bullet = ⟨0, by omega⟩ := by
    have h := fire_right_bullet hψ l r
    rw [if_neg hfireR, hrBullet] at h
    exact h
  have hqfRLabel : qf.2.label = next := by
    exact (fire_right_label hψ l r).trans halign
  have hmove : qm = qf := by
    unfold qm
    unfold eliminateLeadersNoCollisionMove
    simp [hqfRBullet]
  rw [hmove]
  have hqfSource : qf.1.leader = true ∨
      qf.1.signal_B = ⟨1, by omega⟩ := by
    rcases hsource with hleader | hsignal
    · exact .inl ((fire_left_leader hψ l r).trans hleader)
    · by_cases hleader : l.leader = true
      · exact .inl ((fire_left_leader hψ l r).trans hleader)
      · right
        unfold qf eliminateLeadersNoCollisionFire
        simp [hleader, hsignal]
  exact eliminateLeadersNoCollisionSignal_right_one next qf.1 qf.2
    hqfRLabel hqfRBullet hqfSource

/-- On a stable successor edge, an initiator leader or incoming absence
signal writes one at any responder whose own leader-fire guard is disabled.
Unlike the older idle-responder interface, follower signals may be arbitrary. -/
theorem noCollision_right_signal_one_of_aligned_source_noFire
    (hψ : ψ > 0) (l r : AgentState ψ)
    (halign :
      r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hrFire : r.leader = false ∨ r.signal_B = ⟨0, by omega⟩)
    (hsource : l.leader = true ∨ l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨1, by omega⟩ := by
  let next : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.signal_B = _
  have hfireR : ¬(r.leader = true ∧ r.signal_B = ⟨1, by omega⟩) := by
    intro h
    rcases hrFire with hrFollower | hrSignal
    · have hbad : (false : Bool) = true := hrFollower.symm.trans h.1
      simp at hbad
    · have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
        hrSignal.symm.trans h.2
      simp at hbad
  have hqfRBullet : qf.2.bullet = ⟨0, by omega⟩ := by
    have h := fire_right_bullet hψ l r
    rw [if_neg hfireR, hrBullet] at h
    exact h
  have hqfRLabel : qf.2.label = next := by
    exact (fire_right_label hψ l r).trans halign
  have hmove : qm = qf := by
    unfold qm
    unfold eliminateLeadersNoCollisionMove
    simp [hqfRBullet]
  rw [hmove]
  have hqfSource : qf.1.leader = true ∨
      qf.1.signal_B = ⟨1, by omega⟩ := by
    rcases hsource with hleader | hsignal
    · exact .inl ((fire_left_leader hψ l r).trans hleader)
    · by_cases hleader : l.leader = true
      · exact .inl ((fire_left_leader hψ l r).trans hleader)
      · right
        unfold qf eliminateLeadersNoCollisionFire
        simp [hleader, hsignal]
  exact eliminateLeadersNoCollisionSignal_right_one next qf.1 qf.2
    hqfRLabel hqfRBullet hqfSource

/-- Before the terminal leader fire, zero bullets and the absence of an
initiator fire make Algorithm 15 a pure signal-propagation step on all other
`PeaceView` fields. -/
theorem noCollision_idle_propagation_frame
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hnoFire : l.leader = false ∨ l.signal_B = ⟨0, by omega⟩)
    (hlBullet : l.bullet = ⟨0, by omega⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hrSignal : r.signal_B = ⟨0, by omega⟩) :
    let q := eliminateLeadersNoCollision hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨0, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = l.signal_B := by
  let next : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change
    let q := eliminateLeadersNoCollisionSignal next qm.1 qm.2
    q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨0, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = l.signal_B
  have hfireL : ¬(l.leader = true ∧ l.signal_B = ⟨1, by omega⟩) := by
    intro h
    rcases hnoFire with hleader | hsignal <;> simp_all
  have hfireR : ¬(r.leader = true ∧ r.signal_B = ⟨1, by omega⟩) := by
    intro h
    have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hrSignal.symm.trans h.2
    simp at hbad
  have hqf : qf = (l, r) := by
    unfold qf eliminateLeadersNoCollisionFire
    dsimp only
    rw [if_neg hfireL, if_neg hfireR]
  have hrBulletVal : r.bullet.val = 0 := congrArg Fin.val hrBullet
  have hqm : qm = (l, r) := by
    unfold qm
    rw [hqf]
    unfold eliminateLeadersNoCollisionMove
    simp [hrBulletVal]
  rw [hqm]
  have hlabels := signal_labels next l r
  have hshields := signal_shields next l r
  have hleftSignal := signal_left_signal next l r
  have hleaderBullet :
      let q := eliminateLeadersNoCollisionSignal next l r
      q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
        q.1.bullet = l.bullet ∧ q.2.bullet = r.bullet := by
    unfold eliminateLeadersNoCollisionSignal
    dsimp only
    by_cases houter : r.label = next ∨ l.leader = true
    · rw [if_pos houter]
      by_cases hb : r.bullet = ⟨2, by omega⟩
      · rw [if_pos hb]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · rw [if_neg hb]
        exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [if_neg houter]
      exact ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨hleaderBullet.1, hleaderBullet.2.1,
    hlabels.1, hlabels.2, hshields.1, hshields.2,
    hleaderBullet.2.2.1.trans hlBullet,
    hleaderBullet.2.2.2.trans hrBullet, hleftSignal⟩

/-- A barrier whose initiator is a follower blocks an incoming absence signal.
With an idle responder this is an exact zero result, even when the initiator
already carries `signal_B = 1`.  This is the source behavior on the incomplete
group edge entering the unique leader. -/
theorem noCollision_right_signal_zero_of_barrier_follower
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hbarrier : isBarrier hψ l r)
    (hlFollower : l.leader = false)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hrSignal : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨0, by omega⟩ := by
  let next : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.signal_B = _
  have hfireL : ¬(l.leader = true ∧
      l.signal_B = ⟨1, by omega⟩) := by
    intro h
    have hbad : (false : Bool) = true := hlFollower.symm.trans h.1
    simp at hbad
  have hfireR : ¬(r.leader = true ∧
      r.signal_B = ⟨1, by omega⟩) := by
    intro h
    have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hrSignal.symm.trans h.2
    simp at hbad
  have hqf : qf = (l, r) := by
    unfold qf eliminateLeadersNoCollisionFire
    dsimp only
    rw [if_neg hfireL, if_neg hfireR]
  have hrBulletVal : r.bullet.val = 0 := congrArg Fin.val hrBullet
  have hqm : qm = (l, r) := by
    unfold qm
    rw [hqf]
    unfold eliminateLeadersNoCollisionMove
    simp [hrBulletVal]
  rw [hqm]
  have houter : ¬(r.label = next ∨ l.leader = true) := by
    intro h
    rcases h with halign | hleader
    · exact hbarrier halign
    · have hbad : (false : Bool) = true := hlFollower.symm.trans hleader
      simp at hbad
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  rw [if_neg houter]
  exact hrSignal

/-- A live responder bullet moved left by a follower writes zero at its new
initiator host. -/
theorem noCollision_left_signal_zero_of_moved_live
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hb : r.bullet = ⟨2, by omega⟩)
    (hl : l.leader = false)
    (hlabel : r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hrzero : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).1.signal_B =
      ⟨0, by omega⟩ := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).1.signal_B = _
  rw [signal_left_signal]
  have hfireR : ¬(r.leader = true ∧ r.signal_B = ⟨1, by omega⟩) := by
    intro h
    have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hrzero.symm.trans h.2
    simp at hbad
  have hqfRB := fire_right_bullet hψ l r
  have hqfLLeader := fire_left_leader hψ l r
  have hqfRLabel := fire_right_label hψ l r
  rw [hl] at hqfLLeader
  have hqfRB2 : qf.2.bullet = ⟨2, by omega⟩ := by
    rw [if_neg hfireR, hb] at hqfRB
    exact hqfRB
  have hqfRLabelNext : qf.2.label = next := by
    rw [hqfRLabel, hlabel]
  exact move_left_signal_zero_of_live_follower
    next qf.1 qf.2 hqfRB2 hqfLLeader hqfRLabelNext

/-- A live responder bullet moved left by a follower leaves a zero absence
signal at the vacated responder. -/
theorem noCollision_right_signal_zero_of_moved_live
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hb : r.bullet = ⟨2, by omega⟩)
    (hl : l.leader = false)
    (hlabel : r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hrzero : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨0, by omega⟩ := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.signal_B = _
  have hfireR : ¬(r.leader = true ∧ r.signal_B = ⟨1, by omega⟩) := by
    intro h
    have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
      hrzero.symm.trans h.2
    simp at hbad
  have hqfRB := fire_right_bullet hψ l r
  rw [if_neg hfireR, hb] at hqfRB
  have hqfRSignal := fire_right_signal_zero_of_zero hψ l r hrzero
  have hqfLLeader := fire_left_leader hψ l r
  rw [hl] at hqfLLeader
  have hqfRLabel := fire_right_label hψ l r
  have hqfLLabel := fire_left_label hψ l r
  have hmoveLabel : qf.2.label = next := by
    rw [hqfRLabel, hlabel]
  apply signal_right_zero_of_zeros_follower
  · apply move_left_signal_zero_of_live_follower next qf.1 qf.2
    · exact hqfRB
    · exact hqfLLeader
    · exact hmoveLabel
  · rw [move_right_signal]
    exact hqfRSignal
  · apply move_left_leader_of_false
    exact hqfLLeader

/-- Input zero at the initiator remains zero through the complete
no-collision Algorithm-15 kernel. -/
theorem noCollision_left_signal_zero_of_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hzero : l.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).1.signal_B =
      ⟨0, by omega⟩ := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).1.signal_B = _
  rw [signal_left_signal]
  apply move_left_signal_zero_of_zero
  exact fire_left_signal_zero_of_zero hψ l r hzero

/-- Every Algorithm-15 interaction initiated by a leader clears the
initiator's absence signal.  A zero input is framed; a one input takes the
fire branch, which clears it. -/
theorem noCollision_left_signal_zero_of_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true) :
    (eliminateLeadersNoCollision hψ l r).1.signal_B =
      ⟨0, by omega⟩ := by
  have hval : l.signal_B.val = 0 ∨ l.signal_B.val = 1 := by
    omega
  rcases hval with hval | hval
  · have hzero : l.signal_B = ⟨0, by omega⟩ := Fin.ext hval
    exact noCollision_left_signal_zero_of_zero hψ l r hzero
  · have hone : l.signal_B = ⟨1, by omega⟩ := Fin.ext hval
    exact (noCollision_left_fire_fields hψ l r hlLeader hone).2

/-- The responder-leader signal sink preserves the leader-source initiator
signal clearing contract. -/
theorem noCollisionLeaderSink_left_signal_zero_of_leader
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true) :
    (eliminateLeadersNoCollisionLeaderSink hψ l r).1.signal_B =
      ⟨0, by omega⟩ := by
  rw [eliminateLeadersNoCollisionLeaderSink_left_signal_eq]
  exact noCollision_left_signal_zero_of_leader hψ l r hlLeader

/-- If both endpoint absence signals are zero and the initiator is a follower,
the responder remains zero after the complete no-collision kernel. -/
theorem noCollision_right_signal_zero_of_zeros_follower
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.signal_B = ⟨0, by omega⟩)
    (hr : r.signal_B = ⟨0, by omega⟩)
    (hlf : l.leader = false) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨0, by omega⟩ := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.signal_B = _
  apply signal_right_zero_of_zeros_follower
  · apply move_left_signal_zero_of_zero
    exact fire_left_signal_zero_of_zero hψ l r hl
  · rw [move_right_signal]
    exact fire_right_signal_zero_of_zero hψ l r hr
  · apply move_left_leader_of_false
    rw [fire_left_leader]
    exact hlf

/-- A zero initiator absence signal prevents Algorithm 15 from changing its
shield. -/
theorem noCollision_left_shield_of_signal_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).1.shield = l.shield := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  have hf := fire_left_shield_of_signal_zero hψ l r hl
  have hm := move_shields next qf.1 qf.2
  have hs := signal_shields next qm.1 qm.2
  exact hs.1.trans (hm.1.trans hf)

/-- A zero responder absence signal prevents Algorithm 15 from changing its
shield. -/
theorem noCollision_right_shield_of_signal_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.shield = r.shield := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  have hf := fire_right_shield_of_signal_zero hψ l r hr
  have hm := move_shields next qf.1 qf.2
  have hs := signal_shields next qm.1 qm.2
  exact hs.2.trans (hm.2.trans hf)

/-- A zero absence signal prevents the fire stage from changing that endpoint's
shield; movement and the final signal stage frame shields. -/
theorem noCollision_shields_of_signal_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.signal_B = ⟨0, by omega⟩)
    (hr : r.signal_B = ⟨0, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).1.shield = l.shield ∧
      (eliminateLeadersNoCollision hψ l r).2.shield = r.shield := by
  exact ⟨noCollision_left_shield_of_signal_zero hψ l r hl,
    noCollision_right_shield_of_signal_zero hψ l r hr⟩

/-- The no-collision Algorithm-15 kernel frames both labels. -/
theorem noCollision_labels
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollision hψ l r).1.label = l.label ∧
      (eliminateLeadersNoCollision hψ l r).2.label = r.label := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged]
  have hfL := fire_left_label hψ l r
  have hfR := fire_right_label hψ l r
  have hm := move_labels next qf.1 qf.2
  have hs := signal_labels next qm.1 qm.2
  exact ⟨hs.1.trans (hm.1.trans hfL), hs.2.trans (hm.2.trans hfR)⟩

/-! ## Source-covered no-fire frame -/

/-- A leader cannot enter Algorithm 15's fire branch. Followers satisfy this
without constraining their absence signal. -/
def LeaderFireDisabled (u : AgentState ψ) : Prop :=
  u.leader = false ∨ u.signal_B = ⟨0, by omega⟩

/-- With both bullets absent and both leader-fire guards disabled, Algorithm 15
frames leaders, labels, shields, bullets, and the initiator absence signal.
The responder absence signal is intentionally unrestricted because propagation
may update it. -/
theorem noCollision_zero_bullets_noFire_frame
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFire : LeaderFireDisabled l)
    (hrFire : LeaderFireDisabled r)
    (hlBullet : l.bullet = ⟨0, by omega⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩) :
    let q := eliminateLeadersNoCollision hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨0, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = l.signal_B := by
  rcases hlFire with hlFollower | hlSignal
  · rcases hrFire with hrFollower | hrSignal
    · simp [eliminateLeadersNoCollision, hlFollower, hrFollower,
        hlBullet, hrBullet]
    · simp [eliminateLeadersNoCollision, hlFollower, hrSignal,
        hlBullet, hrBullet]
  · rcases hrFire with hrFollower | hrSignal
    · simp [eliminateLeadersNoCollision, hlSignal, hrFollower,
        hlBullet, hrBullet]
    · simp [eliminateLeadersNoCollision, hlSignal, hrSignal,
        hlBullet, hrBullet]

private theorem move_right_live_left_leader (next : Fin ψ)
    (l r : AgentState ψ)
    (hout : (eliminateLeadersNoCollisionMove next l r).2.bullet =
      ⟨2, by omega⟩) :
    (eliminateLeadersNoCollisionMove next l r).1.leader = true := by
  unfold eliminateLeadersNoCollisionMove at hout ⊢
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1] at hout ⊢
    by_cases hcollision : r.bullet = ⟨2, by omega⟩ ∧ l.shield = false
    · rw [if_pos hcollision] at hout ⊢
      simp at hout
    · rw [if_neg hcollision] at hout ⊢
      exact h1.2
  · rw [if_neg h1] at hout ⊢
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2] at hout ⊢
      split at hout <;> simp_all
    · rw [if_neg h2] at hout ⊢
      have hrpos : r.bullet.val > 0 := by
        rw [hout]
        decide
      cases hl : l.leader
      · exact (h2 ⟨hrpos, hl⟩).elim
      · rfl

private theorem signal_left_bullet (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal next l r).1.bullet = l.bullet := by
  rfl

private theorem signal_right_bullet (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal next l r).2.bullet = r.bullet := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  by_cases houter : r.label = next ∨ l.leader = true
  · rw [if_pos houter]
    split <;> rfl
  · rw [if_neg houter]

/-- A live bullet at the initiator output has exactly three possible origins:
it was already there, was fired by the initiator leader, or moved left from a
successor-labelled responder.  This trichotomy drives the global proof. -/
theorem noCollision_left_live_origin
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hout : (eliminateLeadersNoCollision hψ l r).1.bullet =
      ⟨2, by omega⟩) :
    l.bullet = ⟨2, by omega⟩ ∨
      (l.leader = true ∧ l.signal_B = ⟨1, by omega⟩) ∨
      (r.bullet = ⟨2, by omega⟩ ∧ l.leader = false ∧
        r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged] at hout
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).1.bullet = _
    at hout
  rw [signal_left_bullet] at hout
  rw [move_left_bullet] at hout
  have hqfLB : qf.1.bullet =
      if l.leader = true ∧ l.signal_B = ⟨1, by omega⟩ then
        ⟨2, by omega⟩ else l.bullet := fire_left_bullet hψ l r
  have hqfRB : qf.2.bullet =
      if r.leader = true ∧ r.signal_B = ⟨1, by omega⟩ then
        ⟨1, by omega⟩ else r.bullet := fire_right_bullet hψ l r
  have hqfLL : qf.1.leader = l.leader := fire_left_leader hψ l r
  have hqfRL : qf.2.label = r.label := fire_right_label hψ l r
  rw [hqfLB, hqfRB, hqfLL, hqfRL] at hout
  by_cases hL : l.leader = true ∧ l.signal_B = ⟨1, by omega⟩
  · exact Or.inr (Or.inl hL)
  · rw [if_neg hL] at hout
    by_cases hR : r.leader = true ∧ r.signal_B = ⟨1, by omega⟩
    · rw [if_pos hR] at hout
      cases hlv : l.leader
      · by_cases hlabel : r.label = next
        · simp [hlv, hlabel] at hout
        · simp [hlv, hlabel] at hout
          exact Or.inl hout
      · simp [hlv] at hout
        exact Or.inl hout
    · rw [if_neg hR] at hout
      cases hlv : l.leader
      · by_cases hb : r.bullet.val > 0
        · by_cases hlabel : r.label = next
          · simp [hlv, hb, hlabel] at hout
            exact Or.inr (Or.inr ⟨hout, rfl, hlabel⟩)
          · simp [hlv, hb, hlabel] at hout
            exact Or.inl hout
        · simp [hlv, hb] at hout
          exact Or.inl hout
      · simp [hlv] at hout
        exact Or.inl hout

/-- A responder live bullet cannot be freshly created or moved there: it must
be an old responder live bullet blocked by an initiator leader. -/
theorem noCollision_right_live_origin
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hout : (eliminateLeadersNoCollision hψ l r).2.bullet =
      ⟨2, by omega⟩) :
    r.bullet = ⟨2, by omega⟩ ∧ l.leader = true := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged] at hout
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.bullet = _
    at hout
  rw [signal_right_bullet] at hout
  rw [move_right_bullet] at hout
  have hqfRB : qf.2.bullet =
      if r.leader = true ∧ r.signal_B = ⟨1, by omega⟩ then
        ⟨1, by omega⟩ else r.bullet := fire_right_bullet hψ l r
  have hqfLL : qf.1.leader = l.leader := fire_left_leader hψ l r
  rw [hqfRB, hqfLL] at hout
  by_cases hR : r.leader = true ∧ r.signal_B = ⟨1, by omega⟩
  · rw [if_pos hR] at hout
    cases hlv : l.leader <;> simp [hlv] at hout
  · rw [if_neg hR] at hout
    cases hlv : l.leader
    · by_cases hb : r.bullet.val > 0
      · simp [hlv, hb] at hout
      · simp [hlv, hb] at hout
        have hv := congrArg Fin.val hout
        omega
    · by_cases hb : r.bullet.val > 0
      · simp only [hlv, hb, Bool.true_eq, and_self, if_true] at hout
        by_cases hcollision : r.bullet = ⟨2, by omega⟩ ∧ qf.1.shield = false
        · rw [if_pos hcollision] at hout
          simp at hout
        · rw [if_neg hcollision] at hout
          exact ⟨hout, rfl⟩
      · simp [hlv, hb] at hout
        exact ⟨hout, rfl⟩

private theorem signal_left_leader (next : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal next l r).1.leader = l.leader := by
  rfl

private theorem move_survivor_safe (next : Fin ψ)
    (l r : AgentState ψ)
    (hleader : (eliminateLeadersNoCollisionMove next l r).1.leader = true)
    (hbullet : (eliminateLeadersNoCollisionMove next l r).2.bullet =
      ⟨2, by omega⟩) :
    (eliminateLeadersNoCollisionMove next l r).1.shield = true := by
  unfold eliminateLeadersNoCollisionMove at hleader hbullet ⊢
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · rw [if_pos h1] at hleader hbullet ⊢
    by_cases hcollision :
        r.bullet = ⟨2, by omega⟩ ∧ l.shield = false
    · rw [if_pos hcollision] at hleader
      simp at hleader
    · rw [if_neg hcollision] at hleader hbullet ⊢
      cases hshield : l.shield
      · exact (hcollision ⟨hbullet, hshield⟩).elim
      · rfl
  · rw [if_neg h1] at hleader hbullet ⊢
    by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos h2] at hleader hbullet ⊢
      split at hleader <;> simp_all
    · rw [if_neg h2] at hleader hbullet ⊢
      have hrpos : r.bullet.val > 0 := by
        rw [hbullet]
        decide
      exact (h1 ⟨hrpos, hleader⟩).elim

/-- A surviving initiating leader leaves a collision-safe physical pair: if
the responder still carries a live bullet, the surviving leader is shielded.
This is the exact local fact needed to repeat the same outgoing edge safely. -/
theorem noCollisionLeaderSink_survivor_safe
    (hψ : ψ > 0) (l r : AgentState ψ)
    (_hl : l.leader = true) (hr : r.leader = false)
    (hout : (eliminateLeadersNoCollisionLeaderSink
      hψ l r).1.leader = true) :
    (eliminateLeadersNoCollisionLeaderSink hψ l r).2.bullet =
        ⟨2, by omega⟩ →
      (eliminateLeadersNoCollisionLeaderSink hψ l r).1.shield = true := by
  rw [eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
    hψ l r hr] at hout ⊢
  let next : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  rw [eliminateLeadersNoCollision_eq_staged] at hout ⊢
  change (eliminateLeadersNoCollisionSignal
    next qm.1 qm.2).1.leader = true at hout
  have hqmLeader : qm.1.leader = true := by
    simpa only [signal_left_leader] using hout
  intro hbullet
  change (eliminateLeadersNoCollisionSignal
    next qm.1 qm.2).2.bullet = ⟨2, by omega⟩ at hbullet
  have hqmBullet : qm.2.bullet = ⟨2, by omega⟩ := by
    simpa only [signal_right_bullet] using hbullet
  exact (signal_shields next qm.1 qm.2).1.trans
    (move_survivor_safe next qf.1 qf.2 hqmLeader hqmBullet)

/-- A live responder remains live when an initiating leader survives the
rooted Algorithm-15 kernel.  The only branch that changes that responder to a
dummy is precisely the unshielded, zero-signal collision branch, which kills
the initiator. -/
theorem noCollisionLeaderSink_survivor_preserves_responder_live
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hrLive : r.bullet = ⟨2, by omega⟩)
    (hout : (eliminateLeadersNoCollisionLeaderSink
      hψ l r).1.leader = true) :
    (eliminateLeadersNoCollisionLeaderSink
      hψ l r).2.bullet = ⟨2, by omega⟩ := by
  rw [eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
    hψ l r hr] at hout ⊢
  have hsignal : l.signal_B = ⟨0, by omega⟩ ∨
      l.signal_B = ⟨1, by omega⟩ := by
    rcases l.signal_B with ⟨v, hv⟩
    have hval : v = 0 ∨ v = 1 := by omega
    rcases hval with rfl | rfl <;> simp
  rcases hsignal with hsignal | hsignal <;>
    cases hshield : l.shield <;>
    simp [eliminateLeadersNoCollision, hl, hr, hrLive,
      hsignal, hshield] at hout ⊢

private theorem signal_right_zero_of_live (next : Fin ψ) (l r : AgentState ψ)
    (h : r.bullet = ⟨2, by omega⟩)
    (houter : r.label = next ∨ l.leader = true) :
    (eliminateLeadersNoCollisionSignal next l r).2.signal_B =
      ⟨0, by omega⟩ := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  rw [if_pos houter]
  rw [if_pos h]

/-- Every responder live bullet surviving the repaired kernel leaves with
`signal_B=0`, the local exclusion absent from literal Algorithm 15. -/
theorem noCollision_right_live_signal_zero
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hout : (eliminateLeadersNoCollision hψ l r).2.bullet =
      ⟨2, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨0, by omega⟩ := by
  let next : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let qf := eliminateLeadersNoCollisionFire hψ l r
  let qm := eliminateLeadersNoCollisionMove next qf.1 qf.2
  have hstaged := eliminateLeadersNoCollision_eq_staged hψ l r
  rw [hstaged] at hout ⊢
  change (eliminateLeadersNoCollisionSignal next qm.1 qm.2).2.bullet = _
    at hout
  have hqmLive : qm.2.bullet = ⟨2, by omega⟩ := by
    simpa only [signal_right_bullet] using hout
  have hqmLeader : qm.1.leader = true :=
    move_right_live_left_leader next qf.1 qf.2 hqmLive
  exact signal_right_zero_of_live next qm.1 qm.2 hqmLive
    (Or.inr hqmLeader)

/-- Against a follower initiator, repaired Algorithm 15 cannot increase the
number of live bullets on the active pair. -/
theorem eliminateLeadersNoCollision_left_follower_bulletTwoPair_le
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFollower : l.leader = false) :
    let q := eliminateLeadersNoCollision hψ l r
    bulletTwoPairMass q.1 q.2 ≤ bulletTwoPairMass l r := by
  let q := eliminateLeadersNoCollision hψ l r
  change bulletTwoPairMass q.1 q.2 ≤ bulletTwoPairMass l r
  by_cases hqL : q.1.bullet = (⟨2, by omega⟩ : Fin 3)
  · have hleft := noCollision_left_live_origin hψ l r hqL
    have hinputTwo :
        l.bullet = (⟨2, by omega⟩ : Fin 3) ∨
          r.bullet = (⟨2, by omega⟩ : Fin 3) := by
      rcases hleft with hleftOld | hfire | hrightOld
      · exact .inl hleftOld
      · have hbad := hfire.1
        simp [hlFollower] at hbad
      · exact .inr hrightOld.1
    have hqR : q.2.bullet ≠ (⟨2, by omega⟩ : Fin 3) := by
      intro hright
      have horigin := noCollision_right_live_origin hψ l r hright
      have hbad := horigin.2
      simp [hlFollower] at hbad
    unfold bulletTwoPairMass bulletTwoMass
    simp only [hqL, hqR, if_pos]
    rcases hinputTwo with hleft | hright
    · simp [hleft]
    · simp [hright]
  · by_cases hqR : q.2.bullet = (⟨2, by omega⟩ : Fin 3)
    · have horigin := noCollision_right_live_origin hψ l r hqR
      have hbad := horigin.2
      simp [hlFollower] at hbad
    · unfold bulletTwoPairMass bulletTwoMass
      simp only [hqL, hqR, if_false]
      omega

/-- With a leader initiator whose absence signal is zero, repaired Algorithm
15 cannot increase live-bullet mass.  The only live output origins are the
same endpoint's old live bullet; the fire origin is excluded by the zero
signal and follower-style transport is excluded by leadership. -/
theorem eliminateLeadersNoCollision_left_leader_signal_zero_bulletTwoPair_le
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true)
    (hlSignalZero : l.signal_B = ⟨0, by omega⟩) :
    let q := eliminateLeadersNoCollision hψ l r
    bulletTwoPairMass q.1 q.2 ≤ bulletTwoPairMass l r := by
  let q := eliminateLeadersNoCollision hψ l r
  change bulletTwoPairMass q.1 q.2 ≤ bulletTwoPairMass l r
  by_cases hqL : q.1.bullet = (⟨2, by omega⟩ : Fin 3)
  · have horigin := noCollision_left_live_origin hψ l r hqL
    have hlOld : l.bullet = (⟨2, by omega⟩ : Fin 3) := by
      rcases horigin with hlive | hfire | hmove
      · exact hlive
      · have hbad := hfire.2
        rw [hlSignalZero] at hbad
        simp at hbad
      · have hbad := hmove.2.1
        rw [hlLeader] at hbad
        simp at hbad
    by_cases hqR : q.2.bullet = (⟨2, by omega⟩ : Fin 3)
    · have hrOld := (noCollision_right_live_origin hψ l r hqR).1
      unfold bulletTwoPairMass bulletTwoMass
      rw [if_pos hqL, if_pos hqR, if_pos hlOld, if_pos hrOld]
      omega
    · unfold bulletTwoPairMass bulletTwoMass
      rw [if_pos hqL, if_neg hqR, if_pos hlOld]
      omega
  · by_cases hqR : q.2.bullet = (⟨2, by omega⟩ : Fin 3)
    · have hrOld := (noCollision_right_live_origin hψ l r hqR).1
      unfold bulletTwoPairMass bulletTwoMass
      rw [if_neg hqL, if_pos hqR, if_pos hrOld]
      omega
    · unfold bulletTwoPairMass bulletTwoMass
      rw [if_neg hqL, if_neg hqR]
      omega

/-- The responder-leader signal sink preserves the same leader/zero-signal
live-bullet nonincrease contract. -/
theorem
    eliminateLeadersNoCollisionLeaderSink_left_leader_signal_zero_bulletTwoPair_le
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true)
    (hlSignalZero : l.signal_B = ⟨0, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    bulletTwoPairMass q.1 q.2 ≤ bulletTwoPairMass l r := by
  have hle :=
    eliminateLeadersNoCollision_left_leader_signal_zero_bulletTwoPair_le
      hψ l r hlLeader hlSignalZero
  have hbullets :=
    eliminateLeadersNoCollisionLeaderSink_bullets_eq hψ l r
  simpa [bulletTwoPairMass, bulletTwoMass,
    hbullets.1, hbullets.2] using hle

/-- The leader-sink signal guard preserves the follower-initiator
live-bullet nonincrease contract. -/
theorem eliminateLeadersNoCollisionLeaderSink_left_follower_bulletTwoPair_le
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFollower : l.leader = false) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    bulletTwoPairMass q.1 q.2 ≤ bulletTwoPairMass l r := by
  have hle := eliminateLeadersNoCollision_left_follower_bulletTwoPair_le
    hψ l r hlFollower
  have hbullets :=
    eliminateLeadersNoCollisionLeaderSink_bullets_eq hψ l r
  simpa [bulletTwoPairMass, bulletTwoMass,
    hbullets.1, hbullets.2] using hle

end PPLLNoCheckBirthConditionTwoKernel
