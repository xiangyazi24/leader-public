import Leader.Wu.Protocol.Algorithm

/-!
# Explicit candidate repairs for ambiguous thesis pseudocode

Nothing in this module changes `PPLL.ppll`. These definitions are research
alternatives whose faithfulness requires author confirmation. Keeping them
separate prevents an attractive repair from being silently substituted for the
literal protocol under audit.
-/

namespace PPLLRepair

open PPLL

/-- Explicit parameter regime for repaired closedness claims. T10 shows that
`DirectedRing n`'s mere `n>0` premise is insufficient when ψ>1. -/
structure IntegratedRepairRegime (ψ n : Nat) where
  hψ : ψ > 0
  ring : DirectedRing n
  nontrivial : 1 < n

theorem no_integrated_regime_on_one (ψ : Nat) :
    IntegratedRepairRegime ψ 1 → False := by
  intro h
  have hn := h.nontrivial
  omega

private def finMax {n : Nat} (a b : Fin n) : Fin n :=
  if a.val ≥ b.val then a else b

private theorem Prod_fst_ite {c : Prop} [Decidable c] (a b : α × β) :
    (if c then a else b).1 = if c then a.1 else b.1 := by
  by_cases h : c <;> simp [h]

private theorem Prod_snd_ite {c : Prop} [Decidable c] (a b : α × β) :
    (if c then a else b).2 = if c then a.2 else b.2 := by
  by_cases h : c <;> simp [h]

private theorem AgentState_count_ite {ψ : Nat} {c : Prop} [Decidable c]
    (a b : AgentState ψ) :
    (if c then a else b).count = if c then a.count else b.count := by
  by_cases h : c <;> simp [h]

/-- Candidate interpretation of WAIT's bounded counter increment. -/
def satCountSucc (κ count : Nat) : Nat := min (count + 1) κ

theorem satCountSucc_le (κ count : Nat) : satCountSucc κ count ≤ κ := by
  exact Nat.min_le_right _ _

theorem satCountSucc_eq_succ_of_lt {κ count : Nat} (h : count < κ) :
    satCountSucc κ count = count + 1 := by
  unfold satCountSucc
  exact Nat.min_eq_left (by omega)

theorem satCountSucc_at_cap (κ : Nat) : satCountSucc κ κ = κ := by
  unfold satCountSucc
  exact Nat.min_eq_right (by omega)

/-- Initial reset/carry preparation stage of the saturating WAIT candidate. -/
def waitSaturatedPrepare {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let r := if r.label = ⟨0, hψ⟩ then
    { r with reset := true, h_field := false }
  else r
  let l := if l.label = ⟨0, hψ⟩ then
    if l.h_field = true then { l with h_field := false, carry := true }
    else { l with h_field := true }
  else l
  (l, r)

/-- Single carry-consumption stage of the saturating WAIT candidate. -/
def waitSaturatedCarry {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.carry = true then
    if r.h_field = true then
      if r.label = ⟨ψ - 1, by omega⟩ then
        ({ l with carry := false },
         { r with h_field := false, count := satCountSucc κ r.count })
      else
        ({ l with carry := false },
         { r with h_field := false, carry := true })
    else
      ({ l with carry := false }, { r with h_field := true })
  else (l, r)

/-- Reset propagation stage of the saturating WAIT candidate. -/
def waitSaturatedReset {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.reset = true then
    let r := if r.label ≠ ⟨ψ - 1, by omega⟩ then
      { r with reset := true }
    else r
    ({ l with reset := false }, { r with h_field := false })
  else (l, r)

/-- Waiting-token termination/movement stage of the saturating candidate. -/
def waitSaturatedFinish {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let r := if r.label = ⟨ψ - 1, by omega⟩ ∧ r.count = κ then
    { r with wait := false }
  else r
  if r.wait = false ∧ l.label ≠ ⟨ψ - 1, by omega⟩ then
    ({ l with wait := false }, { r with wait := true })
  else (l, r)

/-- Algorithm 3 with exactly one semantic change: line 14 uses saturation at
`κ`. The subsequent printed `count = κ` guard therefore ends waiting in the
same interaction that reaches or attempts to pass the cap. The named stages
are a definitional factoring of the previous candidate. -/
def waitSaturated {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := waitSaturatedPrepare hψ l r
  let q := waitSaturatedCarry hψ κ q.1 q.2
  let q := waitSaturatedReset hψ q.1 q.2
  waitSaturatedFinish hψ κ q.1 q.2

/-- Algorithm-4 production-state initialization after WAIT. -/
def genSigSaturatedStart {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l :=
    if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧
       l.wait = false ∧ l.path = .bot then
      { l with state := .produce }
    else l
  let r :=
    if r.label ≠ ⟨0, hψ⟩ ∧ l.state = .produce ∧ r.path = .bot then
      { r with state := .produce }
    else r
  (l, r)

/-- Algorithm-4 terminal path emission stage. -/
def genSigSaturatedEmit {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let r :=
    if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .produce then
      { r with state := .done,
               path := .some r.label.val (if r.bit then 1 else 0) }
    else r
  (l, r)

/-- Algorithm-4 backward path propagation stage. -/
def genSigSaturatedPropagate {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.state = .produce ∧
       r.state = .done then
    ({ l with state := .done,
              path := .some l.label.val (if l.bit then 1 else 0) },
     { r with state := .depart })
  else (l, r)

/-- Algorithm-4 source departure stage. -/
def genSigSaturatedFinish {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l :=
    if l.label = ⟨0, hψ⟩ ∧ l.state = .done then
      { l with state := .depart, wait := true }
    else l
  (l, r)

/-- Algorithm-4 logic after WAIT, factored without changing assignments. -/
def genSigSaturatedAfterWait {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := genSigSaturatedStart hψ l r
  let q := genSigSaturatedEmit hψ q.1 q.2
  let q := genSigSaturatedPropagate hψ q.1 q.2
  genSigSaturatedFinish hψ q.1 q.2

/-- Algorithm 4 using the separately named saturating WAIT candidate. -/
def genSigSaturated {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := waitSaturated hψ κ l r
  genSigSaturatedAfterWait hψ q.1 q.2

/-- Saturation repairs the concrete Algorithm-1 count-domain escape. -/
theorem waitSaturated_count_closed {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.count ≤ κ) (hr : r.count ≤ κ) :
    (waitSaturated hψ κ l r).1.count ≤ κ ∧
    (waitSaturated hψ κ l r).2.count ≤ κ := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish, Prod_fst_ite, Prod_snd_ite,
    AgentState_count_ite, ite_self]
  constructor
  · exact hl
  · repeat (first | exact hr | exact satCountSucc_le κ r.count | split)

/-! ## Candidate repair for the live-bullet/signal_B collision (T7) -/

/-- A live bullet and an absence signal cannot coexist.  Wu's peacefulness
condition constrains value `2` only; value `1` is a dummy bullet and may be
parked beside a leader while the absence signal starts its next circuit. -/
def LiveBulletSignalExclusive {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.bullet = ⟨2, by omega⟩ → u.signal_B = 0

/-- Leader-triggered bullet generation stage of the no-collision candidate. -/
def eliminateLeadersNoCollisionFire {ψ : Nat} (_hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := if l.leader = true ∧ l.signal_B = ⟨1, by omega⟩ then
    { l with bullet := ⟨2, by omega⟩, shield := true,
             signal_B := ⟨0, by omega⟩ }
  else l
  let r := if r.leader = true ∧ r.signal_B = ⟨1, by omega⟩ then
    { r with bullet := ⟨1, by omega⟩, shield := false,
             signal_B := ⟨0, by omega⟩ }
  else r
  (l, r)

/-- Bullet collision/movement stage of the no-collision candidate. -/
def eliminateLeadersNoCollisionMove {ψ : Nat} (nextLabel : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.bullet.val > 0 ∧ l.leader = true then
    if r.bullet = ⟨2, by omega⟩ ∧ l.shield = false then
      ({ l with leader := false }, { r with bullet := ⟨1, by omega⟩ })
    else (l, r)
  else if r.bullet.val > 0 ∧ l.leader = false then
    if r.label = nextLabel then
      ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ },
       { r with bullet := ⟨0, by omega⟩ })
    else
      (l, { r with bullet := ⟨0, by omega⟩ })
  else (l, r)

/-- Absence-signal update stage of the no-collision candidate. -/
def eliminateLeadersNoCollisionSignal {ψ : Nat} (nextLabel : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let r := if r.label = nextLabel ∨ l.leader = true then
    if r.bullet = ⟨2, by omega⟩ then
      { r with signal_B := ⟨0, by omega⟩ }
    else
      let leaderVal : Fin 2 :=
        if l.leader = true then ⟨1, by omega⟩ else ⟨0, by omega⟩
      { r with signal_B := finMax (finMax l.signal_B r.signal_B) leaderVal }
  else r
  (l, r)

/-- A non-live aligned responder receives the positive absence signal whenever
the initiator is a leader or already carries that signal. -/
theorem eliminateLeadersNoCollisionSignal_right_one_of_not_live
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ)
    (halign : r.label = nextLabel)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩)
    (hsource : l.leader = true ∨ l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollisionSignal nextLabel l r).2.signal_B =
      ⟨1, by omega⟩ := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  rw [if_pos (Or.inl halign)]
  rw [if_neg hrNotLive]
  dsimp only
  have fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    have hx : x.val = 0 ∨ x.val = 1 := by omega
    rcases hx with hx | hx
    · exact .inl (Fin.ext hx)
    · exact .inr (Fin.ext hx)
  rcases fin2_cases l.signal_B with hleft | hleft <;>
    rcases fin2_cases r.signal_B with hright | hright <;>
    cases hleader : l.leader <;>
    simp_all [finMax]

/-- The zero-bullet interface retained for existing callers. -/
theorem eliminateLeadersNoCollisionSignal_right_one
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ)
    (halign : r.label = nextLabel)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hsource : l.leader = true ∨ l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollisionSignal nextLabel l r).2.signal_B =
      ⟨1, by omega⟩ := by
  apply eliminateLeadersNoCollisionSignal_right_one_of_not_live
    nextLabel l r halign
  · intro hlive
    simp [hrBullet] at hlive
  · exact hsource

/-- Staged proof form of the no-collision Algorithm-15 candidate. -/
def eliminateLeadersNoCollisionStaged {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q := eliminateLeadersNoCollisionFire hψ l r
  let q := eliminateLeadersNoCollisionMove nextLabel q.1 q.2
  eliminateLeadersNoCollisionSignal nextLabel q.1 q.2

/-- Algorithm 15 candidate that preserves the intended exclusion between a
live bullet and a bullet-absence signal. It differs only in the final
`signal_B` update: a responder still carrying bullet value `2` is clamped to
zero. Dummy bullet value `1` remains compatible with the signal, as required
when a unique leader starts a new circuit after its dummy returns. This is a
research repair, not silently substituted into `PPLL.ppll`. -/
def eliminateLeadersNoCollision {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.leader = true ∧ l.signal_B = ⟨1, by omega⟩ then
    { l with bullet := ⟨2, by omega⟩, shield := true,
             signal_B := ⟨0, by omega⟩ }
  else l
  let r := if r.leader = true ∧ r.signal_B = ⟨1, by omega⟩ then
    { r with bullet := ⟨1, by omega⟩, shield := false,
             signal_B := ⟨0, by omega⟩ }
  else r
  let (l, r) :=
    if r.bullet.val > 0 ∧ l.leader = true then
      if r.bullet = ⟨2, by omega⟩ ∧ l.shield = false then
        ({ l with leader := false }, { r with bullet := ⟨1, by omega⟩ })
      else (l, r)
    else if r.bullet.val > 0 ∧ l.leader = false then
      if r.label = nextLabel then
        ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ },
         { r with bullet := ⟨0, by omega⟩ })
      else
        (l, { r with bullet := ⟨0, by omega⟩ })
    else (l, r)
  let r := if r.label = nextLabel ∨ l.leader = true then
    if r.bullet = ⟨2, by omega⟩ then
      { r with signal_B := ⟨0, by omega⟩ }
    else
      let leaderVal : Fin 2 :=
        if l.leader = true then ⟨1, by omega⟩ else ⟨0, by omega⟩
      { r with signal_B := finMax (finMax l.signal_B r.signal_B) leaderVal }
  else r
  (l, r)

/-- The staged proof form is definitionally equal to the candidate. -/
theorem eliminateLeadersNoCollision_eq_staged {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    eliminateLeadersNoCollision hψ l r =
      eliminateLeadersNoCollisionStaged hψ l r := by
  rfl

/-- A dummy bullet parked clockwise of a leader is not a live-bullet
collision.  It remains parked, while Algorithm 15's leader source writes the
positive absence signal at the responder.  Clamping every positive bullet
would make this unique-leader circuit permanently impossible. -/
theorem eliminateLeadersNoCollision_right_dummy_signal_of_left_leader
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true)
    (hrFollower : r.leader = false)
    (hrDummy : r.bullet = ⟨1, by omega⟩) :
    let q := eliminateLeadersNoCollision hψ l r
    q.2.bullet = ⟨1, by omega⟩ ∧ q.2.signal_B = ⟨1, by omega⟩ := by
  have fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    have hx : x.val = 0 ∨ x.val = 1 := by omega
    rcases hx with hx | hx
    · exact .inl (Fin.ext hx)
    · exact .inr (Fin.ext hx)
  rcases fin2_cases l.signal_B with hlSignal | hlSignal <;>
    rcases fin2_cases r.signal_B with hrSignal | hrSignal <;>
    simp [eliminateLeadersNoCollision, hlLeader, hrFollower, hrDummy,
      hlSignal, hrSignal, finMax]

/-- A leader source writes the positive absence signal at every follower
responder that does not carry a live bullet.  The two possible responder
bullets are handled uniformly: an idle responder receives the signal in
place, while a dummy responder keeps its dummy and also receives the signal.
No label-alignment premise is needed because the leader-source branch itself
authorizes the Algorithm-15 signal write. -/
theorem eliminateLeadersNoCollision_right_signal_of_left_leader_not_live
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true)
    (hrFollower : r.leader = false)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩) :
    (eliminateLeadersNoCollision hψ l r).2.signal_B =
      ⟨1, by omega⟩ := by
  have hrBulletVal : r.bullet.val = 0 ∨ r.bullet.val = 1 ∨
      r.bullet.val = 2 := by
    omega
  rcases hrBulletVal with hrBulletVal | hrBulletVal | hrBulletVal
  · have hrBullet : r.bullet = ⟨0, by omega⟩ := Fin.ext hrBulletVal
    have fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
      intro x
      have hx : x.val = 0 ∨ x.val = 1 := by omega
      rcases hx with hx | hx
      · exact .inl (Fin.ext hx)
      · exact .inr (Fin.ext hx)
    rcases fin2_cases l.signal_B with hlSignal | hlSignal <;>
      rcases fin2_cases r.signal_B with hrSignal | hrSignal <;>
      simp [eliminateLeadersNoCollision, hlLeader, hrFollower, hrBullet,
        hlSignal, hrSignal, finMax]
  · have hrDummy : r.bullet = ⟨1, by omega⟩ := Fin.ext hrBulletVal
    exact (eliminateLeadersNoCollision_right_dummy_signal_of_left_leader
      hψ l r hlLeader hrFollower hrDummy).2
  · exact (hrNotLive (Fin.ext hrBulletVal)).elim

/-! ## Candidate repair for the rooted leader-entry cut -/

/-- Absence-signal update that also lets an existing responder leader receive
the signal across a nonconsecutive incoming edge.  This is the smallest local
change needed by the rooted nondivisible shield circuit: the old aligned-edge
and leader-initiator cases are unchanged, and the live-bullet clamp remains
in force. -/
def eliminateLeadersNoCollisionSignalLeaderSink {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let r := if r.label = nextLabel ∨
      l.leader = true ∨ r.leader = true then
    if r.bullet = ⟨2, by omega⟩ then
      { r with signal_B := ⟨0, by omega⟩ }
    else
      let leaderVal : Fin 2 :=
        if l.leader = true then ⟨1, by omega⟩ else ⟨0, by omega⟩
      { r with signal_B := finMax (finMax l.signal_B r.signal_B) leaderVal }
  else r
  (l, r)

/-- A responder leader without a live bullet receives any positive source
signal. -/
theorem
    eliminateLeadersNoCollisionSignalLeaderSink_right_one_of_leader_not_live
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ)
    (hrLeader : r.leader = true)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩)
    (hsource : l.leader = true ∨
      l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel l r).2.signal_B = ⟨1, by omega⟩ := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  dsimp only
  rw [if_pos (Or.inr (Or.inr hrLeader))]
  rw [if_neg hrNotLive]
  dsimp only
  have fin2_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    have hx : x.val = 0 ∨ x.val = 1 := by omega
    rcases hx with hx | hx
    · exact .inl (Fin.ext hx)
    · exact .inr (Fin.ext hx)
  rcases fin2_cases l.signal_B with hleft | hleft <;>
    rcases fin2_cases r.signal_B with hright | hright <;>
    cases hleader : l.leader <;>
    simp_all [finMax]

/-- The zero-bullet responder-leader interface retained for existing callers. -/
theorem eliminateLeadersNoCollisionSignalLeaderSink_right_one_of_leader
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ)
    (hrLeader : r.leader = true)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hsource : l.leader = true ∨
      l.signal_B = ⟨1, by omega⟩) :
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel l r).2.signal_B = ⟨1, by omega⟩ := by
  apply
    eliminateLeadersNoCollisionSignalLeaderSink_right_one_of_leader_not_live
      nextLabel l r hrLeader
  · intro hlive
    simp [hrBullet] at hlive
  · exact hsource

/-- Algorithm 15 with only the final signal guard extended by the existing
responder-leader case.  FIRE and MOVE are exactly the no-collision repair
already audited above. -/
def eliminateLeadersNoCollisionLeaderSink {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q := eliminateLeadersNoCollisionFire hψ l r
  let q := eliminateLeadersNoCollisionMove nextLabel q.1 q.2
  eliminateLeadersNoCollisionSignalLeaderSink nextLabel q.1 q.2

private theorem eliminateLeadersNoCollisionMove_right_leader
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove nextLabel l r).2.leader =
      r.leader := by
  simp only [eliminateLeadersNoCollisionMove]
  repeat (first | rfl | split)

private theorem eliminateLeadersNoCollisionMove_right_shield
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove nextLabel l r).2.shield =
      r.shield := by
  simp only [eliminateLeadersNoCollisionMove]
  repeat (first | rfl | split)

private theorem
    eliminateLeadersNoCollisionSignalLeaderSink_right_leader
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel l r).2.leader = r.leader := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | rfl | split)

private theorem
    eliminateLeadersNoCollisionSignalLeaderSink_right_shield
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel l r).2.shield = r.shield := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | rfl | split)

/-- A responder leader carrying the positive absence signal fires on this
interaction.  The responder remains a leader, but its shield is cleared before
movement and the final leader-sink signal update does not change either field.
This is the local certification step needed before a live bullet may eliminate
a duplicate leader. -/
theorem
    eliminateLeadersNoCollisionLeaderSink_responder_signal_one_unshielded
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hrLeader : r.leader = true)
    (hrSignal : r.signal_B = ⟨1, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.2.leader = true ∧ q.2.shield = false := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let fired := eliminateLeadersNoCollisionFire hψ l r
  let moved := eliminateLeadersNoCollisionMove
    nextLabel fired.1 fired.2
  have hfireLeader : fired.2.leader = true := by
    simp [fired, eliminateLeadersNoCollisionFire, hrLeader, hrSignal]
  have hfireShield : fired.2.shield = false := by
    simp [fired, eliminateLeadersNoCollisionFire, hrLeader, hrSignal]
  have hmoveLeader : moved.2.leader = true :=
    (eliminateLeadersNoCollisionMove_right_leader
      nextLabel fired.1 fired.2).trans hfireLeader
  have hmoveShield : moved.2.shield = false :=
    (eliminateLeadersNoCollisionMove_right_shield
      nextLabel fired.1 fired.2).trans hfireShield
  have hsignalLeader :=
    eliminateLeadersNoCollisionSignalLeaderSink_right_leader
      nextLabel moved.1 moved.2
  have hsignalShield :=
    eliminateLeadersNoCollisionSignalLeaderSink_right_shield
      nextLabel moved.1 moved.2
  change
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel moved.1 moved.2).2.leader = true ∧
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel moved.1 moved.2).2.shield = false
  exact ⟨hsignalLeader.trans hmoveLeader,
    hsignalShield.trans hmoveShield⟩

private theorem eliminateLeadersNoCollisionSignalLeaderSink_left
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r).1 = l := by
  rfl

private theorem eliminateLeadersNoCollisionSignalLeaderSink_right_bullet
    {ψ : Nat} (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel l r).2.bullet = r.bullet := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | rfl | split)

/-- **Local live-bullet kill (pair-level).**  An unshielded initiator leader
that does not itself carry the absence signal is eliminated by a live bullet
parked at a follower responder, and that live bullet is spent down to a dummy
in the same interaction.

The signal-zero premise is not cosmetic.  Algorithm 15 fires strictly before
it moves, so an initiator leader carrying `signal_B = 1` re-shields itself
during FIRE and is then immune to the very bullet meant for it; see
`eliminateLeadersNoCollisionLeaderSink_signal_one_initiator_survives`.  The
follower premise on the responder is likewise required: a responder leader
carrying the signal would spend the live bullet down to a dummy during FIRE
before MOVE could use it. -/
theorem eliminateLeadersNoCollisionLeaderSink_initiator_killed_of_live
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true)
    (hlUnshielded : l.shield = false)
    (hlSignalZero : l.signal_B = ⟨0, by omega⟩)
    (hrFollower : r.leader = false)
    (hrLive : r.bullet = ⟨2, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.leader = false ∧ q.2.bullet = ⟨1, by omega⟩ := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let fired := eliminateLeadersNoCollisionFire hψ l r
  let moved := eliminateLeadersNoCollisionMove
    nextLabel fired.1 fired.2
  have hfired : fired = (l, r) := by
    simp [fired, eliminateLeadersNoCollisionFire, hlSignalZero, hrFollower]
  have hmoved : moved = ({ l with leader := false },
      { r with bullet := ⟨1, by omega⟩ }) := by
    simp [moved, hfired, eliminateLeadersNoCollisionMove, hlLeader,
      hlUnshielded, hrLive]
  have hmovedLeader : moved.1.leader = false := by
    rw [hmoved]
  have hmovedBullet : moved.2.bullet = ⟨1, by omega⟩ := by
    rw [hmoved]
  change
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel moved.1 moved.2).1.leader = false ∧
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel moved.1 moved.2).2.bullet = ⟨1, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [eliminateLeadersNoCollisionSignalLeaderSink_left]
    exact hmovedLeader
  · exact (eliminateLeadersNoCollisionSignalLeaderSink_right_bullet
      nextLabel moved.1 moved.2).trans hmovedBullet

/-- **Exact obstruction to killing a signalled initiator leader.**  An
initiator leader carrying the absence signal is shielded by FIRE before the
movement stage runs, so it survives the leader-sink Algorithm 15 and ends
shielded *whatever the responder holds* — in particular a live bullet parked
at the responder cannot eliminate it.

Read in the other direction this is the protection certificate for the
designated survivor: the endpoint that emits the live bullet is the same
endpoint that raises its own shield in the same stage. -/
theorem eliminateLeadersNoCollisionLeaderSink_signal_one_initiator_survives
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlLeader : l.leader = true)
    (hlSignal : l.signal_B = ⟨1, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.leader = true ∧ q.1.shield = true := by
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let fired := eliminateLeadersNoCollisionFire hψ l r
  let moved := eliminateLeadersNoCollisionMove
    nextLabel fired.1 fired.2
  have hfiredLeader : fired.1.leader = true := by
    simp [fired, eliminateLeadersNoCollisionFire, hlLeader, hlSignal]
  have hfiredShield : fired.1.shield = true := by
    simp [fired, eliminateLeadersNoCollisionFire, hlLeader, hlSignal]
  have hmovedL : moved.1 = fired.1 := by
    show (eliminateLeadersNoCollisionMove nextLabel fired.1 fired.2).1
      = fired.1
    unfold eliminateLeadersNoCollisionMove
    split
    · split
      · rename_i h2
        exact absurd h2.2 (by rw [hfiredShield]; simp)
      · rfl
    · split
      · rename_i h3
        exact absurd h3.2 (by rw [hfiredLeader]; simp)
      · rfl
  change
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel moved.1 moved.2).1.leader = true ∧
    (eliminateLeadersNoCollisionSignalLeaderSink
      nextLabel moved.1 moved.2).1.shield = true
  rw [eliminateLeadersNoCollisionSignalLeaderSink_left, hmovedL]
  exact ⟨hfiredLeader, hfiredShield⟩

/-- The leader-sink repair is definitionally identical to the established
no-collision Algorithm 15 whenever the responder is a follower. -/
theorem eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hrFollower : r.leader = false) :
    eliminateLeadersNoCollisionLeaderSink hψ l r =
      eliminateLeadersNoCollision hψ l r := by
  rw [eliminateLeadersNoCollision_eq_staged]
  unfold eliminateLeadersNoCollisionLeaderSink
    eliminateLeadersNoCollisionStaged
  dsimp only
  have hfireFollower :
      (eliminateLeadersNoCollisionFire hψ l r).2.leader = false := by
    unfold eliminateLeadersNoCollisionFire
    simp [hrFollower]
  have hmoveFollower :
      (eliminateLeadersNoCollisionMove
        ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
        (eliminateLeadersNoCollisionFire hψ l r).1
        (eliminateLeadersNoCollisionFire hψ l r).2).2.leader = false := by
    exact (eliminateLeadersNoCollisionMove_right_leader
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
      (eliminateLeadersNoCollisionFire hψ l r).1
      (eliminateLeadersNoCollisionFire hψ l r).2).trans hfireFollower
  unfold eliminateLeadersNoCollisionSignalLeaderSink
    eliminateLeadersNoCollisionSignal
  dsimp only
  simp only [hmoveFollower, Bool.false_eq_true, or_false]

/-- The responder-leader signal sink changes no Algorithm-15 leader bit.  Its
only difference from the established no-collision repair is the final
`signal_B` guard. -/
theorem eliminateLeadersNoCollisionLeaderSink_leaders_eq
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionLeaderSink hψ l r).1.leader =
        (eliminateLeadersNoCollision hψ l r).1.leader ∧
      (eliminateLeadersNoCollisionLeaderSink hψ l r).2.leader =
        (eliminateLeadersNoCollision hψ l r).2.leader := by
  rw [eliminateLeadersNoCollision_eq_staged]
  unfold eliminateLeadersNoCollisionLeaderSink
    eliminateLeadersNoCollisionStaged
    eliminateLeadersNoCollisionSignalLeaderSink
    eliminateLeadersNoCollisionSignal
  dsimp only
  repeat (first | constructor | rfl | split)

/-- The signal-sink guard also changes no Algorithm-15 label. -/
theorem eliminateLeadersNoCollisionLeaderSink_labels_eq
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionLeaderSink hψ l r).1.label =
        (eliminateLeadersNoCollision hψ l r).1.label ∧
      (eliminateLeadersNoCollisionLeaderSink hψ l r).2.label =
        (eliminateLeadersNoCollision hψ l r).2.label := by
  rw [eliminateLeadersNoCollision_eq_staged]
  unfold eliminateLeadersNoCollisionLeaderSink
    eliminateLeadersNoCollisionStaged
    eliminateLeadersNoCollisionSignalLeaderSink
    eliminateLeadersNoCollisionSignal
  dsimp only
  repeat (first | constructor | rfl | split)

/-- The signal-sink guard also changes no Algorithm-15 bullet. -/
theorem eliminateLeadersNoCollisionLeaderSink_bullets_eq
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionLeaderSink hψ l r).1.bullet =
        (eliminateLeadersNoCollision hψ l r).1.bullet ∧
      (eliminateLeadersNoCollisionLeaderSink hψ l r).2.bullet =
        (eliminateLeadersNoCollision hψ l r).2.bullet := by
  rw [eliminateLeadersNoCollision_eq_staged]
  unfold eliminateLeadersNoCollisionLeaderSink
    eliminateLeadersNoCollisionStaged
    eliminateLeadersNoCollisionSignalLeaderSink
    eliminateLeadersNoCollisionSignal
  dsimp only
  repeat (first | constructor | rfl | split)

/-- The responder-leader signal sink changes only the responder-side final
signal guard; the initiator signal is exactly the established Algorithm-15
output signal. -/
theorem eliminateLeadersNoCollisionLeaderSink_left_signal_eq
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionLeaderSink hψ l r).1.signal_B =
      (eliminateLeadersNoCollision hψ l r).1.signal_B := by
  rw [eliminateLeadersNoCollision_eq_staged]
  unfold eliminateLeadersNoCollisionLeaderSink
    eliminateLeadersNoCollisionStaged
    eliminateLeadersNoCollisionSignalLeaderSink
    eliminateLeadersNoCollisionSignal
  dsimp only
  repeat (first | rfl | split)

/-- On an aligned follower-to-follower edge, a positive absence signal either
reaches the responder or a dummy bullet is moved one edge counterclockwise.
The live-bullet case is excluded separately: it is the only positive bullet
that the repaired signal stage clamps.  This local dichotomy is the atomic
progress step used by the finite dummy-bullet rank argument. -/
theorem
    eliminateLeadersNoCollisionLeaderSink_aligned_signal_or_dummy_moves
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFollower : l.leader = false)
    (hrFollower : r.leader = false)
    (halign : r.label =
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlSignal : l.signal_B = ⟨1, by omega⟩)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.2.signal_B = ⟨1, by omega⟩ ∨
      (r.bullet = ⟨1, by omega⟩ ∧
        q.1.bullet = ⟨1, by omega⟩ ∧
        q.2.bullet = ⟨0, by omega⟩) := by
  have hrBulletVal : r.bullet.val = 0 ∨ r.bullet.val = 1 ∨
      r.bullet.val = 2 := by
    omega
  rcases hrBulletVal with hrBulletVal | hrBulletVal | hrBulletVal
  · have hrBullet : r.bullet = ⟨0, by omega⟩ := Fin.ext hrBulletVal
    left
    have hrSignalVal : r.signal_B.val = 0 ∨ r.signal_B.val = 1 := by
      omega
    rcases hrSignalVal with hrSignalVal | hrSignalVal
    · have hrSignal : r.signal_B = ⟨0, by omega⟩ := Fin.ext hrSignalVal
      simp [eliminateLeadersNoCollisionLeaderSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        hlFollower, hrFollower, halign, hlSignal, hrBullet, hrSignal,
        finMax]
    · have hrSignal : r.signal_B = ⟨1, by omega⟩ := Fin.ext hrSignalVal
      simp [eliminateLeadersNoCollisionLeaderSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        hlFollower, hrFollower, halign, hlSignal, hrBullet, hrSignal,
        finMax]
  · have hrBullet : r.bullet = ⟨1, by omega⟩ := Fin.ext hrBulletVal
    right
    simp [eliminateLeadersNoCollisionLeaderSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      hlFollower, hrFollower, halign, hlSignal, hrBullet]
  · exact (hrNotLive (Fin.ext hrBulletVal)).elim

/-- Exact bullet transport on an aligned follower-to-follower edge without a
live responder bullet.  A responder dummy moves to the initiator and the
responder is cleared; a zero responder leaves the initiator bullet unchanged.
No new dummy is created by this step. -/
theorem
    eliminateLeadersNoCollisionLeaderSink_aligned_follower_bullets
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFollower : l.leader = false)
    (hrFollower : r.leader = false)
    (halign : r.label =
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.bullet =
        (if r.bullet = ⟨1, by omega⟩ then ⟨1, by omega⟩
          else l.bullet) ∧
      q.2.bullet = ⟨0, by omega⟩ := by
  have hrBulletVal : r.bullet.val = 0 ∨ r.bullet.val = 1 ∨
      r.bullet.val = 2 := by
    omega
  rcases hrBulletVal with hrBulletVal | hrBulletVal | hrBulletVal
  · have hrBullet : r.bullet = ⟨0, by omega⟩ := Fin.ext hrBulletVal
    simp [eliminateLeadersNoCollisionLeaderSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      hlFollower, hrFollower, halign, hrBullet]
  · have hrBullet : r.bullet = ⟨1, by omega⟩ := Fin.ext hrBulletVal
    simp [eliminateLeadersNoCollisionLeaderSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      hlFollower, hrFollower, halign, hrBullet]
  · exact (hrNotLive (Fin.ext hrBulletVal)).elim

/-- Exact live-bullet transport on an aligned follower-to-follower edge.  The
responder's live bullet moves one edge counterclockwise to the initiator and
the responder is cleared.  This is the directional refinement of pair-mass
nonincrease needed by the rooted live-bullet rank. -/
theorem
    eliminateLeadersNoCollisionLeaderSink_aligned_follower_live_bullets
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFollower : l.leader = false)
    (hrFollower : r.leader = false)
    (halign : r.label =
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hrLive : r.bullet = ⟨2, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.bullet = ⟨2, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ := by
  simp [eliminateLeadersNoCollisionLeaderSink,
    eliminateLeadersNoCollisionFire,
    eliminateLeadersNoCollisionMove,
    eliminateLeadersNoCollisionSignalLeaderSink,
    hlFollower, hrFollower, halign, hrLive]

/-- On a barrier follower-to-leader closing edge, delivery of the returning
absence signal needs no bullet or responder-signal premise.  A positive
responder bullet is discarded by the nonaligned movement branch before the
leader-sink signal stage runs; a zero responder bullet already permits signal
delivery.  Thus the positive initiator signal reaches the leader in either
case. -/
theorem eliminateLeadersNoCollisionLeaderSink_closing_signal_fields
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hbarrier : r.label ≠
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlFollower : l.leader = false)
    (hrLeader : r.leader = true)
    (hlSignal : l.signal_B = ⟨1, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.leader = false ∧ q.2.leader = true ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.2.signal_B = ⟨1, by omega⟩ := by
  have hrSignalVal : r.signal_B.val = 0 ∨ r.signal_B.val = 1 := by
    omega
  rcases hrSignalVal with hrSignalVal | hrSignalVal
  · have hrSignal : r.signal_B = ⟨0, by omega⟩ := Fin.ext hrSignalVal
    have hrBulletVal : r.bullet.val = 0 ∨ r.bullet.val = 1 ∨
        r.bullet.val = 2 := by omega
    rcases hrBulletVal with hrBulletVal | hrBulletVal | hrBulletVal
    · have hrBullet : r.bullet = ⟨0, by omega⟩ := Fin.ext hrBulletVal
      simp [eliminateLeadersNoCollisionLeaderSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        hbarrier, hlFollower, hrLeader, hlSignal, hrSignal,
        hrBullet, finMax]
    · have hrBullet : r.bullet = ⟨1, by omega⟩ := Fin.ext hrBulletVal
      simp [eliminateLeadersNoCollisionLeaderSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        hbarrier, hlFollower, hrLeader, hlSignal, hrSignal,
        hrBullet, finMax]
    · have hrBullet : r.bullet = ⟨2, by omega⟩ := Fin.ext hrBulletVal
      simp [eliminateLeadersNoCollisionLeaderSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        hbarrier, hlFollower, hrLeader, hlSignal, hrSignal,
        hrBullet, finMax]
  · have hrSignal : r.signal_B = ⟨1, by omega⟩ := Fin.ext hrSignalVal
    simp [eliminateLeadersNoCollisionLeaderSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      hbarrier, hlFollower, hrLeader, hlSignal, hrSignal,
      finMax]

/-- On the rooted closing edge, the repair changes exactly the missing
absence-signal receipt: both zero bullets and all leader/label/shield fields
are framed, while the responder leader receives `signal_B = 1`. -/
theorem eliminateLeadersNoCollisionLeaderSink_closing_fields
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlFollower : l.leader = false)
    (hrLeader : r.leader = true)
    (hlSignal : l.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.signal_B = ⟨0, by omega⟩)
    (hlBullet : l.bullet = ⟨0, by omega⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.signal_B = ⟨1, by omega⟩ ∧
      q.2.signal_B = ⟨1, by omega⟩ ∧
      q.1.leader = false ∧ q.2.leader = true ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨0, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ := by
  simp [eliminateLeadersNoCollisionLeaderSink,
    eliminateLeadersNoCollisionFire,
    eliminateLeadersNoCollisionMove,
    eliminateLeadersNoCollisionSignalLeaderSink,
    hlFollower, hrLeader, hlSignal, hrSignal, hlBullet, hrBullet,
    finMax]

/-- Full candidate P_PLL transition with only Algorithm 15 replaced by the
no-collision variant. -/
def ppllNoBulletSignalCollision {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllBeforeEliminateLeaders hψ κ l r
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

/-- Combined-repair boundary immediately before CHECK. -/
def ppllSaturatedBeforeCheck {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  sigMove hψ q.1 q.2

/-- Combined-repair boundary immediately before Algorithm 15. -/
def ppllSaturatedBeforeEliminate {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheck hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSig hψ q.1 q.2
  suppressSig hψ q.1 q.2

/-- Combined-repair boundary immediately before WRITE_SEQ. -/
def ppllSaturatedBeforeWrite {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeEliminate hψ κ l r
  eliminateLeadersNoCollision hψ q.1 q.2

/-- Combined explicit repair branch: saturating WAIT in Algorithm 4 and
no bullet/signal_B collision in Algorithm 15. Signal provenance is deliberately
unchanged and remains an invariant obligation rather than a transition patch. -/
def ppllSaturatedNoCollision {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeWrite hψ κ l r
  writeSeq hψ q.1 q.2

/-! ## Candidate repair for source-aligned signal re-arming (T9) -/

/-- CMP_UPDATE candidate that does not overwrite a source-departing label-zero
state with `congest`. All later Algorithm-7 assignments are unchanged. -/
def cmpUpdateNoSourceRearm {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ l.state ≠ .depart then
    { l with state := .congest }
  else l
  let q := cmpUpdatePropagate hψ l r
  (cmpUpdateSetPath2 hψ q.1, q.2)

/-- Algorithm 6 with only CMP_UPDATE replaced by the no-source-rearm
candidate. -/
def compareSigNoSourceRearm {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let q := cmpUpdateNoSourceRearm hψ l r
      compareSigDispatch hψ q.1 q.2
    | .bot => (l, r)

/-- Integrated-repair boundary immediately before SUPPRESS_SIG. -/
def ppllIntegratedBeforeSuppress {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllSaturatedBeforeCheck hψ κ l r
  let q := checkSig hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  compareSigNoSourceRearm hψ q.1 q.2

/-- Integrated transition candidate combining WAIT saturation, bullet/signal
exclusion, and the T9 source-rearm guard. -/
def ppllIntegratedRepair {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := ppllIntegratedBeforeSuppress hψ κ l r
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

/-- Population-protocol package for the integrated T9 candidate. -/
def integratedProtocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := ppllIntegratedRepair hψ κ
  output := AgentState.outputFn

/-- Population-protocol package for the explicit combined repair branch. -/
def protocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) : PopulationProtocol where
  Q := AgentState ψ
  Y := LeaderOutput
  transition := ppllSaturatedNoCollision hψ κ
  output := AgentState.outputFn

/-! ## Zero-leader bullet egress repair

A separately named MOVE stage that allows a label-zero leader's bullet to
exit across a nonconsecutive follower/leader edge.  This unblocks
multi-leader cleanup at arbitrary interleader distances without adding
state.  The established `eliminateLeadersNoCollisionMove` is not
overwritten. -/

def eliminateLeadersNoCollisionZeroLeaderEgressMove {ψ : Nat}
    (hψ : ψ > 0) (nextLabel : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.bullet.val > 0 ∧ l.leader = true then
    if r.bullet = ⟨2, by omega⟩ ∧ l.shield = false then
      ({ l with leader := false }, { r with bullet := ⟨1, by omega⟩ })
    else (l, r)
  else if r.bullet.val > 0 ∧ l.leader = false then
    if r.label = nextLabel ∨
        (r.leader = true ∧ r.label = ⟨0, hψ⟩) then
      ({ l with bullet := r.bullet, signal_B := ⟨0, by omega⟩ },
       { r with bullet := ⟨0, by omega⟩ })
    else
      (l, { r with bullet := ⟨0, by omega⟩ })
  else (l, r)

theorem eliminateLeadersNoCollisionZeroLeaderEgressMove_eq_of_responder_follower
    {ψ : Nat} (hψ : ψ > 0) (nextLabel : Fin ψ)
    (l r : AgentState ψ) (hr : r.leader = false) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nextLabel l r =
      eliminateLeadersNoCollisionMove nextLabel l r := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionMove]
  split
  · rfl
  · split
    · simp [hr]
    · rfl

theorem eliminateLeadersNoCollisionZeroLeaderEgressMove_eq_of_responder_bullet_zero
    {ψ : Nat} (hψ : ψ > 0) (nextLabel : Fin ψ)
    (l r : AgentState ψ) (hr : r.bullet = ⟨0, by omega⟩) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nextLabel l r =
      eliminateLeadersNoCollisionMove nextLabel l r := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionMove]
  have hbz : ¬(r.bullet.val > 0) := by simp [hr]
  simp [hbz]

theorem eliminateLeadersNoCollisionZeroLeaderEgressMove_eq_of_initiator_leader
    {ψ : Nat} (hψ : ψ > 0) (nextLabel : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = true) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nextLabel l r =
      eliminateLeadersNoCollisionMove nextLabel l r := by
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
    eliminateLeadersNoCollisionMove
  simp [hl]

theorem eliminateLeadersNoCollisionZeroLeaderEgressMove_eq_of_successor_aligned
    {ψ : Nat} (hψ : ψ > 0) (nextLabel : Fin ψ)
    (l r : AgentState ψ) (halign : r.label = nextLabel) :
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nextLabel l r =
      eliminateLeadersNoCollisionMove nextLabel l r := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionMove]
  split
  · rfl
  · split
    · simp [halign]
    · rfl

/-! ## COMPARE action-1 guard repair

`compareBitUpdateR` unconditionally processes any `path2` at position 0,
which destroys CHECK's directional action codes (4 and 6) in the same
interaction.  This separately named repair processes only action-1 tokens,
leaving CHECK results intact for the max-carrier route. -/

def compareBitUpdateRActionOne {ψ : Nat} (hψ : ψ > 0)
    (r : AgentState ψ) : AgentState ψ :=
  match r.path2 with
  | some p2 =>
    if p2.position = 0 ∧ p2.action = 1 then
      let rBitNat := if r.bit then 1 else 0
      if rBitNat > p2.bit then
        { r with path2 := some ⟨0, 0, 0, 3⟩ }
      else if rBitNat < p2.bit then
        { r with path2 := some ⟨0, 0, 0, 4⟩ }
      else
        if r.label = ⟨ψ - 1, by omega⟩ then
          { r with path2 := some ⟨0, 0, 0, 3⟩ }
        else
          { r with path2 := some ⟨0, 0, ψ - 1, 2⟩ }
    else r
  | none => r

theorem compareBitUpdateRActionOne_eq_of_action_one {ψ : Nat} (hψ : ψ > 0)
    (r : AgentState ψ) (hp2 : r.path2 = some p2) (hact : p2.action = 1) :
    compareBitUpdateRActionOne hψ r = compareBitUpdateR hψ r := by
  simp only [compareBitUpdateRActionOne, compareBitUpdateR, hp2]
  split
  · next h =>
    simp [h.1]
  · next h =>
    have hne : p2.position ≠ 0 := fun hp => h ⟨hp, hact⟩
    simp [hne]

theorem compareBitUpdateRActionOne_eq_of_no_path2 {ψ : Nat} (hψ : ψ > 0)
    (r : AgentState ψ) (hnone : r.path2 = none) :
    compareBitUpdateRActionOne hψ r = r := by
  simp [compareBitUpdateRActionOne, hnone]

theorem compareBitUpdateRActionOne_preserves_check_result {ψ : Nat}
    (hψ : ψ > 0) (r : AgentState ψ) (hp2 : r.path2 = some p2)
    (hact : p2.action = 4 ∨ p2.action = 6) :
    compareBitUpdateRActionOne hψ r = r := by
  simp only [compareBitUpdateRActionOne, hp2]
  split
  · next h =>
    rcases hact with hact | hact <;> simp [hact] at h
  · rfl

/-! ## Post-Algorithm-15 dummy bullet sink

A surviving initiator leader clears a follower responder's dummy bullet.
This unblocks the multi-leader cleanup word by removing forged dummy
bullets that suppress absence-signal delivery.  Zero additional state. -/

def dummyBulletSink {ψ : Nat}
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  if q.1.leader = true ∧ q.2.leader = false ∧
      q.2.bullet = ⟨1, by omega⟩ then
    (q.1, { q.2 with bullet := ⟨0, by omega⟩ })
  else
    q

theorem dummyBulletSink_left_eq (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1 = q.1 := by
  simp [dummyBulletSink]; split <;> rfl

theorem dummyBulletSink_eq_of_initiator_follower
    (q : AgentState ψ × AgentState ψ) (h : q.1.leader = false) :
    dummyBulletSink q = q := by
  simp [dummyBulletSink, h]

theorem dummyBulletSink_eq_of_responder_leader
    (q : AgentState ψ × AgentState ψ) (h : q.2.leader = true) :
    dummyBulletSink q = q := by
  simp [dummyBulletSink, h]

theorem dummyBulletSink_eq_of_responder_bullet_zero
    (q : AgentState ψ × AgentState ψ) (h : q.2.bullet = ⟨0, by omega⟩) :
    dummyBulletSink q = q := by
  simp [dummyBulletSink]
  intro _ _
  simp [h]

theorem dummyBulletSink_eq_of_responder_bullet_two
    (q : AgentState ψ × AgentState ψ) (h : q.2.bullet = ⟨2, by omega⟩) :
    dummyBulletSink q = q := by
  simp [dummyBulletSink]
  intro _ _
  simp [h]

theorem dummyBulletSink_clears
    (q : AgentState ψ × AgentState ψ)
    (hl : q.1.leader = true) (hr : q.2.leader = false)
    (hb : q.2.bullet = ⟨1, by omega⟩) :
    (dummyBulletSink q).2.bullet = ⟨0, by omega⟩ := by
  simp [dummyBulletSink, hl, hr, hb]

theorem dummyBulletSink_leader_frame (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.leader = q.1.leader ∧
    (dummyBulletSink q).2.leader = q.2.leader := by
  simp [dummyBulletSink]
  split <;> simp_all

end PPLLRepair
