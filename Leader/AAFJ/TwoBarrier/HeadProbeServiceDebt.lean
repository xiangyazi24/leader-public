import Leader.AAFJ.BarrierAlgebra

/-!
# Local service debt for a persistent AAFJ barrier

While a phase-one barrier is blocked by a probe at its head, the scheduler
must serve the outgoing edge of that head.  The only branch in which this
service fails to clear the head probe is a leader-with-bullet responder.

The finite resource behind that exception is the responder's pair of bits
`leader` and `probe`.  A stubborn service consumes its leader bit, while every
interaction other than the service edge weakly decreases the sum of those two
bits.  In particular, a barrier interaction at the responder may turn its
probe into a leader, but cannot create a second unit of credit.

This file proves the literal child rows only.  The stopped-process wrapper
which turns the five services (arm, at most three blocked-head services, and
advance) into an expected `5*n` raw-interaction bound is kept separate.
-/

set_option autoImplicit false

namespace AAFJPK.PersistentBarrierService

open BarrierAlgebra

private theorem rightNeighbor_rightNeighbor_ne_self_of_two_lt
    {n : Nat} (ring : DirectedRing n) (hn3 : 2 < n) (edge : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor edge) ≠ edge := by
  intro hcycle
  have hv := congrArg Fin.val hcycle
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases hfirst : edge.val + 1 < n
  · rw [Nat.mod_eq_of_lt hfirst] at hv
    by_cases hsecond : edge.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt hsecond] at hv
      omega
    · have hwrap : edge.val + 1 + 1 = n := by omega
      rw [hwrap, Nat.mod_self] at hv
      omega
  · have hwrap : edge.val + 1 = n := by omega
    rw [hwrap, Nat.mod_self] at hv
    have hsmall : 1 < n := by omega
    rw [Nat.mod_eq_of_lt hsmall] at hv
    omega

/-- The two physical bits which can pay for a stubborn blocked-head service. -/
def stubbornCredit {k : Nat} (u : State k) : Nat :=
  (if u.leader then 1 else 0) + (if u.probe then 1 else 0)

private theorem nonbarrier_headProbe_survives_iff_leader_bullet
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v) (hprobe : u.probe = true) :
    (transition hk u v).1.probe = true ↔
      v.leader = true ∧ v.bullet = true := by
  rw [transition_of_nonbarrier hk u v hnon]
  cases hl : v.leader <;> cases hb : v.bullet <;>
    simp [nonBarrierStep, hl, hb, hprobe]

theorem stubbornCredit_le_two {k : Nat} (u : State k) :
    stubbornCredit u ≤ 2 := by
  cases hl : u.leader <;> cases hp : u.probe <;>
    simp [stubbornCredit, hl, hp]

/-- Updating a vertex as an initiator never increases its leader/probe credit.
The barrier branch can exchange one probe for one leader; every nonbarrier
branch keeps the leader bit and can only clear the initiator probe. -/
theorem transition_left_stubbornCredit_le {k : Nat} (hk : 0 < k)
    (u v : State k) :
    stubbornCredit (transition hk u v).1 ≤ stubbornCredit u := by
  by_cases hbar : IsBarrier hk u v
  · rw [transition_of_barrier hk u v hbar]
    cases hp : u.probe <;> cases hphase : u.phase <;>
      cases hvp : v.probe <;>
      simp [barrierStep, probeHitsBarrier, hp, hphase, hvp, stubbornCredit]
  · rw [transition_of_nonbarrier hk u v hbar]
    cases hl : v.leader <;> cases hb : v.bullet <;>
      cases hp : u.probe <;>
      simp [nonBarrierStep, hl, hb, hp, stubbornCredit]

/-- Exact payment row for the stubborn branch.  If a nonbarrier service leaves
the initiator probe set, then it consumes exactly one unit of responder
leader/probe credit. -/
theorem nonbarrier_service_survives_pays_one {k : Nat} (hk : 0 < k)
    (u v : State k) (hnon : ¬ IsBarrier hk u v)
    (hprobe : u.probe = true)
    (hsurvive : (transition hk u v).1.probe = true) :
    stubbornCredit (transition hk u v).2 + 1 = stubbornCredit v := by
  have hex :=
    (nonbarrier_headProbe_survives_iff_leader_bullet
      hk u v hnon hprobe).1 hsurvive
  rw [transition_of_nonbarrier hk u v hnon]
  simp [nonBarrierStep, hex.1, hex.2, stubbornCredit]
  omega

/-- One blocked-head service either clears the probe or spends one unit of the
finite stubborn credit at the next vertex. -/
theorem nonbarrier_service_clears_or_pays {k : Nat} (hk : 0 < k)
    (u v : State k) (hnon : ¬ IsBarrier hk u v)
    (hprobe : u.probe = true) :
    (transition hk u v).1.probe = false ∨
      stubbornCredit (transition hk u v).2 + 1 = stubbornCredit v := by
  cases h : (transition hk u v).1.probe
  · exact Or.inl (by simpa using h)
  · exact Or.inr (nonbarrier_service_survives_pays_one
      hk u v hnon hprobe h)

/-- An interaction other than the incoming service edge cannot increase the
stubborn credit stored at a fixed vertex. -/
theorem off_incoming_edge_stubbornCredit_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (incoming vertex e : Fin n)
    (hincoming : ring.rightNeighbor incoming = vertex)
    (hne : e ≠ incoming) :
    stubbornCredit ((protocol k hk).step ring C e vertex) ≤
      stubbornCredit (C vertex) := by
  by_cases hev : e = vertex
  · subst e
    simp only [PopulationProtocol.step, protocol]
    simp [transition_left_stubbornCredit_le hk]
  · have hrv : ring.rightNeighbor e ≠ vertex := by
      intro h
      apply hne
      apply rightNeighbor_injective ring
      rw [h, hincoming]
    change stubbornCredit
      (if vertex = e then (transition hk (C e) (C (ring.rightNeighbor e))).1
       else if vertex = ring.rightNeighbor e then
         (transition hk (C e) (C (ring.rightNeighbor e))).2
       else C vertex) ≤ stubbornCredit (C vertex)
    simp [Ne.symm hev, Ne.symm hrv]

/-- If `b` is a phase-one barrier blocked by a probe at its head `h`, every
action other than the service edge `h` preserves that blocking probe.  The
only other action which can touch `h` is `b` itself, and its blocked barrier
branch leaves the responder unchanged. -/
theorem blocked_head_probe_preserved_of_ne_service
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hphase : (C b).phase = true)
    (hprobe : (C (ring.rightNeighbor b)).probe = true)
    (hne : e ≠ ring.rightNeighbor b) :
    (((protocol k hk).step ring C e) (ring.rightNeighbor b)).probe = true := by
  let h := ring.rightNeighbor b
  have hbne : b ≠ h := Ne.symm (rightNeighbor_ne_self ring hn2 b)
  by_cases heb : e = b
  · subst e
    have hj : IsBarrier hk (C b) (C h) :=
      (barrierAt_labelsOf_iff hk ring C b).1 hbar
    have hlocal := barrierStep_phase_one_probe_blocked
      hk (C b) (C h) hphase hprobe
    have htrans : transition hk (C b) (C h) =
        (probeHitsBarrier (C b), C h) := by
      rw [transition_of_barrier hk (C b) (C h) hj]
      exact hlocal
    simpa [PopulationProtocol.step, protocol, h, htrans,
      rightNeighbor_ne_self ring hn2 b] using hprobe
  · have her : ring.rightNeighbor e ≠ h := by
      intro her
      apply heb
      apply rightNeighbor_injective ring
      simpa [h] using her
    change (if ring.rightNeighbor b = e then
        (transition hk (C e) (C (ring.rightNeighbor e))).1
      else if ring.rightNeighbor b = ring.rightNeighbor e then
        (transition hk (C e) (C (ring.rightNeighbor e))).2
      else C (ring.rightNeighbor b)).probe = true
    rw [if_neg (Ne.symm hne), if_neg (Ne.symm her)]
    exact hprobe

/-- Ring-level blocked-head row.  Serving the head edge either clears the
blocking probe or decreases by one the stubborn credit at the responder. -/
theorem blocked_head_service_clears_or_pays
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b))
    (hprobe : (C (ring.rightNeighbor b)).probe = true) :
    let h := ring.rightNeighbor b
    let v := ring.rightNeighbor h
    let D := (protocol k hk).step ring C h
    (D h).probe = false ∨ stubbornCredit (D v) + 1 = stubbornCredit (C v) := by
  dsimp only
  let h := ring.rightNeighbor b
  let v := ring.rightNeighbor h
  have hvh : v ≠ h := rightNeighbor_ne_self ring hn2 h
  have hnon : ¬ IsBarrier hk (C h) (C v) := by
    intro hj
    exact hfree ((barrierAt_labelsOf_iff hk ring C h).2 hj)
  have hrow := nonbarrier_service_clears_or_pays
    hk (C h) (C v) hnon (by simpa [h] using hprobe)
  simpa [PopulationProtocol.step, protocol, h, v, hvh] using hrow

/-- Remaining number of services of the blocked head edge.  A clear head has
zero debt; a blocked head has one final clearing service plus the two-bit
stubborn credit at the responder. -/
def blockedDebt {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Nat :=
  let h := ring.rightNeighbor b
  let v := ring.rightNeighbor h
  if (C h).probe then stubbornCredit (C v) + 1 else 0

theorem blockedDebt_le_three {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : blockedDebt ring C b ≤ 3 := by
  simp only [blockedDebt]
  split
  · have hc := stubbornCredit_le_two
      (C (ring.rightNeighbor (ring.rightNeighbor b)))
    omega
  · omega

/-- Before contact, every non-service action weakly decreases the blocked
debt.  The barrier hypotheses are used only to show that the blocked head
probe itself survives an interaction at the barrier tail. -/
theorem blockedDebt_step_le_of_ne_service
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hphase : (C b).phase = true)
    (hprobe : (C (ring.rightNeighbor b)).probe = true)
    (hne : e ≠ ring.rightNeighbor b) :
    blockedDebt ring ((protocol k hk).step ring C e) b ≤
      blockedDebt ring C b := by
  let h := ring.rightNeighbor b
  let v := ring.rightNeighbor h
  let D := (protocol k hk).step ring C e
  have hpD : (D h).probe = true := by
    dsimp [D, h]
    exact blocked_head_probe_preserved_of_ne_service
      hk ring hn2 C b e hbar hphase hprobe hne
  have hcD : stubbornCredit (D v) ≤ stubbornCredit (C v) := by
    dsimp [D, v]
    exact off_incoming_edge_stubbornCredit_le
      hk ring C h v e rfl (by simpa [h] using hne)
  simp [blockedDebt, h, v, D, hpD, hprobe]
  omega

/-- Serving a blocked head edge strictly decreases its finite debt.  This is
the pathwise row which accounts for marked-head leaders and for the one
possible probe-to-leader rebirth at the responder. -/
theorem blockedDebt_step_lt_of_service
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b))
    (hprobe : (C (ring.rightNeighbor b)).probe = true) :
    blockedDebt ring
        ((protocol k hk).step ring C (ring.rightNeighbor b)) b <
      blockedDebt ring C b := by
  let h := ring.rightNeighbor b
  let v := ring.rightNeighbor h
  let D := (protocol k hk).step ring C h
  cases hp : (D h).probe
  · simp [blockedDebt, h, v, D, hp, hprobe]
  · have hnon : ¬ IsBarrier hk (C h) (C v) := by
      intro hj
      exact hfree ((barrierAt_labelsOf_iff hk ring C h).2 hj)
    have hvh : v ≠ h := rightNeighbor_ne_self ring hn2 h
    have hlocalSurvive :
        (transition hk (C h) (C v)).1.probe = true := by
      simpa [D, PopulationProtocol.step, protocol, h, v, hvh] using hp
    have hpayLocal := nonbarrier_service_survives_pays_one
      hk (C h) (C v) hnon (by simpa [h] using hprobe) hlocalSurvive
    have hpay : stubbornCredit (D v) + 1 = stubbornCredit (C v) := by
      simpa [D, PopulationProtocol.step, protocol, h, v, hvh] using hpayLocal
    dsimp [D, h, v] at hpay
    simp [blockedDebt, h, v, D, hp, hprobe]
    omega

/-- Five-service clock attached to a fixed barrier tail.  Contact on either
side is terminal for this local clock; the left-contact test is supplied by
the stopped carrier, while the right-contact test appears here directly.
The values are: cold arm `5`, blocked head `blockedDebt+1`, ready advance `1`.
-/
def serviceDebt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Nat :=
  if BarrierAt hk ring (labelsOf C) b then
    if BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b) then 0
    else if (C b).phase = false then 5
    else if (C (ring.rightNeighbor b)).probe then
      blockedDebt ring C b + 1
    else 1
  else 0

/-- Predictable physical edge served by the five-service clock. -/
def serviceTarget {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Fin n :=
  if (C b).phase = false then b
  else if (C (ring.rightNeighbor b)).probe then ring.rightNeighbor b
  else b

/-- The tagged barrier has not yet contacted a neighbor on either side.  The
left condition is written without choosing a predecessor coordinate. -/
def PreContact {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Prop :=
  BarrierAt hk ring (labelsOf C) b ∧
  ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b) ∧
  ∀ e, ring.rightNeighbor e = b →
    ¬ BarrierAt hk ring (labelsOf C) e

private theorem transition_nonbarrier_phases
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v) :
    (transition hk u v).1.phase = u.phase ∧
      (transition hk u v).2.phase = v.phase := by
  rw [transition_of_nonbarrier hk u v hnon]
  cases hl : v.leader <;> cases hb : v.bullet <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hl, hb, hp]

private theorem transition_nonbarrier_left_probe_false
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v) (hp : u.probe = false) :
    (transition hk u v).1.probe = false := by
  rw [transition_of_nonbarrier hk u v hnon]
  cases hl : v.leader <;> cases hb : v.bullet <;>
    simp [nonBarrierStep, hl, hb, hp]

private theorem transition_barrier_left_phase_true
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v) (hp : u.phase = true) :
    (transition hk u v).1.phase = true := by
  rw [transition_of_barrier hk u v hbar]
  have hpu : (probeHitsBarrier u).phase = true := by simpa [hp]
  unfold barrierStep
  dsimp only
  rw [hpu]
  split
  · rfl
  · split <;> exact hpu

private theorem tail_phase_true_preserved
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hleft : ∀ a, ring.rightNeighbor a = b →
      ¬ BarrierAt hk ring (labelsOf C) a)
    (hp : (C b).phase = true) :
    (((protocol k hk).step ring C e) b).phase = true := by
  by_cases heb : e = b
  · subst e
    have hj := (barrierAt_labelsOf_iff hk ring C b).1 hbar
    have hl := transition_barrier_left_phase_true
      hk (C b) (C (ring.rightNeighbor b)) hj hp
    simp [PopulationProtocol.step, protocol, hl]
  · by_cases hrb : ring.rightNeighbor e = b
    · have hnon : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro hj
        exact hleft e hrb ((barrierAt_labelsOf_iff hk ring C e).2 hj)
      have hr := (transition_nonbarrier_phases
        hk (C e) (C (ring.rightNeighbor e)) hnon).2
      calc
        (((protocol k hk).step ring C e) b).phase =
            (transition hk (C e) (C (ring.rightNeighbor e))).2.phase := by
              simp [PopulationProtocol.step, protocol, Ne.symm heb, hrb]
        _ = (C (ring.rightNeighbor e)).phase := hr
        _ = true := by simpa [hrb] using hp
    · change (if b = e then (transition hk (C e) (C (ring.rightNeighbor e))).1
        else if b = ring.rightNeighbor e then
          (transition hk (C e) (C (ring.rightNeighbor e))).2
        else C b).phase = true
      rw [if_neg (Ne.symm heb), if_neg (Ne.symm hrb)]
      exact hp

private theorem tail_phase_false_preserved_of_ne
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b e : Fin n)
    (hleft : ∀ a, ring.rightNeighbor a = b →
      ¬ BarrierAt hk ring (labelsOf C) a)
    (hp : (C b).phase = false) (heb : e ≠ b) :
    (((protocol k hk).step ring C e) b).phase = false := by
  by_cases hrb : ring.rightNeighbor e = b
  · have hnon : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
      intro hj
      exact hleft e hrb ((barrierAt_labelsOf_iff hk ring C e).2 hj)
    have hr := (transition_nonbarrier_phases
      hk (C e) (C (ring.rightNeighbor e)) hnon).2
    calc
      (((protocol k hk).step ring C e) b).phase =
          (transition hk (C e) (C (ring.rightNeighbor e))).2.phase := by
            simp [PopulationProtocol.step, protocol, Ne.symm heb, hrb]
      _ = (C (ring.rightNeighbor e)).phase := hr
      _ = false := by simpa [hrb] using hp
  · change (if b = e then (transition hk (C e) (C (ring.rightNeighbor e))).1
      else if b = ring.rightNeighbor e then
        (transition hk (C e) (C (ring.rightNeighbor e))).2
      else C b).phase = false
    rw [if_neg (Ne.symm heb), if_neg (Ne.symm hrb)]
    exact hp

private theorem ready_head_probe_false_preserved_of_ne_tail
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b e : Fin n)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b))
    (hp : (C (ring.rightNeighbor b)).probe = false) (heb : e ≠ b) :
    (((protocol k hk).step ring C e) (ring.rightNeighbor b)).probe = false := by
  let h := ring.rightNeighbor b
  by_cases heh : e = h
  · subst e
    have hnon : ¬ IsBarrier hk (C h) (C (ring.rightNeighbor h)) := by
      intro hj
      exact hfree ((barrierAt_labelsOf_iff hk ring C h).2 hj)
    have hl := transition_nonbarrier_left_probe_false
      hk (C h) (C (ring.rightNeighbor h)) hnon (by simpa [h] using hp)
    simp [PopulationProtocol.step, protocol, h, hl]
  · have hrh : ring.rightNeighbor e ≠ h := by
      intro hr
      apply heb
      apply rightNeighbor_injective ring
      simpa [h] using hr
    change (if ring.rightNeighbor b = e then
        (transition hk (C e) (C (ring.rightNeighbor e))).1
      else if ring.rightNeighbor b = ring.rightNeighbor e then
        (transition hk (C e) (C (ring.rightNeighbor e))).2
      else C (ring.rightNeighbor b)).probe = false
    rw [if_neg (Ne.symm heh), if_neg (Ne.symm hrh)]
    exact hp

theorem serviceDebt_le_five {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n) :
    serviceDebt hk ring C b ≤ 5 := by
  unfold serviceDebt
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  have h := blockedDebt_le_three ring C b
  omega

/-- A cold hit at the persistent barrier tail strictly decreases the
five-service debt.  This includes a marked head leader: it either leaves a
ready head or enters the blocked stage, whose two-bit credit is bounded by 2.
-/
theorem serviceDebt_step_lt_of_cold_hit
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b))
    (hcold : (C b).phase = false) :
    serviceDebt hk ring ((protocol k hk).step ring C b) b <
      serviceDebt hk ring C b := by
  let D := (protocol k hk).step ring C b
  have hnot : ¬ AdvanceReady hk ring C b := by
    intro h
    exact Bool.noConfusion (h.2.1.symm.trans hcold)
  have hlabels : labelsOf D = labelsOf C := by
    exact labelsOf_step_eq_self_of_not_ready hk ring C b hnot
  have hbne : b ≠ ring.rightNeighbor b :=
    Ne.symm (rightNeighbor_ne_self ring hn2 b)
  have hj : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1 hbar
  have hlocal := barrierStep_phase_zero
    hk (C b) (C (ring.rightNeighbor b)) hcold
  have htrans : transition hk (C b) (C (ring.rightNeighbor b)) =
      ({ probeHitsBarrier (C b) with phase := true },
        if (C (ring.rightNeighbor b)).leader = false then
          { C (ring.rightNeighbor b) with probe := true }
        else C (ring.rightNeighbor b)) := by
    rw [transition_of_barrier hk _ _ hj]
    exact hlocal
  have hphaseD : (D b).phase = true := by
    simp [D, PopulationProtocol.step, protocol, hbne, htrans]
  have hbarD : BarrierAt hk ring (labelsOf D) b := by
    rw [hlabels]
    exact hbar
  have hfreeD :
      ¬ BarrierAt hk ring (labelsOf D) (ring.rightNeighbor b) := by
    rw [hlabels]
    exact hfree
  have hbound := blockedDebt_le_three ring D b
  have hpost : serviceDebt hk ring D b ≤ 4 := by
    unfold serviceDebt
    rw [if_pos hbarD, if_neg hfreeD, if_neg (by simpa using hphaseD)]
    split <;> omega
  have hpre : serviceDebt hk ring C b = 5 := by
    simp [serviceDebt, hbar, hfree, hcold]
  simpa [D, hpre] using (show serviceDebt hk ring D b < 5 by omega)

/-- A ready hit repairs the tagged barrier edge, hence discharges the final
unit of service debt. -/
theorem serviceDebt_step_lt_of_ready_hit
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b))
    (hphase : (C b).phase = true)
    (hprobe : (C (ring.rightNeighbor b)).probe = false) :
    serviceDebt hk ring ((protocol k hk).step ring C b) b <
      serviceDebt hk ring C b := by
  have hready : AdvanceReady hk ring C b :=
    ⟨(barrierAt_labelsOf_iff hk ring C b).1 hbar, hphase, hprobe⟩
  have hrepair := protocol_advance_repairs_edge hk ring hn2 C b hready
  let D := (protocol k hk).step ring C b
  have hpost : serviceDebt hk ring D b = 0 := by
    simp [serviceDebt, D, hrepair]
  have hpre : serviceDebt hk ring C b = 1 := by
    simp [serviceDebt, hbar, hfree, hphase, hprobe]
  simpa [D, hpost, hpre]

/-- A blocked-head hit decreases the combined clock.  The `n>2` hypothesis
ensures that the service edge's responder is not the tagged barrier tail, so
the service cannot alter the tail phase while paying down blocked debt. -/
theorem serviceDebt_step_lt_of_blocked_hit
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (b : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b))
    (hphase : (C b).phase = true)
    (hprobe : (C (ring.rightNeighbor b)).probe = true) :
    serviceDebt hk ring
        ((protocol k hk).step ring C (ring.rightNeighbor b)) b <
      serviceDebt hk ring C b := by
  let h := ring.rightNeighbor b
  let v := ring.rightNeighbor h
  let D := (protocol k hk).step ring C h
  have hn2 : 1 < n := by omega
  have hnon : ¬ IsBarrier hk (C h) (C v) := by
    intro hj
    exact hfree ((barrierAt_labelsOf_iff hk ring C h).2 hj)
  have hnot : ¬ AdvanceReady hk ring C h := by
    intro hr
    exact hnon hr.1
  have hlabels : labelsOf D = labelsOf C := by
    exact labelsOf_step_eq_self_of_not_ready hk ring C h hnot
  have hbarD : BarrierAt hk ring (labelsOf D) b := by
    rw [hlabels]
    exact hbar
  have hfreeD : ¬ BarrierAt hk ring (labelsOf D) h := by
    rw [hlabels]
    simpa [h] using hfree
  have hhb : h ≠ b := rightNeighbor_ne_self ring hn2 b
  have hvb : v ≠ b := rightNeighbor_rightNeighbor_ne_self_of_two_lt ring hn3 b
  have hphaseD : (D b).phase = true := by
    change (if b = h then (transition hk (C h) (C v)).1
      else if b = v then (transition hk (C h) (C v)).2
      else C b).phase = true
    rw [if_neg (Ne.symm hhb), if_neg (Ne.symm hvb)]
    exact hphase
  have hblocked := blockedDebt_step_lt_of_service
    hk ring hn2 C b hfree hprobe
  change blockedDebt ring D b < blockedDebt ring C b at hblocked
  have hpre : serviceDebt hk ring C b = blockedDebt ring C b + 1 := by
    simp [serviceDebt, hbar, hfree, hphase, hprobe]
  have hpost : serviceDebt hk ring D b = blockedDebt ring D b + 1 := by
    unfold serviceDebt
    rw [if_pos hbarD, if_neg hfreeD, if_neg (by simpa using hphaseD)]
    cases hp : (D h).probe
    · simp [blockedDebt, h, v, hp]
    · simp [blockedDebt, h, v, hp]
  change serviceDebt hk ring D b < serviceDebt hk ring C b
  rw [hpost, hpre]
  exact Nat.add_lt_add_right hblocked 1

/-- Unified target row: before right contact, the history-predictable service
edge strictly decreases the bounded physical debt. -/
theorem serviceTarget_step_strict
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (b : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) b)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor b)) :
    serviceDebt hk ring
        ((protocol k hk).step ring C (serviceTarget ring C b)) b <
      serviceDebt hk ring C b := by
  cases hp : (C b).phase
  · simpa [serviceTarget, hp] using
      serviceDebt_step_lt_of_cold_hit hk ring (by omega) C b
        hbar hfree hp
  · cases hq : (C (ring.rightNeighbor b)).probe
    · simpa [serviceTarget, hp, hq] using
        serviceDebt_step_lt_of_ready_hit hk ring (by omega) C b
          hbar hfree hp hq
    · simpa [serviceTarget, hp, hq] using
        serviceDebt_step_lt_of_blocked_hit hk ring hn3 C b
          hbar hfree hp hq

/-- Exact continuation row for all non-target scheduler children.  If both the
old and new tagged states are still pre-contact, every non-target action
weakly decreases the service debt.  A child which violates `PreContact` is a
terminal contact/advance child in the stopped carrier, rather than an active
child hidden in this hypothesis. -/
theorem serviceDebt_step_le_of_ne_target
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hpre : PreContact hk ring C b)
    (hpost : PreContact hk ring ((protocol k hk).step ring C e) b)
    (hne : e ≠ serviceTarget ring C b) :
    serviceDebt hk ring ((protocol k hk).step ring C e) b ≤
      serviceDebt hk ring C b := by
  let D := (protocol k hk).step ring C e
  have hn2 : 1 < n := by omega
  rcases hpre with ⟨hbar, hfree, hleft⟩
  rcases hpost with ⟨hbarD, hfreeD, hleftD⟩
  cases hp : (C b).phase
  · have hneb : e ≠ b := by
      simpa [serviceTarget, hp] using hne
    have hpD : (D b).phase = false := by
      exact tail_phase_false_preserved_of_ne
        hk ring C b e hleft hp hneb
    dsimp [D] at hpD
    simp [serviceDebt, hbar, hfree, hp, hbarD, hfreeD, hpD]
  · have hpD : (D b).phase = true :=
      tail_phase_true_preserved hk ring C b e hbar hleft hp
    cases hq : (C (ring.rightNeighbor b)).probe
    · have hneb : e ≠ b := by
        simpa [serviceTarget, hp, hq] using hne
      have hqD : (D (ring.rightNeighbor b)).probe = false := by
        exact ready_head_probe_false_preserved_of_ne_tail
          hk ring C b e hfree hq hneb
      dsimp [D] at hpD hqD
      simp [serviceDebt, hbar, hfree, hp, hq,
        hbarD, hfreeD, hpD, hqD]
    · have hneh : e ≠ ring.rightNeighbor b := by
        simpa [serviceTarget, hp, hq] using hne
      have hqD : (D (ring.rightNeighbor b)).probe = true := by
        exact blocked_head_probe_preserved_of_ne_service
          hk ring hn2 C b e hbar hp hq hneh
      have hdebt := blockedDebt_step_le_of_ne_service
        hk ring hn2 C b e hbar hp hq hneh
      change blockedDebt ring D b ≤ blockedDebt ring C b at hdebt
      dsimp [D] at hpD hqD hdebt
      simp [serviceDebt, hbar, hfree, hp, hq,
        hbarD, hfreeD, hpD, hqD]
      omega

#check stubbornCredit_le_two
#check transition_left_stubbornCredit_le
#check nonbarrier_service_survives_pays_one
#check nonbarrier_service_clears_or_pays
#check off_incoming_edge_stubbornCredit_le
#check blocked_head_probe_preserved_of_ne_service
#check blocked_head_service_clears_or_pays
#check blockedDebt_le_three
#check blockedDebt_step_le_of_ne_service
#check blockedDebt_step_lt_of_service
#check serviceDebt_le_five
#check serviceDebt_step_lt_of_cold_hit
#check serviceDebt_step_lt_of_ready_hit
#check serviceDebt_step_lt_of_blocked_hit
#check serviceTarget_step_strict
#check serviceDebt_step_le_of_ne_target

#print axioms transition_left_stubbornCredit_le
#print axioms nonbarrier_service_survives_pays_one
#print axioms off_incoming_edge_stubbornCredit_le
#print axioms blocked_head_probe_preserved_of_ne_service
#print axioms blocked_head_service_clears_or_pays
#print axioms blockedDebt_step_le_of_ne_service
#print axioms blockedDebt_step_lt_of_service
#print axioms serviceDebt_step_lt_of_cold_hit
#print axioms serviceDebt_step_lt_of_ready_hit
#print axioms serviceDebt_step_lt_of_blocked_hit
#print axioms serviceTarget_step_strict
#print axioms serviceDebt_step_le_of_ne_target

end AAFJPK.PersistentBarrierService
