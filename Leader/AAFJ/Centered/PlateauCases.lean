import Leader.AAFJ.Centered.RankMonotone

/-!
# Literal plateau cases for centered AAFJ renewal

This module classifies one literal centered-renewal interaction whose physical
one-barrier rank stays at the same value strictly above the floor.  It exposes
the two compensating events hidden by weak `Phi` monotonicity: deletion of one
bullet-bearing responder leader can create one unit of danger debt, and birth
of the probed barrier tail can discharge that debt.  Every other plateau step
frames the complete physical leader map and the dangerousness bit.

The post-state is always viewed at the exact successor barrier: it advances by
one physical edge precisely on a phase-one barrier interaction.  No claim is
made about a later shield after the barrier has crossed a tracked target.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace PlateauCases

open BarrierAlgebra
open SingleBarrierSanitation

set_option autoImplicit false

/-- One literal packaged centered-renewal interaction. -/
def step {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (selected : Fin n) : Fin n → State k :=
  (CenteredRenewal.protocol k hk).step ring C selected

/-- Exact unique-barrier witness after one centered interaction. -/
def postBarrierTail {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (tail selected : Fin n) : Fin n :=
  if CenteredRenewal.AdvanceReady hk ring C selected then
    ring.rightNeighbor tail
  else tail

/-! ## Consumer payloads -/

/-- The ordinary plateau case: the complete physical leader vector, both
physical and cut leader counts, and the dangerousness bit are unchanged. -/
structure StablePlateau {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail selected : Fin n) : Prop where
  leader_frame : ∀ i : Fin n, (after i).leader = (before i).leader
  physical_count : leaderCount after = leaderCount before
  cut_count :
    leaderCount
        (cutView ring (postBarrierTail hk ring before tail selected) after) =
      leaderCount (cutView ring tail before)
  dangerous_iff :
    Dangerous
        (cutView ring (postBarrierTail hk ring before tail selected) after) ↔
      Dangerous (cutView ring tail before)

/-- The only plateau leader deletion: a nonbarrier incoming bullet deletes
its responder leader, all other leader bits and every probe are framed, and
the lost leader is exchanged for one dangerousness charge.

`last_shield` records the probe for which the responder was the unique later
leader.  This is the witness needed when a covered sweep enters debt mode. -/
structure NonStrictLastDeath {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail selected : Fin n) : Prop where
  nonbarrier : ¬ IsBarrier hk (before selected)
    (before (ring.rightNeighbor selected))
  responder_leader : (before (ring.rightNeighbor selected)).leader = true
  responder_bullet : (before (ring.rightNeighbor selected)).bullet = true
  responder_dies : (after (ring.rightNeighbor selected)).leader = false
  other_leaders : ∀ i : Fin n, i ≠ ring.rightNeighbor selected →
    (after i).leader = (before i).leader
  probe_frame : ∀ i : Fin n, (after i).probe = (before i).probe
  physical_count : leaderCount after + 1 = leaderCount before
  cut_count :
    leaderCount (cutView ring tail after) + 1 =
      leaderCount (cutView ring tail before)
  danger_before : ¬ Dangerous (cutView ring tail before)
  danger_after : Dangerous (cutView ring tail after)
  last_shield : ∃ p : Fin n,
    (before p).probe = true ∧
      (cutCoord ring tail p).val <
        (cutCoord ring tail (ring.rightNeighbor selected)).val ∧
      ∀ ell : Fin n, (before ell).leader = true →
        (cutCoord ring tail p).val < (cutCoord ring tail ell).val →
        ell = ring.rightNeighbor selected

/-- The only plateau leader creation: the selected edge is the unique barrier,
the old tail's literal `probeHitsBarrier` prelude creates exactly that leader
and clears exactly that probe while preserving its bullet, and the birth
exchanges the dangerousness charge for one leader.

The final field exposes the phase-zero/phase-one distinction required by the
renewal consumer: whenever this interaction genuinely advances the barrier,
the exact new tail is phase zero. -/
structure CompensatingTailBirth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail selected : Fin n) : Prop where
  selected_tail : selected = tail
  tail_probe : (before tail).probe = true
  tail_follower : (before tail).leader = false
  tail_born : (after tail).leader = true
  tail_probe_cleared : (after tail).probe = false
  tail_bullet_preserved : (after tail).bullet = (before tail).bullet
  other_leaders : ∀ i : Fin n, i ≠ tail →
    (after i).leader = (before i).leader
  physical_count : leaderCount after = leaderCount before + 1
  cut_count :
    leaderCount
        (cutView ring (postBarrierTail hk ring before tail selected) after) =
      leaderCount (cutView ring tail before) + 1
  danger_before : Dangerous (cutView ring tail before)
  danger_after :
    ¬ Dangerous
      (cutView ring (postBarrierTail hk ring before tail selected) after)
  advance_new_tail_phase_false :
    CenteredRenewal.AdvanceReady hk ring before selected →
      (after (postBarrierTail hk ring before tail selected)).phase = false

/-! ## Rank arithmetic above the floor -/

/-- Exact arithmetic shape of a rank value strictly above the floor. -/
theorem plateau_shape {n k r : Nat} (X : Fin n → State k)
    (hphi : Phi X = r) (hr : 1 < r) :
    (¬ Dangerous X ∧ leaderCount X = r) ∨
      (Dangerous X ∧ leaderCount X + 1 = r) := by
  by_cases hd : Dangerous X
  · right
    refine ⟨hd, ?_⟩
    simp [Phi, dangerBit, hd] at hphi
    omega
  · left
    refine ⟨hd, ?_⟩
    simp [Phi, dangerBit, hd] at hphi
    omega

/-- On a plateau strictly above one, equal leader counts force the same
dangerousness bit. -/
theorem plateau_same_count_dangerous_iff {n k r : Nat}
    (before after : Fin n → State k)
    (hbefore : Phi before = r) (hafter : Phi after = r) (hr : 1 < r)
    (hcount : leaderCount after = leaderCount before) :
    Dangerous after ↔ Dangerous before := by
  rcases plateau_shape before hbefore hr with hb | hb <;>
    rcases plateau_shape after hafter hr with ha | ha
  · exact iff_of_false ha.1 hb.1
  · omega
  · omega
  · exact iff_of_true ha.1 hb.1

/-- A one-leader plateau deletion is possible only by changing the danger bit
from false to true. -/
theorem plateau_drop_danger_status {n k r : Nat}
    (before after : Fin n → State k)
    (hbefore : Phi before = r) (hafter : Phi after = r) (hr : 1 < r)
    (hcount : leaderCount after + 1 = leaderCount before) :
    ¬ Dangerous before ∧ Dangerous after := by
  rcases plateau_shape before hbefore hr with hb | hb <;>
    rcases plateau_shape after hafter hr with ha | ha
  · omega
  · exact ⟨hb.1, ha.1⟩
  · omega
  · omega

/-- A one-leader plateau birth is possible only by changing the danger bit
from true to false. -/
theorem plateau_birth_danger_status {n k r : Nat}
    (before after : Fin n → State k)
    (hbefore : Phi before = r) (hafter : Phi after = r) (hr : 1 < r)
    (hcount : leaderCount after = leaderCount before + 1) :
    Dangerous before ∧ ¬ Dangerous after := by
  rcases plateau_shape before hbefore hr with hb | hb <;>
    rcases plateau_shape after hafter hr with ha | ha
  · omega
  · omega
  · exact ⟨hb.1, ha.1⟩
  · omega

/-! ## Literal leader and count frames -/

/-- Pointwise leader projection of one centered packaged step from its two
local outputs. -/
theorem step_leaders_eq_of_local {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (selected : Fin n)
    (hl : (CenteredRenewal.transition hk (C selected)
        (C (ring.rightNeighbor selected))).1.leader = (C selected).leader)
    (hr : (CenteredRenewal.transition hk (C selected)
        (C (ring.rightNeighbor selected))).2.leader =
      (C (ring.rightNeighbor selected)).leader) :
    ∀ i : Fin n, (step hk ring C selected i).leader = (C i).leader := by
  intro i
  have hre := rightNeighbor_ne_self ring hn2 selected
  by_cases his : i = selected
  · subst i
    simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre]
      using hl
  · by_cases hir : i = ring.rightNeighbor selected
    · subst i
      simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre,
        his] using hr
    · simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        his, hir]

/-- Exact physical count equation for a centered step deleting only its
responder leader. -/
theorem step_leaderCount_single_drop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (selected : Fin n)
    (hl : (CenteredRenewal.transition hk (C selected)
        (C (ring.rightNeighbor selected))).1.leader = (C selected).leader)
    (hbefore : (C (ring.rightNeighbor selected)).leader = true)
    (hafter : (CenteredRenewal.transition hk (C selected)
        (C (ring.rightNeighbor selected))).2.leader = false) :
    leaderCount (step hk ring C selected) + 1 = leaderCount C := by
  apply bitCount_single_drop
    (fun i => (C i).leader)
    (fun i => (step hk ring C selected i).leader)
    (ring.rightNeighbor selected) hbefore
  · have hre := rightNeighbor_ne_self ring hn2 selected
    simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre]
      using hafter
  · intro i hir
    have hre := rightNeighbor_ne_self ring hn2 selected
    by_cases his : i = selected
    · subst i
      simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre]
        using hl
    · simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        his, hir]

/-- Exact physical count equation for a centered step creating only its
selected initiator leader. -/
theorem step_leaderCount_single_birth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (selected : Fin n)
    (hbefore : (C selected).leader = false)
    (hafter : (step hk ring C selected selected).leader = true)
    (hother : ∀ i : Fin n, i ≠ selected →
      (step hk ring C selected i).leader = (C i).leader) :
    leaderCount (step hk ring C selected) = leaderCount C + 1 := by
  exact bitCount_single_birth
    (fun i => (C i).leader)
    (fun i => (step hk ring C selected i).leader)
    selected hbefore hafter hother

/-- A physical leader frame transports the cut count across the exact
successor-barrier convention, including the possible cut rotation. -/
theorem cut_count_eq_of_leader_frame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail selected : Fin n)
    (hframe : ∀ i : Fin n, (after i).leader = (before i).leader) :
    leaderCount
        (cutView ring (postBarrierTail hk ring before tail selected) after) =
      leaderCount (cutView ring tail before) := by
  have hold : leaderCount (cutView ring tail after) =
      leaderCount (cutView ring tail before) := by
    apply leaderCount_eq_of_leaders_eq
    intro i
    exact hframe (cutPos ring tail i)
  by_cases hready : CenteredRenewal.AdvanceReady hk ring before selected
  · simp only [postBarrierTail, hready, if_true]
    rw [cutView_nextBarrier, leaderCount_rotateCut]
    exact hold
  · simpa [postBarrierTail, hready] using hold

/-- A single physical deletion gives the same single-deletion equation in a
fixed physical cut. -/
theorem cut_count_single_drop {n k : Nat} (ring : DirectedRing n)
    (before after : Fin n → State k) (tail victim : Fin n)
    (hbefore : (before victim).leader = true)
    (hafter : (after victim).leader = false)
    (hother : ∀ i : Fin n, i ≠ victim →
      (after i).leader = (before i).leader) :
    leaderCount (cutView ring tail after) + 1 =
      leaderCount (cutView ring tail before) := by
  apply bitCount_single_drop
    (fun i => ((cutView ring tail before) i).leader)
    (fun i => ((cutView ring tail after) i).leader)
    (cutCoord ring tail victim)
  · simpa [cutView] using hbefore
  · simpa [cutView] using hafter
  · intro i hi
    apply hother
    intro hpos
    apply hi
    calc
      i = cutCoord ring tail (cutPos ring tail i) :=
        (cutCoord_cutPos ring tail i).symm
      _ = cutCoord ring tail victim := congrArg (cutCoord ring tail) hpos

/-- A single physical birth gives the same birth equation after switching to
the exact post-step cut. -/
theorem cut_count_single_birth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail selected : Fin n) (hselected : selected = tail)
    (hbefore : (before tail).leader = false)
    (hafter : (after tail).leader = true)
    (hother : ∀ i : Fin n, i ≠ tail →
      (after i).leader = (before i).leader) :
    leaderCount
        (cutView ring (postBarrierTail hk ring before tail selected) after) =
      leaderCount (cutView ring tail before) + 1 := by
  subst selected
  have hold : leaderCount (cutView ring tail after) =
      leaderCount (cutView ring tail before) + 1 := by
    apply bitCount_single_birth
      (fun i => ((cutView ring tail before) i).leader)
      (fun i => ((cutView ring tail after) i).leader)
      (cutCoord ring tail tail)
    · simpa [cutView] using hbefore
    · simpa [cutView] using hafter
    · intro i hi
      apply hother
      intro hpos
      apply hi
      calc
        i = cutCoord ring tail (cutPos ring tail i) :=
          (cutCoord_cutPos ring tail i).symm
        _ = cutCoord ring tail tail := congrArg (cutCoord ring tail) hpos
  by_cases hready : CenteredRenewal.AdvanceReady hk ring before tail
  · simp only [postBarrierTail, hready, if_true]
    rw [cutView_nextBarrier, leaderCount_rotateCut]
    exact hold
  · simpa [postBarrierTail, hready] using hold

/-- Every genuine centered barrier advance resets the exact new tail phase to
zero.  The equality identifying the selected edge with the current tail is
explicit because this lemma is also consumed outside a one-barrier wrapper. -/
theorem advance_new_tail_phase_false {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (tail selected : Fin n) (hselected : selected = tail)
    (hready : CenteredRenewal.AdvanceReady hk ring C selected) :
    (step hk ring C selected
      (postBarrierTail hk ring C tail selected)).phase = false := by
  subst selected
  rcases hready with ⟨hbar, hphase⟩
  have hre := rightNeighbor_ne_self ring hn2 tail
  have htrans : CenteredRenewal.transition hk (C tail)
      (C (ring.rightNeighbor tail)) =
      (probeHitsBarrier (C tail),
        { C (ring.rightNeighbor tail) with
          label := succLabel hk (C tail).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact CenteredRenewal.barrierStep_phase_one hk _ _ hphase
  have hready' : CenteredRenewal.AdvanceReady hk ring C tail :=
    ⟨hbar, hphase⟩
  rw [show postBarrierTail hk ring C tail tail = ring.rightNeighbor tail by
    simp [postBarrierTail, hready']]
  simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans, hre]

/-! ## The unique-later-shield witness in the deletion case -/

/-- If deleting one leader is the only leader change, probes are framed, and
danger appears, then one pre-state probe used the deleted leader as its unique
strictly-later shield. -/
theorem exists_last_shield_of_single_death {n k : Nat}
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail victim : Fin n)
    (hother : ∀ i : Fin n, i ≠ victim →
      (after i).leader = (before i).leader)
    (hprobes : ∀ i : Fin n, (after i).probe = (before i).probe)
    (hbefore : ¬ Dangerous (cutView ring tail before))
    (hafter : Dangerous (cutView ring tail after)) :
    ∃ p : Fin n,
      (before p).probe = true ∧
        (cutCoord ring tail p).val < (cutCoord ring tail victim).val ∧
        ∀ ell : Fin n, (before ell).leader = true →
          (cutCoord ring tail p).val < (cutCoord ring tail ell).val →
          ell = victim := by
  obtain ⟨p, hpAfter, hpNoShield⟩ := hafter
  have hpBefore : ((cutView ring tail before) p).probe = true := by
    change (before (cutPos ring tail p)).probe = true
    rw [← hprobes (cutPos ring tail p)]
    simpa [cutView] using hpAfter
  have hsafe := (not_dangerous_iff (cutView ring tail before)).1 hbefore
  obtain ⟨ell, hpell, hell⟩ := hsafe p hpBefore
  have hunique : ∀ j : Fin n,
      ((cutView ring tail before) j).leader = true → p.val < j.val →
      j = cutCoord ring tail victim := by
    intro j hj hjlater
    apply Classical.byContradiction
    intro hjne
    apply hpNoShield
    refine ⟨j, hjlater, ?_⟩
    change (after (cutPos ring tail j)).leader = true
    rw [hother]
    · simpa [cutView] using hj
    · intro hpos
      apply hjne
      calc
        j = cutCoord ring tail (cutPos ring tail j) :=
          (cutCoord_cutPos ring tail j).symm
        _ = cutCoord ring tail victim := congrArg (cutCoord ring tail) hpos
  have hellVictim : ell = cutCoord ring tail victim :=
    hunique ell hell hpell
  refine ⟨cutPos ring tail p, ?_, ?_, ?_⟩
  · simpa [cutView] using hpBefore
  · simpa [hellVictim] using hpell
  · intro q hq hqLater
    have hqCut :
        ((cutView ring tail before) (cutCoord ring tail q)).leader = true := by
      simpa [cutView] using hq
    have hcoord := hunique (cutCoord ring tail q) hqCut (by simpa using hqLater)
    have hpos := congrArg (cutPos ring tail) hcoord
    simpa using hpos

/-! ## Branch-local classification -/

/-- A leader frame on an above-floor plateau packages the ordinary case. -/
theorem stablePlateau_of_leader_frame {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n → State k)
    (tail selected : Fin n) (hr : 1 < r)
    (hbefore : PhiAt ring tail before = r)
    (hafter :
      PhiAt ring (postBarrierTail hk ring before tail selected) after = r)
    (hframe : ∀ i : Fin n, (after i).leader = (before i).leader) :
    StablePlateau hk ring before after tail selected := by
  have hphysical : leaderCount after = leaderCount before :=
    leaderCount_eq_of_leaders_eq before after hframe
  have hcut := cut_count_eq_of_leader_frame hk ring before after tail selected
    hframe
  have hdanger := plateau_same_count_dangerous_iff
    (cutView ring tail before)
    (cutView ring (postBarrierTail hk ring before tail selected) after)
    hbefore hafter hr hcut
  exact
    { leader_frame := hframe
      physical_count := hphysical
      cut_count := hcut
      dangerous_iff := hdanger }

/-- Outside the literal nonbarrier leader-hit branch, a nonbarrier centered
interaction frames every physical leader bit. -/
theorem nonbarrier_leader_frame_of_not_hit {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (selected : Fin n)
    (hbar : ¬ IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected)))
    (hnot : ¬ ((C (ring.rightNeighbor selected)).leader = true ∧
      (C (ring.rightNeighbor selected)).bullet = true)) :
    ∀ i : Fin n, (step hk ring C selected i).leader = (C i).leader := by
  apply step_leaders_eq_of_local hk ring hn2 C selected
  · cases hleader : (C (ring.rightNeighbor selected)).leader <;>
      cases hbullet : (C (ring.rightNeighbor selected)).bullet <;>
      cases hprobe : (C selected).probe
    all_goals
      simp [CenteredRenewal.transition, hbar, nonBarrierStep,
        hleader, hbullet, hprobe] at hnot ⊢
  · cases hleader : (C (ring.rightNeighbor selected)).leader <;>
      cases hbullet : (C (ring.rightNeighbor selected)).bullet <;>
      cases hprobe : (C selected).probe
    all_goals
      simp [CenteredRenewal.transition, hbar, nonBarrierStep,
        hleader, hbullet, hprobe] at hnot ⊢

/-- Unless the selected barrier tail is a probed follower, the barrier branch
frames every physical leader bit. -/
theorem barrier_leader_frame_of_not_birth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (selected : Fin n)
    (hbar : IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected)))
    (hnot : ¬ ((C selected).probe = true ∧
      (C selected).leader = false)) :
    ∀ i : Fin n, (step hk ring C selected i).leader = (C i).leader := by
  apply step_leaders_eq_of_local hk ring hn2 C selected
  · cases hphase : (C selected).phase <;>
      cases hprobe : (C selected).probe <;>
      cases hleader : (C selected).leader
    all_goals
      simp [CenteredRenewal.transition, hbar, CenteredRenewal.barrierStep,
        probeHitsBarrier, hphase, hprobe, hleader] at hnot ⊢
  · cases hphase : (C selected).phase <;>
      cases hprobe : (C selected).probe <;>
      cases hleader : (C selected).leader <;>
      cases hheadLeader : (C (ring.rightNeighbor selected)).leader
    all_goals
      simp [CenteredRenewal.transition, hbar, CenteredRenewal.barrierStep,
        probeHitsBarrier, hphase, hprobe, hleader, hheadLeader] at hnot ⊢

/-- The literal nonbarrier leader-hit branch, specialized to an above-floor
rank plateau, is exactly `NonStrictLastDeath`. -/
theorem nonbarrier_plateau_death {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (tail selected : Fin n) (hr : 1 < r)
    (hbar : ¬ IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected)))
    (hleader : (C (ring.rightNeighbor selected)).leader = true)
    (hbullet : (C (ring.rightNeighbor selected)).bullet = true)
    (hbefore : PhiAt ring tail C = r)
    (hafter : PhiAt ring (postBarrierTail hk ring C tail selected)
      (step hk ring C selected) = r) :
    NonStrictLastDeath hk ring C (step hk ring C selected) tail selected := by
  have hre := rightNeighbor_ne_self ring hn2 selected
  have htrans : CenteredRenewal.transition hk (C selected)
      (C (ring.rightNeighbor selected)) =
      (C selected, { C (ring.rightNeighbor selected) with leader := false }) := by
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hbar]
    exact nonBarrierStep_leader_hit _ _ hleader hbullet
  have hrespDies :
      (step hk ring C selected (ring.rightNeighbor selected)).leader = false := by
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans, hre]
  have hother : ∀ i : Fin n, i ≠ ring.rightNeighbor selected →
      (step hk ring C selected i).leader = (C i).leader := by
    intro i hir
    by_cases his : i = selected
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans]
    · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, his,
        hir]
  have hprobes : ∀ i : Fin n,
      (step hk ring C selected i).probe = (C i).probe := by
    intro i
    by_cases his : i = selected
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans]
    · by_cases hir : i = ring.rightNeighbor selected
      · subst i
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          hre]
      · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, his,
          hir]
  have hphysical : leaderCount (step hk ring C selected) + 1 =
      leaderCount C := by
    apply step_leaderCount_single_drop hk ring hn2 C selected
    · simp [htrans]
    · exact hleader
    · simp [htrans]
  have hcut : leaderCount (cutView ring tail (step hk ring C selected)) + 1 =
      leaderCount (cutView ring tail C) :=
    cut_count_single_drop ring C (step hk ring C selected) tail
      (ring.rightNeighbor selected) hleader hrespDies hother
  have hnotReady : ¬ CenteredRenewal.AdvanceReady hk ring C selected := by
    intro hready
    exact hbar hready.1
  have hafterFixed : PhiAt ring tail (step hk ring C selected) = r := by
    simpa [postBarrierTail, hnotReady] using hafter
  have hstatus := plateau_drop_danger_status
    (cutView ring tail C) (cutView ring tail (step hk ring C selected))
    hbefore hafterFixed hr hcut
  have hlast := exists_last_shield_of_single_death ring C
    (step hk ring C selected) tail (ring.rightNeighbor selected)
    hother hprobes hstatus.1 hstatus.2
  exact
    { nonbarrier := hbar
      responder_leader := hleader
      responder_bullet := hbullet
      responder_dies := hrespDies
      other_leaders := hother
      probe_frame := hprobes
      physical_count := hphysical
      cut_count := hcut
      danger_before := hstatus.1
      danger_after := hstatus.2
      last_shield := hlast }

/-- The literal barrier hit on a probed follower tail, specialized to an
above-floor plateau, is exactly `CompensatingTailBirth`.  Both phase zero and
phase one are included; the conditional phase field identifies the latter. -/
theorem barrier_plateau_birth {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (C : Fin n → State k)
    (tail selected : Fin n) (hr : 1 < r)
    (hselected : selected = tail)
    (hbar : IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected)))
    (hprobe : (C tail).probe = true)
    (hfollower : (C tail).leader = false)
    (hbefore : PhiAt ring tail C = r)
    (hafter : PhiAt ring (postBarrierTail hk ring C tail selected)
      (step hk ring C selected) = r) :
    CompensatingTailBirth hk ring C (step hk ring C selected) tail selected := by
  subst selected
  have hre := rightNeighbor_ne_self ring hn2 tail
  have htailBorn : (step hk ring C tail tail).leader = true := by
    cases hphase : (C tail).phase <;>
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        CenteredRenewal.transition, hbar, CenteredRenewal.barrierStep,
        probeHitsBarrier, hprobe, hphase]
  have htailProbe : (step hk ring C tail tail).probe = false := by
    cases hphase : (C tail).phase <;>
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        CenteredRenewal.transition, hbar, CenteredRenewal.barrierStep,
        probeHitsBarrier, hprobe, hphase]
  have htailBullet : (step hk ring C tail tail).bullet = (C tail).bullet := by
    cases hphase : (C tail).phase <;>
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        CenteredRenewal.transition, hbar, CenteredRenewal.barrierStep,
        probeHitsBarrier, hprobe, hphase]
  have hother : ∀ i : Fin n, i ≠ tail →
      (step hk ring C tail i).leader = (C i).leader := by
    intro i hit
    by_cases hihead : i = ring.rightNeighbor tail
    · subst i
      cases hphase : (C tail).phase <;>
        cases hheadLeader : (C (ring.rightNeighbor tail)).leader <;>
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
          CenteredRenewal.transition, hbar, CenteredRenewal.barrierStep,
          probeHitsBarrier, hprobe, hphase, hheadLeader, hre]
    · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hit,
        hihead]
  have hphysical : leaderCount (step hk ring C tail) = leaderCount C + 1 :=
    step_leaderCount_single_birth hk ring C tail hfollower htailBorn hother
  have hcut := cut_count_single_birth hk ring C (step hk ring C tail)
    tail tail rfl hfollower htailBorn hother
  have hstatus := plateau_birth_danger_status
    (cutView ring tail C)
    (cutView ring (postBarrierTail hk ring C tail tail)
      (step hk ring C tail)) hbefore hafter hr hcut
  exact
    { selected_tail := rfl
      tail_probe := hprobe
      tail_follower := hfollower
      tail_born := htailBorn
      tail_probe_cleared := htailProbe
      tail_bullet_preserved := htailBullet
      other_leaders := hother
      physical_count := hphysical
      cut_count := hcut
      danger_before := hstatus.1
      danger_after := hstatus.2
      advance_new_tail_phase_false := fun hready =>
        advance_new_tail_phase_false hk ring hn2 C tail tail rfl hready }

/-! ## Headline trichotomy -/

/-- Literal physical one-step plateau classification for the one-barrier
centered AAFJ protocol.

At rank `r > 1`, equality of the rank before and after one step leaves exactly
three possibilities: the leader vector and danger bit are framed; one
bullet-bearing nonbarrier responder leader dies and creates danger debt; or a
probed follower at the unique barrier tail is born and discharges danger debt.
The post-state is measured at `postBarrierTail`, so phase-one rotation is part
of the statement rather than an implicit change of coordinates. -/
theorem centered_plateau_step_cases {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (C : Fin n → State k)
    (tail selected : Fin n) (hone : OneBarrierAt hk ring C tail)
    (hr : 1 < r) (hbefore : PhiAt ring tail C = r)
    (hafter : PhiAt ring (postBarrierTail hk ring C tail selected)
      (step hk ring C selected) = r) :
    StablePlateau hk ring C (step hk ring C selected) tail selected ∨
      NonStrictLastDeath hk ring C (step hk ring C selected) tail selected ∨
      CompensatingTailBirth hk ring C (step hk ring C selected) tail selected := by
  have hn2 : 1 < n := by omega
  by_cases hbar : IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected))
  · have hselected : selected = tail := by
      apply (hone selected).1
      exact (barrierAt_labelsOf_iff hk ring C selected).2 hbar
    by_cases hbirth : (C selected).probe = true ∧
        (C selected).leader = false
    · right
      right
      apply barrier_plateau_birth hk ring hn2 C tail selected hr hselected
        hbar
      · simpa [hselected] using hbirth.1
      · simpa [hselected] using hbirth.2
      · exact hbefore
      · exact hafter
    · left
      apply stablePlateau_of_leader_frame hk ring C (step hk ring C selected)
        tail selected hr hbefore hafter
      exact barrier_leader_frame_of_not_birth hk ring hn2 C selected hbar
        hbirth
  · by_cases hdeath :
        (C (ring.rightNeighbor selected)).leader = true ∧
          (C (ring.rightNeighbor selected)).bullet = true
    · right
      left
      exact nonbarrier_plateau_death hk ring hn2 C tail selected hr hbar
        hdeath.1 hdeath.2 hbefore hafter
    · left
      apply stablePlateau_of_leader_frame hk ring C (step hk ring C selected)
        tail selected hr hbefore hafter
      exact nonbarrier_leader_frame_of_not_hit hk ring hn2 C selected hbar
        hdeath

/-- In canonical coordinates, cutting the literal post-step state at its exact
barrier successor is definitionally the `Rank.cutSuccessor` view. -/
theorem cutView_postBarrierTail_step_eq_cutSuccessor {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (X : Fin n → State k)
    (selected : Fin n) :
    cutView ring
        (postBarrierTail hk ring X (tailCoord ring) selected)
        (step hk ring X selected) =
      Rank.cutSuccessor hk ring X selected := by
  by_cases hready : CenteredRenewal.AdvanceReady hk ring X selected
  · unfold Rank.cutSuccessor
    simp only [hready, if_true, postBarrierTail]
    rw [cutView_nextBarrier, cutView_tailCoord_identity]
    rfl
  · unfold Rank.cutSuccessor
    simp only [hready, if_false, postBarrierTail]
    exact cutView_tailCoord_identity ring (step hk ring X selected)

/-- Canonical-coordinate form of `centered_plateau_step_cases`.  This is the
minimal interface for consumers whose invariant is already stated using
`Rank.cutSuccessor`; the returned cases still name the literal physical
initiator, responder, and old barrier tail. -/
theorem canonical_plateau_step_cases {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (X : Fin n → State k)
    (hbar : CanonicalOneBarrier hk ring X) (selected : Fin n)
    (hr : 1 < r) (hbefore : Phi X = r)
    (hafter : Phi (Rank.cutSuccessor hk ring X selected) = r) :
    StablePlateau hk ring X (step hk ring X selected) (tailCoord ring)
        selected ∨
      NonStrictLastDeath hk ring X (step hk ring X selected)
        (tailCoord ring) selected ∨
      CompensatingTailBirth hk ring X (step hk ring X selected)
        (tailCoord ring) selected := by
  have hone := canonicalOneBarrier_oneBarrierAt_tail hk ring X hbar
  apply centered_plateau_step_cases hk ring hn3 X (tailCoord ring) selected
    hone hr
  · simpa [PhiAt] using hbefore
  · change Phi
      (cutView ring (postBarrierTail hk ring X (tailCoord ring) selected)
        (step hk ring X selected)) = r
    rw [cutView_postBarrierTail_step_eq_cutSuccessor]
    exact hafter

end PlateauCases
end CenteredRenewal
end AAFJPK
