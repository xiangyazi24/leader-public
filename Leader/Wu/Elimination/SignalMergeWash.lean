import Leader.Wu.Elimination.LabelFreeElimination
import Leader.Wu.RaceEntrance.ColourCoupling
import Leader.Core.BalancedFailureRestart

/-!
# Physical signal washing after a merge

All local rows below are the actual modulus-one K2 row used by the finite
label-free component. Signal disorder is allowed. The right-side service
will remove the exposed right signal support while retaining pre-existing
left-prefix disorder; it must not claim to repair an arbitrary whole gap
using only the short right side.
-/

namespace SignalMergeWash

open PPLLRepair LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkKernelC
  LDTwoGapFrame LDSinkTwoGapEpochSuccessor LDSinkBoundedKernel
  LDSinkTwoGapRaceEntranceLocalService LDSinkTwoGapRaceEntranceColourCoupling

set_option autoImplicit false

variable {n : Nat}

abbrev Config (n : Nat) := Fin n → AgentState 1

/-- The exact existing row, with no signal-order or label premise. -/
abbrev post (G : GapFrame n) (C : Config n) (e : Fin n) : Config n :=
  sinkStepC (by decide) G C e

private theorem unit_alignment (l r : AgentState 1) :
    r.label = nextLabel (by decide) l := Subsingleton.elim _ _

/-- A zero responder bullet lets a follower's positive signal advance one
actual edge, even when the responder is the right endpoint leader. -/
theorem signal_advance_pair (l r : AgentState 1)
    (hl : l.leader = false) (hs : l.signal_B = 1)
    (hrs : r.signal_B = 0) (hrb : r.bullet = 0) :
    sinkKernelC (by decide) l r = (l, { r with signal_B := 1 }) := by
  have ha := unit_alignment l r
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hs, hrs, hrb,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink, nextLabel] at ha ⊢
  rw [ha]
  rfl

/-- A nonzero incoming bullet instead clears the signal front and becomes
the physical left-moving sweep bullet in the same raw interaction. -/
theorem signal_to_wave_pair (l r : AgentState 1)
    (hl : l.leader = false) (hrs : r.signal_B = 0) (hrb : r.bullet ≠ 0) :
    sinkKernelC (by decide) l r =
      ({ l with bullet := r.bullet, signal_B := 0 },
       { r with bullet := 0, signal_B := 0 }) :=
  quiet_transfer_pair (by decide) l r hl hrs hrb (unit_alignment l r)

/-- Incoming endpoint FIRE creates a sweep already one cell into the gap. -/
theorem signal_endpoint_incoming_pair (l r : AgentState 1)
    (hl : l.leader = false) (hr : r.leader = true) (hs : r.signal_B = 1) :
    sinkKernelC (by decide) l r =
      ({ l with bullet := 1, signal_B := 0 },
       { r with bullet := 0, shield := false, signal_B := 0 }) :=
  incoming_fire_pair (by decide) l r hl hr hs (unit_alignment l r)

/-- No complete K2 row clears a nonzero initiator bullet. MOVE either
frames it or replaces it by a different nonzero incoming bullet. -/
theorem kernel_left_nonzero (l r : AgentState 1) (hb : l.bullet ≠ 0) :
    (sinkKernelC (by decide) l r).1.bullet ≠ 0 := by
  rcases fin3_cases l.bullet with hlb | hlb | hlb
  · exact (hb hlb).elim
  all_goals
    rcases fin3_cases r.bullet with hrb | hrb | hrb <;>
      rcases fin2_cases l.signal_B with hls | hls <;>
      rcases fin2_cases r.signal_B with hrs | hrs <;>
      cases hll : l.leader <;> cases hrl : r.leader <;> cases hsh : l.shield <;>
      simp [sinkKernelC, eliminateLeadersNoCollisionFire, absorbProtectedMove,
        eliminateLeadersNoCollisionZeroLeaderEgressMove,
        eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
        hlb, hrb, hls, hrs, hll, hrl, hsh]
  all_goals split <;> decide

/-- Left signals are only framed or cleared by a complete K2 interaction. -/
theorem kernel_left_signal_zero (l r : AgentState 1) (hs : l.signal_B = 0) :
    (sinkKernelC (by decide) l r).1.signal_B = 0 := by
  rcases fin3_cases r.bullet with hrb | hrb | hrb <;>
    rcases fin2_cases r.signal_B with hrs | hrs <;>
    cases hll : l.leader <;> cases hrl : r.leader <;> cases hsh : l.shield <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire, absorbProtectedMove,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
      hrb, hs, hrs, hll, hrl, hsh]
  all_goals split <;> rfl

/-- A zero suffix receives no signal from a zero follower source. A sweep
bullet also blocks any positive source by clearing it before SIGNAL. -/
theorem kernel_right_signal_zero (l r : AgentState 1)
    (hl : l.leader = false) (hrs : r.signal_B = 0)
    (hs : l.signal_B = 0 ∨ r.bullet ≠ 0) :
    (sinkKernelC (by decide) l r).2.signal_B = 0 := by
  rcases hs with hls | hrb
  · by_cases hb : r.bullet = 0
    · have ha := unit_alignment l r
      simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hls, hrs, hb,
        absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
        eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink, nextLabel] at ha ⊢
      rw [ha]
      intro _
      rfl
    · rw [signal_to_wave_pair l r hl hrs hb]
  · rw [signal_to_wave_pair l r hl hrs hrb]

/-- A follower's positive signal is retained when it is a responder. The
only local way to clear a front is therefore its outgoing MOVE, or endpoint
FIRE when the front is itself the right leader. -/
theorem kernel_right_follower_signal_one (l r : AgentState 1)
    (hr : r.leader = false) (hrs : r.signal_B = 1) :
    (sinkKernelC (by decide) l r).2.signal_B = 1 := by
  have ha : r.label = (0 : Fin 1) := Subsingleton.elim _ _
  rcases fin3_cases r.bullet with hrb | hrb | hrb <;>
    rcases fin2_cases l.signal_B with hls | hls <;>
    cases hll : l.leader <;> cases hsh : l.shield <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire, absorbProtectedMove,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
      hr, hrs, hrb, hls, hll, hsh, ha]
  all_goals rfl

/-- Present geometry only; signal order is deliberately absent. -/
def GapShape (G : GapFrame n) (C : Config n) : Prop :=
  GapEndpointsPresent G C ∧ GapInteriorFollowers G C

/-- Signals from `t` through the right leader are all zero. -/
def ZeroSuffix (G : GapFrame n) (C : Config n) (t : Nat) : Prop :=
  ∀ j, t ≤ j → j ≤ G.d → (C (G.pos j)).signal_B = 0

/-- A real bullet carries a cleared signal suffix behind it. -/
def Sweep (G : GapFrame n) (C : Config n) (t : Nat) : Prop :=
  (C (G.pos t)).bullet ≠ 0 ∧ ZeroSuffix G C t

/-- A rightmost existing signal, before it advances or creates a sweep. -/
def SignalFront (G : GapFrame n) (C : Config n) (t : Nat) : Prop :=
  (C (G.pos t)).signal_B = 1 ∧ ZeroSuffix G C (t + 1)

/-- The useful right-sector repair target; old left disorder is not hidden. -/
def RightClear (G : GapFrame n) (cut : Nat) (C : Config n) : Prop :=
  ZeroSuffix G C (cut + 1)

private theorem predecessor_of_head (G : GapFrame n) (e : Fin n)
    (t : Nat) (ht : 1 ≤ t) (he : G.ring.rightNeighbor e = G.pos t) :
    e = G.pos (t - 1) := by
  have hh : G.ring.rightNeighbor e = G.ring.rightNeighbor (G.pos (t - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel ht] using he
  have hv := congrArg Fin.val hh
  change (e.val + 1) % n = ((G.pos (t - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (G.pos (t - 1)).isLt
  apply Fin.ext
  by_cases ha : e.val + 1 < n <;>
    by_cases hb : (G.pos (t - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hn : (G.pos (t - 1)).val + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hn : e.val + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega

private theorem at_left (G : GapFrame n) (C : Config n) (t : Nat) :
    post G C (G.pos t) (G.pos t) =
      (sinkKernelC (by decide) (C (G.pos t)) (C (G.pos (t + 1)))).1 := by
  simp [post, sinkStepC, updatePair, gap_rightNeighbor_pos]

private theorem at_right (G : GapFrame n) (C : Config n)
    (t : Nat) (ht : 1 ≤ t) (htn : t < n) :
    post G C (G.pos (t - 1)) (G.pos t) =
      (sinkKernelC (by decide) (C (G.pos (t - 1))) (C (G.pos t))).2 := by
  have hne := G.pos_ne htn (by omega : t - 1 < n) (by omega : t ≠ t - 1)
  simp [post, sinkStepC, updatePair, gap_rightNeighbor_pos, Nat.sub_add_cancel ht, hne]

private theorem at_other (G : GapFrame n) (C : Config n) (e x : Fin n)
    (hl : x ≠ e) (hr : x ≠ G.ring.rightNeighbor e) : post G C e x = C x :=
  sinkStepC_other (by decide) G C e x hl hr

/-- The geometric carrier stays valid on every actual nondeleting row,
without a signal-order invariant. -/
theorem gapShape_step (G : GapFrame n) (C : Config n) (hg : GapShape G C)
    (e : Fin n) (hd : ¬ EndpointDeleted G (post G C e)) :
    GapShape G (post G C e) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hh : (post G C e (G.pos 0)).leader ≠ false :=
      fun h => hd (Or.inl h)
    cases hb : (post G C e (G.pos 0)).leader <;> simp_all
  · have hh : (post G C e (G.pos G.d)).leader ≠ false :=
      fun h => hd (Or.inr h)
    cases hb : (post G C e (G.pos G.d)).leader <;> simp_all
  · intro t ht htd
    exact sinkStepC_follower_preserved (by decide) G C e _ (hg.2 t ht htd)

/-- Away from the one entering edge, arbitrary raw interactions preserve
a zero suffix. The left endpoint of this suffix need not be a leader. -/
theorem zeroSuffix_off_source (G : GapFrame n) (C : Config n)
    (hf : GapInteriorFollowers G C) (t : Nat) (ht : 2 ≤ t)
    (hz : ZeroSuffix G C t) (e : Fin n) (he : e ≠ G.pos (t - 1)) :
    ZeroSuffix G (post G C e) t := by
  intro j htj hjd
  have hjn : j < n := Nat.lt_of_le_of_lt hjd G.hdn
  have hj1 : 1 ≤ j := by omega
  by_cases hjl : G.pos j = e
  · rw [← hjl, at_left]
    exact kernel_left_signal_zero _ _ (hz j htj hjd)
  · by_cases hjr : G.ring.rightNeighbor e = G.pos j
    · have hp := predecessor_of_head G e j hj1 hjr
      have hjt : t < j := by
        by_cases hh : t = j
        · exact (he (by simpa only [hh] using hp)).elim
        · omega
      rw [hp, at_right G C j hj1 hjn]
      exact kernel_right_signal_zero _ _ (hf (j - 1) (by omega) (by omega))
        (hz j htj hjd) (Or.inl (hz (j - 1) (by omega) (by omega)))
    · rw [at_other G C e (G.pos j) hjl (fun h => hjr h.symm)]
      exact hz j htj hjd

/-- The sweep position follows the same real predecessor-edge service. -/
def nextSweep (G : GapFrame n) (t : Nat) (e : Fin n) : Nat :=
  if e = G.pos (t - 1) then t - 1 else t

/-- A physical sweep survives all raw off-target interactions and moves
one cell left exactly at its predecessor. All suffix signals remain zero.
No assumption is made about signals or bullets before the sweep. -/
theorem sweep_step (G : GapFrame n) (C : Config n)
    (hf : GapInteriorFollowers G C) (t : Nat) (ht : 3 ≤ t) (htd : t ≤ G.d)
    (hw : Sweep G C t) (e : Fin n) :
    Sweep G (post G C e) (nextSweep G t e) := by
  have htn : t < n := Nat.lt_of_le_of_lt htd G.hdn
  have hnext : t - 1 ≤ nextSweep G t e ∧ nextSweep G t e ≤ t := by
    unfold nextSweep
    split <;> omega
  constructor
  · by_cases he : e = G.pos (t - 1)
    · rw [nextSweep, if_pos he, he, at_left, Nat.sub_add_cancel (by omega : 1 ≤ t)]
      rw [signal_to_wave_pair _ _ (hf (t - 1) (by omega) (by omega))
        (hw.2 t (Nat.le_refl _) htd) hw.1]
      exact hw.1
    · rw [nextSweep, if_neg he]
      by_cases hl : G.pos t = e
      · rw [← hl, at_left]
        exact kernel_left_nonzero _ _ hw.1
      · have hr : G.pos t ≠ G.ring.rightNeighbor e :=
          fun h => he (predecessor_of_head G e t (by omega) h.symm)
        rw [at_other G C e (G.pos t) hl hr]
        exact hw.1
  · intro j hnj hjd
    have hjn : j < n := Nat.lt_of_le_of_lt hjd G.hdn
    have hj2 : 2 ≤ j := by omega
    by_cases hjl : G.pos j = e
    · rw [← hjl, at_left]
      by_cases hjt : t ≤ j
      · exact kernel_left_signal_zero _ _ (hw.2 j hjt hjd)
      · have he : j + 1 = t := by omega
        rw [he, signal_to_wave_pair _ _ (hf j (by omega) (by omega))
          (hw.2 t (Nat.le_refl _) htd) hw.1]
    · by_cases hjr : G.ring.rightNeighbor e = G.pos j
      · have hp := predecessor_of_head G e j (by omega) hjr
        have hjt : t ≤ j := by
          by_cases he : e = G.pos (t - 1)
          · have hh : G.pos j = G.pos t := by
              rw [← hjr, he, gap_rightNeighbor_pos, Nat.sub_add_cancel (by omega : 1 ≤ t)]
            have hv := congrArg G.off hh
            rw [G.off_pos j hjn, G.off_pos t htn] at hv
            omega
          · simpa only [nextSweep, if_neg he] using hnj
        rw [hp, at_right G C j (by omega) hjn]
        apply kernel_right_signal_zero _ _ (hf (j - 1) (by omega) (by omega))
          (hw.2 j hjt hjd)
        by_cases he : j = t
        · subst j
          exact Or.inr hw.1
        · exact Or.inl (hw.2 (j - 1) (by omega) (by omega))
      · have hjt : t ≤ j := by
          by_cases he : e = G.pos (t - 1)
          · by_cases hjt : t ≤ j
            · exact hjt
            · have hh : j = t - 1 := by omega
              exact (hjl (by rw [hh, he])).elim
          · simpa only [nextSweep, if_neg he] using hnj
        rw [at_other G C e (G.pos j) hjl (fun h => hjr h.symm)]
        exact hw.2 j hjt hjd

private theorem at_right_succ (G : GapFrame n) (C : Config n)
    (t : Nat) (ht : t + 1 < n) :
    post G C (G.pos t) (G.pos (t + 1)) =
      (sinkKernelC (by decide) (C (G.pos t)) (C (G.pos (t + 1)))).2 := by
  simpa only [Nat.add_sub_cancel] using at_right G C (t + 1) (by omega) ht

/-- A rightmost signal is preserved by every edge except its outgoing
service or, when it is at the right leader, that leader's incoming FIRE. -/
theorem signalFront_off (G : GapFrame n) (C : Config n) (hg : GapShape G C)
    (t : Nat) (ht : 1 ≤ t) (htd : t ≤ G.d) (hs : SignalFront G C t)
    (e : Fin n) (he : e ≠ G.pos t)
    (hin : t = G.d → e ≠ G.pos (t - 1)) :
    SignalFront G (post G C e) t := by
  have htn : t < n := Nat.lt_of_le_of_lt htd G.hdn
  constructor
  · by_cases hr : G.ring.rightNeighbor e = G.pos t
    · have hp := predecessor_of_head G e t ht hr
      have hlt : t < G.d := by
        by_cases hd : t = G.d
        · exact (hin hd hp).elim
        · omega
      rw [hp, at_right G C t ht htn]
      exact kernel_right_follower_signal_one _ _ (hg.2 t ht hlt) hs.1
    · rw [at_other G C e (G.pos t) (Ne.symm he) (fun h => hr h.symm)]
      exact hs.1
  · exact zeroSuffix_off_source G C hg.2 (t + 1) (by omega) hs.2 e
      (by simpa only [Nat.add_sub_cancel] using he)

/-- The one front edge either advances the signal by one or creates an
actual sweep bullet. Both branches clear the whole suffix they certify. -/
theorem signalFront_service (G : GapFrame n) (C : Config n)
    (hg : GapShape G C) (t : Nat) (ht : 1 ≤ t) (htd : t < G.d)
    (hs : SignalFront G C t) :
    if (C (G.pos (t + 1))).bullet = 0 then
      SignalFront G (post G C (G.pos t)) (t + 1)
    else Sweep G (post G C (G.pos t)) t := by
  have htn : t < n := Nat.lt_trans htd G.hdn
  have htn' : t + 1 < n := Nat.lt_of_le_of_lt (by omega) G.hdn
  have hright := hs.2 (t + 1) (Nat.le_refl _) (by omega)
  have htail : ZeroSuffix G (post G C (G.pos t)) (t + 2) := by
    apply zeroSuffix_off_source G C hg.2 (t + 2) (by omega)
      (fun j hj hjd => hs.2 j (by omega) hjd)
    have he : t + 2 - 1 = t + 1 := by omega
    rw [he]
    exact G.pos_ne htn htn' (by omega)
  by_cases hb : (C (G.pos (t + 1))).bullet = 0
  · rw [if_pos hb]
    constructor
    · rw [at_right_succ G C t htn', signal_advance_pair _ _ (hg.2 t ht htd) hs.1 hright hb]
    · exact htail
  · rw [if_neg hb]
    have hrow := signal_to_wave_pair (C (G.pos t)) (C (G.pos (t + 1)))
      (hg.2 t ht htd) hright hb
    constructor
    · rw [at_left, hrow]
      exact hb
    · intro j htj hjd
      by_cases he : j = t
      · subst j
        rw [at_left, hrow]
      · by_cases he' : j = t + 1
        · subst j
          rw [at_right_succ G C t htn', hrow]
        · exact htail j (by omega) hjd

/-- Outgoing FIRE at the right endpoint starts a real live sweep. -/
theorem signalFront_endpoint_out (G : GapFrame n) (C : Config n)
    (hg : GapShape G C) (hs : SignalFront G C G.d) :
    Sweep G (post G C (G.pos G.d)) G.d := by
  have hrow := kernelC_outgoing_fire_left (by decide) (C (G.pos G.d))
    (C (G.pos (G.d + 1))) hg.1.2 hs.1
  constructor
  · rw [at_left, hrow]
    exact (by decide : (2 : Fin 3) ≠ 0)
  · intro j hj hjd
    have he : j = G.d := by omega
    subst j
    rw [at_left, hrow]

/-- Incoming FIRE starts the real dummy sweep one cell inside the gap. -/
theorem signalFront_endpoint_in (G : GapFrame n) (C : Config n)
    (hg : GapShape G C) (hs : SignalFront G C G.d) :
    Sweep G (post G C (G.pos (G.d - 1))) (G.d - 1) := by
  have hd := G.hd
  have hrow := signal_endpoint_incoming_pair (C (G.pos (G.d - 1))) (C (G.pos G.d))
    (hg.2 (G.d - 1) (by omega) (by omega)) hg.1.2 hs.1
  constructor
  · rw [at_left, Nat.sub_add_cancel (by omega : 1 ≤ G.d), hrow]
    exact (by decide : (1 : Fin 3) ≠ 0)
  · intro j hj hjd
    have he : j = G.d - 1 ∨ j = G.d := by omega
    rcases he with rfl | rfl
    · rw [at_left, Nat.sub_add_cancel (by omega : 1 ≤ G.d), hrow]
    · rw [at_right G C G.d (by omega) G.hdn, hrow]

/-! The marker below records an existing physical signal or bullet. Every
scheduler letter still applies the original row, including off-service letters. -/

inductive WashMark where
  | signal : Nat → WashMark
  | sweep : Nat → WashMark

def WashMark.pos : WashMark → Nat
  | .signal t | .sweep t => t

def Tracks (G : GapFrame n) (C : Config n) : WashMark → Prop
  | .signal t => SignalFront G C t
  | .sweep t => Sweep G C t

def markStep (G : GapFrame n) (C : Config n) (e : Fin n) : WashMark → WashMark
  | .signal t =>
      if t = G.d then
        if e = G.pos t then .sweep t
        else if e = G.pos (t - 1) then .sweep (t - 1) else .signal t
      else if e = G.pos t then
        if (C (G.pos (t + 1))).bullet = 0 then .signal (t + 1) else .sweep t
      else .signal t
  | .sweep t => .sweep (nextSweep G t e)

def markWork (G : GapFrame n) (cut : Nat) : WashMark → Nat
  | .signal t => 2 * G.d - cut - t + 1
  | .sweep t => t - cut

def markPort (G : GapFrame n) : WashMark → Fin n
  | .signal t => G.pos t
  | .sweep t => G.pos (t - 1)

theorem markStep_tracks (G : GapFrame n) (C : Config n) (hg : GapShape G C)
    (m : WashMark) (hm : 3 ≤ m.pos) (hmd : m.pos ≤ G.d) (ht : Tracks G C m)
    (e : Fin n) : Tracks G (post G C e) (markStep G C e m) := by
  cases m with
  | sweep t => exact sweep_step G C hg.2 t hm hmd ht e
  | signal t =>
      change SignalFront G C t at ht
      change 3 ≤ t at hm
      change t ≤ G.d at hmd
      simp only [markStep]
      by_cases hd : t = G.d
      · rw [if_pos hd]
        by_cases he : e = G.pos t
        · rw [if_pos he]
          subst t
          subst e
          exact signalFront_endpoint_out G C hg ht
        · rw [if_neg he]
          by_cases hi : e = G.pos (t - 1)
          · rw [if_pos hi]
            subst t
            subst e
            exact signalFront_endpoint_in G C hg ht
          · rw [if_neg hi]
            exact signalFront_off G C hg t (by omega) hmd ht e he (fun _ => hi)
      · rw [if_neg hd]
        by_cases he : e = G.pos t
        · rw [if_pos he]
          subst e
          have hs := signalFront_service G C hg t (by omega) (by omega) ht
          split <;> simp_all only [Tracks, if_true, if_false]
        · rw [if_neg he]
          exact signalFront_off G C hg t (by omega) hmd ht e he
            (fun h => (hd h).elim)

theorem markStep_bounds (G : GapFrame n) (C : Config n) (cut : Nat)
    (m : WashMark) (hc : cut < m.pos) (hd : m.pos ≤ G.d) (e : Fin n) :
    cut ≤ (markStep G C e m).pos ∧ (markStep G C e m).pos ≤ G.d := by
  cases m with
  | signal t =>
      by_cases h₁ : t = G.d <;> by_cases h₂ : e = G.pos t <;>
        by_cases h₃ : e = G.pos (t - 1) <;>
        by_cases h₄ : (C (G.pos (t + 1))).bullet = 0 <;>
        simp_all [markStep, WashMark.pos] <;> omega
  | sweep t =>
      by_cases he : e = G.pos (t - 1) <;>
        simp_all [markStep, nextSweep, WashMark.pos] <;> omega

theorem markStep_signal_gt (G : GapFrame n) (C : Config n) (cut : Nat)
    (m : WashMark) (hc : cut < m.pos) (e : Fin n) (t : Nat)
    (he : markStep G C e m = .signal t) : cut < t := by
  cases m <;> simp only [markStep, WashMark.pos, nextSweep] at *
  all_goals repeat' first | split at he
  all_goals simp_all only [WashMark.signal.injEq, reduceCtorEq] <;> omega

theorem markStep_work_le (G : GapFrame n) (C : Config n) (cut : Nat)
    (m : WashMark) (hc : cut < m.pos) (hd : m.pos ≤ G.d) (e : Fin n) :
    markWork G cut (markStep G C e m) ≤ markWork G cut m := by
  cases m with
  | signal t =>
      by_cases h₁ : t = G.d <;> by_cases h₂ : e = G.pos t <;>
        by_cases h₃ : e = G.pos (t - 1) <;>
        by_cases h₄ : (C (G.pos (t + 1))).bullet = 0 <;>
        simp_all [markStep, markWork, WashMark.pos] <;> omega
  | sweep t =>
      by_cases he : e = G.pos (t - 1) <;>
        simp_all [markStep, nextSweep, markWork, WashMark.pos] <;> omega

theorem markStep_work_drop (G : GapFrame n) (C : Config n) (cut : Nat)
    (m : WashMark) (hc : cut < m.pos) (hd : m.pos ≤ G.d) :
    markWork G cut (markStep G C (markPort G m) m) + 1 ≤ markWork G cut m := by
  cases m with
  | signal t =>
      by_cases h₁ : t = G.d <;> by_cases h₂ : (C (G.pos (t + 1))).bullet = 0 <;>
        simp only [markStep, markPort, h₁, h₂, if_true, if_false, markWork, WashMark.pos] at * <;> omega
  | sweep t =>
      simp only [markStep, markPort, nextSweep, if_true, markWork, WashMark.pos] at *
      omega

def WashDone (G : GapFrame n) (cut : Nat) (C : Config n) : Prop :=
  EndpointDeleted G C ∨ RightClear G cut C

structure WashState (G : GapFrame n) (cut : Nat) where
  conf : Config n
  mark : WashMark
  shape : GapShape G conf
  cut_lt : cut < mark.pos
  pos_le : mark.pos ≤ G.d
  tracks : Tracks G conf mark

private theorem wash_next (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (z : WashState G cut) (e : Fin n) (hn : ¬ WashDone G cut (post G z.conf e)) :
    cut < (markStep G z.conf e z.mark).pos := by
  have hb := markStep_bounds G z.conf cut z.mark z.cut_lt z.pos_le e
  have ht := markStep_tracks G z.conf z.shape z.mark (by have := z.cut_lt; omega)
    z.pos_le z.tracks e
  by_cases hh : cut < (markStep G z.conf e z.mark).pos
  · exact hh
  · have he : (markStep G z.conf e z.mark).pos = cut := by omega
    cases hm : markStep G z.conf e z.mark with
    | signal t =>
        have hg := markStep_signal_gt G z.conf cut z.mark z.cut_lt e t hm
        simp only [hm, WashMark.pos] at he
        omega
    | sweep t =>
        simp only [hm, WashMark.pos] at he
        rw [hm] at ht
        exact (hn (.inr (fun j hj hjd => ht.2 j (by omega) hjd))).elim

open FiniteUniformStoppingTree

noncomputable def washStep (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (z : WashState G cut) (e : Fin n) : StopNode (WashState G cut) := by
  classical
  exact if h : WashDone G cut (post G z.conf e) then .success else
    .active ⟨post G z.conf e, markStep G z.conf e z.mark,
      gapShape_step G z.conf z.shape e (fun hd => h (.inl hd)),
      wash_next G cut hc z e h,
      (markStep_bounds G z.conf cut z.mark z.cut_lt z.pos_le e).2,
      markStep_tracks G z.conf z.shape z.mark (by have := z.cut_lt; omega)
        z.pos_le z.tracks e⟩

noncomputable def washWork (G : GapFrame n) (cut : Nat) : StopNode (WashState G cut) → Nat
  | .active z => markWork G cut z.mark
  | .success | .failure => 0

noncomputable def washPotential (G : GapFrame n) (cut : Nat)
    (x : StopNode (WashState G cut)) : Nat := n * washWork G cut x

private theorem wash_child_work (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (z : WashState G cut) (e : Fin n) :
    washWork G cut (washStep G cut hc z e) ≤ markWork G cut (markStep G z.conf e z.mark) := by
  classical
  unfold washStep
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem wash_bellman (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut) :
    NatBellmanSuperSolution (washStep G cut hc) 1 (washPotential G cut) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hl : ∀ e, washWork G cut (washStep G cut hc z e) ≤ washWork G cut (.active z) := by
    intro e
    exact Nat.le_trans (wash_child_work G cut hc z e)
      (markStep_work_le G z.conf cut z.mark z.cut_lt z.pos_le e)
  have hd : washWork G cut (washStep G cut hc z (markPort G z.mark)) + 1 ≤
      washWork G cut (.active z) :=
    Nat.le_trans (Nat.add_le_add_right (wash_child_work G cut hc z _) 1)
      (markStep_work_drop G z.conf cut z.mark z.cut_lt z.pos_le)
  have hs := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => washWork G cut (washStep G cut hc z e)) (washWork G cut (.active z))
    (markPort G z.mark) hl hd
  change 1 * n + (List.ofFn (fun e => n * washWork G cut (washStep G cut hc z e))).sum ≤
    n * (n * washWork G cut (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hh := Nat.mul_le_mul_left n hs
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hh

theorem wash_work_bound (G : GapFrame n) (cut : Nat) (z : WashState G cut) :
    washWork G cut (.active z) ≤ 2 * (G.d - cut) + 1 := by
  have hc := z.cut_lt
  have hd := z.pos_le
  change markWork G cut z.mark ≤ _
  cases hm : z.mark <;> simp only [hm, markWork, WashMark.pos] at * <;> omega

theorem wash_truncated_cost (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (z : WashState G cut) (T : Nat) :
    truncatedActiveCostNumerator (washStep G cut hc) (.active z) T ≤
      n ^ T * (n * (2 * (G.d - cut) + 1)) := by
  have hh := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (washStep G cut hc) 1 (washPotential G cut) (wash_bellman G cut hc) (.active z) T
  exact Nat.le_trans (by simpa only [Nat.one_mul, washPotential] using hh)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left n (wash_work_bound G cut z)))

private theorem wash_no_failure (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (z : WashState G cut) (e : Fin n) : washStep G cut hc z e ≠ .failure := by
  classical
  unfold washStep
  split <;> intro he <;> cases he

theorem wash_half (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut) (z : WashState G cut) :
    n ^ (2 * n * (2 * (G.d - cut) + 1)) ≤
      2 * successCount (washStep G cut hc) (.active z) (2 * n * (2 * (G.d - cut) + 1)) := by
  let T := 2 * n * (2 * (G.d - cut) + 1)
  have hp : 0 < T := Nat.mul_pos (Nat.mul_pos (by decide) G.ring.hn) (by omega)
  have hh := wash_truncated_cost G cut hc z T
  have ha := two_mul_activeCount_le_pow_of_scaled_cost (washStep G cut hc) (.active z)
    hp (by decide : 0 < 1) (num := n * (2 * (G.d - cut) + 1))
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hh)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (washStep G cut hc) (wash_no_failure G cut hc) z T
  have hparts := node_count_partition (washStep G cut hc) (.active z) T
  change n ^ T ≤ 2 * successCount (washStep G cut hc) (.active z) T
  omega

/-- The unmarked process tests the real successor. Its target is a first
hit: later padding is not asserted to preserve right-sector clearance. -/
noncomputable def rawWashStep (G : GapFrame n) (cut : Nat)
    (C : Config n) (e : Fin n) : StopNode (Config n) := by
  classical
  exact if WashDone G cut (post G C e) then .success else .active (post G C e)

noncomputable def rawWashStart (G : GapFrame n) (cut : Nat) (C : Config n) :
    StopNode (Config n) := by
  classical
  exact if WashDone G cut C then .success else .active C

def eraseWash (G : GapFrame n) (cut : Nat) : StopNode (WashState G cut) → StopNode (Config n)
  | .active z => .active z.conf
  | .success => .success
  | .failure => .failure

theorem washStep_erases (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (x : StopNode (WashState G cut)) (e : Fin n) :
    eraseWash G cut (stepNode (washStep G cut hc) x e) =
      stepNode (rawWashStep G cut) (eraseWash G cut x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      by_cases hd : WashDone G cut (post G z.conf e) <;>
        simp [stepNode, washStep, rawWashStep, hd, eraseWash]

private theorem wash_tree_erases (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (w : StopNode (Config n) → Nat) (x : StopNode (WashState G cut)) (T : Nat) :
    treeWeight (washStep G cut hc) (fun y => w (eraseWash G cut y)) x T =
      treeWeight (rawWashStep G cut) w (eraseWash G cut x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      exact ofFn_sum_eq _ _ (fun e => by rw [ih, washStep_erases])

theorem wash_cost_erases (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (x : StopNode (WashState G cut)) (T : Nat) :
    truncatedActiveCostNumerator (washStep G cut hc) x T =
      truncatedActiveCostNumerator (rawWashStep G cut) (eraseWash G cut x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      cases x with
      | success => rfl
      | failure => rfl
      | active z =>
          simp only [truncatedActiveCostNumerator, eraseWash]
          congr 1
          apply ofFn_sum_eq
          intro e
          rw [ih]
          have hh := washStep_erases G cut hc (.active z) e
          exact congrArg (fun y => truncatedActiveCostNumerator (rawWashStep G cut) y T) hh

theorem signalTop_gt_of_not_clear (G : GapFrame n) (cut : Nat) (C : Config n)
    (hn : ¬ RightClear G cut C) : cut < signalTop G C := by
  apply Classical.byContradiction
  intro hh
  apply hn
  intro j hj hjd
  exact signalTop_zero_at G C (by omega) hjd

/-- A current dirty right sector supplies the marker; no future-service
certificate or signal-order premise is part of this construction. -/
def initialWashState (G : GapFrame n) (cut : Nat) (C : Config n)
    (hg : GapShape G C) (hn : ¬ RightClear G cut C) : WashState G cut where
  conf := C
  mark := .signal (signalTop G C)
  shape := hg
  cut_lt := signalTop_gt_of_not_clear G cut C hn
  pos_le := signalTop_le G C
  tracks := ⟨signalTop_one_at G C (by have := signalTop_gt_of_not_clear G cut C hn; omega),
    fun j hj hjd => signalTop_zero_at G C (by omega) hjd⟩

/-- Exact finite expected service numerator, including zero cost when the
right side is already clear. Every charged edge is an original raw edge. -/
theorem right_clear_truncated_cost (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (C : Config n) (hg : GapShape G C) (T : Nat) :
    truncatedActiveCostNumerator (rawWashStep G cut) (rawWashStart G cut C) T ≤
      n ^ T * (n * (2 * (G.d - cut) + 1)) := by
  classical
  by_cases hd : WashDone G cut C
  · simp only [rawWashStart, if_pos hd]
    cases T <;> exact Nat.zero_le _
  · let z := initialWashState G cut C hg (fun hh => hd (.inr hh))
    have hh := wash_truncated_cost G cut hc z T
    rw [wash_cost_erases] at hh
    simpa only [rawWashStart, if_neg hd, eraseWash, z, initialWashState] using hh

/-- A half of the original uniform words hit a clear right sector or an
actual endpoint deletion within `2*n*(2*(d-cut)+1)` interactions. -/
theorem right_clear_half (G : GapFrame n) (cut : Nat) (hc : 2 ≤ cut)
    (C : Config n) (hg : GapShape G C) :
    n ^ (2 * n * (2 * (G.d - cut) + 1)) ≤
      2 * successCount (rawWashStep G cut) (rawWashStart G cut C)
        (2 * n * (2 * (G.d - cut) + 1)) := by
  classical
  by_cases hd : WashDone G cut C
  · simp only [rawWashStart, if_pos hd, successCount, treeWeight_success,
      successWeight, Nat.mul_one]
    omega
  · let z := initialWashState G cut C hg (fun hh => hd (.inr hh))
    have hh := wash_half G cut hc z
    have hw : (fun y : StopNode (WashState G cut) =>
        successWeight (eraseWash G cut y)) = successWeight := by
      funext y
      cases y <;> rfl
    have he := wash_tree_erases G cut hc successWeight (.active z)
      (2 * n * (2 * (G.d - cut) + 1))
    rw [hw] at he
    change successCount (washStep G cut hc) (.active z) _ =
      successCount (rawWashStep G cut) (.active C) _ at he
    rw [he] at hh
    simpa only [rawWashStart, if_neg hd] using hh

/-- A successful stopped word names a prefix of that very word whose
unmodified physical endpoint has the claimed clearance/deletion property. -/
theorem raw_wash_success_prefix (G : GapFrame n) (cut : Nat) (C : Config n)
    (es : List (Fin n))
    (hs : run (stepNode (rawWashStep G cut)) (rawWashStart G cut C) es = .success) :
    ∃ pre suf, es = pre ++ suf ∧ WashDone G cut (run (post G) C pre) := by
  classical
  induction es generalizing C with
  | nil =>
      by_cases hd : WashDone G cut C
      · exact ⟨[], [], rfl, hd⟩
      · simp only [run, rawWashStart, if_neg hd] at hs
        cases hs
  | cons e es ih =>
      by_cases hd : WashDone G cut C
      · exact ⟨[], e :: es, rfl, hd⟩
      · by_cases hh : WashDone G cut (post G C e)
        · exact ⟨[e], es, rfl, hh⟩
        · have ht : run (stepNode (rawWashStep G cut))
              (rawWashStart G cut (post G C e)) es = .success := by
            simpa only [run, rawWashStart, if_neg hd, stepNode, rawWashStep,
              if_neg hh] using hs
          obtain ⟨pre, suf, hp, hdone⟩ := ih (post G C e) ht
          exact ⟨e :: pre, suf, by simp only [List.cons_append, hp], hdone⟩

/-- The same successful scheduler word has the same real prefix endpoint
on the existing finite carrier, with arbitrary labels and controller fields. -/
theorem physical_wash_success_prefix {ψ κ : Nat} (hψ : 0 < ψ)
    (G : GapFrame n) (cut : Nat) (C : Fin n → StateBoundUnifiedCell.UCell ψ κ)
    (es : List (Fin n))
    (hs : run (stepNode (rawWashStep G cut))
      (rawWashStart G cut (LabelFreeElimination.observe C)) es = .success) :
    ∃ pre suf, es = pre ++ suf ∧
      WashDone G cut (LabelFreeElimination.observe
        (run (LabelFreeElimination.step hψ G.ring) C pre)) := by
  obtain ⟨pre, suf, hp, hd⟩ := raw_wash_success_prefix G cut
    (LabelFreeElimination.observe C) es hs
  refine ⟨pre, suf, hp, ?_⟩
  rw [LabelFreeElimination.observe_run]
  exact hd

/-! A real post-merge obstruction to claiming whole-gap repair from an
arbitrary dirty input using only the small right sector. -/

def witnessFrame : TwoGapFrame 8 where
  recovery := ⟨⟨by decide⟩, 0, 4, by decide, by decide⟩
  attack := ⟨⟨by decide⟩, 4, 2, by decide, by decide⟩
  shared := by decide
  length_lt := by decide

def witnessPre (i : Fin 8) : AgentState 1 :=
  { PPLLNoCheckBirthOutputLegitimacy.outputCore (by decide) i with
    leader := decide (i.val = 0 ∨ i.val = 4 ∨ i.val = 6)
    shield := false
    bullet := if i.val = 1 then 1 else if i.val = 5 then 2 else 0
    signal_B := if i.val = 2 ∨ i.val = 5 then 1 else 0 }

def witnessPost : Config 8 := post witnessFrame.attack witnessPre 4

/-- The right gap has length two, and the literal edge four really deletes
the shared leader while leaving a pre-existing left-prefix violation. -/
theorem witness_actual_deletion :
    witnessFrame.recovery.d = 4 ∧ witnessFrame.attack.d = 2 ∧
    (witnessPre 4).leader = true ∧ (witnessPost 4).leader = false ∧
    (witnessPost 1).bullet = 1 ∧ (witnessPost 2).signal_B = 1 := by decide

theorem witness_shape : GapShape (K2GlobalGapClosure.merged witnessFrame) witnessPost := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro t ht htd
  have hd : (K2GlobalGapClosure.merged witnessFrame).d = 6 := rfl
  rw [hd] at htd
  have he : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The half-mass theorem is exercised on a real deleted successor that
still has both old left-prefix disorder and a dirty right sector. -/
theorem witness_not_done : ¬ WashDone (K2GlobalGapClosure.merged witnessFrame) 4 witnessPost := by
  rintro ((hl | hr) | hz)
  · exact (by decide : (witnessPost ((K2GlobalGapClosure.merged witnessFrame).pos 0)).leader ≠ false) hl
  · exact (by decide : (witnessPost ((K2GlobalGapClosure.merged witnessFrame).pos 6)).leader ≠ false) hr
  · have hh := hz 5 (by decide) (by decide)
    exact (by decide : (witnessPost ((K2GlobalGapClosure.merged witnessFrame).pos 5)).signal_B ≠ 0) hh

theorem witness_right_clear_half :
    8 ^ 80 ≤ 2 * successCount (rawWashStep (K2GlobalGapClosure.merged witnessFrame) 4)
      (.active witnessPost) 80 := by
  have hh := right_clear_half (K2GlobalGapClosure.merged witnessFrame) 4
    (by decide) witnessPost witness_shape
  have ht : 2 * 8 * (2 * ((K2GlobalGapClosure.merged witnessFrame).d - 4) + 1) = 80 := rfl
  rw [ht, rawWashStart, if_neg witness_not_done] at hh
  exact hh

private theorem right_word_frames_left (C : Config 8) (es : List (Fin 8))
    (hes : ∀ e, e ∈ es → e = 4 ∨ e = 5) :
    run (post (K2GlobalGapClosure.merged witnessFrame)) C es 1 = C 1 ∧
    run (post (K2GlobalGapClosure.merged witnessFrame)) C es 2 = C 2 := by
  induction es generalizing C with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
      have he := hes e (by simp)
      have hs := ih (post (K2GlobalGapClosure.merged witnessFrame) C e)
        (fun f hf => hes f (by simp [hf]))
      have h1 : post (K2GlobalGapClosure.merged witnessFrame) C e 1 = C 1 := by
        rcases he with rfl | rfl <;>
          exact sinkStepC_other (by decide) _ C _ 1 (by decide) (by decide)
      have h2 : post (K2GlobalGapClosure.merged witnessFrame) C e 2 = C 2 := by
        rcases he with rfl | rfl <;>
          exact sinkStepC_other (by decide) _ C _ 2 (by decide) (by decide)
      exact ⟨hs.1.trans h1, hs.2.trans h2⟩

/-- Any word confined to the small right sector leaves the old left
violation. This refutes a whole-gap wash claim for such a word, but makes
no stochastic runtime lower-bound claim. -/
theorem right_only_word_not_whole_order (es : List (Fin 8))
    (hes : ∀ e, e ∈ es → e = 4 ∨ e = 5) :
    ¬ GapSignalBelowBullets (K2GlobalGapClosure.merged witnessFrame)
      (run (post (K2GlobalGapClosure.merged witnessFrame)) witnessPost es) := by
  obtain ⟨h1, h2⟩ := right_word_frames_left witnessPost es hes
  intro ho
  have hh := ho 1 2 (by decide) (by decide) (by
    change (run (post (K2GlobalGapClosure.merged witnessFrame)) witnessPost es 1).bullet ≠ 0
    rw [h1]
    decide) (by decide) (by decide)
  change (run (post (K2GlobalGapClosure.merged witnessFrame)) witnessPost es 2).signal_B = 0 at hh
  rw [h2] at hh
  exact (by decide : (witnessPost 2).signal_B ≠ 0) hh

end SignalMergeWash

#print axioms SignalMergeWash.signal_advance_pair
#print axioms SignalMergeWash.signal_to_wave_pair
#print axioms SignalMergeWash.kernel_left_nonzero
#print axioms SignalMergeWash.kernel_right_signal_zero
#print axioms SignalMergeWash.kernel_right_follower_signal_one
#print axioms SignalMergeWash.gapShape_step
#print axioms SignalMergeWash.zeroSuffix_off_source
#print axioms SignalMergeWash.sweep_step
#print axioms SignalMergeWash.signalFront_service
#print axioms SignalMergeWash.signalFront_endpoint_out
#print axioms SignalMergeWash.signalFront_endpoint_in
#print axioms SignalMergeWash.markStep_tracks
#print axioms SignalMergeWash.wash_bellman
#print axioms SignalMergeWash.washStep_erases
#print axioms SignalMergeWash.right_clear_truncated_cost
#print axioms SignalMergeWash.right_clear_half
#print axioms SignalMergeWash.raw_wash_success_prefix
#print axioms SignalMergeWash.physical_wash_success_prefix
#print axioms SignalMergeWash.witness_actual_deletion
#print axioms SignalMergeWash.witness_not_done
#print axioms SignalMergeWash.witness_right_clear_half
#print axioms SignalMergeWash.right_only_word_not_whole_order
