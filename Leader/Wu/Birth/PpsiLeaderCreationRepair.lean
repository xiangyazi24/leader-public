import Leader.Wu.Birth.PpsiLeaderCreationSchedule
import Leader.Wu.WallSweep.PreCheckResetContractsDrain

/-!
# Lifting the nondivisible first-leader schedule to the complete repair

The raw P-prime seed-and-chase theorem tracks only the three fields written by
P-prime: label, probe, and phase.  This module packages that projection and
proves that the remaining stages of the complete pre-CHECK wall frame it.  The
result is the simulation interface needed to insert canonical deletion drains
between intended P-prime edges and stop when the first repaired leader appears.
-/

namespace PPLLPpsiLeaderCreationRepair

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWriteIncrementGate
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts
  PPLLPpsiLeaderCreationSchedule
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoKernel

variable {n psi kappa tau : Nat}

/-! ## The physical P-prime control projection -/

/-- Exactly the local fields that participate in the P-prime first-leader
kernel.  Later comparison, reset, bullet, and writer stages must frame this
view for the raw schedule to simulate them. -/
@[ext]
structure PpsiControlView (psi : Nat) where
  label : Fin psi
  probe : Bool
  phase : Bool
  deriving DecidableEq, Repr

/-- Read the P-prime control projection from one physical agent. -/
def PpsiControlView.ofState (u : AgentState psi) : PpsiControlView psi :=
  ⟨u.label, u.probe, u.phase⟩

/-- P-prime controls of an interacting physical pair. -/
def ppsiControlPair (q : AgentState psi × AgentState psi) :
    PpsiControlView psi × PpsiControlView psi :=
  (PpsiControlView.ofState q.1, PpsiControlView.ofState q.2)

/-- P-prime controls after erasing authorization. -/
def authorizedPpsiControlPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    PpsiControlView psi × PpsiControlView psi :=
  ppsiControlPair (q.1.core, q.2.core)

/-- P-prime controls after erasing the bounded authorized carrier. -/
def boundedPpsiControlPair
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) :
    PpsiControlView psi × PpsiControlView psi :=
  authorizedPpsiControlPair (q.1.erase, q.2.erase)

/-- P-prime controls after erasing finite reification and path-stall wrappers. -/
def expiringPpsiControlPair
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) :
    PpsiControlView psi × PpsiControlView psi :=
  ppsiControlPair (q.1.core.erase.core, q.2.core.erase.core)

/-- Pointwise P-prime control equality between physical configurations. -/
def PpsiControlConfigFrame
    (C D : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∀ i, PpsiControlView.ofState (D i).core.erase.core =
    PpsiControlView.ofState (C i).core.erase.core

/-- Erase a finite path-stall configuration to the raw physical carrier. -/
def eraseExpiringConfig
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin n → AgentState psi :=
  fun i => (C i).core.erase.core

/-- A finite configuration realizes the P-prime controls of a raw shadow. -/
def PpsiControlConfigRefines
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∀ i, PpsiControlView.ofState (physical i).core.erase.core =
    PpsiControlView.ofState (raw i)

theorem PpsiControlConfigFrame.refl
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    PpsiControlConfigFrame C C := fun _ => rfl

theorem PpsiControlConfigFrame.trans
    {A B C : Fin n → ExpiringAgentState psi kappa tau}
    (hAB : PpsiControlConfigFrame A B)
    (hBC : PpsiControlConfigFrame B C) :
    PpsiControlConfigFrame A C :=
  fun i => (hBC i).trans (hAB i)

theorem PpsiControlConfigRefines.of_frame
    {raw : Fin n → AgentState psi}
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hrefine : PpsiControlConfigRefines raw C)
    (hframe : PpsiControlConfigFrame C D) :
    PpsiControlConfigRefines raw D :=
  fun i => (hframe i).trans (hrefine i)

theorem eraseExpiringConfig_leaderless_of_peaceFrame
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hframe : PeaceViewConfigFrame C D) :
    RawLeaderless (eraseExpiringConfig D) := by
  intro i
  exact (congrArg PeaceView.leader (hframe i)).trans (hleaderless i)

/-- Pointwise physical framing transports the identity and uniqueness of the
leader. -/
theorem hasUniqueLeader_of_peaceViewConfigFrame
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hframe : PeaceViewConfigFrame C D)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C)) :
    hasUniqueLeader n (eraseExpiringConfig D) := by
  obtain ⟨leader, hleader, honly⟩ := hunique
  refine ⟨leader, ?_, ?_⟩
  · change (D leader).core.erase.core.isLeader
    change (D leader).core.erase.core.leader = true
    change (C leader).core.erase.core.leader = true at hleader
    exact (congrArg PeaceView.leader (hframe leader)).trans hleader
  · intro i hi
    apply honly i
    change (C i).core.erase.core.isLeader
    change (C i).core.erase.core.leader = true
    change (D i).core.erase.core.leader = true at hi
    exact (congrArg PeaceView.leader (hframe i)).symm.trans hi

/-! ## Global live-bullet retry rank -/

/-- Number of live (`bullet = 2`) bullets in a complete physical
configuration.  Dummy bullets do not contribute to the retry rank. -/
def bulletTwoCount
    (C : Fin n → ExpiringAgentState psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n =>
    bulletTwoMass (C i).core.erase.core)).sum

/-- A zero global live-bullet count excludes a live bullet at every physical
site.  Dummy bullets may remain. -/
theorem bullet_ne_two_of_bulletTwoCount_eq_zero
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hzero : bulletTwoCount C = 0) (i : Fin n) :
    (C i).core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [bulletTwoCount, List.ofFn_succ, List.sum_cons] at hzero
      have hhead : bulletTwoMass (C 0).core.erase.core = 0 := by
        omega
      have htail :
          (List.ofFn (fun j : Fin n =>
            bulletTwoMass (C j.succ).core.erase.core)).sum = 0 := by
        omega
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hlive
        unfold bulletTwoMass at hhead
        rw [hlive] at hhead
        simp at hhead
      · exact ih (C := fun j : Fin n => C j.succ) (by
          change (List.ofFn (fun j : Fin n =>
            bulletTwoMass (C j.succ).core.erase.core)).sum = 0
          exact htail) j

/-- Hence every edge satisfies the only bullet/shield premise needed for a
leader to survive a replay: the dangerous live-bullet antecedent is false. -/
theorem edge_safe_of_bulletTwoCount_eq_zero
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hzero : bulletTwoCount C = 0) (i j : Fin n) :
    (C j).core.erase.core.bullet = ⟨2, by omega⟩ →
      (C i).core.erase.core.shield = true := by
  intro hlive
  exact (bullet_ne_two_of_bulletTwoCount_eq_zero C hzero j hlive).elim

/-- Every live bullet, if one exists, is confined to the named leader.  This
is the stable form of the earlier zero-live-bullet subspace: leader-source
steps may retain or fire at the leader, while no follower may acquire a fresh
live bullet. -/
def BulletTwoFreeAwayFrom
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader : Fin n) : Prop :=
  ∀ i, i ≠ leader →
    (C i).core.erase.core.bullet ≠ ⟨2, by omega⟩

/-- Global live-bullet freedom implies freedom away from any named site. -/
theorem bulletTwoFreeAwayFrom_of_bulletTwoCount_eq_zero
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hzero : bulletTwoCount C = 0) (leader : Fin n) :
    BulletTwoFreeAwayFrom C leader := by
  intro i _
  exact bullet_ne_two_of_bulletTwoCount_eq_zero C hzero i

/-- If the responder is distinct from the named leader, freedom away from
that leader discharges the collision-safety premise for their edge. -/
theorem edge_safe_of_bulletTwoFreeAwayFrom
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader responder : Fin n)
    (hfree : BulletTwoFreeAwayFrom C leader)
    (hne : responder ≠ leader) :
    (C responder).core.erase.core.bullet = ⟨2, by omega⟩ →
      (C leader).core.erase.core.shield = true := by
  intro hlive
  exact (hfree responder hne hlive).elim

private theorem sum_ofFn_eq
    (f g : Fin n → Nat) (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- A pointwise physical frame preserves the global live-bullet rank. -/
theorem bulletTwoCount_eq_of_peaceViewConfigFrame
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hframe : PeaceViewConfigFrame C D) :
    bulletTwoCount D = bulletTwoCount C := by
  unfold bulletTwoCount
  apply sum_ofFn_eq
  intro i
  apply bulletTwoMass_eq_of_bullet_eq
  exact congrArg PeaceView.bullet (hframe i)

/-- One physical endpoint contributes at most one unit to the live-bullet
rank. -/
theorem bulletTwoMass_le_one (u : AgentState psi) :
    bulletTwoMass u ≤ 1 := by
  unfold bulletTwoMass
  split <;> omega

/-- The live-bullet retry rank is bounded by the population size. -/
theorem bulletTwoCount_le
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    bulletTwoCount C ≤ n := by
  induction n with
  | zero => simp [bulletTwoCount]
  | succ n ih =>
      rw [bulletTwoCount, List.ofFn_succ, List.sum_cons]
      have hhead := bulletTwoMass_le_one (C 0).core.erase.core
      have htail := ih (C := fun i : Fin n => C i.succ)
      unfold bulletTwoCount at htail
      have htail' :
          (List.ofFn (fun i : Fin n =>
            bulletTwoMass (C i.succ).core.erase.core)).sum ≤ n := by
        simpa using htail
      omega

private theorem add_sum_ofFn_le_add_sum_ofFn_of_one
    (f g : Fin n → Nat) (a b : Nat) (j : Fin n)
    (hpair : a + f j ≤ b + g j)
    (hother : ∀ i, i ≠ j → f i = g i) :
    a + (List.ofFn f).sum ≤ b + (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum :=
          sum_ofFn_eq _ _ (fun i => hother i.succ (by
            intro hbad
            have hv := congrArg Fin.val hbad
            simp at hv))
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 := hother 0 (Ne.symm hj0)
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ) j'
          (by simpa [hjsucc] using hpair)
          (by
            intro i hi
            apply hother i.succ
            intro hbad
            apply hi
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        omega

/-- Replacing two distinct sites by a pair whose combined mass does not
increase cannot increase the sum over the complete finite configuration. -/
theorem sum_ofFn_le_of_pair_le
    (f g : Fin n → Nat) (i j : Fin n)
    (hij : i ≠ j)
    (hpair : f i + f j ≤ g i + g j)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi0 : i = 0
      · subst i
        have hj0 : j ≠ 0 := Ne.symm hij
        have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega

        let j' : Fin n := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        apply add_sum_ofFn_le_add_sum_ofFn_of_one
          (fun k : Fin n => f k.succ) (fun k : Fin n => g k.succ)
          (f 0) (g 0) j'
        · simpa [hjsucc] using hpair
        · intro k hkj
          apply hother k.succ (by
            intro hbad
            have hv := congrArg Fin.val hbad
            simp at hv)
          intro hbad
          apply hkj
          apply Fin.ext
          have hv := congrArg Fin.val hbad
          change k.val + 1 = j.val at hv
          change k.val = j.val - 1
          omega
      · by_cases hj0 : j = 0
        · subst j
          have hipos : 0 < i.val := by
            have hine : i.val ≠ 0 := by
              intro h
              apply hi0
              apply Fin.ext
              simpa using h
            omega
          let i' : Fin n := ⟨i.val - 1, by omega⟩
          have hisucc : i'.succ = i := by
            apply Fin.ext
            change i.val - 1 + 1 = i.val
            omega
          apply add_sum_ofFn_le_add_sum_ofFn_of_one
            (fun k : Fin n => f k.succ) (fun k : Fin n => g k.succ)
            (f 0) (g 0) i'
          · have hcommuted : f 0 + f i ≤ g 0 + g i := by omega
            simpa [hisucc] using hcommuted
          · intro k hki
            apply hother k.succ
            · intro hbad
              apply hki
              apply Fin.ext
              have hv := congrArg Fin.val hbad
              change k.val + 1 = i.val at hv
              change k.val = i.val - 1
              omega
            · intro hbad
              have hv := congrArg Fin.val hbad
              simp at hv
        · have hipos : 0 < i.val := by
            have hine : i.val ≠ 0 := by
              intro h
              apply hi0
              apply Fin.ext
              simpa using h
            omega
          have hjpos : 0 < j.val := by
            have hjne : j.val ≠ 0 := by
              intro h
              apply hj0
              apply Fin.ext
              simpa using h
            omega
          let i' : Fin n := ⟨i.val - 1, by omega⟩
          let j' : Fin n := ⟨j.val - 1, by omega⟩
          have hisucc : i'.succ = i := by
            apply Fin.ext
            change i.val - 1 + 1 = i.val
            omega
          have hjsucc : j'.succ = j := by
            apply Fin.ext
            change j.val - 1 + 1 = j.val
            omega
          have hij' : i' ≠ j' := by
            intro hbad
            apply hij
            rw [← hisucc, ← hjsucc, hbad]
          have hhead : f 0 = g 0 :=
            hother 0 (Ne.symm hi0) (Ne.symm hj0)
          have htail := ih
            (fun k : Fin n => f k.succ)
            (fun k : Fin n => g k.succ) i' j' hij'
            (by simpa [hisucc, hjsucc] using hpair)
            (by
              intro k hki hkj
              apply hother k.succ
              · intro hbad
                apply hki
                apply Fin.ext
                have hv := congrArg Fin.val hbad
                change k.val + 1 = i.val at hv
                change k.val = i.val - 1
                omega
              · intro hbad
                apply hkj
                apply Fin.ext
                have hv := congrArg Fin.val hbad
                change k.val + 1 = j.val at hv
                change k.val = j.val - 1
                omega)
          omega

private theorem sum_ofFn_update_add_one
    (f : Fin n → Nat) (i : Fin n) :
    (List.ofFn (fun k => if k = i then f k + 1 else f k)).sum =
      (List.ofFn f).sum + 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi0 : i = 0
      · subst i
        rw [if_pos rfl]
        have htail :
            (List.ofFn (fun k : Fin n =>
              if k.succ = (0 : Fin (n + 1)) then f k.succ + 1
              else f k.succ)).sum =
            (List.ofFn (fun k : Fin n => f k.succ)).sum := by
          apply sum_ofFn_eq
          intro k
          rw [if_neg (by
            intro hbad
            have hv := congrArg Fin.val hbad
            simp at hv)]
        rw [htail]
        omega
      · have hipos : 0 < i.val := by
          have hine : i.val ≠ 0 := by
            intro h
            apply hi0
            apply Fin.ext
            simpa using h
          omega
        let i' : Fin n := ⟨i.val - 1, by omega⟩
        have hisucc : i'.succ = i := by
          apply Fin.ext
          change i.val - 1 + 1 = i.val
          omega
        rw [if_neg (Ne.symm hi0)]
        have htail := ih (fun k : Fin n => f k.succ) i'
        have htail' :
            (List.ofFn (fun k : Fin n =>
              if k.succ = i then f k.succ + 1 else f k.succ)).sum =
              (List.ofFn (fun k : Fin n => f k.succ)).sum + 1 := by
          simpa [← hisucc] using htail
        omega

/-- Replacing two distinct sites by a pair whose combined mass grows by at
most one grows the complete finite sum by at most one. -/
theorem sum_ofFn_le_add_one_of_pair_le_add_one
    (f g : Fin n → Nat) (i j : Fin n)
    (hij : i ≠ j)
    (hpair : f i + f j ≤ g i + g j + 1)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum + 1 := by
  let gPlus : Fin n → Nat := fun k =>
    if k = i then g k + 1 else g k
  have hpairPlus : f i + f j ≤ gPlus i + gPlus j := by
    unfold gPlus
    rw [if_pos rfl, if_neg (Ne.symm hij)]
    omega
  have hotherPlus : ∀ k, k ≠ i → k ≠ j → f k = gPlus k := by
    intro k hki hkj
    simp [gPlus, hki, hother k hki hkj]
  have hle := sum_ofFn_le_of_pair_le
    f gPlus i j hij hpairPlus hotherPlus
  have hadd := sum_ofFn_update_add_one g i
  change (List.ofFn f).sum ≤ (List.ofFn gPlus).sum at hle
  change (List.ofFn gPlus).sum = (List.ofFn g).sum + 1 at hadd
  omega

/-- Replacing two distinct sites by a pair of strictly smaller combined mass
strictly decreases the sum over the complete finite configuration. -/
theorem sum_ofFn_lt_of_pair_lt
    (f g : Fin n → Nat) (i j : Fin n)
    (hij : i ≠ j)
    (hpair : f i + f j < g i + g j)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  let fPlus : Fin n → Nat := fun k =>
    if k = i then f k + 1 else f k
  have hpairPlus : fPlus i + fPlus j ≤ g i + g j := by
    unfold fPlus
    rw [if_pos rfl, if_neg (Ne.symm hij)]
    omega
  have hotherPlus : ∀ k, k ≠ i → k ≠ j → fPlus k = g k := by
    intro k hki hkj
    simp [fPlus, hki, hother k hki hkj]
  have hle := sum_ofFn_le_of_pair_le
    fPlus g i j hij hpairPlus hotherPlus
  have hadd := sum_ofFn_update_add_one f i
  change (List.ofFn fPlus).sum ≤ (List.ofFn g).sum at hle
  change (List.ofFn fPlus).sum = (List.ofFn f).sum + 1 at hadd
  omega

/-- A complete priority-open physical interaction with a follower initiator
cannot increase the global live-bullet retry rank.  The proof uses the local
two-endpoint contract and frames every other site of the ring. -/
theorem localStepLeaderSink_priority_open_left_follower_bulletTwoCount_le
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hlFollower : (C e).core.erase.core.leader = false) :
    bulletTwoCount
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e) ≤
      bulletTwoCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hlocal :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core := by
    exact
      (wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_follower_bulletTwoPair
        hpsi (C e) (C j) (by simpa [j] using hopen) hlFollower).le
  unfold bulletTwoCount
  apply sum_ofFn_le_of_pair_le
    (fun i => bulletTwoMass (D i).core.erase.core)
    (fun i => bulletTwoMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, q, T, localStep, j, hje, bulletTwoPairMass] using hlocal
  · intro i hie hij
    simp [D, localStep, T, j, hie, hij]

/-- If a priority-open local step kills its initiating leader against a
follower responder, the global live-bullet retry rank strictly decreases. -/
theorem localStepLeaderSink_priority_open_initiator_killed_bulletTwoCount_lt
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hlLeader : (C e).core.erase.core.leader = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (houtFollower :
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e e).core.erase.core.leader = false) :
    bulletTwoCount
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e) <
      bulletTwoCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hDe : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hqFollower : q.1.core.erase.core.leader = false :=
    (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.leader) hDe).symm.trans houtFollower
  have hlocal :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core <
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core := by
    exact
      (wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_killed_bulletTwoPair
        hpsi (C e) (C j) (by simpa [j] using hopen)
          hlLeader (by simpa [j] using hrFollower) hqFollower).lt
  unfold bulletTwoCount
  apply sum_ofFn_lt_of_pair_lt
    (fun i => bulletTwoMass (D i).core.erase.core)
    (fun i => bulletTwoMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, q, T, localStep, j, hje, bulletTwoPairMass] using hlocal
  · intro i hie hij
    simp [D, localStep, T, j, hie, hij]

/-- A priority-open step from the unique leader has the retry dichotomy needed
by the repaired convergence argument: either the initiating leader survives,
or the complete configuration becomes leaderless while the global live-bullet
rank strictly decreases. -/
theorem
    localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hlLeader : (C e).core.erase.core.leader = true)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e))) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    (hasUniqueLeader n (eraseExpiringConfig D) ∧
        (D e).core.erase.core.leader = true) ∨
      (RawLeaderless (eraseExpiringConfig D) ∧
        bulletTwoCount D < bulletTwoCount C) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hotherFollower : ∀ i, i ≠ e →
      (C i).core.erase.core.leader = false := by
    intro i hie
    cases hi : (C i).core.erase.core.leader with
    | false => rfl
    | true =>
        obtain ⟨leader, hleader, honly⟩ := hunique
        have hiUnique : i = leader := by
          apply honly i
          change (C i).core.erase.core.isLeader
          change (C i).core.erase.core.leader = true
          exact hi
        have heUnique : e = leader := by
          apply honly e
          change (C e).core.erase.core.isLeader
          change (C e).core.erase.core.leader = true
          exact hlLeader
        exact False.elim (hie (hiUnique.trans heUnique.symm))
  have hrFollower : (C j).core.erase.core.leader = false :=
    hotherFollower j hje
  have houtResponderFollower : (D j).core.erase.core.leader = false := by
    simpa [D, T, j, localStep, hje] using
      (wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
        hpsi (C e) (C j) (by simpa [j] using hopen)
          hlLeader hrFollower)
  have houtputOther : ∀ i, i ≠ e →
      (D i).core.erase.core.leader = false := by
    intro i hie
    by_cases hij : i = j
    · subst i
      exact houtResponderFollower
    · simpa [D, T, localStep, j, hie, hij] using
        hotherFollower i hie
  cases houtLeader : (D e).core.erase.core.leader with
  | true =>
      have huniqueD : hasUniqueLeader n (eraseExpiringConfig D) := by
        refine ⟨e, ?_, ?_⟩
        · change (D e).core.erase.core.isLeader
          change (D e).core.erase.core.leader = true
          exact houtLeader
        · intro i hi
          by_cases hie : i = e
          · exact hie
          · have hiFollower := houtputOther i hie
            change (D i).core.erase.core.isLeader at hi
            change (D i).core.erase.core.leader = true at hi
            rw [hiFollower] at hi
            contradiction
      exact .inl ⟨huniqueD, houtLeader⟩
  | false =>
      have hleaderless : RawLeaderless (eraseExpiringConfig D) := by
        intro i
        by_cases hie : i = e
        · subst i
          exact houtLeader
        · exact houtputOther i hie
      have hrank : bulletTwoCount D < bulletTwoCount C := by
        exact localStepLeaderSink_priority_open_initiator_killed_bulletTwoCount_lt
          hpsi kappa tau ring hn C e hopen hlLeader
          (by simpa [j] using hrFollower)
          (by simpa [D, T] using houtLeader)
      exact .inr ⟨hleaderless, hrank⟩

private theorem waitSaturatedPrepare_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (waitSaturatedPrepare hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      waitSaturatedPrepare]

private theorem waitSaturatedCarry_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    ppsiControlPair (waitSaturatedCarry hpsi kappa l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      waitSaturatedCarry]

private theorem waitSaturatedReset_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (waitSaturatedReset hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      waitSaturatedReset]

private theorem waitSaturatedFinish_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    ppsiControlPair (waitSaturatedFinish hpsi kappa l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      waitSaturatedFinish]

private theorem waitSaturated_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    ppsiControlPair (waitSaturated hpsi kappa l r) =
      ppsiControlPair (l, r) := by
  let q0 := waitSaturatedPrepare hpsi l r
  let q1 := waitSaturatedCarry hpsi kappa q0.1 q0.2
  let q2 := waitSaturatedReset hpsi q1.1 q1.2
  change ppsiControlPair (waitSaturatedFinish hpsi kappa q2.1 q2.2) =
    ppsiControlPair (l, r)
  exact (waitSaturatedFinish_ppsiControlPair hpsi kappa q2.1 q2.2).trans
    ((waitSaturatedReset_ppsiControlPair hpsi q1.1 q1.2).trans
      ((waitSaturatedCarry_ppsiControlPair hpsi kappa q0.1 q0.2).trans
        (waitSaturatedPrepare_ppsiControlPair hpsi l r)))

private theorem genSigSaturatedStart_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (genSigSaturatedStart hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      genSigSaturatedStart]

private theorem genSigSaturatedEmit_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (genSigSaturatedEmit hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      genSigSaturatedEmit]

private theorem genSigSaturatedPropagate_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (genSigSaturatedPropagate hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      genSigSaturatedPropagate]

private theorem genSigSaturatedFinish_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (genSigSaturatedFinish hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext <;>
    simp [ppsiControlPair, PpsiControlView.ofState,
      genSigSaturatedFinish]

private theorem genSigSaturatedAfterWait_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (genSigSaturatedAfterWait hpsi l r) =
      ppsiControlPair (l, r) := by
  let q0 := genSigSaturatedStart hpsi l r
  let q1 := genSigSaturatedEmit hpsi q0.1 q0.2
  let q2 := genSigSaturatedPropagate hpsi q1.1 q1.2
  change ppsiControlPair (genSigSaturatedFinish hpsi q2.1 q2.2) =
    ppsiControlPair (l, r)
  exact (genSigSaturatedFinish_ppsiControlPair hpsi q2.1 q2.2).trans
    ((genSigSaturatedPropagate_ppsiControlPair hpsi q1.1 q1.2).trans
      ((genSigSaturatedEmit_ppsiControlPair hpsi q0.1 q0.2).trans
        (genSigSaturatedStart_ppsiControlPair hpsi l r)))

private theorem genSigSaturated_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat) (l r : AgentState psi) :
    ppsiControlPair (genSigSaturated hpsi kappa l r) =
      ppsiControlPair (l, r) := by
  let q := waitSaturated hpsi kappa l r
  change ppsiControlPair (genSigSaturatedAfterWait hpsi q.1 q.2) =
    ppsiControlPair (l, r)
  exact (genSigSaturatedAfterWait_ppsiControlPair hpsi q.1 q.2).trans
    (waitSaturated_ppsiControlPair hpsi kappa l r)

private theorem cleanSigGenConnect_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (cleanSigGenConnect u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState cleanSigGenConnect
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigCleanApply_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (cleanSigCleanApply u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState cleanSigCleanApply
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep3_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (cleanSigStep3 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState cleanSigStep3
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep4_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (cleanSigStep4 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState cleanSigStep4
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep5_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (cleanSigStep5 hpsi l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState cleanSigStep5
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSigStep6_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (cleanSigStep6 hpsi l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState cleanSigStep6
    try dsimp only []
    repeat (first | rfl | split)

private theorem cleanSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (cleanSig hpsi l r) = ppsiControlPair (l, r) := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  let q3 := cleanSigStep3 l0 r0
  let q4 := cleanSigStep4 q3.1 q3.2
  let q5 := cleanSigStep5 hpsi q4.1 q4.2
  let q6 := cleanSigStep6 hpsi q5.1 q5.2
  have h0 : ppsiControlPair (l0, r0) = ppsiControlPair (l, r) :=
    Prod.ext (cleanSigGenConnect_ppsiControl l)
      (cleanSigGenConnect_ppsiControl r)
  have h3 := cleanSigStep3_ppsiControlPair l0 r0
  have h4 := cleanSigStep4_ppsiControlPair q3.1 q3.2
  have h5 := cleanSigStep5_ppsiControlPair hpsi q4.1 q4.2
  have h6 := cleanSigStep6_ppsiControlPair hpsi q5.1 q5.2
  have hout :
      ppsiControlPair (cleanSigCleanApply q6.1,
        cleanSigCleanApply q6.2) = ppsiControlPair q6 :=
    Prod.ext (cleanSigCleanApply_ppsiControl q6.1)
      (cleanSigCleanApply_ppsiControl q6.2)
  change ppsiControlPair (cleanSigCleanApply q6.1,
    cleanSigCleanApply q6.2) = ppsiControlPair (l, r)
  exact hout.trans (h6.trans (h5.trans (h4.trans (h3.trans h0))))

private theorem eliminateSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (eliminateSig hpsi l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  · exact (PPLLVerify.eliminateSig_labels_eq hpsi l r).1
  · simp [ppsiControlPair, PpsiControlView.ofState, eliminateSig]
  · simp [ppsiControlPair, PpsiControlView.ofState, eliminateSig]
  · exact (PPLLVerify.eliminateSig_labels_eq hpsi l r).2
  · simp [ppsiControlPair, PpsiControlView.ofState, eliminateSig]
  · simp [ppsiControlPair, PpsiControlView.ofState, eliminateSig]

private theorem sigMoveLeaderPreclear_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (sigMoveLeaderPreclear hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState sigMoveLeaderPreclear
      clearIfLeader clearComparisonSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveStep1_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (sigMoveStep1 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState sigMoveStep1
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveStep2_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (sigMoveStep2 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState sigMoveStep2
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveStep3_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (sigMoveStep3 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState sigMoveStep3
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveStep4_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (sigMoveStep4 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState sigMoveStep4
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveStep5_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (sigMoveStep5 l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState sigMoveStep5
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveTransfers_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (sigMoveTransfers l r) = ppsiControlPair (l, r) := by
  let q0 := sigMoveStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  change ppsiControlPair (sigMoveStep5 q3.1 q3.2) =
    ppsiControlPair (l, r)
  exact (sigMoveStep5_ppsiControlPair q3.1 q3.2).trans
    ((sigMoveStep4_ppsiControlPair q2.1 q2.2).trans
      ((sigMoveStep3_ppsiControlPair q1.1 q1.2).trans
        ((sigMoveStep2_ppsiControlPair q0.1 q0.2).trans
          (sigMoveStep1_ppsiControlPair l r))))

private theorem comparisonLeaderWall_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (comparisonLeaderWall l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState comparisonLeaderWall
      clearComparisonSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveApplyControl_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (sigMoveApplyControl hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState sigMoveApplyControl
    try dsimp only []
    repeat (first | rfl | split)

private theorem sigMoveControlTail_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (sigMoveControlTail hpsi l r) =
      ppsiControlPair (l, r) := by
  let l0 := sigMoveApplyControl hpsi l
  let r0 := sigMoveApplyControl hpsi r
  let l1 := if r0.state = .depart then
    if l0.label.val < psi - 1 ∧ l0.state = .CHECK_ready then
      { l0 with state := .depart }
    else l0
  else l0
  have hl1 : PpsiControlView.ofState l1 =
      PpsiControlView.ofState l0 := by
    unfold l1 PpsiControlView.ofState
    repeat (first | rfl | split)
  change (PpsiControlView.ofState l1, PpsiControlView.ofState r0) =
    (PpsiControlView.ofState l, PpsiControlView.ofState r)
  exact Prod.ext
    (hl1.trans (sigMoveApplyControl_ppsiControl hpsi l))
    (sigMoveApplyControl_ppsiControl hpsi r)

private theorem sigMoveLeaderWall_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (sigMoveLeaderWall hpsi l r) =
      ppsiControlPair (l, r) := by
  let q0 := sigMoveLeaderPreclear hpsi l r
  let moved := sigMoveTransfers q0.1 q0.2
  let walled := comparisonLeaderWall moved.1 moved.2
  change ppsiControlPair (sigMoveControlTail hpsi walled.1 walled.2) =
    ppsiControlPair (l, r)
  exact (sigMoveControlTail_ppsiControlPair hpsi walled.1 walled.2).trans
    ((comparisonLeaderWall_ppsiControlPair moved.1 moved.2).trans
      ((sigMoveTransfers_ppsiControlPair q0.1 q0.2).trans
        (sigMoveLeaderPreclear_ppsiControlPair hpsi l r)))

theorem authorizedReconcile_ppsiControlPair
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hframe : ppsiControlPair (f l.core r.core) =
      ppsiControlPair (l.core, r.core)) :
    authorizedPpsiControlPair (authorizedReconcile f l r) =
      authorizedPpsiControlPair (l, r) := by
  exact hframe

theorem authorizedGenSig_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedGenSig hpsi kappa l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (genSigSaturated hpsi kappa) l r
    (genSigSaturated_ppsiControlPair hpsi kappa l.core r.core)

theorem authorizedCleanSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedCleanSig hpsi l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (cleanSig hpsi) l r
    (cleanSig_ppsiControlPair hpsi l.core r.core)

theorem authorizedEliminateSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedEliminateSig hpsi l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (eliminateSig hpsi) l r
    (eliminateSig_ppsiControlPair hpsi l.core r.core)

theorem authorizedSigMoveLeaderWall_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedSigMoveLeaderWall hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  change ppsiControlPair
      ((authorizedSigMoveLeaderWall hpsi l r).1.core,
        (authorizedSigMoveLeaderWall hpsi l r).2.core) =
    ppsiControlPair (l.core, r.core)
  rw [authorizedSigMoveLeaderWall_core]
  exact sigMoveLeaderWall_ppsiControlPair hpsi l.core r.core

/-- The complete authorized prefix through the SIGMOVE wall has exactly the
physical P-prime control output of its first stage. -/
theorem wallSweepAuthorizedBeforeCheck_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (wallSweepAuthorizedBeforeCheck hpsi kappa l r) =
      ppsiControlPair (pPsiLeaderProbeWall hpsi l.core r.core) := by
  let q0 := authorizedPPsiLeaderProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  have h0 : authorizedPpsiControlPair q0 =
      ppsiControlPair (pPsiLeaderProbeWall hpsi l.core r.core) := by
    rfl
  change authorizedPpsiControlPair
      (authorizedSigMoveLeaderWall hpsi q3.1 q3.2) =
    ppsiControlPair (pPsiLeaderProbeWall hpsi l.core r.core)
  exact (authorizedSigMoveLeaderWall_ppsiControlPair hpsi q3.1 q3.2).trans
    ((authorizedEliminateSig_ppsiControlPair hpsi q2.1 q2.2).trans
      ((authorizedCleanSig_ppsiControlPair hpsi q1.1 q1.2).trans
        ((authorizedGenSig_ppsiControlPair hpsi kappa q0.1 q0.2).trans h0)))

theorem preCheckResetWall_ppsiControlPair
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (preCheckResetWall l r) =
      authorizedPpsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold authorizedPpsiControlPair ppsiControlPair
      PpsiControlView.ofState preCheckResetWall
      clearAuthorizedComparison clearComparisonSignal
    try dsimp only []
    repeat (first | rfl | split)

theorem sanitizeAuthorizedPair_ppsiControlPair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPpsiControlPair (sanitizeAuthorizedPair hpsi q) =
      authorizedPpsiControlPair q := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold authorizedPpsiControlPair ppsiControlPair
      PpsiControlView.ofState sanitizeAuthorizedPair
      sanitizeAuthorizedTerminalEqual
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigSetReady_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (checkSigSetReady u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState checkSigSetReady
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigCheckL_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (checkSigCheckL hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState checkSigCheckL
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigCheckR_ppsiControl
    (hpsi : psi > 0) (l r : AgentState psi) :
    PpsiControlView.ofState (checkSigCheckR hpsi l r) =
      PpsiControlView.ofState r := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState checkSigCheckR
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigSetResult_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (checkSigSetResult u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState checkSigSetResult
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSigSetLeader_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (checkSigSetLeader hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState checkSigSetLeader
    try dsimp only []
    repeat (first | rfl | split)

private theorem checkSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (checkSig hpsi l r) = ppsiControlPair (l, r) := by
  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL hpsi l0
  let r1 := checkSigCheckR hpsi l1 r0
  let l2 := checkSigSetResult l1
  let r2 := checkSigSetResult r1
  change (PpsiControlView.ofState l2,
      PpsiControlView.ofState (checkSigSetLeader hpsi r2)) =
    (PpsiControlView.ofState l, PpsiControlView.ofState r)
  exact Prod.ext
    ((checkSigSetResult_ppsiControl l1).trans
      ((checkSigCheckL_ppsiControl hpsi l0).trans
        (checkSigSetReady_ppsiControl l)))
    ((checkSigSetLeader_ppsiControl hpsi r2).trans
      ((checkSigSetResult_ppsiControl r1).trans
        ((checkSigCheckR_ppsiControl hpsi l1 r0).trans
          (checkSigSetReady_ppsiControl r))))

theorem authorizedCheckSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedCheckSig hpsi l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (checkSig hpsi) l r
    (checkSig_ppsiControlPair hpsi l.core r.core)

private theorem disappearStartR_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (disappearStartR hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState disappearStartR
    try dsimp only []
    repeat (first | rfl | split)

private theorem disappearStartL_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (disappearStartL hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState disappearStartL
    try dsimp only []
    repeat (first | rfl | split)

private theorem disappearCarry_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (disappearCarry hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState disappearCarry
    try dsimp only []
    repeat (first | rfl | split)

private theorem disappear_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (disappear hpsi l r) = ppsiControlPair (l, r) := by
  let q0 := disappearStartR hpsi l r
  let q1 := disappearStartL hpsi q0.1 q0.2
  change ppsiControlPair (disappearCarry hpsi q1.1 q1.2) =
    ppsiControlPair (l, r)
  exact (disappearCarry_ppsiControlPair hpsi q1.1 q1.2).trans
    ((disappearStartL_ppsiControlPair hpsi q0.1 q0.2).trans
      (disappearStartR_ppsiControlPair hpsi l r))

theorem authorizedDisappear_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedDisappear hpsi l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (disappear hpsi) l r
    (disappear_ppsiControlPair hpsi l.core r.core)

theorem compareSigInit_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (compareSigInit u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState compareSigInit
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateReturnPriority_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (cmpUpdateReturnPriority hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState
      cmpUpdateReturnPriority
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (cmpUpdateSetPath2 hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState cmpUpdateSetPath2
    try dsimp only []
    repeat (first | rfl | split)

theorem authorizedCmpUpdate_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedCmpUpdate hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  let allowed := freshComparisonStart hpsi l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := .congest }
  else l.core
  let q := cmpUpdateReturnPriority hpsi lCore r.core
  let lOut := cmpUpdateSetPath2 hpsi q.1
  have hCore : PpsiControlView.ofState lCore =
      PpsiControlView.ofState l.core := by
    unfold lCore PpsiControlView.ofState
    repeat (first | rfl | split)
  have hq := cmpUpdateReturnPriority_ppsiControlPair
    hpsi lCore r.core
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq
  change PpsiControlView.ofState q.1 =
    PpsiControlView.ofState lCore at hqL
  change PpsiControlView.ofState q.2 =
    PpsiControlView.ofState r.core at hqR
  have hOut := cmpUpdateSetPath2_ppsiControl hpsi q.1
  change (PpsiControlView.ofState lOut,
      PpsiControlView.ofState q.2) =
    (PpsiControlView.ofState l.core,
      PpsiControlView.ofState r.core)
  exact Prod.ext
    (hOut.trans (hqL.trans hCore)) hqR

private theorem compareBitUpdateL_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (compareBitUpdateL hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState compareBitUpdateL
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareBitUpdateR_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (compareBitUpdateR hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState compareBitUpdateR
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareBit_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (compareBit hpsi l r) = ppsiControlPair (l, r) := by
  exact Prod.ext (compareBitUpdateL_ppsiControl hpsi l)
    (compareBitUpdateR_ppsiControl hpsi r)

private theorem compareSigDispatch_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (compareSigDispatch hpsi l r) =
      ppsiControlPair (l, r) := by
  cases hpL : l.path2 <;> cases hpR : r.path2 <;>
    simp [compareSigDispatch, hpL, hpR, compareBit_ppsiControlPair]

private theorem authorizedCompareSig_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedCompareSig hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hl0 : PpsiControlView.ofState l0.core =
      PpsiControlView.ofState l.core := by
    exact compareSigInit_ppsiControl l.core
  unfold authorizedCompareSig
  dsimp only
  split
  · exact Prod.ext hl0 rfl
  · split
    · exact Prod.ext hl0 rfl
    · let q := authorizedCmpUpdate hpsi l0 r
      let out := compareSigDispatch hpsi q.1.core q.2.core
      have hq := authorizedCmpUpdate_ppsiControlPair hpsi l0 r
      have hout := compareSigDispatch_ppsiControlPair
        hpsi q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hl0 rfl))

private theorem preCheckResetCheckTail_ppsiControlPair
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPpsiControlPair (preCheckResetCheckTail hpsi q0) =
      authorizedPpsiControlPair q0 := by
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  change authorizedPpsiControlPair
      (authorizedCompareSig hpsi q3.1 q3.2) =
    authorizedPpsiControlPair q0
  exact (authorizedCompareSig_ppsiControlPair hpsi q3.1 q3.2).trans
    ((authorizedDisappear_ppsiControlPair hpsi q2.1 q2.2).trans
      ((authorizedCheckSig_ppsiControlPair hpsi q1.1 q1.2).trans
        ((sanitizeAuthorizedPair_ppsiControlPair hpsi qR).trans
          (preCheckResetWall_ppsiControlPair q0.1 q0.2))))

/-- The repaired prefix through COMPARE still exposes exactly the physical
P-prime control output of the first raw stage. -/
theorem wallSweepPreCheckResetBeforeSuppress_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) =
      ppsiControlPair (pPsiLeaderProbeWall hpsi l.core r.core) := by
  let q0 := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  exact (preCheckResetCheckTail_ppsiControlPair hpsi q0).trans
    (wallSweepAuthorizedBeforeCheck_ppsiControlPair hpsi kappa l r)

private theorem resetKillComparison_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (resetKillComparison u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState resetKillComparison
      clearComparisonSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigStart_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (suppressSigStart l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState suppressSigStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigMoveReset_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (suppressSigMoveReset l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState suppressSigMoveReset
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigTerminal_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (suppressSigTerminal hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState suppressSigTerminal
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigEcho_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (suppressSigEcho l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState suppressSigEcho
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigFinish_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (suppressSigFinish l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState suppressSigFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem suppressSigResetKill_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (suppressSigResetKill hpsi l r) =
      ppsiControlPair (l, r) := by
  let q0 := suppressSigStart l r
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
  let q2 := suppressSigTerminal hpsi q1k.1 q1k.2
  let q3 := suppressSigEcho q2.1 q2.2
  have h0k : ppsiControlPair q0k = ppsiControlPair q0 :=
    Prod.ext (resetKillComparison_ppsiControl q0.1)
      (resetKillComparison_ppsiControl q0.2)
  have h1k : ppsiControlPair q1k = ppsiControlPair q1 :=
    Prod.ext (resetKillComparison_ppsiControl q1.1)
      (resetKillComparison_ppsiControl q1.2)
  change ppsiControlPair (suppressSigFinish q3.1 q3.2) =
    ppsiControlPair (l, r)
  exact (suppressSigFinish_ppsiControlPair q3.1 q3.2).trans
    ((suppressSigEcho_ppsiControlPair q2.1 q2.2).trans
      ((suppressSigTerminal_ppsiControlPair hpsi q1k.1 q1k.2).trans
        (h1k.trans
          ((suppressSigMoveReset_ppsiControlPair q0k.1 q0k.2).trans
            (h0k.trans (suppressSigStart_ppsiControlPair l r))))))

private theorem eliminateLeadersNoCollisionFire_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (eliminateLeadersNoCollisionFire hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState
      eliminateLeadersNoCollisionFire
    try dsimp only []
    repeat (first | rfl | split)

private theorem eliminateLeadersNoCollisionMove_ppsiControlPair
    (nextLabel : Fin psi) (l r : AgentState psi) :
    ppsiControlPair (eliminateLeadersNoCollisionMove nextLabel l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState
      eliminateLeadersNoCollisionMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem eliminateLeadersNoCollisionSignal_ppsiControlPair
    (nextLabel : Fin psi) (l r : AgentState psi) :
    ppsiControlPair (eliminateLeadersNoCollisionSignal nextLabel l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState
      eliminateLeadersNoCollisionSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem eliminateLeadersNoCollision_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (eliminateLeadersNoCollision hpsi l r) =
      ppsiControlPair (l, r) := by
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  change ppsiControlPair
      (eliminateLeadersNoCollisionSignal nextLabel q1.1 q1.2) =
    ppsiControlPair (l, r)
  exact (eliminateLeadersNoCollisionSignal_ppsiControlPair
      nextLabel q1.1 q1.2).trans
    ((eliminateLeadersNoCollisionMove_ppsiControlPair
      nextLabel q0.1 q0.2).trans
      (eliminateLeadersNoCollisionFire_ppsiControlPair hpsi l r))

private theorem writeSeqLeaderMove_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqLeaderMove hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState writeSeqLeaderMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem groupInfoStart_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (groupInfoStart hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState groupInfoStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem groupInfoSet_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (groupInfoSet hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState groupInfoSet
    try dsimp only []
    repeat (first | rfl | split)

private theorem groupInfoUnset_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (groupInfoUnset l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState groupInfoUnset
    try dsimp only []
    repeat (first | rfl | split)

private theorem groupInfo_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (groupInfo hpsi l r) = ppsiControlPair (l, r) := by
  let q0 := groupInfoStart hpsi l r
  let q1 := groupInfoSet hpsi q0.1 q0.2
  change ppsiControlPair (groupInfoUnset q1.1 q1.2) =
    ppsiControlPair (l, r)
  exact (groupInfoUnset_ppsiControlPair q1.1 q1.2).trans
    ((groupInfoSet_ppsiControlPair hpsi q0.1 q0.2).trans
      (groupInfoStart_ppsiControlPair hpsi l r))

private theorem gensigWriteseqStart_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (gensigWriteseqStart hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState gensigWriteseqStart
    try dsimp only []
    repeat (first | rfl | split)

private theorem gensigWriteseqEmit_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (gensigWriteseqEmit hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState gensigWriteseqEmit
    try dsimp only []
    repeat (first | rfl | split)

private theorem gensigWriteseqPropagate_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (gensigWriteseqPropagate hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState gensigWriteseqPropagate
    try dsimp only []
    repeat (first | rfl | split)

private theorem gensigWriteseqFinish_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (gensigWriteseqFinish hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState gensigWriteseqFinish
    try dsimp only []
    repeat (first | rfl | split)

private theorem gensigWriteseq_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (gensigWriteseq hpsi l r) =
      ppsiControlPair (l, r) := by
  let q0 := gensigWriteseqStart hpsi l r
  let q1 := gensigWriteseqEmit hpsi q0.1 q0.2
  let q2 := gensigWriteseqPropagate hpsi q1.1 q1.2
  change ppsiControlPair (gensigWriteseqFinish hpsi q2.1 q2.2) =
    ppsiControlPair (l, r)
  exact (gensigWriteseqFinish_ppsiControlPair hpsi q2.1 q2.2).trans
    ((gensigWriteseqPropagate_ppsiControlPair hpsi q1.1 q1.2).trans
      ((gensigWriteseqEmit_ppsiControlPair hpsi q0.1 q0.2).trans
        (gensigWriteseqStart_ppsiControlPair hpsi l r)))

private theorem writeSeqGenerate_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqGenerate hpsi l r) =
      ppsiControlPair (l, r) := by
  unfold writeSeqGenerate
  split
  · exact gensigWriteseq_ppsiControlPair hpsi l r
  · rfl

private theorem writeSeqSetWriteReady_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (writeSeqSetWriteReady u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeSeqSetWriteReady
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeSeqCheckBit_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (writeSeqCheckBit u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeSeqCheckBit
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeSeqSetWriteAct_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (writeSeqSetWriteAct u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeSeqSetWriteAct
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeSeqFinalR_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (writeSeqFinalR u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeSeqFinalR
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeSeqReady_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (writeSeqReady l r) = ppsiControlPair (l, r) :=
  Prod.ext (writeSeqSetWriteReady_ppsiControl l)
    (writeSeqSetWriteReady_ppsiControl r)

private theorem writeSeqCompare_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqCompare hpsi l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState writeSeqCompare
      writeSeqCheckBit
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeSeqCommands_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqCommands hpsi l r) =
      ppsiControlPair (l, r) := by
  let l0 := writeSeqSetWriteAct l
  let r0 := writeSeqSetWriteAct r
  let r1 := if r0.label = ⟨psi - 1, by omega⟩ ∧
      r0.write_state = .equal then writeSeqFinalR r0 else r0
  have hr1 : PpsiControlView.ofState r1 =
      PpsiControlView.ofState r0 := by
    unfold r1
    split
    · exact writeSeqFinalR_ppsiControl r0
    · rfl
  change (PpsiControlView.ofState l0, PpsiControlView.ofState r1) =
    (PpsiControlView.ofState l, PpsiControlView.ofState r)
  exact Prod.ext (writeSeqSetWriteAct_ppsiControl l)
    (hr1.trans (writeSeqSetWriteAct_ppsiControl r))

private theorem writeSeqPrepare_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqPrepare hpsi l r) =
      ppsiControlPair (l, r) := by
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hpsi q0.1 q0.2
  change ppsiControlPair (writeSeqCommands hpsi q1.1 q1.2) =
    ppsiControlPair (l, r)
  exact (writeSeqCommands_ppsiControlPair hpsi q1.1 q1.2).trans
    ((writeSeqCompare_ppsiControlPair hpsi q0.1 q0.2).trans
      (writeSeqReady_ppsiControlPair l r))

private theorem writeSeqThroughPrepare_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqThroughPrepare hpsi l r) =
      ppsiControlPair (l, r) := by
  let q0 := writeSeqLeaderMove hpsi l r
  let q1 := groupInfo hpsi q0.1 q0.2
  let q2 := writeSeqGenerate hpsi q1.1 q1.2
  change ppsiControlPair (writeSeqPrepare hpsi q2.1 q2.2) =
    ppsiControlPair (l, r)
  exact (writeSeqPrepare_ppsiControlPair hpsi q2.1 q2.2).trans
    ((writeSeqGenerate_ppsiControlPair hpsi q1.1 q1.2).trans
      ((groupInfo_ppsiControlPair hpsi q0.1 q0.2).trans
        (writeSeqLeaderMove_ppsiControlPair hpsi l r)))

private theorem gatePreparedIncrement_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (gatePreparedIncrement u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState gatePreparedIncrement
      clearIncrementAction
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeActionActivate_ppsiControl
    (hpsi : psi > 0) (u : AgentState psi) :
    PpsiControlView.ofState (writeActionActivate hpsi u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeActionActivate
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeActionApplyOverwrite_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (writeActionApplyOverwrite u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeActionApplyOverwrite
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeActionApplyMoveFlip_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (writeActionApplyMoveFlip u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState writeActionApplyMoveFlip
    try dsimp only []
    repeat (first | rfl | split)

private theorem writeActionExecute_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeActionExecute hpsi l r) =
      ppsiControlPair (l, r) := by
  by_cases hedge : l.label < r.label ∨ r.label = ⟨0, hpsi⟩
  · let r0 := if r.write_state = .overwrite then
      writeActionApplyOverwrite r else r
    let r1 := if r0.write_state = .move_flip then
      writeActionApplyMoveFlip r0 else r0
    let r2 := if r1.write_state = .increment_group then
      if r1.bit = true then { r1 with bit := false }
      else { r1 with bit := true, write_state := .depart }
    else r1
    let l0 := if r2.label ≠ ⟨0, hpsi⟩ then
      { l with write_state := r2.write_state }
    else l
    have hr0 : PpsiControlView.ofState r0 =
        PpsiControlView.ofState r := by
      unfold r0
      split
      · exact writeActionApplyOverwrite_ppsiControl r
      · rfl
    have hr1 : PpsiControlView.ofState r1 =
        PpsiControlView.ofState r0 := by
      unfold r1
      split
      · exact writeActionApplyMoveFlip_ppsiControl r0
      · rfl
    have hr2 : PpsiControlView.ofState r2 =
        PpsiControlView.ofState r1 := by
      unfold r2 PpsiControlView.ofState
      repeat (first | rfl | split)
    have hl0 : PpsiControlView.ofState l0 =
        PpsiControlView.ofState l := by
      unfold l0 PpsiControlView.ofState
      repeat (first | rfl | split)
    have hr3 : PpsiControlView.ofState
          { r2 with write_state := .depart } =
        PpsiControlView.ofState r2 := rfl
    unfold writeActionExecute
    rw [if_pos hedge]
    change (PpsiControlView.ofState l0,
        PpsiControlView.ofState { r2 with write_state := .depart }) =
      (PpsiControlView.ofState l, PpsiControlView.ofState r)
    exact Prod.ext hl0 (hr3.trans (hr2.trans (hr1.trans hr0)))
  · unfold writeActionExecute
    rw [if_neg hedge]

private theorem writeAction_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeAction hpsi l r) = ppsiControlPair (l, r) := by
  let l0 := writeActionActivate hpsi l
  let r0 := writeActionActivate hpsi r
  change ppsiControlPair (writeActionExecute hpsi l0 r0) =
    ppsiControlPair (l, r)
  exact (writeActionExecute_ppsiControlPair hpsi l0 r0).trans
    (Prod.ext (writeActionActivate_ppsiControl hpsi l)
      (writeActionActivate_ppsiControl hpsi r))

private theorem moveWsigStart_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigStart l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState moveWsigStart
      moveWsigCheckGenWs
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigCheckLast_ppsiControl
    (u : AgentState psi) :
    PpsiControlView.ofState (moveWsigCheckLast u) =
      PpsiControlView.ofState u := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState moveWsigCheckLast
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigTransfer_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigTransfer l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState moveWsigTransfer
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigMoveWrite_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigMoveWrite l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState moveWsigMoveWrite
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigLeaderSignal_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigLeaderSignal l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState moveWsigLeaderSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigSignalMove_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigSignalMove l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState moveWsigSignalMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigEchoMove_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigEchoMove l r) = ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState moveWsigEchoMove
    try dsimp only []
    repeat (first | rfl | split)

private theorem moveWsigFinish_ppsiControlPair
    (l r : AgentState psi) :
    ppsiControlPair (moveWsigFinish l r) = ppsiControlPair (l, r) := by
  let q0 := moveWsigMoveWrite l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  change ppsiControlPair (moveWsigEchoMove q2.1 q2.2) =
    ppsiControlPair (l, r)
  exact (moveWsigEchoMove_ppsiControlPair q2.1 q2.2).trans
    ((moveWsigSignalMove_ppsiControlPair q1.1 q1.2).trans
      ((moveWsigLeaderSignal_ppsiControlPair q0.1 q0.2).trans
        (moveWsigMoveWrite_ppsiControlPair l r)))

private theorem moveWsig_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (moveWsig hpsi l r) = ppsiControlPair (l, r) := by
  let q0 := moveWsigStart l r
  let l1 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransfer l1 q0.2
  have hCheck : PpsiControlView.ofState l1 =
      PpsiControlView.ofState q0.1 := moveWsigCheckLast_ppsiControl q0.1
  have h1 : ppsiControlPair (l1, q0.2) = ppsiControlPair q0 :=
    Prod.ext hCheck rfl
  change ppsiControlPair (moveWsigFinish q1.1 q1.2) =
    ppsiControlPair (l, r)
  exact (moveWsigFinish_ppsiControlPair q1.1 q1.2).trans
    ((moveWsigTransfer_ppsiControlPair l1 q0.2).trans
      (h1.trans (moveWsigStart_ppsiControlPair l r)))

private theorem writeSeqAfterPrepare_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqAfterPrepare hpsi l r) =
      ppsiControlPair (l, r) := by
  let q := writeAction hpsi l r
  change ppsiControlPair (moveWsig hpsi q.1 q.2) =
    ppsiControlPair (l, r)
  exact (moveWsig_ppsiControlPair hpsi q.1 q.2).trans
    (writeAction_ppsiControlPair hpsi l r)

private theorem writeSeqIncrementGate_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (writeSeqIncrementGate hpsi l r) =
      ppsiControlPair (l, r) := by
  let q := writeSeqThroughPrepare hpsi l r
  let qg := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  have hg : ppsiControlPair qg = ppsiControlPair q :=
    Prod.ext (gatePreparedIncrement_ppsiControl q.1)
      (gatePreparedIncrement_ppsiControl q.2)
  change ppsiControlPair (writeSeqAfterPrepare hpsi qg.1 qg.2) =
    ppsiControlPair (l, r)
  exact (writeSeqAfterPrepare_ppsiControlPair hpsi qg.1 qg.2).trans
    (hg.trans (writeSeqThroughPrepare_ppsiControlPair hpsi l r))

theorem authorizedSuppressSigResetKill_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (authorizedReconcile (suppressSigResetKill hpsi) l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (suppressSigResetKill hpsi) l r
    (suppressSigResetKill_ppsiControlPair hpsi l.core r.core)

private theorem authorizedEliminateLeadersNoCollision_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (authorizedReconcile (eliminateLeadersNoCollision hpsi) l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair
    (eliminateLeadersNoCollision hpsi) l r
      (eliminateLeadersNoCollision_ppsiControlPair hpsi l.core r.core)

theorem authorizedWriteSeqIncrementGate_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (authorizedReconcile (writeSeqIncrementGate hpsi) l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair (writeSeqIncrementGate hpsi) l r
    (writeSeqIncrementGate_ppsiControlPair hpsi l.core r.core)

private theorem authorizedPostSuppress_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (authorizedPostSuppress hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  let q := authorizedReconcile (eliminateLeadersNoCollision hpsi) l r
  change authorizedPpsiControlPair
      (authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2) =
    authorizedPpsiControlPair (l, r)
  exact (authorizedWriteSeqIncrementGate_ppsiControlPair
      hpsi q.1 q.2).trans
    (authorizedEliminateLeadersNoCollision_ppsiControlPair hpsi l r)

private theorem normalizeDeletion_ppsiControl
    (u : AuthorizedAgentState psi) :
    PpsiControlView.ofState (normalizeDeletion u).core =
      PpsiControlView.ofState u.core := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState normalizeDeletion
    try dsimp only []
    repeat (first | rfl | split)

private theorem normalizeDeletion_leader
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

private theorem authorizedPpsiControlPair_frame_of_pair_eq
    (out mid before :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (heq : out = mid)
    (hframe : authorizedPpsiControlPair mid =
      authorizedPpsiControlPair before) :
    authorizedPpsiControlPair out =
      authorizedPpsiControlPair before := by
  subst mid
  exact hframe

private theorem authorizedPpsiControlPair_trans_target
    (out before :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (target : PpsiControlView psi × PpsiControlView psi)
    (hframe : authorizedPpsiControlPair out =
      authorizedPpsiControlPair before)
    (hbefore : authorizedPpsiControlPair before = target) :
    authorizedPpsiControlPair out = target := by
  rw [hframe]
  exact hbefore

attribute [local irreducible]
  wallSweepPreCheckResetBeforeSuppress
  wallSweepPreCheckResetNormalAfterSuppress
  wallSweepPreCheckResetNormalTail
  authorizedPostSuppress

private theorem wallSweepPreCheckResetNormalAfterSuppress_ppsiControlFrame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
    authorizedPpsiControlPair
        (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) =
      authorizedPpsiControlPair pre := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have heq := wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  have hkill := authorizedSuppressSigResetKill_ppsiControlPair
    hpsi pre.1 pre.2
  exact authorizedPpsiControlPair_frame_of_pair_eq
    (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2)
    pre heq hkill

attribute [local semireducible]
  wallSweepPreCheckResetNormalTail authorizedPostSuppress

private theorem wallSweepPreCheckResetNormalTail_ppsiControlFrame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
    authorizedPpsiControlPair
        (wallSweepPreCheckResetNormalTail hpsi kappa l r) =
      authorizedPpsiControlPair pre := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have heq : wallSweepPreCheckResetNormalTail hpsi kappa l r =
      authorizedPostSuppress hpsi after.1 after.2 := rfl
  have hafter :=
    wallSweepPreCheckResetNormalAfterSuppress_ppsiControlFrame
      hpsi kappa l r
  change authorizedPpsiControlPair after =
    authorizedPpsiControlPair pre at hafter
  have hpost := authorizedPostSuppress_ppsiControlPair
    hpsi after.1 after.2
  have hstep : authorizedPpsiControlPair
        (wallSweepPreCheckResetNormalTail hpsi kappa l r) =
      authorizedPpsiControlPair after :=
    authorizedPpsiControlPair_frame_of_pair_eq
      (wallSweepPreCheckResetNormalTail hpsi kappa l r)
      (authorizedPostSuppress hpsi after.1 after.2)
      after heq hpost
  exact authorizedPpsiControlPair_trans_target
    (wallSweepPreCheckResetNormalTail hpsi kappa l r)
    after (authorizedPpsiControlPair pre) hstep hafter

theorem markLeaderBirth_ppsiControlPair
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPpsiControlPair (markLeaderBirth born q) =
      authorizedPpsiControlPair q := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold authorizedPpsiControlPair ppsiControlPair
      PpsiControlView.ofState markLeaderBirth markComparisonForDeletion
    try dsimp only []
    repeat (first | rfl | split)

private theorem pPsi_ppsiControlPair_congr
    (hpsi : psi > 0)
    (l l' r r' : AgentState psi)
    (hlLeader : l'.leader = l.leader)
    (hrLeader : r'.leader = r.leader)
    (hlControl : PpsiControlView.ofState l' =
      PpsiControlView.ofState l)
    (hrControl : PpsiControlView.ofState r' =
      PpsiControlView.ofState r) :
    ppsiControlPair (pPsi hpsi l' r') =
      ppsiControlPair (pPsi hpsi l r) := by
  have hlLabel := congrArg PpsiControlView.label hlControl
  have hlProbe := congrArg PpsiControlView.probe hlControl
  have hlPhase := congrArg PpsiControlView.phase hlControl
  have hrLabel := congrArg PpsiControlView.label hrControl
  have hrProbe := congrArg PpsiControlView.probe hrControl
  have hrPhase := congrArg PpsiControlView.phase hrControl
  change l'.label = l.label at hlLabel
  change l'.probe = l.probe at hlProbe
  change l'.phase = l.phase at hlPhase
  change r'.label = r.label at hrLabel
  change r'.probe = r.probe at hrProbe
  change r'.phase = r.phase at hrPhase
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState
      pPsi
    dsimp only
    simp only [hlLeader, hrLeader, hlLabel, hlProbe, hlPhase,
      hrLabel, hrProbe, hrPhase]
    repeat (first | rfl | split)
  all_goals simp_all

private theorem pPsiLeaderProbeWall_ppsiControlPair_congr
    (hpsi : psi > 0)
    (l l' r r' : AgentState psi)
    (hlLeader : l'.leader = l.leader)
    (hrLeader : r'.leader = r.leader)
    (hlControl : PpsiControlView.ofState l' =
      PpsiControlView.ofState l)
    (hrControl : PpsiControlView.ofState r' =
      PpsiControlView.ofState r) :
    ppsiControlPair (pPsiLeaderProbeWall hpsi l' r') =
      ppsiControlPair (pPsiLeaderProbeWall hpsi l r) := by
  have hlLabel := congrArg PpsiControlView.label hlControl
  have hlProbe := congrArg PpsiControlView.probe hlControl
  have hlPhase := congrArg PpsiControlView.phase hlControl
  have hrLabel := congrArg PpsiControlView.label hrControl
  have hrProbe := congrArg PpsiControlView.probe hrControl
  have hrPhase := congrArg PpsiControlView.phase hrControl
  change l'.label = l.label at hlLabel
  change l'.probe = l.probe at hlProbe
  change l'.phase = l.phase at hlPhase
  change r'.label = r.label at hrLabel
  change r'.probe = r.probe at hrProbe
  change r'.phase = r.phase at hrPhase
  let l0' := if l'.leader = true then { l' with probe := false } else l'
  let r0' := if r'.leader = true ∨ l'.leader = true then
    { r' with probe := false } else r'
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false } else r
  change ppsiControlPair (pPsi hpsi l0' r0') =
    ppsiControlPair (pPsi hpsi l0 r0)
  apply pPsi_ppsiControlPair_congr hpsi
  · simp [l0', l0, hlLeader]
  · simp [r0', r0, hlLeader, hrLeader]
  · apply PpsiControlView.ext <;>
      simp [l0', l0, PpsiControlView.ofState,
        hlLeader, hlLabel, hlProbe, hlPhase]
  · apply PpsiControlView.ext <;>
      simp [r0', r0, PpsiControlView.ofState,
        hlLeader, hrLeader, hrLabel, hrProbe, hrPhase]

private theorem pPsiLeaderProbeWall_normalizeDeletion_ppsiControlPair
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    ppsiControlPair
        (pPsiLeaderProbeWall hpsi
          (normalizeDeletion l).core (normalizeDeletion r).core) =
      ppsiControlPair (pPsiLeaderProbeWall hpsi l.core r.core) := by
  exact pPsiLeaderProbeWall_ppsiControlPair_congr hpsi
    l.core (normalizeDeletion l).core
    r.core (normalizeDeletion r).core
    (normalizeDeletion_leader l) (normalizeDeletion_leader r)
    (normalizeDeletion_ppsiControl l) (normalizeDeletion_ppsiControl r)

attribute [local irreducible]
  wallSweepPreCheckResetNormalTail
  wallSweepPreCheckResetAuthorizedTransition

/-- On the ordinary priority-open branch, the complete authorized repair has
exactly the P-prime controls produced by its first physical stage. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    authorizedPpsiControlPair
        (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l.core r.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have heq : wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born tail :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hmark : authorizedPpsiControlPair (markLeaderBirth born tail) =
      authorizedPpsiControlPair tail :=
    markLeaderBirth_ppsiControlPair born tail
  have htail : authorizedPpsiControlPair tail =
      authorizedPpsiControlPair pre :=
    wallSweepPreCheckResetNormalTail_ppsiControlFrame hpsi kappa l r
  have htransition : authorizedPpsiControlPair
        (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) =
      authorizedPpsiControlPair tail :=
    authorizedPpsiControlPair_frame_of_pair_eq
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r)
      (markLeaderBirth born tail) tail heq hmark
  have hpre : authorizedPpsiControlPair pre =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l0.core r0.core) :=
    wallSweepPreCheckResetBeforeSuppress_ppsiControlPair
      hpsi kappa l0 r0
  have hnormalize : ppsiControlPair
        (pPsiLeaderProbeWall hpsi l0.core r0.core) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l.core r.core) :=
    pPsiLeaderProbeWall_normalizeDeletion_ppsiControlPair hpsi l r
  exact htransition.trans (htail.trans (hpre.trans hnormalize))

/-- Finite reification preserves the priority-open P-prime simulation
exactly. -/
theorem wallSweepPreCheckResetBounded_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase) :
    boundedPpsiControlPair
        (wallSweepPreCheckResetBoundedTransition hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l.erase.core r.erase.core) := by
  let q := wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  have herase := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l r
  change (q.1.erase, q.2.erase) =
    wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.erase r.erase at herase
  have hq := congrArg authorizedPpsiControlPair herase
  change boundedPpsiControlPair q =
    authorizedPpsiControlPair
      (wallSweepPreCheckResetAuthorizedTransition
        hpsi kappa l.erase r.erase) at hq
  exact hq.trans
    (wallSweepPreCheckResetAuthorized_priority_open_ppsiControlPair
      hpsi kappa l.erase r.erase hopen)

theorem deletionPriorityExpireOne_ppsiControl
    (old out : ExpiringAgentState psi kappa tau) :
    PpsiControlView.ofState
        (deletionPriorityExpireOne tau old out).core.erase.core =
      PpsiControlView.ofState out.core.erase.core := by
  apply PpsiControlView.ext
  all_goals
    unfold PpsiControlView.ofState deletionPriorityExpireOne
      pathExpireOne clearComparisonCarrier
      AuthorizedBoundedAgentState.erase BoundedAgentState.erase
    dsimp only
    repeat (first | rfl | split)

/-- The complete path-stall repair simulates one raw P-prime edge whenever
deletion priority is open at that edge. -/
theorem wallSweepPreCheckResetPathStall_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    expiringPpsiControlPair
        (wallSweepPreCheckResetPathStallTransition
          hpsi kappa tau l r) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi
          l.core.erase.core r.core.erase.core) := by
  let q := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  have hq :=
    wallSweepPreCheckResetBounded_priority_open_ppsiControlPair
      hpsi kappa l.core r.core hopen
  change (PpsiControlView.ofState q.1.erase.core,
      PpsiControlView.ofState q.2.erase.core) =
    ppsiControlPair
      (pPsiLeaderProbeWall hpsi
        l.core.erase.core r.core.erase.core) at hq
  have hl := deletionPriorityExpireOne_ppsiControl l lOut
  have hr := deletionPriorityExpireOne_ppsiControl r rOut
  change (PpsiControlView.ofState
        (deletionPriorityExpireOne tau l lOut).core.erase.core,
      PpsiControlView.ofState
        (deletionPriorityExpireOne tau r rOut).core.erase.core) =
    ppsiControlPair
      (pPsiLeaderProbeWall hpsi
        l.core.erase.core r.core.erase.core)
  exact (Prod.ext hl hr).trans hq

attribute [local semireducible]
  wallSweepPreCheckResetAuthorizedTransition

private theorem wallSweepPreCheckResetAuthorized_active_responder_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive r = true) :
    authorizedPpsiControlPair
        (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) =
      authorizedPpsiControlPair (l, r) := by
  have hrpath : r.core.path ≠ .bot := by
    cases hpath : r.core.path with
    | bot => simp [deletionActive, pathPresent, hpath] at hr
    | some label bit => simp
  have hnr := normalizeDeletion_eq_of_path_present r hrpath
  let l0 := normalizeDeletion l
  have hbranch :
      wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
        authorizedEliminateSig hpsi l0 r := by
    simp [wallSweepPreCheckResetAuthorizedTransition, l0, hnr, hr]
  rw [hbranch]
  exact (authorizedEliminateSig_ppsiControlPair hpsi l0 r).trans
    (Prod.ext (normalizeDeletion_ppsiControl l) rfl)

private theorem wallSweepPreCheckResetBounded_active_responder_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hr : deletionActive r.erase = true) :
    boundedPpsiControlPair
        (wallSweepPreCheckResetBoundedTransition hpsi kappa l r) =
      boundedPpsiControlPair (l, r) := by
  let q := wallSweepPreCheckResetBoundedTransition hpsi kappa l r
  have herase := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l r
  change (q.1.erase, q.2.erase) =
    wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.erase r.erase at herase
  have hq := congrArg authorizedPpsiControlPair herase
  change boundedPpsiControlPair q =
    authorizedPpsiControlPair
      (wallSweepPreCheckResetAuthorizedTransition
        hpsi kappa l.erase r.erase) at hq
  exact hq.trans
    (wallSweepPreCheckResetAuthorized_active_responder_ppsiControlPair
      hpsi kappa l.erase r.erase hr)

private theorem wallSweepPreCheckResetPathStall_active_responder_ppsiControlPair
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive r.core.erase = true) :
    expiringPpsiControlPair
        (wallSweepPreCheckResetPathStallTransition
          hpsi kappa tau l r) =
      expiringPpsiControlPair (l, r) := by
  let q := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  have hq :=
    wallSweepPreCheckResetBounded_active_responder_ppsiControlPair
      hpsi kappa l.core r.core hr
  change (PpsiControlView.ofState q.1.erase.core,
      PpsiControlView.ofState q.2.erase.core) =
    expiringPpsiControlPair (l, r) at hq
  have hl := deletionPriorityExpireOne_ppsiControl l lOut
  have hrFrame := deletionPriorityExpireOne_ppsiControl r rOut
  change (PpsiControlView.ofState
        (deletionPriorityExpireOne tau l lOut).core.erase.core,
      PpsiControlView.ofState
        (deletionPriorityExpireOne tau r rOut).core.erase.core) =
    expiringPpsiControlPair (l, r)
  exact (Prod.ext hl hrFrame).trans hq

/-- One active deletion edge frames the P-prime controls pointwise. -/
theorem wallSweepPreCheckResetPathStall_active_edge_ppsiControlFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
    PpsiControlConfigFrame C D := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := wallSweepPreCheckResetPathStallTransition
    hpsi kappa tau (C e) (C j)
  have hpair :=
    wallSweepPreCheckResetPathStall_active_responder_ppsiControlPair
      hpsi kappa tau (C e) (C j) hactive
  let D := localStep ring
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  change PpsiControlConfigFrame C D
  intro i
  by_cases hie : i = e
  · subst i
    rw [hleft]
    exact congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      rw [hright]
      exact congrArg Prod.snd hpair
    · have hsame : D i = C i := by
        simp [D, localStep, hie, hij, j]
      rw [hsame]

/-- The canonical deletion drain also frames every P-prime control. -/
theorem exists_wallSweepPreCheckResetDeletionDrain_ppsiControlFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C schedule
      NoActiveDeletion D ∧ PeaceViewConfigFrame C D ∧
        PpsiControlConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          PeaceViewConfigFrame.refl C, PpsiControlConfigFrame.refl C⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C1 := localStep ring
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
        have hstep := wallSweepPreCheckResetPathStall_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C1 < comparisonPathCount C ∧
          ResetEchoConfigFrame C C1 at hstep
        have hcontrol :=
          wallSweepPreCheckResetPathStall_active_edge_ppsiControlFrame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PpsiControlConfigFrame C C1 at hcontrol
        have hpeace :=
          wallSweepPreCheckResetPathStall_active_edge_peaceView_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PeaceViewConfigFrame C C1 at hpeace
        have hlt : comparisonPathCount C1 < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailPeace, htailControl⟩ :=
          ih (comparisonPathCount C1) hlt C1 rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hpeace.trans htailPeace
        · exact hcontrol.trans htailControl

private theorem pPsiLeaderProbeWall_leaders_false_of_not_birth
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hnotBirth : ¬ (r.probe = true ∧ isBarrier hpsi l r)) :
    (pPsiLeaderProbeWall hpsi l r).1.leader = false ∧
      (pPsiLeaderProbeWall hpsi l r).2.leader = false := by
  cases hp : r.probe with
  | false =>
      exact pPsiLeaderProbeWall_leaders_false_of_no_responder_probe
        hpsi l r hl hr hp
  | true =>
      have hnotBarrier : ¬ isBarrier hpsi l r :=
        fun hbarrier => hnotBirth ⟨hp, hbarrier⟩
      unfold isBarrier at hnotBarrier
      have haligned : r.label =
          ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
        Decidable.not_not.mp hnotBarrier
      exact pPsiLeaderProbeWall_aligned_probe_leaders_false
        hpsi l r hl hr haligned hp

theorem rawLeaderless_localStep_pPsiLeaderProbeWall_of_not_birth
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AgentState psi) (e : Fin n)
    (hleaderless : RawLeaderless C)
    (hnotBirth : ¬ ((C (ring.rightNeighbor e)).probe = true ∧
      isBarrier hpsi (C e) (C (ring.rightNeighbor e)))) :
    RawLeaderless
      (localStep ring (pPsiLeaderProbeWall hpsi) C e) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := pPsiLeaderProbeWall hpsi (C e) (C j)
  have hpair := pPsiLeaderProbeWall_leaders_false_of_not_birth
    hpsi (C e) (C j) (hleaderless e) (hleaderless j) hnotBirth
  intro i
  by_cases hie : i = e
  · subst i
    simpa [localStep, q, j] using hpair.1
  · by_cases hij : i = j
    · subst i
      simpa [localStep, q, j, hje] using hpair.2
    · simpa [localStep, hie, hij, j] using hleaderless i

private theorem ppsiControlRefines_localStep_of_priority_open
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n)
    (hrefine : PpsiControlConfigRefines raw physical)
    (hrawLeaderless : RawLeaderless raw)
    (hphysicalLeaderless : RawLeaderless (eraseExpiringConfig physical))
    (hopen : WallPriorityOpen
      (physical e) (physical (ring.rightNeighbor e))) :
    PpsiControlConfigRefines
      (localStep ring (pPsiLeaderProbeWall hpsi) raw e)
      (localStep ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        physical e) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let rawPair := pPsiLeaderProbeWall hpsi (raw e) (raw j)
  let physicalPair := wallSweepPreCheckResetPathStallTransition
    hpsi kappa tau (physical e) (physical j)
  have hphysicalPair :=
    wallSweepPreCheckResetPathStall_priority_open_ppsiControlPair
      hpsi kappa tau (physical e) (physical j) hopen
  have hinputCongr := pPsiLeaderProbeWall_ppsiControlPair_congr hpsi
    (raw e) (physical e).core.erase.core
    (raw j) (physical j).core.erase.core
    ((hphysicalLeaderless e).trans (hrawLeaderless e).symm)
    ((hphysicalLeaderless j).trans (hrawLeaderless j).symm)
    (hrefine e) (hrefine j)
  have hpair : expiringPpsiControlPair physicalPair =
      ppsiControlPair rawPair := hphysicalPair.trans hinputCongr
  change (PpsiControlView.ofState physicalPair.1.core.erase.core,
      PpsiControlView.ofState physicalPair.2.core.erase.core) =
    (PpsiControlView.ofState rawPair.1,
      PpsiControlView.ofState rawPair.2) at hpair
  intro i
  by_cases hie : i = e
  · subst i
    simpa [localStep, physicalPair, rawPair, j] using
      congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      simpa [localStep, physicalPair, rawPair, j, hje] using
        congrArg Prod.snd hpair
    · simpa [localStep, hie, hij, j] using hrefine i

private theorem raw_birth_edge_creates_physical_leader
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n)
    (hrefine : PpsiControlConfigRefines raw physical)
    (hphysicalLeaderless : RawLeaderless (eraseExpiringConfig physical))
    (hopen : WallPriorityOpen
      (physical e) (physical (ring.rightNeighbor e)))
    (hprobe : (raw (ring.rightNeighbor e)).probe = true)
    (hbarrier : isBarrier hpsi (raw e)
      (raw (ring.rightNeighbor e))) :
    RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          physical e)) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have heLabel := congrArg PpsiControlView.label (hrefine e)
  have hjLabel := congrArg PpsiControlView.label (hrefine j)
  have hjProbe := congrArg PpsiControlView.probe (hrefine j)
  change (physical e).core.erase.core.label = (raw e).label at heLabel
  change (physical j).core.erase.core.label = (raw j).label at hjLabel
  change (physical j).core.erase.core.probe = (raw j).probe at hjProbe
  have hprobePhysical : (physical j).core.erase.core.probe = true :=
    hjProbe.trans hprobe
  have hbarrierPhysical : isBarrier hpsi
      (physical e).core.erase.core (physical j).core.erase.core := by
    unfold isBarrier at hbarrier ⊢
    intro haligned
    apply hbarrier
    calc
      (raw j).label = (physical j).core.erase.core.label := hjLabel.symm
      _ = ⟨((physical e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := haligned
      _ = ⟨((raw e).label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by rw [heLabel]
  let q := wallSweepPreCheckResetPathStallTransition
    hpsi kappa tau (physical e) (physical j)
  have hbirth : q.2.core.erase.core.leader = true :=
    wallSweepPreCheckResetPathStall_priority_open_barrier_probe_birth
      hpsi (physical e) (physical j) hopen
        (hphysicalLeaderless e) (hphysicalLeaderless j)
        hprobePhysical hbarrierPhysical
  let D := localStep ring
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    physical e
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  refine ⟨j, ?_⟩
  change (D j).core.erase.core.leader = true
  rw [hright]
  exact hbirth

/-- A complete repaired edge selected in a globally leaderless configuration
can create at most one physical leader.  Hence any leader it creates is the
unique first leader of the whole ring. -/
theorem localStep_first_physical_leader_unique
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hhas : RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          C e))) :
    hasUniqueLeader n
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          C e)) := by
  let j := ring.rightNeighbor e
  let T := wallSweepPreCheckResetPathStallTransition hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hDe : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hDj : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  have hpair :=
    wallSweepPreCheckResetPathStall_followers_not_both_leaders
      hpsi (C e) (C j) (hleaderless e) (hleaderless j)
  change ¬ (q.1.core.erase.core.leader = true ∧
    q.2.core.erase.core.leader = true) at hpair
  have touched_of_leader : ∀ {i : Fin n},
      (D i).core.erase.core.leader = true → i = e ∨ i = j := by
    intro i hi
    by_cases hie : i = e
    · exact .inl hie
    by_cases hij : i = j
    · exact .inr hij
    have hsame : D i = C i := by
      simp [D, T, localStep, j, hie, hij]
    have hCi : (C i).core.erase.core.leader = false := by
      change (eraseExpiringConfig C i).leader = false
      exact hleaderless i
    rw [hsame, hCi] at hi
    contradiction
  change RawHasLeader (eraseExpiringConfig D) at hhas
  obtain ⟨leader, hleader⟩ := hhas
  have hleaderTouched := touched_of_leader hleader
  refine ⟨leader, by simpa [AgentState.isLeader] using hleader, ?_⟩
  intro i hi
  have hi' : (D i).core.erase.core.leader = true := by
    change (eraseExpiringConfig D i).isLeader at hi
    change (eraseExpiringConfig D i).leader = true
    exact hi
  have hiTouched := touched_of_leader hi'
  rcases hleaderTouched with hleaderE | hleaderJ
  · subst leader
    rcases hiTouched with hiE | hiJ
    · exact hiE
    · exfalso
      apply hpair
      constructor
      · rw [← hDe]
        exact hleader
      · rw [← hDj]
        simpa [hiJ] using hi'
  · subst leader
    rcases hiTouched with hiE | hiJ
    · exfalso
      apply hpair
      constructor
      · rw [← hDe]
        simpa [hiE] using hi'
      · rw [← hDj]
        exact hleader
    · exact hiJ

private theorem runLocalSchedule_append_expiring
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (first second : DetSchedule n) :
    runLocalSchedule ring T C (first ++ second) =
      runLocalSchedule ring T
        (runLocalSchedule ring T C first) second := by
  induction first generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih (localStep ring T C e)

private theorem exists_stopped_unique_preCheckReset_simulation
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau)
    (hrefine : PpsiControlConfigRefines raw physical)
    (hrawLeaderless : RawLeaderless raw)
    (hphysicalLeaderless : RawLeaderless (eraseExpiringConfig physical))
    (word : DetSchedule n)
    (hfinal : RawHasLeader
      (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) raw word)) :
    ∃ actual : DetSchedule n,
      actual.length ≤ word.length * (n + 1) ∧
      hasUniqueLeader n
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
            physical actual)) := by
  induction word generalizing raw physical with
  | nil =>
      simp only [runLocalSchedule] at hfinal
      obtain ⟨i, hi⟩ := hfinal
      rw [hrawLeaderless i] at hi
      contradiction
  | cons e rest ih =>
      obtain ⟨drain, hdrainLength, _hdrainEmpty, hnoActive,
        hpeace, hcontrol⟩ :=
        exists_wallSweepPreCheckResetDeletionDrain_ppsiControlFrame
          hpsi ring hn physical
      let drained := runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        physical drain
      change NoActiveDeletion drained at hnoActive
      change PeaceViewConfigFrame physical drained at hpeace
      change PpsiControlConfigFrame physical drained at hcontrol
      have hrefineDrained : PpsiControlConfigRefines raw drained :=
        hrefine.of_frame hcontrol
      have hphysicalDrainedLeaderless :
          RawLeaderless (eraseExpiringConfig drained) :=
        eraseExpiringConfig_leaderless_of_peaceFrame
          hphysicalLeaderless hpeace
      have hopen : WallPriorityOpen
          (drained e) (drained (ring.rightNeighbor e)) :=
        WallPriorityOpen.of_noActiveDeletion drained hnoActive ring e
      let raw1 := localStep ring (pPsiLeaderProbeWall hpsi) raw e
      let physical1 := localStep ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        drained e
      by_cases hbirth :
          (raw (ring.rightNeighbor e)).probe = true ∧
            isBarrier hpsi (raw e) (raw (ring.rightNeighbor e))
      · have hphysicalBirth : RawHasLeader
            (eraseExpiringConfig physical1) := by
          exact raw_birth_edge_creates_physical_leader
            hpsi kappa tau ring hn raw drained e hrefineDrained
              hphysicalDrainedLeaderless hopen hbirth.1 hbirth.2
        have hphysicalUnique : hasUniqueLeader n
            (eraseExpiringConfig physical1) :=
          localStep_first_physical_leader_unique
            hpsi ring hn drained e hphysicalDrainedLeaderless
              hphysicalBirth
        refine ⟨drain ++ [e], ?_⟩
        refine ⟨?_, ?_⟩
        · have hcount := comparisonPathCount_le physical
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.zero_add, Nat.succ_mul]
          omega
        · rw [runLocalSchedule_append_expiring]
          simpa [physical1, drained, runLocalSchedule] using hphysicalUnique
      · have hraw1Leaderless : RawLeaderless raw1 :=
          rawLeaderless_localStep_pPsiLeaderProbeWall_of_not_birth
            hpsi ring hn raw e hrawLeaderless hbirth
        have hrefine1 : PpsiControlConfigRefines raw1 physical1 :=
          ppsiControlRefines_localStep_of_priority_open
            hpsi kappa tau ring hn raw drained e hrefineDrained
              hrawLeaderless hphysicalDrainedLeaderless hopen
        by_cases hphysical1 : RawHasLeader (eraseExpiringConfig physical1)
        · have hphysicalUnique : hasUniqueLeader n
              (eraseExpiringConfig physical1) :=
            localStep_first_physical_leader_unique
              hpsi ring hn drained e hphysicalDrainedLeaderless hphysical1
          refine ⟨drain ++ [e], ?_⟩
          refine ⟨?_, ?_⟩
          · have hcount := comparisonPathCount_le physical
            simp only [List.length_append, List.length_cons, List.length_nil,
              Nat.zero_add, Nat.succ_mul]
            omega
          · rw [runLocalSchedule_append_expiring]
            simpa [physical1, drained, runLocalSchedule] using hphysicalUnique
        · have hphysical1Leaderless :
              RawLeaderless (eraseExpiringConfig physical1) :=
            RawLeaderless.of_not_hasLeader hphysical1
          have hfinal1 : RawHasLeader
              (runLocalSchedule ring (pPsiLeaderProbeWall hpsi)
                raw1 rest) := by
            simpa [raw1, runLocalSchedule] using hfinal
          obtain ⟨tail, htailLength, htail⟩ :=
            ih raw1 physical1 hrefine1
            hraw1Leaderless hphysical1Leaderless hfinal1
          refine ⟨drain ++ (e :: tail), ?_⟩
          refine ⟨?_, ?_⟩
          · have hcount := comparisonPathCount_le physical
            simp only [List.length_append, List.length_cons, Nat.succ_mul]
            omega
          · rw [runLocalSchedule_append_expiring]
            simpa [physical1, drained, runLocalSchedule] using htail

/-- From a physically leaderless input on a nondivisible ring, the complete
repaired transition has a bounded schedule ending at the unique first physical
leader.  The theorem does not claim that arbitrary pre-existing leaders have
already been eliminated. -/
theorem exists_preCheckReset_hasUniqueLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ actual : DetSchedule n,
      actual.length ≤ (2 * n + 1) * (n + 1) ∧
      hasUniqueLeader n
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
            C actual)) := by
  obtain ⟨word, hwordLength, hrawFinal⟩ :=
    exists_pPsiLeaderProbeWall_hasLeader_of_not_dvd
      hpsi ring hn hndvd (eraseExpiringConfig C)
  obtain ⟨actual, hactualLength, hactualUnique⟩ :=
    exists_stopped_unique_preCheckReset_simulation
      hpsi ring hn (eraseExpiringConfig C) C (fun _ => rfl)
        hleaderless hleaderless word hrawFinal
  refine ⟨actual, ?_, hactualUnique⟩
  exact Nat.le_trans hactualLength
    (Nat.mul_le_mul_right (n + 1) hwordLength)

/-- If `psi` does not divide the ring size, the complete repaired transition
has a finite deterministic schedule reaching a physical leader from every
finite path-stall configuration.  Deletion drains are inserted only where the
birth event itself marked comparison material. -/
theorem exists_preCheckReset_hasLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ actual : DetSchedule n,
      actual.length ≤ (2 * n + 1) * (n + 1) ∧
      RawHasLeader
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
            C actual)) := by
  by_cases hleader : RawHasLeader (eraseExpiringConfig C)
  · exact ⟨[], by simp, by simpa [runLocalSchedule] using hleader⟩
  · have hleaderless : RawLeaderless (eraseExpiringConfig C) :=
      RawLeaderless.of_not_hasLeader hleader
    obtain ⟨word, _hwordLength, hrawFinal⟩ :=
      exists_pPsiLeaderProbeWall_hasLeader_of_not_dvd
        hpsi ring hn hndvd (eraseExpiringConfig C)
    obtain ⟨actual, hactualLength, hactualUnique⟩ :=
      exists_stopped_unique_preCheckReset_simulation
        hpsi ring hn (eraseExpiringConfig C) C (fun _ => rfl)
          hleaderless hleaderless word hrawFinal
    refine ⟨actual, ?_, ?_⟩
    · exact Nat.le_trans hactualLength
        (Nat.mul_le_mul_right (n + 1) _hwordLength)
    · obtain ⟨leader, hleader, _⟩ := hactualUnique
      exact ⟨leader, by simpa [AgentState.isLeader] using hleader⟩

/-! ## Responder-leader signal-sink lift -/

private theorem eliminateLeadersNoCollisionSignalLeaderSink_ppsiControlPair
    (nextLabel : Fin psi) (l r : AgentState psi) :
    ppsiControlPair
        (eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r) =
      ppsiControlPair (l, r) := by
  apply Prod.ext <;> apply PpsiControlView.ext
  all_goals
    unfold ppsiControlPair PpsiControlView.ofState
      eliminateLeadersNoCollisionSignalLeaderSink
    try dsimp only []
    repeat (first | rfl | split)

private theorem eliminateLeadersNoCollisionLeaderSink_ppsiControlPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    ppsiControlPair (eliminateLeadersNoCollisionLeaderSink hpsi l r) =
      ppsiControlPair (l, r) := by
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  change ppsiControlPair
      (eliminateLeadersNoCollisionSignalLeaderSink
        nextLabel q1.1 q1.2) = ppsiControlPair (l, r)
  exact (eliminateLeadersNoCollisionSignalLeaderSink_ppsiControlPair
      nextLabel q1.1 q1.2).trans
    ((eliminateLeadersNoCollisionMove_ppsiControlPair
      nextLabel q0.1 q0.2).trans
      (eliminateLeadersNoCollisionFire_ppsiControlPair hpsi l r))

private theorem authorizedEliminateLeadersNoCollisionLeaderSink_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (authorizedReconcile
          (eliminateLeadersNoCollisionLeaderSink hpsi) l r) =
      authorizedPpsiControlPair (l, r) :=
  authorizedReconcile_ppsiControlPair
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
      (eliminateLeadersNoCollisionLeaderSink_ppsiControlPair
        hpsi l.core r.core)

private theorem authorizedPostSuppressLeaderSink_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (authorizedPostSuppressLeaderSink hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  let q := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  change authorizedPpsiControlPair
      (authorizedReconcile (writeSeqIncrementGate hpsi) q.1 q.2) =
    authorizedPpsiControlPair (l, r)
  exact (authorizedWriteSeqIncrementGate_ppsiControlPair
      hpsi q.1 q.2).trans
    (authorizedEliminateLeadersNoCollisionLeaderSink_ppsiControlPair
      hpsi l r)

private theorem wallSweepPreCheckResetLeaderSinkNormalTail_ppsiControlFrame
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
    authorizedPpsiControlPair
        (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) =
      authorizedPpsiControlPair pre := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have heq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := rfl
  have hafter :=
    wallSweepPreCheckResetNormalAfterSuppress_ppsiControlFrame
      hpsi kappa l r
  change authorizedPpsiControlPair after =
    authorizedPpsiControlPair pre at hafter
  have hpost := authorizedPostSuppressLeaderSink_ppsiControlPair
    hpsi after.1 after.2
  have hstep : authorizedPpsiControlPair
        (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) =
      authorizedPpsiControlPair after :=
    authorizedPpsiControlPair_frame_of_pair_eq
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r)
      (authorizedPostSuppressLeaderSink hpsi after.1 after.2)
      after heq hpost
  exact authorizedPpsiControlPair_trans_target
    (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r)
    after (authorizedPpsiControlPair pre) hstep hafter

attribute [local irreducible]
  wallSweepPreCheckResetLeaderSinkNormalTail
  wallSweepPreCheckResetLeaderSinkAuthorizedTransition
  authorizedPostSuppressLeaderSink

/-- The leader-sink transition has exactly the raw P-prime controls on every
priority-open edge.  The extra Algorithm-15 guard writes only `signal_B`. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    authorizedPpsiControlPair
        (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l.core r.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have heq : wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r = markLeaderBirth born tail :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hmark : authorizedPpsiControlPair (markLeaderBirth born tail) =
      authorizedPpsiControlPair tail :=
    markLeaderBirth_ppsiControlPair born tail
  have htail : authorizedPpsiControlPair tail =
      authorizedPpsiControlPair pre :=
    wallSweepPreCheckResetLeaderSinkNormalTail_ppsiControlFrame
      hpsi kappa l r
  have htransition : authorizedPpsiControlPair
        (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l r) =
      authorizedPpsiControlPair tail :=
    authorizedPpsiControlPair_frame_of_pair_eq
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r)
      (markLeaderBirth born tail) tail heq hmark
  have hpre : authorizedPpsiControlPair pre =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l0.core r0.core) :=
    wallSweepPreCheckResetBeforeSuppress_ppsiControlPair
      hpsi kappa l0 r0
  have hnormalize : ppsiControlPair
        (pPsiLeaderProbeWall hpsi l0.core r0.core) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l.core r.core) :=
    pPsiLeaderProbeWall_normalizeDeletion_ppsiControlPair hpsi l r
  exact htransition.trans (htail.trans (hpre.trans hnormalize))

/-- Finite reification preserves the leader-sink P-prime simulation. -/
theorem wallSweepPreCheckResetLeaderSinkBounded_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hopen : AuthorizedPriorityOpen l.erase r.erase) :
    boundedPpsiControlPair
        (wallSweepPreCheckResetLeaderSinkBoundedTransition
          hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi l.erase.core r.erase.core) := by
  let q := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  have herase := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l r
  change (q.1.erase, q.2.erase) =
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.erase r.erase at herase
  have hq := congrArg authorizedPpsiControlPair herase
  change boundedPpsiControlPair q =
    authorizedPpsiControlPair
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l.erase r.erase) at hq
  exact hq.trans
    (wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_ppsiControlPair
      hpsi kappa l.erase r.erase hopen)

/-- Expiry preserves the priority-open P-prime projection for the leader-sink
transition. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    expiringPpsiControlPair
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau l r) =
      ppsiControlPair
        (pPsiLeaderProbeWall hpsi
          l.core.erase.core r.core.erase.core) := by
  let q := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  have hq :=
    wallSweepPreCheckResetLeaderSinkBounded_priority_open_ppsiControlPair
      hpsi kappa l.core r.core hopen
  change (PpsiControlView.ofState q.1.erase.core,
      PpsiControlView.ofState q.2.erase.core) =
    ppsiControlPair
      (pPsiLeaderProbeWall hpsi
        l.core.erase.core r.core.erase.core) at hq
  have hl := deletionPriorityExpireOne_ppsiControl l lOut
  have hr := deletionPriorityExpireOne_ppsiControl r rOut
  change (PpsiControlView.ofState
        (deletionPriorityExpireOne tau l lOut).core.erase.core,
      PpsiControlView.ofState
        (deletionPriorityExpireOne tau r rOut).core.erase.core) =
    ppsiControlPair
      (pPsiLeaderProbeWall hpsi
        l.core.erase.core r.core.erase.core)
  exact (Prod.ext hl hr).trans hq

/-- The probe wall turns every edge initiated by an existing leader into a
locally normalized P-prime edge: the responder label is the leader's
successor label and neither endpoint retains a probe. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_leader_controls
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false) :
    let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    q.1.core.erase.core.label = l.core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨(l.core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      q.1.core.erase.core.probe = false ∧
      q.2.core.erase.core.probe = false := by
  let raw := pPsiLeaderProbeWall hpsi
    l.core.erase.core r.core.erase.core
  have hraw :
      raw.1.label = l.core.erase.core.label ∧
        raw.2.label =
          ⟨(l.core.erase.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ ∧
        raw.1.probe = false ∧ raw.2.probe = false := by
    simp [raw, pPsiLeaderProbeWall, pPsi, hlLeader, hrFollower]
  let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hcontrols :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_ppsiControlPair
      hpsi kappa tau l r hopen
  change expiringPpsiControlPair q = ppsiControlPair raw at hcontrols
  have hleftLabel := congrArg (fun views => views.1.label) hcontrols
  have hrightLabel := congrArg (fun views => views.2.label) hcontrols
  have hleftProbe := congrArg (fun views => views.1.probe) hcontrols
  have hrightProbe := congrArg (fun views => views.2.probe) hcontrols
  change q.1.core.erase.core.label = raw.1.label at hleftLabel
  change q.2.core.erase.core.label = raw.2.label at hrightLabel
  change q.1.core.erase.core.probe = raw.1.probe at hleftProbe
  change q.2.core.erase.core.probe = raw.2.probe at hrightProbe
  exact ⟨hleftLabel.trans hraw.1,
    hrightLabel.trans hraw.2.1,
    hleftProbe.trans hraw.2.2.1,
    hrightProbe.trans hraw.2.2.2⟩

private theorem wallSweepPreCheckResetLeaderSinkPathStall_active_edge_ppsiControlFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PpsiControlConfigFrame C D := by
  rw [localStep_leaderSink_eq_preCheckReset_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPreCheckResetPathStall_active_edge_ppsiControlFrame
    hpsi ring hn C e hactive

/-- The leader-sink deletion drain also frames every P-prime control. -/
theorem exists_wallSweepPreCheckResetLeaderSinkDeletionDrain_ppsiControlFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C schedule
      NoActiveDeletion D ∧ PeaceViewConfigFrame C D ∧
        PpsiControlConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          PeaceViewConfigFrame.refl C, PpsiControlConfigFrame.refl C⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C1 := localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e
        have hstep := wallSweepPreCheckResetLeaderSink_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C1 < comparisonPathCount C ∧
          ResetEchoConfigFrame C C1 at hstep
        have hcontrol :=
          wallSweepPreCheckResetLeaderSinkPathStall_active_edge_ppsiControlFrame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PpsiControlConfigFrame C C1 at hcontrol
        have hpeace :=
          wallSweepPreCheckResetLeaderSink_active_edge_peaceView_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PeaceViewConfigFrame C C1 at hpeace
        have hlt : comparisonPathCount C1 < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailPeace, htailControl⟩ :=
          ih (comparisonPathCount C1) hlt C1 rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hpeace.trans htailPeace
        · exact hcontrol.trans htailControl

/-! ## Nondivisible first-leader lift for the leader-sink transition -/

theorem ppsiControlRefines_localStepLeaderSink_of_priority_open
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n)
    (hrefine : PpsiControlConfigRefines raw physical)
    (hrawLeaderless : RawLeaderless raw)
    (hphysicalLeaderless : RawLeaderless (eraseExpiringConfig physical))
    (hopen : WallPriorityOpen
      (physical e) (physical (ring.rightNeighbor e))) :
    PpsiControlConfigRefines
      (localStep ring (pPsiLeaderProbeWall hpsi) raw e)
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        physical e) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let rawPair := pPsiLeaderProbeWall hpsi (raw e) (raw j)
  let physicalPair := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau (physical e) (physical j)
  have hphysicalPair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_ppsiControlPair
      hpsi kappa tau (physical e) (physical j) hopen
  have hinputCongr := pPsiLeaderProbeWall_ppsiControlPair_congr hpsi
    (raw e) (physical e).core.erase.core
    (raw j) (physical j).core.erase.core
    ((hphysicalLeaderless e).trans (hrawLeaderless e).symm)
    ((hphysicalLeaderless j).trans (hrawLeaderless j).symm)
    (hrefine e) (hrefine j)
  have hpair : expiringPpsiControlPair physicalPair =
      ppsiControlPair rawPair := hphysicalPair.trans hinputCongr
  change (PpsiControlView.ofState physicalPair.1.core.erase.core,
      PpsiControlView.ofState physicalPair.2.core.erase.core) =
    (PpsiControlView.ofState rawPair.1,
      PpsiControlView.ofState rawPair.2) at hpair
  intro i
  by_cases hie : i = e
  · subst i
    simpa [localStep, physicalPair, rawPair, j] using
      congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      simpa [localStep, physicalPair, rawPair, j, hje] using
        congrArg Prod.snd hpair
    · simpa [localStep, hie, hij, j] using hrefine i

theorem raw_birth_edge_creates_physical_leaderSink
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n)
    (hrefine : PpsiControlConfigRefines raw physical)
    (hphysicalLeaderless : RawLeaderless (eraseExpiringConfig physical))
    (hopen : WallPriorityOpen
      (physical e) (physical (ring.rightNeighbor e)))
    (hprobe : (raw (ring.rightNeighbor e)).probe = true)
    (hbarrier : isBarrier hpsi (raw e)
      (raw (ring.rightNeighbor e))) :
    RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          physical e)) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have heLabel := congrArg PpsiControlView.label (hrefine e)
  have hjLabel := congrArg PpsiControlView.label (hrefine j)
  have hjProbe := congrArg PpsiControlView.probe (hrefine j)
  change (physical e).core.erase.core.label = (raw e).label at heLabel
  change (physical j).core.erase.core.label = (raw j).label at hjLabel
  change (physical j).core.erase.core.probe = (raw j).probe at hjProbe
  have hprobePhysical : (physical j).core.erase.core.probe = true :=
    hjProbe.trans hprobe
  have hbarrierPhysical : isBarrier hpsi
      (physical e).core.erase.core (physical j).core.erase.core := by
    unfold isBarrier at hbarrier ⊢
    intro haligned
    apply hbarrier
    calc
      (raw j).label = (physical j).core.erase.core.label := hjLabel.symm
      _ = ⟨((physical e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := haligned
      _ = ⟨((raw e).label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by rw [heLabel]
  let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau (physical e) (physical j)
  have hbirth : q.2.core.erase.core.leader = true :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_barrier_probe_birth
      hpsi (physical e) (physical j) hopen
        (hphysicalLeaderless e) (hphysicalLeaderless j)
        hprobePhysical hbarrierPhysical
  let D := localStep ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
    physical e
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  refine ⟨j, ?_⟩
  change (D j).core.erase.core.leader = true
  rw [hright]
  exact hbirth

/-- A repaired priority-open interaction that creates a new initiator leader
also leaves its responder label aligned one step clockwise.  The proof rules
out the only unaligned follower/follower P-prime branch: that branch would
produce a label-zero responder leader, contradicting the certified nonzero
CHECK-birth/WRITE-migration endpoint. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_new_initiator_aligned
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hout : (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).1.core.erase.core.leader = true) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.2.core.erase.core.label =
      ⟨(out.1.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  let raw := pPsiLeaderProbeWall hpsi
    l.core.erase.core r.core.erase.core
  change out.2.core.erase.core.label =
    ⟨(out.1.core.erase.core.label.val + 1) % psi,
      Nat.mod_lt _ hpsi⟩
  have hmigration :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_new_initiator_check_migration
      hpsi l r hopen hl hr hout
  have hcontrol :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_ppsiControlPair
      hpsi kappa tau l r hopen
  change expiringPpsiControlPair out = ppsiControlPair raw at hcontrol
  have hleft := congrArg (fun q => q.1.label) hcontrol
  have hright := congrArg (fun q => q.2.label) hcontrol
  change out.1.core.erase.core.label = raw.1.label at hleft
  change out.2.core.erase.core.label = raw.2.label at hright
  have hbeforeWriteLabel :=
    hmigration.authorized.beforeWriteSource.2.2.1
  have hbeforeWriteNonzero :=
    hmigration.authorized.beforeWriteSource.2.2.2
  have houtLabel := hmigration.outputResponder.2
  have houtNonzero : out.2.core.erase.core.label ≠ ⟨0, hpsi⟩ := by
    intro hzero
    apply hbeforeWriteNonzero
    rw [hbeforeWriteLabel, ← houtLabel, hzero]
  have hrawFollower : raw.2.leader = false := by
    cases hraw : raw.2.leader
    · rfl
    · exfalso
      apply houtNonzero
      exact hright.trans
        (pPsiLeaderProbeWall_responder_label_zero_of_followers_of_output_leader
          hpsi l.core.erase.core r.core.erase.core hl hr hraw)
  have hrawAligned :=
    pPsiLeaderProbeWall_responder_aligned_of_followers_of_output_follower
      hpsi l.core.erase.core r.core.erase.core hl hr hrawFollower
  have hrawLeft := pPsiLeaderProbeWall_initiator_label
    hpsi l.core.erase.core r.core.erase.core
  change raw.1.label = l.core.erase.core.label at hrawLeft
  have hinputLeft : l.core.erase.core.label =
      out.1.core.erase.core.label := hrawLeft.symm.trans hleft.symm
  exact hright.trans (hrawAligned.trans (by rw [hinputLeft]))

structure LocalStepInitiatorCheckMigration
    (hpsi : psi > 0)
    (beforeCheck afterCheck beforeWrite authorizedOut :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (edgeOut : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (e j : Fin n) : Prop where
  edge : ExpiringInitiatorCheckMigration hpsi
    beforeCheck afterCheck beforeWrite authorizedOut edgeOut
  initiatorLeader : (D e).core.erase.core.leader = true
  responder :
    (D j).core.erase.core.leader = false ∧
      (D j).core.erase.core.label = ⟨psi - 1, by omega⟩
  aligned :
    (D j).core.erase.core.label =
      ⟨((D e).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- If the scheduled initiator becomes the first physical leader, the local
ring step exposes the same CHECK-birth/WRITE-migration certificate as the edge
transition, and the neighboring responder is a follower at label `psi - 1`. -/
theorem localStepLeaderSink_first_physical_leader_initiator_check_migration
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hleft : (localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e e).core.erase.core.leader = true) :
    LocalStepInitiatorCheckMigration hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion (C e).core.erase)
        (normalizeDeletion (C (ring.rightNeighbor e)).core.erase))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion (C e).core.erase)
        (normalizeDeletion (C (ring.rightNeighbor e)).core.erase))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa
        (C e).core.erase (C (ring.rightNeighbor e)).core.erase)
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa
        (C e).core.erase (C (ring.rightNeighbor e)).core.erase)
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau
        (C e) (C (ring.rightNeighbor e)))
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e)
      e (ring.rightNeighbor e) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hDe : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hDj : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  have hqLeft : q.1.core.erase.core.leader = true :=
    (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.leader) hDe).symm.trans hleft
  have hedge :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_new_initiator_check_migration
      hpsi (C e) (C j) hopen (hleaderless e) (hleaderless j) hqLeft
  have hDRightLeader : (D j).core.erase.core.leader = false :=
    (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.leader) hDj).trans hedge.outputResponder.1
  have hDRightLabel : (D j).core.erase.core.label =
      ⟨psi - 1, by omega⟩ :=
    (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hDj).trans hedge.outputResponder.2
  have hqAligned :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_new_initiator_aligned
      hpsi (C e) (C j) hopen (hleaderless e) (hleaderless j) hqLeft
  have hDAligned : (D j).core.erase.core.label =
      ⟨((D e).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    rw [hDe, hDj]
    exact hqAligned
  have hcertificate : LocalStepInitiatorCheckMigration hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion (C e).core.erase)
        (normalizeDeletion (C j).core.erase))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion (C e).core.erase)
        (normalizeDeletion (C j).core.erase))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa
        (C e).core.erase (C j).core.erase)
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa
        (C e).core.erase (C j).core.erase)
      q D e j := {
    edge := hedge
    initiatorLeader := hleft
    responder := ⟨hDRightLeader, hDRightLabel⟩
    aligned := hDAligned }
  simpa only [j, T, q, D] using hcertificate

/-- A priority-open leader-sink edge selected in a globally leaderless
configuration can create at most one physical leader. -/
theorem localStepLeaderSink_first_physical_leader_unique
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hhas : RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          C e))) :
    hasUniqueLeader n
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          C e)) := by
  let j := ring.rightNeighbor e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hDe : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hDj : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  have hpair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_followers_not_both
      hpsi (C e) (C j) hopen (hleaderless e) (hleaderless j)
  change ¬ (q.1.core.erase.core.leader = true ∧
    q.2.core.erase.core.leader = true) at hpair
  have touched_of_leader : ∀ {i : Fin n},
      (D i).core.erase.core.leader = true → i = e ∨ i = j := by
    intro i hi
    by_cases hie : i = e
    · exact .inl hie
    by_cases hij : i = j
    · exact .inr hij
    have hsame : D i = C i := by
      simp [D, T, localStep, j, hie, hij]
    have hCi : (C i).core.erase.core.leader = false := by
      change (eraseExpiringConfig C i).leader = false
      exact hleaderless i
    rw [hsame, hCi] at hi
    contradiction
  change RawHasLeader (eraseExpiringConfig D) at hhas
  obtain ⟨leader, hleader⟩ := hhas
  have hleaderTouched := touched_of_leader hleader
  refine ⟨leader, by simpa [AgentState.isLeader] using hleader, ?_⟩
  intro i hi
  have hi' : (D i).core.erase.core.leader = true := by
    change (eraseExpiringConfig D i).isLeader at hi
    change (eraseExpiringConfig D i).leader = true
    exact hi
  have hiTouched := touched_of_leader hi'
  rcases hleaderTouched with hleaderE | hleaderJ
  · subst leader
    rcases hiTouched with hiE | hiJ
    · exact hiE
    · exfalso
      apply hpair
      constructor
      · rw [← hDe]
        exact hleader
      · rw [← hDj]
        simpa [hiJ] using hi'
  · subst leader
    rcases hiTouched with hiE | hiJ
    · exfalso
      apply hpair
      constructor
      · rw [← hDe]
        simpa [hiE] using hi'
      · rw [← hDj]
        exact hleader
    · exact hiJ

/-- A decisive barrier/probe birth in a globally leaderless configuration
produces the unique first leader exactly at the responder, with the zero label
assigned by P-prime retained through the complete leader-sink interaction. -/
theorem localStepLeaderSink_barrier_probe_first_leader_unique_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hprobe : (C (ring.rightNeighbor e)).core.erase.core.probe = true)
    (hbarrier : isBarrier hpsi (C e).core.erase.core
      (C (ring.rightNeighbor e)).core.erase.core) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    hasUniqueLeader n (eraseExpiringConfig D) ∧
      ResponderZeroAnchor hpsi
        (D (ring.rightNeighbor e)).core.erase.core := by
  let j := ring.rightNeighbor e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hDj : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  have hzeroPair : ResponderZeroAnchor hpsi q.2.core.erase.core :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_barrier_probe_birth_zero
      hpsi (C e) (C j) hopen (hleaderless e) (hleaderless j)
        hprobe hbarrier
  have hzeroD : ResponderZeroAnchor hpsi (D j).core.erase.core := by
    rw [hDj]
    exact hzeroPair
  have hhas : RawHasLeader (eraseExpiringConfig D) :=
    ⟨j, hzeroD.1⟩
  exact ⟨localStepLeaderSink_first_physical_leader_unique
      hpsi ring hn C e hopen hleaderless hhas,
    by simpa [j] using hzeroD⟩

/-- Every priority-open first-leader step has one of two exact endpoint
shapes: either the scheduled initiator is the leader, or the leader remains at
the responder and is therefore at label zero. -/
theorem localStepLeaderSink_first_physical_leader_location
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hhas : RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          C e))) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    (D e).core.erase.core.leader = true ∨
      ResponderZeroAnchor hpsi
        (D (ring.rightNeighbor e)).core.erase.core := by
  let j := ring.rightNeighbor e
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hDj : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  change (D e).core.erase.core.leader = true ∨
    ResponderZeroAnchor hpsi (D j).core.erase.core
  change RawHasLeader (eraseExpiringConfig D) at hhas
  obtain ⟨i, hi⟩ := hhas
  change (D i).core.erase.core.leader = true at hi
  by_cases hie : i = e
  · subst i
    exact .inl hi
  by_cases hij : i = j
  · subst i
    right
    have hDjLeader : (D j).core.erase.core.leader = true := hi
    have hqLeader : q.2.core.erase.core.leader = true := by
      rw [← hDj]
      exact hDjLeader
    have hqZero :=
      wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_leader_zero
        hpsi (C e) (C j) hopen hqLeader
    rw [hDj]
    exact ⟨hqLeader, hqZero⟩
  · have hsame : D i = C i := by
      simp [D, T, localStep, j, hie, hij]
    have hCi : (C i).core.erase.core.leader = false := by
      change (eraseExpiringConfig C i).leader = false
      exact hleaderless i
    rw [hsame, hCi] at hi
    contradiction

/-- The first-leader location dichotomy with the initiator branch refined to
the exact CHECK-birth/WRITE-migration certificate.  The alternative remains
the independently proved label-zero responder P-prime birth. -/
theorem localStepLeaderSink_first_physical_leader_classified
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hhas : RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e))) :
    LocalStepInitiatorCheckMigration hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion (C e).core.erase)
        (normalizeDeletion (C (ring.rightNeighbor e)).core.erase))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion (C e).core.erase)
        (normalizeDeletion (C (ring.rightNeighbor e)).core.erase))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa
        (C e).core.erase (C (ring.rightNeighbor e)).core.erase)
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa
        (C e).core.erase (C (ring.rightNeighbor e)).core.erase)
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau
        (C e) (C (ring.rightNeighbor e)))
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e)
      e (ring.rightNeighbor e) ∨
    ResponderZeroAnchor hpsi
      ((localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e)
        (ring.rightNeighbor e)).core.erase.core := by
  have hlocation := localStepLeaderSink_first_physical_leader_location
    hpsi ring hn C e hopen hleaderless hhas
  rcases hlocation with hleft | hzero
  · exact .inl
      (localStepLeaderSink_first_physical_leader_initiator_check_migration
        hpsi ring hn C e hopen hleaderless hleft)
  · exact .inr hzero

/-- Configuration-level projection of the classified first-leader step.  In
the initiator branch the neighboring responder is a follower at label
`psi - 1`, and that label is the clockwise successor of the migrated leader's
label. -/
theorem localStepLeaderSink_first_physical_leader_location_strong
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hleaderless : RawLeaderless (eraseExpiringConfig C))
    (hhas : RawHasLeader
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e))) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    ((D e).core.erase.core.leader = true ∧
      (D (ring.rightNeighbor e)).core.erase.core.leader = false ∧
      (D (ring.rightNeighbor e)).core.erase.core.label =
        ⟨psi - 1, by omega⟩ ∧
      (D (ring.rightNeighbor e)).core.erase.core.label =
        ⟨((D e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩) ∨
      ResponderZeroAnchor hpsi
        (D (ring.rightNeighbor e)).core.erase.core := by
  have hclassified := localStepLeaderSink_first_physical_leader_classified
    hpsi ring hn C e hopen hleaderless hhas
  rcases hclassified with hinit | hzero
  · exact .inl ⟨hinit.initiatorLeader, hinit.responder.1,
      hinit.responder.2, hinit.aligned⟩
  · exact .inr hzero

/-- After the first leader appears, the canonical comparison-deletion drain
can be completed without changing the unique leader or either classified
endpoint shape.  Its endpoint has no active deletion, so every subsequent
edge is priority-open. -/
theorem
    exists_wallSweepPreCheckResetLeaderSink_firstLeader_deletionDrained
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (last : Fin n)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hlocation :
      ((C last).core.erase.core.leader = true ∧
        (C (ring.rightNeighbor last)).core.erase.core.leader = false ∧
        (C (ring.rightNeighbor last)).core.erase.core.label =
          ⟨psi - 1, by omega⟩ ∧
        (C (ring.rightNeighbor last)).core.erase.core.label =
          ⟨((C last).core.erase.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩) ∨
      ResponderZeroAnchor hpsi
        (C (ring.rightNeighbor last)).core.erase.core) :
    ∃ drain : DetSchedule n,
      drain.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → drain = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C drain
      NoActiveDeletion D ∧
      PeaceViewConfigFrame C D ∧
      PpsiControlConfigFrame C D ∧
      hasUniqueLeader n (eraseExpiringConfig D) ∧
      (((D last).core.erase.core.leader = true ∧
          (D (ring.rightNeighbor last)).core.erase.core.leader = false ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨psi - 1, by omega⟩ ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨((D last).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩) ∨
        ResponderZeroAnchor hpsi
          (D (ring.rightNeighbor last)).core.erase.core) ∧
      (∀ e, WallPriorityOpen (D e) (D (ring.rightNeighbor e))) := by
  obtain ⟨drain, hlength, hempty, hnoActive, hpeace, hcontrol⟩ :=
    exists_wallSweepPreCheckResetLeaderSinkDeletionDrain_ppsiControlFrame
      hpsi ring hn C
  let D := runLocalSchedule ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C drain
  change NoActiveDeletion D at hnoActive
  change PeaceViewConfigFrame C D at hpeace
  change PpsiControlConfigFrame C D at hcontrol
  have huniqueD : hasUniqueLeader n (eraseExpiringConfig D) :=
    hasUniqueLeader_of_peaceViewConfigFrame hpeace hunique
  have hlocationD :
      ((D last).core.erase.core.leader = true ∧
        (D (ring.rightNeighbor last)).core.erase.core.leader = false ∧
        (D (ring.rightNeighbor last)).core.erase.core.label =
          ⟨psi - 1, by omega⟩ ∧
        (D (ring.rightNeighbor last)).core.erase.core.label =
          ⟨((D last).core.erase.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩) ∨
      ResponderZeroAnchor hpsi
        (D (ring.rightNeighbor last)).core.erase.core := by
    have hleftLabel := congrArg PeaceView.label (hpeace last)
    have hrightLabel :=
      congrArg PeaceView.label (hpeace (ring.rightNeighbor last))
    change (D last).core.erase.core.label =
      (C last).core.erase.core.label at hleftLabel
    change (D (ring.rightNeighbor last)).core.erase.core.label =
      (C (ring.rightNeighbor last)).core.erase.core.label at hrightLabel
    rcases hlocation with hinit | hzero
    · exact .inl ⟨
        (congrArg PeaceView.leader (hpeace last)).trans hinit.1,
        (congrArg PeaceView.leader
          (hpeace (ring.rightNeighbor last))).trans hinit.2.1,
        hrightLabel.trans hinit.2.2.1,
        hrightLabel.trans (hinit.2.2.2.trans (by rw [hleftLabel]))⟩
    · exact .inr ⟨
        (congrArg PeaceView.leader
          (hpeace (ring.rightNeighbor last))).trans hzero.1,
        hrightLabel.trans hzero.2⟩
  refine ⟨drain, hlength, hempty, hnoActive, hpeace, hcontrol,
    huniqueD, hlocationD, ?_⟩
  intro e
  exact WallPriorityOpen.of_noActiveDeletion D hnoActive ring e

private theorem exists_stopped_unique_preCheckResetLeaderSink_simulation
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : Fin n → ExpiringAgentState psi kappa tau)
    (hrefine : PpsiControlConfigRefines raw physical)
    (hrawLeaderless : RawLeaderless raw)
    (hphysicalLeaderless : RawLeaderless (eraseExpiringConfig physical))
    (word : DetSchedule n)
    (hfinal : RawHasLeader
      (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) raw word)) :
    ∃ (actual : DetSchedule n) (last : Fin n),
      actual.length ≤ word.length * (n + 1) ∧
      hasUniqueLeader n
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau)
            physical actual)) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) physical actual
      (((D last).core.erase.core.leader = true ∧
          (D (ring.rightNeighbor last)).core.erase.core.leader = false ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨psi - 1, by omega⟩ ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨((D last).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩) ∨
          ResponderZeroAnchor hpsi
            (D (ring.rightNeighbor last)).core.erase.core) ∧
        bulletTwoCount D ≤ bulletTwoCount physical := by
  induction word generalizing raw physical with
  | nil =>
      simp only [runLocalSchedule] at hfinal
      obtain ⟨i, hi⟩ := hfinal
      rw [hrawLeaderless i] at hi
      contradiction
  | cons e rest ih =>
      obtain ⟨drain, hdrainLength, _hdrainEmpty, hnoActive,
        hpeace, hcontrol⟩ :=
        exists_wallSweepPreCheckResetLeaderSinkDeletionDrain_ppsiControlFrame
          hpsi ring hn physical
      let drained := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        physical drain
      change NoActiveDeletion drained at hnoActive
      change PeaceViewConfigFrame physical drained at hpeace
      change PpsiControlConfigFrame physical drained at hcontrol
      have hrefineDrained : PpsiControlConfigRefines raw drained :=
        hrefine.of_frame hcontrol
      have hphysicalDrainedLeaderless :
          RawLeaderless (eraseExpiringConfig drained) :=
        eraseExpiringConfig_leaderless_of_peaceFrame
          hphysicalLeaderless hpeace
      have hopen : WallPriorityOpen
          (drained e) (drained (ring.rightNeighbor e)) :=
        WallPriorityOpen.of_noActiveDeletion drained hnoActive ring e
      let raw1 := localStep ring (pPsiLeaderProbeWall hpsi) raw e
      let physical1 := localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        drained e
      have hphysical1Count :
          bulletTwoCount physical1 ≤ bulletTwoCount physical := by
        calc
          bulletTwoCount physical1 ≤ bulletTwoCount drained := by
            simpa [physical1] using
              (localStepLeaderSink_priority_open_left_follower_bulletTwoCount_le
                hpsi kappa tau ring hn drained e hopen
                  (hphysicalDrainedLeaderless e))
          _ = bulletTwoCount physical :=
            bulletTwoCount_eq_of_peaceViewConfigFrame hpeace
      by_cases hbirth :
          (raw (ring.rightNeighbor e)).probe = true ∧
            isBarrier hpsi (raw e) (raw (ring.rightNeighbor e))
      · have hphysicalBirth : RawHasLeader
            (eraseExpiringConfig physical1) := by
          exact raw_birth_edge_creates_physical_leaderSink
            hpsi kappa tau ring hn raw drained e hrefineDrained
              hphysicalDrainedLeaderless hopen hbirth.1 hbirth.2
        have hphysicalUnique : hasUniqueLeader n
            (eraseExpiringConfig physical1) :=
          localStepLeaderSink_first_physical_leader_unique
            hpsi ring hn drained e hopen hphysicalDrainedLeaderless
              hphysicalBirth
        have hphysicalLocation :=
          localStepLeaderSink_first_physical_leader_location_strong
            hpsi ring hn drained e hopen hphysicalDrainedLeaderless
              hphysicalBirth
        refine ⟨drain ++ [e], e, ?_, ?_, ?_⟩
        · have hcount := comparisonPathCount_le physical
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.zero_add, Nat.succ_mul]
          omega
        · rw [runLocalSchedule_append_expiring]
          simpa [physical1, drained, runLocalSchedule] using hphysicalUnique
        · rw [runLocalSchedule_append_expiring]
          refine ⟨?_, ?_⟩
          · simpa [physical1, drained, runLocalSchedule] using hphysicalLocation
          · simpa [physical1, drained, runLocalSchedule] using hphysical1Count
      · have hraw1Leaderless : RawLeaderless raw1 :=
          rawLeaderless_localStep_pPsiLeaderProbeWall_of_not_birth
            hpsi ring hn raw e hrawLeaderless hbirth
        have hrefine1 : PpsiControlConfigRefines raw1 physical1 :=
          ppsiControlRefines_localStepLeaderSink_of_priority_open
            hpsi kappa tau ring hn raw drained e hrefineDrained
              hrawLeaderless hphysicalDrainedLeaderless hopen
        by_cases hphysical1 : RawHasLeader (eraseExpiringConfig physical1)
        · have hphysicalUnique : hasUniqueLeader n
              (eraseExpiringConfig physical1) :=
            localStepLeaderSink_first_physical_leader_unique
              hpsi ring hn drained e hopen hphysicalDrainedLeaderless
                hphysical1
          have hphysicalLocation :=
            localStepLeaderSink_first_physical_leader_location_strong
              hpsi ring hn drained e hopen hphysicalDrainedLeaderless
                hphysical1
          refine ⟨drain ++ [e], e, ?_, ?_, ?_⟩
          · have hcount := comparisonPathCount_le physical
            simp only [List.length_append, List.length_cons, List.length_nil,
              Nat.zero_add, Nat.succ_mul]
            omega
          · rw [runLocalSchedule_append_expiring]
            simpa [physical1, drained, runLocalSchedule] using hphysicalUnique
          · rw [runLocalSchedule_append_expiring]
            refine ⟨?_, ?_⟩
            · simpa [physical1, drained, runLocalSchedule] using hphysicalLocation
            · simpa [physical1, drained, runLocalSchedule] using hphysical1Count
        · have hphysical1Leaderless :
              RawLeaderless (eraseExpiringConfig physical1) :=
            RawLeaderless.of_not_hasLeader hphysical1
          have hfinal1 : RawHasLeader
              (runLocalSchedule ring (pPsiLeaderProbeWall hpsi)
                raw1 rest) := by
            simpa [raw1, runLocalSchedule] using hfinal
          obtain ⟨tail, last, htailLength, htailUnique,
              htailLocation, htailCount⟩ :=
            ih raw1 physical1 hrefine1
              hraw1Leaderless hphysical1Leaderless hfinal1
          refine ⟨drain ++ (e :: tail), last, ?_, ?_, ?_⟩
          · have hcount := comparisonPathCount_le physical
            simp only [List.length_append, List.length_cons, Nat.succ_mul]
            omega
          · rw [runLocalSchedule_append_expiring]
            simpa [physical1, drained, runLocalSchedule] using htailUnique
          · rw [runLocalSchedule_append_expiring]
            refine ⟨?_, ?_⟩
            · simpa [physical1, drained, runLocalSchedule] using htailLocation
            · simpa [physical1, drained, runLocalSchedule] using
                Nat.le_trans htailCount hphysical1Count

/-- On a nondivisible ring, the stopped first-leader simulation gives both a
unique physical leader and its exact last-edge shape: either the initiator is
the CHECK-migrated leader with an aligned `psi - 1` follower to its right, or
the responder is a zero-labelled P-prime leader anchor. -/
theorem exists_preCheckResetLeaderSink_firstLeader_location_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (last : Fin n),
      actual.length ≤ (2 * n + 1) * (n + 1) ∧
      hasUniqueLeader n
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau)
            C actual)) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual
      (((D last).core.erase.core.leader = true ∧
          (D (ring.rightNeighbor last)).core.erase.core.leader = false ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨psi - 1, by omega⟩ ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨((D last).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩) ∨
          ResponderZeroAnchor hpsi
            (D (ring.rightNeighbor last)).core.erase.core) ∧
        bulletTwoCount D ≤ bulletTwoCount C := by
  obtain ⟨word, hwordLength, hrawFinal⟩ :=
    exists_pPsiLeaderProbeWall_hasLeader_of_not_dvd
      hpsi ring hn hndvd (eraseExpiringConfig C)
  obtain ⟨actual, last, hactualLength, hactualUnique,
      hactualLocation, hactualCount⟩ :=
    exists_stopped_unique_preCheckResetLeaderSink_simulation
      hpsi ring hn (eraseExpiringConfig C) C (fun _ => rfl)
        hleaderless hleaderless word hrawFinal
  refine ⟨actual, last, ?_, hactualUnique,
    hactualLocation, hactualCount⟩
  exact Nat.le_trans hactualLength
    (Nat.mul_le_mul_right (n + 1) hwordLength)

/-- The nondivisible first-leader schedule can be extended by at most one
canonical deletion drain.  The resulting classified unique-leader endpoint
has no active deletion, hence every edge is ready for the ordinary
priority-open analysis. -/
theorem
    exists_preCheckResetLeaderSink_firstLeader_drained_location_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (last : Fin n),
      actual.length ≤ (2 * n + 1) * (n + 1) + n ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual
      NoActiveDeletion D ∧
      hasUniqueLeader n (eraseExpiringConfig D) ∧
      (((D last).core.erase.core.leader = true ∧
          (D (ring.rightNeighbor last)).core.erase.core.leader = false ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨psi - 1, by omega⟩ ∧
          (D (ring.rightNeighbor last)).core.erase.core.label =
            ⟨((D last).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩) ∨
        ResponderZeroAnchor hpsi
          (D (ring.rightNeighbor last)).core.erase.core) ∧
      (∀ e, WallPriorityOpen (D e) (D (ring.rightNeighbor e))) ∧
      bulletTwoCount D ≤ bulletTwoCount C := by
  obtain ⟨birth, last, hbirthLength, hbirthUnique,
      hbirthLocation, hbirthCount⟩ :=
    exists_preCheckResetLeaderSink_firstLeader_location_of_not_dvd
      hpsi ring hn hndvd C hleaderless
  let C1 := runLocalSchedule ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C birth
  obtain ⟨drain, hdrainLength, _hdrainEmpty, hnoActive,
      hpeace, _hcontrol, hfinalUnique, hfinalLocation, hopen⟩ :=
    exists_wallSweepPreCheckResetLeaderSink_firstLeader_deletionDrained
      hpsi ring hn C1 last hbirthUnique hbirthLocation
  have hfinalCount :
      bulletTwoCount
          (runLocalSchedule ring
            (wallSweepPreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau) C1 drain) =
        bulletTwoCount C1 :=
    bulletTwoCount_eq_of_peaceViewConfigFrame hpeace
  refine ⟨birth ++ drain, last, ?_, ?_⟩
  · have hcount := comparisonPathCount_le C1
    simp only [List.length_append]
    omega
  · rw [runLocalSchedule_append_expiring]
    exact ⟨hnoActive, hfinalUnique, hfinalLocation, hopen,
      Nat.le_trans (Nat.le_of_eq hfinalCount) hbirthCount⟩

/-- Forgetting the exact last-edge classification exposes the regeneration
boundary used by live-bullet retry: a bounded schedule from any leaderless
nondivisible input reaches a deletion-free unique leader without increasing
the global live-bullet rank. -/
theorem
    exists_preCheckResetLeaderSink_drainedUniqueLeader_bulletTwo_le_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (leader : Fin n),
      actual.length ≤ (2 * n + 1) * (n + 1) + n ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual
      NoActiveDeletion D ∧
      hasUniqueLeader n (eraseExpiringConfig D) ∧
      (D leader).core.erase.core.leader = true ∧
      (∀ e, WallPriorityOpen (D e) (D (ring.rightNeighbor e))) ∧
      bulletTwoCount D ≤ bulletTwoCount C := by
  obtain ⟨actual, last, hlength, hnoActive, hunique,
      hlocation, hopen, hcount⟩ :=
    exists_preCheckResetLeaderSink_firstLeader_drained_location_of_not_dvd
      hpsi ring hn hndvd C hleaderless
  let D := runLocalSchedule ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C actual
  rcases hlocation with hinitiator | hresponder
  · exact ⟨actual, last, hlength, hnoActive, hunique,
      hinitiator.1, hopen, hcount⟩
  · exact ⟨actual, ring.rightNeighbor last, hlength,
      hnoActive, hunique, hresponder.1, hopen, hcount⟩

/-- One complete live-bullet retry cycle.  A deletion-free unique leader
either survives its outgoing edge, or that edge kills it and a bounded
nondivisible regeneration reaches another deletion-free unique leader at a
strictly smaller global live-bullet rank. -/
theorem exists_preCheckResetLeaderSink_retryStep_bulletTwo
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader : Fin n)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hnoActive : NoActiveDeletion C) :
    let C1 := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    (hasUniqueLeader n (eraseExpiringConfig C1) ∧
        (C1 leader).core.erase.core.leader = true) ∨
      ∃ (retry : DetSchedule n) (leader' : Fin n),
        retry.length ≤ (2 * n + 1) * (n + 1) + n ∧
        let D := runLocalSchedule ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C1 retry
        NoActiveDeletion D ∧
        hasUniqueLeader n (eraseExpiringConfig D) ∧
        (D leader').core.erase.core.leader = true ∧
        (∀ e, WallPriorityOpen (D e) (D (ring.rightNeighbor e))) ∧
        bulletTwoCount D < bulletTwoCount C := by
  let j := ring.rightNeighbor leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have hstep :=
    localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
      hpsi kappa tau ring hn C leader hunique hleader
        (by simpa [j] using hopen)
  let C1 := localStep ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C leader
  change
    (hasUniqueLeader n (eraseExpiringConfig C1) ∧
        (C1 leader).core.erase.core.leader = true) ∨
      (RawLeaderless (eraseExpiringConfig C1) ∧
        bulletTwoCount C1 < bulletTwoCount C) at hstep
  rcases hstep with hsurvives | ⟨hleaderless, hdrop⟩
  · exact .inl hsurvives
  · obtain ⟨retry, leader', hlength, hnoActiveD, huniqueD,
        hleaderD, hopenD, hcountD⟩ :=
      exists_preCheckResetLeaderSink_drainedUniqueLeader_bulletTwo_le_of_not_dvd
        hpsi ring hn hndvd C1 hleaderless
    exact .inr ⟨retry, leader', hlength, hnoActiveD, huniqueD,
      hleaderD, hopenD, Nat.lt_of_le_of_lt hcountD hdrop⟩

/-- Terminal certificate for the live-bullet retry alone.  It records a
deletion-free unique leader whose designated outgoing interaction again has a
unique leader at the same initiator.  It deliberately does not assert a
shield, label-zero root, or global cleanup fields. -/
def DrainedOutgoingLeaderSurvivor
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∃ leader : Fin n,
    NoActiveDeletion C ∧
    hasUniqueLeader n (eraseExpiringConfig C) ∧
    (C leader).core.erase.core.leader = true ∧
    hasUniqueLeader n
      (eraseExpiringConfig
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C leader)) ∧
    (localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader leader).core.erase.core.leader = true

private theorem
    exists_preCheckResetLeaderSink_outgoingSurvivor_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n) (rank : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader : Fin n)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hnoActive : NoActiveDeletion C)
    (hrank : bulletTwoCount C ≤ rank) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      actual.length ≤ rank *
        ((2 * n + 1) * (n + 1) + n + 1) ∧
      DrainedOutgoingLeaderSurvivor hpsi ring D := by
  induction rank generalizing C leader with
  | zero =>
      have hcycle := exists_preCheckResetLeaderSink_retryStep_bulletTwo
        hpsi ring hn hndvd C leader hunique hleader hnoActive
      let C1 := localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C leader
      change
        (hasUniqueLeader n (eraseExpiringConfig C1) ∧
            (C1 leader).core.erase.core.leader = true) ∨
          ∃ (retry : DetSchedule n) (leader' : Fin n),
            retry.length ≤ (2 * n + 1) * (n + 1) + n ∧
            let D := runLocalSchedule ring
              (wallSweepPreCheckResetLeaderSinkPathStallTransition
                hpsi kappa tau) C1 retry
            NoActiveDeletion D ∧
            hasUniqueLeader n (eraseExpiringConfig D) ∧
            (D leader').core.erase.core.leader = true ∧
            (∀ e, WallPriorityOpen (D e) (D (ring.rightNeighbor e))) ∧
            bulletTwoCount D < bulletTwoCount C at hcycle
      rcases hcycle with hsurvives | hretry
      · refine ⟨[], C, by simp [runLocalSchedule], by simp, ?_⟩
        exact ⟨leader, hnoActive, hunique, hleader,
          hsurvives.1, hsurvives.2⟩
      · obtain ⟨retry, leader', hlength, hnoActiveD, huniqueD,
            hleaderD, hopenD, hdrop⟩ := hretry
        have hbad : False := by omega
        exact False.elim hbad
  | succ rank ih =>
      have hcycle := exists_preCheckResetLeaderSink_retryStep_bulletTwo
        hpsi ring hn hndvd C leader hunique hleader hnoActive
      let C1 := localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C leader
      change
        (hasUniqueLeader n (eraseExpiringConfig C1) ∧
            (C1 leader).core.erase.core.leader = true) ∨
          ∃ (retry : DetSchedule n) (leader' : Fin n),
            retry.length ≤ (2 * n + 1) * (n + 1) + n ∧
            let D := runLocalSchedule ring
              (wallSweepPreCheckResetLeaderSinkPathStallTransition
                hpsi kappa tau) C1 retry
            NoActiveDeletion D ∧
            hasUniqueLeader n (eraseExpiringConfig D) ∧
            (D leader').core.erase.core.leader = true ∧
            (∀ e, WallPriorityOpen (D e) (D (ring.rightNeighbor e))) ∧
            bulletTwoCount D < bulletTwoCount C at hcycle
      rcases hcycle with hsurvives | hretry
      · refine ⟨[], C, by simp [runLocalSchedule], by simp, ?_⟩
        exact ⟨leader, hnoActive, hunique, hleader,
          hsurvives.1, hsurvives.2⟩
      · obtain ⟨retry, leader', hretryLength, hnoActiveD,
            huniqueD, hleaderD, _hopenD, hdrop⟩ := hretry
        let D := runLocalSchedule ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C1 retry
        change NoActiveDeletion D at hnoActiveD
        change hasUniqueLeader n (eraseExpiringConfig D) at huniqueD
        change (D leader').core.erase.core.leader = true at hleaderD
        change bulletTwoCount D < bulletTwoCount C at hdrop
        have hDrank : bulletTwoCount D ≤ rank := by omega
        obtain ⟨tail, E, hE, htailLength, hterminal⟩ :=
          ih D leader' huniqueD hleaderD hnoActiveD hDrank
        let actual := [leader] ++ retry ++ tail
        refine ⟨actual, E, ?_, ?_, hterminal⟩
        · let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
          calc
            E = runLocalSchedule ring T D tail := hE
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C1 retry) tail := by rfl
            _ = runLocalSchedule ring T C1 (retry ++ tail) :=
              (runLocalSchedule_append_expiring
                ring T C1 retry tail).symm
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C [leader])
                (retry ++ tail) := by rfl
            _ = runLocalSchedule ring T C
                ([leader] ++ (retry ++ tail)) :=
              (runLocalSchedule_append_expiring
                ring T C [leader] (retry ++ tail)).symm
            _ = runLocalSchedule ring T C actual := by
              simp [actual, List.append_assoc]
        · unfold actual
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [Nat.succ_mul]
          omega

/-- The global live-bullet rank makes repeated first-leader regeneration
well founded.  Starting from any deletion-free unique leader on a
nondivisible ring, a concrete bounded schedule reaches a deletion-free unique
leader whose designated outgoing edge no longer kills it or creates a second
leader. -/
theorem exists_preCheckResetLeaderSink_outgoingSurvivor_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader : Fin n)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hnoActive : NoActiveDeletion C) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      actual.length ≤ bulletTwoCount C *
        ((2 * n + 1) * (n + 1) + n + 1) ∧
      DrainedOutgoingLeaderSurvivor hpsi ring D := by
  exact exists_preCheckResetLeaderSink_outgoingSurvivor_of_rank
    hpsi ring hn hndvd (bulletTwoCount C) C leader
      hunique hleader hnoActive (Nat.le_refl _)

/-- Combining bounded first-leader regeneration with the live-bullet retry
rank reaches an outgoing survivor from every physically leaderless
nondivisible input.  The bound keeps the actual input rank visible: one
initial regeneration, followed by at most one failed retry per live bullet. -/
theorem
    exists_preCheckResetLeaderSink_outgoingSurvivor_from_leaderless_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      actual.length ≤
        ((2 * n + 1) * (n + 1) + n) +
          bulletTwoCount C *
            ((2 * n + 1) * (n + 1) + n + 1) ∧
      DrainedOutgoingLeaderSurvivor hpsi ring D := by
  obtain ⟨initial, leader, hinitialLength, hnoActiveD,
      huniqueD, hleaderD, _hopenD, hcountD⟩ :=
    exists_preCheckResetLeaderSink_drainedUniqueLeader_bulletTwo_le_of_not_dvd
      hpsi ring hn hndvd C hleaderless
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := runLocalSchedule ring T C initial
  change NoActiveDeletion D at hnoActiveD
  change hasUniqueLeader n (eraseExpiringConfig D) at huniqueD
  change (D leader).core.erase.core.leader = true at hleaderD
  change bulletTwoCount D ≤ bulletTwoCount C at hcountD
  obtain ⟨tail, E, hE, htailLength, hterminal⟩ :=
    exists_preCheckResetLeaderSink_outgoingSurvivor_of_not_dvd
      hpsi ring hn hndvd D leader huniqueD hleaderD hnoActiveD
  let actual := initial ++ tail
  refine ⟨actual, E, ?_, ?_, hterminal⟩
  · calc
      E = runLocalSchedule ring T D tail := hE
      _ = runLocalSchedule ring T C (initial ++ tail) :=
        (runLocalSchedule_append_expiring ring T C initial tail).symm
      _ = runLocalSchedule ring T C actual := by rfl
  · have hmul := Nat.mul_le_mul_right
        ((2 * n + 1) * (n + 1) + n + 1) hcountD
    unfold actual
    simp only [List.length_append]
    omega

/-- The rank-sensitive bound has the uniform cubic form
`2 * (n + 1)^3 - 1`, since a configuration has at most `n` live bullets. -/
theorem
    exists_preCheckResetLeaderSink_outgoingSurvivor_from_leaderless_uniform
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      actual.length ≤ 2 * (n + 1) ^ 3 - 1 ∧
      DrainedOutgoingLeaderSurvivor hpsi ring D := by
  obtain ⟨actual, D, hD, hlength, hterminal⟩ :=
    exists_preCheckResetLeaderSink_outgoingSurvivor_from_leaderless_of_not_dvd
      hpsi ring hn hndvd C hleaderless
  have hmul := Nat.mul_le_mul_right
    ((2 * n + 1) * (n + 1) + n + 1) (bulletTwoCount_le C)
  have hpoly :
      ((2 * n + 1) * (n + 1) + n) +
          n * ((2 * n + 1) * (n + 1) + n + 1) + 1 =
        2 * (n + 1) ^ 3 := by
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
      Nat.two_mul]
    <;> omega
  refine ⟨actual, D, hD, ?_, hterminal⟩
  omega

/-- A neutral expiring carrier is outside deletion priority. -/
private theorem deletionActive_false_of_comparisonNeutral
    (u : ExpiringAgentState psi kappa tau)
    (h : ComparisonNeutral u.core.erase.core) :
    deletionActive u.core.erase = false := by
  simp [deletionActive, pathPresent, h.1, h.2.1]

/-- The normalized outgoing endpoint with its surviving leader named
explicitly.  This form is needed when a later schedule must replay that exact
leader edge rather than forget it behind an existential witness. -/
def NormalizedOutgoingUniqueLeaderAt
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader : Fin n) : Prop :=
  NoActiveDeletion C ∧
    hasUniqueLeader n (eraseExpiringConfig C) ∧
    (C leader).core.erase.core.leader = true ∧
    (C (ring.rightNeighbor leader)).core.erase.core.leader = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.label =
      ⟨((C leader).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ ∧
    (C leader).core.erase.core.probe = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.probe = false ∧
    ComparisonNeutral (C leader).core.erase.core ∧
    ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core ∧
    (C leader).core.erase.core.reset_cmd = false ∧
    (C leader).core.erase.core.echo = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.echo = false ∧
    ((C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩ →
      (C leader).core.erase.core.shield = true)

/-- Concrete endpoint after executing the certified surviving edge.  The
leader is still unique, deletion priority is globally inactive, and its right
edge is normalized in both the P-prime and comparison/reset/echo projections.
No global rooted geometry or remote carrier cleanup is included. -/
def NormalizedOutgoingUniqueLeader
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∃ leader : Fin n,
    NormalizedOutgoingUniqueLeaderAt hpsi ring C leader

/-- A priority-open leader-to-follower interaction which actually retains its
initiating leader produces the exact normalized outgoing endpoint used by the
replay theorem.  This survivor-facing form also covers the fire branch and a
live responder already protected by the input shield. -/
theorem leaderStep_survivor_to_normalizedOutgoingUniqueLeaderAt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrFollower :
      (C (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (houtLeader :
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C leader leader).core.erase.core.leader = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    NormalizedOutgoingUniqueLeaderAt hpsi ring D leader := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C leader
  change (D leader).core.erase.core.leader = true at houtLeader
  have hstep :=
    localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
      hpsi kappa tau ring hn C leader hunique hleader
        (by simpa [j] using hopen)
  change
    (hasUniqueLeader n (eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true) ∨
      (RawLeaderless (eraseExpiringConfig D) ∧
        bulletTwoCount D < bulletTwoCount C) at hstep
  have huniqueD : hasUniqueLeader n (eraseExpiringConfig D) := by
    rcases hstep with hgood | hbad
    · exact hgood.1
    · have hfalse := hbad.1 leader
      change (D leader).core.erase.core.leader = false at hfalse
      rw [houtLeader] at hfalse
      contradiction
  have hrightFollower : (D j).core.erase.core.leader = false := by
    simpa [D, T, j, localStep, hje] using
      (wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
        hpsi (C leader) (C j) hopen hleader
          (by simpa [j] using hrFollower))
  have hcontrolsPair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_leader_controls
      hpsi kappa tau (C leader) (C j) hopen hleader
        (by simpa [j] using hrFollower)
  have hcontrols :
      (D leader).core.erase.core.label =
          (C leader).core.erase.core.label ∧
        (D j).core.erase.core.label =
          ⟨((C leader).core.erase.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ ∧
        (D leader).core.erase.core.probe = false ∧
        (D j).core.erase.core.probe = false := by
    simpa [D, T, j, localStep, hje] using hcontrolsPair
  have hcleanupPair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_leader_source_cleanup
      hpsi (C leader) (C j) hopen hleader
  have hcleanup : ExpiringLeaderSourceCleanup
      ((C leader), (C j)) ((D leader), (D j)) := by
    simpa [D, T, j, localStep, hje] using hcleanupPair
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hiLeader : i = leader
    · subst i
      exact deletionActive_false_of_comparisonNeutral
        (D leader) hcleanup.1
    · by_cases hiRight : i = j
      · subst i
        exact deletionActive_false_of_comparisonNeutral
          (D j) hcleanup.2.1
      · have hsame : D i = C i := by
          simp [D, T, localStep, j, hiLeader, hiRight]
        rw [hsame]
        exact hnoActive i
  have hrightLabel :
      (D j).core.erase.core.label =
        ⟨((D leader).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
    rw [hcontrols.1]
    exact hcontrols.2.1
  have hpairLeader :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (C leader) (C j)).1.core.erase.core.leader = true := by
    simpa [D, T, j, localStep] using houtLeader
  have hsafePair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_safe
      hpsi (C leader) (C j) hopen hleader
        (by simpa [j] using hrFollower) hpairLeader
  have hsafeD :
      (D j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (D leader).core.erase.core.shield = true := by
    simpa [D, T, j, localStep, hje] using hsafePair
  change NormalizedOutgoingUniqueLeaderAt hpsi ring D leader
  refine ⟨hnoActiveD, huniqueD, houtLeader,
    ?_, ?_, hcontrols.2.2.1, hcontrols.2.2.2,
    hcleanup.1, hcleanup.2.1, hcleanup.2.2.1,
    hcleanup.2.2.2.2.1, hcleanup.2.2.2.2.2, ?_⟩
  · simpa [j] using hrightFollower
  · simpa [j] using hrightLabel
  · simpa [j] using hsafeD

/-- One priority-open leader-to-follower interaction from a collision-safe
edge produces the exact normalized outgoing endpoint used by the replay
theorem.  No input label alignment is needed: the source step installs the
successor label itself.  This is the local interface hidden inside the earlier
leaderless-to-first-leader schedule. -/
theorem leaderStep_to_normalizedOutgoingUniqueLeaderAt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrFollower :
      (C (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hsafe :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C leader).core.erase.core.shield = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    NormalizedOutgoingUniqueLeaderAt hpsi ring D leader := by
  let j := ring.rightNeighbor leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have hpairSurvives :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_survives_of_safe
      hpsi (C leader) (C j) hopen hleader
        (by simpa [j] using hrFollower) (by simpa [j] using hsafe)
  have houtLeader :
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C leader leader).core.erase.core.leader = true := by
    simpa [j, localStep] using hpairSurvives
  exact leaderStep_survivor_to_normalizedOutgoingUniqueLeaderAt
    hpsi ring hn C leader hnoActive hunique hleader hrFollower houtLeader

/-- Existential projection of the named-leader normalization interface. -/
theorem leaderStep_to_normalizedOutgoingUniqueLeader
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrFollower :
      (C (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hsafe :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C leader).core.erase.core.shield = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    NormalizedOutgoingUniqueLeader hpsi ring D := by
  exact ⟨leader,
    leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn C leader hnoActive hunique hleader hrFollower hsafe⟩

/-- Executing the terminal surviving edge adds one interaction to the cubic
bound and yields a unique leader with a normalized outgoing label/probe edge. -/
theorem
    exists_preCheckResetLeaderSink_normalizedOutgoing_from_leaderless_uniform
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      actual.length ≤ 2 * (n + 1) ^ 3 ∧
      NormalizedOutgoingUniqueLeader hpsi ring D := by
  obtain ⟨initial, A, hA, hinitialLength, hterminal⟩ :=
    exists_preCheckResetLeaderSink_outgoingSurvivor_from_leaderless_uniform
      hpsi ring hn hndvd C hleaderless
  obtain ⟨leader, hnoActive, hunique, hleader,
      houtUnique, houtLeader⟩ := hterminal
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hjFollower : (A j).core.erase.core.leader = false := by
    obtain ⟨only, _honlyLeader, honly⟩ := hunique
    cases hj : (A j).core.erase.core.leader with
    | false => rfl
    | true =>
        have hjOnly : j = only := by
          apply honly j
          change (A j).core.erase.core.isLeader
          change (A j).core.erase.core.leader = true
          exact hj
        have hleaderOnly : leader = only := by
          apply honly leader
          change (A leader).core.erase.core.isLeader
          change (A leader).core.erase.core.leader = true
          exact hleader
        exact False.elim (hje (hjOnly.trans hleaderOnly.symm))
  have hopen : WallPriorityOpen (A leader) (A j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion A hnoActive ring leader
  have hcontrols :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_leader_controls
      hpsi kappa tau (A leader) (A j) hopen hleader hjFollower
  have hcleanupPair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_leader_source_cleanup
      hpsi (A leader) (A j) hopen hleader
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T A leader
  change hasUniqueLeader n (eraseExpiringConfig D) at houtUnique
  change (D leader).core.erase.core.leader = true at houtLeader
  have hrightFollower : (D j).core.erase.core.leader = false := by
    simpa [D, T, j, localStep, hje] using
      (wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
        hpsi (A leader) (A j) hopen hleader hjFollower)
  have hnormalized :
      (D leader).core.erase.core.label =
          (A leader).core.erase.core.label ∧
        (D j).core.erase.core.label =
          ⟨((A leader).core.erase.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ ∧
        (D leader).core.erase.core.probe = false ∧
        (D j).core.erase.core.probe = false := by
    simpa [D, T, j, localStep, hje] using hcontrols
  have hcleanup : ExpiringLeaderSourceCleanup
      ((A leader), (A j)) ((D leader), (D j)) := by
    simpa [D, T, j, localStep, hje] using hcleanupPair
  have hpairLeader :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (A leader) (A j)).1.core.erase.core.leader = true := by
    simpa [D, T, j, localStep] using houtLeader
  have hsafePair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_safe
      hpsi (A leader) (A j) hopen hleader hjFollower hpairLeader
  have hsafe :
      (D j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (D leader).core.erase.core.shield = true := by
    simpa [D, T, j, localStep, hje] using hsafePair
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hiLeader : i = leader
    · subst i
      exact deletionActive_false_of_comparisonNeutral
        (D leader) hcleanup.1
    · by_cases hiRight : i = j
      · subst i
        exact deletionActive_false_of_comparisonNeutral
          (D j) hcleanup.2.1
      · have hsame : D i = A i := by
          simp [D, T, localStep, j, hiLeader, hiRight]
        rw [hsame]
        exact hnoActive i
  have hrightLabel :
      (D j).core.erase.core.label =
        ⟨((D leader).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
    rw [hnormalized.1]
    exact hnormalized.2.1
  let actual := initial ++ [leader]
  refine ⟨actual, D, ?_, ?_, ?_⟩
  · calc
      D = runLocalSchedule ring T A [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C initial) [leader] := by rw [← hA]
      _ = runLocalSchedule ring T C (initial ++ [leader]) :=
        (runLocalSchedule_append_expiring
          ring T C initial [leader]).symm
      _ = runLocalSchedule ring T C actual := by rfl
  · unfold actual
    simp only [List.length_append, List.length_cons, List.length_nil]
    have hpow : 0 < (n + 1) ^ 3 := Nat.pow_pos (by omega)
    have hpositive : 0 < 2 * (n + 1) ^ 3 :=
      Nat.mul_pos (by omega) hpow
    omega
  · exact ⟨leader, hnoActiveD, houtUnique, houtLeader,
      hrightFollower, hrightLabel,
      hnormalized.2.2.1, hnormalized.2.2.2,
      hcleanup.1, hcleanup.2.1, hcleanup.2.2.1,
      hcleanup.2.2.2.2.1, hcleanup.2.2.2.2.2, hsafe⟩

/-- The named unique leader whose normalized outgoing edge has been replayed
once.  Keeping the physical leader explicit is essential when a caller must
restart the sweep at that same edge. -/
def OutgoingResetFrontierUniqueLeaderAt
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (leader : Fin n) : Prop :=
  NoActiveDeletion C ∧
    hasUniqueLeader n (eraseExpiringConfig C) ∧
    (C leader).core.erase.core.leader = true ∧
    (C (ring.rightNeighbor leader)).core.erase.core.leader = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.label =
      ⟨((C leader).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ ∧
    (C leader).core.erase.core.probe = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.probe = false ∧
    ComparisonNeutral (C leader).core.erase.core ∧
    ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core ∧
    (C leader).core.erase.core.reset_cmd = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true ∧
    (C leader).core.erase.core.echo = false ∧
    (C (ring.rightNeighbor leader)).core.erase.core.echo = false ∧
    ((C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩ →
      (C leader).core.erase.core.shield = true)

/-- Existential projection of the named reset-frontier interface. -/
def OutgoingResetFrontierUniqueLeader
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∃ leader : Fin n,
    OutgoingResetFrontierUniqueLeaderAt hpsi ring C leader

/-- Replaying a normalized surviving edge at its named leader is safe and
forces the reset handoff, because the first execution already cleared the
responder echo and established the exact bullet/shield collision condition. -/
theorem normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (leader : Fin n)
    (hnormal : NormalizedOutgoingUniqueLeaderAt hpsi ring C leader) :
    OutgoingResetFrontierUniqueLeaderAt hpsi ring
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C leader) leader := by
  obtain ⟨hnoActive, hunique, hleader, hjFollower,
      _haligned, _hleftProbe, _hrightProbe, _hleftNeutral,
      _hrightNeutral, _hleftReset, _hleftEcho, hjEcho, hsafe⟩ := hnormal
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C leader
  have hpairSurvives :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_survives_of_safe
      hpsi (C leader) (C j) hopen hleader
        (by simpa [j] using hjFollower) (by simpa [j] using hsafe)
  have houtLeader : (D leader).core.erase.core.leader = true := by
    simpa [D, T, j, localStep] using hpairSurvives
  have hstep :=
    localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
      hpsi kappa tau ring hn C leader hunique hleader
        (by simpa [j] using hopen)
  change
    (hasUniqueLeader n (eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true) ∨
      (RawLeaderless (eraseExpiringConfig D) ∧
        bulletTwoCount D < bulletTwoCount C) at hstep
  have huniqueD : hasUniqueLeader n (eraseExpiringConfig D) := by
    rcases hstep with hgood | hbad
    · exact hgood.1
    · have hfalse := hbad.1 leader
      change (D leader).core.erase.core.leader = false at hfalse
      rw [houtLeader] at hfalse
      contradiction
  have hjFollowerD : (D j).core.erase.core.leader = false := by
    simpa [D, T, j, localStep, hje] using
      (wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
        hpsi (C leader) (C j) hopen hleader
          (by simpa [j] using hjFollower))
  have hcontrolsPair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_leader_controls
      hpsi kappa tau (C leader) (C j) hopen hleader
        (by simpa [j] using hjFollower)
  have hcontrols :
      (D leader).core.erase.core.label =
          (C leader).core.erase.core.label ∧
        (D j).core.erase.core.label =
          ⟨((C leader).core.erase.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ ∧
        (D leader).core.erase.core.probe = false ∧
        (D j).core.erase.core.probe = false := by
    simpa [D, T, j, localStep, hje] using hcontrolsPair
  have hcleanupPair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_leader_source_cleanup
      hpsi (C leader) (C j) hopen hleader
  have hcleanup : ExpiringLeaderSourceCleanup
      ((C leader), (C j)) ((D leader), (D j)) := by
    simpa [D, T, j, localStep, hje] using hcleanupPair
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hiLeader : i = leader
    · subst i
      exact deletionActive_false_of_comparisonNeutral
        (D leader) hcleanup.1
    · by_cases hiRight : i = j
      · subst i
        exact deletionActive_false_of_comparisonNeutral
          (D j) hcleanup.2.1
      · have hsame : D i = C i := by
          simp [D, T, localStep, j, hiLeader, hiRight]
        rw [hsame]
        exact hnoActive i
  have hrightLabel :
      (D j).core.erase.core.label =
        ⟨((D leader).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
    rw [hcontrols.1]
    exact hcontrols.2.1
  have hrightReset : (D j).core.erase.core.reset_cmd = true := by
    rw [hcleanup.2.2.2.1, hjEcho]
    rfl
  have hpairLeader :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (C leader) (C j)).1.core.erase.core.leader = true := by
    simpa [D, T, j, localStep] using houtLeader
  have hsafePair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_safe
      hpsi (C leader) (C j) hopen hleader
        (by simpa [j] using hjFollower) hpairLeader
  have hsafeD :
      (D j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (D leader).core.erase.core.shield = true := by
    simpa [D, T, j, localStep, hje] using hsafePair
  refine ⟨hnoActiveD, huniqueD, houtLeader,
    ?_, ?_, hcontrols.2.2.1, hcontrols.2.2.2,
    hcleanup.1, hcleanup.2.1, hcleanup.2.2.1,
    ?_, hcleanup.2.2.2.2.1, hcleanup.2.2.2.2.2, ?_⟩
  · simpa [j] using hjFollowerD
  · simpa [j] using hrightLabel
  · simpa [j] using hrightReset
  · simpa [j] using hsafeD

/-- Existential wrapper retaining the earlier schedule interface. -/
theorem normalizedOutgoingUniqueLeader_replay_reset_handoff
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hnormal : NormalizedOutgoingUniqueLeader hpsi ring C) :
    ∃ leader : Fin n,
      OutgoingResetFrontierUniqueLeader hpsi ring
        (localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C leader) := by
  obtain ⟨leader, hat⟩ := hnormal
  exact ⟨leader, leader,
    normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
      hpsi ring hn C leader hat⟩

/-- From every leaderless nondivisible input, a bounded schedule reaches the
first authenticated reset frontier.  Relative to the normalized outgoing
leader endpoint, the added schedule is the singleton replay of that edge. -/
theorem
    exists_preCheckResetLeaderSink_resetFrontier_from_leaderless_uniform
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      actual.length ≤ 2 * (n + 1) ^ 3 + 1 ∧
      OutgoingResetFrontierUniqueLeader hpsi ring D := by
  obtain ⟨initial, A, hA, hinitialLength, hnormal⟩ :=
    exists_preCheckResetLeaderSink_normalizedOutgoing_from_leaderless_uniform
      hpsi ring hn hndvd C hleaderless
  obtain ⟨leader, hfrontier⟩ :=
    normalizedOutgoingUniqueLeader_replay_reset_handoff
      hpsi ring hn A hnormal
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T A leader
  change OutgoingResetFrontierUniqueLeader hpsi ring D at hfrontier
  let actual := initial ++ [leader]
  refine ⟨actual, D, ?_, ?_, hfrontier⟩
  · calc
      D = runLocalSchedule ring T A [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C initial) [leader] := by rw [← hA]
      _ = runLocalSchedule ring T C (initial ++ [leader]) :=
        (runLocalSchedule_append_expiring
          ring T C initial [leader]).symm
      _ = runLocalSchedule ring T C actual := by rfl
  · unfold actual
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- On a nondivisible ring, the leader-sink transition has a bounded schedule
from every physically leaderless input to its unique first physical leader. -/
theorem exists_preCheckResetLeaderSink_hasUniqueLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hleaderless : RawLeaderless (eraseExpiringConfig C)) :
    ∃ actual : DetSchedule n,
      actual.length ≤ (2 * n + 1) * (n + 1) ∧
      hasUniqueLeader n
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau)
            C actual)) := by
  obtain ⟨actual, _last, hactualLength, hactualUnique,
      _hactualLocation, _hactualCount⟩ :=
    exists_preCheckResetLeaderSink_firstLeader_location_of_not_dvd
      hpsi ring hn hndvd C hleaderless
  exact ⟨actual, hactualLength, hactualUnique⟩

/-- The same leader-sink transition reaches a physical leader from every
finite input on a nondivisible ring, stopping immediately if one exists. -/
theorem exists_preCheckResetLeaderSink_hasLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ actual : DetSchedule n,
      actual.length ≤ (2 * n + 1) * (n + 1) ∧
      RawHasLeader
        (eraseExpiringConfig
          (runLocalSchedule ring
            (wallSweepPreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau)
            C actual)) := by
  by_cases hleader : RawHasLeader (eraseExpiringConfig C)
  · exact ⟨[], by simp, by simpa [runLocalSchedule] using hleader⟩
  · have hleaderless : RawLeaderless (eraseExpiringConfig C) :=
      RawLeaderless.of_not_hasLeader hleader
    obtain ⟨actual, hlength, hunique⟩ :=
      exists_preCheckResetLeaderSink_hasUniqueLeader_of_not_dvd
        hpsi ring hn hndvd C hleaderless
    refine ⟨actual, hlength, ?_⟩
    obtain ⟨leader, hleader, _⟩ := hunique
    exact ⟨leader, by simpa [AgentState.isLeader] using hleader⟩

end PPLLPpsiLeaderCreationRepair
