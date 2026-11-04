import Leader.Wu.WallSweep.FiniteIntegration
import Leader.Wu.WallSweep.EchoDrain

/-!
# Protected full-transition cleanup interface

T19 deletion priority is the one stage that can return before Algorithm 14.
These proof-only predicates state exactly that the scheduled cleanup word is
not diverted. They add no executable bit and do not require the other full
transition stages to be identity.
-/

namespace PPLLWallSweepFiniteCleanup

open PPLL PPLLRepair PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLPathStallComparisonRepair PPLLWallSweepFinite PPLLResearchFormulation
  PPLLTerminalEqualSupportRepair

/-- The normalized authorized pair reaches the ordinary Algorithm-1 branch. -/
def AuthorizedPriorityOpen (l r : AuthorizedAgentState ψ) : Prop :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  deletionActive l0 = false ∧ deletionActive r0 = false

instance authorizedPriorityOpen_decidable (l r : AuthorizedAgentState ψ) :
    Decidable (AuthorizedPriorityOpen l r) := by
  unfold AuthorizedPriorityOpen
  infer_instance

/-- Priority openness on the actual finite carrier. -/
def WallPriorityOpen (l r : ExpiringAgentState ψ κ τ) : Prop :=
  AuthorizedPriorityOpen l.core.erase r.core.erase

instance wallPriorityOpen_decidable
    (l r : ExpiringAgentState ψ κ τ) :
    Decidable (WallPriorityOpen l r) := by
  unfold WallPriorityOpen
  infer_instance

/-- Executable form used by finite regressions. -/
def wallPriorityOpenBool (l r : ExpiringAgentState ψ κ τ) : Bool :=
  let l0 := normalizeDeletion l.core.erase
  let r0 := normalizeDeletion r.core.erase
  !deletionActive l0 && !deletionActive r0

theorem wallPriorityOpenBool_eq_true_iff
    (l r : ExpiringAgentState ψ κ τ) :
    wallPriorityOpenBool l r = true ↔ WallPriorityOpen l r := by
  simp [wallPriorityOpenBool, WallPriorityOpen, AuthorizedPriorityOpen]

/-- Every call of one concrete scheduled run reaches Algorithm 14. This is a
predicate over the execution, not protocol memory. -/
def WallPriorityOpenAlong (hψ : ψ > 0) (κ τ : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ) :
    DetSchedule n → Prop
  | [] => True
  | e :: rest =>
      WallPriorityOpen (C e) (C (ring.rightNeighbor e)) ∧
      WallPriorityOpenAlong hψ κ τ ring
        (localStep ring (wallSweepPathStallTransition hψ κ τ) C e) rest

/-- Executable form of priority openness along a concrete run. -/
def wallPriorityOpenAlongBool (hψ : ψ > 0) (κ τ : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    : DetSchedule n → Bool
  | [] => true
  | e :: rest =>
      wallPriorityOpenBool (C e) (C (ring.rightNeighbor e)) &&
      wallPriorityOpenAlongBool hψ κ τ ring
        (localStep ring (wallSweepPathStallTransition hψ κ τ) C e) rest

theorem wallPriorityOpenAlongBool_eq_true_iff
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (schedule : DetSchedule n) :
    wallPriorityOpenAlongBool hψ κ τ ring C schedule = true ↔
      WallPriorityOpenAlong hψ κ τ ring C schedule := by
  induction schedule generalizing C with
  | nil => simp [wallPriorityOpenAlongBool, WallPriorityOpenAlong]
  | cons e rest ih =>
      simp only [wallPriorityOpenAlongBool, WallPriorityOpenAlong,
        Bool.and_eq_true, wallPriorityOpenBool_eq_true_iff]
      rw [ih]

/-- Priority openness exposes the one ordinary full-stage composition without
unfolding any of its internal algorithms. -/
theorem wallSweepAuthorizedTransition_eq_normal_of_priority_open
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeRaw := wallSweepAuthorizedBeforeCheck hψ κ l0 r0
    let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
    let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    wallSweepAuthorizedTransition hψ κ l r =
      markLeaderBirth born
        (wallSweepAuthorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  change deletionActive l0 = false ∧ deletionActive r0 = false at hopen
  unfold wallSweepAuthorizedTransition
  dsimp only
  split
  · rename_i hdel
    rw [hopen.2] at hdel
    contradiction
  · split
    · rename_i hdel
      rw [hopen.1] at hdel
      contradiction
    · rfl

/-! ## Strict deletion-interrupt contract -/

/-- One unit for a present physical comparison path. -/
def comparisonPathMass (u : ExpiringAgentState ψ κ τ) : Nat :=
  match u.core.erase.core.path with
  | .bot => 0
  | .some _ _ => 1

/-- Algorithm-14 control and the designated-leader geometry are framed during
a deletion interrupt. -/
def ResetEchoFrame (old new : ExpiringAgentState ψ κ τ) : Prop :=
  new.core.erase.core.leader = old.core.erase.core.leader ∧
  new.core.erase.core.label = old.core.erase.core.label ∧
  new.core.erase.core.reset_cmd = old.core.erase.core.reset_cmd ∧
  new.core.erase.core.echo = old.core.erase.core.echo ∧
  new.core.erase.core.count = old.core.erase.core.count

private theorem deletionActive_true_fields (u : AuthorizedAgentState ψ)
    (hactive : deletionActive u = true) :
    u.core.state = .eliminate_signal ∧ u.core.path ≠ .bot := by
  cases hpath : u.core.path with
  | bot => simp [deletionActive, pathPresent, hpath] at hactive
  | some label bit =>
      have hstate : u.core.state = .eliminate_signal := by
        simpa [deletionActive, pathPresent, hpath] using hactive
      exact ⟨hstate, by simp⟩

/-- On an active responder, the complete authorized wall transition selects
only Algorithm 9. The responder path is deleted; the initiator path and all
reset/echo frame fields are unchanged. -/
theorem wallSweepAuthorized_active_responder_core
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive r = true) :
    let q := wallSweepAuthorizedTransition hψ κ l r
    q.1.core.path = l.core.path ∧ q.2.core.path = .bot ∧
      q.1.core.leader = l.core.leader ∧
      q.2.core.leader = r.core.leader ∧
      q.1.core.label = l.core.label ∧ q.2.core.label = r.core.label ∧
      q.1.core.reset_cmd = l.core.reset_cmd ∧
      q.2.core.reset_cmd = r.core.reset_cmd ∧
      q.1.core.echo = l.core.echo ∧ q.2.core.echo = r.core.echo ∧
      q.1.core.count = l.core.count ∧ q.2.core.count = r.core.count := by
  obtain ⟨hrstate, hrpath⟩ := deletionActive_true_fields r hr
  have hnr := normalizeDeletion_eq_of_path_present r hrpath
  let l0 := normalizeDeletion l
  have hbranch : wallSweepAuthorizedTransition hψ κ l r =
      authorizedEliminateSig hψ l0 r := by
    simp [wallSweepAuthorizedTransition, l0, hnr, hr]
  rw [hbranch]
  unfold authorizedEliminateSig authorizedReconcile
  dsimp only
  unfold l0 normalizeDeletion
  split <;>
    simp [eliminateSig, hrstate]

/-- The active-responder priority branch changes comparison controls only and
frames both shields. -/
theorem wallSweepAuthorized_active_responder_shields
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive r = true) :
    let q := wallSweepAuthorizedTransition hψ κ l r
    q.1.core.shield = l.core.shield ∧
      q.2.core.shield = r.core.shield := by
  obtain ⟨hrstate, hrpath⟩ := deletionActive_true_fields r hr
  have hnr := normalizeDeletion_eq_of_path_present r hrpath
  let l0 := normalizeDeletion l
  have hbranch : wallSweepAuthorizedTransition hψ κ l r =
      authorizedEliminateSig hψ l0 r := by
    simp [wallSweepAuthorizedTransition, l0, hnr, hr]
  rw [hbranch]
  unfold authorizedEliminateSig authorizedReconcile
  dsimp only
  unfold l0 normalizeDeletion
  split <;> simp [eliminateSig, hrstate]

/-- Deletion-priority expiration can retain the base path or clear it, and it
frames every reset/echo field used by the interrupt schedule. -/
theorem deletionPriorityExpireOne_path_frame (old out :
    ExpiringAgentState ψ κ τ) :
    let q := deletionPriorityExpireOne τ old out
    (q.core.erase.core.path = out.core.erase.core.path ∨
      q.core.erase.core.path = .bot) ∧
      q.core.erase.core.leader = out.core.erase.core.leader ∧
      q.core.erase.core.label = out.core.erase.core.label ∧
      q.core.erase.core.reset_cmd = out.core.erase.core.reset_cmd ∧
      q.core.erase.core.echo = out.core.erase.core.echo ∧
      q.core.erase.core.count = out.core.erase.core.count := by
  unfold deletionPriorityExpireOne pathExpireOne
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · constructor
        · exact .inr rfl
        · simp [clearComparisonCarrier, AuthorizedBoundedAgentState.erase,
            BoundedAgentState.erase]
      · simp

/-- The outer deletion/path-stall wrapper never changes the shield bit. -/
theorem deletionPriorityExpireOne_shield_frame
    (old out : ExpiringAgentState ψ κ τ) :
    (deletionPriorityExpireOne τ old out).core.erase.core.shield =
      out.core.erase.core.shield := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · unfold pathExpireOne
    split
    · rfl
    · split
      · unfold clearComparisonCarrier
        rfl
      · rfl

/-- A full wall interaction with an active deletion responder is a strict
path-deletion interrupt. It cannot consume reset/echo progress, and the outer
stall layer cannot recreate path material. -/
theorem wallSweepPathStall_active_responder_contract
    (hψ : ψ > 0) (l r : ExpiringAgentState ψ κ τ)
    (hr : deletionActive r.core.erase = true) :
    let q := wallSweepPathStallTransition hψ κ τ l r
    comparisonPathMass q.1 + comparisonPathMass q.2 <
        comparisonPathMass l + comparisonPathMass r ∧
      comparisonPathMass q.1 ≤ comparisonPathMass l ∧
      comparisonPathMass q.2 < comparisonPathMass r ∧
      ResetEchoFrame l q.1 ∧ ResetEchoFrame r q.2 := by
  let bounded := wallSweepBoundedTransition hψ κ l.core r.core
  let lBase : ExpiringAgentState ψ κ τ := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState ψ κ τ := ⟨bounded.2, r.stall⟩
  let q := (deletionPriorityExpireOne τ l lBase,
    deletionPriorityExpireOne τ r rBase)
  have herase := erase_wallSweepBoundedTransition hψ κ l.core r.core
  have hcore := wallSweepAuthorized_active_responder_core
    hψ κ l.core.erase r.core.erase hr
  rcases hcore with ⟨hcLPath, hcRPath, hcLLeader, hcRLeader,
    hcLLabel, hcRLabel, hcLReset, hcRReset, hcLEcho, hcREcho,
    hcLCount, hcRCount⟩
  have hleftErase := congrArg Prod.fst herase
  have hrightErase := congrArg Prod.snd herase
  change bounded.1.erase =
    (wallSweepAuthorizedTransition hψ κ l.core.erase r.core.erase).1
      at hleftErase
  change bounded.2.erase =
    (wallSweepAuthorizedTransition hψ κ l.core.erase r.core.erase).2
      at hrightErase
  have hlPath : lBase.core.erase.core.path = l.core.erase.core.path := by
    change bounded.1.erase.core.path = l.core.erase.core.path
    rw [hleftErase]
    exact hcLPath
  have hrPath : rBase.core.erase.core.path = .bot := by
    change bounded.2.erase.core.path = .bot
    rw [hrightErase]
    exact hcRPath
  have hlFrame := deletionPriorityExpireOne_path_frame l lBase
  have hrFrame := deletionPriorityExpireOne_path_frame r rBase
  change
    (q.1.core.erase.core.path = lBase.core.erase.core.path ∨
      q.1.core.erase.core.path = .bot) ∧
      _ at hlFrame
  change
    (q.2.core.erase.core.path = rBase.core.erase.core.path ∨
      q.2.core.erase.core.path = .bot) ∧
      _ at hrFrame
  have hresetLeft :
      lBase.core.erase.core.leader = l.core.erase.core.leader ∧
      lBase.core.erase.core.label = l.core.erase.core.label ∧
      lBase.core.erase.core.reset_cmd = l.core.erase.core.reset_cmd ∧
      lBase.core.erase.core.echo = l.core.erase.core.echo ∧
      lBase.core.erase.core.count = l.core.erase.core.count := by
    constructor
    · change bounded.1.erase.core.leader = l.core.erase.core.leader
      rw [hleftErase]
      exact hcLLeader
    constructor
    · change bounded.1.erase.core.label = l.core.erase.core.label
      rw [hleftErase]
      exact hcLLabel
    constructor
    · change bounded.1.erase.core.reset_cmd = l.core.erase.core.reset_cmd
      rw [hleftErase]
      exact hcLReset
    constructor
    · change bounded.1.erase.core.echo = l.core.erase.core.echo
      rw [hleftErase]
      exact hcLEcho
    · change bounded.1.erase.core.count = l.core.erase.core.count
      rw [hleftErase]
      exact hcLCount
  have hresetRight :
      rBase.core.erase.core.leader = r.core.erase.core.leader ∧
      rBase.core.erase.core.label = r.core.erase.core.label ∧
      rBase.core.erase.core.reset_cmd = r.core.erase.core.reset_cmd ∧
      rBase.core.erase.core.echo = r.core.erase.core.echo ∧
      rBase.core.erase.core.count = r.core.erase.core.count := by
    constructor
    · change bounded.2.erase.core.leader = r.core.erase.core.leader
      rw [hrightErase]
      exact hcRLeader
    constructor
    · change bounded.2.erase.core.label = r.core.erase.core.label
      rw [hrightErase]
      exact hcRLabel
    constructor
    · change bounded.2.erase.core.reset_cmd = r.core.erase.core.reset_cmd
      rw [hrightErase]
      exact hcRReset
    constructor
    · change bounded.2.erase.core.echo = r.core.erase.core.echo
      rw [hrightErase]
      exact hcREcho
    · change bounded.2.erase.core.count = r.core.erase.core.count
      rw [hrightErase]
      exact hcRCount
  change comparisonPathMass q.1 + comparisonPathMass q.2 <
      comparisonPathMass l + comparisonPathMass r ∧
    comparisonPathMass q.1 ≤ comparisonPathMass l ∧
    comparisonPathMass q.2 < comparisonPathMass r ∧
    ResetEchoFrame l q.1 ∧ ResetEchoFrame r q.2
  have hrInput : r.core.erase.core.path ≠ .bot :=
    (deletionActive_true_fields r.core.erase hr).2
  have hqLeft : q.1.core.erase.core.path = l.core.erase.core.path ∨
      q.1.core.erase.core.path = .bot := by
    rcases hlFrame.1 with hkeep | hclear
    · exact .inl (hkeep.trans hlPath)
    · exact .inr hclear
  have hqRight : q.2.core.erase.core.path = .bot := by
    rcases hrFrame.1 with hkeep | hclear
    · exact hkeep.trans hrPath
    · exact hclear
  have hleftMass : comparisonPathMass q.1 ≤ comparisonPathMass l := by
    cases hlIn : l.core.erase.core.path with
    | bot =>
      have hqL : q.1.core.erase.core.path = .bot :=
        hqLeft.elim (fun h => h.trans hlIn) id
      simp [comparisonPathMass, hqL, hlIn]
    | some lLabel lBit =>
      rcases hqLeft with hkeep | hclear
      · simp [comparisonPathMass, hkeep, hlIn]
      · simp [comparisonPathMass, hclear, hlIn]
  have hrightMass : comparisonPathMass q.2 < comparisonPathMass r := by
    cases hrIn : r.core.erase.core.path with
    | bot => exact (hrInput hrIn).elim
    | some rLabel rBit => simp [comparisonPathMass, hqRight, hrIn]
  refine ⟨by omega, hleftMass, hrightMass, ?_, ?_⟩
  · unfold ResetEchoFrame
    exact ⟨hlFrame.2.1.trans hresetLeft.1,
      hlFrame.2.2.1.trans hresetLeft.2.1,
      hlFrame.2.2.2.1.trans hresetLeft.2.2.1,
      hlFrame.2.2.2.2.1.trans hresetLeft.2.2.2.1,
      hlFrame.2.2.2.2.2.trans hresetLeft.2.2.2.2⟩
  · unfold ResetEchoFrame
    exact ⟨hrFrame.2.1.trans hresetRight.1,
      hrFrame.2.2.1.trans hresetRight.2.1,
      hrFrame.2.2.2.1.trans hresetRight.2.2.1,
      hrFrame.2.2.2.2.1.trans hresetRight.2.2.2.1,
      hrFrame.2.2.2.2.2.trans hresetRight.2.2.2.2⟩

/-- A full active-responder deletion interrupt frames both shields through
bounded reification and the outer expiry wrapper. -/
theorem wallSweepPathStall_active_responder_shields
    (hψ : ψ > 0) (l r : ExpiringAgentState ψ κ τ)
    (hr : deletionActive r.core.erase = true) :
    let q := wallSweepPathStallTransition hψ κ τ l r
    q.1.core.erase.core.shield = l.core.erase.core.shield ∧
      q.2.core.erase.core.shield = r.core.erase.core.shield := by
  let bounded := wallSweepBoundedTransition hψ κ l.core r.core
  let lBase : ExpiringAgentState ψ κ τ := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState ψ κ τ := ⟨bounded.2, r.stall⟩
  let q := (deletionPriorityExpireOne τ l lBase,
    deletionPriorityExpireOne τ r rBase)
  have herase := erase_wallSweepBoundedTransition hψ κ l.core r.core
  have hleftErase := congrArg Prod.fst herase
  have hrightErase := congrArg Prod.snd herase
  change bounded.1.erase =
    (wallSweepAuthorizedTransition hψ κ l.core.erase r.core.erase).1
      at hleftErase
  change bounded.2.erase =
    (wallSweepAuthorizedTransition hψ κ l.core.erase r.core.erase).2
      at hrightErase
  have hcore := wallSweepAuthorized_active_responder_shields
    hψ κ l.core.erase r.core.erase hr
  have hbaseL : lBase.core.erase.core.shield =
      l.core.erase.core.shield := by
    change bounded.1.erase.core.shield = l.core.erase.core.shield
    rw [hleftErase]
    exact hcore.1
  have hbaseR : rBase.core.erase.core.shield =
      r.core.erase.core.shield := by
    change bounded.2.erase.core.shield = r.core.erase.core.shield
    rw [hrightErase]
    exact hcore.2
  change q.1.core.erase.core.shield = l.core.erase.core.shield ∧
    q.2.core.erase.core.shield = r.core.erase.core.shield
  exact ⟨(deletionPriorityExpireOne_shield_frame l lBase).trans hbaseL,
    (deletionPriorityExpireOne_shield_frame r rBase).trans hbaseR⟩

/-! ## Global deletion-drain measure -/

def comparisonPathCount (C : Fin n → ExpiringAgentState ψ κ τ) : Nat :=
  (List.ofFn (fun i => comparisonPathMass (C i))).sum

theorem comparisonPathMass_le_one (u : ExpiringAgentState ψ κ τ) :
    comparisonPathMass u ≤ 1 := by
  unfold comparisonPathMass
  split <;> omega

/-- At most one physical comparison path is stored per agent. -/
theorem comparisonPathCount_le (C : Fin n → ExpiringAgentState ψ κ τ) :
    comparisonPathCount C ≤ n := by
  induction n with
  | zero => simp [comparisonPathCount]
  | succ n ih =>
      rw [comparisonPathCount, List.ofFn_succ, List.sum_cons]
      have hhead := comparisonPathMass_le_one (C 0)
      have htail := ih (C := fun i : Fin n => C i.succ)
      unfold comparisonPathCount at htail
      have htail' :
          (List.ofFn (fun i : Fin n => comparisonPathMass (C i.succ))).sum ≤ n := by
        simpa using htail
      omega

private theorem sum_ofFn_le
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_lt_of_le_of_lt
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i)
    (j : Fin n) (hj : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail := sum_ofFn_le
          (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
          (fun i => hfg i.succ)
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
          simp [j']
          omega
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
          (fun i => hfg i.succ) j' (by rw [hjsucc]; exact hj)
        have hhead := hfg 0
        omega

def NoActiveDeletion (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  ∀ i, deletionActive (C i).core.erase = false

theorem deletionActive_normalize_false (u : AuthorizedAgentState ψ)
    (h : deletionActive u = false) :
    deletionActive (normalizeDeletion u) = false := by
  unfold normalizeDeletion
  split
  · simp [deletionActive, pathPresent]
  · exact h

/-- A globally drained configuration opens the ordinary branch on every edge. -/
theorem WallPriorityOpen.of_noActiveDeletion
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : NoActiveDeletion C) (ring : DirectedRing n) (e : Fin n) :
    WallPriorityOpen (C e) (C (ring.rightNeighbor e)) := by
  unfold WallPriorityOpen AuthorizedPriorityOpen
  exact ⟨deletionActive_normalize_false _ (hC e),
    deletionActive_normalize_false _ (hC (ring.rightNeighbor e))⟩

def ResetEchoConfigFrame
    (C D : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  ∀ i, ResetEchoFrame (C i) (D i)

def ShieldConfigFrame
    (C D : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  ∀ i, (D i).core.erase.core.shield = (C i).core.erase.core.shield

theorem ResetEchoFrame.refl (u : ExpiringAgentState ψ κ τ) :
    ResetEchoFrame u u := by
  simp [ResetEchoFrame]

theorem ResetEchoFrame.trans {a b c : ExpiringAgentState ψ κ τ}
    (hab : ResetEchoFrame a b) (hbc : ResetEchoFrame b c) :
    ResetEchoFrame a c := by
  unfold ResetEchoFrame at hab hbc ⊢
  exact ⟨hbc.1.trans hab.1,
    hbc.2.1.trans hab.2.1,
    hbc.2.2.1.trans hab.2.2.1,
    hbc.2.2.2.1.trans hab.2.2.2.1,
    hbc.2.2.2.2.trans hab.2.2.2.2⟩

theorem ResetEchoConfigFrame.trans
    {A B C : Fin n → ExpiringAgentState ψ κ τ}
    (hAB : ResetEchoConfigFrame A B)
    (hBC : ResetEchoConfigFrame B C) :
    ResetEchoConfigFrame A C := by
  intro i
  exact (hAB i).trans (hBC i)

theorem ShieldConfigFrame.refl
    (C : Fin n → ExpiringAgentState ψ κ τ) :
    ShieldConfigFrame C C := by
  intro i
  rfl

theorem ShieldConfigFrame.trans
    {A B C : Fin n → ExpiringAgentState ψ κ τ}
    (hAB : ShieldConfigFrame A B)
    (hBC : ShieldConfigFrame B C) :
    ShieldConfigFrame A C := by
  intro i
  exact (hBC i).trans (hAB i)

/-- Scheduling the predecessor of an active host strictly decreases the global
physical path count and frames reset/echo data at every ring position. -/
theorem wallSweepPathStall_active_edge_decreases
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hactive : deletionActive (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPathStallTransition hψ κ τ) C e
    comparisonPathCount D < comparisonPathCount C ∧
      ResetEchoConfigFrame C D := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := wallSweepPathStallTransition hψ κ τ (C e) (C j)
  have hpair := wallSweepPathStall_active_responder_contract
    hψ (C e) (C j) hactive
  change comparisonPathMass q.1 + comparisonPathMass q.2 <
      comparisonPathMass (C e) + comparisonPathMass (C j) ∧
    comparisonPathMass q.1 ≤ comparisonPathMass (C e) ∧
    comparisonPathMass q.2 < comparisonPathMass (C j) ∧
    ResetEchoFrame (C e) q.1 ∧ ResetEchoFrame (C j) q.2 at hpair
  let D := localStep ring
    (wallSweepPathStallTransition hψ κ τ) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  have hmassLe : ∀ i, comparisonPathMass (D i) ≤
      comparisonPathMass (C i) := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hpair.2.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact Nat.le_of_lt hpair.2.2.1
      · have hsame : D i = C i := by
          simp [D, localStep, hie, hij, j]
        rw [hsame]
        exact Nat.le_refl _
  have hmassLt : comparisonPathMass (D j) < comparisonPathMass (C j) := by
    rw [hright]
    exact hpair.2.2.1
  constructor
  · unfold comparisonPathCount
    exact sum_ofFn_lt_of_le_of_lt
      (fun i => comparisonPathMass (D i))
      (fun i => comparisonPathMass (C i)) hmassLe j hmassLt
  · intro i
    by_cases hie : i = e
    · subst i
      change ResetEchoFrame (C e) (D e)
      rw [hleft]
      exact hpair.2.2.2.1
    · by_cases hij : i = j
      · subst i
        change ResetEchoFrame (C j) (D j)
        rw [hright]
        exact hpair.2.2.2.2
      · have hsame : D i = C i := by
          simp [D, localStep, hie, hij, j]
        change ResetEchoFrame (C i) (D i)
        rw [hsame]
        exact ResetEchoFrame.refl (C i)

/-- One global deletion interrupt frames every shield pointwise. -/
theorem wallSweepPathStall_active_edge_shield_frame
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hactive : deletionActive (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPathStallTransition hψ κ τ) C e
    ShieldConfigFrame C D := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := wallSweepPathStallTransition hψ κ τ (C e) (C j)
  have hpair := wallSweepPathStall_active_responder_shields
    hψ (C e) (C j) hactive
  let D := localStep ring
    (wallSweepPathStallTransition hψ κ τ) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  change ShieldConfigFrame C D
  intro i
  by_cases hie : i = e
  · subst i
    rw [hleft]
    exact hpair.1
  · by_cases hij : i = j
    · subst i
      rw [hright]
      exact hpair.2
    · have hsame : D i = C i := by
        simp [D, localStep, hie, hij, j]
      rw [hsame]

theorem rightNeighbor_leftNeighbor_wall
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-- Every currently active deletion wave admits a full-transition drain using
only predecessor edges. No interrupt can run a birth stage, and the whole
drain preserves reset/echo progress pointwise. -/
theorem exists_wallSweepDeletionDrain
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      let D := runLocalSchedule ring
        (wallSweepPathStallTransition hψ κ τ) C schedule
      NoActiveDeletion D ∧ ResetEchoConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, hnone, fun i => ResetEchoFrame.refl (C i)⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true =>
              exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j := by
          exact rightNeighbor_leftNeighbor_wall ring j
        let C₁ := localStep ring
          (wallSweepPathStallTransition hψ κ τ) C e
        have hstep := wallSweepPathStall_active_edge_decreases
          hψ ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C₁ < comparisonPathCount C ∧
          ResetEchoConfigFrame C C₁ at hstep
        have hlt : comparisonPathCount C₁ < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailNoActive, htailFrame⟩ :=
          ih (comparisonPathCount C₁) hlt C₁ rfl
        refine ⟨e :: tail, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · exact htailNoActive
        · exact hstep.2.trans htailFrame

/-- Canonical deletion drain with the two schedule-level facts needed by the
protected cleanup replay: shields are framed, and an already drained input
chooses the empty schedule. -/
theorem exists_wallSweepDeletionDrain_cleanupFrame
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPathStallTransition hψ κ τ) C schedule
      NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
        ShieldConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          fun i => ResetEchoFrame.refl (C i), ShieldConfigFrame.refl C⟩
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
        let C₁ := localStep ring
          (wallSweepPathStallTransition hψ κ τ) C e
        have hstep := wallSweepPathStall_active_edge_decreases
          hψ ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C₁ < comparisonPathCount C ∧
          ResetEchoConfigFrame C C₁ at hstep
        have hshield := wallSweepPathStall_active_edge_shield_frame
          hψ ring hn C e (by simpa [hneighbor] using hj)
        change ShieldConfigFrame C C₁ at hshield
        have hlt : comparisonPathCount C₁ < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailFrame, htailShield⟩ :=
          ih (comparisonPathCount C₁) hlt C₁ rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hstep.2.trans htailFrame
        · exact hshield.trans htailShield

/-- Restartable cleanup ranking: an interrupt decreases path count, while an
ordinary logical edge consumes one `(n+1)` block. -/
def cleanupInterruptMeasure
    (rest : DetSchedule n) (C : Fin n → ExpiringAgentState ψ κ τ) : Nat :=
  rest.length * (n + 1) + comparisonPathCount C

/-- A deletion interrupt leaves the logical word unchanged and strictly lowers
the secondary path-count component. -/
theorem cleanupInterruptMeasure_interrupt_lt
    (rest : DetSchedule n)
    (C D : Fin n → ExpiringAgentState ψ κ τ)
    (hdecrease : comparisonPathCount D < comparisonPathCount C) :
    cleanupInterruptMeasure rest D < cleanupInterruptMeasure rest C := by
  unfold cleanupInterruptMeasure
  omega

/-- Consuming one logical cleanup edge strictly lowers the ranking even when
that ordinary full transition creates the maximum possible number of paths. -/
theorem cleanupInterruptMeasure_intended_lt
    (e : Fin n) (rest : DetSchedule n)
    (C D : Fin n → ExpiringAgentState ψ κ τ) :
    cleanupInterruptMeasure rest D < cleanupInterruptMeasure (e :: rest) C := by
  have hbound := comparisonPathCount_le D
  have hn : 0 < n := by
    cases n with
    | zero => exact Fin.elim0 e
    | succ n => exact Nat.zero_lt_succ n
  unfold cleanupInterruptMeasure
  rw [List.length_cons, Nat.succ_mul]
  omega

/-! ## Restartable logical-word execution -/

/-- A flattened physical schedule executes each logical word edge only after a
bounded deletion drain. The relation records the no-active boundary and the
reset/echo frame of every inserted drain. -/
def RestartableWallExecution (hψ : ψ > 0) (κ τ : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ) :
    DetSchedule n → DetSchedule n →
      (Fin n → ExpiringAgentState ψ κ τ) → Prop
  | [], actual, D =>
      ∃ drain : DetSchedule n,
        actual = drain ∧
        D = runLocalSchedule ring
          (wallSweepPathStallTransition hψ κ τ) C drain ∧
        drain.length ≤ comparisonPathCount C ∧
        NoActiveDeletion D ∧ ResetEchoConfigFrame C D
  | e :: rest, actual, D =>
      ∃ (drain : DetSchedule n)
        (C₀ C₁ : Fin n → ExpiringAgentState ψ κ τ)
        (tail : DetSchedule n),
        actual = drain ++ [e] ++ tail ∧
        C₀ = runLocalSchedule ring
          (wallSweepPathStallTransition hψ κ τ) C drain ∧
        drain.length ≤ comparisonPathCount C ∧
        NoActiveDeletion C₀ ∧ ResetEchoConfigFrame C C₀ ∧
        C₁ = localStep ring
          (wallSweepPathStallTransition hψ κ τ) C₀ e ∧
        RestartableWallExecution hψ κ τ ring C₁ rest tail D

private theorem runLocalSchedule_append_wall
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (s t : DetSchedule n) :
    runLocalSchedule ring T C (s ++ t) =
      runLocalSchedule ring T (runLocalSchedule ring T C s) t := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

/-- The restart certificate records an actual execution of its flattened
physical schedule, not only its logical drain boundaries. -/
theorem RestartableWallExecution.runLocalSchedule_eq
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState ψ κ τ)
    (h : RestartableWallExecution hψ κ τ ring C word actual D) :
    D = runLocalSchedule ring
      (wallSweepPathStallTransition hψ κ τ) C actual := by
  induction word generalizing C actual with
  | nil =>
      rcases h with ⟨drain, hactual, hD, _, _, _⟩
      subst actual
      exact hD
  | cons e rest ih =>
      rcases h with ⟨drain, C0, C1, tail, hactual, hC0, _, _, _, hC1,
        htail⟩
      subst actual
      calc
        D = runLocalSchedule ring
            (wallSweepPathStallTransition hψ κ τ) C1 tail :=
          ih C1 tail htail
        _ = runLocalSchedule ring
            (wallSweepPathStallTransition hψ κ τ)
            (localStep ring (wallSweepPathStallTransition hψ κ τ) C0 e)
            tail := by rw [← hC1]
        _ = runLocalSchedule ring
            (wallSweepPathStallTransition hψ κ τ) C0 ([e] ++ tail) := rfl
        _ = runLocalSchedule ring
            (wallSweepPathStallTransition hψ κ τ)
            (runLocalSchedule ring
              (wallSweepPathStallTransition hψ κ τ) C drain)
            ([e] ++ tail) := by rw [← hC0]
        _ = runLocalSchedule ring
            (wallSweepPathStallTransition hψ κ τ) C
            (drain ++ ([e] ++ tail)) :=
          (runLocalSchedule_append_wall ring
            (wallSweepPathStallTransition hψ κ τ) C drain
            ([e] ++ tail)).symm
        _ = runLocalSchedule ring
            (wallSweepPathStallTransition hψ κ τ) C
            (drain ++ [e] ++ tail) := by simp [List.append_assoc]

/-- Every finite logical cleanup word has an interrupting full-wall execution.
Its actual schedule pays at most `n` deletion edges before each logical edge
and one final drain. -/
theorem exists_restartableWallCleanupSchedule
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (word : DetSchedule n) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState ψ κ τ),
      RestartableWallExecution hψ κ τ ring C word actual D ∧
      actual.length ≤
        word.length * (n + 1) + comparisonPathCount C := by
  induction word generalizing C with
  | nil =>
      obtain ⟨drain, hlength, hnoActive, hframe⟩ :=
        exists_wallSweepDeletionDrain hψ ring hn C
      let D := runLocalSchedule ring
        (wallSweepPathStallTransition hψ κ τ) C drain
      change NoActiveDeletion D at hnoActive
      change ResetEchoConfigFrame C D at hframe
      refine ⟨drain, D, ?_, ?_⟩
      · exact ⟨drain, rfl, rfl, hlength, hnoActive, hframe⟩
      · simpa using hlength
  | cons e rest ih =>
      obtain ⟨drain, hlength, hnoActive, hframe⟩ :=
        exists_wallSweepDeletionDrain hψ ring hn C
      let C₀ := runLocalSchedule ring
        (wallSweepPathStallTransition hψ κ τ) C drain
      change NoActiveDeletion C₀ at hnoActive
      change ResetEchoConfigFrame C C₀ at hframe
      let C₁ := localStep ring
        (wallSweepPathStallTransition hψ κ τ) C₀ e
      obtain ⟨tail, D, htail, htailLength⟩ := ih C₁
      let actual := drain ++ [e] ++ tail
      refine ⟨actual, D, ?_, ?_⟩
      · exact ⟨drain, C₀, C₁, tail, rfl, rfl, hlength,
          hnoActive, hframe, rfl, htail⟩
      · have hcount := comparisonPathCount_le C₁
        unfold actual
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [Nat.succ_mul]
        omega

end PPLLWallSweepFiniteCleanup
