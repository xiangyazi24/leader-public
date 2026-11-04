import Leader.Wu.WallSweep.ClockwiseRetry
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy

set_option autoImplicit false

namespace BirthFullHostCheckEntry

open PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepPreCheckResetRepair

/-! ## Divisible CHECK entry under the current complete host

The earlier six-edge CHECK-origin witness used the combined-local and older
wall transitions.  This module replays that physical writer under the complete
reset-probe, leader-sink, birth-signal-zero host used by the current
nondivisible entry theorems.  It does not assume a refinement from the abstract
`BirthSweepSpec` control carrier, which is a different transition system.
-/

/-- The existing canonical four-site CHECK witness, run under the same host
as `exists_birthSignalZero_hasUniqueLeader_of_not_dvd`. -/
def checkEntryAfter : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule (⟨by omega⟩ : DirectedRing 4)
    (wallSweepBirthSignalZeroPathStallTransition (by omega) 0 6)
    twoGroupTrap twoGroupTrapEscapeSchedule

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The complete current host preserves the CHECK-origin escape in six
physical interactions and gives its new leader the required zero signal. -/
theorem current_host_check_entry :
    (checkEntryAfter 0).core.core.leader = false ∧
    (checkEntryAfter 1).core.core.leader = false ∧
    (checkEntryAfter 2).core.core.leader = true ∧
    (checkEntryAfter 3).core.core.leader = false ∧
    (checkEntryAfter 2).core.core.label = 0 ∧
    (checkEntryAfter 2).core.core.signal_B = 0 := by
  decide

/-- Place the four-site physical CHECK writer inside any larger ring.  The
selected six edges never use the edge leaving this window. -/
def embedFour {n : Nat} (hfour : 4 ≤ n) (i : Fin 4) : Fin n :=
  ⟨i.val, by omega⟩

private theorem embedFour_eq_iff {n : Nat} (hfour : 4 ≤ n) (i j : Fin 4) :
    embedFour hfour i = embedFour hfour j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun k : Fin n => k.val) h
  · rintro rfl
    rfl

private theorem embedFour_neighbor {n : Nat} (ring : DirectedRing n)
    (hfour : 4 ≤ n) (e : Fin 4) (he : e.val < 3) :
    ring.rightNeighbor (embedFour hfour e) =
      embedFour hfour ((⟨by omega⟩ : DirectedRing 4).rightNeighbor e) := by
  apply Fin.ext
  change (e.val + 1) % n = (e.val + 1) % 4
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The existing two-group CHECK fixture is required only on its four local
cells; all other finite-state registers in the population are arbitrary. -/
def CheckWindow {n : Nat} (hfour : 4 ≤ n)
    (C : Fin n → ExpiringAgentState 2 0 6) : Prop :=
  ∀ i, C (embedFour hfour i) = twoGroupTrap i

private theorem fourWindow_step
    {Q : Type} {n : Nat} (ring : DirectedRing n) (hfour : 4 ≤ n)
    (T : Q → Q → Q × Q) (small : Fin 4 → Q) (large : Fin n → Q)
    (e : Fin 4) (he : e.val < 3)
    (hagree : ∀ i, large (embedFour hfour i) = small i) :
    ∀ i, localStep ring T large (embedFour hfour e) (embedFour hfour i) =
      localStep (⟨by omega⟩ : DirectedRing 4) T small e i := by
  intro i
  have hnbr := embedFour_neighbor ring hfour e he
  simp only [localStep, hnbr, hagree, embedFour_eq_iff]

/-- Locality lifts the same physical six-edge writer to a larger ring.  The
proof follows each selected endpoint, so it does not replace the host's
transition by an abstract birth guard or a reseeded process. -/
private theorem fourWindow_run
    {Q : Type} {n : Nat} (ring : DirectedRing n) (hfour : 4 ≤ n)
    (T : Q → Q → Q × Q) (word : DetSchedule 4)
    (hnonwrap : ∀ e ∈ word, e.val < 3)
    (small : Fin 4 → Q) (large : Fin n → Q)
    (hagree : ∀ i, large (embedFour hfour i) = small i) :
    ∀ i, runLocalSchedule ring T large (word.map (embedFour hfour))
        (embedFour hfour i) =
      runLocalSchedule (⟨by omega⟩ : DirectedRing 4) T small word i := by
  induction word generalizing small large with
  | nil => exact hagree
  | cons e rest ih =>
      have he := hnonwrap e List.mem_cons_self
      have htail : ∀ f ∈ rest, f.val < 3 :=
        fun f hf => hnonwrap f (List.mem_cons_of_mem e hf)
      exact ih htail _ _ (fourWindow_step ring hfour T small large e he hagree)

/-- The relocated physical CHECK word has exactly six interactions. -/
def checkWindowSchedule {n : Nat} (hfour : 4 ≤ n) : DetSchedule n :=
  twoGroupTrapEscapeSchedule.map (embedFour hfour)

attribute [local irreducible] wallSweepBirthSignalZeroPathStallTransition

/-- A four-cell CHECK window in any larger ring creates a zero-labelled,
zero-signal leader under the complete current host within six interactions.
The rest of the population is arbitrary.  Producing `CheckWindow` from every
leaderless divisible input remains a separate physical normalization task. -/
theorem checkWindow_creates_leader
    {n : Nat} (ring : DirectedRing n) (hfour : 4 ≤ n)
    (C : Fin n → ExpiringAgentState 2 0 6) (hC : CheckWindow hfour C) :
    (checkWindowSchedule hfour).length = 6 ∧
      let D := runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition (by omega) 0 6)
        C (checkWindowSchedule hfour)
      (D (embedFour hfour 2)).core.core.leader = true ∧
      (D (embedFour hfour 2)).core.core.label = 0 ∧
      (D (embedFour hfour 2)).core.core.signal_B = 0 := by
  have hnonwrap : ∀ e ∈ twoGroupTrapEscapeSchedule, e.val < 3 := by
    decide
  have hsim := fourWindow_run ring hfour
    (wallSweepBirthSignalZeroPathStallTransition (by omega) 0 6)
    twoGroupTrapEscapeSchedule hnonwrap twoGroupTrap C hC 2
  refine ⟨by simp [checkWindowSchedule, twoGroupTrapEscapeSchedule], ?_⟩
  dsimp only [checkWindowSchedule]
  rw [hsim]
  exact ⟨current_host_check_entry.2.2.1,
    current_host_check_entry.2.2.2.2⟩

attribute [local semireducible] wallSweepBirthSignalZeroPathStallTransition

/-! ## The same writer must not be mistaken for a safety certificate

The old no-CHECK protocol's `OutputLegit` ignores the ruler bits.  Its canonical
six-site member therefore contains two equal follower groups away from the
existing leader.  The exact current full host executes the same CHECK writer
there and creates another leader.  This is a full-host trace, rather than a
claim about the separate PPartial or abstract sweep models.
-/

/-- Canonical member of the earlier output-safe kernel on six sites. -/
def remoteLeaderInitial : Fin 6 → ExpiringAgentState 2 0 6 :=
  outputFinite (by omega : 0 < 2) 0 6

/-- The source-authenticated comparison occurs strictly on sites two to five,
so none of its six scheduled edges touches the existing leader at zero. -/
def remoteLeaderAfter : Fin 6 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule (⟨by omega⟩ : DirectedRing 6)
    (wallSweepBirthSignalZeroPathStallTransition (by omega) 0 6)
    remoteLeaderInitial [2, 3, 2, 4, 3, 4]

/-- The input really satisfies the imported output-safe kernel; there are no
forged comparison paths or authorization bits in this canonical fixture. -/
theorem remoteLeaderInitial_outputLegit :
    OutputLegit (by omega : 0 < 2) (⟨by omega⟩ : DirectedRing 6)
      remoteLeaderInitial :=
  outputLegit_inhabited (by omega) 0 6 (⟨by omega⟩ : DirectedRing 6)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The real complete host can create a second leader by comparing genuinely
equal remote groups in the old output-safe kernel.  Stronger ruler/snapshot
safety is necessary before this writer can be composed into a closed protocol. -/
theorem current_host_remote_equal_creates_second_leader :
    (remoteLeaderAfter 0).core.core.leader = true ∧
      (remoteLeaderAfter 4).core.core.leader = true := by
  decide

attribute [local irreducible] wallSweepBirthSignalZeroPathStallTransition

/-- The six-edge full-host endpoint fails the actual imported uniqueness
field, so the old output-safe kernel cannot be reused as its closed kernel. -/
theorem remoteLeaderAfter_not_outputLegit :
    ¬ OutputLegit (by omega : 0 < 2) (⟨by omega⟩ : DirectedRing 6)
      remoteLeaderAfter := by
  intro h
  obtain ⟨leader, _, honly⟩ := h.unique_leader
  have hzero := honly 0 (by
    change (remoteLeaderAfter 0).core.core.leader = true
    exact current_host_remote_equal_creates_second_leader.1)
  have hfour := honly 4 (by
    change (remoteLeaderAfter 4).core.core.leader = true
    exact current_host_remote_equal_creates_second_leader.2)
  have hbad : (0 : Fin 6) = 4 := hzero.trans hfour.symm
  have hv := congrArg (fun i : Fin 6 => i.val) hbad
  omega

/-- The old kernel is not closed under the same full local transition used
by the checked nondivisible leader-entry theorem.  The statement is about the
actual local transition; no alternative protocol dispatcher is substituted. -/
theorem current_host_not_closes_outputLegit :
    ¬ (∀ C : Fin 6 → ExpiringAgentState 2 0 6,
      OutputLegit (by omega : 0 < 2) (⟨by omega⟩ : DirectedRing 6) C →
      ∀ e, OutputLegit (by omega : 0 < 2) (⟨by omega⟩ : DirectedRing 6)
        (localStep (⟨by omega⟩ : DirectedRing 6)
          (wallSweepBirthSignalZeroPathStallTransition (by omega) 0 6) C e)) := by
  intro hclosed
  have hrun : ∀ word : DetSchedule 6,
      ∀ C : Fin 6 → ExpiringAgentState 2 0 6,
        OutputLegit (by omega : 0 < 2) (⟨by omega⟩ : DirectedRing 6) C →
        OutputLegit (by omega : 0 < 2) (⟨by omega⟩ : DirectedRing 6)
          (runLocalSchedule (⟨by omega⟩ : DirectedRing 6)
            (wallSweepBirthSignalZeroPathStallTransition (by omega) 0 6) C word) := by
    intro word
    induction word with
    | nil => intros C hC; exact hC
    | cons e rest ih =>
        intro C hC
        exact ih _ (hclosed C hC e)
  exact remoteLeaderAfter_not_outputLegit
    (hrun [2, 3, 2, 4, 3, 4] remoteLeaderInitial remoteLeaderInitial_outputLegit)

end BirthFullHostCheckEntry

#print axioms BirthFullHostCheckEntry.current_host_check_entry
#print axioms BirthFullHostCheckEntry.checkWindow_creates_leader
#print axioms BirthFullHostCheckEntry.current_host_remote_equal_creates_second_leader
#print axioms BirthFullHostCheckEntry.current_host_not_closes_outputLegit
