import Leader.Wu.Epoch.FilterSweepAmplification

/-!
# Exact reduction of epoch slots to a directed voter process

Subtracting the physical position from an epoch slot turns the local successor
rule into copying one color clockwise: edge `i → i+1` leaves color `i`
unchanged and writes it to `i+1`.  The integrated P_PLL core is irrelevant to
this projection because the epoch filter frames slots exactly.

This reduction isolates the quantitative scheduler problem.  A protected
rotation is precisely voter-color consensus together with endpoint cleanliness.
Thus the current random convergence analysis is a directed asynchronous voter
consensus problem, not an unspecified P_PLL probability phase.
-/

namespace PPLLEpochVoterReduction

open PPLLResearchFormulation PPLLProtectedEpochProtocol
  PPLLProtectedEpochSweep PPLLDerivedEpochRepair

/-! ## Modular color coordinate -/

/-- Epoch color (or anchor discrepancy) at position `i`: slot minus physical
position modulo `n`.  A protected rotation has one common color at every
position. -/
def epochColor (i : Fin n) (u : EpochAgentState n ψ κ) : Fin n :=
  u.slot - i

/-- Pointwise color projection of an epoch configuration. -/
def epochColorConfig (C : Fin n → EpochAgentState n ψ κ) : Fin n → Fin n :=
  fun i => epochColor i (C i)

private theorem mod_add_mod_left (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem mod_add_mod_right (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

/-- A slot satisfying the rotation formula has the advertised common color. -/
theorem epochColor_eq_of_rotation (anchor i : Fin n)
    (u : EpochAgentState n ψ κ)
    (hslot : u.slot.val = (anchor.val + i.val) % n) :
    epochColor i u = anchor := by
  apply Fin.ext
  simp only [epochColor, Fin.sub_def]
  rw [hslot, mod_add_mod_right]
  have heq : n - i.val + (anchor.val + i.val) = n + anchor.val := by
    omega
  rw [heq, add_self_mod, Nat.mod_eq_of_lt anchor.isLt]

/-- Conversely, a common color determines the slot rotation formula. -/
theorem slot_rotation_of_epochColor_eq (anchor i : Fin n)
    (u : EpochAgentState n ψ κ)
    (hcolor : epochColor i u = anchor) :
    u.slot.val = (anchor.val + i.val) % n := by
  have hv := congrArg Fin.val hcolor
  simp only [epochColor, Fin.sub_def] at hv
  have hv2 := congrArg (fun x : Nat => (x + i.val) % n) hv
  rw [mod_add_mod_left] at hv2
  have heq : n - i.val + u.slot.val + i.val = n + u.slot.val := by
    omega
  rw [heq, add_self_mod, Nat.mod_eq_of_lt u.slot.isLt] at hv2
  exact hv2

/-- Advancing both physical position and slot by one preserves epoch color,
including the modular wrap edge. -/
theorem epochColor_successor
    (hn : n > 0) (ring : DirectedRing n)
    (slot i : Fin n) :
    nextSlot hn slot - ring.rightNeighbor i = slot - i := by
  apply Fin.ext
  simp only [Fin.sub_def, nextSlot, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    by_cases hs : slot.val + 1 < n
    · rw [Nat.mod_eq_of_lt hs]
      have hsame : n - (i.val + 1) + (slot.val + 1) =
          n - i.val + slot.val := by omega
      rw [hsame]
    · have hse : slot.val + 1 = n := by omega
      rw [hse, Nat.mod_self]
      have hleft : n - (i.val + 1) + 0 = n - i.val - 1 := by omega
      have hright : n - i.val + slot.val =
          n + (n - i.val - 1) := by omega
      rw [hleft, hright, add_self_mod]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    by_cases hs : slot.val + 1 < n
    · rw [Nat.mod_eq_of_lt hs]
      have hleft : n - 0 + (slot.val + 1) = n + (slot.val + 1) := by
        omega
      have hright : n - i.val + slot.val = slot.val + 1 := by omega
      rw [hleft, hright, add_self_mod]
    · have hse : slot.val + 1 = n := by omega
      rw [hse, Nat.mod_self]
      have hleft : n - 0 + 0 = n := by omega
      have hright : n - i.val + slot.val = n := by omega
      rw [hleft, hright, Nat.mod_self]

/-! ## Directed voter semantics -/

/-- One clockwise voter update: the responder copies the initiator's color;
all other colors are unchanged. -/
def directedVoterStep (ring : DirectedRing n)
    (D : Fin n → Fin n) (e : Fin n) : Fin n → Fin n :=
  fun i => if i = e then D e
    else if i = ring.rightNeighbor e then D e else D i

/-- Execute a schedule in the directed voter projection. -/
def runDirectedVoterSchedule (ring : DirectedRing n)
    (D : Fin n → Fin n) : DetSchedule n → Fin n → Fin n
  | [] => D
  | e :: rest =>
      runDirectedVoterSchedule ring (directedVoterStep ring D e) rest

/-- One P_PLL-derived filtered step projects exactly to one directed voter
update, for every integrated core state and every edge. -/
theorem epochColorConfig_localStep
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (e : Fin n) :
    epochColorConfig
      (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) =
      directedVoterStep ring (epochColorConfig C) e := by
  funext i
  let j := ring.rightNeighbor e
  let q := ppllEpochFilterTransition hψ κ ring.hn (C e) (C j)
  have hq := ppllEpochFilter_local_contract hψ κ ring.hn (C e) (C j)
  change q.1.slot = (C e).slot ∧
    q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  change epochColor i
      (if i = e then q.1 else if i = j then q.2 else C i) =
    (if i = e then epochColorConfig C e
      else if i = j then epochColorConfig C e else epochColorConfig C i)
  by_cases hie : i = e
  · subst i
    simp only [if_pos]
    unfold epochColorConfig epochColor
    rw [hq.1]
  · by_cases hij : i = j
    · subst i
      rw [if_neg hie, if_pos rfl, if_neg hie, if_pos rfl]
      unfold epochColorConfig epochColor
      rw [hq.2.1, hq.1]
      exact epochColor_successor ring.hn ring (C e).slot e
    · simp [hie, hij, epochColorConfig]

/-- Whole filtered executions project exactly to directed voter executions on
the same scheduler word. -/
theorem epochColorConfig_runLocalSchedule
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (s : DetSchedule n) :
    epochColorConfig
      (runLocalSchedule ring (ppllEpochFilterTransition hψ κ ring.hn) C s) =
      runDirectedVoterSchedule ring (epochColorConfig C) s := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [runLocalSchedule, runDirectedVoterSchedule]
      rw [ih, epochColorConfig_localStep]

/-! ## Protected rotations are clean voter consensus -/

/-- Every position carries one common voter color. -/
def EpochColorConsensus (C : Fin n → EpochAgentState n ψ κ) : Prop :=
  ∃ anchor : Fin n, ∀ i, epochColorConfig C i = anchor

/-- The physical protected predicate is exactly color consensus plus endpoint
cleanliness.  Its explicit edge-coverage field follows algebraically from the
rotation and carries no extra convergence content. -/
theorem protectedEpoch_iff_colorConsensus_clean
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    ProtectedEpoch ring.hn ring C ↔
      EpochColorConsensus C ∧ ∀ i, EpochClean (C i) := by
  constructor
  · rintro ⟨anchor, hrot, hcovered, hclean⟩
    refine ⟨⟨anchor, ?_⟩, hclean⟩
    intro i
    exact epochColor_eq_of_rotation anchor i (C i) (hrot i)
  · rintro ⟨⟨anchor, hcolor⟩, hclean⟩
    have hrot : ∀ i, (C i).slot.val = (anchor.val + i.val) % n := by
      intro i
      exact slot_rotation_of_epochColor_eq anchor i (C i) (hcolor i)
    exact ⟨anchor, hrot,
      rotation_implies_covered ring.hn ring anchor C hrot, hclean⟩

end PPLLEpochVoterReduction
