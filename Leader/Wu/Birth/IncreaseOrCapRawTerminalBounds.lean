import Leader.Wu.Birth.WaitClockMassDirtyMass

namespace BirthPhaseB3RawTerminalBounds

open PPLL PPLLRepair
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing

set_option autoImplicit false
set_option Elab.async false

private theorem twoPos : 0 < 2 := by decide

/-- Canonical width-two service edge. -/
def p0 {n : Nat} (hfit : 2 < n) : Fin n :=
  port hfit (0 : Fin 1)

/-- Canonical width-two tracked terminal. -/
def p1 {n : Nat} (hfit : 2 < n) : Fin n :=
  site hfit (1 : Fin 2)

/-- The canonical service edge really has the terminal as responder. -/
theorem right_p0 {n : Nat} (hfit : 2 < n) :
    (ring hfit).rightNeighbor (p0 hfit) = p1 hfit := by
  unfold p0
  rw [right_port hfit (0 : Fin 1)]
  apply Fin.ext
  rfl

private theorem prepare_left_count_frame (l r : AgentState 2) :
    (waitSaturatedPrepare twoPos l r).1.count = l.count := by
  simp [waitSaturatedPrepare]

private theorem prepare_right_count_frame (l r : AgentState 2) :
    (waitSaturatedPrepare twoPos l r).2.count = r.count := by
  simp [waitSaturatedPrepare]

private theorem carry_left_count_frame (cap : Nat) (l r : AgentState 2) :
    (waitSaturatedCarry twoPos cap l r).1.count = l.count := by
  simp [waitSaturatedCarry]

private theorem wait_left_count_frame (cap : Nat) (l r : AgentState 2) :
    (waitSaturated twoPos cap l r).1.count = l.count := by
  unfold waitSaturated
  rw [(BirthWaitClockAudit.finish_count_frame twoPos cap _ _).1,
    (BirthWaitClockAudit.reset_count_frame twoPos _ _).1,
    carry_left_count_frame cap _ _, prepare_left_count_frame l r]

private theorem wait_right_count_bounds
    (cap : Nat) (l r : AgentState 2) (hc : r.count <= cap) :
    r.count <= (waitSaturated twoPos cap l r).2.count /\
      (waitSaturated twoPos cap l r).2.count <= r.count + 1 /\
      (waitSaturated twoPos cap l r).2.count <= cap := by
  rw [BirthWaitClockAudit.prepared_count_row twoPos cap l r,
    prepare_right_count_frame l r]
  split
  · exact ⟨Nat.le_min.mpr ⟨by omega, hc⟩,
      Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  · exact ⟨Nat.le_refl _, by omega, hc⟩

private theorem edge_of_right_eq_p1 {n : Nat}
    (hfit : 2 < n) (e : Fin n)
    (hr : p1 hfit = (ring hfit).rightNeighbor e) :
    e = p0 hfit := by
  have hv := congrArg Fin.val hr
  change 1 = (e.val + 1) % n at hv
  have he := e.isLt
  have hlt : e.val + 1 < n := by
    refine Classical.byContradiction (fun h => ?_)
    have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega
  rw [Nat.mod_eq_of_lt hlt] at hv
  apply Fin.ext
  change e.val = 0
  omega

/-- Public width-two version of the private one-step terminal bound.
The extra two clauses record the one-unit bound and the only strict row. -/
theorem rawStep_terminal_bounds {n : Nat}
    (hfit : 2 < n) (cap : Nat)
    (C : Fin n -> AgentState 2) (e : Fin n)
    (hc : (C (p1 hfit)).count <= cap) :
    (C (p1 hfit)).count <=
        (rawStep hfit (by decide : 2 <= 2) cap C e (p1 hfit)).count /\
      (rawStep hfit (by decide : 2 <= 2) cap C e (p1 hfit)).count <=
        (C (p1 hfit)).count + 1 /\
      (rawStep hfit (by decide : 2 <= 2) cap C e (p1 hfit)).count <= cap /\
      ((C (p1 hfit)).count <
          (rawStep hfit (by decide : 2 <= 2) cap C e (p1 hfit)).count ->
        e = p0 hfit) := by
  have hn : 1 < n := by omega
  have hne : (ring hfit).rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt (ring hfit) hn e
  by_cases hi : p1 hfit = e
  · subst e
    rw [rawStep_initiator hfit (by decide : 2 <= 2) cap C (p1 hfit),
      wait_left_count_frame cap]
    omega
  · by_cases hr : p1 hfit = (ring hfit).rightNeighbor e
    · have hcR : (C ((ring hfit).rightNeighbor e)).count <= cap := by
        rw [<- hr]
        exact hc
      have hb := wait_right_count_bounds cap
        (C e) (C ((ring hfit).rightNeighbor e)) hcR
      rw [hr]
      unfold rawStep
      rw [updatePair_responder C e ((ring hfit).rightNeighbor e) _ hne]
      exact ⟨hb.1, hb.2.1, hb.2.2,
        fun _ => edge_of_right_eq_p1 hfit e hr⟩
    · unfold rawStep
      rw [updatePair_other C e ((ring hfit).rightNeighbor e)
        (p1 hfit) _ hi hr]
      omega

/-- A strict terminal increase is exactly on the canonical responder edge. -/
theorem rawStep_terminal_strict_only_p0 {n : Nat}
    (hfit : 2 < n) (cap : Nat)
    (C : Fin n -> AgentState 2) (e : Fin n)
    (hc : (C (p1 hfit)).count <= cap)
    (hinc : (C (p1 hfit)).count <
      (rawStep hfit (by decide : 2 <= 2) cap C e (p1 hfit)).count) :
    e = p0 hfit /\ (ring hfit).rightNeighbor e = p1 hfit := by
  have he := (rawStep_terminal_bounds hfit cap C e hc).2.2.2 hinc
  subst e
  exact ⟨rfl, right_p0 hfit⟩

/-- Public run version.  Induction accumulates the one-unit bound. -/
theorem rawRun_terminal_bounds {n : Nat}
    (hfit : 2 < n) (cap : Nat)
    (C : Fin n -> AgentState 2) (es : List (Fin n))
    (hc : (C (p1 hfit)).count <= cap) :
    (C (p1 hfit)).count <=
        (rawRun hfit (by decide : 2 <= 2) cap C es (p1 hfit)).count /\
      (rawRun hfit (by decide : 2 <= 2) cap C es (p1 hfit)).count <=
        (C (p1 hfit)).count + es.length /\
      (rawRun hfit (by decide : 2 <= 2) cap C es (p1 hfit)).count <= cap := by
  induction es generalizing C with
  | nil => simp [rawRun, hc]
  | cons e es ih =>
      have hs := rawStep_terminal_bounds hfit cap C e hc
      have ht := ih
        (rawStep hfit (by decide : 2 <= 2) cap C e) hs.2.2.1
      have hlen :
          (rawRun hfit (by decide : 2 <= 2) cap
            (rawStep hfit (by decide : 2 <= 2) cap C e) es (p1 hfit)).count <=
            (C (p1 hfit)).count + (e :: es).length := by
        simp only [List.length_cons]
        omega
      simpa only [rawRun] using
        ⟨Nat.le_trans hs.1 ht.1, hlen, ht.2.2⟩

end BirthPhaseB3RawTerminalBounds

#print axioms BirthPhaseB3RawTerminalBounds.right_p0
#print axioms BirthPhaseB3RawTerminalBounds.rawStep_terminal_bounds
#print axioms BirthPhaseB3RawTerminalBounds.rawStep_terminal_strict_only_p0
#print axioms BirthPhaseB3RawTerminalBounds.rawRun_terminal_bounds
