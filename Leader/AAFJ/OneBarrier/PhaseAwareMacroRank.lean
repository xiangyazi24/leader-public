import Leader.AAFJ.OneBarrier.ModeComposition
import Leader.AAFJ.OneBarrier.DangerousProbeChase
import Leader.AAFJ.OneBarrier.MultipleLeaderProgress

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OriginalPhaseAwareMacroRank

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalUniqueLeaderCleanup
open OriginalMultipleLeaderOneBarrier
open OriginalOneBarrierComposition
open OriginalDangerousProbeChase
open CenteredRenewal.OneBarrierCleanup

abbrev hk2 : 0 < (2 : Nat) := by decide

def ring3 : DirectedRing 3 := ⟨by decide⟩

def q (bullet leader : Bool) (label : Fin 2) (probe phase : Bool) : State 2 :=
  { bullet := bullet, leader := leader, label := label, probe := probe, phase := phase }

/-! This is a safe unique state: there is no probe, and the sole leader is a
bullet-bearing responder of the first non-barrier edge in the accepted
non-ready cleanup word. -/
def SafeUnique (i : Fin 3) : State 2 :=
  if i = 0 then q false false 0 false false
  else if i = 1 then q true true 1 false false
  else q false false 0 false false

def SafeEndpoint : Fin 3 → State 2 :=
  rawRun hk2 ring3 SafeUnique [2, 0, 0, 2]

/-! The concrete safe branch loses the named unique leader.  This is the
physical endpoint behind terminalRank=0; it is not an outer Phi descent. -/
theorem safe_branch_mode_loss :
    OneBarrierAt hk2 ring3 SafeUnique 2 ∧
      UniqueLeaderAt SafeUnique 1 ∧
      ¬ Dangerous (cutView ring3 2 SafeUnique) ∧
      OneBarrierAt hk2 ring3 SafeEndpoint 0 ∧
      leaderCount SafeEndpoint = 0 ∧
      (∀ l : Fin 3, ¬ UniqueLeaderAt SafeEndpoint l) ∧
      terminalRank ring3 2 1 SafeUnique = 2 ∧
      terminalRank ring3 0 1 SafeEndpoint = 0 ∧
      PhiAt ring3 0 SafeEndpoint = PhiAt ring3 2 SafeUnique := by
  decide +kernel

/-! This is the literal word selected by the accepted non-ready unique
cleanup branch.  It witnesses the terminalRank endpoint rather than merely
unfolding the endpoint predicate. -/
theorem safe_cleanup_word_is_progress :
    ([2, 0, 0, 2] : List (Fin 3)).length ≤ 4 ∧
      OneBarrierAt hk2 ring3 SafeEndpoint 0 ∧
      (CleanAt hk2 ring3 SafeEndpoint 0 1 ∨
        terminalRank ring3 0 1 SafeEndpoint <
          terminalRank ring3 2 1 SafeUnique) := by
  decide +kernel

theorem safe_cleanup_selector_is_nonready :
    ¬ AdvanceReady hk2 ring3 SafeUnique 2 ∧
      (if AdvanceReady hk2 ring3 SafeUnique 2 then
          ([2] : List (Fin 3))
        else [2, 0, 0, 2]) = [2, 0, 0, 2] := by
  decide +kernel

/-! The same concrete word is literally an edge of the public composition
relation.  Its reduction disjunct is the terminalRank alternative; the
relation intentionally does not expose that the endpoint has zero leaders. -/
theorem safe_cleanup_is_mode_relation :
    OneBarrierMode SafeUnique ∧
      ∃ w b',
        w.length ≤ 8 * 3 ∧
          OneBarrierAt hk2 ring3 (rawRun hk2 ring3 SafeUnique w) b' ∧
          OneBarrierReduction hk2 ring3 2 SafeUnique b'
            (rawRun hk2 ring3 SafeUnique w) := by
  constructor
  · exact Or.inr (Or.inl ⟨1, by decide +kernel⟩)
  · refine ⟨[2, 0, 0, 2], 0, by decide, by decide +kernel, ?_⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨1, by decide +kernel⟩))))

/-! A payload tuple records the mode, cut potential, dangerousness, tail
phase/probe/bullet payload, and a responder-control debt.  The first
coordinate is deliberately mode-aware; the remaining coordinates are the
smallest concrete control fields exposed by the accepted transitions. -/
def bit (b : Bool) : Nat := if b then 1 else 0

def responderDebtAt (b : Fin 3) (C : Fin 3 → State 2) : Nat :=
  bit (C (ring3.rightNeighbor b)).leader +
    bit (C (ring3.rightNeighbor b)).bullet +
    bit (C (ring3.rightNeighbor b)).phase +
    bit (C (ring3.rightNeighbor b)).probe

def bulletDebtAt (C : Fin 3 → State 2) : Nat :=
  (List.ofFn (fun i : Fin 3 => bit (C i).bullet)).sum

/-! This is the proposed mode order after accounting for the concrete safe
unique-to-zero cleanup: Dangerous Unique = 2, Multiple/Zero = 1, and safe
Unique = 0.  The global bullet count comes before this phase coordinate. -/
def phaseModeRankAt (b : Fin 3) (C : Fin 3 → State 2) : Nat :=
  if leaderCount C = 1 then
    if Dangerous (cutView ring3 b C) then 2 else 0
  else 1

def phaseAwareTuple8At (b : Fin 3) (C : Fin 3 → State 2) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (PhiAt ring3 b C,
    bulletDebtAt C,
    phaseModeRankAt b C,
    dangerBit (cutView ring3 b C),
    bit (C b).phase,
    bit (C b).probe,
    bit (C b).bullet,
    responderDebtAt b C)

def phaseAwareTuple8 (C : Fin 3 → State 2) :=
  phaseAwareTuple8At (2 : Fin 3) C

def modeRankAt (b : Fin 3) (C : Fin 3 → State 2) : Nat :=
  if leaderCount C = 0 then 0
  else if leaderCount C = 1 then
    if Dangerous (cutView ring3 b C) then 3 else 1
  else 2

def phaseAwareTupleAt (b : Fin 3) (C : Fin 3 → State 2) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (modeRankAt b C,
    PhiAt ring3 b C,
    dangerBit (cutView ring3 b C),
    bit (C b).phase,
    bit (C b).probe,
    bit (C b).bullet,
    responderDebtAt b C)

def responderDebt (C : Fin 3 → State 2) : Nat :=
  responderDebtAt (2 : Fin 3) C

def modeRank (C : Fin 3 → State 2) : Nat :=
  modeRankAt (2 : Fin 3) C

def phaseAwareTuple (C : Fin 3 → State 2) :=
  phaseAwareTupleAt (2 : Fin 3) C

/-! Explicit lexicographic order for the displayed tuple. -/
def LexNat : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if a = b then LexNat as bs else false

def Lex7 (x y : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Prop :=
  LexNat
    [x.1, x.2.1, x.2.2.1, x.2.2.2.1,
      x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2]
    [y.1, y.2.1, y.2.2.1, y.2.2.2.1,
      y.2.2.2.2.1, y.2.2.2.2.2.1, y.2.2.2.2.2.2] = true

def tuple8List (x : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : List Nat :=
  [x.1, x.2.1, x.2.2.1, x.2.2.2.1,
    x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
    x.2.2.2.2.2.2.2]

def Lex8 (x y : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Prop :=
  LexNat (tuple8List x) (tuple8List y) = true

/-! Concrete dangerous/multiple/unique states from the accepted obstruction. -/
def U0 (i : Fin 3) : State 2 :=
  if i = 0 then q false false 0 false false
  else if i = 1 then q false true 1 true false
  else q true false 0 true false

def U1 : Fin 3 → State 2 :=
  (protocol 2 hk2).step ring3 U0 (2 : Fin 3)

def U2 : Fin 3 → State 2 :=
  (protocol 2 hk2).step ring3 U1 (1 : Fin 3)

/-! A concrete zero-leader birth word.  It is the source-level chase for the
quiet one-barrier state: arm at 2, carry the probe through 0 and 1, then hit
2 to create a leader. -/
def ZeroStart (i : Fin 3) : State 2 :=
  if i = 1 then q false false 1 false false
  else q false false 0 false false

def ZeroBirthWord : List (Fin 3) := [2, 0, 1, 2]

def ZeroBirthEnd : Fin 3 → State 2 :=
  rawRun hk2 ring3 ZeroStart ZeroBirthWord

theorem zero_birth_macro_is_phase_decrease :
    OneBarrierAt hk2 ring3 ZeroStart 2 ∧
      (∀ i : Fin 3, (ZeroStart i).leader = false) ∧
      OneBarrierAt hk2 ring3 ZeroBirthEnd 0 ∧
      (∃ ell : Fin 3, UniqueLeaderAt ZeroBirthEnd ell) ∧
      leaderCount ZeroBirthEnd = 1 ∧
      PhiAt ring3 (0 : Fin 3) ZeroBirthEnd = 1 ∧
      Lex8 (phaseAwareTuple8At (0 : Fin 3) ZeroBirthEnd)
        (phaseAwareTuple8At (2 : Fin 3) ZeroStart) := by
  constructor
  · decide +kernel
  constructor
  · intro i
    by_cases h0 : i = (0 : Fin 3)
    · subst i
      decide +kernel
    · by_cases h1 : i = (1 : Fin 3)
      · subst i
        decide +kernel
      · have h2 : i = (2 : Fin 3) := by
          apply Fin.ext
          omega
        subst i
        decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · unfold Lex8 tuple8List
    decide +kernel

def U1Sweep := parkedSweepWord ring3 (2 : Fin 3)
def U1S := rawRun hk2 ring3 U1 U1Sweep
def U1Discharge := endpointDischargeWord U1S (2 : Fin 3)
def U1MacroWord := U1Sweep ++ U1Discharge
def U1D := rawRun hk2 ring3 U1 U1MacroWord

/-! The accepted producers are tested at their actual word endpoints.  The
dangerous tail-hit instance uses the source `macroWord` at witness 2, hence
the one-letter word U0 --[2]--> U1.  The accepted
multiple producer uses parkedSweepWord followed by its literal endpoint
discharge word U1MacroWord, ending at U1D.  The raw U1--[1]-->U2 transition
below is only a negative diagnostic: it is not the multiple producer and must
not be smuggled into a macro-level rank proof. -/
theorem dangerous_tail_word_is_actual_macro :
    endpointDischargeWord U0 (2 : Fin 3) = [2] ∧
      rawRun hk2 ring3 U0 [2] = U1 ∧
      leaderCount U1 = 2 ∧
      PhiAt ring3 (2 : Fin 3) U1 = PhiAt ring3 (2 : Fin 3) U0 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · decide +kernel
  · decide +kernel

theorem dangerous_tail_macroWord_is_source_word :
    macroWord ring3 (2 : Fin 3) (2 : Fin 3) = [2] ∧
      macroBarrier hk2 ring3 U0 (2 : Fin 3) (2 : Fin 3) = 2 ∧
      rawRun hk2 ring3 U0
          (macroWord ring3 (2 : Fin 3) (2 : Fin 3)) = U1 := by
  constructor
  · rfl
  constructor
  · decide +kernel
  · rfl

theorem selected_fixture_input_modes :
    OneBarrierAt hk2 ring3 U0 2 ∧
      UniqueLeaderAt U0 1 ∧
      Dangerous (cutView ring3 2 U0) ∧
      OneBarrierAt hk2 ring3 U1 2 ∧
      leaderCount U1 = 2 ∧
      ¬ Dangerous (cutView ring3 2 U1) := by
  decide +kernel
theorem multiple_macro_U1_endpoint :
    OneBarrierAt hk2 ring3 U1D
      (endpointDischargeBarrier ring3 U1S (2 : Fin 3)) ∧
      (∃ ell : Fin 3, UniqueLeaderAt U1D ell) ∧
      ¬ Dangerous
        (cutView ring3 (endpointDischargeBarrier ring3 U1S (2 : Fin 3)) U1D) ∧
      PhiAt ring3 (endpointDischargeBarrier ring3 U1S (2 : Fin 3)) U1D ≤
        PhiAt ring3 (2 : Fin 3) U1 := by
  decide +kernel

theorem multiple_macro_U1_decreases :
    Lex7
      (phaseAwareTupleAt
        (endpointDischargeBarrier ring3 U1S (2 : Fin 3)) U1D)
      (phaseAwareTupleAt (2 : Fin 3) U1) := by
  unfold Lex7
  decide +kernel

theorem dangerous_tail_macro_decreases :
    Lex7 (phaseAwareTuple U1) (phaseAwareTuple U0) := by
  unfold Lex7
  decide +kernel

/-! The bullet-before-phase candidate orients all three concrete selected
macro tests available here.  In the safe cleanup test the mode coordinate
goes up (safe Unique to Zero), but bulletDebt goes down first. -/
theorem phase_rank_safe_cleanup_decreases :
    Lex8
      (phaseAwareTuple8At (0 : Fin 3) SafeEndpoint)
      (phaseAwareTuple8At (2 : Fin 3) SafeUnique) := by
  unfold Lex8 tuple8List
  decide +kernel

theorem phase_rank_dangerous_tail_decreases :
    Lex8 (phaseAwareTuple8 U1) (phaseAwareTuple8 U0) := by
  unfold Lex8 tuple8List
  decide +kernel

theorem phase_rank_multiple_macro_decreases :
    Lex8
      (phaseAwareTuple8At
        (endpointDischargeBarrier ring3 U1S (2 : Fin 3)) U1D)
      (phaseAwareTuple8 U1) := by
  unfold Lex8 tuple8List
  decide +kernel

theorem phase_rank_safe_cleanup_pays_with_bullets :
    bulletDebtAt SafeEndpoint < bulletDebtAt SafeUnique ∧
      phaseModeRankAt (0 : Fin 3) SafeEndpoint = 1 ∧
      phaseModeRankAt (2 : Fin 3) SafeUnique = 0 ∧
      PhiAt ring3 (0 : Fin 3) SafeEndpoint =
        PhiAt ring3 (2 : Fin 3) SafeUnique := by
  decide +kernel

theorem dangerous_payload_distinguishes_U0_U2 :
    phaseAwareTuple U0 ≠ phaseAwareTuple U2 := by
  decide +kernel

theorem raw_mode_switch_not_oriented_by_tuple :
    ¬ Lex7 (phaseAwareTuple U2) (phaseAwareTuple U1) := by
  unfold Lex7
  decide +kernel

/-! The requested endpoint strengthening is false at the public cleanup
interface: its terminalRank branch can be exactly the safe-to-zero endpoint
above.  It therefore cannot be relabelled as preservation of UniqueLeaderAt
or as strict Phi descent. -/
theorem safe_endpoint_disproves_same_unique_strengthening :
    ¬ UniqueLeaderAt SafeEndpoint 1 ∧
      ¬ (PhiAt ring3 0 SafeEndpoint < PhiAt ring3 2 SafeUnique) := by
  decide +kernel

#print axioms safe_branch_mode_loss
#print axioms safe_cleanup_word_is_progress
#print axioms safe_cleanup_selector_is_nonready
#print axioms safe_cleanup_is_mode_relation
#print axioms dangerous_tail_word_is_actual_macro
#print axioms dangerous_tail_macroWord_is_source_word
#print axioms selected_fixture_input_modes
#print axioms multiple_macro_U1_endpoint
#print axioms multiple_macro_U1_decreases
#print axioms zero_birth_macro_is_phase_decrease
#print axioms dangerous_tail_macro_decreases
#print axioms phase_rank_safe_cleanup_decreases
#print axioms phase_rank_dangerous_tail_decreases
#print axioms phase_rank_multiple_macro_decreases
#print axioms phase_rank_safe_cleanup_pays_with_bullets
#print axioms dangerous_payload_distinguishes_U0_U2
#print axioms raw_mode_switch_not_oriented_by_tuple
#print axioms safe_endpoint_disproves_same_unique_strengthening

end AAFJPK.OriginalPhaseAwareMacroRank
