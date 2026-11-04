import Leader.Wu.Birth.ShortDoneStateBound
import Leader.Wu.Birth.ShortDoneTerminalLoadBound
import Leader.Wu.Birth.WaitClockMassDirtyMass
import Leader.Wu.Birth.ShortWaitTerminalEntryMass
import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleRotation
import Leader.Wu.Birth.CheckParametricWait

set_option autoImplicit false

namespace Q11497FeasibilityAudit

/-- The exact iterated-log scale used by the checked short-DONE state consumer. -/
def scale (n : Nat) : Nat :=
  BirthShortDoneDispatcher.loglogScale n

/-- A size-safe version of the intended iterated-log width parameter.
The `min` is only needed to make the old WAIT theorem's `psi < n` premise
literal at every finite `n` in the range considered below. -/
def psiChoice (n : Nat) : Nat :=
  Nat.min (scale n + 1) (n - 1)

/-- The repaired WAIT proof width. -/
def widthChoice : Nat := 2

/-- A WAIT cap with a fixed linear iterated-log envelope. -/
def kappaChoice (n : Nat) : Nat := scale n + 1

/-- A finite expiry budget that also dominates the checked constant-16 witness. -/
def tauChoice (n : Nat) : Nat := 16 * (scale n + 1)

private theorem scale_ge_one (n : Nat) : 1 <= scale n := by
  unfold scale BirthShortDoneDispatcher.loglogScale
  omega

private theorem psi_two_le (n : Nat) (hn : 3 <= n) :
    2 <= psiChoice n := by
  unfold psiChoice
  apply Nat.le_min.mpr
  constructor
  · have hs := scale_ge_one n
    omega
  · omega

private theorem psi_pos (n : Nat) (hn : 3 <= n) :
    0 < psiChoice n := by
  have h := psi_two_le n hn
  omega

private theorem psi_lt_n (n : Nat) (hn : 3 <= n) :
    psiChoice n < n := by
  have hle : psiChoice n <= n - 1 := by
    unfold psiChoice
    exact Nat.min_le_right _ _
  omega

private theorem width_pos : 0 < widthChoice := by
  unfold widthChoice
  omega

private theorem width_le_psi (n : Nat) (hn : 3 <= n) :
    widthChoice <= psiChoice n := by
  have h := psi_two_le n hn
  simpa [widthChoice] using h

private theorem psi_le_kappa_succ (n : Nat) :
    psiChoice n <= kappaChoice n + 1 := by
  have hle : psiChoice n <= scale n + 1 := by
    unfold psiChoice
    exact Nat.min_le_left _ _
  unfold kappaChoice
  omega

private theorem kappa_pos (n : Nat) : 0 < kappaChoice n := by
  have hs := scale_ge_one n
  unfold kappaChoice
  omega

private theorem kappa_poly (n : Nat) :
    kappaChoice n + 1 <= 3 * scale n := by
  have hs := scale_ge_one n
  unfold kappaChoice
  omega

private theorem tau_ge_sixteen (n : Nat) : 16 <= tauChoice n := by
  have hs := scale_ge_one n
  unfold tauChoice
  omega

private theorem tau_poly (n : Nat) :
    tauChoice n + 1 <= 33 * scale n := by
  have hs := scale_ge_one n
  unfold tauChoice
  omega

/-- The elementary order contradiction used by the two literal small-ring
incompatibility receipts below. -/
private theorem lower_upper_contradiction {a b : Nat}
    (hlo : a <= b) (hhi : b < a) : False := by
  exact (Nat.not_lt_of_ge hlo) hhi

private theorem three_lt_four : (3 : Nat) < 4 := by
  exact Nat.lt_succ_self 3

/-- From the first ring size accepted by the checked Local3 timing theorem,
all pure numeric state/WAIT/constant-expiry inequalities are simultaneous.
This deliberately does not claim the caller-supplied terminal `hscale`. -/
theorem pure_parameter_conjunction (n : Nat) (hn : 4 <= n) :
    2 <= psiChoice n /\
    0 < psiChoice n /\
    0 < widthChoice /\
    widthChoice <= psiChoice n /\
    psiChoice n < n /\
    psiChoice n <= kappaChoice n + 1 /\
    0 < kappaChoice n /\
    16 <= tauChoice n /\
    kappaChoice n + 1 <= 3 * scale n /\
    tauChoice n + 1 <= 33 * scale n := by
  have hn3 : 3 <= n := by omega
  exact
    ⟨psi_two_le n hn3,
      psi_pos n hn3,
      width_pos,
      width_le_psi n hn3,
      psi_lt_n n hn3,
      psi_le_kappa_succ n,
      kappa_pos n,
      tau_ge_sixteen n,
      kappa_poly n,
      tau_poly n⟩

/-- Direct instantiation of the checked actual expiring short-DONE certificate
with fixed constants A=3, a=1, B=33, b=1. -/
theorem state_bound_candidate (n : Nat) (hn : 4 <= n) :
    (BirthShortDoneDispatcher.stateCertificate
      (psi_pos n (by omega : 3 <= n))
      width_pos
      (width_le_psi n (by omega : 3 <= n))
      (kappaChoice n) (tauChoice n)).values.length <=
      2 * 61931520000000 *
        (3 * scale n) ^ 8 *
        (33 * scale n) := by
  have hn3 : 3 <= n := by omega
  have hk :
      kappaChoice n + 1 <= 3 * (scale n) ^ 1 := by
    simpa [Nat.pow_one] using kappa_poly n
  have ht :
      tauChoice n + 1 <= 33 * (scale n) ^ 1 := by
    simpa [Nat.pow_one] using tau_poly n
  simpa [scale, Nat.pow_one] using
    (BirthShortDoneDispatcher.finite_state_bound_polyloglog
      (ψ := psiChoice n) (width := widthChoice)
      (κ := kappaChoice n) (τ := tauChoice n) (n := n)
      (psi_pos n hn3) width_pos (width_le_psi n hn3)
      (psi_le_kappa_succ n)
      3 1 33 1 hk ht)

/-- The first literal incompatibility: both WAIT mass interfaces require this
pair when n=2.  It is independent of every state-count parameter. -/
theorem wait_n2_hypotheses_impossible (width : Nat) :
    not (2 <= width /\ width < 2) := by
  have hfalse : decide (2 <= width /\ width < 2) = false := by
    simp only [decide_eq_false_iff_not]
    intro h
    exact lower_upper_contradiction h.1 h.2
  simp [hfalse]

/-- The checked Local3 1/16 timing consumer has the stricter small-ring
boundary `4 <= n`, so its hypotheses cannot hold at n=3. -/
theorem local3_n3_hypothesis_impossible :
    not (4 <= (3 : Nat)) := by
  have hfalse : decide (4 <= (3 : Nat)) = false := by
    simp only [decide_eq_false_iff_not]
    intro h
    exact lower_upper_contradiction h three_lt_four
  simp [hfalse]

/-- Closed arithmetic receipt for the n=3 candidate.  It clears the WAIT/state
numeric conditions, but not the separate Local3 `4 <= n` premise. -/
theorem n3_parameters :
    scale 3 = 1 /\
    psiChoice 3 = 2 /\
    kappaChoice 3 = 2 /\
    tauChoice 3 = 32 /\
    2 <= psiChoice 3 /\
    psiChoice 3 < 3 := by
  decide

/-- Closed arithmetic receipt for the first Local3-admissible size. -/
theorem n4_parameters :
    scale 4 = 2 /\
    psiChoice 4 = 3 /\
    kappaChoice 4 = 3 /\
    tauChoice 4 = 48 /\
    2 <= psiChoice 4 /\
    psiChoice 4 < 4 := by
  decide

end Q11497FeasibilityAudit

#print axioms Q11497FeasibilityAudit.pure_parameter_conjunction
#print axioms Q11497FeasibilityAudit.state_bound_candidate
#print axioms Q11497FeasibilityAudit.wait_n2_hypotheses_impossible
#print axioms Q11497FeasibilityAudit.local3_n3_hypothesis_impossible
#print axioms Q11497FeasibilityAudit.n3_parameters
#print axioms Q11497FeasibilityAudit.n4_parameters
