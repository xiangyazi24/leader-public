import Leader.L3.StateCount
import Leader.L3.Closure
import Leader.L3.SerClockCost
import Leader.L3.ProbStages

/-!
# Stage-wise assembly of the linear-lease headline

Source: research/paper/l3/appendices/renewal.tex, thm:linear-lease,
lines 1511-1528 and 1804-1823, using the adapted-cut sequence
of thm:main at lines 1004-1194 and the F.10/F.36 ledgers.

This is a conditional theorem. The paper's reference process is
coupled through a fresh-origin renewal, not an ordinary physical
Markov stage; that coupling remains a separate named obligation.
The S1 serializer clock is *inside* the rooted reference budget.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Exact finite-slice and conservative spatial stage ledgers -/

/-- F.9-F.10, tables at renewal.tex:552-600. Each row is
    (permit, rooted renewal, checker). The separate reserve is 4.
    These are the selected EXEC9 finite advice rows. -/
def headlineFiniteLedger : Nat → Nat × Nat × Nat
  | 3 => (41946, 16357, 5963)
  | 4 => (51784, 13603, 5963)
  | 5 => (116107, 35842, 6093)
  | 6 => (61625, 56049, 6093)
  | 7 => (63536, 25963, 6093)
  | 8 => (64525, 17821, 6093)
  | 9 => (65028, 14496, 6093)
  | 10 => (65281, 12922, 6093)
  | 11 => (65409, 12125, 6093)
  | 12 => (32737, 41081, 6093)
  | 13 => (32753, 38542, 6093)
  | 14 => (32761, 37275, 6093)
  | 15 => (32765, 36637, 6093)
  | 16 => (32767, 36281, 6093)
  | 17 => (65535, 20611, 1154)
  | 18 => (65536, 17175, 1154)
  | 19 => (65536, 15600, 1154)
  | 20 => (65536, 14826, 1154)
  | 21 => (65536, 14432, 1154)
  | 22 => (65536, 14232, 1154)
  | 23 => (65536, 14127, 1154)
  | 24 => (65536, 14072, 1154)
  | 25 => (65536, 14044, 1154)
  | 26 => (65536, 14027, 1154)
  | 27 => (65536, 14020, 1154)
  | 28 => (65536, 14017, 1154)
  | 29 => (65536, 14013, 1154)
  | 30 => (65536, 14013, 1154)
  | 31 => (65536, 14013, 1154)
  | 32 => (65536, 14013, 1154)
  | _ => (0, 0, 0)

/-- F.7, F.12-F.14: the selected reference mean ceiling for
    each finite advice slice, BEFORE the fresh-origin renewal. -/
def headlineFiniteReference : Nat → Nat
  | 3 => 8185
  | 4 => 7432
  | 5 => 17118
  | 6 => 12678
  | 7 => 10045
  | 8 => 8536
  | 9 => 7691
  | 10 => 7224
  | 11 => 6968
  | 12 => 6830
  | 13 => 6756
  | 14 => 6716
  | 15 => 6695
  | 16 => 6683
  | 17 => 9128
  | 18 => 8385
  | 19 => 7991
  | 20 => 7783
  | 21 => 7673
  | 22 => 7616
  | 23 => 7586
  | 24 => 7570
  | 25 => 7562
  | 26 => 7557
  | 27 => 7555
  | 28 => 7554
  | 29 => 7553
  | 30 => 7553
  | 31 => 7553
  | 32 => 7553
  | _ => 0

/-- F.34-F.36, renewal.tex:1646-1724. The rows s=6..16
    contain the published permit (including its 192 reserve
    for s>=7), rooted renewal, and checker 2^20. -/
def headlineLargeTable : Nat → Nat × Nat × Nat
  | 6 => (1048576, 225163, 1048576)
  | 7 => (6996623552, 2257676, 1048576)
  | 8 => (7720796352, 2458208, 1048576)
  | 9 => (8480620736, 2695495, 1048576)
  | 10 => (9276096704, 2980660, 1048576)
  | 11 => (10107224256, 3329821, 1048576)
  | 12 => (10974003392, 3767242, 1048576)
  | 13 => (11876434112, 4331232, 1048576)
  | 14 => (12814516416, 5086016, 1048576)
  | 15 => (13788250304, 6148120, 1048576)
  | 16 => (14797635776, 7753219, 1048576)
  | _ => (0, 0, 0)

/-- For s>=17, F.37 replaces the discontinuous power-of-two
    permit by 192+34(8s+101)(s+13)(A+1), and the renewal
    by 3A(A+1), A=557s+119981. Those upper rates are
    intentionally conservative, not exact C_lin(s) values. -/
def headlineLargeLedger (s : Nat) : Nat × Nat × Nat :=
  if s ≤ 16 then headlineLargeTable s
  else
    (192 + 34 * (8 * s + 101) * (s + 13) * (557 * s + 119982),
     3 * (557 * s + 119981) * (557 * s + 119982),
     1048576)

/-- F.10 for q<=32, and F.36/F.37 for psi>=6. -/
def headlineSelectedLedger (n : Nat) : Nat × Nat × Nat :=
  if ceilLogTwo n ≤ 32 then headlineFiniteLedger (ceilLogTwo n)
  else headlineLargeLedger (ceilLogTwo (ceilLogTwo n))

def headlinePermitRate (n : Nat) : Nat :=
  (headlineSelectedLedger n).1

def headlineRenewalRate (n : Nat) : Nat :=
  (headlineSelectedLedger n).2.1

def headlineCheckerRate (n : Nat) : Nat :=
  (headlineSelectedLedger n).2.2

/-- F.10/F.36: two purification units, one request reserve and
    one rendezvous unit, in addition to permit, renewal, checker. -/
def headlineStageRate (n : Nat) : Nat :=
  headlinePermitRate n + headlineRenewalRate n +
    headlineCheckerRate n + 4

def headlineStageCost (n : Nat) : Nat :=
  headlineStageRate n * n ^ 2

def headlineFiniteRate (q : Nat) : Nat :=
  (headlineFiniteLedger q).1 + (headlineFiniteLedger q).2.1 +
    (headlineFiniteLedger q).2.2 + 4

def headlineLargeRate (s : Nat) : Nat :=
  (headlineLargeLedger s).1 + (headlineLargeLedger s).2.1 +
    (headlineLargeLedger s).2.2 + 4

/-- F.14, renewal.tex:623-629: unique maximum C_5=158046.
    All 30 values are kernel-decided, not a floating calculation. -/
theorem headlineFiniteRate_bound (q : Nat)
    (hthree : 3 ≤ q) (hmax : q ≤ 32) :
    headlineFiniteRate q ≤ 158046 := by
  have hfinite :
      ∀ i : Fin 33, 3 ≤ i.val →
        headlineFiniteRate i.val ≤ 158046 := by decide
  exact hfinite ⟨q, by omega⟩ hthree

/-- F.39, renewal.tex:1781-1793, for the exact small widths 6..16.
    The s=7 integer margin is 129, so no additional stage is
    charged outside this ledger. -/
theorem headlineLargeRate_small (s : Nat)
    (hsix : 6 ≤ s) (hmax : s ≤ 16) :
    headlineLargeRate s ≤ 20407959 * s ^ 3 := by
  have hfinite :
      ∀ i : Fin 17, 6 ≤ i.val →
        headlineLargeRate i.val ≤ 20407959 * i.val ^ 3 := by decide
  exact hfinite ⟨s, by omega⟩ hsix

/-- Only linear integer arithmetic is exposed to omega here.
    The huge constant is separated from nonlinear s-expressions. -/
private theorem headlineLargeConstantBound
    (t : Nat) (ht : 4913 ≤ t) :
    192 + 1048576 + 4 ≤ 1000 * t := by
  omega

/-- Abstract Presburger bridge for the three pieces of the cubic
    bound. The inputs A and B are already bounded by their own
    Nat.mul_le_mul certificates; this lemma never unfolds them. -/
private theorem headlineLargeLinearBridge
    (A B t : Nat)
    (hA : A ≤ 7616000 * t)
    (hB : B ≤ 12000000 * t)
    (hconstant : 192 + 1048576 + 4 ≤ 1000 * t) :
    192 + A + B + 1048576 + 4 ≤ 20407959 * t := by
  omega

/-- F.37-F.39, s>=17: a deliberately looser integer-only
    polynomial majorant. Its coefficient 19617000 is below
    20407959, avoiding any false monotonicity assertion
    about the piecewise threshold pin. -/
theorem headlineLargeRate_tail (s : Nat) (hs : 17 ≤ s) :
    headlineLargeRate s ≤ 20407959 * s ^ 3 := by
  have hf : 8 * s + 101 ≤ 14 * s := by omega
  have hw : s + 13 ≤ 2 * s := by omega
  have ha : 557 * s + 119982 ≤ 8000 * s := by omega
  have hb : 557 * s + 119981 ≤ 8000 * s := by omega
  have hpermit :
      34 * (8 * s + 101) * (s + 13) *
          (557 * s + 119982) ≤ 7616000 * s ^ 3 := by
    calc
      34 * (8 * s + 101) * (s + 13) *
          (557 * s + 119982) ≤
        34 * (14 * s) * (2 * s) * (8000 * s) :=
          Nat.mul_le_mul (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.le_refl 34) hf) hw) ha
      _ = (34 * 14 * 2 * 8000) * s ^ 3 := by
        rw [show s ^ 3 = s * s * s from by
          simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]]
        ac_rfl
      _ = 7616000 * s ^ 3 := by
        have hnum : 34 * 14 * 2 * 8000 = 7616000 := by omega
        rw [hnum]
  have hrenew :
      3 * (557 * s + 119981) * (557 * s + 119982) ≤
        12000000 * s ^ 3 := by
    calc
      3 * (557 * s + 119981) * (557 * s + 119982) ≤
        3 * (8000 * s) * (8000 * s) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 3) hb) ha
      _ = 192000000 * (s * s) := by
        have hnum : 3 * 8000 * 8000 = 192000000 := by omega
        calc
          3 * (8000 * s) * (8000 * s) =
              (3 * 8000 * 8000) * (s * s) := by ac_rfl
          _ = 192000000 * (s * s) := by rw [hnum]
      _ ≤ 12000000 * s ^ 3 := by
        have h16 : 16 ≤ s := by omega
        have hmul : 16 * (s * s) ≤ s * (s * s) :=
          Nat.mul_le_mul_right (s * s) h16
        calc
          192000000 * (s * s) =
              12000000 * (16 * (s * s)) := by
                have hnum : 12000000 * 16 = 192000000 := by omega
                rw [← hnum, Nat.mul_assoc]
          _ ≤ 12000000 * (s * (s * s)) :=
            Nat.mul_le_mul_left 12000000 hmul
          _ = 12000000 * s ^ 3 := by
            simp [Nat.pow_succ, Nat.mul_assoc]
  have hcube : 4913 ≤ s ^ 3 := by
    have hmul : (17 * 17) * 17 ≤ (s * s) * s :=
      Nat.mul_le_mul
        (Nat.mul_le_mul hs hs) hs
    have hnum : 17 * 17 * 17 = 4913 := by omega
    have hpow : s ^ 3 = (s * s) * s := by
      simp [Nat.pow_succ, Nat.mul_assoc]
    simpa only [hnum, hpow] using hmul
  have hconstant : 192 + 1048576 + 4 ≤ 1000 * s ^ 3 :=
    headlineLargeConstantBound (s ^ 3) hcube
  have hlarge : ¬ s ≤ 16 := by omega
  calc
    headlineLargeRate s =
      192 + 34 * (8 * s + 101) * (s + 13) *
          (557 * s + 119982) +
        3 * (557 * s + 119981) * (557 * s + 119982) +
        1048576 + 4 := by
          simp [headlineLargeRate, headlineLargeLedger, hlarge]
    _ ≤ 20407959 * s ^ 3 :=
      headlineLargeLinearBridge
        (34 * (8 * s + 101) * (s + 13) *
          (557 * s + 119982))
        (3 * (557 * s + 119981) * (557 * s + 119982))
        (s ^ 3) hpermit hrenew hconstant

theorem headlineLargeRate_bound (s : Nat) (hs : 6 ≤ s) :
    headlineLargeRate s ≤ 20407959 * s ^ 3 := by
  by_cases h : s ≤ 16
  · exact headlineLargeRate_small s hs h
  · exact headlineLargeRate_tail s (by omega)

/-- F.14 and F.39: the actual additive stage ledger fits the
    selected linear-lease bound, in both advice regimes. -/
theorem headlineStageCost_le_linearLeaseBound
    (n : Nat) (hn : 5 ≤ n) :
    headlineStageCost n ≤ linearLeaseBound n := by
  have hthree : 3 ≤ ceilLogTwo n :=
    ceilLogTwo_ge_three n hn
  unfold headlineStageCost linearLeaseBound
  by_cases hf : ceilLogTwo n ≤ 32
  · rw [if_pos hf]
    have hh := headlineFiniteRate_bound (ceilLogTwo n) hthree hf
    have heq : headlineStageRate n =
        headlineFiniteRate (ceilLogTwo n) := by
      simp [headlineStageRate, headlinePermitRate,
        headlineRenewalRate, headlineCheckerRate,
        headlineSelectedLedger, headlineFiniteRate, hf]
    change headlineStageRate n * n ^ 2 ≤
      158046 * n ^ 2
    rw [heq]
    exact Nat.mul_le_mul_right (n ^ 2) hh
  · rw [if_neg hf]
    have hs : 6 ≤ ceilLogTwo (ceilLogTwo n) :=
      ceilLogTwo_ge_six (ceilLogTwo n) (by omega)
    have hh := headlineLargeRate_bound
      (ceilLogTwo (ceilLogTwo n)) hs
    have heq : headlineStageRate n =
        headlineLargeRate (ceilLogTwo (ceilLogTwo n)) := by
      simp [headlineStageRate, headlinePermitRate,
        headlineRenewalRate, headlineCheckerRate,
        headlineSelectedLedger, headlineLargeRate, hf]
    change headlineStageRate n * n ^ 2 ≤
      20407959 * ceilLogTwo (ceilLogTwo n) ^ 3 * n ^ 2
    rw [heq]
    exact Nat.mul_le_mul_right (n ^ 2) hh

/-! ## Actual physical stage predicates -/

abbrev HeadlineConfiguration (n : Nat) :=
  (protocol (ceilLogTwo n)).Configuration n

/-- All stage time is charged on the same selected physical service. -/
def headlinePhysicalNext {n : Nat} (ring : DirectedRing n) :
    HeadlineConfiguration n → Fin n → HeadlineConfiguration n :=
  fun C e => (protocol (ceilLogTwo n)).step ring C e

/-- The currently fixed target in Closure.lean:2942-2947.
    It retains its concrete readerFoldValid receipt predicate. -/
def headlineGeneratedTarget {n : Nat} (ring : DirectedRing n) :
    HeadlineConfiguration n → Prop :=
  Closure.targetSet (q := ceilLogTwo n) ring

/-- renewal.tex:1006-1014: native-peaceful purified,
    with every surviving native leader protected. This is
    a physical condition, not a ghost inherited-history label. -/
def headlinePurified {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Prop :=
  P ring (nativeProjection C) ∧
  ((∃ i : Fin n, (C i).l = true) →
    Protected ring (nativeProjection C))

/-- renewal.tex:1019-1034: a physical grant is available,
    or a protected rooted state makes first birth unnecessary. -/
def headlineGrantReady {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Prop :=
  (∃ i : Fin n, (C i).l = true ∧
    Protected ring (nativeProjection C)) ∨
  (headlinePurified ring C ∧
    ∃ i : Fin n, (C i).grant = true)

/-- renewal.tex:1030-1035: physical grant plus request,
    unless the protected root is already present. -/
def headlineRequestReady {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Prop :=
  (∃ i : Fin n, (C i).l = true ∧
    Protected ring (nativeProjection C)) ∨
  (headlinePurified ring C ∧
    (∃ i : Fin n, (C i).grant = true) ∧
    (∃ j : Fin n, (C j).req = true))

/-- renewal.tex:1035-1045,1058: protected rooted cut sigma_0. -/
def headlineRooted {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) : Prop :=
  Protected ring (nativeProjection C) ∧
    ∃ i : Fin n, (C i).l = true

/-- renewal.tex:1006-1014, charge 2n^2 for the true
    purification entrance from arbitrary Cartesian states. -/
def StageNativePurification {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlinePurified ring D ∨ headlineGeneratedTarget ring D)
      C ((2 * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1019-1029; F.9/F.36 physical permit clock
    from the purified leaderless case (zero if inherited). -/
def StageFirstGrant {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlinePurified ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
      C ((headlinePermitRate n * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1030-1032,1040-1046; the checker allowance
    plus the n/2 request remainder rounded into one n^2 unit. -/
def StageRequestChecker {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineGrantReady ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineRequestReady ring D ∨ headlineGeneratedTarget ring D)
      C (((headlineCheckerRate n + 1) * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1032-1040, the n^2 physical request/grant
    rendezvous yielding a protected rooted sigma_0 cut. -/
def StageFirstProtectedBirth {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineRequestReady ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineRooted ring D ∨ headlineGeneratedTarget ring D)
      C ((n ^ 2 : Nat) : Rat)

/-- renewal.tex:65-108,234-302,1172-1194. F.3/F.10/F.36:
    restartable REAL rooted renewal including repeated fresh
    divergences. This is NOT obtained just by adding reference
    sigma_B,... stages on the real process. -/
def StageRootedRenewal {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineRooted ring C →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (headlineGeneratedTarget ring) C
      ((headlineRenewalRate n * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1223-1235 and 1864-1874: generated target
    is closed on every actual physical service, not only no-fire. -/
def StageGeneratedClosure {n : Nat} (ring : DirectedRing n) : Prop :=
  PopulationProtocol.ClosedPred
    (protocol (ceilLogTwo n)) ring (headlineGeneratedTarget ring)

/-- renewal.tex:1223-1235: generated target is permanently safe
    at its physical leader site under all reachable edge words. -/
def StageGeneratedSafety {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n,
    headlineGeneratedTarget ring C →
    PopulationProtocol.IsSafe
      (protocol (ceilLogTwo n)) ring C (fun b => b)

/-! ## The reference's internal cuts are in its decorated state -/

/-- renewal.tex:1058-1074, F.33. For the finite counter the
    inherited-authority extinction rate is 1; for the spatial
    reference its conservative rate is 116b+232, b=s+11.
    The reference state includes inherited/fresh provenance. -/
def headlineInheritedRate (q : Nat) : Nat :=
  if q ≤ 32 then 1
  else if ceilLogTwo q = 6 then 1
  else 116 * (ceilLogTwo q + 11) + 232

/-- renewal.tex:1058-1077, sigma_0 to sigma_B.
    The class lives on a decorated reference state, not merely
    a physical configuration. -/
def StageInheritedAuthorityExtinction {n : Nat} {S : Type}
    (referenceNext : S → Fin n → S)
    (rooted inheritedGone : S → Prop)
    (q : Nat) : Prop :=
  ∀ x, rooted x →
    UniformFirstHit.ExpectedHittingTimeAtMost
      referenceNext inheritedGone x
      ((headlineInheritedRate q * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1074-1085, sigma_B to grant-free sigma_G.
    Strict 109/3 n^2 is safely charged 37n^2. -/
def StageReferenceGrantDrain {n : Nat} {S : Type}
    (referenceNext : S → Fin n → S)
    (inheritedGone grantFree : S → Prop) : Prop :=
  ∀ x, inheritedGone x →
    UniformFirstHit.ExpectedHittingTimeAtMost
      referenceNext grantFree x ((37 * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1087-1097, sigma_G to singleton sigma_1:
    exactly one contraction charged after all old grants drain. -/
def StageReferenceSingleton {n : Nat} {S : Type}
    (referenceNext : S → Fin n → S)
    (grantFree singleton : S → Prop) : Prop :=
  ∀ x, grantFree x →
    UniformFirstHit.ExpectedHittingTimeAtMost
      referenceNext singleton x ((4917 * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1099-1116, sigma_1 to prepared sigma_p:
    5n^2+n/2 is conservatively charged 6n^2. -/
def StageReferencePreparation {n : Nat} {S : Type}
    (referenceNext : S → Fin n → S)
    (singleton prepared : S → Prop) : Prop :=
  ∀ x, singleton x →
    UniformFirstHit.ExpectedHittingTimeAtMost
      referenceNext prepared x ((6 * n ^ 2 : Nat) : Rat)

/-- renewal.tex:1118-1130 and F.6: from prepared sigma_p
    through recurrence writer, reader retirement, digit and
    comparison, debt and request drain. F.6 gives a combined
    upper envelope, NOT separate numerical charges for
    each of these undisplayed intermediate cuts. -/
def StageReferenceGeneratedFinish {n : Nat} {S : Type}
    (referenceNext : S → Fin n → S)
    (prepared generated : S → Prop) (finishRate : Nat) : Prop :=
  ∀ x, prepared x →
    UniformFirstHit.ExpectedHittingTimeAtMost
      referenceNext generated x ((finishRate * n ^ 2 : Nat) : Rat)

/-! ## The nested reference coefficient A, before renewal -/

/-- F.7, F.34, renewal.tex:364-365,1646-1665:
    a reference attempt, not an additional real-world charge. -/
def headlineReferenceRate (q : Nat) : Nat :=
  if q ≤ 32 then headlineFiniteReference q
  else if ceilLogTwo q = 6 then 121125
  else 557 * ceilLogTwo q + 119981

/-- A reference finish allowance is the nonnegative remainder
    after charging sigma_0 -> sigma_B -> sigma_G -> sigma_1 ->
    sigma_p. It is not separately proved by F.6; the physical
    writer/reader/digit results must justify this final substage. -/
def headlineReferenceFinishRate (q : Nat) : Nat :=
  headlineReferenceRate q -
    (headlineInheritedRate q + 37 + 4917 + 6)

/-- The displayed prefix charges fit inside A at every finite
    advice slice and at every linear spatial width. -/
theorem headlineReferencePrefix_le (q : Nat) (hthree : 3 ≤ q) :
    headlineInheritedRate q + 37 + 4917 + 6 ≤
      headlineReferenceRate q := by
  by_cases hfinite : q ≤ 32
  · have hcheck :
        ∀ i : Fin 33, 3 ≤ i.val →
          headlineInheritedRate i.val + 37 + 4917 + 6 ≤
            headlineReferenceRate i.val := by decide
    exact hcheck ⟨q, by omega⟩ hthree
  · have hsix : 6 ≤ ceilLogTwo q :=
      ceilLogTwo_ge_six q (by omega)
    by_cases hwidth : ceilLogTwo q = 6
    · simp [headlineInheritedRate, headlineReferenceRate,
        hfinite, hwidth]
    · have hseven : 7 ≤ ceilLogTwo q := by omega
      simp only [headlineInheritedRate, headlineReferenceRate,
        if_neg hfinite, if_neg hwidth]
      omega

/-- Exact nested reference accounting: the five stage rates
    add to the F.7/F.34 reference ceiling A, which is charged
    once inside the F.3 renewal, not again after the renewal. -/
theorem headlineReferenceRate_decompose
    (q : Nat) (hthree : 3 ≤ q) :
    headlineInheritedRate q + 37 + 4917 + 6 +
        headlineReferenceFinishRate q =
      headlineReferenceRate q := by
  unfold headlineReferenceFinishRate
  have hb := headlineReferencePrefix_le q hthree
  omega

/-! ## Already kernel-proved stage contributions -/

/-- Clause 0, renewal.tex:1416-1489, now StateCount.lean:415-422. -/
def StageAlphabetBudget (n : Nat) : Prop :=
  ∃ N, N ≤ stateBudget (compileAdvice (ceilLogTwo n)).s ∧
    ∃ decode : Fin N → Agent (compileAdvice (ceilLogTwo n)),
      (∀ i j, decode i = decode j → i = j) ∧
      (∀ a, ∃ i, decode i = a)

theorem stageAlphabetBudget_of_stateCount
    (n : Nat) (hn : 5 ≤ n) : StageAlphabetBudget n :=
  stateCount n hn

/-- A generated target has zero OLD requests; this is the
    already proved Closure.targetRequestsZero, not full closure. -/
def StageGeneratedRequestsQuiet {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineGeneratedTarget ring C →
    ∀ i : Fin n, (C i).req = false

theorem stageGeneratedRequestsQuiet_of_Closure
    {n : Nat} (ring : DirectedRing n) :
    StageGeneratedRequestsQuiet ring := by
  intro C h i
  exact Closure.targetRequestsZero ring
    (Closure.readerFoldValid (ceilLogTwo n) n)
    C h i

/-- The one-native-leader factor of the fixed target is already
    supplied by Closure.NativeFactor. This is not yet IsSafe:
    freezing the output along every reachable edge remains open. -/
def StageGeneratedOneNativeLeader {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ C : HeadlineConfiguration n, headlineGeneratedTarget ring C →
    OneNativeLeader (nativeProjection C)

theorem stageGeneratedOneNativeLeader_of_Closure
    {n : Nat} (ring : DirectedRing n) :
    StageGeneratedOneNativeLeader ring := by
  intro C h
  exact h.1.1

/-- SerClockCost: physically executed S1 from a
    WFixedRoot entrance, with no-root-loss closure supplied.
    This stage is paid INSIDE F.6/F.34's rooted reference
    allowance, not added to F.10/F.36 a second time. -/
def StageSerializerSOne {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (H : (Fin n → ProjW c) → Prop) : Prop :=
  ∀ s, H s →
    UniformFirstHit.ExpectedHittingTimeAtMost
      (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active s : ClockSerializerStopNode n c)
      ((n * (5 * n - 4) : Nat) : Rat)

theorem stageSerializerSOne_of_SerClockCost {n : Nat}
    {c : Compiled} (ring : DirectedRing n)
    (root : Fin n) (H : (Fin n → ProjW c) → Prop)
    (hn : 4 ≤ n)
    (hclosed : ClockSerializerNoRootLossFromG ring root H) :
    StageSerializerSOne ring root H := by
  intro s hs
  exact clockSerializerSOneExpectedFromG
    ring root H hclosed s hs hn

/-! ## Same-scheduler stopping-time composition -/

/-- A one-stage cost to B or target, then a restarted cost
    from any B-cut to target, composes on the same Fin n
    scheduler. This is ProbStages.lean:275-295 specialized
    to stage coefficients times n^2. -/
private theorem headlineComposeRates {S : Type} {n : Nat}
    (next : S → Fin n → S) (A B Target : S → Prop)
    (a b : Nat) (hn : 0 < n)
    (hfirst : ∀ x, A x →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next (fun y => B y ∨ Target y) x
        ((a * n ^ 2 : Nat) : Rat))
    (hsecond : ∀ y, B y →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next Target y ((b * n ^ 2 : Nat) : Rat)) :
    ∀ x, A x →
      UniformFirstHit.ExpectedHittingTimeAtMost next Target x
        (((a + b) * n ^ 2 : Nat) : Rat) := by
  intro x hx
  have hh := Prob.expectedHittingTimeAtMost_stage_le
    next hn x B Target (a * n ^ 2) (b * n ^ 2)
    (hfirst x hx) hsecond
  simpa only [Nat.add_mul] using hh

/-- Reference-stage composition when the paper supplies separate
    B (not B-or-Generated) first-hit clocks. Enlarge the first
    target, then use the same-scheduler Markov composition. -/
private theorem headlineComposeDirect {S : Type} {n : Nat}
    (next : S → Fin n → S) (A B Target : S → Prop)
    (a b : Nat) (hn : 0 < n)
    (hfirst : ∀ x, A x →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next B x ((a * n ^ 2 : Nat) : Rat))
    (hsecond : ∀ y, B y →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next Target y ((b * n ^ 2 : Nat) : Rat)) :
    ∀ x, A x →
      UniformFirstHit.ExpectedHittingTimeAtMost next Target x
        (((a + b) * n ^ 2 : Nat) : Rat) := by
  have hfirstUnion :
      ∀ x, A x →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next (fun y => B y ∨ Target y) x
          ((a * n ^ 2 : Nat) : Rat) := by
    intro x hx
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next (fun y => B y ∨ Target y) hn x (a * n ^ 2)).2
    have hcost := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next B hn x (a * n ^ 2)).1 (hfirst x hx)
    intro T
    exact Nat.le_trans
      (Prob.costNumerator_target_mono next
        B (fun y => B y ∨ Target y)
        (fun y hy => Or.inl hy) x T)
      (hcost T)
  exact headlineComposeRates next A B Target a b hn
    hfirstUnion hsecond

/-- renewal.tex:1058-1146 and F.7/F.34.
    The complete five-cut reference chain has mean <= A n^2
    on its own decorated reference state. This does not yet
    imply the physical rooted renewal R n^2: F.1-F.4's
    fresh-origin causal coupling remains a separate obligation. -/
theorem headlineReferenceStagesCompose {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (rooted inheritedGone grantFree singleton prepared generated : S → Prop)
    (q : Nat) (hthree : 3 ≤ q) (hn : 0 < n)
    (hOld : StageInheritedAuthorityExtinction
      next rooted inheritedGone q)
    (hDrain : StageReferenceGrantDrain
      next inheritedGone grantFree)
    (hSingle : StageReferenceSingleton
      next grantFree singleton)
    (hPrep : StageReferencePreparation
      next singleton prepared)
    (hFinish : StageReferenceGeneratedFinish
      next prepared generated (headlineReferenceFinishRate q)) :
    ∀ x, rooted x →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next generated x
        ((headlineReferenceRate q * n ^ 2 : Nat) : Rat) := by
  have hPrepared :
      ∀ x, prepared x →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next generated x
          ((headlineReferenceFinishRate q * n ^ 2 : Nat) : Rat) :=
    hFinish
  have hSingleton :
      ∀ x, singleton x →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next generated x
          (((6 + headlineReferenceFinishRate q) * n ^ 2 : Nat) : Rat) := by
    exact headlineComposeDirect next singleton prepared generated
      6 (headlineReferenceFinishRate q) hn hPrep hPrepared
  have hGrantFree :
      ∀ x, grantFree x →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next generated x
          (((4917 + (6 + headlineReferenceFinishRate q)) *
            n ^ 2 : Nat) : Rat) := by
    exact headlineComposeDirect next grantFree singleton generated
      4917 (6 + headlineReferenceFinishRate q)
      hn hSingle hSingleton
  have hInheritedGone :
      ∀ x, inheritedGone x →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next generated x
          (((37 + (4917 + (6 + headlineReferenceFinishRate q))) *
            n ^ 2 : Nat) : Rat) := by
    exact headlineComposeDirect next inheritedGone grantFree generated
      37 (4917 + (6 + headlineReferenceFinishRate q))
      hn hDrain hGrantFree
  have hRoot :
      ∀ x, rooted x →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next generated x
          (((headlineInheritedRate q +
            (37 + (4917 + (6 + headlineReferenceFinishRate q)))) *
            n ^ 2 : Nat) : Rat) := by
    exact headlineComposeDirect next rooted inheritedGone generated
      (headlineInheritedRate q)
      (37 + (4917 + (6 + headlineReferenceFinishRate q)))
      hn hOld hInheritedGone
  have hRate :
      headlineInheritedRate q +
        (37 + (4917 + (6 + headlineReferenceFinishRate q))) =
      headlineReferenceRate q := by
    have hh := headlineReferenceRate_decompose q hthree
    omega
  intro x hx
  simpa only [hRate] using hRoot x hx

private theorem headlineRate_reassoc (n : Nat) :
    2 + (headlinePermitRate n +
      ((headlineCheckerRate n + 1) +
        (1 + headlineRenewalRate n))) =
      headlineStageRate n := by
  unfold headlineStageRate
  omega

/-- The physical state classes above and the six OPEN stage
    premises imply the complete linear-lease headline.
    The proof does not relabel the reference sigma_B,... as
    stopping times on the undecorated real configuration. -/
theorem l3Headline_of_stages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hpurify : StageNativePurification ring)
    (hgrant : StageFirstGrant ring)
    (hrequest : StageRequestChecker ring)
    (hbirth : StageFirstProtectedBirth ring)
    (hrenew : StageRootedRenewal ring)
    (hclosed : StageGeneratedClosure ring)
    (hsafe : StageGeneratedSafety ring) :
    L3Headline ring := by
  unfold L3Headline
  refine ⟨stateCount n hn, headlineGeneratedTarget ring,
    hclosed, hsafe, ?_⟩
  have hroot :
      ∀ C : HeadlineConfiguration n,
        headlineRooted ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
          C ((headlineRenewalRate n * n ^ 2 : Nat) : Rat) :=
    hrenew
  have hready :
      ∀ C : HeadlineConfiguration n,
        headlineRequestReady ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
          C (((1 + headlineRenewalRate n) * n ^ 2 : Nat) : Rat) := by
    exact headlineComposeRates (headlinePhysicalNext ring)
      (headlineRequestReady ring) (headlineRooted ring)
      (headlineGeneratedTarget ring) 1 (headlineRenewalRate n)
      (by omega)
      (by intro C hC; rw [Nat.one_mul]; exact hbirth C hC) hroot
  have hgrantReady :
      ∀ C : HeadlineConfiguration n,
        headlineGrantReady ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
          C ((((headlineCheckerRate n + 1) +
            (1 + headlineRenewalRate n)) * n ^ 2 : Nat) : Rat) := by
    exact headlineComposeRates (headlinePhysicalNext ring)
      (headlineGrantReady ring) (headlineRequestReady ring)
      (headlineGeneratedTarget ring)
      (headlineCheckerRate n + 1) (1 + headlineRenewalRate n)
      (by omega) hrequest hready
  have hpurified :
      ∀ C : HeadlineConfiguration n,
        headlinePurified ring C →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
          C (((headlinePermitRate n +
            ((headlineCheckerRate n + 1) +
              (1 + headlineRenewalRate n))) * n ^ 2 : Nat) : Rat) := by
    exact headlineComposeRates (headlinePhysicalNext ring)
      (headlinePurified ring) (headlineGrantReady ring)
      (headlineGeneratedTarget ring)
      (headlinePermitRate n)
      ((headlineCheckerRate n + 1) + (1 + headlineRenewalRate n))
      (by omega) hgrant hgrantReady
  have hall :
      ∀ C : HeadlineConfiguration n,
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
          C (((2 + (headlinePermitRate n +
            ((headlineCheckerRate n + 1) +
              (1 + headlineRenewalRate n)))) * n ^ 2 : Nat) : Rat) := by
    intro C
    exact headlineComposeRates (headlinePhysicalNext ring)
      (fun _ => True) (headlinePurified ring)
      (headlineGeneratedTarget ring)
      2 (headlinePermitRate n +
        ((headlineCheckerRate n + 1) +
          (1 + headlineRenewalRate n)))
      (by omega) (fun X _ => hpurify X) hpurified C True.intro
  intro C0
  have htotal :
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
        C0 ((headlineStageCost n : Nat) : Rat) := by
    have hh := hall C0
    simpa only [headlineStageCost, headlineRate_reassoc n] using hh
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
    (by omega : 0 < n) C0 (linearLeaseBound n)).2
  have hh := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
    (by omega : 0 < n) C0 (headlineStageCost n)).1 htotal
  intro T
  exact Nat.le_trans (hh T)
    (Nat.mul_le_mul_left (n ^ T)
      (headlineStageCost_le_linearLeaseBound n hn))

/-!
OPEN OBLIGATIONS (not axioms or additional theorems):
- StageNativePurification: Native.lean / Purification birth-overlay,
  renewal.tex:1006-1014.
- StageFirstGrant: Counter.lean, FreshScan.lean,
  renewal.tex:1019-1029 and F.9/F.36.
- StageRequestChecker: FreshScan.lean / EWord.lean,
  renewal.tex:1030-1046.
- StageFirstProtectedBirth: Native.lean / GrantDrain.lean,
  renewal.tex:1032-1045.
- StageInheritedAuthorityExtinction: Counter.lean / GrantDrain.lean,
  reference ghost with inherited/fresh identity, sigma_B.
- StageReferenceGrantDrain: GrantDrain.lean, sigma_G.
- StageReferenceSingleton: TripleDeletion.lean, sigma_1.
- StageReferencePreparation: SealedPrep.lean / repair.tex,
  sigma_p.
- headlineReferenceStagesCompose composes all five reference-cut
  clocks if their named numerical stage premises hold; it does
  not establish the fresh-origin real-process renewal.
- StageReferenceGeneratedFinish: EWord.lean, FreshScan.lean,
  CouponClear.lean, SealedClose.lean, sigma_p to generated.
- StageRootedRenewal: FreshScan.lean / ProbRenewal.lean must
  connect the reference cuts to the real fresh-origin divergence
  restart F.1-F.4, without charging reference stages AGAIN.
- StageGeneratedClosure: Closure.lean must close ALL factors
  (including final debt/request) under every physical service.
- StageGeneratedSafety: Closure.lean / Headline.lean must
  promote one permanent physical leader to IsSafe.

Already proved:
- stateCount proves StageAlphabetBudget for n>=5.
- Closure.targetRequestsZero proves StageGeneratedRequestsQuiet.
- SerClockCost.clockSerializerSOneExpectedFromG proves
  StageSerializerSOne given ClockSerializerNoRootLossFromG.
- Closure.NativeFactor proves StageGeneratedOneNativeLeader,
  but one leader is insufficient without all-edge output freezing.
  The latter is a projected, named closure hypothesis, not
  implied merely by the final target's native factor.

NUMERICAL ACCOUNTING:
- At q=5 the bound is saturated exactly by F.14.
- No additional S1 charge is permitted outside the rooted
  renewal reference allowance.
- For psi>=17 the conservative F.37 rates remain within
  19617000*psi^3 < 20407959*psi^3.
- The finite and small-spatial rates use the F.10/F.36 tables.
- This conditional assembler does not claim those open physical
  stage clocks already follow from the cited kernel modules.
-/
end L3
