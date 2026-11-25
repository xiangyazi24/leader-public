import Leader.L3.Prime.BankCount
import Leader.L3.Headline.RenewalCleanBank

/-!
Q4686: signed clean renewal from the sharp BANK origin count.
Source pin: d8ec1aedf8fcf2c01636337b6901478cee9bedab.

UNCOMPILED DRAFT. The commands at the end request the later axioms
audit; no compiler run or audit result is claimed by this delivery.
U3a slot preservation, clean coverage and the clean reference clock
remain explicit premises.
-/

set_option autoImplicit false
set_option Elab.async false

namespace L3.HeadlineRenewalCleanBank

open L3
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (retryCount)

/-- Sharp origin charge for the physical target G itself. -/
def ReferenceOriginChargeSharpAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop)
    (D : RootedReferenceData ring) (cnum cden : Nat) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ G seed.val → ∀ T : Nat,
      cden * Prob.originsNumerator D.referenceNext D.referenceStop
        D.spawn (D.referenceStart seed) T ≤
        cden * (n ^ T * n) +
          cnum * costNumerator D.referenceNext D.referenceStop
            (D.referenceStart seed) T

/-- The sharp certificate uses the actual threshold K. -/
structure RootedReferenceCertificateSharpAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop)
    (hn : 5 ≤ n) (D : RootedReferenceData ring)
    (A K cnum cden : Nat) : Prop where
  domination : ReferenceAttemptDominationAt ring G hn D
  coverage : ReferenceRetryCoverageAt ring G hn D
  charge : ReferenceOriginChargeSharpAt ring G D cnum cden
  rarity : ReferenceOriginRarityK ring D K
  clock : ReferenceClockAt ring G D A

private theorem signedSharpCeilingLeOfMul (a d R : Nat)
    (hd : 0 < d) (h : a ≤ d * R) :
    Prob.ceilNat a d ≤ R := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hmul : d * (a / d) ≤ d * R := by omega
  have hquot : a / d ≤ R := Nat.le_of_mul_le_mul_left hmul hd
  by_cases hz : a % d = 0
  · simpa only [Prob.ceilNat, if_pos hz, Nat.add_zero] using hquot
  · have hne : a / d ≠ R := by
      intro hh
      rw [hh] at he
      omega
    have hsucc : a / d + 1 ≤ R := by omega
    simpa only [Prob.ceilNat, if_neg hz] using hsucc

/-- Sharp renewal for an arbitrary physical target G. -/
theorem rootedCostFromReferenceSharpAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop)
    (hn : 5 ≤ n)
    (D : RootedReferenceData ring) (A K cnum cden R : Nat)
    (h : RootedReferenceCertificateSharpAt ring G hn D A K cnum cden)
    (hrho : cden * n + cnum * (A * n ^ 2) < 2 ^ K * cden)
    (hreserve :
      (A * n ^ 2) * (2 ^ K * cden) ≤
        (2 ^ K * cden -
          (cden * n + cnum * (A * n ^ 2))) * (R * n ^ 2)) :
    ∀ C : HeadlineConfiguration n, headlineRooted ring C → ∀ T : Nat,
      costNumerator (headlinePhysicalNext ring) G C T ≤
        n ^ T * (R * n ^ 2) := by
  classical
  have hsimulation :
      Prob.RetrySimulation (referenceKernelAt ring G hn D)
        (headlinePhysicalNext ring) G
        (rootedTrialRelation (H := D.Memory) ring) :=
    rootedTrialSimulationAt ring G hn D.initialMemory D.memoryNext D.cut
  have hattempt : ∀ seed : RootedSeed ring,
      (referenceKernelAt ring G hn D).valid seed → ∀ T : Nat,
      costNumerator
        (Prob.attemptStepper (referenceKernelAt ring G hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernelAt ring G hn D).start seed)) T ≤
          n ^ T * (A * n ^ 2) := by
    intro seed hvalid T
    exact Nat.le_trans
      (referenceAttemptCostAt ring G hn D h.domination seed hvalid T)
      (h.clock seed hvalid T)
  have hretry : ∀ seed : RootedSeed ring,
      (referenceKernelAt ring G hn D).valid seed → ∀ T : Nat,
      (2 ^ K * cden) *
        retryCount (referenceKernelAt ring G hn D)
          (.active ((referenceKernelAt ring G hn D).start seed)) T ≤
        (cden * n + cnum * (A * n ^ 2)) * n ^ T := by
    intro seed hvalid T
    have hcover :=
      referenceRetryCountAt ring G hn D h.coverage seed hvalid T
    have hmass := Prob.origin_counting_sharp_le
      D.referenceNext D.referenceStop D.spawn D.win
      1 (2 ^ K) h.rarity (D.referenceStart seed)
      cnum cden n (A * n ^ 2)
      (h.charge seed hvalid) (h.clock seed hvalid)
    calc
      (2 ^ K * cden) *
          retryCount (referenceKernelAt ring G hn D)
            (.active ((referenceKernelAt ring G hn D).start seed)) T ≤
        (2 ^ K * cden) *
          Prob.originEventNumerator D.referenceNext D.referenceStop
            D.spawn D.win (D.referenceStart seed) T :=
        Nat.mul_le_mul_left _ hcover
      _ ≤ 1 * (n ^ T * (cden * n + cnum * (A * n ^ 2))) :=
        hmass T
      _ = (cden * n + cnum * (A * n ^ 2)) * n ^ T := by
        simp only [Nat.one_mul]
        ac_rfl
  have hceil :
      Prob.renewalCeiling
        (A * n ^ 2)
        (cden * n + cnum * (A * n ^ 2))
        (2 ^ K * cden) ≤ R * n ^ 2 := by
    change Prob.ceilNat
      ((A * n ^ 2) * (2 ^ K * cden))
      (2 ^ K * cden -
        (cden * n + cnum * (A * n ^ 2))) ≤ R * n ^ 2
    exact signedSharpCeilingLeOfMul _ _ _ (by omega) hreserve
  intro C hC T
  by_cases hterminal : G C
  · rw [costNumerator_terminal (headlinePhysicalNext ring)
      G C hterminal T]
    exact Nat.zero_le _
  · have hcost := Prob.costNumerator_renewal_le
      (headlinePhysicalNext ring) G
      (referenceKernelAt ring G hn D)
      (rootedTrialRelation (H := D.Memory) ring)
      hsimulation
      (A * n ^ 2)
      (cden * n + cnum * (A * n ^ 2))
      (2 ^ K * cden) hrho hattempt hretry
      C (⟨C, hC⟩ : RootedSeed ring) hterminal rfl T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left (n ^ T) hceil)

end L3.HeadlineRenewalCleanBank

namespace L3.Prime

open L3.HeadlineRenewal

private theorem signedRenewalDenominatorBound (b : Nat) :
    b * (b + 2) ≤ 4 * ((b - b / 2) * (b / 2 + 1)) := by
  let u := b / 2
  have hmod : b % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsplit := Nat.div_add_mod b 2
  have hparity : b = 2 * u ∨ b = 2 * u + 1 := by
    dsimp only [u]
    omega
  change b * (b + 2) ≤ 4 * ((b - u) * (u + 1))
  rcases hparity with heven | hodd
  · rw [heven]
    rw [show 2 * u - u = u by omega]
    rw [show 2 * u + 2 = 2 * (u + 1) by omega]
    calc
      (2 * u) * (2 * (u + 1)) = (2 * 2) * (u * (u + 1)) := by ac_rfl
      _ ≤ 4 * (u * (u + 1)) := Nat.le_refl _
  · rw [hodd]
    rw [show 2 * u + 1 - u = u + 1 by omega]
    rw [show (2 * u + 1) + 2 = 2 * u + 3 by omega]
    have hsq : (2 * u) * (2 * u) = 4 * (u * u) := by
      calc
        _ = (2 * 2) * (u * u) := by ac_rfl
        _ = _ := rfl
    have hthree : (2 * u) * 3 = 6 * u := by
      calc
        _ = (2 * 3) * u := by ac_rfl
        _ = _ := rfl
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, hsq, hthree]
    omega

private theorem signedRenewalParameters (n : Nat)
    (hsigned : signedBand (ceilLogTwo n)) :
    bankCountWidth n = ceilLogTwo (ceilLogTwo n) + 11 ∧
      renewalBankReferenceCeiling n = signedA (ceilLogTwo (ceilLogTwo n)) ∧
      headlineRenewalRate n = (4 * renewalBankReferenceCeiling n + 2) / 3 := by
  obtain ⟨hs, _, _, _⟩ :=
    compileAdvice_K_signed_bounds (ceilLogTwo n) hsigned
  have hsq := ceilLogTwo_le_self (ceilLogTwo n)
  have hnot32 : ¬ ceilLogTwo n ≤ 32 := by omega
  have hnot6 : ceilLogTwo (ceilLogTwo n) ≠ 6 := by omega
  have hnot16 : ¬ ceilLogTwo (ceilLogTwo n) ≤ 16 := by omega
  have hmax : max 2 (ceilLogTwo (ceilLogTwo n)) =
      ceilLogTwo (ceilLogTwo n) := by omega
  have hb : bankCountWidth n = ceilLogTwo (ceilLogTwo n) + 11 := by
    change (compileAdvice (ceilLogTwo n)).s + 11 =
      ceilLogTwo (ceilLogTwo n) + 11
    rw [compileAdvice_s, hmax]
  have hA : renewalBankReferenceCeiling n =
      signedA (ceilLogTwo (ceilLogTwo n)) := by
    simp [renewalBankReferenceCeiling, headlineReferenceRate,
      hnot32, hnot6, signedA]
  refine ⟨hb, hA, ?_⟩
  rw [hA]
  simp [headlineRenewalRate, headlineSelectedLedger, hnot32,
    headlineLargeLedger, hnot16, hs, signedA]

private theorem signedRenewalExponentGap (q : Nat) (hsigned : signedBand q) :
    q + 59 ≤ (compileAdvice q).K := by
  obtain ⟨hs, hK, _, htlt⟩ := compileAdvice_K_signed_bounds q hsigned
  have hsq := ceilLogTwo_le_self q
  have hqmin : 2 ≤ q := by omega
  have hqpow := (ceilLogTwo_spec q hqmin).1
  have hsmall : ceilLogTwo q - 2 < 2 ^ (ceilLogTwo q - 2) :=
    Nat.lt_two_pow_self
  have hbase : ceilLogTwo q - 1 ≤ 2 ^ (ceilLogTwo q - 2) := by omega
  have hpow : 2 ^ (ceilLogTwo q - 1) =
      2 * 2 ^ (ceilLogTwo q - 2) := by
    rw [show ceilLogTwo q - 1 = (ceilLogTwo q - 2) + 1 by omega,
      Nat.pow_succ, Nat.mul_comm]
  have hdouble : 2 * (ceilLogTwo q - 1) ≤ 2 ^ (ceilLogTwo q - 1) := by
    rw [hpow]
    exact Nat.mul_le_mul_left 2 hbase
  rw [hK]
  omega

/-- The two integer bounds for (T3.1): the clock contribution is at
most one eighth, and the inherited-origin contribution is tiny. -/
theorem signedRenewalNumeratorBounds (n : Nat) (hn : 5 ≤ n)
    (hsigned : signedBand (ceilLogTwo n)) :
    let d := (bankCountWidth n - bankCountHalf n) * (bankCountHalf n + 1)
    0 < d ∧
      8 * (renewalBankReferenceCeiling n * n ^ 2) ≤
        2 ^ (compileAdvice (ceilLogTwo n)).K * d ∧
      2 ^ 59 * n ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  let q := ceilLogTwo n
  let s := ceilLogTwo q
  let t := signedT s
  let b := bankCountWidth n
  let d := (b - b / 2) * (b / 2 + 1)
  let A := renewalBankReferenceCeiling n
  let K := (compileAdvice q).K
  change 0 < d ∧ 8 * (A * n ^ 2) ≤ 2 ^ K * d ∧ 2 ^ 59 * n ≤ 2 ^ K
  have hparams := signedRenewalParameters n hsigned
  have hb : b = s + 11 := hparams.1
  have hA : A = signedA s := hparams.2.1
  obtain ⟨hsRaw, hKRaw, _, htltRaw⟩ :=
    compileAdvice_K_signed_bounds q hsigned
  have hs : 40000 ≤ s := hsRaw
  have hK : K = 2 * q - t := hKRaw
  have htlt : t < s := htltRaw
  have hsq : s ≤ q := ceilLogTwo_le_self q
  have hKt : K + t = 2 * q := by omega
  have hBden : signedB s ≤ 4 * d := by
    have hw := signedRenewalDenominatorBound b
    change b * (b + 2) ≤ 4 * d at hw
    calc
      signedB s = b * (b + 2) := by
        rw [hb]
        simp [signedB, Nat.add_assoc]
      _ ≤ 4 * d := hw
  have hbase : 32 * A * 2 ^ t ≤ signedB s := by
    rw [hA]
    exact (signedT_spec s hs).2.1
  have hAd : 8 * A * 2 ^ t ≤ d := by
    have hscaled : 4 * (8 * A * 2 ^ t) ≤ 4 * d := by
      calc
        4 * (8 * A * 2 ^ t) = ((4 * 8) * A) * 2 ^ t := by ac_rfl
        _ = 32 * A * 2 ^ t := rfl
        _ ≤ signedB s := hbase
        _ ≤ 4 * d := hBden
    exact Nat.le_of_mul_le_mul_left hscaled (by decide : 0 < (4 : Nat))
  have hApos : 0 < A := by
    rw [hA]
    unfold signedA
    omega
  have hprod : 0 < 8 * A * 2 ^ t :=
    Nat.mul_pos (Nat.mul_pos (by decide) hApos) (Nat.two_pow_pos _)
  have hd : 0 < d := by omega
  have hnq : n ≤ 2 ^ q := (ceilLogTwo_spec n (by omega)).2
  have hnsq : n ^ 2 ≤ 2 ^ (2 * q) := by
    calc
      n ^ 2 = n * n := by simp [Nat.pow_succ]
      _ ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul hnq hnq
      _ = 2 ^ (2 * q) := by
        rw [show 2 * q = q + q by omega, Nat.pow_add]
  have hAterm : 8 * (A * n ^ 2) ≤ 2 ^ K * d := by
    calc
      8 * (A * n ^ 2) = (8 * A) * n ^ 2 := by ac_rfl
      _ ≤ (8 * A) * 2 ^ (2 * q) := Nat.mul_le_mul_left _ hnsq
      _ = 2 ^ K * (8 * A * 2 ^ t) := by
        rw [← hKt, Nat.pow_add]
        ac_rfl
      _ ≤ 2 ^ K * d := Nat.mul_le_mul_left _ hAd
  have hgap : q + 59 ≤ K := signedRenewalExponentGap q hsigned
  have htiny : 2 ^ 59 * n ≤ 2 ^ K := by
    calc
      2 ^ 59 * n ≤ 2 ^ 59 * 2 ^ q := Nat.mul_le_mul_left _ hnq
      _ = 2 ^ (q + 59) := by
        rw [Nat.pow_add]
        ac_rfl
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hgap
  exact ⟨hd, hAterm, htiny⟩

/-- Integer hrho and hreserve for the signed clean renewal kernel. -/
theorem signedRenewalMargins (n : Nat) (hn : 5 ≤ n)
    (hsigned : signedBand (ceilLogTwo n)) :
    let A := renewalBankReferenceCeiling n
    let d := (bankCountWidth n - bankCountHalf n) * (bankCountHalf n + 1)
    let K := (compileAdvice (ceilLogTwo n)).K
    let R := headlineRenewalRate n
    d * n + 1 * (A * n ^ 2) < 2 ^ K * d ∧
      (A * n ^ 2) * (2 ^ K * d) ≤
        (2 ^ K * d - (d * n + 1 * (A * n ^ 2))) * (R * n ^ 2) := by
  let A := renewalBankReferenceCeiling n
  let d := (bankCountWidth n - bankCountHalf n) * (bankCountHalf n + 1)
  let K := (compileAdvice (ceilLogTwo n)).K
  let R := headlineRenewalRate n
  change d * n + 1 * (A * n ^ 2) < 2 ^ K * d ∧
    (A * n ^ 2) * (2 ^ K * d) ≤
      (2 ^ K * d - (d * n + 1 * (A * n ^ 2))) * (R * n ^ 2)
  have hbounds := signedRenewalNumeratorBounds n hn hsigned
  change 0 < d ∧ 8 * (A * n ^ 2) ≤ 2 ^ K * d ∧ 2 ^ 59 * n ≤ 2 ^ K at hbounds
  obtain ⟨hd, hAterm, htiny⟩ := hbounds
  have heighth : 8 * n ≤ 2 ^ K :=
    Nat.le_trans (Nat.mul_le_mul_right n (by decide : 8 ≤ (2 : Nat) ^ 59)) htiny
  have hinherited : 8 * (d * n) ≤ 2 ^ K * d := by
    calc
      8 * (d * n) = (8 * n) * d := by ac_rfl
      _ ≤ 2 ^ K * d := Nat.mul_le_mul_right d heighth
  let N := d * n + A * n ^ 2
  let D := 2 ^ K * d
  have hquarter : 4 * N ≤ D := by
    have hsum := Nat.add_le_add hinherited hAterm
    change 8 * (d * n) + 8 * (A * n ^ 2) ≤ D + D at hsum
    change 4 * (d * n + A * n ^ 2) ≤ D
    omega
  have hDpos : 0 < D := Nat.mul_pos (Nat.two_pow_pos _) hd
  have hlt : N < D := by omega
  have hNle : N ≤ D := Nat.le_of_lt hlt
  have hminus : D - N + N = D := Nat.sub_add_cancel hNle
  have hgap : 3 * D ≤ 4 * (D - N) := by omega
  have hround : 4 * A ≤ 3 * R := by
    have hR : R = (4 * A + 2) / 3 :=
      (signedRenewalParameters n hsigned).2.2
    have hmod := Nat.div_add_mod (4 * A + 2) 3
    have hmodlt := Nat.mod_lt (4 * A + 2) (by decide : 0 < (3 : Nat))
    rw [hR]
    omega
  have hscaled : 4 * (A * D) ≤ 4 * ((D - N) * R) := by
    calc
      4 * (A * D) = (4 * A) * D := by ac_rfl
      _ ≤ (3 * R) * D := Nat.mul_le_mul_right D hround
      _ = (3 * D) * R := by ac_rfl
      _ ≤ (4 * (D - N)) * R := Nat.mul_le_mul_right R hgap
      _ = 4 * ((D - N) * R) := by ac_rfl
  have hfactor : A * D ≤ (D - N) * R :=
    Nat.le_of_mul_le_mul_left hscaled (by decide : 0 < (4 : Nat))
  have hreserve : (A * n ^ 2) * D ≤ (D - N) * (R * n ^ 2) := by
    calc
      (A * n ^ 2) * D = (A * D) * n ^ 2 := by ac_rfl
      _ ≤ ((D - N) * R) * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hfactor
      _ = (D - N) * (R * n ^ 2) := by ac_rfl
  simp only [Nat.one_mul]
  change N < D ∧ (A * n ^ 2) * D ≤ (D - N) * (R * n ^ 2)
  exact ⟨hlt, hreserve⟩

end L3.Prime

namespace L3.Prime

open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.RenewalReferenceClock
open L3.GrantDrainEntrance
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- The installed local potential theorem supplies the step bound once
slot preservation is available. -/
theorem bankCountStepBoundOfSlots {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e)) :
    BankCountStepBound ring := by
  intro r e h
  exact bankCountPotentialStepOfSlots ring hn hbank r e h.1 h.2
    (hslotnext r e h)

/-- This clean-reference charge holds for every seed. Its presentation
with an arbitrary nonterminality gate therefore supports every G. -/
theorem bankCleanReferenceOriginChargeSharpAtOfSlots {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e)) :
    ReferenceOriginChargeSharpAt ring G
      (bankCleanRootedReferenceData ring hbank) 1
      ((bankCountWidth n - bankCountHalf n) * (bankCountHalf n + 1)) := by
  have hstep := bankCountStepBoundOfSlots ring hn hbank hslotnext
  intro seed _ T
  have hcard : ∀ x : (bankCleanRootedReferenceData ring hbank).Reference,
      (bankCountHalf n + 1) *
        ((List.finRange n).countP (fun e => bankCountNom ring x.val e)) ≤ n := by
    intro x
    rw [← bankCountFilterLengthCount]
    exact bankCountNomPacked ring x.val
  simpa only [Nat.one_mul] using
    (bankCountOriginNumeratorChargeOfWordCharge
      (bankCleanRootedReferenceData ring hbank).referenceNext
      (bankCleanRootedReferenceData ring hbank).referenceStop
      (bankCleanRootedReferenceData ring hbank).spawn
      (fun x e => bankCountNom ring x.val e)
      (bankCountWidth n - bankCountHalf n) (bankCountHalf n + 1) n hcard
      ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
      (fun word => bankCountCleanReferenceWordChargeOfStep
        ring hn hbank hslotnext hstep
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
        (bankCountInvStart ring hn hbank seed) word)
      T)

/-- Signed clean renewal, conditional on U3a, clean coverage and clock. -/
theorem signedCleanRenewalOfSlots {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcoverage : ReferenceRetryCoverageAt ring (headlineCleanTarget ring) hn
      (bankCleanRootedReferenceData ring hbank))
    (hclock : ReferenceClockAt ring (headlineCleanTarget ring)
      (bankCleanRootedReferenceData ring hbank) (renewalBankReferenceCeiling n))
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e)) :
    signedBand (ceilLogTwo n) → StageCleanRootedRenewalCost ring := by
  intro hsb
  obtain ⟨hrho, hreserve⟩ := signedRenewalMargins n hn hsb
  have hcertificate : RootedReferenceCertificateSharpAt
      ring (headlineCleanTarget ring) hn
      (bankCleanRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n) (compileAdvice (ceilLogTwo n)).K 1
      ((bankCountWidth n - bankCountHalf n) * (bankCountHalf n + 1)) := {
    domination := bankValidReferenceAttemptDominationClean ring hn hbank
    coverage := hcoverage
    charge := bankCleanReferenceOriginChargeSharpAtOfSlots
      ring (headlineCleanTarget ring) hn hbank hslotnext
    rarity := renewalBankCleanRarity hn ring hbank
    clock := hclock }
  exact rootedCostFromReferenceSharpAt ring (headlineCleanTarget ring) hn
    (bankCleanRootedReferenceData ring hbank)
    (renewalBankReferenceCeiling n) (compileAdvice (ceilLogTwo n)).K 1
    ((bankCountWidth n - bankCountHalf n) * (bankCountHalf n + 1))
    (headlineRenewalRate n) hcertificate
    (by simpa only [Nat.one_mul] using hrho)
    (by simpa only [Nat.one_mul] using hreserve)

/-- Replace the former signed-renewal premise of the existing BANK
assembly by U3a; its other hypotheses supply coverage and clock. -/
theorem bankCleanStageRootedRenewalCostOfSlots {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank)
    (hthreshold : L3.BankRetryCoverage.BankCutGenuineHeadThreshold ring hbank)
    (rooted : (bankCleanRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineCleanTarget ring seed.val →
        rooted ((bankCleanRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankCleanRootedReferenceData ring hbank).referenceNext rooted
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n))
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e)) :
    StageCleanRootedRenewalCost ring := by
  exact bankCleanStageRootedRenewalCost ring hn hbank hdigit hthreshold
    rooted hstart hOld
    (signedCleanRenewalOfSlots ring hn hbank
      (bankReferenceRetryCoverageOfHeadThresholdClean ring hn hbank hthreshold)
      (bankCleanReferenceClock ring hn hbank hdigit rooted hstart hOld)
      hslotnext)

/-- SMALL advice never enters the signed band. -/
theorem signedCleanRenewalOfSmall {n : Nat} (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SignedCleanRenewal ring := by
  intro hsb
  exact False.elim (not_signedBand_of_useSmall (ceilLogTwo n) hsmall hsb)

end L3.Prime

#print axioms L3.HeadlineRenewalCleanBank.rootedCostFromReferenceSharpAt
#print axioms L3.Prime.signedRenewalNumeratorBounds
#print axioms L3.Prime.signedRenewalMargins
#print axioms L3.Prime.bankCountStepBoundOfSlots
#print axioms L3.Prime.bankCleanReferenceOriginChargeSharpAtOfSlots
#print axioms L3.Prime.signedCleanRenewalOfSlots
#print axioms L3.Prime.bankCleanStageRootedRenewalCostOfSlots
#print axioms L3.Prime.signedCleanRenewalOfSmall
