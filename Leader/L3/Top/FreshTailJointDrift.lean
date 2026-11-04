import Leader.L3.Top.FreshTailTicketPrepaid
import Leader.L3.Top.FreshTailTicketCharge
import Leader.L3.Top.FreshTailJointTarget

/-!
Q7c P.3 J4: the single
joint potential

  Psi(Z) = c*(Z) + (r+2) (A - R(Z)) + W(Z),

with c* = the earlier prepaid source potential (topFreshTailPrepaidPotential),
R = the physical comparison source-port receipt count, A = r(r+3)/2
(the receipt bound) and W = the raw P.2 target potential
topPortPotential. One (r+2) voucher per actual accepted port; no second
topClockB per port.

On a reached leaderless cut before the first genuine border tail, every
actual edge has Psi' + [charged] <= Psi, and the adapted nominated edge
(rightmost charged source service if the target border is free, the P.2
target frontier edge otherwise) lowers Psi by one.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A = r(r+3)/2, the bound on accepted source-port receipts
through the first genuine border tail. -/
def topFreshTailJointVoucherCap (r : Nat) : Nat := (r * r + 3 * r) / 2

/-- Section 1: Psi = c* + (r+2)(A - R) + W. -/
noncomputable def topFreshTailJointPotential
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Nat :=
  topFreshTailPrepaidPotential ring C s Z +
    (topClockSpan n + 2) *
      (topFreshTailJointVoucherCap (topClockSpan n) -
        topFreshTailPortReceiptCount s Z) +
    topPortPotential s Z

/-- The strict prefixes of a successor word are the prefixes of the
cut word. Consumer: topFreshTailJointHistoryReserveStep and the
pre-anchor closure in TopFreshTailJointAnchor. -/
theorem topFreshTailJointPrefixStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hfull : ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre)) :
    ∀ pre suffix : List (Fin n),
      pre ++ suffix = (topFixedTraceNext ring C Z e).2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre) := by
  intro pre suffix h hne
  rcases List.eq_nil_or_concat suffix with hnil | ⟨w, x, hw⟩
  · exact absurd hnil hne
  · rw [hw, List.concat_eq_append] at h
    have h' : (pre ++ w) ++ [x] = Z.2 ++ [e] := by
      rw [List.append_assoc]
      exact h
    exact hfull pre w (List.append_inj' h' rfl).1

/-- All prefixes, including the cut itself, avoid a genuine tail once
the strict ones do and the cut does. Consumer: the pre-anchor closure
in TopFreshTailJointAnchor. -/
theorem topFreshTailJointPrefixFull
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hstrict : ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 →
      suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre))
    (hnow : ¬ topClockGenuineTailAccepted C s Z) :
    ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre) := by
  intro pre suffix h
  by_cases hs : suffix = []
  · subst hs
    rw [List.append_nil] at h
    have hr : Z = topFixedTraceRun ring C Z.2 := hreach
    rw [h, ← hr]
    exact hnow
  · exact hstrict pre suffix h hs

/-- I.receipt: before the first genuine border tail, through
it, the physical receipt count is at most A = r(r+3)/2.
Consumer: topFreshTailJointHistoryReserveStep (voucher arithmetic). -/
theorem topFreshTailJointReceiptCap
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hpre : ∀ (pre suffix : List (Fin n)),
      pre ++ suffix = Z.2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre)) :
    topFreshTailPortReceiptCount s Z ≤
      topFreshTailJointVoucherCap (topClockSpan n) := by
  obtain ⟨i, d, hi, hd, hc⟩ :=
    topFreshTailPreTailAcceptedPortBound ring C s hn hbad Z hreach hpre
  unfold topFreshTailJointVoucherCap
  have hm : topClockSpan n * (topClockSpan n + 1) =
      topClockSpan n * topClockSpan n + topClockSpan n := Nat.mul_succ _ _
  rw [hm] at hd
  generalize topClockSpan n * topClockSpan n = q at hd ⊢
  omega

/-- The prepaid source potential is positive on every cut (the border
reserve is at least r+1, the frontier rank r-f at least one).
Consumer: the stopped-potential drop in TopFreshTailJointAnchor. -/
theorem topFreshTailJointPrepaidPos
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n) :
    1 ≤ topFreshTailPrepaidPotential ring C s Z := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  unfold topFreshTailPrepaidPotential
  cases hf : topFreshTailPrepaidFrontier ring C s Z with
  | none =>
      simp only
      have hres : 1 ≤ topFreshTailPrepaidReserve (topClockSpan n)
          (Z.1.1 (certSite s 0)).qOut := by
        cases (Z.1.1 (certSite s 0)).qOut with
        | E => simp only [topFreshTailPrepaidReserve]; omega
        | U => simp only [topFreshTailPrepaidReserve]; omega
        | D v t => cases t <;> simp only [topFreshTailPrepaidReserve] <;> omega
      omega
  | some f =>
      simp only
      have := (topFreshTailPrepaidSearchSome _ _ f hf).2.1
      omega

/-- Section 6 item 7, all-edge half (I.joint). On a reached cut of
a leaderless bad complete pair whose whole history avoids a genuine
border tail, every actual edge whose successor is not a genuine tail
satisfies Psi' + [charged] <= Psi: an accepted port moves (R, W) by
(+1, +(r+2)) so the voucher term absorbs W, and every other edge has
R' = R, W' <= W; c* is the earlier prepaid step.
Consumer: topFreshTailJointNominatedDrop and the all-edge nonincrease
in topFreshTailJointAnchorCostFromReachedDrift. -/
theorem topFreshTailJointHistoryReserveStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hfull : ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre))
    (e : Fin n)
    (hng : ¬ topClockGenuineTailAccepted C s (topFixedTraceNext ring C Z e)) :
    topFreshTailJointPotential ring C s (topFixedTraceNext ring C Z e) +
        (if TopFreshTailPrepaidCharged ring C s Z e then 1 else 0) ≤
      topFreshTailJointPotential ring C s Z := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hstep := topFreshTailPrepaidSourceContactStep ring C s hn hbad hleader
    Z hreach e hng
  have hcap := topFreshTailJointReceiptCap ring C s hn hbad
    (topFixedTraceNext ring C Z e) (topClockReachedNext ring C Z e hreach)
    (topFreshTailJointPrefixStep ring C s Z e hfull)
  have hcount := topFreshTailTicketReceiptCountStep ring C s Z e
  unfold topFreshTailJointPotential
  cases hx : topFreshTailGenealogyPortExport ring C s Z e with
  | none =>
      rw [hx] at hcount
      have hR : topFreshTailPortReceiptCount s (topFixedTraceNext ring C Z e) =
          topFreshTailPortReceiptCount s Z := by
        rw [hcount]
        rfl
      have hW : topPortPotential s (topFixedTraceNext ring C Z e) ≤
          topPortPotential s Z := by
        by_cases hoffer : topPortReadyOfferFirstMatch ring s Z e
        · obtain ⟨hsite, hnb, hyi, hyc⟩ := hoffer
          rw [hnb] at hyi hyc
          cases hxo : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut with
          | D v t =>
              obtain ⟨y, hy, _⟩ :=
                (topFreshTailJointPortAcceptedTargetBirth ring C s hn hbad Z
                  hreach e hsite hyi hyc v t hxo).2.2.2.1
              rw [hx] at hy
              cases hy
          | E =>
              exact Nat.le_of_eq
                (topFreshTailJointFreePortUnreadFrame ring C s hn hbad Z hreach e
                  hsite hyi hyc (by rw [hxo]; rfl)).2.2.2.2.1
          | U =>
              exact Nat.le_of_eq
                (topFreshTailJointFreePortUnreadFrame ring C s hn hbad Z hreach e
                  hsite hyi hyc (by rw [hxo]; rfl)).2.2.2.2.1
        · exact topFreshTailJointTargetUntouchedAndInternalBound ring C s hbad Z
            hreach e hoffer
      rw [hR]
      omega
  | some x =>
      obtain ⟨hsite, ⟨v, t, hD⟩, hyi, hyc⟩ :=
        topFreshTailJointExportFree ring C s hn hbad Z hreach e x hx
      have hacc := topFreshTailJointPortAcceptedTargetBirth ring C s hn hbad Z
        hreach e hsite hyi hyc v t hD
      rw [hacc.2.2.2.2.1, hacc.2.2.2.2.2]
      rw [hacc.2.2.2.2.1] at hcap
      have hsub : topFreshTailJointVoucherCap (topClockSpan n) -
            topFreshTailPortReceiptCount s Z =
          (topFreshTailJointVoucherCap (topClockSpan n) -
            (topFreshTailPortReceiptCount s Z + 1)) + 1 := by omega
      rw [hsub, Nat.mul_succ]
      omega

/-- The source search of the nominated edge: the rightmost occupied
source offset at or ahead of F1 (or anywhere, before F1 exists). -/
noncomputable def topFreshTailJointSourceSearch
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Option Nat :=
  topFreshTailPrepaidSearch
    (fun j => (topFreshTailPrepaidFrontier ring C s Z).getD 0 ≤ j ∧
      (Z.1.1 (certSite s j)).qOut ≠ .E)
    (topClockSpan n)

/-- Section 4: the rightmost charged source service, or the
source-zero bootstrap when no charged carrier exists. -/
noncomputable def topFreshTailJointSourceEdge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Fin n :=
  match topFreshTailJointSourceSearch ring C s Z with
  | none => certSite s 0
  | some j => certSite s j

/-- Section 4: the adapted nominated edge. A function of the
current physical cut and the prepaid frontier (hence of Z.1.1, Z.1.2,
Z.2); not a fixed schedule. -/
noncomputable def topFreshTailJointNominatedEdge
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Fin n :=
  if (Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
      (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF then
    topFreshTailJointSourceEdge ring C s Z
  else topPortFrontierEdge s Z

/-- Section 6 item 6 (I.selector). If the OLD target border is
E/OFF, the nominated source service is a charged useful source contact:
the source-zero bootstrap (no occupied slot at all), an OLD U sample,
a D hop into an OLD empty successor, or the accepted terminal D.
Consumer: topFreshTailJointNominatedDrop. -/
theorem topFreshTailJointRightmostChargedEligible
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hfree : (Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
      (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF) :
    TopFreshTailPrepaidCharged ring C s Z
      (topFreshTailJointSourceEdge ring C s Z) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  unfold topFreshTailJointSourceEdge
  cases hsearch : topFreshTailJointSourceSearch ring C s Z with
  | none =>
      have hnone := topFreshTailPrepaidSearchNone _ _ hsearch
      have hfront : topFreshTailPrepaidFrontier ring C s Z = none := by
        cases hf : topFreshTailPrepaidFrontier ring C s Z with
        | none => rfl
        | some f =>
            exfalso
            obtain ⟨hP, hflt, _⟩ := topFreshTailPrepaidSearchSome _ _ f hf
            obtain ⟨_, _, v, _, _, hq⟩ := hP
            apply hnone f hflt
            refine ⟨?_, ?_⟩
            · rw [hf]
              exact Nat.le_refl f
            · rw [hq]
              intro h
              cases h
      have hE : (Z.1.1 (certSite s 0)).qOut = .E := by
        have h0 := hnone 0 (by omega)
        rw [hfront] at h0
        exact Classical.byContradiction (fun h => h0 ⟨Nat.le_refl 0, h⟩)
      simp only
      have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
      have hb := topFreshTailCausalBadBorderBirthStep ring C s hn hbad Z
        (certSite s 0) hqueue ⟨0, by omega⟩ rfl rfl hE
      refine ⟨0, by omega, rfl, ?_, ?_⟩
      · rw [hb.1, hE]
        intro h
        cases h
      · intro f hf
        rw [hfront] at hf
        cases hf
  | some j =>
      obtain ⟨⟨hlo, hne⟩, hj, hmax⟩ := topFreshTailPrepaidSearchSome _ _ j hsearch
      simp only
      refine ⟨j, hj, rfl, ?_, ?_⟩
      · have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z
          hreach ⟨j, hj⟩
        have hxl : (Z.1.1 (certSite s j)).l = false := hgeo.1
        have hyl : (Z.1.1 (ring.rightNeighbor (certSite s j))).l = false := hgeo.2.1
        cases hq : (Z.1.1 (certSite s j)).qOut with
        | E => exact absurd hq hne
        | U =>
            rw [topFreshTailFifoUnreadSamples ring C Z (certSite s j) hxl hyl hq]
            intro h
            cases h
        | D v t =>
            by_cases hlast : j + 1 < topClockSpan n
            · have hyE : (Z.1.1 (ring.rightNeighbor (certSite s j))).qOut = .E := by
                rw [topFreshTailTicketNeighborSite]
                have h1 := hmax (j + 1) (by omega) hlast
                exact Classical.byContradiction (fun h => h1 ⟨by omega, h⟩)
              have hyb : (Z.1.1 (ring.rightNeighbor (certSite s j))).beta = false := by
                have h := hgeo.2.2.2
                have hc : ¬ ((⟨j, hj⟩ : Fin (topClockSpan n)).val + 1 = topClockSpan n) := by
                  show ¬ (j + 1 = topClockSpan n)
                  omega
                rw [if_neg hc] at h
                exact h
              have hmove := topFreshTailFifoDataMove ring (by omega) C Z (certSite s j)
                v t hxl hyl hq hyE hyb
              rw [hmove.1]
              cases t <;> intro h <;> cases h
            · have hsite : certSite s j = certSite s (topClockSpan n - 1) := by
                congr 1
                omega
              have hport := topFreshTailTicketPortRow ring C s hn hbad Z hreach
                (certSite s j) hsite v t hq
              rw [hport.2.1, hport.1, hfree.1, hfree.2]
              simp only [InTok.isE, QCarry.isOff, Bool.and_self, if_true]
              cases t <;> intro h <;> cases h
      · intro f hf
        rw [hf] at hlo
        exact hlo

/-- Section 6 item 7, nominated half. On a reached leaderless cut
whose history avoids a genuine tail, the nominated edge lowers Psi by at
least one unless its successor is a genuine tail: with a free border the
charged source service debits c* (and an acceptance is paid by its own
voucher); with a blocked border the P.2 frontier edge lowers W, records
no receipt and does not raise c*.
Consumer: topFreshTailJointAnchorCostFromReachedDrift
(Prob.costNumerator_le_of_nominated_edge). -/
theorem topFreshTailJointNominatedDrop
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hleader : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hfull : ∀ pre suffix : List (Fin n), pre ++ suffix = Z.2 →
      ¬ topClockGenuineTailAccepted C s (topFixedTraceRun ring C pre))
    (hng : ¬ topClockGenuineTailAccepted C s
      (topFixedTraceNext ring C Z (topFreshTailJointNominatedEdge ring C s Z))) :
    topFreshTailJointPotential ring C s
        (topFixedTraceNext ring C Z (topFreshTailJointNominatedEdge ring C s Z)) + 1 ≤
      topFreshTailJointPotential ring C s Z := by
  by_cases hfree : (Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
      (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF
  · simp only [topFreshTailJointNominatedEdge, if_pos hfree] at hng ⊢
    have hch := topFreshTailJointRightmostChargedEligible ring C s hn hbad Z
      hreach hfree
    have hstep := topFreshTailJointHistoryReserveStep ring C s hn hbad hleader
      Z hreach hfull (topFreshTailJointSourceEdge ring C s Z) hng
    rw [if_pos hch] at hstep
    exact hstep
  · simp only [topFreshTailJointNominatedEdge, if_neg hfree] at hng ⊢
    have hstep := topFreshTailPrepaidSourceContactStep ring C s hn hbad hleader
      Z hreach (topPortFrontierEdge s Z) hng
    have hW := topFreshTailJointBlockedPortFrontierDrop ring C s hbad Z hreach hfree
    have hcount := topFreshTailTicketReceiptCountStep ring C s Z
      (topPortFrontierEdge s Z)
    have hnone : topFreshTailGenealogyPortExport ring C s Z
        (topPortFrontierEdge s Z) = none := by
      cases hx : topFreshTailGenealogyPortExport ring C s Z
          (topPortFrontierEdge s Z) with
      | none => rfl
      | some x =>
          exfalso
          obtain ⟨_, _, hyi, hyc⟩ :=
            topFreshTailJointExportFree ring C s hn hbad Z hreach _ x hx
          exact hfree ⟨hyi, hyc⟩
    rw [hnone] at hcount
    have hR : topFreshTailPortReceiptCount s
          (topFixedTraceNext ring C Z (topPortFrontierEdge s Z)) =
        topFreshTailPortReceiptCount s Z := by
      rw [hcount]
      rfl
    unfold topFreshTailJointPotential
    rw [hR]
    omega

end L3

#print axioms L3.topFreshTailJointPrefixStep
#print axioms L3.topFreshTailJointPrefixFull
#print axioms L3.topFreshTailJointReceiptCap
#print axioms L3.topFreshTailJointPrepaidPos
#print axioms L3.topFreshTailJointHistoryReserveStep
#print axioms L3.topFreshTailJointRightmostChargedEligible
#print axioms L3.topFreshTailJointNominatedDrop
