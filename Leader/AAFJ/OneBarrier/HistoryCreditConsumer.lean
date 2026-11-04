import Leader.AAFJ.OneBarrier.ModeHistoryCredit

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.GenericOneBarrierHistoryCredit

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.SingleBarrierSanitation.DirtyTailBellman
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalUniqueLeaderCleanup
open AAFJPK.OriginalDangerousProbeChase
open AAFJPK.OriginalMultipleLeaderOneBarrier
open AAFJPK.SelectedMultipleUniqueSafe
open AAFJPK.OddZeroPhiFamily
open AAFJPK.OddZeroModeDebt
open AAFJPK.OriginalPhaseAwareMacroRank
open AAFJPK.OneBarrierModeRankConsumer
open AAFJPK.OneBarrierModeHistoryCredit
open AAFJPK.CenteredRenewal.OneBarrierCleanup

abbrev oddHk2 : 0 < 2 := AAFJPK.OddZeroPhiFamily.hk2
abbrev phaseHk2 : 0 < 2 := AAFJPK.OriginalPhaseAwareMacroRank.hk2
abbrev phaseRing3 : DirectedRing 3 := AAFJPK.OriginalPhaseAwareMacroRank.ring3

/-!
This file is the generic consumer layer for the five-coordinate certificate
introduced in `ZZAAFJOneBarrierModeHistoryCredit`:

`(PhiAt, historyCredit, zeroModeDebt, finiteModeRank, dirtyCtl)`.

The producer theorems in the repository are deliberately partial.  In
particular, the generic zero-birth producer does not expose the bullet frame
of its existential endpoint, and the generic safe-Unique producer exposes a
`CleanAt`/`terminalRank` branch rather than a history-credit conclusion.  The
theorems below retain those exact endpoint obligations instead of turning the
producer disjunctions into a total transition relation.
-/

/-! ## Small arithmetic facts used by the generic endpoint consumers -/

private theorem ofFn_sum_zero {m : Nat} (f : Fin m → Nat)
    (hf : ∀ i, f i = 0) : (List.ofFn f).sum = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons]
      have h0 : f 0 = 0 := hf 0
      have ht : (List.ofFn (fun i : Fin m => f i.succ)).sum = 0 := by
        apply ih
        intro i
        exact hf i.succ
      simp [h0, ht]

theorem bulletCredit_eq_zero_of_all_false
    {n k : Nat} (C : Fin n → State k)
    (hbullet : ∀ i, (C i).bullet = false) :
    bulletCredit C = 0 := by
  unfold bulletCredit
  apply ofFn_sum_zero
  intro i
  simp [hbullet i]

theorem historyCredit_eq_zero_of_all_false
    {n k : Nat} (C : Fin n → State k)
    (hbullet : ∀ i, (C i).bullet = false) :
    historyCredit C = 0 := by
  unfold historyCredit
  rw [bulletCredit_eq_zero_of_all_false C hbullet]
  simp

private theorem one_le_bitCount_of_true {n : Nat} (bits : Fin n → Bool)
    (i : Fin n) (hi : bits i = true) : 1 ≤ bitCount bits := by
  let after : Fin n → Bool := fun j => if j = i then false else bits j
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro j hji
    simp [after, hji])
  omega

private theorem two_le_bitCount_of_two_true {n : Nat}
    (bits : Fin n → Bool) (i j : Fin n) (hi : bits i = true)
    (hj : bits j = true) (hne : j ≠ i) :
    2 ≤ bitCount bits := by
  let after : Fin n → Bool := fun x => if x = i then false else bits x
  have hafterJ : after j = true := by simp [after, hne, hj]
  have hone := one_le_bitCount_of_true after j hafterJ
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro x hxi
    simp [after, hxi])
  omega

private theorem bitCount_false {n : Nat} :
    bitCount (fun _ : Fin n => false) = 0 := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
      rw [bitCount_succ]
      simp [ih]

private theorem leaderCount_eq_one_of_unique
    {n k : Nat} (C : Fin n → State k) (ell : Fin n)
    (hell : (C ell).leader = true)
    (hunique : ∀ i : Fin n, (C i).leader = true → i = ell) :
    leaderCount C = 1 := by
  let before : Fin n → Bool := fun _ => false
  let after : Fin n → Bool := fun i => (C i).leader
  have hbefore : before ell = false := by rfl
  have hafter : after ell = true := by simpa [after] using hell
  have hother : ∀ i, i ≠ ell → after i = before i := by
    intro i hne
    by_cases hi : (C i).leader = false
    · simp [after, before, hi]
    · have hit : (C i).leader = true := by
        cases h : (C i).leader <;> simp_all
      exact False.elim (hne (hunique i hit))
  have h := bitCount_single_birth before after ell hbefore hafter hother
  have hzero : bitCount before = 0 := by
    simpa [before] using (bitCount_false (n := n))
  unfold leaderCount
  change bitCount after = 1
  simpa [hzero] using h

private theorem leaderCount_ge_two_of_multiple
    {n k : Nat} (C : Fin n → State k)
    (hmultiple : AAFJPK.OriginalMultipleLeaderOneBarrier.MultipleLeaders C) :
    2 ≤ leaderCount C := by
  rcases hmultiple with ⟨i, j, hij, hi, hj⟩
  unfold leaderCount
  exact two_le_bitCount_of_two_true
    (fun q => (C q).leader) i j hi hj hij.symm

private theorem leaderCount_ge_two_of_dangerous_multiple
    {n k : Nat} (C : Fin n → State k)
    (hmultiple : AAFJPK.OriginalDangerousProbeChase.MultipleLeaders C) :
    2 ≤ leaderCount C := by
  rcases hmultiple with ⟨i, j, hij, hi, hj⟩
  unfold leaderCount
  exact two_le_bitCount_of_two_true
    (fun q => (C q).leader) i j hi hj hij.symm

private theorem leaderCount_pos_of_leader
    {n k : Nat} (C : Fin n → State k) (ell : Fin n)
    (hell : (C ell).leader = true) :
    0 < leaderCount C := by
  have h := one_le_bitCount_of_true
    (fun i : Fin n => (C i).leader) ell hell
  unfold leaderCount
  omega

private theorem zeroModeDebt_eq_zero_of_leader
    {n k : Nat} (C : Fin n → State k) (ell : Fin n)
    (hell : (C ell).leader = true) :
    zeroModeDebt C = 0 := by
  have hpos := leaderCount_pos_of_leader C ell hell
  simp [zeroModeDebt, Nat.ne_of_gt hpos]

private theorem zeroModeDebt_eq_zero_of_multiple
    {n k : Nat} (C : Fin n → State k)
    (hmultiple : AAFJPK.OriginalMultipleLeaderOneBarrier.MultipleLeaders C) :
    zeroModeDebt C = 0 := by
  have hpos : 0 < leaderCount C := by
    have htwo := leaderCount_ge_two_of_multiple C hmultiple
    omega
  simp [zeroModeDebt, Nat.ne_of_gt hpos]

/-! ## Explicit lexicographic constructors -/

private theorem lexNat_lt {a b : Nat} {as bs : List Nat}
    (h : a < b) : lexNat (a :: as) (b :: bs) = true := by
  simp [lexNat, h]

theorem historyModeDrop_of_phi_eq_credit_eq_debt_lt
    {n k : Nat} (ring : DirectedRing n)
    (b b' : Fin n) (C D : Fin n → State k)
    (hphi : PhiAt ring b' D = PhiAt ring b C)
    (hcredit : historyCredit D = historyCredit C)
    (hdebt : zeroModeDebt D < zeroModeDebt C) :
    HistoryModeDrop ring b C b' D := by
  unfold HistoryModeDrop historyModeList
  simp [lexNat, hphi, hcredit, hdebt]

theorem historyModeDrop_of_phi_lt
    {n k : Nat} (ring : DirectedRing n)
    (b b' : Fin n) (C D : Fin n → State k)
    (hphi : PhiAt ring b' D < PhiAt ring b C) :
    HistoryModeDrop ring b C b' D := by
  unfold HistoryModeDrop historyModeList
  simp [lexNat, hphi]

theorem historyModeDrop_of_phi_le_credit_le_debt_eq_mode_lt
    {n k : Nat} (ring : DirectedRing n)
    (b b' : Fin n) (C D : Fin n → State k)
    (hphi : PhiAt ring b' D ≤ PhiAt ring b C)
    (hcredit : historyCredit D ≤ historyCredit C)
    (hdebt : zeroModeDebt D = zeroModeDebt C)
    (hmode : finiteModeRank ring b' D < finiteModeRank ring b C) :
    HistoryModeDrop ring b C b' D := by
  unfold HistoryModeDrop historyModeList
  by_cases hphi_lt : PhiAt ring b' D < PhiAt ring b C
  · exact lexNat_lt hphi_lt
  · have hphi_eq : PhiAt ring b' D = PhiAt ring b C := by omega
    by_cases hcredit_lt : historyCredit D < historyCredit C
    · simp [lexNat, hphi_eq, hcredit_lt]
    · have hcredit_eq : historyCredit D = historyCredit C := by omega
      simp [lexNat, hphi_eq, hcredit_eq, hdebt, hmode]

/-! ## The exact-family odd zero producer

`oddZero_selected_birth_decreases` is genuinely generic in the odd family.
Its existential endpoint does not carry a bullet frame, so the history
consumer takes precisely that missing frame as an explicit endpoint premise.
This is the strongest rank statement justified by the current producer API.
-/

theorem oddZero_source_historyCredit_zero
    {m : Nat} (hm : 1 ≤ m) :
    historyCredit (oddZero m) = 0 := by
  exact historyCredit_eq_zero_of_all_false _ (fun i => rfl)

theorem oddZero_selected_birth_history_drop_of_bullet_free_endpoint
    {m : Nat} (hm : 1 ≤ m)
    {w : List (Fin (2 * m + 1))} {b' ell : Fin (2 * m + 1)}
    (hw : w.length ≤ (2 * m + 1) + 2)
    (hB : OneBarrierAt oddHk2 (oddRing m)
      (rawRun oddHk2 (oddRing m) (oddZero m) w) b')
    (hphi : PhiAt (oddRing m) b'
      (rawRun oddHk2 (oddRing m) (oddZero m) w) = 1)
    (hunique : UniqueLeaderAt
      (rawRun oddHk2 (oddRing m) (oddZero m) w) ell)
    (hbullet : ∀ i,
      (rawRun oddHk2 (oddRing m) (oddZero m) w i).bullet = false) :
    HistoryModeDrop (oddRing m) (oddTail m) (oddZero m)
      b' (rawRun oddHk2 (oddRing m) (oddZero m) w) := by
  have hcredit : historyCredit
      (rawRun oddHk2 (oddRing m) (oddZero m) w) =
      historyCredit (oddZero m) := by
    rw [historyCredit_eq_zero_of_all_false _ hbullet,
      oddZero_source_historyCredit_zero hm]
  have hdebtC := oddZero_source_mode_debt hm
  have hdebtD := zeroModeDebt_eq_zero_of_leader
    (rawRun oddHk2 (oddRing m) (oddZero m) w) ell hunique.1
  have hdebt : zeroModeDebt
      (rawRun oddHk2 (oddRing m) (oddZero m) w) <
      zeroModeDebt (oddZero m) := by
    rw [hdebtD, hdebtC]
    omega
  have hphiC : PhiAt (oddRing m) (oddTail m) (oddZero m) = 1 :=
    oddZero_phi_one hm
  exact historyModeDrop_of_phi_eq_credit_eq_debt_lt
    (oddRing m) (oddTail m) b' (oddZero m)
    (rawRun oddHk2 (oddRing m) (oddZero m) w)
    (hphi.trans hphiC.symm) hcredit hdebt

theorem oddZero_selected_birth_history_consumer
    {m : Nat} (hm : 1 ≤ m) :
    ∀ {w : List (Fin (2 * m + 1))} {b' ell : Fin (2 * m + 1)},
      w.length ≤ (2 * m + 1) + 2 →
      OneBarrierAt oddHk2 (oddRing m)
        (rawRun oddHk2 (oddRing m) (oddZero m) w) b' →
      PhiAt (oddRing m) b'
        (rawRun oddHk2 (oddRing m) (oddZero m) w) = 1 →
      UniqueLeaderAt
        (rawRun oddHk2 (oddRing m) (oddZero m) w) ell →
      (∀ i, (rawRun oddHk2 (oddRing m) (oddZero m) w i).bullet = false) →
      HistoryModeDrop (oddRing m) (oddTail m) (oddZero m)
        b' (rawRun oddHk2 (oddRing m) (oddZero m) w) := by
  intro w b' ell hw hB hphi hunique hbullet
  exact oddZero_selected_birth_history_drop_of_bullet_free_endpoint
    hm hw hB hphi hunique hbullet

/-! ## Generic dangerous and selected-multiple consumers -/

theorem dangerous_macro_history_consumer
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b l p : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hunique : UniqueLeaderAt C l)
    (hprobe : (cutView ring b C p).probe = true)
    (hshield : ¬ Shielded (cutView ring b C) p)
    (hcredit : historyCredit
      (rawRun hk ring C (macroWord ring b p)) ≤ historyCredit C)
    (hphi : PhiAt ring (macroBarrier hk ring C b p)
      (rawRun hk ring C (macroWord ring b p)) ≤ PhiAt ring b C) :
    OneBarrierAt hk ring (rawRun hk ring C (macroWord ring b p))
        (macroBarrier hk ring C b p) ∧
      HistoryModeDrop ring b C (macroBarrier hk ring C b p)
        (rawRun hk ring C (macroWord ring b p)) := by
  have hmacro := dangerous_probe_macro hk ring hn3 hndvd C b l p
    hB hunique.1 hprobe hshield
  have hsourceDanger : Dangerous (cutView ring b C) :=
    ⟨p, hprobe, hshield⟩
  have hcountC := leaderCount_eq_one_of_unique C l hunique.1 hunique.2
  have hdebtC := zeroModeDebt_eq_zero_of_leader C l hunique.1
  have hmodeC : finiteModeRank ring b C = 2 := by
    simp [finiteModeRank, hcountC, hsourceDanger]
  have hBmacro : OneBarrierAt hk ring
      (rawRun hk ring C (macroWord ring b p))
      (macroBarrier hk ring C b p) := by
    simpa using hmacro.1
  refine ⟨hBmacro, ?_⟩
  rcases hmacro.2 with hmultiple | hphilt
  · have hcountD : 2 ≤ leaderCount
        (rawRun hk ring C (macroWord ring b p)) :=
      leaderCount_ge_two_of_dangerous_multiple _ hmultiple
    have hdebtD := zeroModeDebt_eq_zero_of_multiple _
      (by
        rcases hmultiple with ⟨i, j, hij, hi, hj⟩
        exact ⟨i, j, hij, hi, hj⟩ :
          AAFJPK.OriginalMultipleLeaderOneBarrier.MultipleLeaders
            (rawRun hk ring C (macroWord ring b p)))
    have hmodeD : finiteModeRank ring (macroBarrier hk ring C b p)
        (rawRun hk ring C (macroWord ring b p)) = 1 := by
      have hne : leaderCount
          (rawRun hk ring C (macroWord ring b p)) ≠ 1 := by omega
      simp [finiteModeRank, hne]
    exact historyModeDrop_of_phi_le_credit_le_debt_eq_mode_lt
      ring b (macroBarrier hk ring C b p)
      C (rawRun hk ring C (macroWord ring b p))
      hphi hcredit (hdebtD.trans hdebtC.symm)
      (by rw [hmodeD, hmodeC]; omega)
  · exact historyModeDrop_of_phi_lt ring b (macroBarrier hk ring C b p)
      C (rawRun hk ring C (macroWord ring b p)) hphilt

theorem selected_multiple_unique_safe_history_consumer
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hmultiple : AAFJPK.OriginalMultipleLeaderOneBarrier.MultipleLeaders C) :
    ∀ (hunique : ∃ ell, UniqueLeaderAt
      (rawRun hk ring (rawRun hk ring C (parkedSweepWord ring b))
        (endpointDischargeWord (rawRun hk ring C (parkedSweepWord ring b)) b)) ell),
      let S := rawRun hk ring C (parkedSweepWord ring b)
      let D := rawRun hk ring S (endpointDischargeWord S b)
      let b' := endpointDischargeBarrier ring S b
      OneBarrierAt hk ring D b' ∧
        HistoryModeDrop ring b C b' D := by
  intro hunique
  let S := rawRun hk ring C (parkedSweepWord ring b)
  let D := rawRun hk ring S (endpointDischargeWord S b)
  let b' := endpointDischargeBarrier ring S b
  have hphi := multiple_selected_unique_endpoint_phi_drop
    hk ring hn3 hndvd C b hB hmultiple hunique
  have hS := parked_sweep_original_sterile hk ring (by omega) C b
    hndvd hB
  have hB' : OneBarrierAt hk ring D b' := by
    cases hprobeS : (S b).probe with
    | false =>
        have hD : D = S := by
          simp [D, S, endpointDischargeWord, hprobeS, rawRun]
        have hb' : b' = b := by
          simp [b', endpointDischargeBarrier, hprobeS]
        simpa [hD, hb'] using hS.1
    | true =>
        cases hphaseS : (S b).phase with
        | false =>
            have hnot : ¬ AAFJPK.BarrierAlgebra.AdvanceReady hk ring S b := by
              intro hready
              exact Bool.noConfusion (hready.2.1.symm.trans hphaseS)
            have hstep :=
              AAFJPK.SingleBarrierSanitation.oneBarrierAt_step
                hk ring (by omega) S b b hndvd hS.1
            have hD : D = (protocol k hk).step ring S b := by
              simp [D, endpointDischargeWord, hprobeS, rawRun]
              rfl
            have hb' : b' = b := by
              simp [b', endpointDischargeBarrier, hprobeS, hphaseS]
            simpa [hD, hb', hnot] using hstep
        | true =>
            have hbar : IsBarrier hk (S b) (S (ring.rightNeighbor b)) :=
              (barrierAt_labelsOf_iff hk ring S b).mp ((hS.1 b).2 rfl)
            have hhead : (S (ring.rightNeighbor b)).probe = false :=
              hS.2.1 _ (rightNeighbor_ne_self ring (by omega) b)
            have hready : AAFJPK.BarrierAlgebra.AdvanceReady hk ring S b :=
              ⟨hbar, hphaseS, hhead⟩
            have hstep :=
              AAFJPK.SingleBarrierSanitation.oneBarrierAt_step
                hk ring (by omega) S b b hndvd hS.1
            have hD : D = (protocol k hk).step ring S b := by
              simp [D, endpointDischargeWord, hprobeS, rawRun]
              rfl
            have hb' : b' = ring.rightNeighbor b := by
              simp [b', endpointDischargeBarrier, hprobeS, hphaseS]
            simpa [hD, hb', hready] using hstep
  refine ⟨?_, ?_⟩
  · exact hB'
  · exact historyModeDrop_of_phi_lt ring b b' C D hphi

/-! ## Generic dirty-tail service interface -/

theorem dirty_tail_history_consumer
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hphi : PhiAt ring b C = 1)
    (hbullet : (C b).bullet = true)
    (hcredit : historyCredit
      (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
      historyCredit C)
    (hdebt : zeroModeDebt
      (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
      zeroModeDebt C)
    (hmode : finiteModeRank ring b
      (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
      finiteModeRank ring b C) :
    OneBarrierAt hk ring
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) b ∧
      HistoryModeDrop ring b C b
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) := by
  obtain ⟨hword, hB', hphiD, hclear, hleader⟩ :=
    dirtyTail_two_incoming_clear hk ring hn3 hndvd C b hB hphi hbullet
  have hDdirty : dirtyCtl
      (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) b <
      dirtyCtl C b := by
    have hclear' :
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b] b).bullet =
          false := by simpa only [rawRun] using hclear
    simp only [dirtyCtl, hclear', hbullet, Bool.false_eq_true, if_false,
      if_true]
    omega
  refine ⟨hB', ?_⟩
  unfold HistoryModeDrop historyModeList
  have hphiEq : PhiAt ring b
      (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
      PhiAt ring b C := hphiD.trans hphi.symm
  simp [lexNat, hphiEq, hcredit, hdebt, hmode, hDdirty]

/-! ## The generic safe-Unique edge remains genuinely smaller than the API

The next fixture is a source-grounded Protocol-6 counterexample to the
unconditional generic claim that the non-dangerous Unique branch always pays
the history bit.  The unique leader itself carries a live bullet through the
exact `uniqueLeader_progress` word `[2,0,0,2]`; the endpoint still has that
bullet, so its history credit is unchanged.  Thus a generic safe-cleanup
theorem needs an additional endpoint control (for example the bullet-free
endpoint premise in the odd-zero consumer), or a new producer theorem.
-/

def SafeUniqueTailBullet (i : Fin 3) : State 2 :=
  if i = 0 then q false false 0 false false
  else if i = 1 then q false false 1 false false
  else q true true 0 false false

def SafeUniqueTailBulletEndpoint : Fin 3 → State 2 :=
  rawRun phaseHk2 phaseRing3 SafeUniqueTailBullet [2, 0, 0, 2]

theorem generic_safe_cleanup_history_counterexample :
    OneBarrierAt phaseHk2 phaseRing3 SafeUniqueTailBullet 2 ∧
      UniqueLeaderAt SafeUniqueTailBullet 2 ∧
      ¬ Dangerous (cutView phaseRing3 2 SafeUniqueTailBullet) ∧
      historyCredit SafeUniqueTailBullet = 1 ∧
      SafeUniqueTailBulletEndpoint =
        rawRun phaseHk2 phaseRing3 SafeUniqueTailBullet [2, 0, 0, 2] ∧
      OneBarrierAt phaseHk2 phaseRing3 SafeUniqueTailBulletEndpoint 0 ∧
      UniqueLeaderAt SafeUniqueTailBulletEndpoint 2 ∧
      historyCredit SafeUniqueTailBulletEndpoint = 1 ∧
      ¬ historyCredit SafeUniqueTailBulletEndpoint <
        historyCredit SafeUniqueTailBullet := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-! The four producer interfaces above are the maximal generic subgraph
currently exposed by the accepted source modules.  The final conjunct is
deliberately a counterexample-shaped gap statement, not a totality claim. -/

theorem maximal_generic_one_barrier_subgraph_strict_rank :
    (∀ {m : Nat} (hm : 1 ≤ m)
      {w : List (Fin (2 * m + 1))} {b' ell : Fin (2 * m + 1)},
      w.length ≤ (2 * m + 1) + 2 →
      OneBarrierAt oddHk2 (oddRing m)
        (rawRun oddHk2 (oddRing m) (oddZero m) w) b' →
      PhiAt (oddRing m) b'
        (rawRun oddHk2 (oddRing m) (oddZero m) w) = 1 →
      UniqueLeaderAt
        (rawRun oddHk2 (oddRing m) (oddZero m) w) ell →
      (∀ i, (rawRun oddHk2 (oddRing m) (oddZero m) w i).bullet = false) →
      HistoryModeDrop (oddRing m) (oddTail m) (oddZero m)
        b' (rawRun oddHk2 (oddRing m) (oddZero m) w)) ∧
    (∀ {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
      (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
      (C : Fin n → State k) (b l p : Fin n)
      (hB : OneBarrierAt hk ring C b)
      (hunique : UniqueLeaderAt C l)
      (hprobe : (cutView ring b C p).probe = true)
      (hshield : ¬ Shielded (cutView ring b C) p)
      (hcredit : historyCredit
        (rawRun hk ring C (macroWord ring b p)) ≤ historyCredit C)
      (hphi : PhiAt ring (macroBarrier hk ring C b p)
        (rawRun hk ring C (macroWord ring b p)) ≤ PhiAt ring b C),
      HistoryModeDrop ring b C (macroBarrier hk ring C b p)
        (rawRun hk ring C (macroWord ring b p))) ∧
    (∀ {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
      (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
      (C : Fin n → State k) (b : Fin n)
      (hB : OneBarrierAt hk ring C b)
      (hmultiple : AAFJPK.OriginalMultipleLeaderOneBarrier.MultipleLeaders C)
      (hunique : ∃ ell, UniqueLeaderAt
        (rawRun hk ring (rawRun hk ring C (parkedSweepWord ring b))
          (endpointDischargeWord
            (rawRun hk ring C (parkedSweepWord ring b)) b)) ell),
      let S := rawRun hk ring C (parkedSweepWord ring b)
      let D := rawRun hk ring S (endpointDischargeWord S b)
      let b' := endpointDischargeBarrier ring S b
      HistoryModeDrop ring b C b' D) ∧
    (∀ {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
      (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
      (C : Fin n → State k) (b : Fin n)
      (hB : OneBarrierAt hk ring C b)
      (hphi : PhiAt ring b C = 1)
      (hbullet : (C b).bullet = true)
      (hcredit : historyCredit
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
        historyCredit C)
      (hdebt : zeroModeDebt
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
        zeroModeDebt C)
      (hmode : finiteModeRank ring b
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b]) =
        finiteModeRank ring b C),
      HistoryModeDrop ring b C b
        (rawRun hk ring C [ring.leftNeighbor b, ring.leftNeighbor b])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm w b' ell hw hB hphi hunique hbullet
    exact oddZero_selected_birth_history_drop_of_bullet_free_endpoint
      hm hw hB hphi hunique hbullet
  · intro n k hk ring hn3 hndvd C b l p hB hunique hprobe hshield
      hcredit hphi
    exact (dangerous_macro_history_consumer hk ring hn3 hndvd C b l p
      hB hunique hprobe hshield hcredit hphi).2
  · intro n k hk ring hn3 hndvd C b hB hmultiple hunique
    dsimp
    exact (selected_multiple_unique_safe_history_consumer
      hk ring hn3 hndvd C b hB hmultiple hunique).2
  · intro n k hk ring hn3 hndvd C b hB hphi hbullet hcredit hdebt hmode
    exact (dirty_tail_history_consumer hk ring hn3 hndvd C b hB hphi
      hbullet hcredit hdebt hmode).2

#print axioms bulletCredit_eq_zero_of_all_false
#print axioms oddZero_selected_birth_history_drop_of_bullet_free_endpoint
#print axioms dangerous_macro_history_consumer
#print axioms selected_multiple_unique_safe_history_consumer
#print axioms dirty_tail_history_consumer
#print axioms generic_safe_cleanup_history_counterexample
#print axioms maximal_generic_one_barrier_subgraph_strict_rank

end AAFJPK.GenericOneBarrierHistoryCredit
