import Leader.L3.StageM.EntryRun

/-!
# The strict cohort packed at its targets at the tail export (F1, old half)

At the letter right after the export of the strict cohort's tail sample (`tau = tx + 1`), the
target cell `R + m` holds the strict atom `a_m` (the sample read at source cell `m`), as a pending
or settled input with the tail bit `m = 0`, not live, and the settled cells form a top run
(`CohortArrived`, `CohortSettledTop`): `wPackedAtExport`. This module holds the cell rows and the
strict carry chain; the tracking lemmas and `wPackedAtExport` itself are in `L3.StageMEntryPack`.

Route (2026-11-02 11:17 handover, research/lean-l3/ledgers/stage-m-notes.md, item 2):

* operands: use `m` of the strict ledger reads the input of `R + m` one letter before it
  (`wCarryChain`: the carry chain of `L3.DigitEntryBridge.carryChain` with the operand of every
  use; a success also needs a settled, carry-free input there);
* positions: backward from its use, `a_m` sits in `[R, R + m]` at every letter after `tau`
  (`wBackRange`: a strict atom never re-enters the source, `exportUnique`'s clause of
  `GhostCorrDistinct`), so at `tau` the `R` atoms fill the `R` target cells in order;
* shapes: a target cell that is `X` or live keeps that shape while it keeps its ghost
  (`tgtOtherKeep`), so the settled, carry-free use cell was pending or settled already at `tau`;
* settled top: a settled cell `q` at `tau` became settled at some letter `f` (`R + m` ≠ the cell of
  `a_m` at its export), which needs a settled cell `q + 1` (`tgtSettledForm`); that cell holds
  `a_{m+1}` from `f` to `tau` (`wPassStep`), so its tail bit is `false`, and it stays settled while
  `q` is settled (`tgtSettledTopKeep`).
-/

namespace L3.StageMEntryCarryRows

set_option autoImplicit false
set_option linter.unusedSectionVars false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
open L3.WidthPacketMomentGroupCompletion
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.ValueLedger
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.SitePin
open L3.DigitEntryPhase
open L3.StageMEntryRun

/-! ### Row tables of one target edge -/

section Tables

variable {n : Nat}

/-- A live or tombstone left cell loses its ghost. Consumer: `tgtOtherKeep`. -/
theorem finXOther (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi : Option (DigitAtom n)) (h : cohortTokIn ix kx = .other) :
    finInX bx ix kx iy ky gxi = none := by
  cases kx <;> cases ix <;> simp_all [cohortTokIn, finInX]

/-- Consumer: `tgtOtherKeep`. -/
theorem termOther (ix : BankRepairDigitInSh) (kx : Bool) (gxi : Option (DigitAtom n))
    (h : cohortTokIn ix kx = .other) : ghostTermIn ix kx gxi = none := by
  cases kx <;> cases ix <;> simp_all [cohortTokIn, ghostTermIn]

/-- A live or tombstone delimiter input that keeps a ghost stays live or tombstone. Consumer:
`tgtOtherKeep`. -/
theorem delOther (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (b : DigitAtom n)
    (h : cohortTokIn iy ky = .other) (hb : (ghostDel stamp ox iy ky gxo gyi).2 = some b) :
    cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
      .other := by
  cases ky <;> cases iy <;> cases ox <;> simp_all [cohortTokIn, ghostDel, bankRepairDigitDelStep]

/-- A live or tombstone right input that keeps a ghost stays live or tombstone. Consumer:
`tgtOtherKeep`. -/
theorem finYOther (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi : Option (DigitAtom n)) (b : DigitAtom n)
    (h : cohortTokIn iy ky = .other) (hb : finInY ix kx iy ky gxi gyi = some b) :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .other := by
  cases ky <;> cases iy <;> cases kx <;> cases ix <;> cases bx <;>
    simp_all [cohortTokIn, finInY, finInYFree, finYX, finYP, shS, bankRepairDigitFinStep] <;>
    (repeat' split) <;> simp_all

/-- A settled left cell that stays settled keeps its ghost. Consumer: `tgtSettledKeep`. -/
theorem finXSettled (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi : Option (DigitAtom n)) (T T' : Bool) (h : cohortTokIn ix kx = .settled T)
    (h' : cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
      (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .settled T') :
    finInX bx ix kx iy ky gxi = gxi := by
  obtain ⟨rfl, rfl⟩ := tokInSettled h
  cases bx <;> cases ky <;> cases T <;> simp_all [cohortTokIn, finInX, bankRepairDigitFinStep]

/-- Consumer: `tgtSettledKeep`. -/
theorem termSettled (ix : BankRepairDigitInSh) (kx : Bool) (gxi : Option (DigitAtom n)) (T : Bool)
    (h : cohortTokIn ix kx = .settled T) : ghostTermIn ix kx gxi = gxi := by
  obtain ⟨rfl, rfl⟩ := tokInSettled h
  simp [ghostTermIn]

/-- Consumer: `tgtSettledKeep`. -/
theorem delSettled (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (T : Bool)
    (h : cohortTokIn iy ky = .settled T) : (ghostDel stamp ox iy ky gxo gyi).2 = gyi := by
  obtain ⟨rfl, rfl⟩ := tokInSettled h
  cases ox <;> simp [ghostDel]

/-- A settled right input that stays settled keeps its ghost. Consumer: `tgtSettledKeep`. -/
theorem finYSettled (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi : Option (DigitAtom n)) (T T' : Bool)
    (h : cohortTokIn iy ky = .settled T)
    (h' : cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .settled T') :
    finInY ix kx iy ky gxi gyi = gyi := by
  obtain ⟨rfl, rfl⟩ := tokInSettled h
  cases kx <;> cases ix <;> cases bx <;>
    simp_all [cohortTokIn, finInY, finInYFree, finYX, finYP, shS, bankRepairDigitFinStep] <;>
    (repeat' split) <;> simp_all

/-- A right input becomes settled only if it was settled. Consumer: `tgtSettledForm`. -/
theorem finYNewSettled (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) (T : Bool)
    (h' : cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .settled T) :
    cohortTokIn iy ky = .settled T := by
  cases ky <;> cases iy <;> cases kx <;> cases ix <;> cases bx <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep] <;> (repeat' split) <;> simp_all

/-- A left input becomes settled only below a settled right input. Consumer:
`tgtSettledForm`. -/
theorem finXNewSettled (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky : Bool) (T : Bool)
    (hold : ∀ T', cohortTokIn ix kx ≠ .settled T')
    (h' : cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
      (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .settled T) :
    ∃ T', cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .settled T' := by
  cases ky <;> cases iy <;> cases kx <;> cases ix <;> cases bx <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep] <;> (repeat' split) <;> simp_all

/-- A settled left cell keeps a settled, tail-free right cell. Consumer: `tgtSettledTopKeep`. -/
theorem finTopKeep (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (T : Bool) (hx : cohortTokIn ix kx = .settled T)
    (hy : cohortTokIn iy ky = .settled false) :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
      (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .settled false := by
  obtain ⟨rfl, rfl⟩ := tokInSettled hx
  obtain ⟨rfl, rfl⟩ := tokInSettled hy
  cases bx <;> cases T <;> simp [cohortTokIn, bankRepairDigitFinStep]

/-- A settled tail-free left cell off the delimiter stays settled. Consumer:
`tgtSettledTopKeep`. -/
theorem finXKeepFalse (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (hx : cohortTokIn ix kx = .settled false) :
    cohortTokIn (bankRepairDigitFinStep false ix kx iy ky).1
      (bankRepairDigitFinStep false ix kx iy ky).2.1 = .settled false := by
  obtain ⟨rfl, rfl⟩ := tokInSettled hx
  cases ky <;> simp [cohortTokIn, bankRepairDigitFinStep]

/-- Consumer: `tgtSettledTopKeep`. -/
theorem termKeepFalse (ix : BankRepairDigitInSh) (kx : Bool)
    (hx : cohortTokIn ix kx = .settled false) :
    cohortTokIn (cohortTermStep ix kx).1 (cohortTermStep ix kx).2 = .settled false := by
  obtain ⟨rfl, rfl⟩ := tokInSettled hx
  simp [cohortTokIn, cohortTermStep]

end Tables

/-! ### One letter on one target cell -/

section Cell

variable {n : Nat} {R : Nat} {s : CohortLane} {ke : Option Nat}
  {a a' : Nat → Option (DigitAtom n)} {stamp : DigitStamp n} {gxo : DigitOutGhost n}

/-- **A live or tombstone target cell that keeps a ghost stays live or tombstone.** Consumer:
`wOtherRun`. -/
theorem tgtOtherKeep (hR : 2 ≤ R) (hm : MoveH R s ke a a' stamp gxo) (q : Nat) (h1 : R ≤ q)
    (h2 : q < 2 * R) (hT : cohortTok R s q = .other) (b : DigitAtom n) (hb : a' q = some b) :
    cohortTok R (cohortLaneStep R s ke) q = .other := by
  cases ke with
  | none => exact hT
  | some k =>
    show cohortTok R (cohortEdge R s k) q = .other
    by_cases hkq : k = q
    · subst hkq
      by_cases hk1 : k + 1 < 2 * R
      · exfalso
        have hx := congrArg Prod.fst (hm.2.2.1 k rfl h1 hk1)
        simp only [ghostFinIn] at hx
        rw [cohortTokTgt s h1] at hT
        rw [finXOther _ _ _ _ _ _ hT, hb] at hx
        cases hx
      · exfalso
        have hk2 : k = 2 * R - 1 := by omega
        have hx := hm.2.2.2 (by rw [hk2])
        rw [← hk2] at hx
        rw [cohortTokTgt s h1] at hT
        rw [termOther _ _ _ hT] at hx
        rw [hb] at hx
        cases hx
    · by_cases hkq1 : k + 1 = q
      · by_cases hqR : q = R
        · have hk : k = R - 1 := by omega
          have hdel := hm.2.1 (by rw [hk])
          rw [hqR] at hb hT ⊢
          rw [hdel, ← hk] at hb
          have e := (cohortTokDel R k s (by omega)).2
          rw [show k + 1 = R by omega] at e
          rw [e]
          rw [cohortTokTgt s (Nat.le_refl R)] at hT
          exact delOther stamp _ _ _ gxo (a R) b hT hb
        · have hRk : R ≤ k := by omega
          have hy := congrArg Prod.snd (hm.2.2.1 k rfl hRk (by omega))
          simp only [ghostFinIn] at hy
          rw [hkq1, hb] at hy
          have e := (cohortTokFin R k s hRk (by omega)).2
          rw [hkq1] at e
          rw [e]
          rw [cohortTokTgt s h1] at hT
          exact finYOther _ _ _ _ _ _ _ b hT hy.symm
      · rw [cohortTokFrame R k q s (fun h => hkq h.symm) (fun h => hkq1 h.symm)]
        exact hT

/-- **A target cell settled before and after a letter keeps its ghost.** Consumer:
`wSettledGhost`. -/
theorem tgtSettledKeep (hm : MoveH R s ke a a' stamp gxo) (q : Nat) (h1 : R ≤ q)
    (h2 : q < 2 * R) (T T' : Bool) (hT : cohortTok R s q = .settled T)
    (hT' : cohortTok R (cohortLaneStep R s ke) q = .settled T') : a' q = a q := by
  cases ke with
  | none => exact hm.1 q h1 h2 (fun h => by cases h) (fun h => by cases h)
  | some k =>
    change cohortTok R (cohortEdge R s k) q = .settled T' at hT'
    by_cases hkq : k = q
    · subst hkq
      by_cases hk1 : k + 1 < 2 * R
      · have hx := congrArg Prod.fst (hm.2.2.1 k rfl h1 hk1)
        simp only [ghostFinIn] at hx
        rw [hx]
        rw [(cohortTokFin R k s h1 hk1).1] at hT'
        rw [cohortTokTgt s h1] at hT
        exact finXSettled _ _ _ _ _ _ T T' hT hT'
      · have hk2 : k = 2 * R - 1 := by omega
        have hx := hm.2.2.2 (by rw [hk2])
        rw [← hk2] at hx
        rw [hx]
        rw [cohortTokTgt s h1] at hT
        exact termSettled _ _ _ T hT
    · by_cases hkq1 : k + 1 = q
      · by_cases hqR : q = R
        · have hk : k = R - 1 := by omega
          have hdel := hm.2.1 (by rw [hk])
          rw [hqR] at hT ⊢
          rw [hdel]
          rw [cohortTokTgt s (Nat.le_refl R)] at hT
          exact delSettled stamp _ _ _ gxo (a R) T hT
        · have hRk : R ≤ k := by omega
          have hy := congrArg Prod.snd (hm.2.2.1 k rfl hRk (by omega))
          simp only [ghostFinIn] at hy
          rw [hkq1] at hy
          rw [hy]
          have e := (cohortTokFin R k s hRk (by omega)).2
          rw [hkq1] at e
          rw [e] at hT'
          rw [cohortTokTgt s h1] at hT
          exact finYSettled _ _ _ _ _ _ _ T T' hT hT'
      · exact hm.1 q h1 h2 (fun h => hkq (Option.some.inj h))
          (fun h => by have := Option.some.inj h; omega)

/-- **A target cell becomes settled only below a settled cell.** Consumer: `wSettledTop`. -/
theorem tgtSettledForm (q : Nat) (h1 : R < q) (h2 : q + 1 < 2 * R)
    (hold : ∀ T, cohortTok R s q ≠ .settled T) (T : Bool)
    (hnew : cohortTok R (cohortLaneStep R s ke) q = .settled T) :
    ∃ T', cohortTok R (cohortLaneStep R s ke) (q + 1) = .settled T' := by
  cases ke with
  | none => exact absurd hnew (hold T)
  | some k =>
    change cohortTok R (cohortEdge R s k) q = .settled T at hnew
    show ∃ T', cohortTok R (cohortEdge R s k) (q + 1) = .settled T'
    rw [cohortTokTgt s (by omega)] at hold
    by_cases hkq : k = q
    · subst hkq
      have e := cohortTokFin R k s (by omega) h2
      rw [e.1] at hnew
      rw [e.2]
      exact finXNewSettled _ _ _ _ _ T hold hnew
    · by_cases hkq1 : k + 1 = q
      · exfalso
        have e := (cohortTokFin R k s (by omega) (by omega)).2
        rw [hkq1] at e
        rw [e] at hnew
        exact hold T (finYNewSettled _ _ _ _ _ T hnew)
      · exfalso
        rw [cohortTokFrame R k q s (fun h => hkq h.symm) (fun h => hkq1 h.symm),
          cohortTokTgt s (by omega)] at hnew
        exact hold T hnew

/-- **A settled cell keeps a settled, tail-free cell above it.** Consumer: `wSettledTop`. -/
theorem tgtSettledTopKeep (q : Nat) (h1 : R < q) (h2 : q + 1 < 2 * R) (T : Bool)
    (hx : cohortTok R s q = .settled T) (hy : cohortTok R s (q + 1) = .settled false) :
    cohortTok R (cohortLaneStep R s ke) (q + 1) = .settled false := by
  cases ke with
  | none => exact hy
  | some k =>
    show cohortTok R (cohortEdge R s k) (q + 1) = .settled false
    rw [cohortTokTgt s (by omega)] at hx
    rw [cohortTokTgt s (by omega)] at hy
    by_cases hkq : k = q
    · subst hkq
      rw [(cohortTokFin R k s (by omega) h2).2]
      exact finTopKeep _ _ _ _ _ T hx hy
    · by_cases hkq1 : k = q + 1
      · subst hkq1
        by_cases h3 : q + 1 + 1 < 2 * R
        · rw [(cohortTokFin R (q + 1) s (by omega) h3).1]
          have hb : decide (q + 1 = R) = false := decide_eq_false (by omega)
          rw [hb]
          exact finXKeepFalse _ _ _ _ hy
        · rw [cohortTokTerm R (q + 1) s (by omega)]
          exact termKeepFalse _ _ hy
      · rw [cohortTokFrame R k (q + 1) s (fun h => hkq1 h.symm) (fun h => hkq (by omega)),
          cohortTokTgt s (by omega)]
        exact hy

end Cell


/-! ### The right ledger of a success, with its operand -/

section CarryOp

variable {c : Compiled} {n : Nat}

/-- The right ledger of a replay is kept, or a success (live left carry, carry-free settled right
input) appends a use stamped by the letter that reads the right input. Consumer: `carryYDOp`. -/
theorem replayCarryYOp (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hlx : x.leader = false) (hly : y.leader = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry ∨
    (x.carryLive = true ∧ y.carryLive = false ∧ y.input.isS = true ∧
      ∃ u : DigitUse c n, u.time = time ∧ u.operand = gy.input ∧
      (digitLaneReplay lane time source destination x y gx gy).y.carry =
        some ⟨(L3.DigitEntryBridge.oldLedger ⟨time, source, lane⟩ gx.carry).inherited,
          (L3.DigitEntryBridge.oldLedger ⟨time, source, lane⟩ gx.carry).uses ++ [u]⟩) := by
  cases hxc : x.carryLive
  · exact Or.inl (replayCarryYKeep lane time source destination x y gx gy hlx hly hxc)
  · simp [digitLaneReplay, hlx, hly, hxc, L3.DigitEntryBridge.oldLedger]
    (repeat' split) <;> simp_all

/-- The right-cell ledger row of a Fin edge, with the operand of a success. Consumer:
`carryYRingOp`. -/
theorem carryYDOp (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false) :
    (laneGhost lane (digitService t e d X Y gx gy).y).carry = (laneGhost lane gy).carry ∨
    (bankRepairDigitLaneLive lane X.top = true ∧ bankRepairDigitLaneLive lane Y.top = false ∧
      (bankRepairDigitLaneIn lane Y.top).isS = true ∧
      ∃ u : DigitUse c n, u.time = t ∧ u.operand = (laneGhost lane gy).input ∧
      (laneGhost lane (digitService t e d X Y gx gy).y).carry =
        some ⟨(L3.DigitEntryBridge.oldLedger ⟨t, e, lane⟩ (laneGhost lane gx).carry).inherited,
          (L3.DigitEntryBridge.oldLedger ⟨t, e, lane⟩ (laneGhost lane gx).carry).uses ++ [u]⟩) := by
  have h := replayCarryYOp lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
  simp only [laneViewLive, laneViewIn] at h
  rw [serviceLaneY, serviceLane]
  exact h

/-- A settled input token. Consumer: `carryYRingOp`. -/
theorem isSSome {A : Nat} (i : InTok A) (h : i.isS = true) :
    ∃ T, bankRepairDigitInShOf i = .S T := by
  cases i with
  | S v T => exact ⟨T, rfl⟩
  | _ => simp [InTok.isS] at h

/-- The right ledger of a Fin edge on the ring, with the operand and the success shape.
Consumer: `wCarryOrigin`. -/
theorem carryYRingOp (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (lane : DigitLane) (A : DigitAudit c n) (k : Nat) (hRk : R ≤ k) (hk2 : k + 1 < 2 * R) :
    (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).carry =
      (laneCells ring root lane src A.current (k + 1)).carry ∨
    ((cohortProj ring root lane src R S).live k = true ∧
      (cohortProj ring root lane src R S).live (k + 1) = false ∧
      (∃ T, (cohortProj ring root lane src R S).inp (k + 1) = .S T) ∧
      ∃ u : DigitUse c n, u.time = A.clock + 1 ∧
      u.operand = (laneCells ring root lane src A.current (k + 1)).input ∧
      (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).carry =
        some ⟨(L3.DigitEntryBridge.oldLedger ⟨A.clock + 1, digitSite ring root (src + k), lane⟩
            (laneCells ring root lane src A.current k).carry).inherited,
          (L3.DigitEntryBridge.oldLedger ⟨A.clock + 1, digitSite ring root (src + k), lane⟩
            (laneCells ring root lane src A.current k).carry).uses ++ [u]⟩) := by
  have hy : laneCells ring root lane src
      (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
      laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
    unfold laneCells
    rw [show digitSite ring root (src + (k + 1)) =
      ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
  have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  rw [hy, projLive ring root lane src R S k hRk (by omega),
    projLive ring root lane src R S (k + 1) (by omega) hk2,
    projIn ring root lane src R S (k + 1) (by omega) hk2]
  rcases carryYDOp lane (A.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
    (A.current (digitSite ring root (src + k)))
    (A.current (digitSite ring root (src + k + 1))) hlx hly with h | ⟨h1, h2, h3, u, hu1, hu2, hu3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, isSSome _ h3, u, hu1, hu2, hu3⟩

end CarryOp

/-! ### The strict carry chain at a boundary reference, with operands -/

section Chain

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- **Ledger origin** of one coupled letter on a target cell: kept, launched at `R` (one use
reading the input of `R`), or a success from the cell below (one more use); new uses are stamped
by the letter; a success reads the settled, carry-free input of `q` (port of `carryOrigin` with
the operand). Consumer: `wCarryTB`, `wCarryBack`, `wCarryCreate`. -/
theorem wCarryOrigin (Base : Bool → DigitAtom n → Prop)
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1)
    (hc : GhostCorr ring root lane src R Base (piD (ref.phys z.1)) z.2) (e : Fin n)
    (q : Nat) (hRq : R ≤ q) (hq : q < 2 * R) (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hK : caA ring root lane src (widthDigitAuditNext ref.toWidthDigitReference z e).2 q = some K) :
    caA ring root lane src z.2 q = some K ∨
    (q = R ∧ cohortEdgeOf root src R e = some R ∧
      ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n, u.time = z.2.clock + 1 ∧
        u.operand = inA ring root lane src z.2 R ∧ K = ⟨none, [u]⟩) ∨
    (R < q ∧ cohortEdgeOf root src R e = some (q - 1) ∧
      (∃ T, cohortTok R (cohortProj ring root lane src R (piD (ref.phys z.1))) q = .settled T) ∧
      ∃ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n),
        caA ring root lane src z.2 (q - 1) = some L ∧ u.time = z.2.clock + 1 ∧
          u.operand = inA ring root lane src z.2 q ∧ K = ⟨L.inherited, L.uses ++ [u]⟩) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hbR hb2R
    hbF lane z.2 jx hj hbX hbY
  change (laneCells ring root lane src (digitAuditStep ring (piD (ref.phys z.1)) z.2
    (digitSite ring root jx)).current q).carry = some K at hK
  unfold caA inA
  rcases hke : cohortEdgeOf root src R (digitSite ring root jx) with _ | k
  · left
    have := congrArg DigitLaneGhost.carry (hrows.1 q hRq hq (by rw [hke]; simp) (by rw [hke]; simp))
    rw [this] at hK
    exact hK
  · have hjk := edgeOfSome ring root src R jx k hj hke
    by_cases hkq : k = q
    · subst hkq
      by_cases hk2 : k + 1 < 2 * R
      · obtain ⟨-, hX, -, -⟩ := hrows.2.2.1 k hke hRq hk2
        rcases hX with h | h | ⟨h1, -, u, hu1, hu2, hu3⟩
        · rw [h] at hK
          cases hK
        · left
          rw [← hK, h]
        · right; left
          rw [hu3] at hK
          refine ⟨h1, by rw [h1], u, hu1, by rw [hu2, h1], (Option.some.inj hK).symm⟩
      · have hkt : k = 2 * R - 1 := by omega
        obtain ⟨-, hX, -⟩ := hrows.2.2.2 (by rw [hke, hkt])
        rw [hkt] at hK ⊢
        rcases hX with h | h
        · rw [h] at hK
          cases hK
        · left
          rw [← hK, h]
    · by_cases hkq1 : k + 1 = q
      · subst hkq1
        by_cases hkR : k + 1 = R
        · have hk' : k = R - 1 := by omega
          obtain ⟨-, hcR⟩ := hrows.2.1 (by rw [hke, hk'])
          left
          rw [show k + 1 = R from hkR] at hK ⊢
          rw [← hK, hcR]
        · subst hjk
          rcases carryYRingOp ring (by omega) root (piD (ref.phys z.1)) R src hsrc hend hroot lane
            z.2 k (by omega) hq with h | ⟨hl, hl', ⟨T, hT⟩, u, hu1, hop, hu2⟩
          · left
            rw [← hK, h]
          · right; right
            obtain ⟨L, hLk⟩ : ∃ L, (laneCells ring root lane src z.2.current k).carry = some L := by
              have h3 := (hc.2 k (by omega) (by omega)).2
              rw [hl] at h3
              exact Option.isSome_iff_exists.mp h3.symm
            rw [hu2, hLk] at hK
            refine ⟨by omega, by simp, ⟨T, ?_⟩, L, u, by simp [hLk], hu1, hop, ?_⟩
            · rw [cohortTokTgt _ (by omega), hT, hl']
              rfl
            · exact (Option.some.inj hK).symm
      · left
        have := congrArg DigitLaneGhost.carry (hrows.1 q hRq hq
          (by rw [hke]; intro h; exact hkq (Option.some.inj h))
          (by rw [hke]; intro h; have := Option.some.inj h; omega))
        rw [this] at hK
        exact hK


include hn hR hsrc hend in
/-- The terminal receipt of the last pair edge records the live last cell's ledger (port of
`termLedger`). Consumer: `L3.StageMEntryCyc`. -/
theorem wTermLedger
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some (2 * R - 1))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : (digitReceiptLane lane (svcAt ring (piD (ref.phys z.1)) z.2 e)).terminal = some U) :
    (cohortProj ring root lane src R (piD (ref.phys z.1))).live (2 * R - 1) = true ∧
      U.ledger = caA ring root lane src z.2 (2 * R - 1) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hbR
    hb2R hbF lane z.2 jx hj hbX hbY
  exact (hrows.2.2.2 hke).2.2 U hU

include hn hR hsrc hend in
/-- The target-input rows of one coupled letter (`MoveH`). Consumer: `wSettledGhost`,
`wOtherRun`. -/
theorem wMoveH (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref.toWidthDigitReference root src R z.1) (e : Fin n) :
    MoveH R (cohortProj ring root lane src R (piD (ref.phys z.1))) (cohortEdgeOf root src R e)
      (inA ring root lane src z.2)
      (inA ring root lane src (widthDigitAuditNext ref.toWidthDigitReference z e).2)
      (DigitStamp.mk (z.2.clock + 1) e lane) ((laneCells ring root lane src z.2.current (R - 1)).out) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD (ref.phys z.1)) R src hR hsrc hend hroot hbR
    hb2R hbF lane z.2 jx hj hbX hbY
  exact ⟨fun q h1 h2 h3 h4 => congrArg DigitLaneGhost.input (hrows.1 q h1 h2 h3 h4),
    fun hk => (hrows.2.1 hk).1, fun k hk h1 h2 => (hrows.2.2.1 k hk h1 h2).1,
    fun hk => (hrows.2.2.2 hk).1⟩

variable (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : WidthRunInv ring ref root lane src R q0)
  (hi0 : q0.2 = digitAuditInitial (piD (ref.phys q0.1))) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 hi0 hc0 in
/-- Ledger uses on target cells are stamped no later than the prefix. Consumer:
`wCarryCreate`. -/
theorem wCarryTB : ∀ t, t ≤ W.length → ∀ q (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n),
    R ≤ q → q < 2 * R →
    caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2 q = some K →
    ∀ u, u ∈ K.uses → u.time ≤ t := by
  intro t
  induction t with
  | zero =>
    intro _ q K _ _ hK u hu
    exfalso
    have h0 : (wRunAt ref.toWidthDigitReference q0 W 0).2 =
        digitAuditInitial (piD (ref.phys q0.1)) := hi0
    rw [h0] at hK
    change (laneGhost lane (digitGhostInitial (piD (ref.phys q0.1))
      (digitSite ring root (src + q)))).carry = some K at hK
    rw [laneGhostInitial] at hK
    simp only [DigitLaneGhost.initial] at hK
    split at hK
    · rw [← Option.some.inj hK] at hu
      exact absurd hu List.not_mem_nil
    · cases hK
  | succ t ih =>
    intro ht q K hRq hq hK u hu
    obtain ⟨e, -, hstep, -⟩ := wStepAt ref root src R q0 W t (by omega)
    rw [hstep] at hK
    have hcor := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t
    have hclk := wClock ref q0 hc0 W t (by omega)
    rcases wCarryOrigin ref hn root lane src R hR hsrc hend (InheritedOk lane) _ hcor.1.1
      hcor.1.2.2.2.2.1 e q hRq hq K hK with h | ⟨-, -, u', hu1, -, rfl⟩ |
        ⟨hRq', -, -, L, u', hL, hu1, -, rfl⟩
    · exact Nat.le_succ_of_le (ih (by omega) q K hRq hq h u hu)
    · simp at hu
      subst hu
      omega
    · rcases List.mem_append.mp hu with hu | hu
      · exact Nat.le_succ_of_le (ih (by omega) (q - 1) L (by omega) (by omega) hL u hu)
      · simp at hu
        subst hu
        omega

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **Backward persistence of a ledger**: a ledger whose last use has time `u` has sat at its
cell since `u` (a letter that creates or extends a ledger stamps its own time last). Consumer:
`wCarryChain`. -/
theorem wCarryBack (t' q : Nat) (ht' : t' ≤ W.length) (hRq : R ≤ q) (hq : q < 2 * R)
    (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (l : List (DigitUse (compileAdvice (ceilLogTwo n)) n))
    (u : DigitUse (compileAdvice (ceilLogTwo n)) n) (hKu : K.uses = l ++ [u])
    (hK : caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W t').2 q = some K) :
    ∀ d, u.time + d ≤ t' →
      caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W (t' - d)).2 q =
        some K := by
  intro d
  induction d with
  | zero => intro _; exact hK
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    rw [show t' - d = t' - (d + 1) + 1 by omega] at h1
    obtain ⟨e, -, hstep, -⟩ := wStepAt ref root src R q0 W (t' - (d + 1)) (by omega)
    rw [hstep] at h1
    have hcor := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W (t' - (d + 1))
    have hclk := wClock ref q0 hc0 W (t' - (d + 1)) (by omega)
    rcases wCarryOrigin ref hn root lane src R hR hsrc hend (InheritedOk lane) _ hcor.1.1
      hcor.1.2.2.2.2.1 e q hRq hq K h1 with h | ⟨-, -, u', hu1, -, hK'⟩ |
        ⟨-, -, -, L, u', -, hu1, -, hK'⟩
    · exact h
    · exfalso
      have h3 : [] ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
      have h5 := (L3.DigitEntryBridge.lastEq h3).2
      subst h5
      omega
    · exfalso
      have h3 : L.uses ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
      have h5 := (L3.DigitEntryBridge.lastEq h3).2
      subst h5
      omega

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **Creation of a ledger** at the time of its last use: launched at `R` by the letter before
(reading the input of `R`), or extended from the cell below by a success that reads the settled
input of the cell. Consumer: `wCarryChain`. -/
theorem wCarryCreate (q : Nat) (hRq : R ≤ q) (hq : q < 2 * R)
    (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (l : List (DigitUse (compileAdvice (ceilLogTwo n)) n))
    (u : DigitUse (compileAdvice (ceilLogTwo n)) n) (hKu : K.uses = l ++ [u]) (hu0 : 0 < u.time)
    (hul : u.time ≤ W.length)
    (hK : caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W u.time).2 q = some K) :
    (q = R ∧ wKe root src R W (u.time - 1) = some R ∧ l = [] ∧ K.inherited = none ∧
      u.operand =
        inA ring root lane src (wRunAt ref.toWidthDigitReference q0 W (u.time - 1)).2 R) ∨
    (R < q ∧ wKe root src R W (u.time - 1) = some (q - 1) ∧
      caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W (u.time - 1)).2 (q - 1) =
        some ⟨K.inherited, l⟩ ∧
      u.operand = inA ring root lane src (wRunAt ref.toWidthDigitReference q0 W (u.time - 1)).2 q ∧
      ∃ T', cohortTok R (wLane ref root lane src R q0 W (u.time - 1)) q = .settled T') := by
  have e1 : u.time = u.time - 1 + 1 := by omega
  rw [e1] at hK
  obtain ⟨e, -, hstep, hke⟩ := wStepAt ref root src R q0 W (u.time - 1) (by omega)
  rw [hstep] at hK
  rw [hke]
  have hcor := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W (u.time - 1)
  have hclk := wClock ref q0 hc0 W (u.time - 1) (by omega)
  rcases wCarryOrigin ref hn root lane src R hR hsrc hend (InheritedOk lane) _ hcor.1.1
    hcor.1.2.2.2.2.1 e q hRq hq K hK with h | ⟨hqR, hkR, u', hu1, hu2, hK'⟩ |
      ⟨hRq', hk1, hset, L, u', hL, hu1, hop, hK'⟩
  · exfalso
    have := wCarryTB ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (u.time - 1) (by omega) q K
      hRq hq h u (by rw [hKu]; simp)
    omega
  · left
    have h3 : [] ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
    obtain ⟨h4, h5⟩ := L3.DigitEntryBridge.lastEq h3
    subst h5
    exact ⟨hqR, hkR, h4.symm, by subst hK'; rfl, hu2⟩
  · right
    have h3 : L.uses ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
    obtain ⟨h4, h5⟩ := L3.DigitEntryBridge.lastEq h3
    subst h5
    refine ⟨hRq', hk1, ?_, hop, hset⟩
    subst hK' h4
    exact hL

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **The strict carry chain (step 4c, carry half).** From the recorded terminal ledger (`R`
uses, no inherited carry) back to the launch: the ledger of the first `m + 1` uses sits at
`R + m` from use `m` until the letter before use `m + 1` (the terminal for `m = R - 1`), that
letter draws the edge `R + m`, and use `m` read the input of cell `R + m` one letter before it,
which was settled and carry-free for `m > 0` (port of `carryChain` with the operands). Consumer:
`wPackedAtExport`. -/
theorem wCarryChain (Lu : List (DigitUse (compileAdvice (ceilLogTwo n)) n))
    (uz : Nat → DigitUse (compileAdvice (ceilLogTwo n)) n) (T : Nat)
    (hlen : Lu.length = R) (hLu : ∀ m, m < R → Lu[m]? = some (uz m))
    (hpos : ∀ m, m < R → 0 < (uz m).time) (hbelow : ∀ m, m < R → (uz m).time < T)
    (hinc : ∀ m, m + 1 < R → (uz m).time < (uz (m + 1)).time) (hT : T ≤ W.length)
    (hterm : caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W (T - 1)).2
      (2 * R - 1) = some ⟨none, Lu⟩)
    (hkT : wKe root src R W (T - 1) = some (2 * R - 1)) :
    (∀ m, m < R → ∀ t, (uz m).time ≤ t → t + 1 ≤ (if m + 1 < R then (uz (m + 1)).time else T) →
      caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2 (R + m) =
        some ⟨none, Lu.take (m + 1)⟩) ∧
    (∀ m, m < R →
      wKe root src R W ((if m + 1 < R then (uz (m + 1)).time else T) - 1) = some (R + m)) ∧
    (uz 0).operand =
      inA ring root lane src (wRunAt ref.toWidthDigitReference q0 W ((uz 0).time - 1)).2 R ∧
    (∀ m, m < R → (uz m).operand =
      inA ring root lane src (wRunAt ref.toWidthDigitReference q0 W ((uz m).time - 1)).2 (R + m) ∧
      (0 < m → ∃ T', cohortTok R (wLane ref root lane src R q0 W ((uz m).time - 1)) (R + m) =
        .settled T')) := by
  have htake : ∀ m, m < R → Lu.take (m + 1) = Lu.take m ++ [uz m] := by
    intro m hm
    rw [List.take_add_one, hLu m hm]
    rfl
  have hwin : ∀ m, m < R → (uz m).time < (if m + 1 < R then (uz (m + 1)).time else T) ∧
      (if m + 1 < R then (uz (m + 1)).time else T) ≤ T := by
    intro m hm
    split
    · exact ⟨hinc m (by assumption), Nat.le_of_lt (hbelow (m + 1) (by assumption))⟩
    · exact ⟨hbelow m hm, Nat.le_refl T⟩
  have key : ∀ d m, m + d + 1 = R →
      caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W
        ((if m + 1 < R then (uz (m + 1)).time else T) - 1)).2 (R + m) =
          some ⟨none, Lu.take (m + 1)⟩ ∧
      wKe root src R W ((if m + 1 < R then (uz (m + 1)).time else T) - 1) = some (R + m) := by
    intro d
    induction d with
    | zero =>
      intro m hm
      rw [if_neg (by omega), show R + m = 2 * R - 1 by omega, List.take_of_length_le (by omega)]
      exact ⟨hterm, hkT⟩
    | succ d ih =>
      intro m hm
      obtain ⟨h1, -⟩ := ih (m + 1) (by omega)
      obtain ⟨hw1, hw2⟩ := hwin (m + 1) (by omega)
      generalize (if m + 1 + 1 < R then (uz (m + 1 + 1)).time else T) = Wd at h1 hw1 hw2
      have hb := wCarryBack ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (Wd - 1) (R + (m + 1))
        (by omega) (by omega) (by omega) ⟨none, Lu.take (m + 1 + 1)⟩ (Lu.take (m + 1)) (uz (m + 1))
        (htake (m + 1) (by omega)) h1 (Wd - 1 - (uz (m + 1)).time) (by omega)
      rw [show Wd - 1 - (Wd - 1 - (uz (m + 1)).time) = (uz (m + 1)).time by omega] at hb
      rw [if_pos (by omega)]
      rcases wCarryCreate ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (R + (m + 1))
        (by omega) (by omega) ⟨none, Lu.take (m + 1 + 1)⟩ (Lu.take (m + 1)) (uz (m + 1))
        (htake (m + 1) (by omega)) (hpos (m + 1) (by omega)) (by omega) hb with
        ⟨hq, -⟩ | ⟨-, hk, hc, -, -⟩
      · omega
      · rw [show R + (m + 1) - 1 = R + m by omega] at hk hc
        exact ⟨hc, hk⟩
  refine ⟨?_, fun m hm => (key (R - 1 - m) m (by omega)).2, ?_, ?_⟩
  · intro m hm t h1 h2
    obtain ⟨hc, -⟩ := key (R - 1 - m) m (by omega)
    obtain ⟨hw1, hw2⟩ := hwin m hm
    generalize (if m + 1 < R then (uz (m + 1)).time else T) = Wd at hc hw1 hw2 h2
    have hb := wCarryBack ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (Wd - 1) (R + m)
      (by omega) (by omega) (by omega) ⟨none, Lu.take (m + 1)⟩ (Lu.take m) (uz m) (htake m hm) hc
      (Wd - 1 - t) (by omega)
    rwa [show Wd - 1 - (Wd - 1 - t) = t by omega] at hb
  · obtain ⟨hc, -⟩ := key (R - 1) 0 (by omega)
    obtain ⟨hw1, hw2⟩ := hwin 0 (by omega)
    generalize (if 0 + 1 < R then (uz (0 + 1)).time else T) = Wd at hc hw1 hw2
    have hb := wCarryBack ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (Wd - 1) (R + 0)
      (by omega) (by omega) (by omega) ⟨none, Lu.take (0 + 1)⟩ (Lu.take 0) (uz 0)
      (htake 0 (by omega)) hc (Wd - 1 - (uz 0).time) (by omega)
    rw [show Wd - 1 - (Wd - 1 - (uz 0).time) = (uz 0).time by omega] at hb
    rcases wCarryCreate ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (R + 0) (by omega)
      (by omega) ⟨none, Lu.take (0 + 1)⟩ (Lu.take 0) (uz 0) (htake 0 (by omega)) (hpos 0 (by omega))
      (by omega) hb with ⟨-, -, -, -, hop⟩ | ⟨hq, -⟩
    · exact hop
    · omega
  · intro m hm
    obtain ⟨hc, -⟩ := key (R - 1 - m) m (by omega)
    obtain ⟨hw1, hw2⟩ := hwin m hm
    generalize (if m + 1 < R then (uz (m + 1)).time else T) = Wd at hc hw1 hw2
    have hb := wCarryBack ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (Wd - 1) (R + m)
      (by omega) (by omega) (by omega) ⟨none, Lu.take (m + 1)⟩ (Lu.take m) (uz m) (htake m hm) hc
      (Wd - 1 - (uz m).time) (by omega)
    rw [show Wd - 1 - (Wd - 1 - (uz m).time) = (uz m).time by omega] at hb
    rcases wCarryCreate ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (R + m) (by omega)
      (by omega) ⟨none, Lu.take (m + 1)⟩ (Lu.take m) (uz m) (htake m hm) (hpos m hm)
      (by omega) hb with ⟨hq, -, -, -, hop⟩ | ⟨-, -, -, hop, hset⟩
    · refine ⟨?_, fun h0 => by omega⟩
      rw [hop, show R + m = R by omega]
    · exact ⟨hop, fun _ => hset⟩

end Chain

end L3.StageMEntryCarryRows

#print axioms L3.StageMEntryCarryRows.tgtOtherKeep
#print axioms L3.StageMEntryCarryRows.tgtSettledKeep
#print axioms L3.StageMEntryCarryRows.tgtSettledForm
#print axioms L3.StageMEntryCarryRows.tgtSettledTopKeep
#print axioms L3.StageMEntryCarryRows.carryYRingOp
#print axioms L3.StageMEntryCarryRows.wCarryOrigin
#print axioms L3.StageMEntryCarryRows.wCarryChain
#print axioms L3.StageMEntryCarryRows.wMoveH
