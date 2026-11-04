import Leader.L3.Bank.RepairDigitUseCells

/-!
# Clause (C) of the comparison close: the aged window of one pair

`DigitPairCurrent … cut now` (Target.lean) asks, on one complete pair, that every source data
packet and every pending or settled target input carries a recorded sample of the source block
stamped in `(cut, now]` with the cell's value and tail, every unread source cell has an unread
ghost, no target input is a tombstone, and every live target carry has a clean nonempty ledger of
such samples.  Most of this is already carried by the existing correspondences (`GhostCorr`,
`ValCorr`, `UseVal`, `TimeBound`); what they do not say is the age of the atoms.  This module adds
exactly that, on the lane cells of one pair, generic in the compiled protocol:

* `LiveE`: a live target carry has an empty input; closed under every literal row
  (`liveEEdge`, shapes only);
* `WinAge … cut`: `LiveE`, every tracked atom (source output, target input) is a sample stamped
  after `cut`, and every target ledger is clean, nonempty, and uses only samples of the source
  block stamped after `cut`;
* `winAgeStep`: every letter keeps `WinAge` on a state of the cycle class `CohortCycIn` (the
  generated class; only its carry clause `tgtLive` is used), given the correspondence;
* `pairCurrentOfAge`: `WinAge` + `CohortCycIn` + the correspondences give `DigitPairCurrent`.

Model check: research/lean-l3/ledgers/close-mc.py (section 9 of close-family-notes.md):
`WinAge restart` with the cycle class holds at the terminal letter of the first strict
completion after `restart` and at every later state, R ≤ 3, from arbitrary scratch.
-/

namespace L3.CurrentWin

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.CohortTail
open L3.PacketClass
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.ValueCorr
open L3.ValueLedger
open L3.UseRows
open L3.UseCells

/-! ### Shapes: a live carry has an empty input -/

section Shapes

/-- A live target carry has an empty input.  Consumer: `WinAge`, `pairCurrentOfAge`. -/
def LiveE (R : Nat) (s : CohortLane) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → s.live q = true → s.inp q = .E

/-- The delivery row leaves a live delimiter with an empty input.  Consumer: `liveEEdge`. -/
theorem delLiveE (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool) :
    (bankRepairDigitDelStep ox iy ky).2.2 = true → (bankRepairDigitDelStep ox iy ky).2.1 = .E := by
  rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;> (try cases T) <;>
    simp [bankRepairDigitDelStep]

/-- The Fin row leaves both live ends with empty inputs.  Consumer: `liveEEdge`. -/
theorem finLiveE (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) :
    ((bankRepairDigitFinStep bx ix kx iy ky).2.1 = true →
        (bankRepairDigitFinStep bx ix kx iy ky).1 = .E) ∧
      ((bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = true →
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.1 = .E) := by
  rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> (try cases T) <;> simp [bankRepairDigitFinStep]

/-- The terminal row never leaves a live carry.  Consumer: `liveEEdge`. -/
theorem termLiveE (ix : BankRepairDigitInSh) (kx : Bool) : (cohortTermStep ix kx).2 = false := by
  rcases ix with _ | _ | T | T <;> cases kx <;> (try cases T) <;> simp [cohortTermStep]

/-- **`LiveE` is closed under every literal row.**  Consumer: `winAgeStep`. -/
theorem liveEEdge {R : Nat} {s : CohortLane} (h : LiveE R s) (k : Nat) :
    LiveE R (cohortEdge R s k) := by
  intro q h1 h2 hl
  by_cases c1 : k + 1 < R
  · simp only [cohortEdge, if_pos c1] at hl ⊢
    exact h q h1 h2 hl
  · by_cases c2 : k + 1 = R
    · simp only [cohortEdge, if_neg c1, if_pos c2, cohortUpd] at hl ⊢
      by_cases hq : q = k + 1
      · rw [if_pos hq] at hl ⊢
        exact delLiveE _ _ _ hl
      · rw [if_neg hq] at hl ⊢
        exact h q h1 h2 hl
    · by_cases c3 : k + 1 < 2 * R
      · simp only [cohortEdge, if_neg c1, if_neg c2, if_pos c3, cohortUpd] at hl ⊢
        have hf := finLiveE (decide (k = R)) (s.inp k) (s.live k) (s.inp (k + 1)) (s.live (k + 1))
        by_cases hq : q = k + 1
        · rw [if_pos hq] at hl ⊢
          exact hf.2 hl
        · rw [if_neg hq] at hl ⊢
          by_cases hq' : q = k
          · rw [if_pos hq'] at hl ⊢
            exact hf.1 hl
          · rw [if_neg hq'] at hl ⊢
            exact h q h1 h2 hl
      · by_cases c4 : k + 1 = 2 * R
        · simp only [cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_pos c4, cohortUpd] at hl ⊢
          by_cases hq : q = k
          · rw [if_pos hq] at hl
            rw [termLiveE] at hl
            cases hl
          · rw [if_neg hq] at hl ⊢
            exact h q h1 h2 hl
        · simp only [cohortEdge, if_neg c1, if_neg c2, if_neg c3, if_neg c4] at hl ⊢
          exact h q h1 h2 hl

/-- `LiveE` along the lane step of any letter.  Consumer: `winAgeStep`. -/
theorem liveELaneStep {R : Nat} {s : CohortLane} (h : LiveE R s) :
    ∀ ke : Option Nat, LiveE R (cohortLaneStep R s ke)
  | none => h
  | some k => liveEEdge h k

end Shapes

/-! ### The aged window -/

section Aged

variable {c : Compiled} {n : Nat}

/-- A sampled atom stamped after `cut`.  Consumer: `WinAge`. -/
def AgedAtom (cut : Nat) (x : DigitAtom n) : Prop :=
  ∃ id : DigitStamp n, x = .sampled id ∧ cut < id.time

/-- A use made by `now` of a sample of the source block stamped after `cut` and before the use.
Consumer: `WinAge`. -/
def UseAged (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R cut now : Nat)
    (u : DigitUse c n) : Prop :=
  u.time ≤ now ∧ ∃ id : DigitStamp n, u.operand = some (.sampled id) ∧ cut < id.time ∧
    id.time < u.time ∧ id.lane = lane ∧ ∃ q, q < R ∧ id.site = digitSite ring root (src + q)

/-- **The aged window** of one pair at `cut`: live carries have empty inputs, every tracked atom is
a sample stamped after `cut`, and every target ledger is clean, nonempty and uses only aged
samples of the source block.  Consumer: `winAgeStep`, `pairCurrentOfAge`. -/
def WinAge (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R cut : Nat)
    (s : CohortLane) (A : DigitAudit c n) : Prop :=
  LiveE R s ∧
  (∀ q (x : DigitAtom n), trackedAt R (laneCells ring root lane src A.current) q = some x →
    AgedAtom cut x) ∧
  (∀ q, R ≤ q → q < 2 * R → ∀ L : DigitCarryGhost c n,
    (laneCells ring root lane src A.current q).carry = some L →
    L.inherited = none ∧ L.uses ≠ [] ∧
      ∀ u, u ∈ L.uses → UseAged ring root lane src R cut A.clock u)

theorem useAgedMono {ring : DirectedRing n} {root : Fin n} {lane : DigitLane} {src R cut now now' : Nat}
    (hle : now ≤ now') {u : DigitUse c n} (h : UseAged ring root lane src R cut now u) :
    UseAged ring root lane src R cut now' u :=
  ⟨Nat.le_trans h.1 hle, h.2⟩

/-- A settled target input carries an aged sample of the source block, stamped no later than the
clock.  Consumer: `winAgeStep`. -/
theorem settledAged (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R cut : Nat)
    (Base : Bool → DigitAtom n → Prop) (hnb : ∀ T (id : DigitStamp n), ¬ Base T (.sampled id))
    (S : Fin n → ProjD c) (A : DigitAudit c n)
    (hgc : GhostCorrDistinct ring root lane src R Base S A)
    (h : WinAge ring root lane src R cut (cohortProj ring root lane src R S) A)
    (q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) (T : Bool)
    (hS : (cohortProj ring root lane src R S).inp q = .S T) :
    ∃ id : DigitStamp n, (laneCells ring root lane src A.current q).input = some (.sampled id) ∧
      cut < id.time ∧ id.time ≤ A.clock ∧ id.lane = lane ∧
      ∃ q', q' < R ∧ id.site = digitSite ring root (src + q') := by
  have hc := (hgc.1.2 q h1 h2).1
  rw [hS] at hc
  obtain ⟨b, hb⟩ := optSome hc
  have htr : trackedAt R (laneCells ring root lane src A.current) q = some b := by
    unfold trackedAt
    rw [if_neg (by omega), if_pos h2]
    exact hb
  obtain ⟨id, rfl, hcut⟩ := h.2.1 q b htr
  have htb := hgc.2.2.1 q id htr
  have hok : GhostOk ring root lane src R Base A T (.sampled id) := by
    have := hc
    rw [hb] at this
    exact this
  rcases hok with hbase | ⟨smp, hsid, -, -, hl, q', hq', hsite⟩
  · exact (hnb T id hbase).elim
  · have hid : smp.id = id := by
      simp only [DigitAtom.sampled.injEq] at hsid
      exact hsid.symm
    rw [hid] at hl hsite
    exact ⟨id, hb, hcut, htb, hl, q', hq', hsite⟩

/-- **Every letter keeps the aged window** on a state of the cycle class (projected ring, layout
hypotheses of `cohortProjStep`, the correspondence with a base that holds no sample).  Consumer:
the run lemmas of clause (C). -/
theorem winAgeStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop)
    (hnb : ∀ T (id : DigitStamp n), ¬ Base T (.sampled id)) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (cut : Nat) (hcut : cut ≤ A.clock)
    (hgc : GhostCorrDistinct ring root lane src R Base S A)
    {jj o : Nat} {g : (Nat → Nat) × Nat}
    (hcyc : CohortCycIn R jj (cohortProj ring root lane src R S) g o)
    (h : WinAge ring root lane src R cut (cohortProj ring root lane src R S) A) :
    WinAge ring root lane src R cut (cohortProj ring root lane src R (phiD ring S (digitSite ring root j)))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  have hclk : (digitAuditStep ring S A (digitSite ring root j)).clock = A.clock + 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j hj hbX hbY]
    exact liveELaneStep h.1 _
  · obtain ⟨k, hfr, hm⟩ := trackedStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF
      lane A j hj hbX hbY
    have hfresh : ∀ x : DigitAtom n,
        some (DigitAtom.sampled (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane)) =
          some x → AgedAtom cut x := by
      intro x hx
      simp only [Option.some.injEq] at hx
      exact ⟨_, hx.symm, by show cut < A.clock + 1; omega⟩
    intro q x hx
    by_cases hq1 : q = k
    · subst hq1
      rcases (hm x).1 hx with h3 | h3
      · exact h.2.1 _ x h3
      · exact hfresh x h3
    · by_cases hq2 : q = k + 1
      · subst hq2
        rcases (hm x).2 hx with h3 | ⟨h3, -⟩
        · exact h.2.1 _ x h3
        · exact h.2.1 _ x h3
      · rw [hfr q hq1 hq2] at hx
        exact h.2.1 q x hx
  · obtain ⟨cfr, cdel, cfin, cterm⟩ := tgtRows ring hn root S R src hR hsrc hend hroot hbR hb2R
      hbF lane A j hj hbX hbY
    rw [hclk]
    have hold : ∀ q, R ≤ q → q < 2 * R → ∀ L : DigitCarryGhost c n,
        (laneCells ring root lane src A.current q).carry = some L →
        L.inherited = none ∧ L.uses ≠ [] ∧
          ∀ u, u ∈ L.uses → UseAged ring root lane src R cut (A.clock + 1) u := by
      intro q h1 h2 L hL
      obtain ⟨a1, a2, a3⟩ := h.2.2 q h1 h2 L hL
      exact ⟨a1, a2, fun u hu => useAgedMono (Nat.le_succ _) (a3 u hu)⟩
    have hnew : ∀ q, R ≤ q → q < 2 * R → ∀ T,
        (cohortProj ring root lane src R S).inp q = .S T →
        ∀ u : DigitUse c n, u.time = A.clock + 1 →
        u.operand = (laneCells ring root lane src A.current q).input →
        UseAged ring root lane src R cut (A.clock + 1) u := by
      intro q h1 h2 T hS u hut huo
      obtain ⟨id, hid, hcut', htb, hl, q', hq', hsite⟩ :=
        settledAged ring root lane src R cut Base hnb S A hgc h q h1 h2 T hS
      exact ⟨by omega, id, by rw [huo, hid], hcut', by omega, hl, q', hq', hsite⟩
    intro q h1 h2 L hLq
    by_cases hk1 : cohortEdgeOf root src R (digitSite ring root j) = some q
    · by_cases hq : q + 1 < 2 * R
      · rcases (cfin q hk1 h1 hq).2.1 with h3 | h3 | ⟨hqR, hS, u, hut, huo, hu⟩
        · rw [h3] at hLq; cases hLq
        · rw [h3] at hLq; exact hold q h1 h2 L hLq
        · rw [hu] at hLq
          cases hLq
          obtain ⟨T, hT⟩ : ∃ T, (cohortProj ring root lane src R S).inp q = .S T := by
            revert hS
            cases (cohortProj ring root lane src R S).inp q <;> simp [shS]
          refine ⟨rfl, by simp, fun u' hu' => ?_⟩
          simp only [List.mem_singleton] at hu'
          rw [hu']
          exact hnew q h1 h2 T hT u hut huo
      · have hq' : q = 2 * R - 1 := by omega
        subst hq'
        rcases (cterm hk1).2.1 with h3 | h3
        · rw [h3] at hLq; cases hLq
        · rw [h3] at hLq; exact hold _ h1 h2 L hLq
    · by_cases hk2 : cohortEdgeOf root src R (digitSite ring root j) = some (q - 1)
      · by_cases hqR : q = R
        · subst q
          rw [(cdel hk2).2] at hLq
          exact hold _ h1 h2 L hLq
        · have hf := cfin (q - 1) hk2 (by omega) (by omega)
          rw [show q - 1 + 1 = q by omega] at hf
          by_cases hlk : (cohortProj ring root lane src R S).live (q - 1) = true
          · obtain ⟨-, hset⟩ := tgtLive hcyc (q - 1) (by omega) (by omega) hlk
            have hsq := hset q (by omega) h2
            rw [cohortTokTgt _ h1] at hsq
            obtain ⟨hS, hlq⟩ := tokInSettled hsq
            obtain ⟨L0, hL0⟩ : ∃ L0, (laneCells ring root lane src A.current (q - 1)).carry =
                some L0 := by
              have := (hgc.1.2 (q - 1) (by omega) (by omega)).2
              rw [hlk] at this
              cases h0 : (laneCells ring root lane src A.current (q - 1)).carry with
              | none => rw [h0] at this; cases this
              | some L0 => exact ⟨L0, rfl⟩
            obtain ⟨u, hut, huo, hu⟩ := hf.2.2.2 hlk hlq false hS L0 hL0
            rw [hu] at hLq
            cases hLq
            obtain ⟨hi0, -, hops0⟩ := hold (q - 1) (by omega) (by omega) L0 hL0
            refine ⟨hi0, by simp, fun u' hu' => ?_⟩
            rcases List.mem_append.mp hu' with hu' | hu'
            · exact hops0 u' hu'
            · simp only [List.mem_singleton] at hu'
              rw [hu']
              exact hnew q h1 h2 false hS u hut huo
          · have hlk' : (cohortProj ring root lane src R S).live (q - 1) = false := by
              simpa using hlk
            rw [hf.2.2.1 hlk'] at hLq
            exact hold q h1 h2 L hLq
      · rw [cfr q h1 h2 hk1 hk2] at hLq
        exact hold q h1 h2 L hLq

end Aged

/-! ### Currentness of the pair -/

section Current

variable {c : Compiled} {n : Nat}

theorem endpointGhostLane (lane : DigitLane) (g : DigitGhost c n) :
    digitEndpointGhost lane g = laneGhost lane g := by
  cases lane <;> rfl

/-- **`DigitPairCurrent` from the aged window**: on a state of the cycle class with the ghost
correspondence (base without samples), the value correspondence and the use values, the aged
window at `cut` gives the currentness of the pair at `cut` and the clock.  Consumer: clause (C)
of `WidthComparisonClose`. -/
theorem pairCurrentOfAge (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (hspan : digitSpan c = R)
    (Base : Bool → DigitAtom n → Prop) (hnb : ∀ T (id : DigitStamp n), ¬ Base T (.sampled id))
    (S : Fin n → ProjD c) (A : DigitAudit c n) (cut : Nat)
    (hgc : GhostCorrDistinct ring root lane src R Base S A)
    (hval : ValCorr ring root lane src R S A) (huv : UseVal ring root lane src R A)
    {jj o : Nat} {g : (Nat → Nat) × Nat}
    (hcyc : CohortCycIn R jj (cohortProj ring root lane src R S) g o)
    (h : WinAge ring root lane src R cut (cohortProj ring root lane src R S) A) :
    DigitPairCurrent ring root A S A.current lane src (src + R) cut A.clock := by
  intro offset hoff
  rw [hspan] at hoff
  have hpkt : ∀ (q : Nat) (a : DigitAtom n) (T : Bool) (v : Fin c.topA),
      trackedAt R (laneCells ring root lane src A.current) q = some a →
      GhostOk ring root lane src R Base A T a → AtomSV A (some a) v T →
      DigitCurrentPacket ring root A lane src cut A.clock (some a) v T := by
    intro q a T v htr hok hsv
    obtain ⟨id, rfl, hcut⟩ := h.2.1 q a htr
    have htb : id.time ≤ A.clock := hgc.2.2.1 q id htr
    rcases hok with hbase | ⟨smp, hsid, -, -, hl, q', hq', hsite⟩
    · exact (hnb T id hbase).elim
    · have hid : smp.id = id := by
        simp only [DigitAtom.sampled.injEq] at hsid
        exact hsid.symm
      obtain ⟨s', hs', hs'id, hs'v, hs'T⟩ := hsv id rfl
      rw [hid] at hl hsite
      exact ⟨id, s', q', rfl, hs'id, hs', hl, by rw [hspan]; exact hq', hsite, hcut, htb,
        hs'v, hs'T⟩
  have hR2 : R ≤ R + offset := Nat.le_add_right R offset
  have hR3 : R + offset < 2 * R := by omega
  have eS : digitEndpointGhost lane (A.current (digitSite ring root (src + offset))) =
      laneCells ring root lane src A.current offset := by
    rw [endpointGhostLane]; rfl
  have eT : digitEndpointGhost lane (A.current (digitSite ring root (src + R + offset))) =
      laneCells ring root lane src A.current (R + offset) := by
    rw [endpointGhostLane, Nat.add_assoc]; rfl
  have trS : trackedAt R (laneCells ring root lane src A.current) offset =
      (laneCells ring root lane src A.current offset).out.atom := by
    unfold trackedAt; rw [if_pos hoff]
  have trT : trackedAt R (laneCells ring root lane src A.current) (R + offset) =
      (laneCells ring root lane src A.current (R + offset)).input := by
    unfold trackedAt; rw [if_neg (by omega), if_pos hR3]
  dsimp only
  rw [eS, eT]
  refine ⟨?_, ?_, ?_⟩
  · have hO := hgc.1.1 offset hoff
    rw [projOut ring root lane src R S offset hoff] at hO
    have hV := hval.1 offset hoff
    unfold DigitCurrentOutput
    rw [digitEndpointView, laneViewOut]
    generalize bankRepairDigitLaneOut lane (S (digitSite ring root (src + offset))).top = ot
      at hO hV ⊢
    cases ot with
    | E => trivial
    | U =>
      have hob : (laneCells ring root lane src A.current offset).out.obligation.isSome = true := hO
      revert hob
      cases (laneCells ring root lane src A.current offset).out with
      | empty => simp [DigitOutGhost.obligation]
      | unread cause => intro _; exact ⟨cause, rfl⟩
      | packet a => simp [DigitOutGhost.obligation]
    | D v T =>
      have hO' : optOk (GhostOk ring root lane src R Base A T)
          (laneCells ring root lane src A.current offset).out.atom := hO
      have hV' : AtomSV A (laneCells ring root lane src A.current offset).out.atom v T := hV
      obtain ⟨b, hb⟩ := optSome hO'
      rw [hb] at hO' hV'
      show DigitCurrentPacket ring root A lane src cut A.clock
        (laneCells ring root lane src A.current offset).out.atom v T
      rw [hb]
      exact hpkt offset b T v (by rw [trS, hb]) hO' hV'
  · have hI := (hgc.1.2 (R + offset) hR2 hR3).1
    rw [projIn ring root lane src R S (R + offset) hR2 hR3] at hI
    have hV := hval.2 (R + offset) hR2 hR3
    have hlv := (hgc.1.2 (R + offset) hR2 hR3).2
    have hpin := projIn ring root lane src R S (R + offset) hR2 hR3
    unfold DigitCurrentInput
    rw [digitEndpointView, laneViewIn, Nat.add_assoc]
    generalize hit : bankRepairDigitLaneIn lane (S (digitSite ring root (src + (R + offset)))).top =
      it at hI hV hpin ⊢
    cases it with
    | E => trivial
    | X =>
      have hX : (cohortProj ring root lane src R S).inp (R + offset) = .X := by
        rw [hpin]; rfl
      by_cases hl : (cohortProj ring root lane src R S).live (R + offset) = true
      · have := h.1 (R + offset) hR2 hR3 hl
        rw [hX] at this
        cases this
      · exact tgtNoX hcyc (R + offset) hR2 hR3 (by simpa using hl) hX
    | P v T =>
      have hI' : optOk (GhostOk ring root lane src R Base A T)
          (laneCells ring root lane src A.current (R + offset)).input := hI
      have hV' : AtomSV A (laneCells ring root lane src A.current (R + offset)).input v T := hV
      obtain ⟨b, hb⟩ := optSome hI'
      rw [hb] at hI' hV'
      show DigitCurrentPacket ring root A lane src cut A.clock
        (laneCells ring root lane src A.current (R + offset)).input v T
      rw [hb]
      exact hpkt (R + offset) b T v (by rw [trT, hb]) hI' hV'
    | S v T =>
      have hI' : optOk (GhostOk ring root lane src R Base A T)
          (laneCells ring root lane src A.current (R + offset)).input := hI
      have hV' : AtomSV A (laneCells ring root lane src A.current (R + offset)).input v T := hV
      obtain ⟨b, hb⟩ := optSome hI'
      rw [hb] at hI' hV'
      show DigitCurrentPacket ring root A lane src cut A.clock
        (laneCells ring root lane src A.current (R + offset)).input v T
      rw [hb]
      exact hpkt (R + offset) b T v (by rw [trT, hb]) hI' hV'
  · intro hlive
    have hlv := (hgc.1.2 (R + offset) hR2 hR3).2
    rw [projLive ring root lane src R S (R + offset) hR2 hR3] at hlv
    have hlive' : bankRepairDigitLaneLive lane
        (S (digitSite ring root (src + (R + offset)))).top = true := by
      have := hlive
      rw [digitEndpointView, laneViewLive, Nat.add_assoc] at this
      exact this
    rw [hlive'] at hlv
    obtain ⟨L, hL⟩ : ∃ L, (laneCells ring root lane src A.current (R + offset)).carry = some L := by
      cases h0 : (laneCells ring root lane src A.current (R + offset)).carry with
      | none => rw [h0] at hlv; cases hlv
      | some L => exact ⟨L, rfl⟩
    obtain ⟨hi0, hne, hops⟩ := h.2.2 (R + offset) hR2 hR3 L hL
    have huv' := huv.1 (R + offset) hR2 hR3 L hL
    refine ⟨L, hL, hi0, hne, fun u hu => ?_⟩
    obtain ⟨hut, id, hop, hcut, hlt, hl, q', hq', hsite⟩ := hops u hu
    obtain ⟨s', hs', hs'id, hs'v, hs'T⟩ := huv' u hu id hop
    refine ⟨hut, ⟨id, s', q', hop, hs'id, hs', hl, by rw [hspan]; exact hq', hsite, hcut,
      by omega, hs'v, hs'T⟩, id, hop, hlt⟩

end Current

end L3.CurrentWin

#print axioms L3.CurrentWin.liveEEdge
#print axioms L3.CurrentWin.winAgeStep
#print axioms L3.CurrentWin.pairCurrentOfAge
