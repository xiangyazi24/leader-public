import Leader.L3.Bank.RepairDigitPacketMomentV

/-!
# Lemma e-packet, the renewal trial: the outcome offset is fixed by the queue head

repair.tex, the renewal trial: "At a packet-only cut let `k` be the oldest pending serial, or
the next serial if none is pending, and let `h = k mod r`. If `h = 0`, the next group settles in
alignment. If `h = r - 1`, the oldest tail is deleted at the terminal, leaving a group boundary.
For `1 ≤ h ≤ r - 2`, the first tail settles at offset `h`."

On the lane the serial stream after the distinguished tail is the aligned queue
`extWord = F^a (T F^(R-1))^(b+1)` (`L3.PacketMomentPending.AlignExt`): in serial order every
group is `F^(R-1) T`, the tail at residue `R - 1` (the distinguished tail opens the stream), so the
oldest pending (or next) serial has residue `headRes R a = R - 1 - a`.

Along the trial (`L3.PacketMomentV.VI`, settled non-tail run of `i` cells, queue index `a`) the
index `vIdx R a i` (`a + i`, or `R - 1` at a terminal deletion `a = i = 0`) is kept by every
letter (`vStepIdx`), and the tail settles at offset `R - 1 - vIdx` (`VTAt`). From the packet-only
cut (`i = 0`) this is the paper's case split (`vOffsetOfRes`): offset `headRes` for
`1 ≤ headRes ≤ R - 2` (the misaligned cut `RacePend`), offset `0` for `headRes = 0` (aligned)
and for `headRes = R - 1` (deletion, then the aligned group). `vMomentAtCoupled` is the moment
bound of `L3.PacketMomentV.vMomentCoupled` with this exact target.
-/

namespace L3.PacketMomentVSerial

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketRelease
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentAlign
open L3.PacketMomentPending
open L3.PacketMomentV

/-- **The trial index**: non-tails still to settle before the outcome tail, counted with the
settled run; a terminal deletion (`a = i = 0`) passes to the next group (`R - 1`).
Consumer: `VIAt`, `vStepIdx`. -/
def vIdx (R a i : Nat) : Nat := if a + i = 0 then R - 1 else a + i

/-- The trial class at index `m`. Consumer: `vMomentAt`. -/
def VIAt (R m : Nat) (s : CohortLane) : Prop :=
  ∃ a i, i + a + 1 ≤ R ∧ AlignExt R a s ∧ VShape R i s ∧ vIdx R a i = m

/-- **The trial target at index `m`**: the window is carry-free, a tail is settled at offset
`R - 1 - m` (cell `2R - 1 - m`), its older suffix is settled non-tails to its right, and only empty
cells and moving packets are to its left (repair.tex: "Its own older suffix is settled to its
right; younger work remains moving or unexported to its left"). Consumer: `vMomentAt`,
`vtAtRace`, the aligned completion at `m = R - 1`. -/
def VTAt (R m : Nat) (s : CohortLane) : Prop :=
  m + 1 ≤ R ∧ ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧
    (q = 2 * R - 1 - m → s.inp q = .S true) ∧
    (2 * R - m ≤ q → s.inp q = .S false) ∧
    (q < 2 * R - 1 - m → s.inp q = .E ∨ isPI (s.inp q) = true)

/-- **One letter of the trial keeps the index**: the successor is the target at the index, or a
trial state with the same index. Consumer: `vMomentAt`. -/
theorem vStepIdx (R : Nat) (hR : 3 ≤ R) (s : CohortLane) (k a i : Nat) (hai : i + a + 1 ≤ R)
    (hA : AlignExt R a s) (hS : VShape R i s) :
    (a = 0 ∧ 1 ≤ i ∧ VTAt R i (cohortEdge R s k)) ∨ VIAt R (vIdx R a i) (cohortEdge R s k) := by
  have hsR := sROf R i s hS
  have hwin := shapeWin R i s hS
  have hcell := hS.2
  have halign := alignExtStep R a (by omega) s k hA hwin
  by_cases h1 : k + 1 < R
  · -- a source letter
    have hinp : (cohortEdge R s k).inp = s.inp := by unfold cohortEdge; rw [if_pos h1]
    have hlive : (cohortEdge R s k).live = s.live := by unfold cohortEdge; rw [if_pos h1]
    have hA' : AlignExt R a (cohortEdge R s k) := by
      rcases halign with ⟨h, _⟩ | ⟨B, _, _, _, hk, _⟩
      · exact h
      · omega
    have hS' : VShape R i (cohortEdge R s k) :=
      ⟨hS.1, fun q h1 h2 => by rw [hinp, hlive]; exact hS.2 q h1 h2⟩
    exact Or.inr ⟨a, i, hai, hA', hS', rfl⟩
  by_cases h2 : k + 1 = R
  · -- the port letter
    have hlR := (hcell R (by omega) (by omega)).1
    have hoth : ∀ q, q ≠ R → (cohortEdge R s k).inp q = s.inp q ∧
        (cohortEdge R s k).live q = s.live q := by
      intro q hq
      unfold cohortEdge; rw [if_neg h1, if_pos h2]
      exact ⟨by show cohortUpd s.inp (k + 1) _ q = _; simp [cohortUpd, show q ≠ k + 1 by omega],
        by show cohortUpd s.live (k + 1) _ q = _; simp [cohortUpd, show q ≠ k + 1 by omega]⟩
    have hA' : AlignExt R a (cohortEdge R s k) := by
      rcases halign with ⟨h, _⟩ | ⟨B, _, _, _, hk, _⟩
      · exact h
      · omega
    rcases srcStep R (by omega) s k hA.1 with ⟨_, hpw⟩ | ⟨hk0, _⟩ | ⟨B, ⟨_, _, _, hP, hlP⟩, _⟩
    · obtain ⟨hiR, hlR'⟩ := hpw h2
      rw [hlR, if_neg (by simp)] at hiR
      have hinp : (cohortEdge R s k).inp = s.inp := by
        funext q; by_cases hq : q = R
        · rw [hq, hiR]
        · exact (hoth q hq).1
      have hlive : (cohortEdge R s k).live = s.live := by
        funext q; by_cases hq : q = R
        · rw [hq, hlR', hlR]
        · exact (hoth q hq).2
      have hS' : VShape R i (cohortEdge R s k) :=
        ⟨hS.1, fun q h1 h2 => by rw [hinp, hlive]; exact hS.2 q h1 h2⟩
      exact Or.inr ⟨a, i, hai, hA', hS', rfl⟩
    · omega
    · -- an export
      have hS' : VShape R i (cohortEdge R s k) := by
        refine ⟨hS.1, fun q hq1 hq2 => ?_⟩
        by_cases hq : q = R
        · subst hq
          refine ⟨hlP, fun h => by omega, fun _ => Or.inr (by rw [hP]; rfl)⟩
        · rw [(hoth q hq).1, (hoth q hq).2]; exact hS.2 q hq1 hq2
      exact Or.inr ⟨a, i, hai, hA', hS', rfl⟩
  by_cases h3 : k + 1 < 2 * R
  · -- an internal window edge
    have hk : R ≤ k := by omega
    have hform := edgeInner R s k hk h3
    have hck := hcell k hk (by omega)
    have hck1 := hcell (k + 1) (by omega) h3
    rw [hck.1, hck1.1] at hform
    have hid : ∀ f : BankRepairDigitInSh × Bool × BankRepairDigitInSh × Bool,
        bankRepairDigitFinStep (decide (k = R)) (s.inp k) false (s.inp (k + 1)) false = f →
        f = (s.inp k, false, s.inp (k + 1), false) → cohortEdge R s k = s := by
      intro f hf hfe
      rw [hform, hf, hfe]
      exact laneSame s _ _ (updSame _ _ _ _ rfl rfl)
        (updSame _ _ _ _ hck.1.symm hck1.1.symm)
    have hidCase : cohortEdge R s k = s →
        (a = 0 ∧ 1 ≤ i ∧ VTAt R i (cohortEdge R s k)) ∨
          VIAt R (vIdx R a i) (cohortEdge R s k) := by
      intro he
      rw [he]
      exact Or.inr ⟨a, i, hai, hA, hS, rfl⟩
    by_cases hreg : 2 * R - i ≤ k
    · have hSk := hck.2.1 hreg
      have hkR : decide (k = R) = false := by simp; omega
      exact hidCase (hid _ rfl (by rw [hkR, hSk, finS]))
    · rcases hck.2.2 (by omega) with hEk | hPk
      · exact hidCase (hid _ rfl (by rw [hEk, finE]))
      · obtain ⟨B, hB⟩ : ∃ B, s.inp k = .P B := by
          revert hPk; cases s.inp k with
          | P T => intro _; exact ⟨T, rfl⟩
          | _ => intro h; cases h
        by_cases hreg1 : 2 * R - i ≤ k + 1
        · -- settlement beside the settled run: a removal
          have hSk1 := hck1.2.1 hreg1
          have hi0 : 1 ≤ i := by omega
          have hinpk : (cohortEdge R s k).inp k = .S B := by
            rw [hform, hB, hSk1, finPS]; simp [cohortUpd]
          have hinpk1 : (cohortEdge R s k).inp (k + 1) = .S false := by
            rw [hform, hB, hSk1, finPS]; simp [cohortUpd]
          have hlv : (cohortEdge R s k).live = s.live := by
            rw [hform, hB, hSk1, finPS]
            exact updSame _ _ _ _ hck.1.symm hck1.1.symm
          have hothI : ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).inp q = s.inp q := by
            intro q hq hq'
            rw [hform]; simp [cohortUpd, hq, hq']
          rcases halign with ⟨_, _, hls⟩ | ⟨B', _, hB', hA', _, _, hPk', _, _⟩
          · exfalso
            have := hls.1 hk h3
            rw [hinpk, hinpk1, hB, hSk1] at this
            simp [pwI] at this
          · rw [hB] at hPk'
            cases hPk'
            by_cases ha0 : a = 0
            · left
              refine ⟨ha0, hi0, hS.1, fun q hq1 hq2 =>
                ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩⟩
              · rw [show q = k by omega, hinpk, hB', ha0]; rfl
              · by_cases hqk1 : q = k + 1
                · rw [hqk1, hinpk1]
                · rw [hothI q (by omega) hqk1]; exact (hcell q hq1 hq2).2.1 (by omega)
              · rw [hothI q (by omega) (by omega)]; exact (hcell q hq1 hq2).2.2 (by omega)
            · right
              have hBf : B = false := by rw [hB']; simp [ha0]
              rw [if_neg ha0] at hA'
              have hS' : VShape R (i + 1) (cohortEdge R s k) := by
                refine ⟨by omega, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, ?_, ?_⟩⟩
                · intro hq
                  by_cases hqk : q = k
                  · rw [hqk, hinpk, hBf]
                  · by_cases hqk1 : q = k + 1
                    · rw [hqk1, hinpk1]
                    · rw [hothI q hqk hqk1]; exact (hcell q hq1 hq2).2.1 (by omega)
                · intro hq
                  rw [hothI q (by omega) (by omega)]
                  exact (hcell q hq1 hq2).2.2 (by omega)
              refine ⟨a - 1, i + 1, by omega, hA', hS', ?_⟩
              unfold vIdx; rw [if_neg (by omega), if_neg (by omega)]; omega
        · rcases hck1.2.2 (by omega) with hEk1 | hPk1
          · -- a move
            have hinpk : (cohortEdge R s k).inp k = .E := by
              rw [hform, hB, hEk1, finPE]; simp [cohortUpd]
            have hinpk1 : (cohortEdge R s k).inp (k + 1) = .P B := by
              rw [hform, hB, hEk1, finPE]; simp [cohortUpd]
            have hlv : (cohortEdge R s k).live = s.live := by
              rw [hform, hB, hEk1, finPE]
              exact updSame _ _ _ _ hck.1.symm hck1.1.symm
            have hothI : ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).inp q = s.inp q := by
              intro q hq hq'
              rw [hform]; simp [cohortUpd, hq, hq']
            have hA' : AlignExt R a (cohortEdge R s k) := by
              rcases halign with ⟨h, _⟩ | ⟨B', _, _, _, _, _, _, hset, _⟩
              · exact h
              · have := (hset h3).1; rw [hEk1] at this; cases this
            have hS' : VShape R i (cohortEdge R s k) := by
              refine ⟨hS.1, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, ?_, ?_⟩⟩
              · intro hq
                rw [hothI q (by omega) (by omega)]; exact (hcell q hq1 hq2).2.1 hq
              · intro hq
                by_cases hqk : q = k
                · rw [hqk, hinpk]; exact Or.inl rfl
                · by_cases hqk1 : q = k + 1
                  · rw [hqk1, hinpk1]; exact Or.inr rfl
                  · rw [hothI q hqk hqk1]; exact (hcell q hq1 hq2).2.2 hq
            exact Or.inr ⟨a, i, hai, hA', hS', rfl⟩
          · obtain ⟨B1, hB1⟩ : ∃ B1, s.inp (k + 1) = .P B1 := by
              revert hPk1; cases s.inp (k + 1) with
              | P T => intro _; exact ⟨T, rfl⟩
              | _ => intro h; cases h
            exact hidCase (hid _ rfl (by rw [hB, hB1, finPP]))
  by_cases h4 : k + 1 = 2 * R
  · -- the terminal edge
    have hform := edgeTerm R s k h4 (by omega)
    have hck := hcell k (by omega) (by omega)
    rw [hck.1] at hform
    have hid : (cohortTermStep (s.inp k) false) = (s.inp k, false) → cohortEdge R s k = s := by
      intro hf
      rw [hform, hf]
      exact laneSame s _ _ (updOne _ _ _ rfl) (updOne _ _ _ hck.1.symm)
    by_cases hi0 : i = 0
    · subst hi0
      rcases hck.2.2 (by omega) with hEk | hPk
      · have he := hid (by rw [hEk]; rfl)
        rw [he]
        exact Or.inr ⟨a, 0, hai, hA, hS, rfl⟩
      · obtain ⟨B, hB⟩ : ∃ B, s.inp k = .P B := by
          revert hPk; cases s.inp k with
          | P T => intro _; exact ⟨T, rfl⟩
          | _ => intro h; cases h
        have hinpk : (cohortEdge R s k).inp k = retireOf (.P B) := by
          rw [hform, hB]; cases B <;> simp [cohortUpd, cohortTermStep, retireOf]
        have hlv : (cohortEdge R s k).live = s.live := by
          rw [hform, hB]
          exact updOne _ _ _ (by rw [hck.1]; cases B <;> rfl)
        have hothI : ∀ q, q ≠ k → (cohortEdge R s k).inp q = s.inp q := by
          intro q hq; rw [hform]; simp [cohortUpd, hq]
        rcases halign with ⟨_, _, hls⟩ | ⟨B', _, hB', hA', _, _, hPk', _, _⟩
        · exfalso
          have := hls.2 h4
          rw [hinpk, hB] at this
          cases B <;> simp [pwI, retireOf] at this
        · rw [hB] at hPk'
          cases hPk'
          right
          by_cases ha0 : a = 0
          · have hBt : B = true := by rw [hB', ha0]; rfl
            rw [if_pos ha0] at hA'
            have hS' : VShape R 0 (cohortEdge R s k) := by
              refine ⟨by omega, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1,
                fun h => by omega, fun _ => ?_⟩⟩
              by_cases hqk : q = k
              · rw [hqk, hinpk, hBt]; exact Or.inl rfl
              · rw [hothI q hqk]; exact (hcell q hq1 hq2).2.2 (by omega)
            refine ⟨R - 1, 0, by omega, hA', hS', ?_⟩
            unfold vIdx; rw [if_neg (by omega), if_pos (by omega)]; omega
          · have hBf : B = false := by rw [hB']; simp [ha0]
            rw [if_neg ha0] at hA'
            have hS' : VShape R 1 (cohortEdge R s k) := by
              refine ⟨by omega, fun q hq1 hq2 => ⟨by rw [hlv]; exact (hcell q hq1 hq2).1, ?_, ?_⟩⟩
              · intro hq
                rw [show q = k by omega, hinpk, hBf]; rfl
              · intro hq
                rw [hothI q (by omega)]; exact (hcell q hq1 hq2).2.2 (by omega)
            have ha1 := hA.2.1
            refine ⟨a - 1, 1, by omega, hA', hS', ?_⟩
            unfold vIdx; rw [if_neg (by omega), if_neg (by omega)]; omega
    · have hSk := hck.2.1 (by omega)
      have he := hid (by rw [hSk]; rfl)
      rw [he]
      exact Or.inr ⟨a, i, hai, hA, hS, rfl⟩
  · -- past the pair
    rw [edgeFar R s k (by omega)]
    exact Or.inr ⟨a, i, hai, hA, hS, rfl⟩

/-- **The renewal trial with its exact outcome, on the lane.** Consumer: `vMomentAtCoupled`. -/
theorem vMomentAt {n : Nat} (R : Nat) (hR : 3 ≤ R) (hn : 1 ≤ n) (N : Nat) (hN : n ≤ N)
    (site : Nat → Fin n) (edgeOf : Fin n → Option Nat)
    (hedge : ∀ k, k < 2 * R → edgeOf (site k) = some k) (m : Nat) (s : CohortLane)
    (hs : VIAt R m s) :
    MomentBoundQ (releaseNext R edgeOf) (VTAt R m) N (N ^ vPot R s) ((N - n) ^ vPot R s) s := by
  obtain ⟨a, i, hai, hA, hS, hm⟩ := hs
  have hlane := vMoment R hR hn N hN site edgeOf hedge s ⟨a, i, hai, hA, hS⟩
  exact momentSimQ (releaseNext R edgeOf) (releaseNext R edgeOf)
    (fun x y => x = y ∧ (VTAt R m x ∨ VIAt R m x)) (VTAt R m) (VT R) N _ _
    (fun x y e hxy hna => by
      obtain ⟨rfl, hx⟩ := hxy
      rcases hx with hx | ⟨a', i', hai', hA', hS', hm'⟩
      · exact absurd hx hna
      · refine ⟨rfl, ?_⟩
        show VTAt R m (cohortLaneStep R x (edgeOf e)) ∨ VIAt R m (cohortLaneStep R x (edgeOf e))
        cases edgeOf e with
        | none => exact Or.inr ⟨a', i', hai', hA', hS', hm'⟩
        | some k =>
          rcases vStepIdx R hR x k a' i' hai' hA' hS' with ⟨ha0, hi1, ht⟩ | hv
          · left
            have : vIdx R a' i' = i' := by
              unfold vIdx; rw [if_neg (by omega)]; omega
            rw [← hm', this]; exact ht
          · right; rw [← hm']; exact hv)
    (fun x y hxy hg => by
      obtain ⟨rfl, hx⟩ := hxy
      rcases hx with hx | ⟨a', i', _, _, hS', _⟩
      · exact hx
      · exact absurd hg (shapeNoVT R i' x hS')) s s ⟨rfl, Or.inr ⟨a, i, hai, hA, hS, hm⟩⟩ hlane

/-- **The renewal trial with its exact outcome, on the coupled chain.** From every layout state
whose lane is a trial state of index `m`, the tail settles carry-free at offset `R - 1 - m` with
`E[z^{T_V}] ≤ w^{(R+2)(2R+2)}`. Consumer: the per-pair moment (the race from `RacePend` at the
predicted offset, or the aligned completion at offset `0`). -/
theorem vMomentAtCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (hs : VIAt R m (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VTAt R m (laneOfState ring hbank root lane src R y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hvi : VI R (laneOfState ring hbank root lane src R x) := by
    obtain ⟨a, i, hai, hA, hS, _⟩ := hs
    exact ⟨a, i, hai, hA, hS⟩
  have hlane := vMomentAt R hR (by omega) N (Nat.le_of_lt hN)
    (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
    (fun k hk => cohortEdgeOfSite ring root src R hend k hk) m
    (laneOfState ring hbank root lane src R x) hs
  have hco := momentSimQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => VTAt R m (laneOfState ring hbank root lane src R y)) (VTAt R m) N _ _
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R (by omega) hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by rw [hys.2]; exact hg) x _ ⟨hx, rfl⟩ hlane
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (vPotLe R _ hvi)

/-! ### The serial residue of the queue head -/

/-- **The residue of the oldest pending (or next) serial** in an aligned queue `F^a (T F^(R-1))^…`:
in serial order each group is `F^(R-1) T`, so the head has residue `R - 1 - a` (paper
`h = k mod r`). Consumer: `vOffsetOfRes`. -/
def headRes (R a : Nat) : Nat := R - 1 - a

/-- **The paper's case split of the renewal trial.** At a packet-only cut (empty settled run)
with head residue `h`, the outcome offset `R - 1 - vIdx` is `h` for `1 ≤ h ≤ R - 2` (the
misaligned-tail cut), and `0` for `h = 0` (aligned settlement) and `h = R - 1` (terminal deletion
of the oldest tail, then the aligned group). Consumer: the per-pair moment (choice between the
race and the aligned completion). -/
theorem vOffsetOfRes (R a : Nat) (hR : 3 ≤ R) (ha : a + 1 ≤ R) :
    (1 ≤ headRes R a → headRes R a + 2 ≤ R → R - 1 - vIdx R a 0 = headRes R a) ∧
      (headRes R a = 0 → R - 1 - vIdx R a 0 = 0) ∧
      (headRes R a = R - 1 → R - 1 - vIdx R a 0 = 0) := by
  unfold headRes vIdx
  refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩
  · rw [if_neg (by omega)]; omega
  · rw [if_neg (by omega)]; omega
  · rw [if_pos (by omega)]; omega

/-- A packet-only cut has the trial shape with an empty settled run. Consumer:
`viAtOfPacketOnly`. -/
theorem shapeOfPacketOnly (R : Nat) (hR : 1 ≤ R) (s : CohortLane)
    (hP : L3.PacketMomentRetire.PacketOnly R s) : VShape R 0 s := by
  refine ⟨by omega, fun q hq1 hq2 => ?_⟩
  obtain ⟨h1, h2⟩ := hP (q - R) (by omega)
  have hq : R + (q - R) = q := by omega
  simp only [winOf, liftC, hq, L3.PacketMomentRetire.obW] at h1 h2
  have hl : s.live q = false := by
    cases hlq : s.live q with
    | false => rfl
    | true => rw [hlq] at h2; simp at h2
  refine ⟨hl, fun h => absurd h (by omega), fun _ => ?_⟩
  revert h1 h2
  cases s.inp q with
  | E => intro _ _; exact Or.inl rfl
  | P T => intro _ _; exact Or.inr rfl
  | X => intro _ h; simp [cellIn] at h
  | S T => cases T <;> (intro h _; simp [cellIn, Inp.isS] at h)

/-- **Entry at an aligned packet-only cut with its index.** Consumer: `vMomentAtCoupled` after the
retirement phase. -/
theorem viAtOfPacketOnly (R a : Nat) (s : CohortLane) (hA : AlignExt R a s)
    (hP : L3.PacketMomentRetire.PacketOnly R s) : VIAt R (vIdx R a 0) s :=
  ⟨a, 0, by have := hA.2.1; omega, hA, shapeOfPacketOnly R (by have := hA.2.1; omega) s hP, rfl⟩

/-- The outcome read on the coupled chain: the misaligned-tail cut at the offset of the index.
Consumer: the start of the fair race (`L3.DigitPacketRace.misalignedRace`). -/
theorem vtAtRace {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : VTAt R m (laneOfState ring hbank root lane src R y)) :
    L3.DigitPacketRace.RacePend ring hbank root lane src R (R - 1 - m) y := by
  obtain ⟨hm, hc⟩ := h
  have hq := hc (2 * R - 1 - m) (by omega) (by omega)
  show (laneOfState ring hbank root lane src R y).inp (R + (R - 1 - m)) = .S true ∧
    (laneOfState ring hbank root lane src R y).live (R + (R - 1 - m)) = false
  rw [show R + (R - 1 - m) = 2 * R - 1 - m by omega]
  exact ⟨hq.2.1 rfl, hq.1⟩

end L3.PacketMomentVSerial

#print axioms L3.PacketMomentVSerial.vStepIdx
#print axioms L3.PacketMomentVSerial.vMomentAt
#print axioms L3.PacketMomentVSerial.vMomentAtCoupled
#print axioms L3.PacketMomentVSerial.vOffsetOfRes
#print axioms L3.PacketMomentVSerial.viAtOfPacketOnly
#print axioms L3.PacketMomentVSerial.vtAtRace
