import Leader.L3.Width.DigitQuietEntryValuesFirst

/-!
# The comparison ledger

The analogue of `CarryAll` for the comparison lane.  A physical comparison carry mirrors the ghost
carry; a ledger that is not inherited is a chain of uses at consecutive sites whose carry bit is the
conjunction of "the input is the top digit" and whose error bit records a target digit other than
input plus carry-in (`CheckChain`).  Every use of a ledger has read the target digit of the state
before its own frame.

* `checkInv_pair`, `checkAllStep`, `auditCheckFold`: the invariant along the audit;
* `checkBits`: with the correct digits the bit is the carry-in and the error is false;
* `carryBitsComparison`: the comparison `CarryBits` of a pair at a pin bundle.

Consumer: `L3.QuietEntryValues.pairComparisonOfCut` (WidthDigitQuietEntryValuesFinal).

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3.QuietEntryValues

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.AcceptedReceipts
open L3.DigitQuiet
open L3.QuietEntryPair
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WriterCurrent
open L3.UseTrack
open L3.StageMEntryRun
open L3.Correspondence
open L3.GhostBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

section Rows

variable (c : Compiled) (ox oy : Agent c) (bX bY : Bool)

/-- Leader row of the comparison carry.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_root (h : ox.l = true ∨ oy.l = true) :
    (liveTopPair c ox oy bX bY).x.qCarry = (if ox.qCarry.isL = true then .OFF else ox.qCarry) ∧
      (liveTopPair c ox oy bX bY).y.qCarry = (if oy.qCarry.isL = true then .OFF else oy.qCarry) := by
  rcases h with h | h <;>
    constructor <;>
    simp [liveTopPair, h]

/-- Terminal row.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_terminal (cc ee : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbY : oy.beta = true) (hw : ox.qCarry = .L cc ee) :
    (liveTopPair c ox oy bX bY).x.qCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.qCarry = oy.qCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, QCarry.isL, QCarry.isOff, topTerminal]

/-- Blocked row, destination carry live.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_blockedCarry (cc ee c' e' : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbY : oy.beta = false) (hw : ox.qCarry = .L cc ee) (hy : oy.qCarry = .L c' e') :
    (liveTopPair c ox oy bX bY).x.qCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.qCarry = oy.qCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hy, QCarry.isL, QCarry.isOff, topTerminal]

/-- Blocked row, destination without settled input.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_blockedInput (cc ee : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbY : oy.beta = false) (hw : ox.qCarry = .L cc ee) (hs : oy.qIn.isS = false) :
    (liveTopPair c ox oy bX bY).x.qCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.qCarry = oy.qCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hs, QCarry.isL, QCarry.isOff, topTerminal]

/-- Advance row.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_advance (cc ee : Bool) (v : Fin c.topA) (T : Bool) (hxl : ox.l = false)
    (hyl : oy.l = false) (hbY : oy.beta = false) (hw : ox.qCarry = .L cc ee)
    (hoff : oy.qCarry = .OFF) (hs : oy.qIn = .S v T) :
    (liveTopPair c ox oy bX bY).x.qCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.qCarry = .L (cc && (v.val + 1 == c.topA))
        (ee || (oy.d.val != mod (v.val + (if cc then 1 else 0)) c.topA)) := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, QCarry.isL, QCarry.isOff, InTok.isS,
      topTerminal, inV, qcC, qcE, QC]

/-- Launch row.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_launch (v : Fin c.topA) (T : Bool) (hxl : ox.l = false) (hyl : oy.l = false)
    (hbX : ox.beta = true) (hw : ox.qCarry = .OFF) (hs : ox.qIn = .S v T) :
    (liveTopPair c ox oy bX bY).x.qCarry =
        .L (v.val + 1 == c.topA) (ox.d.val != mod (v.val + 1) c.topA) ∧
      (liveTopPair c ox oy bX bY).y.qCarry = oy.qCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbX, hw, hs, QCarry.isL, QCarry.isOff, InTok.isS, topBorder, inV, QC]

/-- Idle row, source not a delimiter.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_idleBeta (hxl : ox.l = false) (hyl : oy.l = false) (hbX : ox.beta = false)
    (hw : ox.qCarry = .OFF) :
    (liveTopPair c ox oy bX bY).x.qCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.qCarry = oy.qCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hbX, hw, QCarry.isL, QCarry.isOff, topBorder]

/-- Idle row, source without settled input.  Consumer: `checkInv_pair`. -/
theorem liveTop_q_idleInput (hxl : ox.l = false) (hyl : oy.l = false) (hw : ox.qCarry = .OFF)
    (hs : ox.qIn.isS = false) :
    (liveTopPair c ox oy bX bY).x.qCarry = .OFF ∧
      (liveTopPair c ox oy bX bY).y.qCarry = oy.qCarry := by
  constructor <;>
    simp [liveTopPair, hxl, hyl, hw, hs, QCarry.isL, QCarry.isOff]

end Rows

section Chain

variable {c : Compiled} {n : Nat}

/-- The comparison ledger of a carry at site `i`: uses at consecutive sites, carry bit and error bit
as the checker computes them.  Consumer: `CheckInv`, `checkBits`. -/
inductive CheckChain (ring : DirectedRing n) : Fin n → Bool → Bool → List (DigitUse c n) → Prop
  | launch (i : Fin n) (u : DigitUse c n) (ht : u.target = i) (hc : u.carryIn = true) :
      CheckChain ring i (u.value.val + 1 == c.topA)
        (u.targetDigit.val != mod (u.value.val + 1) c.topA) [u]
  | snoc {i : Fin n} {cc ee : Bool} {us : List (DigitUse c n)} (u : DigitUse c n)
      (h : CheckChain ring i cc ee us) (ht : u.target = ring.rightNeighbor i)
      (hc : u.carryIn = cc) :
      CheckChain ring (ring.rightNeighbor i) (cc && (u.value.val + 1 == c.topA))
        (ee || (u.targetDigit.val != mod (u.value.val + (if cc then 1 else 0)) c.topA)) (us ++ [u])

/-- The comparison-carry invariant of one site, with a predicate `P` on the time, target and read
digit of every use.  Consumer: `checkInv_pair`, `CheckAll`. -/
def CheckInv (ring : DirectedRing n) (P : Nat → Fin n → Fin c.topA → Prop) (i : Fin n) (q : QCarry)
    (g : Option (DigitCarryGhost c n)) : Prop :=
  match q with
  | .OFF => g = none
  | .L cc ee => ∃ L : DigitCarryGhost c n, g = some L ∧
      (∀ u, u ∈ L.uses → P u.time u.target u.targetDigit) ∧
      (L.inherited = none → CheckChain ring i cc ee L.uses)

variable {ring : DirectedRing n} {P : Nat → Fin n → Fin c.topA → Prop}

/-- Leader row of the invariant.  Consumer: `checkInv_pair`. -/
theorem checkInv_root (i : Fin n) (q : QCarry) (g : Option (DigitCarryGhost c n))
    (hg : CheckInv ring P i q g) :
    CheckInv ring P i (if q.isL = true then .OFF else q) (if q.isL = true then none else g) := by
  cases q with
  | OFF => simpa [QCarry.isL] using hg
  | L cc ee => simp [QCarry.isL, CheckInv]

/-- **One edge step preserves the comparison-carry invariant**, for the physical row `liveTopPair`
and the ghost row `digitLaneReplay`.  Consumer: `checkAllStep`. -/
theorem checkInv_pair (time : Nat) (source dest : Fin n) (hdest : dest = ring.rightNeighbor source)
    (ox oy : Agent c) (bX bY : Bool) (xv yv : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hl : xv.leader = ox.l) (hyl : yv.leader = oy.l)
    (hcx : xv.carryLive = ox.qCarry.isL) (hcy : yv.carryLive = oy.qCarry.isL)
    (hmx : xv.marker = ox.beta) (hmy : yv.marker = oy.beta)
    (hix : xv.input = ox.qIn) (hiy : yv.input = oy.qIn)
    (hbx : xv.carryBit = qcC ox.qCarry) (hex : xv.carryError = qcE ox.qCarry)
    (hdx : xv.digit = ox.d) (hdy : yv.digit = oy.d)
    (hPx : P time source ox.d) (hPy : P time dest oy.d)
    (hx : CheckInv ring P source ox.qCarry gx.carry) (hy : CheckInv ring P dest oy.qCarry gy.carry) :
    CheckInv ring P source (liveTopPair c ox oy bX bY).x.qCarry
        (digitLaneReplay .comparison time source dest xv yv gx gy).x.carry ∧
      CheckInv ring P dest (liveTopPair c ox oy bX bY).y.qCarry
        (digitLaneReplay .comparison time source dest xv yv gx gy).y.carry := by
  by_cases hroot : ox.l = true ∨ oy.l = true
  · have hr : (xv.leader || yv.leader) = true := by
      rw [hl, hyl]; rcases hroot with h | h <;> simp [h]
    have p := liveTop_q_root c ox oy bX bY hroot
    have g := replay_carry_root .comparison time source dest xv yv gx gy hr
    rw [p.1, p.2, g.1, g.2, hcx, hcy]
    exact ⟨checkInv_root _ _ _ hx, checkInv_root _ _ _ hy⟩
  · have hxl : ox.l = false := by
      cases h : ox.l
      · rfl
      · exact absurd (Or.inl h) hroot
    have hyl' : oy.l = false := by
      cases h : oy.l
      · rfl
      · exact absurd (Or.inr h) hroot
    have hvx : xv.leader = false := by rw [hl, hxl]
    have hvy : yv.leader = false := by rw [hyl, hyl']
    cases hw : ox.qCarry with
    | L cc ee =>
      have hxc : xv.carryLive = true := by rw [hcx, hw]; rfl
      rw [hw] at hx hbx hex
      have hbx' : xv.carryBit = cc := hbx
      have hex' : xv.carryError = ee := hex
      by_cases hbY : oy.beta = true
      · have hm : yv.marker = true := by rw [hmy]; exact hbY
        have p := liveTop_q_terminal c ox oy bX bY cc ee hxl hyl' hbY hw
        have g := replay_carry_terminal .comparison time source dest xv yv gx gy hvx hvy hxc hm
        rw [p.1, p.2, g.1, g.2]
        exact ⟨rfl, hy⟩
      · have hbY' : oy.beta = false := Bool.eq_false_iff.mpr hbY
        have hm : yv.marker = false := by rw [hmy]; exact hbY'
        cases hyw : oy.qCarry with
        | L c' e' =>
          have hyc : yv.carryLive = true := by rw [hcy, hyw]; rfl
          have p := liveTop_q_blockedCarry c ox oy bX bY cc ee c' e' hxl hyl' hbY' hw hyw
          have g := replay_carry_blockedCarry .comparison time source dest xv yv gx gy hvx hvy hxc hm hyc
          rw [p.1, p.2, g.1, g.2, hyw]
          rw [hyw] at hy
          exact ⟨rfl, hy⟩
        | OFF =>
          have hyc : yv.carryLive = false := by rw [hcy, hyw]; rfl
          rw [hyw] at hy
          by_cases hs : oy.qIn.isS = true
          · obtain ⟨v, T, hS⟩ : ∃ v T, oy.qIn = .S v T := by
              cases hI : oy.qIn with
              | S v T => exact ⟨v, T, rfl⟩
              | E => rw [hI] at hs; simp [InTok.isS] at hs
              | X => rw [hI] at hs; simp [InTok.isS] at hs
              | P v T => rw [hI] at hs; simp [InTok.isS] at hs
            have his : yv.input.isS = true := by rw [hiy, hS]; rfl
            have p := liveTop_q_advance c ox oy bX bY cc ee v T hxl hyl' hbY' hw hyw hS
            have g := replay_carry_success .comparison time source dest xv yv gx gy hvx hvy hxc hm hyc his
            rw [p.1, p.2, g.1, g.2]
            refine ⟨rfl, ?_⟩
            obtain ⟨L, hL, hPL, hch⟩ := hx
            rw [hL]
            have hv : inV c yv.input = v := by rw [hiy, hS]; rfl
            refine ⟨_, rfl, fun u hu => ?_, fun hinh => ?_⟩
            · simp only [Option.getD_some, List.mem_append, List.mem_singleton] at hu
              rcases hu with hu | rfl
              · exact hPL u hu
              · simp only [hdy]
                exact hPy
            · simp only [Option.getD_some] at hinh ⊢
              have := CheckChain.snoc (ring := ring)
                ({ time := time, target := dest, operand := gy.input, value := inV c yv.input,
                   tail := inT yv.input, targetDigit := yv.digit, carryIn := xv.carryBit,
                   errorIn := xv.carryError } : DigitUse c n) (hch hinh) hdest hbx'
              dsimp only at this
              have eq1 : (inV c yv.input).val = v.val := by rw [hv]
              have eq2 : yv.digit.val = oy.d.val := by rw [hdy]
              rw [eq1, eq2, ← hdest] at this
              exact this
          · have hs' : oy.qIn.isS = false := Bool.eq_false_iff.mpr hs
            have his : yv.input.isS = false := by rw [hiy]; exact hs'
            have p := liveTop_q_blockedInput c ox oy bX bY cc ee hxl hyl' hbY' hw hs'
            have g := replay_carry_blockedInput .comparison time source dest xv yv gx gy hvx hvy hxc hm his
            rw [p.1, p.2, g.1, g.2, hyw]
            exact ⟨rfl, hy⟩
    | OFF =>
      have hxc : xv.carryLive = false := by rw [hcx, hw]; rfl
      rw [hw] at hx
      have hx0 : gx.carry = none := hx
      by_cases hbX : ox.beta = true
      · by_cases hs : ox.qIn.isS = true
        · obtain ⟨v, T, hS⟩ : ∃ v T, ox.qIn = .S v T := by
            cases hI : ox.qIn with
            | S v T => exact ⟨v, T, rfl⟩
            | E => rw [hI] at hs; simp [InTok.isS] at hs
            | X => rw [hI] at hs; simp [InTok.isS] at hs
            | P v T => rw [hI] at hs; simp [InTok.isS] at hs
          have hm : xv.marker = true := by rw [hmx]; exact hbX
          have his : xv.input.isS = true := by rw [hix, hS]; rfl
          have p := liveTop_q_launch c ox oy bX bY v T hxl hyl' hbX hw hS
          have g := replay_carry_launch .comparison time source dest xv yv gx gy hvx hvy hxc hm his
          rw [p.1, p.2, g.1, g.2]
          refine ⟨⟨_, rfl, fun u hu => ?_, fun _ => ?_⟩, hy⟩
          · simp only [List.mem_singleton] at hu
            subst hu
            simp only [hdx]
            exact hPx
          · have hv : inV c xv.input = v := by rw [hix, hS]; rfl
            have := CheckChain.launch (ring := ring) source
              ({ time := time, target := source, operand := gx.input, value := inV c xv.input,
                 tail := inT xv.input, targetDigit := xv.digit, carryIn := true,
                 errorIn := false } : DigitUse c n) rfl rfl
            dsimp only at this ⊢
            have eq1 : (inV c xv.input).val = v.val := by rw [hv]
            have eq2 : xv.digit.val = ox.d.val := by rw [hdx]
            rw [eq1, eq2] at this
            exact this
        · have hs' : ox.qIn.isS = false := Bool.eq_false_iff.mpr hs
          have his : xv.input.isS = false := by rw [hix]; exact hs'
          have p := liveTop_q_idleInput c ox oy bX bY hxl hyl' hw hs'
          have g := replay_carry_idleInput .comparison time source dest xv yv gx gy hvx hvy hxc his
          rw [p.1, p.2, g.1, g.2, hx0]
          exact ⟨rfl, hy⟩
      · have hbX' : ox.beta = false := Bool.eq_false_iff.mpr hbX
        have hm : xv.marker = false := by rw [hmx]; exact hbX'
        have p := liveTop_q_idleBeta c ox oy bX bY hxl hyl' hbX' hw
        have g := replay_carry_idleMarker .comparison time source dest xv yv gx gy hvx hvy hxc hm
        rw [p.1, p.2, g.1, g.2, hx0]
        exact ⟨rfl, hy⟩

/-- The predicate of a use of the audit: its target digit is read at its own frame.  Consumer:
`CheckAll`. -/
def FramedRead (A : DigitAudit c n) : Nat → Fin n → Fin c.topA → Prop :=
  fun t i d => ∃ f ∈ A.frames, f.time = t ∧ d = (f.old i).top.d

/-- The comparison-carry invariant at every site of the audit.  Consumer: `auditCheckFold`. -/
def CheckAll (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  ∀ i, CheckInv ring (FramedRead A) i (S i).top.qCarry (A.current i).comparison.carry

/-- `CheckInv` is monotone in the predicate.  Consumer: `checkAllStep`. -/
theorem checkInvMono {P Q : Nat → Fin n → Fin c.topA → Prop}
    (h : ∀ t i d, P t i d → Q t i d) (i : Fin n) (q : QCarry) (g : Option (DigitCarryGhost c n))
    (hg : CheckInv ring P i q g) : CheckInv ring Q i q g := by
  cases q with
  | OFF => exact hg
  | L cc ee =>
    obtain ⟨L, h1, h2, h3⟩ := hg
    exact ⟨L, h1, fun u hu => h _ _ _ (h2 u hu), h3⟩

/-- **The invariant is preserved by one audited edge.**  Consumer: `auditCheckFold`. -/
theorem checkAllStep (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) (h : CheckAll ring S A) :
    CheckAll ring (phiD ring S e) (digitAuditStep ring S A e) := by
  intro i
  have hmono : ∀ j q g, CheckInv ring (FramedRead A) j q g →
      CheckInv ring (FramedRead (digitAuditStep ring S A e)) j q g := fun j q g =>
    checkInvMono (fun t k d ⟨f, hf, h1, h2⟩ => ⟨f, List.mem_cons_of_mem _ hf, h1, h2⟩) j q g
  have hnew : ∀ k, FramedRead (digitAuditStep ring S A e) (A.clock + 1) k (S k).top.d :=
    fun k => ⟨_, List.mem_cons_self .., rfl, rfl⟩
  have hs := checkInv_pair (P := FramedRead (digitAuditStep ring S A e)) (ring := ring) (A.clock + 1)
    e (ring.rightNeighbor e) rfl (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta
    (digitLaneView .comparison (S e) (S e).word.beta)
    (digitLaneView .comparison (S (ring.rightNeighbor e)) (S (ring.rightNeighbor e)).word.beta)
    (A.current e).comparison (A.current (ring.rightNeighbor e)).comparison
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (hnew e) (hnew _)
    (hmono _ _ _ (h e)) (hmono _ _ _ (h (ring.rightNeighbor e)))
  by_cases hie : i = e
  · subst hie
    simpa [phiD, projectedEdge, digitAuditStep, digitGhostStep, pairD, topD, digitService] using hs.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      simpa [phiD, projectedEdge, digitAuditStep, digitGhostStep, hie, pairD, topD, digitService]
        using hs.2
    · have := hmono _ _ _ (h i)
      simpa [phiD, projectedEdge, digitAuditStep, digitGhostStep, hie, hij] using this

/-- The invariant at the initial audit: live carries are inherited.  Consumer: `auditCheckFold`. -/
theorem checkAllInitial (S : Fin n → ProjD c) : CheckAll ring S (digitAuditInitial S) := by
  intro i
  show CheckInv ring _ i (S i).top.qCarry (digitGhostInitial S i).comparison.carry
  cases hq : (S i).top.qCarry with
  | OFF =>
    simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hq,
      QCarry.isL, CheckInv]
  | L cc ee =>
    simp only [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hq,
      QCarry.isL, CheckInv, if_true]
    exact ⟨_, rfl, fun u hu => by simp at hu, fun h => by simp at h⟩

/-- **The comparison ledger along the audit fold from a drained start.**  Consumer:
`carryBitsComparison`. -/
theorem auditCheckFold {ring : DirectedRing n} (ref : WidthDigitReference ring) (w : List (Fin n)) :
    ∀ p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ref.drained p.1 → CheckAll ring (piD (ref.phys p.1)) p.2 →
      CheckAll ring (piD (ref.phys (w.foldl (widthDigitAuditNext ref) p).1))
        (w.foldl (widthDigitAuditNext ref) p).2 := by
  induction w with
  | nil => intro p _ hi; exact hi
  | cons e w ih =>
    intro p hd hi
    simp only [List.foldl_cons]
    apply ih
    · exact ref.drainedClosed p.1 hd e
    · show CheckAll ring (piD (ref.phys (ref.next p.1 e))) _
      rw [ref.digitStep p.1 hd e]
      exact checkAllStep _ _ e hi

/-- Consumer: `checkBits`. -/
theorem natBeqDecide (a b : Nat) : (a == b) = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by simp)

/-- **With the correct digits the comparison ledger has carry bit the carry-in and no error.**
Consumer: `carryBitsComparison`. -/
theorem checkBits (root : Fin n) (hn2 : 2 ≤ n) (Dp Dt : Nat → Fin c.topA) (b : Nat)
    {i : Fin n} {cc ee : Bool} {us : List (DigitUse c n)} (h : CheckChain ring i cc ee us)
    (hv : ∀ m (u : DigitUse c n), us[m]? = some u → u.value = Dp m)
    (hD : ∀ m (u : DigitUse c n), us[m]? = some u → u.target = digitSite ring root (b + m) →
      u.targetDigit = Dt m)
    (hE : ∀ m, m < us.length → Dt m = c.digitMod ((Dp m).val + (if carryInto Dp m then 1 else 0)))
    (hi : i = digitSite ring root (b + us.length - 1)) (hb : b + us.length ≤ n) :
    cc = carryInto Dp us.length ∧ ee = false := by
  induction h with
  | launch i u ht hc =>
    have hv0 := hv 0 u rfl
    have hD0 := hD 0 u rfl (by rw [ht, hi]; rfl)
    have hE0 := hE 0 (by simp)
    constructor
    · simp [carryInto, hv0, natBeqDecide]
    · have hval : (Dt 0).val = mod ((Dp 0).val + 1) c.topA := by
        rw [hE0]
        simp [carryInto, Compiled.digitMod]
      simp [hD0, hv0, hval]
  | @snoc i cc ee us u h ht hc ih =>
    have hlen : (us ++ [u]).length = us.length + 1 := by simp
    rw [hlen] at hi hb
    have hpos : 0 < us.length := by
      cases h <;> simp
    have hi' : i = digitSite ring root (b + us.length - 1) := by
      have e1 : digitSite ring root (b + us.length - 1 + 1) = ring.rightNeighbor i := by
        rw [show b + us.length - 1 + 1 = b + (us.length + 1) - 1 by omega]
        exact hi.symm
      exact leftOfSite root i hn2 _ (by omega) e1 (by omega)
    have hget : ∀ (m : Nat) (x : DigitUse c n), us[m]? = some x → (us ++ [u])[m]? = some x := by
      intro m x hm
      have hlt := (List.getElem?_eq_some_iff.mp hm).1
      rw [List.getElem?_append_left hlt]
      exact hm
    obtain ⟨h1, h2⟩ := ih (fun m x hm => hv m x (hget m x hm)) (fun m x hm => hD m x (hget m x hm))
      (fun m hm => hE m (by rw [hlen]; omega)) hi' (by omega)
    have hlast : (us ++ [u])[us.length]? = some u := by simp
    have hv1 := hv _ u hlast
    have hE1 := hE us.length (by rw [hlen]; omega)
    have hsite : u.target = digitSite ring root (b + us.length) := by
      rw [ht, hi]
      show _ = digitSite ring root (b + us.length)
      rw [show b + (us.length + 1) - 1 = b + us.length by omega]
    have hD1 := hD _ u hlast hsite
    rw [hlen]
    subst h1
    subst h2
    constructor
    · simp [carryInto, hv1, natBeqDecide]
    · have hval : (Dt us.length).val =
          mod ((Dp us.length).val + (if carryInto Dp us.length then 1 else 0)) c.topA := by
        rw [hE1]
        rfl
      simp [hD1, hv1, hval]

end Chain

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (root : Fin n) (src R : Nat)

/-- **The comparison `CarryBits` of a pair at a pin bundle**: from the ledger of the bundle, the
digits of the target as read since the bundle was born and the digit equations of the pair.
Consumer: `pairComparisonOfCut`. -/
theorem carryBitsComparison (hn2 : 2 ≤ n) (start : ref.State) (hd : ref.drained start)
    (w : List (Fin n)) (after born : Nat) (g : (Nat → Nat) × Nat) (hend : src + 2 * R ≤ n)
    (h : PairBundle ref root DigitLane.comparison src R after born
      (stateAt ref start w w.length, g))
    (hDig : SamplesCurrent ring root DigitLane.comparison src R after
      (stateAt ref start w w.length).2 (piD (ref.phys (stateAt ref start w w.length).1)))
    (hQ : ∀ k, k < R → ∀ t, born ≤ t → t < w.length →
      digitAt ref start w t (digitSite ring root (src + R + k)) =
        digitAt ref start w w.length (digitSite ring root (src + R + k)))
    (hE : ∀ k, k < R → digitAt ref start w w.length (digitSite ring root (src + R + k)) =
      (compileAdvice (ceilLogTwo n)).digitMod
        ((digitAt ref start w w.length (digitSite ring root (src + k))).val +
          (if carryInto (fun m => digitAt ref start w w.length (digitSite ring root (src + m))) k
            then 1 else 0))) :
    CarryBits R (fun k => view ring root (piD (ref.phys (stateAt ref start w w.length).1))
        DigitLane.comparison (src + R + k))
      (fun k => (piD (ref.phys (stateAt ref start w w.length).1)
        (digitSite ring root (src + k))).top.d) := by
  intro k hk hl
  have hT := scanTieOfProj (root := root) (lane := DigitLane.comparison) (src := src) (R := R)
    (ring := ring) (piD (ref.phys (stateAt ref start w w.length).1))
  have hc1 := cycleOfLive ref root src R DigitLane.comparison after born _ h (R + k) (by omega)
    (by omega) (by rw [hT.live k hk]; exact hl)
  have hsite : digitSite ring root (src + R + k) = digitSite ring root (src + (R + k)) := by
    rw [Nat.add_assoc]
  have hfoldEq : stateAt ref start w w.length = w.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) := by
    unfold stateAt
    rw [List.take_length]
  have hck : CheckAll ring (piD (ref.phys (stateAt ref start w w.length).1))
      (stateAt ref start w w.length).2 := by
    rw [hfoldEq]
    exact auditCheckFold ref w (start, _) hd (checkAllInitial _)
  have hcar := hck (digitSite ring root (src + R + k))
  cases hq : (piD (ref.phys (stateAt ref start w w.length).1)
      (digitSite ring root (src + R + k))).top.qCarry with
  | OFF =>
    exfalso
    simp [view, digitEndpointView, digitLaneView, hq, QCarry.isL] at hl
  | L cc ee =>
    rw [hq] at hcar
    obtain ⟨L, hL, hP, hch⟩ := hcar
    have hLq : caA ring root DigitLane.comparison src (stateAt ref start w w.length).2 (R + k) =
        some L := by
      unfold caA laneCells laneGhost
      rw [← hsite]
      exact hL
    obtain ⟨hinh, hlen, hv⟩ := ledgerValsOfBundle ref root src R DigitLane.comparison after born _ h
      hDig hc1 (R + k) (by omega) (by omega) L hLq
    have hlen' : L.uses.length = k + 1 := by omega
    obtain ⟨h1, h2⟩ := checkBits (ring := ring) root hn2
      (fun m => (piD (ref.phys (stateAt ref start w w.length).1)
        (digitSite ring root (src + m))).top.d)
      (fun m => (piD (ref.phys (stateAt ref start w w.length).1)
        (digitSite ring root (src + R + m))).top.d) (src + R) (hch hinh)
      (fun m u hm => (hv m u hm).1)
      (fun m u hm htg => by
        have hmem : u ∈ L.uses := List.mem_iff_getElem?.mpr ⟨m, hm⟩
        obtain ⟨f, hf, hft, hfd⟩ := hP u hmem
        have hfr : f ∈ (w.foldl (widthDigitAuditNext ref)
            (start, digitAuditInitial (piD (ref.phys start)))).2.frames := by
          rw [← hfoldEq]
          exact hf
        obtain ⟨f1, f2, f3, -⟩ := frameLink ref start w hd f hfr
        have hb := (hv m u hm).2
        have hml : m < R := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          omega
        rw [hfd, f3, hft, htg]
        exact hQ m hml _ (by omega) (by omega))
      (fun m hm => hE m (by omega))
      (by rw [hlen']; rw [show src + R + (k + 1) - 1 = src + R + k by omega]) (by omega)
    rw [hlen'] at h1
    have hbit : (view ring root (piD (ref.phys (stateAt ref start w w.length).1))
        DigitLane.comparison (src + R + k)).carryBit = cc := by
      simp [view, digitEndpointView, digitLaneView, hq, qcC]
    have herr : (view ring root (piD (ref.phys (stateAt ref start w w.length).1))
        DigitLane.comparison (src + R + k)).carryError = ee := by
      simp [view, digitEndpointView, digitLaneView, hq, qcE]
    exact ⟨hbit.trans h1, herr.trans h2⟩

end L3.QuietEntryValues

#print axioms L3.QuietEntryValues.checkInv_pair
#print axioms L3.QuietEntryValues.auditCheckFold
#print axioms L3.QuietEntryValues.checkBits
#print axioms L3.QuietEntryValues.carryBitsComparison
