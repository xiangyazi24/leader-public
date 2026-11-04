import Leader.L3.Bank.RepairDigitTailChainRun

/-!
# Group coherence on the source side: nothing descended from a tail overtakes it

`L3.TailChain` carries, for every border-tail stamp `sigma0`, the cells BEHIND the packet
`sampled sigma0` (they name tails ranked from `sigma0`). The completion rank of clause (R) also
needs the cells AHEAD of it: every rearm tail ahead of `sampled sigma0` is older than `sigma0`.
This module proves that on the actual audit and derives the coherence of a completion group.

* `AheadCell b A o g`: the rearm tail of a `U`, the cause tail of a `D` cell's sample and the
  atom of a `D true` are all older than `b`.
* `CellBound`: every source cell is `AheadCell (clock + 1)`; `ExpCause`: the sample of every
  delimiter export has a cause tail older than the export.
* `AheadBar`, `AheadAt sigma0`: the packet `sampled sigma0` sits at cell `p` (or was exported,
  `p = R`) and every cell ahead of `p` is `AheadCell sigma0.time`; `sigma0`'s own cause tail is
  older than `sigma0`; and `ExpBefore`: an export whose sample's cause tail is no older than
  `sigma0` comes after the export of `sigma0`.
* `SrcLetter`: one audit letter on the source block, in the three shapes of
  `L3.TailChain.barrierStep` (frame, Pipe, Del); `srcLetterRing` proves it on the projected ring.
* `aheadRunStep`, `aheadRunInitial`: `AheadRun` (the three clauses for every `sigma0`) is a run
  invariant.
* `groupCause`: at any state carrying `TailInv`, `AheadRun`, the frame order and the distinct
  correspondence, a completion whose tail sample is later than a recorded border tail `sigma0`
  is `DigitTerminalRanked` from `sigma0`: all its samples name the same border tail, the cause
  tail of its own tail sample (upper bound from `ExpBefore` at the tail, lower bound from
  `ExportRanked` at the cause tail, equality from the latest-tail clause of `BorderChain`).
-/

namespace L3.TailAhead

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.TailChain

/-! ### Cells ahead -/

section Cells

variable {c : Compiled} {n : Nat}

/-- **A cell older than `b`**: the rearm tail of a `U`, the cause tail of the sample of a `D`,
and the atom of a `D true` are stamped before `b`. Consumer: `CellBound`, `AheadBar`. -/
def AheadCell (b : Nat) (A : DigitAudit c n) : BankRepairDigitOutSh → DigitOutGhost n → Prop
  | .E, _ => True
  | .U, g => ∀ rho tl : DigitStamp n,
      g = .unread (.afterTail rho (some (.sampled tl))) → tl.time < b
  | .D T, g => (T = true → ∀ id : DigitStamp n, g.atom = some (.sampled id) → id.time < b) ∧
      ∀ smp : DigitSample c n, DigitRecordedSample A smp → g.atom = some (.sampled smp.id) →
        ∀ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) →
          tl.time < b

/-- `AheadCell` under a larger bound and a grown audit (old atoms are older than the new frame).
Consumer: every step lemma below. -/
theorem aheadCellMono {A A' : DigitAudit c n} {b b' : Nat} (hb : b ≤ b')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (o : BankRepairDigitOutSh) (g : DigitOutGhost n)
    (hTB : ∀ id : DigitStamp n, g.atom = some (.sampled id) → id.time ≤ A.clock)
    (h : AheadCell b A o g) : AheadCell b' A' o g := by
  cases o with
  | E => trivial
  | U =>
    intro rho tl hg
    have := h rho tl hg
    omega
  | D T =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hT id hid => ?_, fun smp hs hat rho tl hc => ?_⟩
    · have := h1 hT id hid
      omega
    · rcases hnewT smp hs with hs' | ht
      · have := h2 smp hs' hat rho tl hc
        omega
      · have := hTB smp.id hat
        omega

/-- An obligation names the unread ghost it came from. Consumer: `aheadPipeRow`,
`aheadAtStep`. -/
theorem obligationUnread (g : DigitOutGhost n) (u : DigitUnread n)
    (h : g.obligation = some u) : g = .unread u := by
  cases g with
  | empty => cases h
  | unread u' =>
    have h' : some u' = some u := h
    cases h'
    rfl
  | packet a => cases h

/-- A fresh `D` cell made by a `U` read is older than `b` once the `U` was. Consumer:
`aheadPipeRow`, `aheadDelRow`. -/
theorem aheadFresh {A' : DigitAudit c n} (hfo' : AuditFrameOrder A') (b : Nat)
    (stamp : DigitStamp n) (T : Bool) (hT : T = true → stamp.time < b) (gxo : DigitOutGhost n)
    (hx : AheadCell b A' .U gxo)
    (hnew : ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = gxo.obligation) :
    AheadCell b A' (.D T) (.packet (some (.sampled stamp))) := by
  obtain ⟨s1, hid1, hs1, hc1⟩ := hnew
  refine ⟨fun hTt id hid => ?_, fun smp hs hat rho tl hc => ?_⟩
  · have hid' : some (DigitAtom.sampled stamp) = some (DigitAtom.sampled id) := hid
    cases hid'
    exact hT hTt
  · have hat' : some (DigitAtom.sampled stamp) = some (DigitAtom.sampled smp.id) := hat
    have hsid : stamp = smp.id := by cases hat'; rfl
    have hss : s1 = smp := recordedSampleUnique hfo' hs1 hs (by rw [hid1, hsid])
    subst hss
    rw [hc1] at hc
    exact hx rho tl (obligationUnread gxo _ hc)

/-- A rearm left by a departing `D true` older than `b` is older than `b`. Consumer:
`aheadPipeRow`, `aheadDelRow`. -/
theorem aheadRearm {A : DigitAudit c n} (b : Nat) (stamp : DigitStamp n) (gxo : DigitOutGhost n)
    (hx : AheadCell b A (.D true) gxo) :
    AheadCell b A .U (.unread (.afterTail stamp gxo.atom)) := by
  intro rho tl hg
  have hat : gxo.atom = some (.sampled tl) := by
    simp only [DigitOutGhost.unread.injEq, DigitUnread.afterTail.injEq] at hg
    exact hg.2
  exact hx.1 rfl tl hat

/-- A `D` cell is read only through its atom. Consumer: `aheadPipeRow`. -/
theorem aheadPacketAtom {A : DigitAudit c n} (b : Nat) (T : Bool) (gxo : DigitOutGhost n)
    (hx : AheadCell b A (.D T) gxo) : AheadCell b A (.D T) (.packet gxo.atom) := hx

/-- **Pipe rows on two cells older than `b`**: a `U` read mints a `D` whose sample names the
old rearm tail; a departing `D true` rearms with its own atom; moves and blocks keep atoms.
Consumer: `cellBoundStep`, `aheadBarStep`. -/
theorem aheadPipeRow {A A' : DigitAudit c n} (b : Nat) (hfo' : AuditFrameOrder A')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (stamp : DigitStamp n) (bx : Bool) (hbx : bx = true → stamp.time < b)
    (ox oy : BankRepairDigitOutSh) (gxo gyo : DigitOutGhost n)
    (hTBx : ∀ id : DigitStamp n, gxo.atom = some (.sampled id) → id.time ≤ A.clock)
    (hTBy : ∀ id : DigitStamp n, gyo.atom = some (.sampled id) → id.time ≤ A.clock)
    (hx : AheadCell b A ox gxo) (hy : AheadCell b A oy gyo)
    (hnew : ox = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = gxo.obligation) :
    AheadCell b A' (bankRepairDigitPipeStep bx ox oy).1 (ghostPipe stamp bx ox oy gxo gyo).1 ∧
      AheadCell b A' (bankRepairDigitPipeStep bx ox oy).2 (ghostPipe stamp bx ox oy gxo gyo).2 := by
  have hx' := aheadCellMono (Nat.le_refl b) hnewT ox gxo hTBx hx
  have hy' := aheadCellMono (Nat.le_refl b) hnewT oy gyo hTBy hy
  cases ox with
  | E =>
    cases bx
    · exact ⟨hx', hy'⟩
    · refine ⟨fun rho tl hg => ?_, hy'⟩
      cases hg
  | U =>
    exact ⟨aheadFresh hfo' b stamp bx hbx gxo hx' (hnew rfl), hy'⟩
  | D T =>
    cases oy with
    | E =>
      cases T
      · exact ⟨trivial, aheadPacketAtom b false gxo hx'⟩
      · exact ⟨aheadRearm b stamp gxo hx', aheadPacketAtom b true gxo hx'⟩
    | U => exact ⟨hx', hy'⟩
    | D T' => exact ⟨hx', hy'⟩

/-- **The Del row on a cell older than `b`**. Consumer: `cellBoundStep`, `aheadBarStep`. -/
theorem aheadDelRow {A A' : DigitAudit c n} (b : Nat) (hfo' : AuditFrameOrder A')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n))
    (hTBx : ∀ id : DigitStamp n, gxo.atom = some (.sampled id) → id.time ≤ A.clock)
    (hx : AheadCell b A ox gxo)
    (hnew : ox = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = gxo.obligation) :
    AheadCell b A' (bankRepairDigitDelStep ox iy ky).1 (ghostDel stamp ox iy ky gxo gyi).1 := by
  have hx' := aheadCellMono (Nat.le_refl b) hnewT ox gxo hTBx hx
  cases ox with
  | E => exact hx'
  | U => exact aheadFresh hfo' b stamp false (fun h => absurd h (by decide)) gxo hx' (hnew rfl)
  | D T =>
    cases ky
    · cases iy with
      | E =>
        cases T
        · exact trivial
        · exact aheadRearm b stamp gxo hx'
      | X => exact hx'
      | P T' => exact hx'
      | S T' => exact hx'
    · exact hx'

end Cells

/-! ### One letter on the source block -/

section Letter

variable {c : Compiled} {n : Nat}

/-- **One audit letter on the source block** (outputs `o`, ghosts `go` before; `o'`, `go'`
after), in the three shapes of `L3.TailChain.barrierStep`: framed, a Pipe edge `k → k+1`, or the
Del edge `R-1 → R`; with the new border samples (only a `U` read at the border) and the new
delimiter exports (only the Del edge, carrying the old atom of cell `R-1`; an accepted `D`
exports). Consumer: `cellBoundStep`, `expCauseStep`, `aheadBarStep`, `aheadAtStep`. -/
def SrcLetter (R : Nat) (src0 : Fin n) (lane : DigitLane) (A A' : DigitAudit c n)
    (OnE : DigitExport c n → Prop) (o o' : Nat → BankRepairDigitOutSh)
    (go go' : Nat → DigitOutGhost n) : Prop :=
  ((∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp) ∧
    (∀ x : DigitExport c n, DigitRecordedExport A' x → OnE x → DigitRecordedExport A x) ∧
    (∀ q, q < R → o' q = o q ∧ go' q = go q)) ∨
  (∃ (k : Nat) (stamp : DigitStamp n), k + 1 < R ∧ stamp.time = A.clock + 1 ∧
    o' k = (bankRepairDigitPipeStep (decide (k = 0)) (o k) (o (k + 1))).1 ∧
    o' (k + 1) = (bankRepairDigitPipeStep (decide (k = 0)) (o k) (o (k + 1))).2 ∧
    go' k = (ghostPipe stamp (decide (k = 0)) (o k) (o (k + 1)) (go k) (go (k + 1))).1 ∧
    go' (k + 1) = (ghostPipe stamp (decide (k = 0)) (o k) (o (k + 1)) (go k) (go (k + 1))).2 ∧
    (∀ q, q < R → q ≠ k → q ≠ k + 1 → o' q = o q ∧ go' q = go q) ∧
    (o k = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = (go k).obligation) ∧
    (∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp ∨ (k = 0 ∧ o 0 = .U ∧ smp.id = stamp)) ∧
    (∀ x : DigitExport c n, DigitRecordedExport A' x → OnE x → DigitRecordedExport A x)) ∨
  (∃ (k : Nat) (stamp : DigitStamp n) (iy : BankRepairDigitInSh) (ky : Bool)
      (gyi : Option (DigitAtom n)), k + 1 = R ∧ stamp.time = A.clock + 1 ∧
    o' k = (bankRepairDigitDelStep (o k) iy ky).1 ∧
    go' k = (ghostDel stamp (o k) iy ky (go k) gyi).1 ∧
    (∀ q, q < R → q ≠ k → o' q = o q ∧ go' q = go q) ∧
    (o k = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = (go k).obligation) ∧
    (∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp) ∧
    (∀ x : DigitExport c n, DigitRecordedExport A' x → OnE x → DigitRecordedExport A x ∨
      (x.time = A.clock + 1 ∧ (∃ T, o k = .D T) ∧ x.operand = (go k).atom)) ∧
    (∀ T, o k = .D T → iy = .E → ky = false → ∃ x0 : DigitExport c n,
      DigitRecordedExport A' x0 ∧ OnE x0 ∧ x0.operand = (go k).atom))

/-- **Every source cell is older than the next frame.** Consumer: `AheadRun`. -/
def CellBound (R : Nat) (A : DigitAudit c n) (o : Nat → BankRepairDigitOutSh)
    (go : Nat → DigitOutGhost n) : Prop :=
  ∀ q, q < R → AheadCell (A.clock + 1) A (o q) (go q)

/-- **The sample of every delimiter export names a tail older than the export.** Consumer:
`AheadRun`, `aheadAtStep`. -/
def ExpCause (A : DigitAudit c n) (OnE : DigitExport c n → Prop) : Prop :=
  ∀ (x : DigitExport c n) (smp : DigitSample c n), DigitRecordedExport A x → OnE x →
    x.operand = some (.sampled smp.id) → DigitRecordedSample A smp →
    ∀ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) →
      tl.time < x.time

/-- **Nothing descended from `sigma0` is exported before `sigma0`.** Consumer: `AheadAt`,
`groupCause`. -/
def ExpBefore (A : DigitAudit c n) (sigma0 : DigitStamp n) (OnE : DigitExport c n → Prop) :
    Prop :=
  ∀ (x : DigitExport c n) (smp : DigitSample c n), DigitRecordedExport A x → OnE x →
    x.operand = some (.sampled smp.id) → DigitRecordedSample A smp →
    ∀ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) →
      sigma0.time ≤ tl.time →
      ∃ x0 : DigitExport c n, DigitRecordedExport A x0 ∧ OnE x0 ∧
        x0.operand = some (.sampled sigma0) ∧ x0.time < x.time

/-- **The packet of `sigma0` and the cells ahead of it**: it sits at cell `p < R` as a `D true`,
or it was exported (`p = R`); every cell ahead of `p` is older than `sigma0`. Consumer:
`AheadAt`. -/
def AheadBar (R : Nat) (A : DigitAudit c n) (sigma0 : DigitStamp n)
    (OnE : DigitExport c n → Prop) (o : Nat → BankRepairDigitOutSh)
    (go : Nat → DigitOutGhost n) : Prop :=
  ∃ p, p ≤ R ∧ (p < R → o p = .D true ∧ (go p).atom = some (.sampled sigma0)) ∧
    (p = R → ∃ x0 : DigitExport c n, DigitRecordedExport A x0 ∧ OnE x0 ∧
      x0.operand = some (.sampled sigma0)) ∧
    ∀ j, p < j → j < R → AheadCell sigma0.time A (o j) (go j)

/-- **The ahead invariant of one border tail** (vacuous before `sigma0` is minted). Consumer:
`AheadRun`, `groupCause`. -/
def AheadAt (R : Nat) (src0 : Fin n) (lane : DigitLane) (A : DigitAudit c n)
    (OnE : DigitExport c n → Prop) (sigma0 : DigitStamp n) (o : Nat → BankRepairDigitOutSh)
    (go : Nat → DigitOutGhost n) : Prop :=
  (∃ s0 : DigitSample c n, DigitRecordedSample A s0 ∧ s0.id = sigma0) →
  sigma0.site = src0 → sigma0.lane = lane →
  (∀ s0 : DigitSample c n, DigitRecordedSample A s0 → s0.id = sigma0 →
    ∀ rho tl : DigitStamp n, s0.cause = some (.afterTail rho (some (.sampled tl))) →
      tl.time < sigma0.time) ∧
  AheadBar R A sigma0 OnE o go ∧ ExpBefore A sigma0 OnE

variable {R : Nat} {src0 : Fin n} {lane : DigitLane} {A A' : DigitAudit c n}
  {OnE : DigitExport c n → Prop} {o o' : Nat → BankRepairDigitOutSh}
  {go go' : Nat → DigitOutGhost n}

/-- **`CellBound` across one letter.** Consumer: `aheadRunStep`. -/
theorem cellBoundStep (hS : SrcLetter R src0 lane A A' OnE o o' go go')
    (hclk : A'.clock = A.clock + 1) (hfo' : AuditFrameOrder A')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (hTB : ∀ q, q < R → ∀ id : DigitStamp n, (go q).atom = some (.sampled id) → id.time ≤ A.clock)
    (h : CellBound R A o go) : CellBound R A' o' go' := by
  have up : ∀ q, q < R → AheadCell (A.clock + 2) A (o q) (go q) := fun q hq =>
    aheadCellMono (by omega) (fun smp hs => Or.inl hs) _ _ (hTB q hq) (h q hq)
  have keep : ∀ q, q < R → AheadCell (A'.clock + 1) A' (o q) (go q) := fun q hq =>
    aheadCellMono (by omega) hnewT _ _ (hTB q hq) (h q hq)
  intro q hq
  rcases hS with ⟨-, -, hfr⟩ | ⟨k, stamp, hk, hst, o1, o2, g1, g2, hfr, hnew, -, -⟩ |
      ⟨k, stamp, iy, ky, gyi, hk, hst, o1, g1, hfr, hnew, -, -, -⟩
  · rw [(hfr q hq).1, (hfr q hq).2]
    exact keep q hq
  · obtain ⟨n1, n2⟩ := aheadPipeRow (A.clock + 2) hfo' hnewT stamp (decide (k = 0))
      (fun _ => by omega) (o k) (o (k + 1)) (go k) (go (k + 1)) (hTB k (by omega))
      (hTB (k + 1) hk) (up k (by omega)) (up (k + 1) hk) hnew
    rw [hclk]
    by_cases e1 : q = k
    · subst e1
      rw [o1, g1]
      exact n1
    · by_cases e2 : q = k + 1
      · subst e2
        rw [o2, g2]
        exact n2
      · rw [(hfr q hq e1 e2).1, (hfr q hq e1 e2).2, ← hclk]
        exact keep q hq
  · have n1 := aheadDelRow (A.clock + 2) hfo' hnewT stamp (o k) iy ky (go k) gyi
      (hTB k (by omega)) (up k (by omega)) hnew
    rw [hclk]
    by_cases e1 : q = k
    · subst e1
      rw [o1, g1]
      exact n1
    · rw [(hfr q hq e1).1, (hfr q hq e1).2, ← hclk]
      exact keep q hq

/-- **`ExpCause` across one letter**: a new export carries the atom of cell `R-1`, older than
the new frame by `CellBound`. Consumer: `aheadRunStep`. -/
theorem expCauseStep (hS : SrcLetter R src0 lane A A' OnE o o' go go')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (hTB : ∀ q, q < R → ∀ id : DigitStamp n, (go q).atom = some (.sampled id) → id.time ≤ A.clock)
    (hXT : ∀ (x : DigitExport c n) (id : DigitStamp n), DigitRecordedExport A x → OnE x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ A.clock)
    (hcb : CellBound R A o go) (h : ExpCause A OnE) : ExpCause A' OnE := by
  have hold : ∀ (x : DigitExport c n) (smp : DigitSample c n), DigitRecordedExport A x →
      OnE x → x.operand = some (.sampled smp.id) → DigitRecordedSample A' smp →
      ∀ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) →
        tl.time < x.time := by
    intro x smp hx he hop hs rho tl hc
    rcases hnewT smp hs with hs' | ht
    · exact h x smp hx he hop hs' rho tl hc
    · have := hXT x smp.id hx he hop
      omega
  intro x smp hx he hop hs rho tl hc
  rcases hS with ⟨-, hX, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, hX⟩ |
      ⟨k, stamp, iy, ky, gyi, hk, hst, -, -, -, -, -, hX, -⟩
  · exact hold x smp (hX x hx he) he hop hs rho tl hc
  · exact hold x smp (hX x hx he) he hop hs rho tl hc
  · rcases hX x hx he with hx' | ⟨ht, ⟨T, hT⟩, hopx⟩
    · exact hold x smp hx' he hop hs rho tl hc
    · have hcell := hcb k (by omega)
      rw [hT] at hcell
      have hat : (go k).atom = some (.sampled smp.id) := by rw [← hopx, hop]
      rcases hnewT smp hs with hs' | hts
      · have := hcell.2 smp hs' hat rho tl hc
        omega
      · have := hTB k (by omega) smp.id hat
        omega

/-- **The packet of an old `sigma0` and the cells ahead of it across one letter.** Consumer:
`aheadAtStep`. -/
theorem aheadBarStep (sigma0 : DigitStamp n) (hS : SrcLetter R src0 lane A A' OnE o o' go go')
    (hfo' : AuditFrameOrder A')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (hrecX : ∀ x : DigitExport c n, DigitRecordedExport A x → DigitRecordedExport A' x)
    (hTB : ∀ q, q < R → ∀ id : DigitStamp n, (go q).atom = some (.sampled id) → id.time ≤ A.clock)
    (h : AheadBar R A sigma0 OnE o go) : AheadBar R A' sigma0 OnE o' go' := by
  obtain ⟨p, hpR, hpos, hpex, hcells⟩ := h
  have hpex' : p = R → ∃ x0 : DigitExport c n, DigitRecordedExport A' x0 ∧ OnE x0 ∧
      x0.operand = some (.sampled sigma0) := fun hp =>
    (hpex hp).elim fun x0 ⟨a, b, d⟩ => ⟨x0, hrecX x0 a, b, d⟩
  have hcellM : ∀ j, p < j → j < R → AheadCell sigma0.time A' (o j) (go j) := fun j h1 h2 =>
    aheadCellMono (Nat.le_refl _) hnewT _ _ (hTB j h2) (hcells j h1 h2)
  rcases hS with ⟨-, -, hfr⟩ | ⟨k, stamp, hk, hst, o1, o2, g1, g2, hfr, hnew, -, -⟩ |
      ⟨k, stamp, iy, ky, gyi, hk, hst, o1, g1, hfr, hnew, -, -, hacc⟩
  · refine ⟨p, hpR, fun hp => ?_, hpex', fun j h1 h2 => ?_⟩
    · rw [(hfr p hp).1, (hfr p hp).2]
      exact hpos hp
    · rw [(hfr j h2).1, (hfr j h2).2]
      exact hcellM j h1 h2
  · -- Pipe `k → k+1`
    rcases Nat.lt_or_ge (k + 1) p with hlt | hge
    · refine ⟨p, hpR, fun hp => ?_, hpex', fun j h1 h2 => ?_⟩
      · rw [(hfr p hp (by omega) (by omega)).1, (hfr p hp (by omega) (by omega)).2]
        exact hpos hp
      · rw [(hfr j h2 (by omega) (by omega)).1, (hfr j h2 (by omega) (by omega)).2]
        exact hcellM j h1 h2
    · rcases Nat.lt_or_ge k p with hlt2 | hge2
      · -- the right cell holds the packet: blocked
        have hpk : p = k + 1 := by omega
        obtain ⟨hD, hat⟩ := hpos (by omega)
        rw [hpk] at hD hat
        obtain ⟨k1, k2⟩ := pipeKeepRight (decide (k = 0)) (o k) stamp (go k) (go (k + 1))
        refine ⟨p, hpR, fun _ => ⟨?_, ?_⟩, hpex', fun j h1 h2 => ?_⟩
        · rw [hpk, o2, hD, k1]
        · rw [hpk, g2, hD, k2]
          exact hat
        · rw [(hfr j h2 (by omega) (by omega)).1, (hfr j h2 (by omega) (by omega)).2]
          exact hcellM j h1 h2
      · rcases Nat.lt_or_ge p k with hlt3 | hge3
        · -- both cells ahead
          have hk0 : decide (k = 0) = false := decide_eq_false (by omega)
          obtain ⟨n1, n2⟩ := aheadPipeRow sigma0.time hfo' hnewT stamp (decide (k = 0))
            (fun h => by rw [hk0] at h; cases h) (o k) (o (k + 1)) (go k) (go (k + 1))
            (hTB k (by omega)) (hTB (k + 1) hk) (hcells k hlt3 (by omega))
            (hcells (k + 1) (by omega) hk) hnew
          refine ⟨p, hpR, fun hp => ?_, hpex', fun j h1 h2 => ?_⟩
          · rw [(hfr p hp (by omega) (by omega)).1, (hfr p hp (by omega) (by omega)).2]
            exact hpos hp
          · by_cases e1 : j = k
            · subst e1
              rw [o1, g1]
              exact n1
            · by_cases e2 : j = k + 1
              · subst e2
                rw [o2, g2]
                exact n2
              · rw [(hfr j h2 e1 e2).1, (hfr j h2 e1 e2).2]
                exact hcellM j h1 h2
        · -- the left cell holds the packet
          have hpk : p = k := by omega
          obtain ⟨hD, hat⟩ := hpos (by omega)
          rw [hpk] at hD hat
          rcases hyo : o (k + 1) with _ | _ | T'
          · -- hop
            refine ⟨k + 1, by omega, fun _ => ⟨?_, ?_⟩, fun h => by omega, fun j h1 h2 => ?_⟩
            · rw [o2, hD, hyo]
              rfl
            · rw [g2, hD, hyo]
              exact hat
            · rw [(hfr j h2 (by omega) (by omega)).1, (hfr j h2 (by omega) (by omega)).2]
              exact hcellM j (by omega) h2
          · refine ⟨p, hpR, fun _ => ⟨?_, ?_⟩, hpex', fun j h1 h2 => ?_⟩
            · rw [hpk, o1, hD, hyo]
              rfl
            · rw [hpk, g1, hD, hyo]
              exact hat
            · by_cases e2 : j = k + 1
              · subst e2
                have hc := hcellM (k + 1) (by omega) h2
                rw [o2, g2, hD, hyo]
                rw [hyo] at hc
                exact hc
              · rw [(hfr j h2 (by omega) e2).1, (hfr j h2 (by omega) e2).2]
                exact hcellM j h1 h2
          · refine ⟨p, hpR, fun _ => ⟨?_, ?_⟩, hpex', fun j h1 h2 => ?_⟩
            · rw [hpk, o1, hD, hyo]
              rfl
            · rw [hpk, g1, hD, hyo]
              exact hat
            · by_cases e2 : j = k + 1
              · subst e2
                have hc := hcellM (k + 1) (by omega) h2
                rw [o2, g2, hD, hyo]
                rw [hyo] at hc
                exact hc
              · rw [(hfr j h2 (by omega) e2).1, (hfr j h2 (by omega) e2).2]
                exact hcellM j h1 h2
  · -- Del `R-1 → R`
    rcases Nat.lt_or_ge p k with hlt | hge
    · have n1 := aheadDelRow sigma0.time hfo' hnewT stamp (o k) iy ky (go k) gyi
        (hTB k (by omega)) (hcells k hlt (by omega)) hnew
      refine ⟨p, hpR, fun hp => ?_, hpex', fun j h1 h2 => ?_⟩
      · rw [(hfr p hp (by omega)).1, (hfr p hp (by omega)).2]
        exact hpos hp
      · by_cases e1 : j = k
        · subst e1
          rw [o1, g1]
          exact n1
        · rw [(hfr j h2 e1).1, (hfr j h2 e1).2]
          exact hcellM j h1 h2
    · rcases Nat.lt_or_ge k p with hlt2 | hge2
      · -- the packet has left the block
        refine ⟨p, hpR, fun hp => by omega, hpex', fun j h1 h2 => by omega⟩
      · have hpk : p = k := by omega
        obtain ⟨hD, hat⟩ := hpos (by omega)
        rw [hpk] at hD hat
        have keep : o' k = .D true ∧ go' k = go k → AheadBar R A' sigma0 OnE o' go' := by
          intro ⟨e1, e2⟩
          exact ⟨k, by omega, fun _ => ⟨e1, by rw [e2]; exact hat⟩, fun h => by omega,
            fun j h1 h2 => by omega⟩
        cases hky : ky
        · cases hiy : iy with
          | E =>
            obtain ⟨x0, hx0, he0, hop0⟩ := hacc true hD hiy hky
            exact ⟨R, Nat.le_refl R, fun h => absurd h (Nat.lt_irrefl R),
              fun _ => ⟨x0, hx0, he0, by rw [hop0, hat]⟩, fun j h1 h2 => by omega⟩
          | X => exact keep ⟨by rw [o1, hD, hiy, hky]; rfl, by rw [g1, hD, hiy, hky]; rfl⟩
          | P T' => exact keep ⟨by rw [o1, hD, hiy, hky]; rfl, by rw [g1, hD, hiy, hky]; rfl⟩
          | S T' => exact keep ⟨by rw [o1, hD, hiy, hky]; rfl, by rw [g1, hD, hiy, hky]; rfl⟩
        · exact keep ⟨by rw [o1, hD, hky]; rfl, by rw [g1, hD, hky]; rfl⟩

/-- **The ahead invariant of one border tail across one letter**: for an old `sigma0` by
`aheadBarStep` and the three cases of a new export; at the letter minting `sigma0` (a `U` read
at the border) the packet starts at cell 0, every other cell is older than the new frame by
`CellBound`, and no export can name a later tail by `ExpCause`. Consumer: `aheadRunStep`. -/
theorem aheadAtStep (hR : 2 ≤ R) (sigma0 : DigitStamp n)
    (hS : SrcLetter R src0 lane A A' OnE o o' go go')
    (hclk : A'.clock = A.clock + 1) (hfo' : AuditFrameOrder A')
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (hTS : ∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.time ≤ A.clock)
    (hrecS : ∀ smp : DigitSample c n, DigitRecordedSample A smp → DigitRecordedSample A' smp)
    (hrecX : ∀ x : DigitExport c n, DigitRecordedExport A x → DigitRecordedExport A' x)
    (hTB : ∀ q, q < R → ∀ id : DigitStamp n, (go q).atom = some (.sampled id) → id.time ≤ A.clock)
    (hXT : ∀ (x : DigitExport c n) (id : DigitStamp n), DigitRecordedExport A x → OnE x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ A.clock)
    (hXT' : ∀ (x : DigitExport c n) (id : DigitStamp n), DigitRecordedExport A' x → OnE x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ A'.clock)
    (hcb : CellBound R A o go) (hec' : ExpCause A' OnE)
    (h : AheadAt R src0 lane A OnE sigma0 o go) : AheadAt R src0 lane A' OnE sigma0 o' go' := by
  intro ⟨s0, hr0, hid0⟩ hsite hlane
  have hsl : s0.id.site = src0 := by rw [hid0]; exact hsite
  have hll : s0.id.lane = lane := by rw [hid0]; exact hlane
  have hBor : DigitRecordedSample A s0 ∨
      (∃ (stamp : DigitStamp n), stamp.time = A.clock + 1 ∧ s0.id = stamp ∧ o 0 = .U ∧
        (∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
          smp.cause = (go 0).obligation) ∧
        o' 0 = .D true ∧ (go' 0).atom = some (.sampled stamp) ∧
        ∀ q, 0 < q → q < R → o' q = o q ∧ go' q = go q) := by
    rcases hS with ⟨hB, -, -⟩ | ⟨k, stamp, hk, hst, o1, o2, g1, g2, hfr, hnew, hB, -⟩ |
        ⟨-, -, -, -, -, -, -, -, -, -, -, hB, -, -⟩
    · exact Or.inl (hB s0 hr0 hsl hll)
    · rcases hB s0 hr0 hsl hll with h' | ⟨hk0, hU, hid⟩
      · exact Or.inl h'
      · subst hk0
        right
        refine ⟨stamp, hst, hid, hU, hnew hU, ?_, ?_, fun q h1 h2 => ?_⟩
        · rw [o1, hU]
          rfl
        · rw [g1, hU]
          rfl
        · by_cases e : q = 1
          · subst e
            refine ⟨?_, ?_⟩
            · rw [o2, hU]
              rfl
            · rw [g2, hU]
              rfl
          · exact hfr q h2 (by omega) e
    · exact Or.inl (hB s0 hr0 hsl hll)
  rcases hBor with hold | ⟨stamp, hst, hid, hU, hnew, hD', hat', hfr0⟩
  · -- `sigma0` was minted before this letter
    obtain ⟨hself, hbar, hexp⟩ := h ⟨s0, hold, hid0⟩ hsite hlane
    have hs0T : sigma0.time ≤ A.clock := by rw [← hid0]; exact hTS s0 hold
    have hself' : ∀ s1 : DigitSample c n, DigitRecordedSample A' s1 → s1.id = sigma0 →
        ∀ rho tl : DigitStamp n, s1.cause = some (.afterTail rho (some (.sampled tl))) →
          tl.time < sigma0.time := by
      intro s1 hs1 hid1 rho tl hc
      rcases hnewT s1 hs1 with hs1' | ht
      · exact hself s1 hs1' hid1 rho tl hc
      · rw [hid1] at ht
        omega
    have hbar' := aheadBarStep sigma0 hS hfo' hnewT hrecX hTB hbar
    refine ⟨hself', hbar', ?_⟩
    have hold' : ∀ (x : DigitExport c n) (smp : DigitSample c n), DigitRecordedExport A x →
        OnE x → x.operand = some (.sampled smp.id) → DigitRecordedSample A' smp →
        ∀ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) →
          sigma0.time ≤ tl.time →
          ∃ x0 : DigitExport c n, DigitRecordedExport A' x0 ∧ OnE x0 ∧
            x0.operand = some (.sampled sigma0) ∧ x0.time < x.time := by
      intro x smp hx he hop hs rho tl hc hle
      rcases hnewT smp hs with hs' | ht
      · obtain ⟨x0, a, b, d, e⟩ := hexp x smp hx he hop hs' rho tl hc hle
        exact ⟨x0, hrecX x0 a, b, d, e⟩
      · have := hXT x smp.id hx he hop
        omega
    intro x smp hx he hop hs rho tl hc hle
    rcases hS with ⟨-, hX, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, hX⟩ |
        ⟨k, stamp, iy, ky, gyi, hk, hst, -, -, -, -, -, hX, -⟩
    · exact hold' x smp (hX x hx he) he hop hs rho tl hc hle
    · exact hold' x smp (hX x hx he) he hop hs rho tl hc hle
    · rcases hX x hx he with hx' | ⟨ht, ⟨T, hT⟩, hopx⟩
      · exact hold' x smp hx' he hop hs rho tl hc hle
      · have hat : (go k).atom = some (.sampled smp.id) := by rw [← hopx, hop]
        obtain ⟨p, hpR, hpos, hpex, hcells⟩ := hbar
        rcases Nat.lt_or_ge p k with hlt | hge
        · have hcell := hcells k hlt (by omega)
          rw [hT] at hcell
          rcases hnewT smp hs with hs' | hts
          · have := hcell.2 smp hs' hat rho tl hc
            omega
          · have := hTB k (by omega) smp.id hat
            omega
        · rcases Nat.lt_or_ge k p with hlt2 | hge2
          · obtain ⟨x0, a, b, d⟩ := hpex (by omega)
            have := (hXT x0 sigma0 a b d).2
            exact ⟨x0, hrecX x0 a, b, d, by omega⟩
          · have hpk : p = k := by omega
            rw [hpk] at hpos
            have hsg : smp.id = sigma0 := by
              have h2 := (hpos (by omega)).2
              rw [hat] at h2
              cases h2
              rfl
            have := hself' smp hs hsg rho tl hc
            omega
  · -- `sigma0` is minted by this letter
    have hsig : sigma0 = stamp := by rw [← hid0, hid]
    subst hsig
    have hB0 := hcb 0 (by omega)
    rw [hU] at hB0
    refine ⟨fun s1 hs1 hid1 rho tl hc => ?_, ⟨0, by omega, fun _ => ⟨hD', hat'⟩,
      fun h => by omega, fun j h1 h2 => ?_⟩, fun x smp hx he hop hs rho tl hc hle => ?_⟩
    · obtain ⟨s2, hid2, hs2, hc2⟩ := hnew
      have hss : s2 = s1 := recordedSampleUnique hfo' hs2 hs1 (by rw [hid2, hid1])
      subst hss
      rw [hc2] at hc
      have := hB0 rho tl (obligationUnread (go 0) _ hc)
      omega
    · rw [(hfr0 j h1 h2).1, (hfr0 j h1 h2).2]
      exact aheadCellMono (by omega) hnewT _ _ (hTB j h2) (hcb j h2)
    · have h1 := hec' x smp hx he hop hs rho tl hc
      have h2 := (hXT' x smp.id hx he hop).2
      omega

end Letter

/-! ### The source block on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- An export on the delimiter edge, with its destination. Consumer: `AheadRun`, `groupCause`. -/
def OnEdgeD (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (x : DigitExport c n) : Prop :=
  OnEdge ring root lane src R x ∧ x.destination = digitSite ring root (src + R)

/-- **`SrcLetter` on the projected ring** (layout hypotheses of `cohortProjStep`). Consumer:
`aheadRunStep`. -/
theorem srcLetterRing (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    SrcLetter R (digitSite ring root src) lane A (digitAuditStep ring S A (digitSite ring root j))
      (OnEdgeD ring root lane src R) (cohortProj ring root lane src R S).out
      (cohortProj ring root lane src R (phiD ring S (digitSite ring root j))).out
      (fun q => (laneCells ring root lane src A.current q).out)
      (fun q => (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root j)).current q).out) := by
  have hBnew := fun smp hs hsi hl =>
    newBorderSample ring root S src R hR hsrc hend hroot hb0 lane A j hj hbX smp hs hsi hl
  have hXnew : ∀ x : DigitExport c n,
      DigitRecordedExport (digitAuditStep ring S A (digitSite ring root j)) x →
      OnEdgeD ring root lane src R x → DigitRecordedExport A x ∨ j = src + (R - 1) := by
    intro x hx he
    rcases recordedExportStepCases ring S A _ x hx with h | ⟨-, hse, -⟩
    · exact Or.inl h
    · exact Or.inr (bankRepairDigitSiteInj ring root hj (by omega) (hse.symm.trans he.1.2))
  rw [cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j hj hbX hbY]
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin]
    obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    rw [Nat.add_sub_cancel_left]
    show SrcLetter R (digitSite ring root src) lane A
      (digitAuditStep ring S A (digitSite ring root (src + k))) (OnEdgeD ring root lane src R)
      (cohortProj ring root lane src R S).out (cohortEdge R (cohortProj ring root lane src R S) k).out
      (fun q => (laneCells ring root lane src A.current q).out)
      (fun q => (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current q).out)
    have hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R →
        (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current q).out =
        (laneCells ring root lane src A.current q).out := by
      intro q hq1 hq2 hq
      unfold laneCells
      rw [curFar]
      · intro he
        exact hq1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        exact hq2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
    have hx : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).x := by
      unfold laneCells
      rw [curX]
    have hy : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
      unfold laneCells
      rw [show digitSite ring root (src + (k + 1)) =
        ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
    have hnewU : k < R → (cohortProj ring root lane src R S).out k = .U →
        ∃ smp : DigitSample c n,
          smp.id = DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane ∧
          DigitRecordedSample (digitAuditStep ring S A (digitSite ring root (src + k))) smp ∧
          smp.cause = (laneCells ring root lane src A.current k).out.obligation := by
      intro hkR hU
      rw [projOut ring root lane src R S k hkR] at hU
      obtain ⟨smp, e1, e2, e3, -⟩ :=
        freshSampleCause ring S A (digitSite ring root (src + k)) lane hlx hly hU
      exact ⟨smp, e1, e2, e3⟩
    by_cases h1 : k + 1 < R
    · -- Pipe
      have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = 0) := by
        by_cases hk0 : k = 0
        · rw [decide_eq_true hk0, hk0]
          exact hb0
        · rw [decide_eq_false hk0]
          exact hbF k (by omega) (by omega) (by omega)
      have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = decide (k = 0) := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbx
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hbF (k + 1) (by omega) (by omega) (by omega)
      have hrowP : ((laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current k).out,
          (laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).out) =
          ghostPipe (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane)
            (decide (k = 0)) ((cohortProj ring root lane src R S).out k)
            ((cohortProj ring root lane src R S).out (k + 1))
            (laneCells ring root lane src A.current k).out
            (laneCells ring root lane src A.current (k + 1)).out := by
        rw [hx, hy, projOut ring root lane src R S k (by omega),
          projOut ring root lane src R S (k + 1) h1, ← hmX]
        exact rowPipeD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
      obtain ⟨o1, o2, o3⟩ := pipeOut R k h1 (cohortProj ring root lane src R S)
      right
      left
      refine ⟨k, DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane, h1, rfl, o1, o2,
        congrArg Prod.fst hrowP, congrArg Prod.snd hrowP,
        fun q hq e1 e2 => ⟨o3 q e1 e2, hfr q e1 e2 (by omega)⟩, hnewU (by omega), ?_, ?_⟩
      · intro smp r1 r2 r3
        rcases hBnew smp r1 r2 r3 with h' | ⟨hk0, hid, hU, -, -⟩
        · exact Or.inl h'
        · right
          obtain rfl : k = 0 := by omega
          exact ⟨rfl, by rw [projOut ring root lane src R S 0 (by omega)]; exact hU, hid⟩
      · intro x hx' he
        rcases hXnew x hx' he with h' | h'
        · exact h'
        · omega
    · by_cases h2 : k + 1 = R
      · -- Del
        have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = false := by
          rw [laneMarkerXBeta lane _ _ hbX]
          exact hbF k (by omega) (by omega) (by omega)
        have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = true := by
          rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + R by omega]
          exact hbR
        have hrow := rowDelD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy
        obtain ⟨o1, o3⟩ := delOut R k h2 (cohortProj ring root lane src R S)
        right
        right
        refine ⟨k, DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane,
          (cohortProj ring root lane src R S).inp (k + 1),
          (cohortProj ring root lane src R S).live (k + 1),
          (laneCells ring root lane src A.current (k + 1)).input, h2, rfl, o1, ?_,
          fun q hq e1 => ⟨o3 q e1, hfr q e1 (by omega) (by omega)⟩, hnewU (by omega), ?_, ?_, ?_⟩
        · show (laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current k).out = _
          rw [hx, projOut ring root lane src R S k (by omega),
            projIn ring root lane src R S (k + 1) (by omega) (by omega),
            projLive ring root lane src R S (k + 1) (by omega) (by omega)]
          exact congrArg Prod.fst hrow.1
        · intro smp r1 r2 r3
          rcases hBnew smp r1 r2 r3 with h' | ⟨hk0, -⟩
          · exact h'
          · omega
        · intro x hx' he
          have := newEdgeExport ring root S src R hR hsrc hend hroot hbR hbF lane A (src + k)
            (by omega) hbX hbY x hx' he.1
          rw [show R - 1 = k by omega] at this
          exact this
        · intro T hD hE hK
          rw [projOut ring root lane src R S k (by omega)] at hD
          rw [projIn ring root lane src R S (k + 1) (by omega) (by omega)] at hE
          rw [projLive ring root lane src R S (k + 1) (by omega) (by omega)] at hK
          obtain ⟨ex, e1, e2, e3, e4, e5, e6, -, -⟩ := recordDeliveryD lane (A.clock + 1)
            (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
            (A.current (digitSite ring root (src + k)))
            (A.current (digitSite ring root (src + k + 1))) hlx hly hmy hD hE hK
          refine ⟨ex, ⟨DigitFrame.mk (A.clock + 1) (digitSite ring root (src + k)) S A.current
            (svcAt ring S A (digitSite ring root (src + k))), List.mem_cons.mpr (Or.inl rfl),
            by rw [e3], by rw [e5], by rw [e4]; exact e1⟩,
            ⟨⟨e4, by rw [e5, show src + (R - 1) = src + k by omega]⟩,
              by rw [e6, show src + R = src + (k + 1) by omega]; rfl⟩, e2⟩
      · -- Fin and Term: the source outputs are framed
        left
        refine ⟨fun smp r1 r2 r3 => ?_, fun x hx' he => ?_, fun q hq => ⟨?_, ?_⟩⟩
        · rcases hBnew smp r1 r2 r3 with h' | ⟨hk0, -⟩
          · exact h'
          · omega
        · rcases hXnew x hx' he with h' | h'
          · exact h'
          · omega
        · rw [edgeOutHigh R k (by omega)]
        · exact hfr q (by omega) (by omega) (by omega)
  · rw [if_neg hin]
    show SrcLetter R (digitSite ring root src) lane A
      (digitAuditStep ring S A (digitSite ring root j)) (OnEdgeD ring root lane src R)
      (cohortProj ring root lane src R S).out (cohortProj ring root lane src R S).out
      (fun q => (laneCells ring root lane src A.current q).out)
      (fun q => (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root j)).current q).out)
    have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
        laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q := by
      intro q hq n1 n2
      unfold laneCells
      rw [curFar]
      · intro he
        exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        by_cases hjn : j + 1 < n
        · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
        · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
          have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
          omega
    left
    refine ⟨fun smp r1 r2 r3 => ?_, fun x hx' he => ?_, fun q hq => ⟨rfl, ?_⟩⟩
    · rcases hBnew smp r1 r2 r3 with h' | ⟨hjs, -⟩
      · exact h'
      · omega
    · rcases hXnew x hx' he with h' | h'
      · exact h'
      · omega
    · by_cases h1 : j + 1 = src
      · by_cases hq0 : q = 0
        · subst hq0
          have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
          have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
          have hmy : laneMarkerY lane (S (digitSite ring root j))
              (S (digitSite ring root (j + 1))) = true := by
            rw [laneMarkerYBeta lane _ _ hbY, h1]
            exact hb0
          show (laneGhost lane ((digitAuditStep ring S A (digitSite ring root j)).current
            (digitSite ring root (src + 0)))).out =
            (laneGhost lane (A.current (digitSite ring root (src + 0)))).out
          rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
            rw [← h1]; rfl, curY ring hn]
          exact rowEntryD lane (A.clock + 1) (digitSite ring root j)
            (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
            (S (digitSite ring root (j + 1))) (A.current (digitSite ring root j))
            (A.current (digitSite ring root (j + 1))) hlx hly hmy
        · show (laneCells ring root lane src _ q).out = _
          rw [farNe q (by omega) (by omega) (by omega)]
      · show (laneCells ring root lane src _ q).out = _
        rw [farNe q (by omega) (by omega) (by omega)]

end Ring

/-! ### The run invariant and the coherence of a completion group -/

section Run

variable {c : Compiled} {n : Nat}

/-- **The ahead run invariant** of one block and lane: `CellBound`, `ExpCause`, and `AheadAt`
for every border-tail stamp. Consumer: `aheadRunStep`, `groupCause`. -/
def AheadRun (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  CellBound R A (cohortProj ring root lane src R S).out
    (fun q => (laneCells ring root lane src A.current q).out) ∧
  ExpCause A (OnEdgeD ring root lane src R) ∧
  ∀ sigma0 : DigitStamp n, AheadAt R (digitSite ring root src) lane A
    (OnEdgeD ring root lane src R) sigma0 (cohortProj ring root lane src R S).out
    (fun q => (laneCells ring root lane src A.current q).out)

/-- **`AheadRun` across one letter** (projected ring, layout hypotheses of `cohortProjStep`, the
distinct correspondence before and after). Consumer: the run lemmas of the width and BANK
chains (`L3.CloseRank`). -/
theorem aheadRunStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (hfo : AuditFrameOrder A) (hgd : GhostCorrDistinct ring root lane src R Base S A)
    (hgd' : GhostCorrDistinct ring root lane src R Base (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)))
    (h : AheadRun ring root lane src R S A) :
    AheadRun ring root lane src R (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  have hS := srcLetterRing ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A j hj
    hbX hbY
  have hfo' := auditFrameOrderStep ring S A (digitSite ring root j) hfo
  have hnewT : ∀ smp : DigitSample c n,
      DigitRecordedSample (digitAuditStep ring S A (digitSite ring root j)) smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1 := by
    intro smp hs
    rcases recordedSampleStepCases ring S A _ smp hs with h' | ⟨ht, -⟩
    · exact Or.inl h'
    · exact Or.inr ht
  have hTS := fun smp hs => recordedSampleTimeLe A hfo smp hs
  have hrecS := fun smp hs => recordedSampleStep ring S A (digitSite ring root j) smp hs
  have hrecX := fun x hx => recordedExportStep ring S A (digitSite ring root j) x hx
  have hTB : ∀ q, q < R → ∀ id : DigitStamp n,
      (laneCells ring root lane src A.current q).out.atom = some (.sampled id) →
      id.time ≤ A.clock := by
    intro q hq id hid
    exact hgd.2.2.1 q id (by unfold tracked trackedAt; rw [if_pos hq]; exact hid)
  have hXT : ∀ (x : DigitExport c n) (id : DigitStamp n), DigitRecordedExport A x →
      OnEdgeD ring root lane src R x → x.operand = some (.sampled id) →
      id.time < x.time ∧ x.time ≤ A.clock :=
    fun x id hx he hop => hgd.2.2.2.1 x id hx he.1 hop
  have hXT' : ∀ (x : DigitExport c n) (id : DigitStamp n),
      DigitRecordedExport (digitAuditStep ring S A (digitSite ring root j)) x →
      OnEdgeD ring root lane src R x → x.operand = some (.sampled id) →
      id.time < x.time ∧ x.time ≤ (digitAuditStep ring S A (digitSite ring root j)).clock :=
    fun x id hx he hop => hgd'.2.2.2.1 x id hx he.1 hop
  obtain ⟨hcb, hec, hat⟩ := h
  have hec' := expCauseStep hS hnewT hTB hXT hcb hec
  exact ⟨cellBoundStep hS rfl hfo' hnewT hTB hcb, hec',
    fun sigma0 => aheadAtStep hR sigma0 hS rfl hfo' hnewT hTS hrecS hrecX hTB hXT hXT' hcb hec'
      (hat sigma0)⟩

/-- An initial output ghost is never an `afterTail` obligation. Consumer: `aheadRunInitial`. -/
theorem initOutNotAfter (lane : DigitLane) (site : Fin n) (v : DigitLaneView c)
    (rho : DigitStamp n) (t : Option (DigitAtom n)) :
    (DigitLaneGhost.initial lane site v).out ≠ .unread (.afterTail rho t) := by
  intro h
  simp only [DigitLaneGhost.initial] at h
  split at h <;> cases h

/-- A cell with no `afterTail` obligation, on an audit with no recorded sample, whose sampled
atom is older than `b`, is older than `b`. Consumer: `aheadRunInitial`. -/
theorem aheadCellFresh (b : Nat) (A : DigitAudit c n) (o : BankRepairDigitOutSh)
    (g : DigitOutGhost n)
    (hU : ∀ rho tl : DigitStamp n, g ≠ .unread (.afterTail rho (some (.sampled tl))))
    (hnr : ∀ smp : DigitSample c n, ¬ DigitRecordedSample A smp)
    (hTB : ∀ id : DigitStamp n, g.atom = some (.sampled id) → id.time < b) :
    AheadCell b A o g := by
  cases o with
  | E => trivial
  | U => exact fun rho tl hg => absurd hg (hU rho tl)
  | D T => exact ⟨fun _ id hid => hTB id hid, fun smp hs => absurd hs (hnr smp)⟩

/-- At the audit start nothing is recorded and no obligation names a tail. Consumer: the run
lemmas of `L3.CloseRank`. -/
theorem aheadRunInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) : AheadRun ring root lane src R S (digitAuditInitial S) := by
  have hnr : ∀ smp : DigitSample c n, ¬ DigitRecordedSample (digitAuditInitial S) smp := by
    intro smp h
    obtain ⟨f, hf, -⟩ := h
    exact absurd hf List.not_mem_nil
  have hnx : ∀ x : DigitExport c n, ¬ DigitRecordedExport (digitAuditInitial S) x := by
    intro x h
    obtain ⟨f, hf, -⟩ := h
    exact absurd hf List.not_mem_nil
  have hTB := (ghostCorrDistinctInitial ring root lane src R S).2.2.1
  refine ⟨fun q hq => ?_, fun x smp hx => absurd hx (hnx x),
    fun sigma0 ⟨s0, hs0, _⟩ => absurd hs0 (hnr s0)⟩
  refine aheadCellFresh _ _ _ _ (fun rho tl => ?_) hnr (fun id hid => ?_)
  · cases lane
    · exact initOutNotAfter DigitLane.writer (digitSite ring root (src + q))
        (digitLaneView .writer (S (digitSite ring root (src + q)))
          (S (digitSite ring root (src + q))).word.beta) rho _
    · exact initOutNotAfter DigitLane.comparison (digitSite ring root (src + q))
        (digitLaneView .comparison (S (digitSite ring root (src + q)))
          (S (digitSite ring root (src + q))).word.beta) rho _
  · have := hTB q id (by unfold tracked trackedAt; rw [if_pos hq]; exact hid)
    show id.time < 0 + 1
    have h0 : (digitAuditInitial S).clock = 0 := rfl
    omega

/-- **Coherence of a completion group** at any state carrying `TailInv` (every stamp),
`AheadRun`, the frame order and the distinct correspondence: a completion whose tail sample is
later than a recorded border tail `sigma0` of the lane is `DigitTerminalRanked` from `sigma0`
(rank `k + 1`, `k` the rank of the cause tail of its tail sample). Each sample `j > 0` names a
tail `tl'` with `tl ≤ tl'` (`ExportRanked` at `tl`: `tl` is exported before the group by
`ExpBefore` at `tl` and the group's export interval) and `tl' < sigma` (`ExpBefore` at the
group's tail `sigma`: otherwise `sigma` is exported before export `j`); `tl` is the latest
border sample before `sigma`, so `tl' = tl`. Consumer: `L3.CloseRank` (clause (R) and the
writer ranks). -/
theorem groupCause (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (hend : src + 2 * digitSpan c < n) (Base : Bool → DigitAtom n → Prop)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (hfo : AuditFrameOrder A)
    (hgd : GhostCorrDistinct ring root lane src (digitSpan c) Base S A)
    (htail : ∀ sigma0, TailInv ring root lane src (digitSpan c) sigma0 S A)
    (hah : AheadRun ring root lane src (digitSpan c) S A)
    (cut : Nat) (T : DigitTerminal c n)
    (hT : DigitCompletion ring A root src (src + digitSpan c) lane cut T)
    (sigma0 : DigitStamp n)
    (hs0 : ∃ s0 : DigitSample c n, DigitRecordedSample A s0 ∧ s0.id = sigma0)
    (hsite : sigma0.site = digitSite ring root src) (hlane : sigma0.lane = lane)
    (hlate : ∀ (L : DigitCarryGhost c n) (u : DigitUse c n) (id : DigitStamp n),
      T.ledger = some L → L.uses.head? = some u → u.operand = some (.sampled id) →
      sigma0.time < id.time)
    (anchor : DigitTerminal c n) :
    DigitTerminalRanked A lane (digitSite ring root src) anchor sigma0 T := by
  obtain ⟨-, -, -, -, -, -, pos, ledger, samples, exports, uses, hled, hinh, hlen, hall, hord,
    hother⟩ := hT
  obtain ⟨r0, l0, si0, -, -, rx0, xl0, xs0, xd0, xo0, -, -, ui0, -, uo0, -, -, -, -, -⟩ :=
    hall ⟨0, pos⟩
  have hhead : ledger.uses.head? = ledger.uses[0]? := by
    cases ledger.uses <;> rfl
  have si0' : (samples ⟨0, pos⟩).id.site = digitSite ring root src := by
    rw [si0]
    rfl
  have hlt0 : sigma0.time < (samples ⟨0, pos⟩).id.time :=
    hlate ledger _ _ hled (hhead.trans ui0) uo0
  obtain ⟨-, hch0, -⟩ := htail sigma0 hs0 hsite hlane
  obtain ⟨-, rho, tl, hcs, ⟨k, hk⟩, hrl, hrs, h1, h2, hlat⟩ :=
    hch0 (samples ⟨0, pos⟩) r0 si0' l0 hlt0
  have htlB : (∃ s : DigitSample c n, DigitRecordedSample A s ∧ s.id = tl) ∧
      tl.site = digitSite ring root src ∧ tl.lane = lane := by
    rcases tailRankedCases ⟨k, hk⟩ with htl | ⟨smp, hid, hps, -, hpr, hpl, -⟩
    · rw [htl]
      exact ⟨hs0, hsite, hlane⟩
    · exact ⟨⟨smp, hpr, hid⟩, by rw [← hid]; exact hps, by rw [← hid]; exact hpl⟩
  obtain ⟨-, -, hexpTl⟩ := hah.2.2 tl htlB.1 htlB.2.1 htlB.2.2
  obtain ⟨xtl, hxtl, hetl, hoptl, htxtl⟩ := hexpTl (exports ⟨0, pos⟩) (samples ⟨0, pos⟩) rx0
    ⟨⟨xl0, xs0⟩, xd0⟩ xo0 r0 rho tl hcs (Nat.le_refl _)
  have hlast : xtl.time < (exports ⟨digitSpan c - 1, by omega⟩).time := by
    rcases Nat.lt_or_ge xtl.time (exports ⟨digitSpan c - 1, by omega⟩).time with h | h
    · exact h
    · exfalso
      obtain ⟨j', hj'⟩ := hother xtl hxtl hetl.1.1 hetl.1.2 hetl.2 h (Nat.le_of_lt htxtl)
      obtain ⟨-, -, sij, -, -, -, -, -, -, xoj, -, -, -, -, -, -, -, -, -, -⟩ := hall j'
      have hj'lt := j'.isLt
      rw [hj'] at hoptl
      have e := xoj.symm.trans hoptl
      simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
      have hs := sij
      rw [e, htlB.2.1] at hs
      have hj0 := bankRepairDigitSiteInj ring root (by omega) (by omega) hs
      have hjj : j' = ⟨0, pos⟩ := Fin.ext (by show j'.val = 0; omega)
      rw [hjj] at e
      rw [← e] at h1
      omega
  have hcoh : ∀ j : Fin (digitSpan c),
      DigitSampleCohort A lane (digitSite ring root src) anchor sigma0 (samples j) (k + 1) := by
    intro j
    have hjlt := j.isLt
    obtain ⟨rj, lj, sij, -, -, rxj, xlj, xsj, xdj, xoj, -, -, -, -, -, -, -, -, -, -⟩ := hall j
    refine ⟨rj, lj, Or.inr ?_⟩
    by_cases hj0 : j.val = 0
    · have hjj : j = ⟨0, pos⟩ := Fin.ext hj0
      subst hjj
      exact ⟨tl, k, rho, rfl, hk, hcs, hrl, by rw [hrs, si0'], h1, h2⟩
    · have hxl : (exports ⟨digitSpan c - 1, by omega⟩).time ≤ (exports j).time := by
        by_cases hjl : j.val = digitSpan c - 1
        · have hjj : j = ⟨digitSpan c - 1, by omega⟩ := Fin.ext hjl
          rw [hjj]
          exact Nat.le_refl _
        · exact Nat.le_of_lt (hord j ⟨digitSpan c - 1, by omega⟩ (by show j.val < digitSpan c - 1; omega)).1
      obtain ⟨-, -, hexR⟩ := htail tl htlB.1 htlB.2.1 htlB.2.2
      rcases hexR xtl (exports j) hxtl rxj hetl.1 ⟨xlj, xsj⟩ hoptl (by omega) with
        hsame | ⟨smp, hop, hchn⟩
      · exfalso
        have e := xoj.symm.trans hsame
        simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
        have hs := sij
        rw [e, htlB.2.1] at hs
        have := bankRepairDigitSiteInj ring root (by omega) (by omega) hs
        omega
      · obtain ⟨hsr, -, rho', tl', hcs', ⟨k', hk'⟩, hrl', hrs', h1', h2'⟩ := hchn
        have e := hop.symm.trans xoj
        simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
        have hss : smp = samples j := recordedSampleUnique hfo hsr rj e
        subst hss
        have hge := tailRankTimeGe hk'
        have hup : tl'.time < (samples ⟨0, pos⟩).id.time := by
          rcases Nat.lt_or_ge tl'.time (samples ⟨0, pos⟩).id.time with h | h
          · exact h
          · exfalso
            obtain ⟨-, -, hexpS⟩ := hah.2.2 (samples ⟨0, pos⟩).id ⟨samples ⟨0, pos⟩, r0, rfl⟩
              si0' l0
            obtain ⟨x0', hx0', he0', hop0', ht0'⟩ := hexpS (exports j) (samples j) rxj ⟨⟨xlj, xsj⟩, xdj⟩
              xoj rj rho' tl' hcs' h
            have huniq := hgd.2.2.2.2.2 x0' (exports ⟨0, pos⟩) (samples ⟨0, pos⟩).id hx0' rx0
              he0'.1 ⟨xl0, xs0⟩ hop0' xo0
            rw [huniq] at ht0'
            have := (hord ⟨0, pos⟩ j (by show 0 < j.val; omega)).1
            omega
        have heq : tl' = tl := by
          rcases tailRankedCases ⟨k', hk'⟩ with h | ⟨p', hid', hps', -, hpr', hpl', -⟩
          · exact h
          · have hle := hlat p' hpr' hps' hpl' (by rw [hid']; exact hup)
            rw [hid'] at hle
            have ht : tl'.time = tl.time := by omega
            have hs1 : tl'.site = tl.site := by rw [← hid', hps', htlB.2.1]
            have hl1 : tl'.lane = tl.lane := by rw [← hid', hpl', htlB.2.2]
            cases tl'
            cases tl
            simp only at ht hs1 hl1
            subst ht
            subst hs1
            subst hl1
            rfl
        rw [heq] at hcs' h1'
        exact ⟨tl, k, rho', rfl, hk, hcs', hrl', hrs', h1', h2'⟩
  refine ⟨ledger, k + 1, hled, hinh, fun h => ?_, fun use hu => ?_⟩
  · rw [h] at hlen
    simp at hlen
    omega
  · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hu
    have hj : i < digitSpan c := by rw [← hlen]; exact hi
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, uij, -, uoj, -, -, -, -, -⟩ := hall ⟨i, hj⟩
    have h' : ledger.uses[i]? = some use := by rw [List.getElem?_eq_getElem hi, hget]
    have hu' : uses ⟨i, hj⟩ = use := Option.some.inj (uij.symm.trans h')
    rw [← hu', uoj]
    exact ⟨samples ⟨i, hj⟩, rfl, hcoh ⟨i, hj⟩⟩

end Run

end L3.TailAhead

#print axioms L3.TailAhead.cellBoundStep
#print axioms L3.TailAhead.expCauseStep
#print axioms L3.TailAhead.aheadBarStep
#print axioms L3.TailAhead.aheadAtStep
#print axioms L3.TailAhead.srcLetterRing
#print axioms L3.TailAhead.aheadRunStep
#print axioms L3.TailAhead.aheadRunInitial
#print axioms L3.TailAhead.groupCause
