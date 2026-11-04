import Leader.L3.Bank.RepairDigitCohortWindow

/-!
# ReachRank producer (a): the source-tail chain

Fix one complete source block `a(j) = digitSite ring root (src + j)`, `j < R`, one lane, and a
border-tail stamp `sigma0` minted by a `U` read at the source delimiter `a(0)` (the anchor tail of
`DigitAnchor`). On paper, every later border-tail sample names the immediately
preceding border tail as the atom of its `afterTail` cause. This module transcribes that argument
on the actual audit (`A.current`, `A.frames`), with no free labels.

The transcription of the earlier stamped source FIFO (S1) is a **barrier invariant** (`TailBarrier`):
the packet `sampled sigma0` is a one-way barrier. While it sits at source cell `p < R` (as a
physical `D true` carrying exactly the atom `sampled sigma0`), every cell `j < p` behind it is
*settled* (`TailCell`):

* `U`: its ghost is `unread (afterTail rho (some (sampled tl))))` with `tl` a ranked border tail
  (`DigitTailRank` from `sigma0`), `rho` a rearm at this site and lane, `tl.time < rho.time ≤ clock`
  (S2, I3);
* `D true`: its atom is `sampled tl` with `tl` a ranked border tail (S1: a `D true` carries an
  original border sample, not a sample made at `j`);
* `D false`: not at the border, and its atom is a recorded sample whose cause names a ranked tail
  through a rearm at the sample's own site (S3, I4);
* `E`: not at the border (S5: no bootstrap).

The border cell carries in addition `BorderLatest`: it is `D true` or `U`, and the tail it names is
the latest recorded border sample (S4 at the border: no second read between two tail releases).
When the barrier leaves the block (`p = R`, exactly when the anchor export is recorded) every cell
is settled.

the earlier per-site exit lists `P_j` are not needed for producer (a): the barrier and the border's
latest-tail clause carry everything the successor constructor of `DigitTailRank` asks for.
-/

namespace L3.TailChain

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow

/-! ### The clauses -/

section Clauses

variable {c : Compiled} {n : Nat}

/-- A border tail ranked from `sigma0` by the target's `DigitTailRank`. -/
def TailRanked (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n) (sigma0 t : DigitStamp n) :
    Prop :=
  ∃ k, DigitTailRank A lane src0 sigma0 t k

/-- A recorded sample whose cause names a ranked border tail through a rearm at the sample's own
site and lane, strictly between the tail and the sample (S3, the successor branch of
`DigitSampleCohort`). -/
def SampleChained (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n) (sigma0 : DigitStamp n)
    (smp : DigitSample c n) : Prop :=
  DigitRecordedSample A smp ∧ smp.id.lane = lane ∧
  ∃ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) ∧
    TailRanked A lane src0 sigma0 tl ∧ rho.lane = lane ∧ rho.site = smp.id.site ∧
    tl.time < rho.time ∧ rho.time < smp.id.time

/-- A settled source cell behind the barrier (`border`: the cell is the source delimiter). -/
def TailCell (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n) (sigma0 : DigitStamp n)
    (site : Fin n) (border : Bool) : BankRepairDigitOutSh → DigitOutGhost n → Prop
  | .E, _ => border = false
  | .U, g => ∃ rho tl : DigitStamp n, g = .unread (.afterTail rho (some (.sampled tl))) ∧
      TailRanked A lane src0 sigma0 tl ∧ rho.lane = lane ∧ rho.site = site ∧
      tl.time < rho.time ∧ rho.time ≤ A.clock
  | .D true, g => ∃ tl : DigitStamp n, g.atom = some (.sampled tl) ∧
      TailRanked A lane src0 sigma0 tl ∧ tl.time ≤ A.clock
  | .D false, g => border = false ∧ ∃ smp : DigitSample c n, g.atom = some (.sampled smp.id) ∧
      SampleChained A lane src0 sigma0 smp

/-- The border cell is `D true` or `U`, and the tail it names (the atom, or the atom of the
rearm cause) is the latest recorded border sample of this lane. -/
def BorderLatest (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n)
    (o : BankRepairDigitOutSh) (g : DigitOutGhost n) : Prop :=
  ∃ tl : DigitStamp n,
    ((o = .D true ∧ g.atom = some (.sampled tl)) ∨
      (o = .U ∧ ∃ rho : DigitStamp n, g = .unread (.afterTail rho (some (.sampled tl))))) ∧
    ∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.site = src0 →
      smp.id.lane = lane → smp.id.time ≤ tl.time

/-- **The barrier invariant**: the packet `sampled sigma0` is at
cell `p` (or has left the block, `p = R`), every cell behind it is settled, and the border names
the latest border tail. -/
def TailBarrier (R : Nat) (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n)
    (sigma0 : DigitStamp n) (site : Nat → Fin n) (o : Nat → BankRepairDigitOutSh)
    (go : Nat → DigitOutGhost n) : Prop :=
  ∃ p, p ≤ R ∧ (p < R → o p = .D true ∧ (go p).atom = some (.sampled sigma0)) ∧
    (∀ j, j < p → TailCell A lane src0 sigma0 (site j) (decide (j = 0)) (o j) (go j)) ∧
    BorderLatest A lane src0 (o 0) (go 0)

/-- I2 on the recorded border samples after `sigma0`: tail bit set, the cause names the
latest earlier border sample `tl` (ranked), through a rearm at the border, with strict times. -/
def BorderChain (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n) (sigma0 : DigitStamp n) :
    Prop :=
  ∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.site = src0 →
    smp.id.lane = lane → sigma0.time < smp.id.time →
    smp.tail = true ∧
    ∃ rho tl : DigitStamp n, smp.cause = some (.afterTail rho (some (.sampled tl))) ∧
      TailRanked A lane src0 sigma0 tl ∧ rho.lane = lane ∧ rho.site = src0 ∧
      tl.time < rho.time ∧ rho.time < smp.id.time ∧
      ∀ other : DigitSample c n, DigitRecordedSample A other → other.id.site = src0 →
        other.id.lane = lane → other.id.time < smp.id.time → other.id.time ≤ tl.time

/-- Exports (on the delimiter edge, `OnE`) no earlier than the export of `sigma0` carry `sigma0`
or a chained sample. -/
def ExportRanked (A : DigitAudit c n) (lane : DigitLane) (src0 : Fin n) (sigma0 : DigitStamp n)
    (OnE : DigitExport c n → Prop) : Prop :=
  ∀ x0 x : DigitExport c n, DigitRecordedExport A x0 → DigitRecordedExport A x → OnE x0 → OnE x →
    x0.operand = some (.sampled sigma0) → x0.time ≤ x.time →
    x.operand = some (.sampled sigma0) ∨
      ∃ smp : DigitSample c n, x.operand = some (.sampled smp.id) ∧
        SampleChained A lane src0 sigma0 smp

/-- One audit letter: old recorded samples survive and the clock advances by one. -/
def AuditGrows (A A' : DigitAudit c n) : Prop :=
  (∀ smp : DigitSample c n, DigitRecordedSample A smp → DigitRecordedSample A' smp) ∧
    A'.clock = A.clock + 1

end Clauses

/-! ### Monotonicity under audit growth -/

section Mono

variable {c : Compiled} {n : Nat} {A A' : DigitAudit c n} {lane : DigitLane} {src0 : Fin n}
  {sigma0 : DigitStamp n}

/-- Consumer: `tailRankedMono`. -/
theorem tailRankMono (h : ∀ smp : DigitSample c n, DigitRecordedSample A smp →
      DigitRecordedSample A' smp) {t : DigitStamp n} {k : Nat}
    (hk : DigitTailRank A lane src0 sigma0 t k) : DigitTailRank A' lane src0 sigma0 t k := by
  induction hk with
  | anchor => exact DigitTailRank.anchor
  | successor _ sample rearm recorded sampleLane sampleSource sampleTail cause rearmLane
      rearmSource previousBefore rearmBefore ih =>
    exact DigitTailRank.successor ih sample rearm (h sample recorded)
      sampleLane sampleSource sampleTail cause rearmLane rearmSource previousBefore rearmBefore

/-- Consumer: every preservation lemma below. -/
theorem tailRankedMono (h : ∀ smp : DigitSample c n, DigitRecordedSample A smp →
      DigitRecordedSample A' smp) {t : DigitStamp n}
    (ht : TailRanked A lane src0 sigma0 t) : TailRanked A' lane src0 sigma0 t := by
  obtain ⟨k, hk⟩ := ht
  exact ⟨k, tailRankMono h hk⟩

/-- Consumer: `tailCellMono`, `exportRankedStep`. -/
theorem sampleChainedMono (h : ∀ smp : DigitSample c n, DigitRecordedSample A smp →
      DigitRecordedSample A' smp) {smp : DigitSample c n}
    (hs : SampleChained A lane src0 sigma0 smp) : SampleChained A' lane src0 sigma0 smp := by
  obtain ⟨h1, h2, rho, tl, h3, h4, h5⟩ := hs
  exact ⟨h _ h1, h2, rho, tl, h3, tailRankedMono h h4, h5⟩

/-- Consumer: the barrier step lemmas. -/
theorem tailCellMono (h : ∀ smp : DigitSample c n, DigitRecordedSample A smp →
      DigitRecordedSample A' smp) (hclk : A.clock ≤ A'.clock) {site : Fin n} {border : Bool} :
    ∀ (o : BankRepairDigitOutSh) (g : DigitOutGhost n),
      TailCell A lane src0 sigma0 site border o g → TailCell A' lane src0 sigma0 site border o g
  | .E, _, hc => hc
  | .U, _, hc => by
      obtain ⟨rho, tl, h1, h2, h3, h4, h5, h6⟩ := hc
      exact ⟨rho, tl, h1, tailRankedMono h h2, h3, h4, h5, Nat.le_trans h6 hclk⟩
  | .D true, _, hc => by
      obtain ⟨tl, h1, h2, h3⟩ := hc
      exact ⟨tl, h1, tailRankedMono h h2, Nat.le_trans h3 hclk⟩
  | .D false, _, hc => by
      obtain ⟨h1, smp, h2, h3⟩ := hc
      exact ⟨h1, smp, h2, sampleChainedMono h h3⟩

/-- Consumer: `barrierDel`, `barrierFrame`, `barrierPipe`. -/
theorem borderLatestMono (h : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      smp.id.site = src0 → smp.id.lane = lane → DigitRecordedSample A smp)
    {o : BankRepairDigitOutSh} {g : DigitOutGhost n}
    (hb : BorderLatest A lane src0 o g) : BorderLatest A' lane src0 o g := by
  obtain ⟨tl, h1, h2⟩ := hb
  exact ⟨tl, h1, fun smp r1 r2 r3 => h2 smp (h smp r1 r2 r3) r2 r3⟩

/-- A ranked tail is `sigma0` or the id of a chained border sample (the successor constructor).
Consumer: `exportRankedStep`, `settledRankedOutput`. -/
theorem tailRankedCases {t : DigitStamp n} (ht : TailRanked A lane src0 sigma0 t) :
    t = sigma0 ∨ ∃ smp : DigitSample c n, smp.id = t ∧ smp.id.site = src0 ∧ smp.tail = true ∧
      SampleChained A lane src0 sigma0 smp := by
  obtain ⟨k, hk⟩ := ht
  cases hk with
  | anchor => exact Or.inl rfl
  | successor hprev sample rearm recorded sampleLane sampleSource sampleTail cause rearmLane
      rearmSource previousBefore rearmBefore =>
    exact Or.inr ⟨sample, rfl, sampleSource, sampleTail, recorded, sampleLane, rearm, _, cause,
      ⟨_, hprev⟩, rearmLane, by rw [rearmSource, sampleSource], previousBefore, rearmBefore⟩

end Mono

/-! ### One-edge rows on one cell -/

section Rows

variable {c : Compiled} {n : Nat} {A A' : DigitAudit c n} {lane : DigitLane} {src0 : Fin n}
  {sigma0 : DigitStamp n}

/-- Pipe output rows `D true` into a non-empty right cell are blocked. -/
theorem pipeKeepRight (bx : Bool) (ox : BankRepairDigitOutSh) (stamp : DigitStamp n)
    (gxo gyo : DigitOutGhost n) :
    (bankRepairDigitPipeStep bx ox (.D true)).2 = .D true ∧
      (ghostPipe stamp bx ox (.D true) gxo gyo).2 = gyo := by
  rcases ox with _ | _ | T <;> exact ⟨rfl, rfl⟩

/-- **Pipe rows behind the barrier** (table C rows: U read at `a(0)` and at `a(j)`, `D true`
hop into `E`, `D false` move, blocked, `E` at an internal cell). Both cells settled before, both
settled after; a `U` read at the border mints a ranked tail (`DigitTailRank.successor`), a `U`
read inside mints a chained `D false`. Consumer: `barrierPipe`. -/
theorem tailPipeBehind (hgrow : AuditGrows A A') (stamp : DigitStamp n)
    (hst : stamp.time = A.clock + 1) (hsl : stamp.lane = lane) (sx sy : Fin n)
    (hss : stamp.site = sx) (bx : Bool) (hb0 : bx = true → sx = src0)
    (ox oy : BankRepairDigitOutSh) (gxo gyo : DigitOutGhost n)
    (hx : TailCell A lane src0 sigma0 sx bx ox gxo)
    (hy : TailCell A lane src0 sigma0 sy false oy gyo)
    (hnew : ox = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = gxo.obligation ∧ smp.tail = bx) :
    TailCell A' lane src0 sigma0 sx bx (bankRepairDigitPipeStep bx ox oy).1
        (ghostPipe stamp bx ox oy gxo gyo).1 ∧
      TailCell A' lane src0 sigma0 sy false (bankRepairDigitPipeStep bx ox oy).2
        (ghostPipe stamp bx ox oy gxo gyo).2 := by
  obtain ⟨hrec, hclk⟩ := hgrow
  have hle : A.clock ≤ A'.clock := by omega
  have hy' := tailCellMono hrec hle oy gyo hy
  rcases ox with _ | _ | T
  · have hbx : bx = false := hx
    subst hbx
    exact ⟨hx, hy'⟩
  · obtain ⟨rho, tl, hg, hrk, hrl, hrs, h1, h2⟩ := hx
    obtain ⟨smp, hid, hsr, hcs, htl⟩ := hnew rfl
    have hcause : smp.cause = some (.afterTail rho (some (.sampled tl))) := by
      rw [hcs, hg]
      rfl
    refine ⟨?_, hy'⟩
    cases bx
    · show false = false ∧ ∃ s' : DigitSample c n,
          (DigitOutGhost.packet (some (DigitAtom.sampled stamp))).atom =
            some (.sampled s'.id) ∧ SampleChained A' lane src0 sigma0 s'
      refine ⟨rfl, smp, by rw [hid]; rfl, hsr, by rw [hid, hsl], rho, tl, hcause,
        tailRankedMono hrec hrk, hrl, by rw [hrs, hid, hss], h1, by rw [hid, hst]; omega⟩
    · have hsx := hb0 rfl
      obtain ⟨k, hk⟩ := hrk
      have hrank : DigitTailRank A' lane src0 sigma0 smp.id (k + 1) :=
        DigitTailRank.successor (tailRankMono hrec hk) smp rho hsr (by rw [hid, hsl])
          (by rw [hid, hss, hsx]) htl hcause hrl (by rw [hrs, hsx]) h1 (by rw [hid, hst]; omega)
      rw [hid] at hrank
      show ∃ t' : DigitStamp n,
          (DigitOutGhost.packet (some (DigitAtom.sampled stamp))).atom = some (.sampled t') ∧
            TailRanked A' lane src0 sigma0 t' ∧ t'.time ≤ A'.clock
      exact ⟨stamp, rfl, ⟨k + 1, hrank⟩, by omega⟩
  · cases T
    · obtain ⟨hbx, smp, hat, hch⟩ := hx
      subst hbx
      have hch' := sampleChainedMono hrec hch
      rcases oy with _ | _ | T'
      · exact ⟨rfl, rfl, smp, hat, hch'⟩
      · exact ⟨⟨rfl, smp, hat, hch'⟩, hy'⟩
      · exact ⟨⟨rfl, smp, hat, hch'⟩, hy'⟩
    · obtain ⟨tl, hat, hrk, htle⟩ := hx
      have hrk' := tailRankedMono hrec hrk
      rcases oy with _ | _ | T'
      · refine ⟨⟨stamp, tl, ?_, hrk', hsl, hss, by rw [hst]; omega, by omega⟩,
          ⟨tl, hat, hrk', by omega⟩⟩
        show DigitOutGhost.unread (.afterTail stamp gxo.atom) = _
        rw [hat]
      · exact ⟨⟨tl, hat, hrk', by omega⟩, hy'⟩
      · exact ⟨⟨tl, hat, hrk', by omega⟩, hy'⟩

/-- **Del rows behind the barrier** (table C rows: U read at `a(R-1)`, accepted `D true` export,
blocked `D true`, accepted `D false` export, `E`). Consumer: `barrierDel`. -/
theorem tailDelBehind (hgrow : AuditGrows A A') (stamp : DigitStamp n)
    (hst : stamp.time = A.clock + 1) (hsl : stamp.lane = lane) (sx : Fin n)
    (hss : stamp.site = sx) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n))
    (hx : TailCell A lane src0 sigma0 sx false ox gxo)
    (hnew : ox = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧ DigitRecordedSample A' smp ∧
      smp.cause = gxo.obligation ∧ smp.tail = false) :
    TailCell A' lane src0 sigma0 sx false (bankRepairDigitDelStep ox iy ky).1
      (ghostDel stamp ox iy ky gxo gyi).1 := by
  obtain ⟨hrec, hclk⟩ := hgrow
  have hle : A.clock ≤ A'.clock := by omega
  rcases ox with _ | _ | T
  · exact hx
  · obtain ⟨rho, tl, hg, hrk, hrl, hrs, h1, h2⟩ := hx
    obtain ⟨smp, hid, hsr, hcs, -⟩ := hnew rfl
    have hcause : smp.cause = some (.afterTail rho (some (.sampled tl))) := by
      rw [hcs, hg]
      rfl
    show false = false ∧ ∃ s' : DigitSample c n,
        (DigitOutGhost.packet (some (DigitAtom.sampled stamp))).atom =
          some (.sampled s'.id) ∧ SampleChained A' lane src0 sigma0 s'
    exact ⟨rfl, smp, by rw [hid]; rfl, hsr, by rw [hid, hsl], rho, tl, hcause,
      tailRankedMono hrec hrk, hrl, by rw [hrs, hid, hss], h1, by rw [hid, hst]; omega⟩
  · cases T
    · obtain ⟨-, smp, hat, hch⟩ := hx
      have hch' := sampleChainedMono hrec hch
      cases ky
      · rcases iy with _ | _ | T' | T'
        · exact rfl
        · exact ⟨rfl, smp, hat, hch'⟩
        · exact ⟨rfl, smp, hat, hch'⟩
        · exact ⟨rfl, smp, hat, hch'⟩
      · exact ⟨rfl, smp, hat, hch'⟩
    · obtain ⟨tl, hat, hrk, htle⟩ := hx
      have hrk' := tailRankedMono hrec hrk
      cases ky
      · rcases iy with _ | _ | T' | T'
        · refine ⟨stamp, tl, ?_, hrk', hsl, hss, by rw [hst]; omega, by omega⟩
          show DigitOutGhost.unread (.afterTail stamp gxo.atom) = _
          rw [hat]
        · exact ⟨tl, hat, hrk', by omega⟩
        · exact ⟨tl, hat, hrk', by omega⟩
        · exact ⟨tl, hat, hrk', by omega⟩
      · exact ⟨tl, hat, hrk', by omega⟩

/-- **The border rows** (table C: Pipe at `a(0)`; the bootstrap row `E` at the marker cannot
fire, since the border is `D true` or `U`). The border keeps naming the latest border tail.
Consumer: `barrierPipe`. -/
theorem borderPipe (hgrow : AuditGrows A A') (stamp : DigitStamp n)
    (hst : stamp.time = A.clock + 1)
    (hTB : ∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.time ≤ A.clock)
    (ox oy : BankRepairDigitOutSh) (gxo gyo : DigitOutGhost n)
    (hb : BorderLatest A lane src0 ox gxo)
    (hB : ∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp ∨ (ox = .U ∧ smp.id = stamp)) :
    BorderLatest A' lane src0 (bankRepairDigitPipeStep true ox oy).1
      (ghostPipe stamp true ox oy gxo gyo).1 := by
  obtain ⟨tl, hshape, hlat⟩ := hb
  rcases hshape with ⟨hD, hat⟩ | ⟨hU, rho, hg⟩
  · subst hD
    have hold : ∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
        smp.id.lane = lane → smp.id.time ≤ tl.time := by
      intro smp r1 r2 r3
      rcases hB smp r1 r2 r3 with h | ⟨h, -⟩
      · exact hlat smp h r2 r3
      · cases h
    rcases oy with _ | _ | T'
    · refine ⟨tl, Or.inr ⟨rfl, stamp, ?_⟩, hold⟩
      show DigitOutGhost.unread (.afterTail stamp gxo.atom) = _
      rw [hat]
    · exact ⟨tl, Or.inl ⟨rfl, hat⟩, hold⟩
    · exact ⟨tl, Or.inl ⟨rfl, hat⟩, hold⟩
  · subst hU
    refine ⟨stamp, Or.inl ⟨rfl, rfl⟩, fun smp r1 r2 r3 => ?_⟩
    rcases hB smp r1 r2 r3 with h | ⟨-, h⟩
    · have := hTB smp h
      omega
    · rw [h]
      exact Nat.le_refl _

end Rows

/-! ### The barrier across one letter -/

section Barrier

variable {c : Compiled} {n : Nat} {A A' : DigitAudit c n} {lane : DigitLane} {src0 : Fin n}
  {sigma0 : DigitStamp n} {site : Nat → Fin n}

/-- A letter off the source outputs (Fin, Term, entry, far edges and the other lane): the source
outputs and their ghosts are framed. Consumer: `tailInvStep`. -/
theorem barrierFrame (R : Nat) (hgrow : AuditGrows A A') (o o' : Nat → BankRepairDigitOutSh)
    (go go' : Nat → DigitOutGhost n)
    (hb : TailBarrier R A lane src0 sigma0 site o go)
    (ho : ∀ q, q < R → o' q = o q) (hg : ∀ q, q < R → go' q = go q) (hR : 0 < R)
    (hB : ∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp) :
    TailBarrier R A' lane src0 sigma0 site o' go' := by
  obtain ⟨hrec, hclk⟩ := hgrow
  have hle : A.clock ≤ A'.clock := by omega
  obtain ⟨p, hpR, hpos, hcells, hbord⟩ := hb
  refine ⟨p, hpR, fun hp => ?_, fun j hj => ?_, ?_⟩
  · rw [ho p hp, hg p hp]
    exact hpos hp
  · rw [ho j (by omega), hg j (by omega)]
    exact tailCellMono hrec hle _ _ (hcells j hj)
  · rw [ho 0 hR, hg 0 hR]
    exact borderLatestMono hB hbord

/-- The source outputs after a Pipe edge. -/
theorem pipeOut (R k : Nat) (hk : k + 1 < R) (s : CohortLane) :
    (cohortEdge R s k).out k =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).1 ∧
      (cohortEdge R s k).out (k + 1) =
        (bankRepairDigitPipeStep (decide (k = 0)) (s.out k) (s.out (k + 1))).2 ∧
      ∀ q, q ≠ k → q ≠ k + 1 → (cohortEdge R s k).out q = s.out q := by
  refine ⟨?_, ?_, fun q h1 h2 => ?_⟩
  · simp [cohortEdge, hk, cohortUpd]
  · simp [cohortEdge, hk, cohortUpd]
  · simp [cohortEdge, hk, cohortUpd, h1, h2]

/-- The source outputs after the Del edge. -/
theorem delOut (R k : Nat) (hk : k + 1 = R) (s : CohortLane) :
    (cohortEdge R s k).out k =
        (bankRepairDigitDelStep (s.out k) (s.inp (k + 1)) (s.live (k + 1))).1 ∧
      ∀ q, q ≠ k → (cohortEdge R s k).out q = s.out q := by
  have c1 : ¬ k + 1 < R := by omega
  refine ⟨?_, fun q h1 => ?_⟩
  · simp [cohortEdge, c1, hk, cohortUpd]
  · simp [cohortEdge, c1, hk, cohortUpd, h1]

/-- **Pipe edge** `a(k) → a(k+1)`, `k + 1 < R`: the barrier hops (`p = k`, right cell `E`), stays
blocked, or both cells are behind it (`tailPipeBehind`); the border keeps its latest tail
(`borderPipe`). Consumer: `tailInvStep`. -/
theorem barrierPipe (R k : Nat) (hk : k + 1 < R) (hgrow : AuditGrows A A')
    (stamp : DigitStamp n) (hst : stamp.time = A.clock + 1) (hsl : stamp.lane = lane)
    (hss : stamp.site = site k) (hsite0 : site 0 = src0) (hs0 : sigma0.time ≤ A.clock)
    (hTB : ∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.time ≤ A.clock)
    (s : CohortLane) (go go' : Nat → DigitOutGhost n)
    (hb : TailBarrier R A lane src0 sigma0 site s.out go)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < R → go' q = go q)
    (hrow : (go' k, go' (k + 1)) =
      ghostPipe stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (go k) (go (k + 1)))
    (hnew : s.out k = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧
      DigitRecordedSample A' smp ∧ smp.cause = (go k).obligation ∧ smp.tail = decide (k = 0))
    (hB : ∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp ∨ (k = 0 ∧ s.out 0 = .U ∧ smp.id = stamp)) :
    TailBarrier R A' lane src0 sigma0 site (cohortEdge R s k).out go' := by
  have hgrow' := hgrow
  obtain ⟨hrec, hclk⟩ := hgrow
  have hle : A.clock ≤ A'.clock := by omega
  obtain ⟨o1, o2, o3⟩ := pipeOut R k hk s
  have g1 : go' k = (ghostPipe stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (go k)
      (go (k + 1))).1 := congrArg Prod.fst hrow
  have g2 : go' (k + 1) = (ghostPipe stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (go k)
      (go (k + 1))).2 := congrArg Prod.snd hrow
  obtain ⟨p, hpR, hpos, hcells, hbord⟩ := hb
  have hcellM : ∀ j, j < p →
      TailCell A' lane src0 sigma0 (site j) (decide (j = 0)) (s.out j) (go j) :=
    fun j hj => tailCellMono hrec hle _ _ (hcells j hj)
  have hborder : BorderLatest A' lane src0 ((cohortEdge R s k).out 0) (go' 0) := by
    by_cases hk0 : k = 0
    · subst hk0
      rw [o1, g1]
      exact borderPipe hgrow' stamp hst hTB (s.out 0) (s.out (0 + 1)) (go 0) (go (0 + 1)) hbord
        (fun smp r1 r2 r3 => (hB smp r1 r2 r3).imp_right (fun h => ⟨h.2.1, h.2.2⟩))
    · rw [o3 0 (Ne.symm hk0) (by omega), hfr 0 (Ne.symm hk0) (by omega) (by omega)]
      refine borderLatestMono (fun smp r1 r2 r3 => ?_) hbord
      rcases hB smp r1 r2 r3 with h | ⟨h, -⟩
      · exact h
      · exact absurd h hk0
  have hbx0 : decide (k = 0) = true → site k = src0 := by
    intro h
    rw [of_decide_eq_true h, hsite0]
  have hdk1 : decide (k + 1 = 0) = false := decide_eq_false (by omega)
  rcases Nat.lt_or_ge (k + 1) p with hlt | hge
  · -- both cells behind the barrier
    have hy := hcells (k + 1) hlt
    rw [hdk1] at hy
    obtain ⟨n1, n2⟩ := tailPipeBehind hgrow' stamp hst hsl (site k) (site (k + 1)) hss
      (decide (k = 0)) hbx0 (s.out k) (s.out (k + 1)) (go k) (go (k + 1))
      (hcells k (by omega)) hy hnew
    refine ⟨p, hpR, fun hp => ?_, fun j hj => ?_, hborder⟩
    · rw [o3 p (by omega) (by omega), hfr p (by omega) (by omega) hp]
      exact hpos hp
    · by_cases e1 : j = k
      · subst e1
        rw [o1, g1]
        exact n1
      · by_cases e2 : j = k + 1
        · subst e2
          rw [o2, g2, hdk1]
          exact n2
        · rw [o3 j e1 e2, hfr j e1 e2 (by omega)]
          exact hcellM j hj
  · rcases Nat.lt_or_ge k p with hlt2 | hge2
    · -- the right cell holds the barrier: it is blocked and settled
      have hpk : p = k + 1 := by omega
      obtain ⟨hD, hat⟩ := hpos (by omega)
      rw [hpk] at hD hat
      have hy : TailCell A lane src0 sigma0 (site (k + 1)) false (s.out (k + 1)) (go (k + 1)) := by
        rw [hD]
        exact ⟨sigma0, hat, ⟨0, DigitTailRank.anchor⟩, hs0⟩
      obtain ⟨n1, -⟩ := tailPipeBehind hgrow' stamp hst hsl (site k) (site (k + 1)) hss
        (decide (k = 0)) hbx0 (s.out k) (s.out (k + 1)) (go k) (go (k + 1))
        (hcells k (by omega)) hy hnew
      obtain ⟨k1, k2⟩ := pipeKeepRight (decide (k = 0)) (s.out k) stamp (go k) (go (k + 1))
      refine ⟨p, hpR, fun _ => ?_, fun j hj => ?_, hborder⟩
      · rw [hpk, o2, g2, hD, k1, k2]
        exact ⟨rfl, hat⟩
      · by_cases e1 : j = k
        · subst e1
          rw [o1, g1]
          exact n1
        · rw [o3 j e1 (by omega), hfr j e1 (by omega) (by omega)]
          exact hcellM j hj
    · rcases Nat.lt_or_ge p k with hlt3 | hge3
      · -- both cells ahead of the barrier
        refine ⟨p, hpR, fun hp => ?_, fun j hj => ?_, hborder⟩
        · rw [o3 p (by omega) (by omega), hfr p (by omega) (by omega) hp]
          exact hpos hp
        · rw [o3 j (by omega) (by omega), hfr j (by omega) (by omega) (by omega)]
          exact hcellM j hj
      · -- the left cell holds the barrier
        have hpk : p = k := by omega
        obtain ⟨hD, hat⟩ := hpos (by omega)
        rw [hpk] at hD hat
        rcases hyo : s.out (k + 1) with _ | _ | T'
        · -- hop
          refine ⟨k + 1, by omega, fun _ => ?_, fun j hj => ?_, hborder⟩
          · rw [o2, g2, hD, hyo]
            exact ⟨rfl, hat⟩
          · by_cases e1 : j = k
            · subst e1
              rw [o1, g1, hD, hyo]
              refine ⟨stamp, sigma0, ?_, ⟨0, DigitTailRank.anchor⟩, hsl, hss, by omega,
                by omega⟩
              show DigitOutGhost.unread (.afterTail stamp (go j).atom) = _
              rw [hat]
            · rw [o3 j e1 (by omega), hfr j e1 (by omega) (by omega)]
              exact hcellM j (by omega)
        · refine ⟨p, hpR, fun _ => ?_, fun j hj => ?_, hborder⟩
          · rw [hpk, o1, g1, hD, hyo]
            exact ⟨rfl, hat⟩
          · rw [o3 j (by omega) (by omega), hfr j (by omega) (by omega) (by omega)]
            exact hcellM j hj
        · refine ⟨p, hpR, fun _ => ?_, fun j hj => ?_, hborder⟩
          · rw [hpk, o1, g1, hD, hyo]
            exact ⟨rfl, hat⟩
          · rw [o3 j (by omega) (by omega), hfr j (by omega) (by omega) (by omega)]
            exact hcellM j hj

/-- **Del edge** `a(R-1) → a(R)`: the barrier leaves the block on an accepted export, stays
blocked, or the cell is behind it (`tailDelBehind`). Consumer: `tailInvStep`. -/
theorem barrierDel (R k : Nat) (hk : k + 1 = R) (hR : 2 ≤ R) (hgrow : AuditGrows A A')
    (stamp : DigitStamp n) (hst : stamp.time = A.clock + 1) (hsl : stamp.lane = lane)
    (hss : stamp.site = site k) (hs0 : sigma0.time ≤ A.clock)
    (s : CohortLane) (go go' : Nat → DigitOutGhost n) (gyi : Option (DigitAtom n))
    (hb : TailBarrier R A lane src0 sigma0 site s.out go)
    (hfr : ∀ q, q ≠ k → q < R → go' q = go q)
    (hrow : go' k =
      (ghostDel stamp (s.out k) (s.inp (k + 1)) (s.live (k + 1)) (go k) gyi).1)
    (hnew : s.out k = .U → ∃ smp : DigitSample c n, smp.id = stamp ∧
      DigitRecordedSample A' smp ∧ smp.cause = (go k).obligation ∧ smp.tail = false)
    (hB : ∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp) :
    TailBarrier R A' lane src0 sigma0 site (cohortEdge R s k).out go' := by
  have hgrow' := hgrow
  obtain ⟨hrec, hclk⟩ := hgrow
  have hle : A.clock ≤ A'.clock := by omega
  obtain ⟨o1, o3⟩ := delOut R k hk s
  obtain ⟨p, hpR, hpos, hcells, hbord⟩ := hb
  have hcellM : ∀ j, j < p →
      TailCell A' lane src0 sigma0 (site j) (decide (j = 0)) (s.out j) (go j) :=
    fun j hj => tailCellMono hrec hle _ _ (hcells j hj)
  have hk0 : k ≠ 0 := by omega
  have hborder : BorderLatest A' lane src0 ((cohortEdge R s k).out 0) (go' 0) := by
    rw [o3 0 (Ne.symm hk0), hfr 0 (Ne.symm hk0) (by omega)]
    exact borderLatestMono hB hbord
  have hdk : decide (k = 0) = false := decide_eq_false hk0
  rcases Nat.lt_or_ge k p with hlt | hge
  · -- the cell is behind the barrier (p = R)
    have hx := hcells k hlt
    rw [hdk] at hx
    have n1 := tailDelBehind hgrow' stamp hst hsl (site k) hss (s.out k) (s.inp (k + 1))
      (s.live (k + 1)) (go k) gyi hx hnew
    refine ⟨p, hpR, fun hp => by omega, fun j hj => ?_, hborder⟩
    by_cases e1 : j = k
    · subst e1
      rw [o1, hrow, hdk]
      exact n1
    · rw [o3 j e1, hfr j e1 (by omega)]
      exact hcellM j hj
  · rcases Nat.lt_or_ge p k with hlt2 | hge2
    · refine ⟨p, hpR, fun hp => ?_, fun j hj => ?_, hborder⟩
      · rw [o3 p (by omega), hfr p (by omega) hp]
        exact hpos hp
      · rw [o3 j (by omega), hfr j (by omega) (by omega)]
        exact hcellM j hj
    · have hpk : p = k := by omega
      obtain ⟨hD, hat⟩ := hpos (by omega)
      rw [hpk] at hD hat
      have hcellsK : ∀ j, j < k →
          TailCell A' lane src0 sigma0 (site j) (decide (j = 0)) ((cohortEdge R s k).out j)
            (go' j) := by
        intro j hj
        rw [o3 j (by omega), hfr j (by omega) (by omega)]
        exact hcellM j (by omega)
      have keep : (cohortEdge R s k).out k = .D true ∧ go' k = go k →
          TailBarrier R A' lane src0 sigma0 site (cohortEdge R s k).out go' := by
        intro ⟨e1, e2⟩
        refine ⟨k, by omega, fun _ => ⟨e1, by rw [e2]; exact hat⟩, hcellsK, hborder⟩
      cases hky : s.live (k + 1)
      · rcases hiy : s.inp (k + 1) with _ | _ | T' | T'
        · -- accepted export: the barrier leaves the block
          refine ⟨R, Nat.le_refl R, fun h => absurd h (Nat.lt_irrefl R), fun j hj => ?_, hborder⟩
          by_cases e1 : j = k
          · subst e1
            rw [o1, hrow, hD, hiy, hky, hdk]
            refine ⟨stamp, sigma0, ?_, ⟨0, DigitTailRank.anchor⟩, hsl, hss, by omega,
              by omega⟩
            show DigitOutGhost.unread (.afterTail stamp (go j).atom) = _
            rw [hat]
          · exact hcellsK j (by omega)
        · exact keep ⟨by rw [o1, hD, hiy, hky]; rfl, by rw [hrow, hD, hiy, hky]; rfl⟩
        · exact keep ⟨by rw [o1, hD, hiy, hky]; rfl, by rw [hrow, hD, hiy, hky]; rfl⟩
        · exact keep ⟨by rw [o1, hD, hiy, hky]; rfl, by rw [hrow, hD, hiy, hky]; rfl⟩
      · exact keep ⟨by rw [o1, hD, hky]; rfl, by rw [hrow, hD, hky]; rfl⟩

end Barrier

/-! ### The border chain and the export clause across one letter -/

section Clauses

variable {c : Compiled} {n : Nat} {A A' : DigitAudit c n} {lane : DigitLane} {src0 : Fin n}
  {sigma0 : DigitStamp n} {site : Nat → Fin n}

/-- **I2 step**: a new border sample is a `U` read at the border, which is behind the barrier
(the barrier's own cell is `D true`); its cause is the border's `afterTail` obligation, naming
the latest border tail. Consumer: `tailInvStep`. -/
theorem borderChainStep (R : Nat) (hR : 0 < R) (hgrow : AuditGrows A A')
    (hTB : ∀ smp : DigitSample c n, DigitRecordedSample A smp → smp.id.time ≤ A.clock)
    (hnewT : ∀ smp : DigitSample c n, DigitRecordedSample A' smp →
      DigitRecordedSample A smp ∨ smp.id.time = A.clock + 1)
    (hsite0 : site 0 = src0) (o : Nat → BankRepairDigitOutSh) (go : Nat → DigitOutGhost n)
    (hbar : TailBarrier R A lane src0 sigma0 site o go)
    (hB : ∀ smp : DigitSample c n, DigitRecordedSample A' smp → smp.id.site = src0 →
      smp.id.lane = lane → DigitRecordedSample A smp ∨
        (smp.id.time = A.clock + 1 ∧ o 0 = .U ∧ smp.cause = (go 0).obligation ∧
          smp.tail = true))
    (hch : BorderChain A lane src0 sigma0) : BorderChain A' lane src0 sigma0 := by
  obtain ⟨hrec, hclk⟩ := hgrow
  intro smp r1 r2 r3 hlt
  rcases hB smp r1 r2 r3 with hold | ⟨ht, hU, hcs, htl⟩
  · obtain ⟨htl, rho, tl, hcs, hrk, hrl, hrs, h1, h2, hlat⟩ := hch smp hold r2 r3 hlt
    have hT := hTB smp hold
    refine ⟨htl, rho, tl, hcs, tailRankedMono hrec hrk, hrl, hrs, h1, h2,
      fun other o1 o2 o3 o4 => ?_⟩
    rcases hnewT other o1 with ho | ho
    · exact hlat other ho o2 o3 o4
    · omega
  · obtain ⟨p, -, hpos, hcells, hbord⟩ := hbar
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · subst h0
        have h' := (hpos hR).1
        rw [hU] at h'
        cases h'
      · exact h0
    have hc := hcells 0 hp
    rw [hU] at hc
    obtain ⟨rho, tl, hg, hrk, hrl, hrs, h1, h2⟩ := hc
    obtain ⟨tl', hshape, hlat⟩ := hbord
    have htt : tl' = tl := by
      rcases hshape with ⟨hD, -⟩ | ⟨-, rho', hg'⟩
      · rw [hU] at hD
        cases hD
      · rw [hg] at hg'
        simp only [DigitOutGhost.unread.injEq, DigitUnread.afterTail.injEq, Option.some.injEq,
          DigitAtom.sampled.injEq] at hg'
        exact hg'.2.symm
    subst htt
    refine ⟨htl, rho, tl', by rw [hcs, hg]; rfl, tailRankedMono hrec hrk, hrl,
      by rw [hrs, hsite0], h1, by omega, fun other o1 o2 o3 o4 => ?_⟩
    rcases hnewT other o1 with ho | ho
    · exact hlat other ho o2 o3
    · omega

/-- **I4 handed to the target**: once the export of `sigma0` is recorded the barrier has left the
block (`hNo`, the M1 clause that an exported atom is on no source cell), so every later export
leaves a settled cell. Consumer: `tailInvStep`. -/
theorem exportRankedStep (R : Nat) (hR : 2 ≤ R) (OnE : DigitExport c n → Prop)
    (hgrow : AuditGrows A A')
    (hXT : ∀ x : DigitExport c n, DigitRecordedExport A x → x.time ≤ A.clock)
    (o : Nat → BankRepairDigitOutSh) (go : Nat → DigitOutGhost n)
    (hbar : TailBarrier R A lane src0 sigma0 site o go)
    (hX : ∀ x : DigitExport c n, DigitRecordedExport A' x → OnE x →
      DigitRecordedExport A x ∨
        (x.time = A.clock + 1 ∧ (∃ T, o (R - 1) = .D T) ∧ x.operand = (go (R - 1)).atom))
    (hNo : ∀ x0 : DigitExport c n, DigitRecordedExport A x0 → OnE x0 →
      x0.operand = some (.sampled sigma0) → ∀ q, q < R → (go q).atom ≠ some (.sampled sigma0))
    (hex : ExportRanked A lane src0 sigma0 OnE) : ExportRanked A' lane src0 sigma0 OnE := by
  obtain ⟨hrec, -⟩ := hgrow
  intro x0 x r0 r e0 e hop hle
  rcases hX x0 r0 e0 with old0 | ⟨t0, -, hop0⟩
  · rcases hX x r e with oldx | ⟨-, ⟨T, hT⟩, hopx⟩
    · rcases hex x0 x old0 oldx e0 e hop hle with h | ⟨smp, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨smp, h1, sampleChainedMono hrec h2⟩
    · obtain ⟨p, hpR, hpos, hcells, -⟩ := hbar
      have hpR' : p = R := by
        rcases Nat.lt_or_ge p R with hlt | hge
        · exact absurd (hpos hlt).2 (hNo x0 old0 e0 hop p hlt)
        · omega
      have hc := hcells (R - 1) (by omega)
      rw [hT] at hc
      cases T
      · obtain ⟨-, smp, hat, hch⟩ := hc
        exact Or.inr ⟨smp, by rw [hopx, hat], sampleChainedMono hrec hch⟩
      · obtain ⟨tl, hat, hrk, -⟩ := hc
        rcases tailRankedCases hrk with h | ⟨smp, hid, -, -, hch⟩
        · left
          rw [hopx, hat, h]
        · right
          exact ⟨smp, by rw [hopx, hat, hid], sampleChainedMono hrec hch⟩
  · rcases hX x r e with oldx | ⟨-, -, hopx⟩
    · have := hXT x oldx
      omega
    · left
      rw [hopx, ← hop0, hop]

end Clauses

/-! ### Audit facts of one letter -/

section Audit

variable {c : Compiled} {n : Nat}

/-- Consumer: `tailInvStep`, `tailChainOfAnchor`. -/
theorem recordedSampleTimeLe (A : DigitAudit c n) (hfo : AuditFrameOrder A)
    (smp : DigitSample c n) (h : DigitRecordedSample A smp) : smp.id.time ≤ A.clock := by
  obtain ⟨f, hf, ht, -⟩ := h
  rw [← ht]
  exact (hfo.2.1 f hf).2

/-- Every recorded sample of the stepped audit is old, or the new frame's sample of its lane.
Consumer: `newBorderSample`, `tailInvStep`. -/
theorem recordedSampleStepCases (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (smp : DigitSample c n)
    (h : DigitRecordedSample (digitAuditStep ring S A e) smp) :
    DigitRecordedSample A smp ∨
      (smp.id.time = A.clock + 1 ∧ smp.id.site = e ∧
        (digitReceiptLane smp.id.lane (svcAt ring S A e)).sample = some smp) := by
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := h
  rcases auditFrameMemStepCases ring S A e f hf with hf' | hf'
  · exact Or.inl ⟨f, hf', h1, h2, h3, h4⟩
  · subst hf'
    exact Or.inr ⟨h1.symm, h2.symm, h3⟩

/-- A lane replay records a sample only on a `U` read (S0), with the stamp of the service, the
old obligation as cause and the border bit as tail. Consumer: `serviceSampleU`. -/
theorem replaySampleU (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) (hlx : x.leader = false)
    (hly : y.leader = false) (smp : DigitSample c n)
    (h : (digitLaneReplay lane time source destination x y gx gy).sample = some smp) :
    bankRepairDigitOutShOf x.out = .U ∧ smp.id = DigitStamp.mk time source lane ∧
      smp.cause = gx.out.obligation ∧ smp.tail = x.marker := by
  cases hxo : x.out with
  | U =>
    obtain ⟨s', h1, h2, -, h4, -, h6, -, -⟩ := recordUnreadRead lane time source destination
      x y gx gy hlx hly (by rw [hxo]; rfl)
    rw [h1] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, h2, h6, h4⟩
  | E =>
    exfalso
    revert h
    cases hym : y.marker <;> cases hxm : x.marker <;>
      simp [digitLaneReplay, hlx, hly, hxo, hym, hxm, OutTok.isD, OutTok.isU, OutTok.isE] <;>
      (repeat' split) <;> simp_all
  | D v T =>
    exfalso
    revert h
    cases hym : y.marker <;> cases hyo : y.out <;>
      simp [digitLaneReplay, hlx, hly, hxo, hym, hyo, OutTok.isD, OutTok.isU, OutTok.isE] <;>
      (repeat' split) <;> simp_all

/-- `replaySampleU` on the record fields. Consumer: `newBorderSample`. -/
theorem serviceSampleU (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (smp : DigitSample c n)
    (h : (digitReceiptLane lane (digitService t e d X Y gx gy)).sample = some smp) :
    bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top) = .U ∧
      smp.id = DigitStamp.mk t e lane ∧ smp.cause = (laneGhost lane gx).out.obligation ∧
      smp.tail = laneMarkerX lane X Y := by
  rw [serviceLane] at h
  obtain ⟨h1, h2, h3, h4⟩ := replaySampleU lane t e d _ _ _ _
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly) smp h
  rw [laneViewOutSh] at h1
  rw [laneViewMarker] at h4
  exact ⟨h1, h2, h3, h4⟩

/-- A `U` read records a sample of the new frame whose cause is the old obligation (S0).
Consumer: `barrierStep`. -/
theorem freshSampleCause (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (lane : DigitLane) (hlx : (S e).word.native.l = false)
    (hly : (S (ring.rightNeighbor e)).word.native.l = false)
    (hU : bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (S e).top) = .U) :
    ∃ smp : DigitSample c n, smp.id = DigitStamp.mk (A.clock + 1) e lane ∧
      DigitRecordedSample (digitAuditStep ring S A e) smp ∧
      smp.cause = (laneGhost lane (A.current e)).out.obligation ∧
      smp.tail = laneMarkerX lane (S e) (S (ring.rightNeighbor e)) := by
  obtain ⟨s', h1, h2, -, h4, h5, h6, -, -⟩ := recordUnreadRead lane (A.clock + 1) e
    (ring.rightNeighbor e)
    (digitLaneView lane (S e) (laneMarkerX lane (S e) (S (ring.rightNeighbor e))))
    (digitLaneView lane (S (ring.rightNeighbor e))
      (laneMarkerY lane (S e) (S (ring.rightNeighbor e))))
    (laneGhost lane (A.current e)) (laneGhost lane (A.current (ring.rightNeighbor e)))
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewOutSh]; exact hU)
  refine ⟨s', h2, ⟨DigitFrame.mk (A.clock + 1) e S A.current (svcAt ring S A e),
    List.mem_cons.mpr (Or.inl rfl), by rw [h2], by rw [h2], ?_, ?_⟩, h6,
    by rw [h4, laneViewMarker]⟩
  · show (digitReceiptLane s'.id.lane (svcAt ring S A e)).sample = some s'
    rw [h2]
    show (digitReceiptLane lane (digitService (A.clock + 1) e (ring.rightNeighbor e) (S e)
      (S (ring.rightNeighbor e)) (A.current e) (A.current (ring.rightNeighbor e)))).sample = _
    rw [serviceLane]
    exact h1
  · show s'.value = (S e).top.d
    rw [h5, laneViewDigit]

end Audit

/-! ### The barrier on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- The barrier invariant of one pair and lane, read on the actual audit ghosts. -/
def SourceBarrier (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (sigma0 : DigitStamp n) (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  TailBarrier R A lane (digitSite ring root src) sigma0 (fun j => digitSite ring root (src + j))
    (cohortProj ring root lane src R S).out
    (fun q => (laneCells ring root lane src A.current q).out)

/-- **The anchored run invariant**: once the border-tail sample `sigma0` (at the
source delimiter, on this lane) is recorded, the barrier invariant, the border chain (I2) and
the export clause hold. Vacuous before `sigma0` is minted, so it holds from the audit start.
Consumer: `tailInvStep`, `tailInvFromStart`, `tailChainOfAnchor`. -/
def TailInv (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (sigma0 : DigitStamp n) (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  (∃ s0 : DigitSample c n, DigitRecordedSample A s0 ∧ s0.id = sigma0) →
  sigma0.site = digitSite ring root src → sigma0.lane = lane →
  SourceBarrier ring root lane src R sigma0 S A ∧
  BorderChain A lane (digitSite ring root src) sigma0 ∧
  ExportRanked A lane (digitSite ring root src) sigma0 (OnEdge ring root lane src R)

/-- Source outputs are untouched by the target edges. -/
theorem edgeOutHigh (R k : Nat) (hk : R ≤ k) (s : CohortLane) :
    (cohortEdge R s k).out = s.out := by
  have c1 : ¬ k + 1 < R := by omega
  have c2 : ¬ k + 1 = R := by omega
  unfold cohortEdge
  rw [if_neg c1, if_neg c2]
  by_cases h3 : k + 1 < 2 * R
  · rw [if_pos h3]
  · rw [if_neg h3]
    by_cases h4 : k + 1 = 2 * R
    · rw [if_pos h4]
    · rw [if_neg h4]

/-- A new recorded border sample of this lane is a `U` read at the border by this letter (S0).
Consumer: `barrierStep`, `tailInvStep`. -/
theorem newBorderSample (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (lane : DigitLane) (A : DigitAudit c n) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (smp : DigitSample c n)
    (h : DigitRecordedSample (digitAuditStep ring S A (digitSite ring root j)) smp)
    (hs : smp.id.site = digitSite ring root src) (hl : smp.id.lane = lane) :
    DigitRecordedSample A smp ∨
      (j = src ∧ smp.id = DigitStamp.mk (A.clock + 1) (digitSite ring root src) lane ∧
        bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (S (digitSite ring root src)).top) =
          .U ∧
        smp.cause = (laneGhost lane (A.current (digitSite ring root src))).out.obligation ∧
        smp.tail = true) := by
  rcases recordedSampleStepCases ring S A _ smp h with hold | ⟨-, hse, hrc⟩
  · exact Or.inl hold
  · right
    have hjs : j = src :=
      bankRepairDigitSiteInj ring root hj (by omega) (hse.symm.trans hs)
    subst hjs
    rw [hl] at hrc
    have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := serviceSampleU lane (A.clock + 1) _ _ _ _ _ _ hlx hly smp hrc
    refine ⟨rfl, h2, h1, h3, ?_⟩
    rw [h4, laneMarkerXBeta lane _ _ hbX]
    exact hb0

/-- A new recorded export on the delimiter edge comes from an accepted `D` at `a(R-1)` and
carries its ghost atom. Consumer: `tailInvStep`. -/
theorem newEdgeExport (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n) (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (x : DigitExport c n)
    (h : DigitRecordedExport (digitAuditStep ring S A (digitSite ring root j)) x)
    (he : OnEdge ring root lane src R x) :
    DigitRecordedExport A x ∨
      (x.time = A.clock + 1 ∧ (∃ T, (cohortProj ring root lane src R S).out (R - 1) = .D T) ∧
        x.operand = (laneCells ring root lane src A.current (R - 1)).out.atom) := by
  rcases recordedExportStepCases ring S A _ x h with hold | ⟨ht, hse, hrc⟩
  · exact Or.inl hold
  · right
    obtain ⟨hl, hsr⟩ := he
    have hjs : j = src + (R - 1) :=
      bankRepairDigitSiteInj ring root hj (by omega) (hse.symm.trans hsr)
    subst hjs
    rw [hl] at hrc
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1)) (by omega)
      (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1) + 1) (by omega)
      (by omega)
    have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
        (S (digitSite ring root (src + (R - 1) + 1))) = false := by
      rw [laneMarkerXBeta lane _ _ hbX]
      exact hbF (R - 1) (by omega) (by omega) (by omega)
    have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
        (S (digitSite ring root (src + (R - 1) + 1))) = true := by
      rw [laneMarkerYBeta lane _ _ hbY, show src + (R - 1) + 1 = src + R by omega]
      exact hbR
    obtain ⟨T, hT, -, -⟩ := delExportShapes lane (A.clock + 1) _ _ _ _ _ _ hlx hly hmx hmy x hrc
    obtain ⟨hop, -, -⟩ := delExportD lane (A.clock + 1) _ _ _ _ _ _ hlx hly hmx hmy x hrc
    refine ⟨ht, ⟨T, ?_⟩, hop⟩
    rw [projOut ring root lane src R S (R - 1) (by omega)]
    exact hT

/-- **The barrier across one letter on the ring** (one lemma per edge class, as in
`ghostCorrStep`). Consumer: `tailInvStep`. -/
theorem barrierStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
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
        (S (digitSite ring root (j + 1))).word.beta)
    (sigma0 : DigitStamp n) (hfo : AuditFrameOrder A) (hs0 : sigma0.time ≤ A.clock)
    (h : SourceBarrier ring root lane src R sigma0 S A) :
    SourceBarrier ring root lane src R sigma0 (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  have hgrow : AuditGrows A (digitAuditStep ring S A (digitSite ring root j)) :=
    ⟨fun smp hs => recordedSampleStep ring S A _ smp hs, rfl⟩
  have hTB := fun smp hs => recordedSampleTimeLe A hfo smp hs
  have hBnew := fun smp hs hsi hl =>
    newBorderSample ring root S src R hR hsrc hend hroot hb0 lane A j hj hbX smp hs hsi hl
  unfold SourceBarrier
  rw [cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j hj hbX hbY]
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin]
    obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    rw [Nat.add_sub_cancel_left]
    show TailBarrier R _ lane _ sigma0 _ (cohortEdge R (cohortProj ring root lane src R S) k).out _
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
      apply barrierPipe (site := fun j => digitSite ring root (src + j))
        (src0 := digitSite ring root src) R k h1 hgrow
        (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane) rfl rfl rfl rfl hs0
        hTB (cohortProj ring root lane src R S)
        (fun q => (laneCells ring root lane src A.current q).out)
        (fun q => (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current q).out) h
        (fun q a b d => hfr q a b (by omega))
      · show ((laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current k).out,
          (laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).out) = _
        rw [hx, hy, projOut ring root lane src R S k (by omega),
          projOut ring root lane src R S (k + 1) h1, ← hmX]
        exact rowPipeD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
      · intro hU
        rw [projOut ring root lane src R S k (by omega)] at hU
        obtain ⟨smp, e1, e2, e3, e4⟩ :=
          freshSampleCause ring S A (digitSite ring root (src + k)) lane hlx hly hU
        exact ⟨smp, e1, e2, e3, by rw [e4]; exact hmX⟩
      · intro smp r1 r2 r3
        rcases hBnew smp r1 r2 r3 with h' | ⟨hk0, hid, hU, -, -⟩
        · exact Or.inl h'
        · right
          obtain rfl : k = 0 := by omega
          exact ⟨rfl, by rw [projOut ring root lane src R S 0 (by omega)]; exact hU, hid⟩
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
        apply barrierDel (site := fun j => digitSite ring root (src + j))
          (src0 := digitSite ring root src) R k h2 hR hgrow
          (DigitStamp.mk (A.clock + 1) (digitSite ring root (src + k)) lane) rfl rfl rfl hs0
          (cohortProj ring root lane src R S)
          (fun q => (laneCells ring root lane src A.current q).out)
          (fun q => (laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current q).out)
          (laneCells ring root lane src A.current (k + 1)).input h
          (fun q a d => hfr q a (by omega) (by omega))
        · show (laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root (src + k))).current k).out = _
          rw [hx, projOut ring root lane src R S k (by omega),
            projIn ring root lane src R S (k + 1) (by omega) (by omega),
            projLive ring root lane src R S (k + 1) (by omega) (by omega)]
          exact congrArg Prod.fst hrow.1
        · intro hU
          rw [projOut ring root lane src R S k (by omega)] at hU
          obtain ⟨smp, e1, e2, e3, e4⟩ :=
            freshSampleCause ring S A (digitSite ring root (src + k)) lane hlx hly hU
          exact ⟨smp, e1, e2, e3, by rw [e4]; exact hmx⟩
        · intro smp r1 r2 r3
          rcases hBnew smp r1 r2 r3 with h' | ⟨hk0, -⟩
          · exact h'
          · omega
      · -- Fin and Term: the source outputs are framed
        apply barrierFrame R hgrow _ _ _ _ h
          (fun q _ => by rw [edgeOutHigh R k (by omega)])
          (fun q hq => hfr q (by omega) (by omega) (by omega)) (by omega)
        intro smp r1 r2 r3
        rcases hBnew smp r1 r2 r3 with h' | ⟨hk0, -⟩
        · exact h'
        · omega
  · rw [if_neg hin]
    show TailBarrier R _ lane _ sigma0 _ (cohortProj ring root lane src R S).out _
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
    apply barrierFrame R hgrow _ _ _ _ h (fun q _ => rfl) (fun q hq => ?_) (by omega)
    · intro smp r1 r2 r3
      rcases hBnew smp r1 r2 r3 with h' | ⟨hjs, -⟩
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

end L3.TailChain

#print axioms L3.TailChain.tailPipeBehind
#print axioms L3.TailChain.tailDelBehind
#print axioms L3.TailChain.borderPipe
#print axioms L3.TailChain.barrierPipe
#print axioms L3.TailChain.barrierDel
#print axioms L3.TailChain.barrierFrame
#print axioms L3.TailChain.borderChainStep
#print axioms L3.TailChain.exportRankedStep
#print axioms L3.TailChain.barrierStep
#print axioms L3.TailChain.newEdgeExport
