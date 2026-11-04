import Leader.L3.Bank.RepairDigitTailChain

/-!
# ReachRank producer (a) on reached runs: the anchored tail chain

`L3.TailChain` proves that the barrier invariant `TailInv` (S0-S4 as a forward invariant on
the actual audit) survives one letter on the projected ring. This module

* carries it along the coupled BANK x audit chain from the audit start (`TailRun`,
  `tailRunFromStart`): for every border-tail stamp `sigma0` at once, together with the layout,
  the frame order and the distinct correspondence `GhostCorrDistinct`;
* reads S5 off `DigitAnchor` (`anchorTailExport`): the anchor tail is a recorded border sample and
  its export on the delimiter edge precedes the anchor terminal, so the barrier has left the block
  (`tailChainActive`: every source cell settled, the border never `E`, so no bootstrap);
* proves that border-tail ranks are unique on an ordered audit (`tailRankUnique`), so the cohort
  label of a sample (the rank of the tail its cause names, plus one) is well defined;
* states the producer on reached runs (`tailChainFromStart`): every border-tail sample after the
  anchor tail names the latest earlier border sample through a border rearm, with strict times,
  and has the next `DigitTailRank` (I2); every source cell is ranked in the sense of
  `DigitRankedOutput` (I3/I4); every export no earlier than the anchor export carries the anchor
  tail or a chained sample.
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

/-! ### One letter of the run invariant -/

section Step

variable {c : Compiled} {n : Nat}

/-- **`TailInv` across one letter** (projected ring, layout hypotheses of `cohortProjStep`).
If `sigma0` was recorded before, the barrier, the border chain and the export clause step; if it
is minted by this letter (a `U` read at the border), the barrier starts at the border with the new
`D true` carrying exactly `sampled sigma0`. Consumer: `tailRunStep`. -/
theorem tailInvStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
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
    (sigma0 : DigitStamp n) (hfo : AuditFrameOrder A)
    (hgd : GhostCorrDistinct ring root lane src R Base S A)
    (h : TailInv ring root lane src R sigma0 S A) :
    TailInv ring root lane src R sigma0 (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  intro ⟨s0, hr0, hid0⟩ hsite hlane
  have hgrow : AuditGrows A (digitAuditStep ring S A (digitSite ring root j)) :=
    ⟨fun smp hs => recordedSampleStep ring S A _ smp hs, rfl⟩
  have hfo' := auditFrameOrderStep ring S A (digitSite ring root j) hfo
  have hgd' := ghostCorrDistinctStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF
    lane Base A j hj hbX hbY hgd
  rcases newBorderSample ring root S src R hR hsrc hend hroot hb0 lane A j hj hbX s0 hr0
      (by rw [hid0]; exact hsite) (by rw [hid0]; exact hlane) with hold | ⟨hjs, hid, hU, -, -⟩
  · obtain ⟨hb, hc, hx⟩ := h ⟨s0, hold, hid0⟩ hsite hlane
    have hs0 : sigma0.time ≤ A.clock := by
      rw [← hid0]
      exact recordedSampleTimeLe A hfo s0 hold
    refine ⟨barrierStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A j hj
      hbX hbY sigma0 hfo hs0 hb, ?_, ?_⟩
    · refine borderChainStep (site := fun j => digitSite ring root (src + j)) R (by omega) hgrow
        (fun smp hs => recordedSampleTimeLe A hfo smp hs) (fun smp hs => ?_) rfl _ _ hb
        (fun smp r1 r2 r3 => ?_) hc
      · rcases recordedSampleStepCases ring S A _ smp hs with h' | ⟨h', -⟩
        · exact Or.inl h'
        · exact Or.inr h'
      · rcases newBorderSample ring root S src R hR hsrc hend hroot hb0 lane A j hj hbX smp r1 r2
            r3 with h' | ⟨-, hid', hU', hcs', htl'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨by rw [hid'], by rw [projOut ring root lane src R S 0 (by omega)]; exact hU',
            hcs', htl'⟩
    · exact exportRankedStep (site := fun j => digitSite ring root (src + j)) R hR
        (OnEdge ring root lane src R) hgrow (fun x hx => recordedTimeLe A hfo x hx) _ _ hb
        (fun x hx he => newEdgeExport ring root S src R hR hsrc hend hroot hbR hbF lane A j hj
          hbX hbY x hx he)
        (fun x0 r0 e0 hop q hq hat => hgd.2.2.2.2.1 q sigma0 x0 hq
          (by unfold tracked trackedAt; rw [if_pos hq]; exact hat) r0 e0 hop) hx
  · -- `sigma0` is minted by this letter, a `U` read at the border
    subst hjs
    have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
    have hsig : sigma0 = DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane := by
      rw [← hid0, hid]
    have hst0 : sigma0.time = A.clock + 1 := by rw [hsig]
    have hU0 : bankRepairDigitOutShOf
        (bankRepairDigitLaneOut lane (S (digitSite ring root (j + 0))).top) = .U := hU
    have hout : (cohortProj ring root lane j R (phiD ring S (digitSite ring root j))).out 0 =
        .D true := by
      rw [cohortProjStep ring hn root S R j hR hsrc hend hroot hb0 hbR hb2R hbF lane j hj hbX hbY]
      have he := cohortEdgeOfSite ring root j R hend 0 (by omega)
      rw [Nat.add_zero] at he
      rw [he]
      show (cohortEdge R _ 0).out 0 = _
      rw [(pipeOut R 0 (by omega) _).1, projOut ring root lane j R S 0 (by omega), hU0]
      rfl
    have hgh : (laneCells ring root lane j
        (digitAuditStep ring S A (digitSite ring root j)).current 0).out =
        .packet (some (.sampled sigma0)) := by
      obtain ⟨s', -, h2, -, -, h5⟩ := recordUnreadReadD lane (A.clock + 1) (digitSite ring root j)
        (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
        (S (ring.rightNeighbor (digitSite ring root j))) (A.current (digitSite ring root j))
        (A.current (ring.rightNeighbor (digitSite ring root j))) hlx hly hU
      show (laneGhost lane ((digitAuditStep ring S A (digitSite ring root j)).current
        (digitSite ring root j))).out = _
      rw [curX]
      unfold svcAt
      rw [h5, h2, hsig]
    have hat : (laneCells ring root lane j
        (digitAuditStep ring S A (digitSite ring root j)).current 0).out.atom =
        some (.sampled sigma0) := by
      rw [hgh]
      rfl
    refine ⟨⟨0, Nat.zero_le _, fun _ => ⟨hout, hat⟩, fun q hq => absurd hq (Nat.not_lt_zero _),
      sigma0, Or.inl ⟨hout, hat⟩, fun smp r1 _ _ => ?_⟩, ?_, ?_⟩
    · have : smp.id.time ≤ A.clock + 1 := recordedSampleTimeLe _ hfo' smp r1
      omega
    · intro smp r1 _ _ hlt
      have : smp.id.time ≤ A.clock + 1 := recordedSampleTimeLe _ hfo' smp r1
      omega
    · intro x0 x r0 _ e0 _ hop _
      obtain ⟨h1, h2⟩ := hgd'.2.2.2.1 x0 sigma0 r0 e0 hop
      have h2' : x0.time ≤ A.clock + 1 := h2
      omega

end Step

/-! ### The coupled run -/

section Run

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- **The run invariant**: layout, frame order, the distinct correspondence, and `TailInv` for
every border-tail stamp. Consumer: `tailRunStep`, `tailRunFromStart`, `tailChainOfRun`. -/
def TailRun (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  CohortLayout ring hbank root src R z.1 ∧ AuditFrameOrder z.2 ∧
  GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2 ∧
  ∀ sigma0 : DigitStamp n, TailInv ring root lane src R sigma0 (piD z.1.val.1) z.2

include hn hR hsrc hend in
/-- One coupled letter keeps `TailRun`. Consumer: `tailRunWord`. -/
theorem tailRunStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : TailRun ring hbank root lane src R Base z) (e : Fin n) :
    TailRun ring hbank root lane src R Base (bankRepairDigitBoundaryAuditNext ring hbank z e) := by
  obtain ⟨hz, hfo, hgd, hinv⟩ := h
  obtain ⟨hz', hgd'⟩ :=
    ghostCorrDistinctBankStep ring hn hbank root lane src R hR hsrc hend Base z hz hgd e
  refine ⟨hz', auditFrameOrderStep ring _ z.2 e hfo, hgd', fun sigma0 => ?_⟩
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  show TailInv ring root lane src R sigma0 (piD (bankRepairNext ring hbank z.1 e).val.1)
    (digitAuditStep ring (piD z.1.val.1) z.2 e)
  rw [heq]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact tailInvStep ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hb0 hbR hb2R
    hbF lane Base z.2 j hj hbX hbY sigma0 hfo hgd (hinv sigma0)

include hn hR hsrc hend in
/-- `TailRun` along every coupled word. Consumer: `tailRunFromStart`. -/
theorem tailRunWord (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      TailRun ring hbank root lane src R Base z →
      TailRun ring hbank root lane src R Base
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z) := by
  induction word with
  | nil => intro z h; exact h
  | cons e rest ih =>
      intro z h
      exact ih _ (tailRunStep ring hn hbank root lane src R hR hsrc hend Base z h e)

/-- At the audit start nothing is recorded, so `TailInv` is vacuous. Consumer:
`tailRunFromStart`. -/
theorem tailInvInitial {c : Compiled} (S : Fin n → ProjD c) (sigma0 : DigitStamp n) :
    TailInv ring root lane src R sigma0 S (digitAuditInitial S) := by
  intro ⟨s0, ⟨f, hf, _⟩, _⟩
  exact absurd hf (List.not_mem_nil)

include hn hR hsrc hend in
/-- **The reached-run invariant**: from the audit start of any layout state, along every coupled
word. Consumer: `tailChainFromStart`. -/
theorem tailRunFromStart (z : BankReferenceState ring hbank)
    (hz : CohortLayout ring hbank root src R z) (word : List (Fin n)) :
    TailRun ring hbank root lane src R (InheritedOk lane)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (z, digitAuditInitial (piD z.val.1))) :=
  tailRunWord ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) word _
    ⟨hz, auditFrameOrderInitial _, ghostCorrDistinctInitial ring root lane src R _,
      fun sigma0 => tailInvInitial ring root lane src R _ sigma0⟩

end Run

/-! ### S5: the anchor activates the block -/

section Anchor

variable {c : Compiled} {n : Nat}

/-- **S5 from the anchor record**: the anchor tail is a recorded border sample of the lane, and
the completion's `j = 0` export carries it on the delimiter edge strictly before the anchor
terminal. Consumer: `tailChainOfRun`. -/
theorem anchorTailExport (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (src R : Nat) (hr : digitSpan c = R) (lane : DigitLane) (T0 : DigitTerminal c n)
    (sigma0 : DigitStamp n) (h : DigitAnchor ring A root src (src + R) lane T0 sigma0) :
    (∃ s0 : DigitSample c n, DigitRecordedSample A s0 ∧ s0.id = sigma0) ∧
    sigma0.site = digitSite ring root src ∧ sigma0.lane = lane ∧
    DigitAnchorMember T0 sigma0 ∧
    ∃ x0 : DigitExport c n, DigitRecordedExport A x0 ∧ OnEdge ring root lane src R x0 ∧
      x0.operand = some (.sampled sigma0) ∧ x0.time < T0.time := by
  obtain ⟨⟨hc, -⟩, ledger, firstUse, sample, a1, a2, a3, a4, a5, a6, a7, -⟩ := h
  obtain ⟨-, -, -, -, -, -, positive, ledger', samples, exports, uses, l1, -, -, hall, -, -⟩ := hc
  have hle : ledger' = ledger := Option.some.inj (l1.symm.trans a1)
  subst hle
  obtain ⟨-, -, -, -, -, x1, x2, x3, -, x5, -, -, u1, -, u3, -, -, -, t2, t3⟩ :=
    hall ⟨0, positive⟩
  have hhead : ledger'.uses.head? = ledger'.uses[0]? := by
    cases ledger'.uses <;> rfl
  have hfu : firstUse = uses ⟨0, positive⟩ := by
    rw [hhead] at a2
    exact Option.some.inj (a2.symm.trans u1)
  have hsg : sigma0 = (samples ⟨0, positive⟩).id := by
    have h3 := a3
    rw [hfu, u3] at h3
    exact (DigitAtom.sampled.inj (Option.some.inj h3)).symm
  have hmem : firstUse ∈ ledger'.uses := by
    cases hl : ledger'.uses with
    | nil => rw [hl] at a2; cases a2
    | cons u rest =>
        rw [hl] at a2
        obtain rfl := Option.some.inj a2
        exact List.Mem.head _
  refine ⟨⟨sample, a4, a5⟩, by rw [← a5]; exact a7, by rw [← a5]; exact a6,
    ⟨ledger', firstUse, a1, hmem, a3⟩, exports ⟨0, positive⟩, x1, ⟨x2, by rw [x3, hr]⟩,
    by rw [x5, hsg], by omega⟩

/-- **Activation**: once the export of `sigma0` on the delimiter edge is recorded, the barrier
has left the block (the M1 clause: an exported atom is on no source cell), so every source cell
is settled and the border is `D true` or `U`. Consumer: `tailChainOfRun`. -/
theorem tailChainActive (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (sigma0 : DigitStamp n) (hgd : GhostCorrDistinct ring root lane src R Base S A)
    (hinv : TailInv ring root lane src R sigma0 S A)
    (hs0 : ∃ s0 : DigitSample c n, DigitRecordedSample A s0 ∧ s0.id = sigma0)
    (hsite : sigma0.site = digitSite ring root src) (hlane : sigma0.lane = lane)
    (x0 : DigitExport c n) (hx0 : DigitRecordedExport A x0) (he0 : OnEdge ring root lane src R x0)
    (hop0 : x0.operand = some (.sampled sigma0)) :
    (∀ q, q < R → TailCell A lane (digitSite ring root src) sigma0 (digitSite ring root (src + q))
      (decide (q = 0)) ((cohortProj ring root lane src R S).out q)
      (laneCells ring root lane src A.current q).out) ∧
    BorderLatest A lane (digitSite ring root src) ((cohortProj ring root lane src R S).out 0)
      (laneCells ring root lane src A.current 0).out ∧
    BorderChain A lane (digitSite ring root src) sigma0 ∧
    ExportRanked A lane (digitSite ring root src) sigma0 (OnEdge ring root lane src R) := by
  obtain ⟨⟨p, hpR, hpos, hcells, hbord⟩, hc, hx⟩ := hinv hs0 hsite hlane
  have hp : p = R := by
    rcases Nat.lt_or_ge p R with hlt | hge
    · exact absurd hop0 (hgd.2.2.2.2.1 p sigma0 x0 hlt
        (by unfold tracked trackedAt; rw [if_pos hlt]; exact (hpos hlt).2) hx0 he0)
    · omega
  exact ⟨fun q hq => hcells q (by omega), hbord, hc, hx⟩

end Anchor

/-! ### Rank uniqueness and the target's ranked outputs -/

section Ranks

variable {c : Compiled} {n : Nat} {A : DigitAudit c n} {lane : DigitLane} {src0 : Fin n}
  {sigma0 : DigitStamp n}

/-- Ranked tails are no older than the anchor tail. Consumer: `tailRankUnique`. -/
theorem tailRankTimeGe {t : DigitStamp n} {k : Nat}
    (h : DigitTailRank A lane src0 sigma0 t k) : sigma0.time ≤ t.time := by
  induction h with
  | anchor => exact Nat.le_refl _
  | successor _ sample rearm _ _ _ _ _ _ _ previousBefore rearmBefore ih => omega

/-- Two recorded samples with one id are equal (frame times are injective). Consumer:
`tailRankUnique`. -/
theorem recordedSampleUnique (hfo : AuditFrameOrder A) {s s' : DigitSample c n}
    (h : DigitRecordedSample A s) (h' : DigitRecordedSample A s') (hid : s.id = s'.id) :
    s = s' := by
  obtain ⟨f, hf, t1, -, r1, -⟩ := h
  obtain ⟨f', hf', t1', -, r1', -⟩ := h'
  have hff : f = f' := auditFrameTimeInj A hfo f f' hf hf' (by rw [t1, t1', hid])
  subst hff
  rw [hid, r1'] at r1
  exact (Option.some.inj r1).symm

/-- Inversion of `DigitTailRank`. Consumer: `tailRankUnique`. -/
theorem tailRankInv {t : DigitStamp n} {k : Nat} (h : DigitTailRank A lane src0 sigma0 t k) :
    (t = sigma0 ∧ k = 0) ∨
      ∃ (previous : DigitStamp n) (rank : Nat) (sample : DigitSample c n) (rearm : DigitStamp n),
        k = rank + 1 ∧ sample.id = t ∧ DigitTailRank A lane src0 sigma0 previous rank ∧
        DigitRecordedSample A sample ∧
        sample.cause = some (DigitUnread.afterTail rearm (some (DigitAtom.sampled previous))) ∧
        previous.time < rearm.time ∧ rearm.time < sample.id.time := by
  cases h with
  | anchor => exact Or.inl ⟨rfl, rfl⟩
  | successor hprev sample rearm recorded _ _ _ cause _ _ previousBefore rearmBefore =>
    exact Or.inr ⟨_, _, sample, rearm, rfl, rfl, hprev, recorded, cause, previousBefore,
      rearmBefore⟩

/-- **Ranks are unique** on an ordered audit: the cohort label of a sample (rank of the tail its
cause names, plus one) is well defined. Consumer: producers (b), (c) (epoch labels). -/
theorem tailRankUnique (hfo : AuditFrameOrder A) {t : DigitStamp n} {k : Nat}
    (h : DigitTailRank A lane src0 sigma0 t k) :
    ∀ {k' : Nat}, DigitTailRank A lane src0 sigma0 t k' → k = k' := by
  induction h with
  | anchor =>
    intro k' h'
    rcases tailRankInv h' with ⟨-, hk⟩ | ⟨previous, rank, sample, rearm, -, hid, hp, -, -, h1, h2⟩
    · exact hk.symm
    · have := tailRankTimeGe hp
      rw [hid] at h2
      omega
  | successor hprev sample rearm recorded _ _ _ cause _ _ previousBefore rearmBefore ih =>
    intro k' h'
    rcases tailRankInv h' with ⟨hs, -⟩ | ⟨previous', rank', sample', rearm', hk, hid, hp, hr, hc,
        -, -⟩
    · have := tailRankTimeGe hprev
      rw [hs] at rearmBefore
      omega
    · have hss : sample' = sample := recordedSampleUnique hfo hr recorded hid
      subst hss
      rw [cause] at hc
      simp only [Option.some.injEq, DigitUnread.afterTail.injEq, DigitAtom.sampled.injEq] at hc
      obtain ⟨-, hpp⟩ := hc
      subst hpp
      rw [hk, ih hp]

/-- A chained sample is in the successor cohort of its tail's rank. Consumer:
`settledRankedOutput`. -/
theorem chainedCohort (anchor : DigitTerminal c n) {smp : DigitSample c n}
    (h : SampleChained A lane src0 sigma0 smp) :
    ∃ k, DigitSampleCohort A lane src0 anchor sigma0 smp (k + 1) := by
  obtain ⟨r, l, rho, tl, cs, ⟨k, hk⟩, rl, rs, t1, t2⟩ := h
  exact ⟨k, r, l, Or.inr ⟨tl, k, rho, rfl, hk, cs, rl, rs, t1, t2⟩⟩

/-- **I3/I4 in the target's terms**: a settled source cell is a `DigitRankedOutput` (the source
half of `DigitPairRanked`). Consumer: the `DigitPairRanked` / ReachRank assembly. -/
theorem settledRankedOutput (anchor : DigitTerminal c n) (site : Fin n) (border : Bool)
    (hmem : DigitAnchorMember anchor sigma0) (s0 : DigitSample c n)
    (hr0 : DigitRecordedSample A s0) (hid0 : s0.id = sigma0) (hl0 : s0.id.lane = lane)
    (v : DigitLaneView c) (g : DigitLaneGhost c n)
    (hc : TailCell A lane src0 sigma0 site border (bankRepairDigitOutShOf v.out) g.out) :
    DigitRankedOutput A lane src0 site anchor sigma0 A.clock v g := by
  unfold DigitRankedOutput
  cases hv : v.out with
  | E => trivial
  | U =>
    rw [hv] at hc
    obtain ⟨rho, tl, hg, ⟨k, hk⟩, hrl, hrs, h1, h2⟩ := hc
    exact ⟨_, k + 1, hg, ⟨tl, k, rho, rfl, hk, rfl, hrl, h1⟩, hrs, h2⟩
  | D val T =>
    rw [hv] at hc
    cases T
    · obtain ⟨-, smp, hat, hch⟩ := hc
      obtain ⟨k, hk⟩ := chainedCohort anchor hch
      exact ⟨k + 1, smp, hat, hk⟩
    · obtain ⟨tl, hat, hrk, -⟩ := hc
      rcases tailRankedCases hrk with htl | ⟨smp, hid, -, -, hch⟩
      · exact ⟨0, s0, by rw [hat, htl, hid0], hr0, hl0, Or.inl ⟨rfl, by rw [hid0]; exact hmem⟩⟩
      · obtain ⟨k, hk⟩ := chainedCohort anchor hch
        exact ⟨k + 1, smp, by rw [hat, hid], hk⟩

end Ranks

/-! ### The producer on reached runs -/

section Producer

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

include hR in
/-- **ReachRank producer (a), tail succession** at any state carrying the run
invariant, given the anchor record:

1. every border-tail sample of the lane after the anchor tail has tail bit set and cause
   `afterTail rho (some (sampled tl))` with `rho` a border rearm of the lane,
   `tl.time < rho.time < smp.id.time`, `tl` the latest earlier border sample, `tl` ranked `k`
   and the sample ranked `k + 1` (`DigitTailRank.successor`), and `tl` the anchor tail or itself a
   recorded border-tail sample;
2. every source cell is ranked (`DigitRankedOutput`, I3/I4 at every offset);
3. the border output is `U` or `D true` (no bootstrap after the anchor tail);
4. every export on the delimiter edge no earlier than the anchor export carries the anchor tail
   or a chained sample.

Consumer: ReachRank step 2 and producers (b)/(c), whose input is S5/I2. -/
theorem tailChainOfRun
    (w : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hw : TailRun ring hbank root lane src R Base w)
    (hr : digitSpan (compileAdvice (ceilLogTwo n)) = R)
    (T0 : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (sigma0 : DigitStamp n)
    (hanc : DigitAnchor ring w.2 root src (src + R) lane T0 sigma0) :
    (∀ smp : DigitSample (compileAdvice (ceilLogTwo n)) n, DigitRecordedSample w.2 smp →
      smp.id.site = digitSite ring root src → smp.id.lane = lane → sigma0.time < smp.id.time →
      smp.tail = true ∧
      ∃ (rho tl : DigitStamp n) (k : Nat),
        smp.cause = some (.afterTail rho (some (.sampled tl))) ∧
        DigitTailRank w.2 lane (digitSite ring root src) sigma0 tl k ∧
        DigitTailRank w.2 lane (digitSite ring root src) sigma0 smp.id (k + 1) ∧
        rho.lane = lane ∧ rho.site = digitSite ring root src ∧
        tl.time < rho.time ∧ rho.time < smp.id.time ∧
        (∀ other : DigitSample (compileAdvice (ceilLogTwo n)) n, DigitRecordedSample w.2 other →
          other.id.site = digitSite ring root src → other.id.lane = lane →
          other.id.time < smp.id.time → other.id.time ≤ tl.time) ∧
        (tl = sigma0 ∨ ∃ prev : DigitSample (compileAdvice (ceilLogTwo n)) n,
          DigitRecordedSample w.2 prev ∧ prev.id = tl ∧
          prev.id.site = digitSite ring root src ∧ prev.id.lane = lane ∧ prev.tail = true)) ∧
    (∀ q, q < R →
      DigitRankedOutput w.2 lane (digitSite ring root src) (digitSite ring root (src + q)) T0
        sigma0 w.2.clock (digitEndpointView lane (piD w.1.val.1) (digitSite ring root (src + q)))
        (digitEndpointGhost lane (w.2.current (digitSite ring root (src + q))))) ∧
    (bankRepairDigitOutShOf
        (bankRepairDigitLaneOut lane (piD w.1.val.1 (digitSite ring root src)).top) = .U ∨
      bankRepairDigitOutShOf
        (bankRepairDigitLaneOut lane (piD w.1.val.1 (digitSite ring root src)).top) = .D true) ∧
    ExportRanked w.2 lane (digitSite ring root src) sigma0 (OnEdge ring root lane src R) := by
  obtain ⟨-, hfo, hgd, hinv⟩ := hw
  obtain ⟨hs0, hsite, hlane, hmem, x0, hx0, he0, hop0, -⟩ :=
    anchorTailExport ring w.2 root src R hr lane T0 sigma0 hanc
  obtain ⟨hcells, hbord, hch, hex⟩ := tailChainActive ring root lane src R Base (piD w.1.val.1)
    w.2 sigma0 hgd (hinv sigma0) hs0 hsite hlane x0 hx0 he0 hop0
  obtain ⟨s0, hr0, hid0⟩ := hs0
  refine ⟨fun smp r1 r2 r3 hlt => ?_, fun q hq => ?_, ?_, hex⟩
  · obtain ⟨htl, rho, tl, hcs, ⟨k, hk⟩, hrl, hrs, h1, h2, hlat⟩ := hch smp r1 r2 r3 hlt
    refine ⟨htl, rho, tl, k, hcs, hk,
      DigitTailRank.successor hk smp rho r1 r3 r2 htl hcs hrl hrs h1 h2, hrl, hrs, h1, h2, hlat, ?_⟩
    rcases tailRankedCases ⟨k, hk⟩ with h | ⟨prev, hid, hps, hpt, hpr, hpl, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨prev, hpr, hid, hps, hpl, hpt⟩
  · have hc := hcells q hq
    rw [projOut ring root lane src R (piD w.1.val.1) q hq] at hc
    refine settledRankedOutput T0 _ (decide (q = 0)) hmem s0 hr0 hid0 (by rw [hid0]; exact hlane) _ _ ?_
    show TailCell _ _ _ _ _ _
      (bankRepairDigitOutShOf (digitLaneView lane (piD w.1.val.1 (digitSite ring root (src + q)))
        (piD w.1.val.1 (digitSite ring root (src + q))).word.beta).out)
      (laneGhost lane (w.2.current (digitSite ring root (src + q)))).out
    rw [laneViewOutSh]
    exact hc
  · obtain ⟨tl, hshape, -⟩ := hbord
    rw [projOut ring root lane src R (piD w.1.val.1) 0 (by omega)] at hshape
    rcases hshape with ⟨hD, -⟩ | ⟨hU, -⟩
    · exact Or.inr hD
    · exact Or.inl hU

include hn hR hsrc hend in
/-- **Producer (a) on reached runs**: the conclusions of `tailChainOfRun` at the end of every
coupled word from the audit start of a layout state, for every anchor of that audit. Consumer:
the reached-run restatement of ReachRank (writer: WidthWriterReceiptsClose over WidthZeroRun;
comparison: WidthComparisonClose clause (R)). -/
theorem tailChainFromStart (z : BankReferenceState ring hbank)
    (hz : CohortLayout ring hbank root src R z) (word : List (Fin n))
    (hr : digitSpan (compileAdvice (ceilLogTwo n)) = R)
    (T0 : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (sigma0 : DigitStamp n)
    (hanc : DigitAnchor ring (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (z, digitAuditInitial (piD z.val.1))).2 root src (src + R) lane T0 sigma0) :
    TailRun ring hbank root lane src R (InheritedOk lane)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (z, digitAuditInitial (piD z.val.1))) ∧
    ∀ q, q < R →
      DigitRankedOutput (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (z, digitAuditInitial (piD z.val.1))).2 lane (digitSite ring root src)
        (digitSite ring root (src + q)) T0 sigma0
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (z, digitAuditInitial (piD z.val.1))).2.clock
        (digitEndpointView lane (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (z, digitAuditInitial (piD z.val.1))).1.val.1) (digitSite ring root (src + q)))
        (digitEndpointGhost lane ((word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (z, digitAuditInitial (piD z.val.1))).2.current (digitSite ring root (src + q)))) := by
  have hw := tailRunFromStart ring hn hbank root lane src R hR hsrc hend z hz word
  exact ⟨hw, (tailChainOfRun ring hbank root lane src R hR (InheritedOk lane) _ hw hr T0 sigma0
    hanc).2.1⟩

end Producer

end L3.TailChain

#print axioms L3.TailChain.tailInvStep
#print axioms L3.TailChain.tailRunStep
#print axioms L3.TailChain.tailRunFromStart
#print axioms L3.TailChain.anchorTailExport
#print axioms L3.TailChain.tailChainActive
#print axioms L3.TailChain.tailRankUnique
#print axioms L3.TailChain.settledRankedOutput
#print axioms L3.TailChain.tailChainOfRun
#print axioms L3.TailChain.tailChainFromStart
