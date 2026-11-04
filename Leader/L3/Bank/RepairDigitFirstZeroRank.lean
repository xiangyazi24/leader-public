import Leader.L3.Bank.RepairDigitFirstZeroPass

/-!
# T19: the first-zero stage, rank layer

The first-zero rank on the projected ring together with its audit. A *pass* is the obligation
carried by one root-launched lineage: its head token sits at site `h`; the edge at `h` advances
the head by one site (the token moves, or merges into the token ahead and the lineage transfers
to the survivor); a ZERO head proposes at its site when it fires. The writable first block is
`[first, E)` with `E = min stop (n - 1)`.

Phases: pass one pending, pass one running, pass two pending, pass two running, done. Pass two is
launched only after pass one is complete, so its proposals are later than pass one's at every
site. Costs: pending `pend + (E + 1)` / `pend` (`pend = E` with site 1 empty, `E + 1`
otherwise), running `(E - h) + (E + 1)` / `E - h`, done `0`. The rank is the least cost over the
valid phase records; no edge raises it and the nominated edge (the head edge, the launch edge or
the edge clearing site 1) lowers it.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ### The frame of the rank -/

/-- Geometry, the audit-start layout, the writable end `E`, extinction at `r0` and the tokens. -/
structure BankRepairDigitZeroFrame {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) :
    Prop where
  geom : BankRepairDigitZeroGeom ring root R first stop S
  start : BankRepairDigitZeroBlock ring root R first stop A.start
  endStop : E ≤ stop
  endSize : E + 1 ≤ n
  endWrit : ∀ k, k < stop → k + 1 < n → k < E
  endTwo : 2 ≤ E
  extinct : DigitBaseExtinct ring root A 0 r0
  retired : r0 ≤ A.clock
  toks : BankRepairDigitZeroToks ring root first stop S A.current

/-- A running pass: lineage, head token at site `h`, covers of `[first, h)` later than `lo`. -/
structure BankRepairDigitZeroRun {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 lo : Nat) (A : DigitAudit c n) (h born last : Nat)
    (chain : List (DigitBaseOrigin n)) : Prop where
  lin : DigitBaseLineage ring root A born chain last
  lastLe : last ≤ A.clock
  bornLo : lo < born
  headPos : 1 ≤ h
  headEnd : h < E
  head : ∃ o rest, chain = o :: rest ∧ (A.current (digitSite ring root h)).base = some o
  cov : ∀ k, first ≤ k → k < h → ∃ p, DigitCoverProposal ring root A 0 r0 A.clock chain
    (digitSite ring root k) p ∧ lo < p.time

/-- A complete pass: covers of `[first, E)` in the window `(lo, stamp]`. -/
structure BankRepairDigitZeroDone {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 lo : Nat) (A : DigitAudit c n) (born last stamp : Nat)
    (chain : List (DigitBaseOrigin n)) : Prop where
  lin : DigitBaseLineage ring root A born chain last
  lastLe : last ≤ A.clock
  bornLo : lo < born
  bornStamp : born ≤ stamp
  stampLe : stamp ≤ A.clock
  cov : ∀ k, first ≤ k → k < E → ∃ p, DigitCoverProposal ring root A 0 r0 A.clock chain
    (digitSite ring root k) p ∧ lo < p.time ∧ p.time ≤ stamp

/-! ### Small facts -/

theorem bankRepairDigitZeroOcc {c : Compiled} {n : Nat} {ring : DirectedRing n} {root : Fin n}
    {first stop : Nat} {S : Fin n → ProjD c} {G : Fin n → DigitGhost c n}
    (ht : BankRepairDigitZeroToks ring root first stop S G) (i : Fin n)
    (o : DigitBaseOrigin n) (h : (G i).base = some o) : (S i).top.wBase ≠ .NONE := by
  intro hw
  rw [ht.empty i hw] at h
  cases h

/-- An occupied site other than the source keeps its label. -/
theorem bankRepairDigitZeroGhostKeep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (hn : 2 ≤ n) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) (time : Nat) (e : Fin n)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta)
    (i : Fin n) (hi : i ≠ e) (hw : (S i).top.wBase ≠ .NONE) :
    (digitGhostStep ring S G time e i).base = (G i).base := by
  obtain ⟨_, _, _, hgy, _, hrest⟩ := bankRepairDigitZeroEdge ring hn S G time e hbX hbY
  by_cases hs : i = ring.rightNeighbor e
  · subst hs
    rw [hgy]
    exact (bankRepairDigitZeroKeepY time e (ring.rightNeighbor e) (S e)
      (S (ring.rightNeighbor e)) (S e).word.beta (S (ring.rightNeighbor e)).word.beta
      (G e).base (G (ring.rightNeighbor e)).base hw).2
  · rw [(hrest i hi hs).2]

/-- The segment of a block layout is the block. -/
theorem bankRepairDigitZeroSegmentEq {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c)
    (hb : BankRepairDigitZeroBlock ring root R first stop S) (first' stop' : Nat)
    (hseg : DigitFirstSegment ring root S first' stop') : first' = first ∧ stop' = stop := by
  obtain ⟨⟨⟨h0, hn', hbt⟩, hbef⟩, ⟨_, hlt, hle, hstopb, hbetw⟩⟩ := hseg
  have h2 := hb.firstTwo
  have h3 := hb.firstStop
  have h4 := hb.stopSize
  have hff : first ≤ first' := ((hb.layout first' h0 hn').1 hbt).1
  have hfeq : first' = first := by
    rcases Nat.lt_or_ge first first' with h | h
    · have := hbef first (by omega) h
      rw [bankRepairDigitZeroBetaFirst ring root R first stop S hb] at this
      cases this
    · omega
  refine ⟨hfeq, ?_⟩
  rcases Nat.lt_or_ge stop' stop with h | h
  · exfalso
    have hb1 := hstopb (by omega)
    rw [bankRepairDigitZeroBetaInner ring root R first stop S hb stop' (by omega) h] at hb1
    cases hb1
  · rcases Nat.lt_or_ge stop stop' with h' | h'
    · exfalso
      have hb1 := hbetw stop (by omega) h'
      rw [bankRepairDigitZeroBetaStop ring root R first stop S hb (by omega)] at hb1
      cases hb1
    · omega

/-! ### Pending launches -/

/-- The pending cost: `E` with site 1 empty, `E + 1` otherwise. -/
def bankRepairDigitZeroPend {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (E : Nat) (S : Fin n → ProjD c) : Nat :=
  if (S (digitSite ring root 1)).top.wBase = .NONE then E else E + 1

/-- The pending nominated edge: the launch edge, or the edge clearing site 1. -/
def bankRepairDigitZeroPendAim {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) : Fin n :=
  if (S (digitSite ring root 1)).top.wBase = .NONE then root else digitSite ring root 1

theorem bankRepairDigitZeroPendLe {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (E : Nat) (S : Fin n → ProjD c) :
    bankRepairDigitZeroPend ring root E S ≤ E + 1 := by
  unfold bankRepairDigitZeroPend
  split <;> omega

theorem bankRepairDigitZeroPendGe {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (E : Nat) (S : Fin n → ProjD c) :
    E ≤ bankRepairDigitZeroPend ring root E S := by
  unfold bankRepairDigitZeroPend
  split <;> omega

theorem bankRepairDigitZeroPendNone {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (E : Nat) (S : Fin n → ProjD c)
    (h : (S (digitSite ring root 1)).top.wBase = .NONE) :
    bankRepairDigitZeroPend ring root E S = E := by
  unfold bankRepairDigitZeroPend
  rw [if_pos h]

theorem bankRepairDigitZeroPendSome {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (E : Nat) (S : Fin n → ProjD c)
    (h : (S (digitSite ring root 1)).top.wBase ≠ .NONE) :
    bankRepairDigitZeroPend ring root E S = E + 1 := by
  unfold bankRepairDigitZeroPend
  rw [if_neg h]

/-- Off the launch, no edge raises the pending cost. -/
theorem bankRepairDigitZeroPendStep {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A) (e : Fin n)
    (hne : ¬ (e = root ∧ (S (digitSite ring root 1)).top.wBase = .NONE)) :
    bankRepairDigitZeroPend ring root E (phiD ring S e) ≤ bankRepairDigitZeroPend ring root E S := by
  have hn := hF.geom.size
  by_cases h1 : (S (digitSite ring root 1)).top.wBase = .NONE
  · have he : e ≠ root := fun h => hne ⟨h, h1⟩
    obtain ⟨hx, _, _, _, _, hrest⟩ := bankRepairDigitZeroEdge ring (by omega) S A.current 0 e
      (hF.geom.betaX e) (hF.geom.betaY e)
    have hS1 : (phiD ring S e (digitSite ring root 1)).top.wBase = .NONE := by
      by_cases hs : digitSite ring root 1 = e
      · rw [hs]
        exact hx
      · have hs' : digitSite ring root 1 ≠ ring.rightNeighbor e := by
          intro h
          exact he (bankRepairDigitRightInj ring e root h.symm)
        rw [(hrest _ hs hs').1]
        exact h1
    rw [bankRepairDigitZeroPendNone ring root E _ hS1, bankRepairDigitZeroPendNone ring root E _ h1]
    exact Nat.le_refl _
  · rw [bankRepairDigitZeroPendSome ring root E _ h1]
    exact bankRepairDigitZeroPendLe ring root E _

/-- The nominated pending edge off the launch clears site 1. -/
theorem bankRepairDigitZeroPendDrop {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A) (e : Fin n)
    (ha : e = bankRepairDigitZeroPendAim ring root S)
    (hne : ¬ (e = root ∧ (S (digitSite ring root 1)).top.wBase = .NONE)) :
    bankRepairDigitZeroPend ring root E (phiD ring S e) + 1 ≤
      bankRepairDigitZeroPend ring root E S := by
  have hn := hF.geom.size
  unfold bankRepairDigitZeroPendAim at ha
  by_cases h1 : (S (digitSite ring root 1)).top.wBase = .NONE
  · rw [if_pos h1] at ha
    exact absurd ⟨ha, h1⟩ hne
  · rw [if_neg h1] at ha
    rw [ha]
    obtain ⟨hx, _, _, _, _, _⟩ := bankRepairDigitZeroEdge ring (by omega) S A.current 0
      (digitSite ring root 1) (hF.geom.betaX _) (hF.geom.betaY _)
    rw [bankRepairDigitZeroPendNone ring root E _ hx, bankRepairDigitZeroPendSome ring root E _ h1]
    exact Nat.le_refl _

/-! ### Pass steps -/

/-- A root launch into an empty site 1 starts a pass. -/
theorem bankRepairDigitZeroLaunch {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    (h1 : (S (digitSite ring root 1)).top.wBase = .NONE) {lo : Nat} (hlo : lo ≤ A.clock) :
    BankRepairDigitZeroRun ring root first E r0 lo (digitAuditStep ring S A root) 1
      (A.clock + 1) (A.clock + 1)
      [DigitBaseOrigin.rootLaunch (A.clock + 1) root (ring.rightNeighbor root)] := by
  have hn := hF.geom.size
  have hE2 := hF.endTwo
  have hf2 := hF.geom.firstTwo
  have hx : (S root).word.native.l = true := (hF.geom.rootIff root).2 rfl
  have hy := bankRepairDigitSiteNonroot ring root S hF.geom.rootIff 1 (by omega) (by omega)
  have hlaunch := bankRepairDigitZeroRowLaunch (A.clock + 1) root (ring.rightNeighbor root)
    (S root) (S (ring.rightNeighbor root)) (S root).word.beta
    (S (ring.rightNeighbor root)).word.beta (A.current root).base
    (A.current (ring.rightNeighbor root)).base hx hy h1
  obtain ⟨_, _, _, hgy, hbY', _⟩ := bankRepairDigitZeroEdge ring (by omega) S A.current
    (A.clock + 1) root (hF.geom.betaX _) (hF.geom.betaY _)
  obtain ⟨f, hf, hft, hfe, hfb⟩ := bankRepairDigitZeroHead ring S A root
  rw [hbY'] at hfb
  refine ⟨DigitBaseLineage.launch (A.clock + 1) ⟨f, hf, hft, hfe, by rw [hfb]; exact hlaunch.2⟩,
    Nat.le_refl _, by omega, Nat.le_refl _, by omega, ⟨_, [], rfl, ?_⟩,
    fun k hk1 hk2 => absurd hk2 (by omega)⟩
  show (digitGhostStep ring S A.current (A.clock + 1) root (ring.rightNeighbor root)).base = _
  rw [hgy]
  exact hlaunch.2

/-- Off the head edge a running pass stays put. -/
theorem bankRepairDigitZeroRunKeep {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 lo : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    {h b l : Nat} {ch : List (DigitBaseOrigin n)}
    (hr : BankRepairDigitZeroRun ring root first E r0 lo A h b l ch) (e : Fin n)
    (he : e ≠ digitSite ring root h) :
    BankRepairDigitZeroRun ring root first E r0 lo (digitAuditStep ring S A e) h b l ch := by
  have hn := hF.geom.size
  obtain ⟨o, rest, hch, hlab⟩ := hr.head
  refine ⟨bankRepairDigitZeroLineageMono ring root A _ (bankRepairDigitZeroStepSub ring S A e)
      hr.lin, Nat.le_trans hr.lastLe (Nat.le_succ _), hr.bornLo, hr.headPos, hr.headEnd,
    ⟨o, rest, hch, ?_⟩, fun k hk1 hk2 => ?_⟩
  · show (digitGhostStep ring S A.current (A.clock + 1) e (digitSite ring root h)).base = some o
    rw [bankRepairDigitZeroGhostKeep ring (by omega) S A.current (A.clock + 1) e
      (hF.geom.betaX e) (hF.geom.betaY e) _ (fun h' => he h'.symm)
      (bankRepairDigitZeroOcc hF.toks _ o hlab)]
    exact hlab
  · obtain ⟨p, hp, hlo⟩ := hr.cov k hk1 hk2
    exact ⟨p, bankRepairDigitZeroCoverMono ring root A _ (bankRepairDigitZeroStepSub ring S A e)
      0 r0 A.clock (A.clock + 1) (Nat.le_succ _) ch ch (fun _ h => h) _ p hp, hlo⟩

/-- Firing the head edge covers the head site (if writable) on top of the old covers. -/
theorem bankRepairDigitZeroFireCov {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 lo : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    {h b l : Nat} {ch : List (DigitBaseOrigin n)}
    (hr : BankRepairDigitZeroRun ring root first E r0 lo A h b l ch) :
    ∀ k, first ≤ k → k < h + 1 → ∃ p, DigitCoverProposal ring root
      (digitAuditStep ring S A (digitSite ring root h)) 0 r0 (A.clock + 1) ch
      (digitSite ring root k) p ∧ lo < p.time ∧ p.time ≤ A.clock + 1 := by
  have hn := hF.geom.size
  have hEn := hF.endSize
  have hhE := hr.headEnd
  have hh1 := hr.headPos
  have hret := hF.retired
  have hborn := bankRepairDigitZeroLineageBorn ring root A hr.lin
  have hbl := hr.bornLo
  have hll := hr.lastLe
  intro k hk1 hk2
  rcases Nat.lt_or_ge k h with hkh | hkh
  · obtain ⟨p, hp, hlo⟩ := hr.cov k hk1 hkh
    exact ⟨p, bankRepairDigitZeroCoverMono ring root A _ (bankRepairDigitZeroStepSub ring S A _)
      0 r0 A.clock (A.clock + 1) (Nat.le_succ _) ch ch (fun _ h => h) _ p hp, hlo,
      Nat.le_trans hp.2.2.2.1 (Nat.le_succ _)⟩
  · have hkeq : k = h := by omega
    rw [hkeq] at hk1 ⊢
    obtain ⟨o, rest, hch, hlab⟩ := hr.head
    have hocc := bankRepairDigitZeroOcc hF.toks _ o hlab
    have hzero := (hF.toks.place h (by omega) hocc).2.2.2 hk1
    obtain ⟨born, hb0, hlab'⟩ := hF.toks.label _ hocc
    rw [hlab] at hlab'
    have ho := Option.some.inj hlab'
    have hx := bankRepairDigitSiteNonroot ring root S hF.geom.rootIff h (by omega) (by omega)
    have hy := bankRepairDigitSiteNonroot ring root S hF.geom.rootIff (h + 1) (by omega)
      (by omega)
    obtain ⟨f, hf, hft, hfe, hfb⟩ := bankRepairDigitZeroHead ring S A (digitSite ring root h)
    obtain ⟨_, _, _, _, hbY', _⟩ := bankRepairDigitZeroEdge ring (by omega) S A.current
      (A.clock + 1) (digitSite ring root h) (hF.geom.betaX _) (hF.geom.betaY _)
    rw [hbY'] at hfb
    have hprop := (bankRepairDigitZeroRowFront (A.clock + 1) (digitSite ring root h)
      (ring.rightNeighbor (digitSite ring root h)) (S (digitSite ring root h))
      (S (ring.rightNeighbor (digitSite ring root h))) (S (digitSite ring root h)).word.beta
      (S (ring.rightNeighbor (digitSite ring root h))).word.beta
      (A.current (digitSite ring root h)).base
      (A.current (ring.rightNeighbor (digitSite ring root h))).base hx hy).1 hzero
    refine ⟨DigitZeroProposal.mk (A.clock + 1) (digitSite ring root h)
        (A.current (digitSite ring root h)).base,
      ⟨⟨f, hf, ?_, hft.symm, hfe.symm⟩, rfl, ?_, Nat.le_refl _, born, hb0, ?_, ?_⟩, ?_,
      Nat.le_refl _⟩
    · rw [hfb]
      exact hprop
    · show r0 < A.clock + 1
      omega
    · show (A.current (digitSite ring root h)).base = _
      rw [hlab, ho]
    · rw [hch, ← ho]
      exact List.Mem.head _
    · show lo < A.clock + 1
      omega

/-- Firing the head edge short of the end advances the pass by one site. -/
theorem bankRepairDigitZeroFireRun {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 lo : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    {h b l : Nat} {ch : List (DigitBaseOrigin n)}
    (hr : BankRepairDigitZeroRun ring root first E r0 lo A h b l ch) (hE : h + 1 < E) :
    ∃ l' ch', BankRepairDigitZeroRun ring root first E r0 lo
      (digitAuditStep ring S A (digitSite ring root h)) (h + 1) b l' ch' := by
  have hn := hF.geom.size
  have hEn := hF.endSize
  have hES := hF.endStop
  have hh1 := hr.headPos
  have hll := hr.lastLe
  have hcov := bankRepairDigitZeroFireCov hF hr
  obtain ⟨o, rest, hch, hlab⟩ := hr.head
  have hocc := bankRepairDigitZeroOcc hF.toks _ o hlab
  have hplace := hF.toks.place h (by omega) hocc
  have hx := bankRepairDigitSiteNonroot ring root S hF.geom.rootIff h (by omega) (by omega)
  have hy := bankRepairDigitSiteNonroot ring root S hF.geom.rootIff (h + 1) (by omega)
    (by omega)
  have hmv : (S (digitSite ring root h)).top.wBase = .SEEK ∨
      ((S (digitSite ring root h)).top.wBase = .ZERO ∧
        (S (ring.rightNeighbor (digitSite ring root h))).word.beta = false) := by
    rcases Nat.lt_or_ge h first with hf | hf
    · exact Or.inl (hplace.2.2.1 hf)
    · exact Or.inr ⟨hplace.2.2.2 hf, bankRepairDigitZeroBetaInner ring root R first stop S
        hF.geom.toBankRepairDigitZeroBlock (h + 1) (by omega) (by omega)⟩
  have hfront := bankRepairDigitZeroRowFront (A.clock + 1) (digitSite ring root h)
    (ring.rightNeighbor (digitSite ring root h)) (S (digitSite ring root h))
    (S (ring.rightNeighbor (digitSite ring root h))) (S (digitSite ring root h)).word.beta
    (S (ring.rightNeighbor (digitSite ring root h))).word.beta
    (A.current (digitSite ring root h)).base
    (A.current (ring.rightNeighbor (digitSite ring root h))).base hx hy
  obtain ⟨_, _, _, hgy, hbY', _⟩ := bankRepairDigitZeroEdge ring (by omega) S A.current
    (A.clock + 1) (digitSite ring root h) (hF.geom.betaX _) (hF.geom.betaY _)
  have hsub := bankRepairDigitZeroStepSub ring S A (digitSite ring root h)
  by_cases hyw : (S (ring.rightNeighbor (digitSite ring root h))).top.wBase = .NONE
  · have hnew := (hfront.2.2 hmv hyw).2
    refine ⟨l, ch, bankRepairDigitZeroLineageMono ring root A _ hsub hr.lin,
      Nat.le_trans hr.lastLe (Nat.le_succ _), hr.bornLo, by omega, hE, ⟨o, rest, hch, ?_⟩, ?_⟩
    · show (digitGhostStep ring S A.current (A.clock + 1) (digitSite ring root h)
        (ring.rightNeighbor (digitSite ring root h))).base = some o
      rw [hgy, hnew, hlab]
    · intro k hk1 hk2
      obtain ⟨p, hp, hlo, _⟩ := hcov k hk1 hk2
      exact ⟨p, hp, hlo⟩
  · obtain ⟨born', _, hlab2⟩ := hF.toks.label _ hyw
    have hmerge := hfront.2.1 hmv hyw
    have hkeep := (bankRepairDigitZeroKeepY (A.clock + 1) (digitSite ring root h)
      (ring.rightNeighbor (digitSite ring root h)) (S (digitSite ring root h))
      (S (ring.rightNeighbor (digitSite ring root h))) (S (digitSite ring root h)).word.beta
      (S (ring.rightNeighbor (digitSite ring root h))).word.beta
      (A.current (digitSite ring root h)).base
      (A.current (ring.rightNeighbor (digitSite ring root h))).base hyw).2
    obtain ⟨f, hf, hft, hfe, hfb⟩ := bankRepairDigitZeroHead ring S A (digitSite ring root h)
    rw [hbY'] at hfb
    have hlin : DigitBaseLineage ring root A b (o :: rest) l := by
      rw [← hch]
      exact hr.lin
    have hlin' := bankRepairDigitZeroLineageMono ring root A _ hsub hlin
    refine ⟨f.time, .rootLaunch born' root (ring.rightNeighbor root) :: o :: rest,
      DigitBaseLineage.transfer hlin' f
        (DigitBaseMerge.mk (A.clock + 1) (digitSite ring root h)
          (ring.rightNeighbor (digitSite ring root h)) (A.current (digitSite ring root h)).base
          (A.current (ring.rightNeighbor (digitSite ring root h))).base)
        (.rootLaunch born' root (ring.rightNeighbor root)) hf
        (by rw [hfb]; exact hmerge) (by rw [hft]; omega) hft.symm hlab hlab2,
      by rw [hft]; exact Nat.le_refl _, hr.bornLo, by omega, hE, ⟨_, _, rfl, ?_⟩, ?_⟩
    · show (digitGhostStep ring S A.current (A.clock + 1) (digitSite ring root h)
        (ring.rightNeighbor (digitSite ring root h))).base = _
      rw [hgy, hkeep, hlab2]
    · intro k hk1 hk2
      obtain ⟨p, hp, hlo, _⟩ := hcov k hk1 hk2
      refine ⟨p, bankRepairDigitZeroCoverMono ring root _ _ (fun _ h => h) 0 r0 (A.clock + 1)
        (A.clock + 1) (Nat.le_refl _) ch _ (fun x hx => ?_) _ p hp, hlo⟩
      rw [hch] at hx
      exact List.Mem.tail _ hx

/-- Firing the head edge at the end completes the pass. -/
theorem bankRepairDigitZeroFireDone {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 lo : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    {h b l : Nat} {ch : List (DigitBaseOrigin n)}
    (hr : BankRepairDigitZeroRun ring root first E r0 lo A h b l ch) (hE : h + 1 = E) :
    BankRepairDigitZeroDone ring root first E r0 lo
      (digitAuditStep ring S A (digitSite ring root h)) b l (A.clock + 1) ch := by
  have hcov := bankRepairDigitZeroFireCov hF hr
  have hborn := bankRepairDigitZeroLineageBorn ring root A hr.lin
  have hll := hr.lastLe
  exact ⟨bankRepairDigitZeroLineageMono ring root A _ (bankRepairDigitZeroStepSub ring S A _)
      hr.lin, Nat.le_trans hr.lastLe (Nat.le_succ _), hr.bornLo, by omega, Nat.le_refl _,
    fun k hk1 hk2 => hcov k hk1 (by omega)⟩

/-- A complete pass stays complete. -/
theorem bankRepairDigitZeroDoneStep {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {first E r0 lo : Nat} (S : Fin n → ProjD c) {A : DigitAudit c n}
    {b l st : Nat} {ch : List (DigitBaseOrigin n)}
    (hd : BankRepairDigitZeroDone ring root first E r0 lo A b l st ch) (e : Fin n) :
    BankRepairDigitZeroDone ring root first E r0 lo (digitAuditStep ring S A e) b l st ch := by
  refine ⟨bankRepairDigitZeroLineageMono ring root A _ (bankRepairDigitZeroStepSub ring S A e)
      hd.lin, Nat.le_trans hd.lastLe (Nat.le_succ _), hd.bornLo, hd.bornStamp,
    Nat.le_trans hd.stampLe (Nat.le_succ _), fun k hk1 hk2 => ?_⟩
  obtain ⟨p, hp, h1, h2⟩ := hd.cov k hk1 hk2
  exact ⟨p, bankRepairDigitZeroCoverMono ring root A _ (bankRepairDigitZeroStepSub ring S A e)
    0 r0 A.clock (A.clock + 1) (Nat.le_succ _) ch ch (fun _ h => h) _ p hp, h1, h2⟩

/-! ### Phases -/

/-- The five phases of the two passes. -/
inductive BankRepairDigitZeroPhase (n : Nat) where
  | pendOne
  | runOne (h born last : Nat) (chain : List (DigitBaseOrigin n))
  | pendTwo (born last stamp : Nat) (chain : List (DigitBaseOrigin n))
  | runTwo (born last stamp : Nat) (chain : List (DigitBaseOrigin n)) (h born' last' : Nat)
      (chain' : List (DigitBaseOrigin n))
  | done (born last stamp : Nat) (chain : List (DigitBaseOrigin n)) (born' last' stamp' : Nat)
      (chain' : List (DigitBaseOrigin n))

def BankRepairDigitZeroValid {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (first E r0 : Nat) (A : DigitAudit c n) : BankRepairDigitZeroPhase n → Prop
  | .pendOne => True
  | .runOne h b l ch => BankRepairDigitZeroRun ring root first E r0 r0 A h b l ch
  | .pendTwo b l st ch => BankRepairDigitZeroDone ring root first E r0 r0 A b l st ch
  | .runTwo b l st ch h b' l' ch' =>
      BankRepairDigitZeroDone ring root first E r0 r0 A b l st ch ∧
        BankRepairDigitZeroRun ring root first E r0 st A h b' l' ch'
  | .done b l st ch b' l' st' ch' =>
      BankRepairDigitZeroDone ring root first E r0 r0 A b l st ch ∧
        BankRepairDigitZeroDone ring root first E r0 st A b' l' st' ch'

def bankRepairDigitZeroCost {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (E : Nat) (S : Fin n → ProjD c) : BankRepairDigitZeroPhase n → Nat
  | .pendOne => bankRepairDigitZeroPend ring root E S + (E + 1)
  | .runOne h _ _ _ => (E - h) + (E + 1)
  | .pendTwo _ _ _ _ => bankRepairDigitZeroPend ring root E S
  | .runTwo _ _ _ _ h _ _ _ => E - h
  | .done _ _ _ _ _ _ _ _ => 0

def bankRepairDigitZeroAim {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) : BankRepairDigitZeroPhase n → Fin n
  | .pendOne => bankRepairDigitZeroPendAim ring root S
  | .runOne h _ _ _ => digitSite ring root h
  | .pendTwo _ _ _ _ => bankRepairDigitZeroPendAim ring root S
  | .runTwo _ _ _ _ h _ _ _ => digitSite ring root h
  | .done _ _ _ _ _ _ _ _ => root

/-- One edge: a valid phase record at no higher cost, strictly lower on the nominated edge. -/
theorem bankRepairDigitZeroPhaseStep {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    (d : BankRepairDigitZeroPhase n) (hd : BankRepairDigitZeroValid ring root first E r0 A d)
    (e : Fin n) :
    ∃ d', BankRepairDigitZeroValid ring root first E r0 (digitAuditStep ring S A e) d' ∧
      bankRepairDigitZeroCost ring root E (phiD ring S e) d' ≤
        bankRepairDigitZeroCost ring root E S d ∧
      (e = bankRepairDigitZeroAim ring root S d → 0 < bankRepairDigitZeroCost ring root E S d →
        bankRepairDigitZeroCost ring root E (phiD ring S e) d' + 1 ≤
          bankRepairDigitZeroCost ring root E S d) := by
  have hE2 := hF.endTwo
  have hpl := bankRepairDigitZeroPendLe ring root E (phiD ring S e)
  have hpg := bankRepairDigitZeroPendGe ring root E S
  cases d with
  | pendOne =>
      by_cases hl : e = root ∧ (S (digitSite ring root 1)).top.wBase = .NONE
      · obtain ⟨he, h1⟩ := hl
        rw [he]
        have hp := bankRepairDigitZeroPendNone ring root E S h1
        refine ⟨.runOne 1 (A.clock + 1) (A.clock + 1)
            [.rootLaunch (A.clock + 1) root (ring.rightNeighbor root)],
          bankRepairDigitZeroLaunch hF h1 hF.retired, ?_, fun _ _ => ?_⟩
        · show E - 1 + (E + 1) ≤ bankRepairDigitZeroPend ring root E S + (E + 1)
          omega
        · show E - 1 + (E + 1) + 1 ≤ bankRepairDigitZeroPend ring root E S + (E + 1)
          omega
      · refine ⟨.pendOne, True.intro, ?_, fun ha _ => ?_⟩
        · show bankRepairDigitZeroPend ring root E (phiD ring S e) + (E + 1) ≤
            bankRepairDigitZeroPend ring root E S + (E + 1)
          have := bankRepairDigitZeroPendStep hF e hl
          omega
        · show bankRepairDigitZeroPend ring root E (phiD ring S e) + (E + 1) + 1 ≤
            bankRepairDigitZeroPend ring root E S + (E + 1)
          have := bankRepairDigitZeroPendDrop hF e ha hl
          omega
  | runOne h b l ch =>
      change BankRepairDigitZeroRun ring root first E r0 r0 A h b l ch at hd
      have hhE := hd.headEnd
      by_cases he : e = digitSite ring root h
      · rw [he]
        by_cases hE : h + 1 < E
        · obtain ⟨l', ch', hr'⟩ := bankRepairDigitZeroFireRun hF hd hE
          refine ⟨.runOne (h + 1) b l' ch', hr', ?_, fun _ _ => ?_⟩
          · show E - (h + 1) + (E + 1) ≤ E - h + (E + 1)
            omega
          · show E - (h + 1) + (E + 1) + 1 ≤ E - h + (E + 1)
            omega
        · have hE' : h + 1 = E := by omega
          have hpl' := bankRepairDigitZeroPendLe ring root E (phiD ring S (digitSite ring root h))
          refine ⟨.pendTwo b l (A.clock + 1) ch, bankRepairDigitZeroFireDone hF hd hE', ?_,
            fun _ _ => ?_⟩
          · show bankRepairDigitZeroPend ring root E (phiD ring S (digitSite ring root h)) ≤
              E - h + (E + 1)
            omega
          · show bankRepairDigitZeroPend ring root E (phiD ring S (digitSite ring root h)) + 1 ≤
              E - h + (E + 1)
            omega
      · exact ⟨.runOne h b l ch, bankRepairDigitZeroRunKeep hF hd e he, Nat.le_refl _,
          fun ha _ => absurd ha he⟩
  | pendTwo b l st ch =>
      change BankRepairDigitZeroDone ring root first E r0 r0 A b l st ch at hd
      by_cases hl : e = root ∧ (S (digitSite ring root 1)).top.wBase = .NONE
      · obtain ⟨he, h1⟩ := hl
        rw [he]
        have hp := bankRepairDigitZeroPendNone ring root E S h1
        refine ⟨.runTwo b l st ch 1 (A.clock + 1) (A.clock + 1)
            [.rootLaunch (A.clock + 1) root (ring.rightNeighbor root)],
          ⟨bankRepairDigitZeroDoneStep S hd root, bankRepairDigitZeroLaunch hF h1 hd.stampLe⟩,
          ?_, fun _ _ => ?_⟩
        · show E - 1 ≤ bankRepairDigitZeroPend ring root E S
          omega
        · show E - 1 + 1 ≤ bankRepairDigitZeroPend ring root E S
          omega
      · refine ⟨.pendTwo b l st ch, bankRepairDigitZeroDoneStep S hd e,
          bankRepairDigitZeroPendStep hF e hl, fun ha _ => bankRepairDigitZeroPendDrop hF e ha hl⟩
  | runTwo b l st ch h b' l' ch' =>
      obtain ⟨hd1, hd2⟩ := hd
      have hhE := hd2.headEnd
      by_cases he : e = digitSite ring root h
      · rw [he]
        by_cases hE : h + 1 < E
        · obtain ⟨l'', ch'', hr'⟩ := bankRepairDigitZeroFireRun hF hd2 hE
          refine ⟨.runTwo b l st ch (h + 1) b' l'' ch'',
            ⟨bankRepairDigitZeroDoneStep S hd1 _, hr'⟩, ?_, fun _ _ => ?_⟩
          · show E - (h + 1) ≤ E - h
            omega
          · show E - (h + 1) + 1 ≤ E - h
            omega
        · have hE' : h + 1 = E := by omega
          refine ⟨.done b l st ch b' l' (A.clock + 1) ch',
            ⟨bankRepairDigitZeroDoneStep S hd1 _, bankRepairDigitZeroFireDone hF hd2 hE'⟩, ?_,
            fun _ _ => ?_⟩
          · show 0 ≤ E - h
            omega
          · show 0 + 1 ≤ E - h
            omega
      · exact ⟨.runTwo b l st ch h b' l' ch',
          ⟨bankRepairDigitZeroDoneStep S hd1 e, bankRepairDigitZeroRunKeep hF hd2 e he⟩,
          Nat.le_refl _, fun ha _ => absurd ha he⟩
  | done b l st ch b' l' st' ch' =>
      obtain ⟨hd1, hd2⟩ := hd
      exact ⟨.done b l st ch b' l' st' ch',
        ⟨bankRepairDigitZeroDoneStep S hd1 e, bankRepairDigitZeroDoneStep S hd2 e⟩,
        Nat.le_refl _, fun _ h => absurd h (Nat.lt_irrefl 0)⟩

/-- Two complete passes are the two base covers. -/
theorem bankRepairDigitZeroTarget {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    {b l st b' l' st' : Nat} {ch ch' : List (DigitBaseOrigin n)}
    (h1 : BankRepairDigitZeroDone ring root first E r0 r0 A b l st ch)
    (h2 : BankRepairDigitZeroDone ring root first E r0 st A b' l' st' ch') :
    DigitTwoBaseCovers ring root A 0 r0 A.clock := by
  refine ⟨hF.extinct, hF.retired, Nat.le_refl _,
    Or.inr ⟨b, b', l, l', ch, ch', ?_, ?_, h1.lin, h2.lin, h1.lastLe, h2.lastLe, ?_⟩⟩
  · have := h1.bornLo
    omega
  · have := h1.bornStamp
    have := h2.bornLo
    omega
  · intro i hi
    obtain ⟨first', stop', k, hseg, hk1, hk2, hk3, rfl⟩ := hi
    obtain ⟨hf1, hs1⟩ := bankRepairDigitZeroSegmentEq ring root R first stop A.start hF.start
      first' stop' hseg
    rw [hf1] at hk1
    rw [hs1] at hk2
    have hkE := hF.endWrit k hk2 hk3
    obtain ⟨p1, hp1, _, ht1⟩ := h1.cov k hk1 hkE
    obtain ⟨p2, hp2, ht2, _⟩ := h2.cov k hk1 hkE
    exact ⟨p1, p2, hp1, hp2, by omega⟩

/-- Cost zero only at the target. -/
theorem bankRepairDigitZeroCostZero {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    (d : BankRepairDigitZeroPhase n) (hd : BankRepairDigitZeroValid ring root first E r0 A d)
    (h0 : bankRepairDigitZeroCost ring root E S d = 0) :
    DigitTwoBaseCovers ring root A 0 r0 A.clock := by
  have hpg := bankRepairDigitZeroPendGe ring root E S
  have hE2 := hF.endTwo
  cases d with
  | pendOne =>
      change bankRepairDigitZeroPend ring root E S + (E + 1) = 0 at h0
      omega
  | runOne h b l ch =>
      change E - h + (E + 1) = 0 at h0
      omega
  | pendTwo b l st ch =>
      change bankRepairDigitZeroPend ring root E S = 0 at h0
      omega
  | runTwo b l st ch h b' l' ch' =>
      obtain ⟨_, hd2⟩ := hd
      have := hd2.headEnd
      change E - h = 0 at h0
      omega
  | done b l st ch b' l' st' ch' =>
      obtain ⟨hd1, hd2⟩ := hd
      exact bankRepairDigitZeroTarget hF hd1 hd2

/-! ### The rank -/

theorem bankRepairDigitZeroLeastOf (Q : Nat → Prop) (h : ∃ m, Q m) :
    ∃ k, Q k ∧ ∀ j, Q j → k ≤ j := by
  classical
  obtain ⟨m, hm⟩ := h
  have key : ∀ N, ∀ m, m ≤ N → Q m → ∃ k, Q k ∧ ∀ j, Q j → k ≤ j := by
    intro N
    induction N with
    | zero =>
        intro m hm hq
        have h0 : m = 0 := by omega
        rw [h0] at hq
        exact ⟨0, hq, fun j _ => Nat.zero_le j⟩
    | succ N ih =>
        intro m hm hq
        by_cases hex : ∃ j, j ≤ N ∧ Q j
        · obtain ⟨j, hj, hqj⟩ := hex
          exact ih j hj hqj
        · refine ⟨m, hq, fun j hqj => ?_⟩
          rcases Nat.lt_or_ge j m with hjm | hjm
          · exact absurd ⟨j, by omega, hqj⟩ hex
          · exact hjm
  exact key m m (Nat.le_refl _) hm

/-- Some valid phase record costs at most `m`. -/
def BankRepairDigitZeroBound {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (first E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) (m : Nat) : Prop :=
  ∃ d, BankRepairDigitZeroValid ring root first E r0 A d ∧
    bankRepairDigitZeroCost ring root E S d ≤ m

theorem bankRepairDigitZeroBoundEx {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) :
    ∃ m, BankRepairDigitZeroBound ring root first E r0 S A m :=
  ⟨_, .pendOne, True.intro, Nat.le_refl _⟩

/-- The first-zero rank: the least cost of a valid phase record. -/
noncomputable def bankRepairDigitZeroRank {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) : Nat :=
  Classical.choose (bankRepairDigitZeroLeastOf _ (bankRepairDigitZeroBoundEx ring root first E r0 S A))

theorem bankRepairDigitZeroRankLe {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (d : BankRepairDigitZeroPhase n) (hd : BankRepairDigitZeroValid ring root first E r0 A d) :
    bankRepairDigitZeroRank ring root first E r0 S A ≤ bankRepairDigitZeroCost ring root E S d := by
  unfold bankRepairDigitZeroRank
  exact (Classical.choose_spec (bankRepairDigitZeroLeastOf _
    (bankRepairDigitZeroBoundEx ring root first E r0 S A))).2 _ ⟨d, hd, Nat.le_refl _⟩

theorem bankRepairDigitZeroRankAch {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) :
    ∃ d, BankRepairDigitZeroValid ring root first E r0 A d ∧
      bankRepairDigitZeroCost ring root E S d ≤ bankRepairDigitZeroRank ring root first E r0 S A := by
  unfold bankRepairDigitZeroRank
  exact (Classical.choose_spec (bankRepairDigitZeroLeastOf _
    (bankRepairDigitZeroBoundEx ring root first E r0 S A))).1

/-- No edge raises the rank. -/
theorem bankRepairDigitZeroRankStep {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A) (e : Fin n) :
    bankRepairDigitZeroRank ring root first E r0 (phiD ring S e) (digitAuditStep ring S A e) ≤
      bankRepairDigitZeroRank ring root first E r0 S A := by
  obtain ⟨d0, hd0, hc0⟩ := bankRepairDigitZeroRankAch ring root first E r0 S A
  obtain ⟨d', hd', hc', _⟩ := bankRepairDigitZeroPhaseStep hF d0 hd0 e
  exact Nat.le_trans (bankRepairDigitZeroRankLe ring root first E r0 _ _ d' hd')
    (Nat.le_trans hc' hc0)

/-- Off the target some edge lowers the rank. -/
theorem bankRepairDigitZeroRankDrop {c : Compiled} {n : Nat} {ring : DirectedRing n}
    {root : Fin n} {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    (hnt : ¬ DigitTwoBaseCovers ring root A 0 r0 A.clock) :
    ∃ e : Fin n, bankRepairDigitZeroRank ring root first E r0 (phiD ring S e)
        (digitAuditStep ring S A e) + 1 ≤ bankRepairDigitZeroRank ring root first E r0 S A := by
  obtain ⟨d0, hd0, hc0⟩ := bankRepairDigitZeroRankAch ring root first E r0 S A
  have hpos : 0 < bankRepairDigitZeroCost ring root E S d0 := by
    rcases Nat.eq_zero_or_pos (bankRepairDigitZeroCost ring root E S d0) with h | h
    · exact absurd (bankRepairDigitZeroCostZero hF d0 hd0 h) hnt
    · exact h
  obtain ⟨d', hd', _, hdrop⟩ :=
    bankRepairDigitZeroPhaseStep hF d0 hd0 (bankRepairDigitZeroAim ring root S d0)
  exact ⟨_, Nat.le_trans (Nat.add_le_add_right
    (bankRepairDigitZeroRankLe ring root first E r0 _ _ d' hd') 1)
    (Nat.le_trans (hdrop rfl hpos) hc0)⟩

/-- The rank never exceeds two full passes. -/
theorem bankRepairDigitZeroRankUpper {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first E r0 : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) :
    bankRepairDigitZeroRank ring root first E r0 S A ≤ 2 * E + 2 := by
  have h := bankRepairDigitZeroRankLe ring root first E r0 S A .pendOne True.intro
  have hp := bankRepairDigitZeroPendLe ring root E S
  change bankRepairDigitZeroRank ring root first E r0 S A ≤
    bankRepairDigitZeroPend ring root E S + (E + 1) at h
  omega

end L3.RenewalReferenceClock
