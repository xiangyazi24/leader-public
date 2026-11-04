import Leader.L3.Bank.RepairDigitFinalFlush

/-!
# T19: the first-zero stage, row layer

The base token of the literal top row (`liveTopPair`, `digitBaseReplay`) on the projected ring:

* every service clears its source site's base token;
* a destination site either keeps its token and label, receives a fresh root launch, or receives
  the source's token and label (a ZERO into a non-border site, or a SEEK, which turns ZERO on a
  border);
* the audit's frames only grow, so lineages, proposals and `DigitAt` endpoints persist.

Two run invariants: `bankRepairDigitZeroSound` (after retirement every token carries a root
launch label) and `bankRepairDigitZeroLaunchLayout` (a root-launched SEEK sits in the leading
prefix, a root-launched ZERO in the first segment).
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ### Stage composition (a public copy of the half-unit reserve) -/

theorem bankRepairDigitZeroReserve {S : Type} {n : Nat}
    (next : S → Fin n → S) (A P : S → Prop) (allowance : Nat)
    (hsecond : ∀ y, A y → ∀ T,
      2 * costNumerator next P y T ≤ n ^ T * allowance) :
    ∀ y T,
      2 * costNumerator next P y T ≤
        2 * costNumerator next (fun z => A z ∨ P z) y T +
          n ^ T * allowance := by
  classical
  intro y T
  induction T generalizing y with
  | zero =>
      simp only [costNumerator_zero, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hp : P y
      · have hu : A y ∨ P y := Or.inr hp
        rw [costNumerator_terminal next P y hp (T + 1),
          costNumerator_terminal next (fun z => A z ∨ P z)
            y hu (T + 1)]
        simp only [Nat.mul_zero, Nat.zero_add]
        exact Nat.zero_le _
      · by_cases ha : A y
        · have hu : A y ∨ P y := Or.inl ha
          rw [costNumerator_terminal next (fun z => A z ∨ P z)
            y hu (T + 1)]
          simpa only [Nat.mul_zero, Nat.zero_add] using
            hsecond y ha (T + 1)
        · have hu : ¬ (A y ∨ P y) := by
            intro h
            rcases h with hA | hP
            · exact ha hA
            · exact hp hP
          have hs :
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next (fun z => A z ∨ P z)
                  (next y e) T)).sum +
                n ^ (T + 1) * allowance := by
            calc
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum =
                  (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next P (next y e) T)).sum := by
                    rw [ofFn_sum_mul_left]
              _ ≤ (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next
                      (fun z => A z ∨ P z) (next y e) T +
                        n ^ T * allowance)).sum :=
                    ofFn_sum_le _ _ (fun e => ih (next y e))
              _ = 2 * (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum +
                      n ^ (T + 1) * allowance := by
                    rw [ofFn_sum_add, ofFn_sum_const,
                      ofFn_sum_mul_left, Nat.pow_succ]
                    ac_rfl
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z) y hu T]
          omega

theorem bankRepairDigitZeroCompose {S : Type} {n : Nat}
    (next : S → Fin n → S) (A B Target : S → Prop) (a b : Nat)
    (hfirst : BankRepairDigitChargedStage next A B a)
    (hsecond : BankRepairDigitChargedStage next B Target b) :
    BankRepairDigitChargedStage next A Target (a + b) := by
  intro x hx T
  have hfirstUnion :
      2 * costNumerator next (fun z => B z ∨ Target z) x T ≤ n ^ T * a := by
    have hmono := L3.Prob.costNumerator_target_mono next B
      (fun z => B z ∨ Target z) (fun z hz => Or.inl hz) x T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono) (hfirst x hx T)
  have hreserve := bankRepairDigitZeroReserve next B Target b
    (fun y hy U => hsecond y hy U) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T + n ^ T * b := hreserve
    _ ≤ n ^ T * a + n ^ T * b := Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * (a + b) := by rw [Nat.mul_add]

/-! ### Literal base rows -/

/-- Every service clears the source site's base token. -/
theorem bankRepairDigitZeroRowX (c : Compiled) (ox oy : Agent c) (bx bY : Bool) :
    (liveTopPair c ox oy bx bY).x.wBase = .NONE := by
  rw [bankRepairDigitLiveTopWBaseX]
  cases ox.l <;> cases oy.l <;> cases hw : ox.wBase <;> simp

theorem bankRepairDigitZeroReplayX {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : ProjD c) (bY : Bool) (gx gy : Option (DigitBaseOrigin n)) :
    (digitBaseReplay time src dst x y bY gx gy).x = none ∨
      (x.top.wBase = .NONE ∧ (digitBaseReplay time src dst x y bY gx gy).x = gx) := by
  unfold digitBaseReplay
  cases x.word.native.l <;> cases y.word.native.l <;> cases hw : x.top.wBase <;> simp

/-- The destination site: kept, launched, or fed by the source token. -/
theorem bankRepairDigitZeroRowY {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : ProjD c) (bX bY : Bool) (gx gy : Option (DigitBaseOrigin n)) :
    ((liveTopPair c x.lift y.lift bX bY).y.wBase = y.top.wBase ∧
        (digitBaseReplay time src dst x y bY gx gy).y = gy) ∨
    (x.word.native.l = true ∧ y.word.native.l = false ∧ y.top.wBase = .NONE ∧
        (liveTopPair c x.lift y.lift bX bY).y.wBase = .SEEK ∧
        (digitBaseReplay time src dst x y bY gx gy).y = some (.rootLaunch time src dst)) ∨
    (x.word.native.l = false ∧ y.word.native.l = false ∧ x.top.wBase = .ZERO ∧ bY = false ∧
        y.top.wBase = .NONE ∧ (liveTopPair c x.lift y.lift bX bY).y.wBase = .ZERO ∧
        (digitBaseReplay time src dst x y bY gx gy).y = gx) ∨
    (x.word.native.l = false ∧ y.word.native.l = false ∧ x.top.wBase = .SEEK ∧
        y.top.wBase = .NONE ∧
        (liveTopPair c x.lift y.lift bX bY).y.wBase = (if bY then .ZERO else .SEEK) ∧
        (digitBaseReplay time src dst x y bY gx gy).y = gx) := by
  rw [bankRepairDigitLiveTopWBaseY]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw]
  unfold digitBaseReplay
  cases x.word.native.l <;> cases y.word.native.l <;> cases x.top.wBase <;>
    cases y.top.wBase <;> cases bY <;> simp

theorem bankRepairDigitZeroKeepY {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : ProjD c) (bX bY : Bool) (gx gy : Option (DigitBaseOrigin n))
    (h : y.top.wBase ≠ .NONE) :
    (liveTopPair c x.lift y.lift bX bY).y.wBase = y.top.wBase ∧
      (digitBaseReplay time src dst x y bY gx gy).y = gy := by
  rcases bankRepairDigitZeroRowY time src dst x y bX bY gx gy with
    h1 | ⟨_, _, h2, _⟩ | ⟨_, _, _, _, h2, _⟩ | ⟨_, _, _, h2, _⟩
  · exact h1
  all_goals exact absurd h2 h

/-- The root launch into an empty successor. -/
theorem bankRepairDigitZeroRowLaunch {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : ProjD c) (bX bY : Bool) (gx gy : Option (DigitBaseOrigin n))
    (hx : x.word.native.l = true) (hy : y.word.native.l = false) (hw : y.top.wBase = .NONE) :
    (liveTopPair c x.lift y.lift bX bY).y.wBase = .SEEK ∧
      (digitBaseReplay time src dst x y bY gx gy).y = some (.rootLaunch time src dst) := by
  rw [bankRepairDigitLiveTopWBaseY]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw' : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw']
  unfold digitBaseReplay
  simp [hx, hy, hw]

/-- A travelling token: its proposal, its merge, and its move. -/
theorem bankRepairDigitZeroRowFront {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : ProjD c) (bX bY : Bool) (gx gy : Option (DigitBaseOrigin n))
    (hx : x.word.native.l = false) (hy : y.word.native.l = false) :
    (x.top.wBase = .ZERO →
      (digitBaseReplay time src dst x y bY gx gy).proposal =
        some (DigitZeroProposal.mk time src gx)) ∧
    ((x.top.wBase = .SEEK ∨ (x.top.wBase = .ZERO ∧ bY = false)) → y.top.wBase ≠ .NONE →
      (digitBaseReplay time src dst x y bY gx gy).merge =
        some (DigitBaseMerge.mk time src dst gx gy)) ∧
    ((x.top.wBase = .SEEK ∨ (x.top.wBase = .ZERO ∧ bY = false)) → y.top.wBase = .NONE →
      (liveTopPair c x.lift y.lift bX bY).y.wBase ≠ .NONE ∧
        (digitBaseReplay time src dst x y bY gx gy).y = gx) := by
  rw [bankRepairDigitLiveTopWBaseY]
  have hl : ∀ a : ProjD c, a.lift.l = a.word.native.l := fun _ => rfl
  have hw' : ∀ a : ProjD c, a.lift.wBase = a.top.wBase := fun _ => rfl
  simp only [hl, hw']
  unfold digitBaseReplay
  cases hwx : x.top.wBase <;> cases hwy : y.top.wBase <;> cases bY <;> simp [hx, hy]

/-! ### One projected service -/

theorem bankRepairDigitZeroServiceBase {c : Compiled} {n : Nat} (time : Nat) (e j : Fin n)
    (x y : ProjD c) (gx gy : DigitGhost c n) :
    (digitService time e j x y gx gy).base =
      digitBaseReplay time e j x y (workerW x.word y.word).betaY gx.base gy.base := rfl

/-- The base coordinates after one service on the projected ring. -/
theorem bankRepairDigitZeroEdge {c : Compiled} {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) (time : Nat) (e : Fin n)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
      (S (ring.rightNeighbor e)).word.beta) :
    (phiD ring S e e).top.wBase = .NONE ∧
    (phiD ring S e (ring.rightNeighbor e)).top.wBase =
      (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift (S e).word.beta
        (S (ring.rightNeighbor e)).word.beta).y.wBase ∧
    (digitGhostStep ring S G time e e).base =
      (digitBaseReplay time e (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
        (S (ring.rightNeighbor e)).word.beta (G e).base (G (ring.rightNeighbor e)).base).x ∧
    (digitGhostStep ring S G time e (ring.rightNeighbor e)).base =
      (digitBaseReplay time e (ring.rightNeighbor e) (S e) (S (ring.rightNeighbor e))
        (S (ring.rightNeighbor e)).word.beta (G e).base (G (ring.rightNeighbor e)).base).y ∧
    (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY =
      (S (ring.rightNeighbor e)).word.beta ∧
    ∀ i, i ≠ e → i ≠ ring.rightNeighbor e →
      phiD ring S e i = S i ∧ digitGhostStep ring S G time e i = G i := by
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring hn e
  obtain ⟨h1, h2, h3, _⟩ := bankRepairDigitPhiDAt ring hn S e hbX hbY
  have hbY' : (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY =
      (S (ring.rightNeighbor e)).word.beta := hbY
  refine ⟨?_, ?_, ?_, ?_, hbY', fun i hi hj => ⟨h3 i hi hj, ?_⟩⟩
  · rw [h1]
    exact bankRepairDigitZeroRowX c _ _ _ _
  · rw [h2]
    rfl
  · simp only [digitGhostStep, if_pos rfl, digitService, hbY']
  · simp only [digitGhostStep, if_neg hne, if_pos rfl, ↓reduceIte, digitService, hbY']
  · simp only [digitGhostStep, if_neg hi, if_neg hj]

/-! ### Frames only grow -/

theorem bankRepairDigitZeroLineageMono {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (A A' : DigitAudit c n)
    (hsub : ∀ f, f ∈ A.frames → f ∈ A'.frames) {b : Nat} {ch : List (DigitBaseOrigin n)}
    {l : Nat} (h : DigitBaseLineage ring root A b ch l) :
    DigitBaseLineage ring root A' b ch l := by
  induction h
  · rename_i hl
    obtain ⟨f, hf, h1, h2, h3⟩ := hl
    exact .launch _ ⟨f, hsub f hf, h1, h2, h3⟩
  · rename_i f merge survivor hf hm ht hclock hin hout ih
    exact .transfer ih f merge survivor (hsub f hf) hm ht hclock hin hout

theorem bankRepairDigitZeroLineageBorn {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (A : DigitAudit c n) {b : Nat} {ch : List (DigitBaseOrigin n)}
    {l : Nat} (h : DigitBaseLineage ring root A b ch l) : b ≤ l := by
  induction h
  · exact Nat.le_refl _
  · rename_i _ _ _ _ _ ht _ _ _ ih
    omega

theorem bankRepairDigitZeroCoverMono {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (A A' : DigitAudit c n)
    (hsub : ∀ f, f ∈ A.frames → f ∈ A'.frames) (boundary retired cut cut' : Nat)
    (hcut : cut ≤ cut') (ch ch' : List (DigitBaseOrigin n))
    (hch : ∀ o, o ∈ ch → o ∈ ch') (site : Fin n) (p : DigitZeroProposal n)
    (h : DigitCoverProposal ring root A boundary retired cut ch site p) :
    DigitCoverProposal ring root A' boundary retired cut' ch' site p := by
  obtain ⟨⟨f, hf, h1, h2, h3⟩, hs, hr, hc, born, hb, ho, hm⟩ := h
  exact ⟨⟨f, hsub f hf, h1, h2, h3⟩, hs, hr, Nat.le_trans hc hcut, born, hb, ho, hch _ hm⟩

theorem bankRepairDigitZeroAtMono {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (A A' : DigitAudit c n) (hstart : A'.start = A.start)
    (hsub : ∀ f, f ∈ A.frames → f ∈ A'.frames) (cut : Nat) (S : Fin n → ProjD c)
    (G : Fin n → DigitGhost c n) (h : DigitAt ring A cut S G) : DigitAt ring A' cut S G := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨f, hf, rest⟩
  · exact Or.inl ⟨h0, by rw [hstart]; exact h1, by rw [hstart]; exact h2⟩
  · exact Or.inr ⟨f, hsub f hf, rest⟩

theorem bankRepairDigitZeroExtinctMono {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (A A' : DigitAudit c n) (hstart : A'.start = A.start)
    (hsub : ∀ f, f ∈ A.frames → f ∈ A'.frames) (boundary retired : Nat)
    (h : DigitBaseExtinct ring root A boundary retired) :
    DigitBaseExtinct ring root A' boundary retired := by
  obtain ⟨hle, S, G, hat, hs⟩ := h
  exact ⟨hle, S, G, bankRepairDigitZeroAtMono ring A A' hstart hsub retired S G hat, hs⟩

theorem bankRepairDigitZeroStepSub {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∀ f, f ∈ A.frames → f ∈ (digitAuditStep ring S A e).frames :=
  fun _ hf => List.mem_cons_of_mem _ hf

end L3.RenewalReferenceClock
