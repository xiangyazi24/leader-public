import Leader.Wu.Authorization.CheckReadyStep
import Leader.Wu.Authorization.PostCleanHole

/-!
Original-row unsupported lock/compare1 successor.

Satisfiable raw entrance: ψ=3, j=0, own labels/paths 0 and 1,
left lineage-depart, right lock or compare1, common path mark,
empty tokens and follower/reset-free endpoints. This is not a
generator-reachability claim.

Only the advertised raw afterCleanToFinal_pairHole is consumed from
PostCleanHole; its pipeline convenience wrapper is not used. The two
factorizations below are reproved by definitional equality.
-/

namespace PPLLAuthCheckUnsupportedWave

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
open PPLLAuthGenDrain PPLLAuthResetDrain PPLLAuthCheckComponentStep

set_option autoImplicit false
variable {ψ : Nat}

/-- Original entrance. In particular, there is no right-control or carry pin. -/
structure Boundary (l r : AuthState ψ) (j bl br : Nat) (γ : ProvColor) : Prop where
  lk : l.core.label.val = j
  rk : r.core.label.val = j + 1
  interior : j + 2 < ψ
  lp : l.core.path = .some j bl
  rp : r.core.path = .some (j + 1) br
  ls : l.core.state = .depart
  rs : r.core.state = .lock ∨ r.core.state = .compare1
  lt : l.core.path2 = none
  rt : r.core.path2 = none
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false
  lpm : l.path_mark = γ
  rpm : r.path_mark = γ
  cm : l.ctrl_mark = l.path_mark

variable (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
variable {j bl br : Nat} {γ : ProvColor}

private theorem probe_row (h : Boundary l r j bl br γ) :
    Boundary (P0 hp l r).1 (P0 hp l r).2 j bl br γ := by
  have hn : r.core.label.val = (l.core.label.val + 1) % ψ := by
    rw [h.rk, h.lk]
    have hi : j + 1 < ψ := by have := h.interior; omega
    exact (Nat.mod_eq_of_lt hi).symm
  obtain ⟨x, y, he⟩ := P0_frame hp l r h.ll h.rl hn
  rw [he]
  exact ⟨h.lk, h.rk, h.interior, h.lp, h.rp, h.ls, h.rs,
    h.lt, h.rt, h.ll, h.rl, h.lr, h.rr, h.lpm, h.rpm, h.cm⟩

private theorem wait_row (h : Boundary l r j bl br γ) :
    Boundary (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 j bl br γ := by
  have hw := W_fields hp κ l r
  have hd : av (lift2 (waitSaturated hp κ) l r).1 = av l ∧
      av (lift2 (waitSaturated hp κ) l r).2 = av r :=
    wait_dv hp κ l.core r.core
  generalize lift2 (waitSaturated hp κ) l r = q at hw hd ⊢
  rcases hw with ⟨sL, pL, tL, kL, fL, cL, mL,
    sR, pR, tR, kR, fR, cR, mR⟩
  simp only [av, dv, Prod.mk.injEq] at hd
  rcases hd with ⟨⟨rL, _, _, _⟩, ⟨rR, _, _, _⟩⟩
  refine ⟨(congrArg (fun k : Fin ψ => k.val) kL).trans h.lk,
    (congrArg (fun k : Fin ψ => k.val) kR).trans h.rk,
    h.interior, pL.trans h.lp, pR.trans h.rp, sL.trans h.ls, ?_,
    tL.trans h.lt, tR.trans h.rt, fL.trans h.ll, fR.trans h.rl,
    rL.trans h.lr, rR.trans h.rr, mL.trans h.lpm, mR.trans h.rpm,
    cL.trans (h.cm.trans mL.symm)⟩
  rcases h.rs with hs | hs
  · exact Or.inl (sR.trans hs)
  · exact Or.inr (sR.trans hs)

private theorem gen_row (h : Boundary l r j bl br γ) :
    Boundary (genSigAuth hp κ l r).1 (genSigAuth hp κ l r).2 j bl br γ := by
  have hw := wait_row hp κ l r h
  unfold genSigAuth
  -- Abstract WAIT in the outer goal, not just inside a local equality.
  generalize lift2 (waitSaturated hp κ) l r = q at hw ⊢
  rcases q with ⟨a, b⟩
  dsimp only at hw ⊢
  change Boundary (gsBody hp a b).1 (gsBody hp a b).2 j bl br γ
  have he : gsBody hp a b = (a, b) := by
    rcases hw.rs with hs | hs <;>
      simp [gsBody, gsH, gsR, gsE, gsPair, gsF,
        AuthState.st, hw.lp, hw.ls, hs]
  rw [he]
  exact hw

private theorem clean_row (h : Boundary l r j bl br γ) :
    let q := T1 hp cfg (l, r)
    PairHole q ∨ Boundary q.1 q.2 j bl br γ := by
  have hv := T1_cv hp cfg (l, r)
  have ha := T1_pa hp cfg (l, r)
  dsimp only
  generalize T1 hp cfg (l, r) = q at hv ha ⊢
  rcases hv with ⟨vL, vR, pL, pR⟩
  rcases pL with pL | pL
  · rcases pR with pR | pR
    · right
      simp only [cv, Prod.mk.injEq] at vL vR
      simp only [PA, av, dv, Prod.mk.injEq] at ha
      rcases vL with ⟨sL, _, cL, tL, mL⟩
      rcases vR with ⟨sR, _, _, tR, mR⟩
      rcases ha with ⟨⟨rL, _, kL, fL⟩, ⟨rR, _, kR, fR⟩⟩
      refine ⟨(congrArg (fun k : Fin ψ => k.val) kL).trans h.lk,
        (congrArg (fun k : Fin ψ => k.val) kR).trans h.rk,
        h.interior, pL.trans h.lp, pR.trans h.rp, sL.trans h.ls, ?_,
        tL.trans h.lt, tR.trans h.rt, fL.trans h.ll, fR.trans h.rl,
        rL.trans h.lr, rR.trans h.rr, mL.trans h.lpm, mR.trans h.rpm,
        cL.trans (h.cm.trans mL.symm)⟩
      rcases h.rs with hs | hs
      · exact Or.inl (sR.trans hs)
      · exact Or.inr (sR.trans hs)
    · exact Or.inl (Or.inr pR)
  · exact Or.inl (Or.inl pL)

/-- The actual original P0/GENSIG/CLEAN cut, not a restored pair. -/
def cleanCut : AuthState ψ × AuthState ψ :=
  let p := P0 hp l r
  let g := genSigAuth hp κ p.1 p.2
  T1 hp cfg g

theorem cleanCut_hole_or_boundary (h : Boundary l r j bl br γ) :
    let c := cleanCut hp κ l r
    PairHole c ∨ Boundary c.1 c.2 j bl br γ := by
  have hP := probe_row hp l r h
  unfold cleanCut
  generalize P0 hp l r = p at hP ⊢
  dsimp only
  have hG := gen_row hp κ p.1 p.2 hP
  generalize genSigAuth hp κ p.1 p.2 = g at hG ⊢
  exact clean_row hp g.1 g.2 hG

private def afterClean : AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

private theorem move_row (h : Boundary l r j bl br γ) :
    moveSourceAuth hp cfg l r = (l, r) := by
  rcases h.rs with hs | hs <;>
    simp [moveSourceAuth, validateCheck, headBad, checkState, verdict,
      isHead, aligned, sanitizeP2, p2Valid, step1Auth, moveTokensAuth,
      leaderWallAuth, applyControlAuth, AuthState.st, h.lp, h.rp,
      h.lk, h.rk, h.ls, hs, h.lt, h.rt, h.ll, h.rl]

private theorem afterClean_row (h : Boundary l r j bl br γ) :
    afterClean hp l r = (l, r) := by
  have hrel : lift2Life (releaseSource hp) l r = (l, r) := by
    rcases h.rs with hs | hs <;> simp [lift2Life, releaseSource, hs]
  have hel : lift2 (eliminateSig hp) l r = (l, r) := by
    rcases h.rs with hs | hs <;> simp [lift2, eliminateSig, hs]
  unfold afterClean
  rw [hrel]
  dsimp only
  rw [hel]
  dsimp only
  rw [move_row hp l r h]
  dsimp only
  rcases h.rs with hs | hs <;>
    simp [liftLife, dropStale, aligned, preCheckResetAuth, normalizeReady,
      normalizeOrphan, normalizeCarrier, releaseCongest, h.ll, h.rl,
      h.lr, h.rr, h.lp, h.rp, h.lk, h.rk, h.ls, hs]

private theorem check_row (h : Boundary l r j bl br γ) :
    checkSourceAuth hp cfg l r = (l, r) := by
  have hL : checkSigCheckL hp l.core = l.core := by
    cases hj : j <;> simp [checkSigCheckL, h.lp, hj, h.ls]
  rcases h.rs with hs | hs <;>
    simp [checkSourceAuth, validateCheck, headBad, checkState, verdict,
      certPred, isHead, aligned, readyAuth, waveState, checkSigSetReadyGuarded,
      controlPending, checkSigSetReady, hL, issue, AuthState.st,
      AuthState.withCore, h.lp, h.rp, h.lk, h.rk, h.ls, hs, h.lt, h.rt]

/-- All carry valuations are quantified; geometry excludes the state-changing
terminal branch, while p/p_carry updates are deliberately not framed. -/
private theorem disappear_row (h : Boundary l r j bl br γ) :
    Boundary (disappearAuth hp l r).1 (disappearAuth hp l r).2 j bl br γ := by
  have hrt : r.core.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro he
    have hv := congrArg (fun k : Fin ψ => k.val) he
    dsimp only at hv
    rw [h.rk] at hv
    have hi := h.interior
    omega
  rcases h.rs with hs | hs <;>
    cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
    simp [disappearAuth, lift2, disappearStartL, disappearCarry,
      AuthState.st, h.ls, hs, hc, hb, hrt] <;>
    refine ⟨h.lk, h.rk, h.interior, h.lp, h.rp, ?_, ?_,
      h.lt, h.rt, h.ll, h.rl, h.lr, h.rr, h.lpm, h.rpm, h.cm⟩ <;>
    simp [h.ls, hs]

private theorem repair_row (h : Boundary l r j bl br γ) :
    repairAuth l r = (l, r) := by
  rcases h.rs with hs | hs <;>
    simp [repairAuth, liftLife, normalizeOrphan, normalizeCarrier,
      releaseCongest, lift2Life, releaseReadySuffix, ackTailAuth, ackTail,
      lift2, lockedState, AuthState.st, h.ll, h.rl, h.lp, h.rp,
      h.lk, h.rk, h.ls, hs, h.lt, h.rt]

/-- RIGHT-FIRST maintenance: j+1 is nonhead, so depart is not locked support.
The right control mark is unrestricted, including equality with the left. -/
theorem maintain_unsupported (h : Boundary l r j bl br γ) :
    maintainAuth l r = (l, r.lineage .depart) := by
  rcases h.rs with hs | hs <;>
    simp [maintainAuth, AuthState.st, lockedState,
      h.lp, h.rp, h.ls, hs, h.cm]

/-- Neither completion nor wave propagation can re-lock from this left cell;
the nonterminal geometry also excludes a last/zero session start. -/
private theorem compare_row (h : Boundary l r j bl br γ) :
    compareLifecycleAuth κ l r = (l, r.lineage .depart) := by
  have hjT : j ≠ ψ - 1 := by have := h.interior; omega
  unfold compareLifecycleAuth
  simp only [h.lp]
  rw [maintain_unsupported l r h]
  simp [completeWaveAuth, waveAuth, lift2, PPLLFableDesignR1.dropStray,
    landBackwardAuth, landForwardAuth, AuthState.lineage, AuthState.st,
    lockedState, h.lp, h.rp, h.ls, h.lt, h.rt, hjT]

private def postClean : AuthState ψ × AuthState ψ :=
  let a := afterClean hp l r
  let q := checkSourceAuth hp cfg a.1 a.2
  let d := disappearAuth hp q.1 q.2
  let z := repairAuth d.1 d.2
  compareLifecycleAuth κ z.1 z.2

private theorem postClean_released (h : Boundary l r j bl br γ) :
    Released l r (postClean hp κ l r) := by
  unfold postClean
  rw [afterClean_row hp l r h]
  dsimp only
  rw [check_row hp l r h]
  dsimp only
  have hd := disappear_row hp l r h
  generalize disappearAuth hp l r = d at hd ⊢
  rw [repair_row d.1 d.2 hd]
  dsimp only
  rw [compare_row κ d.1 d.2 hd]
  exact ⟨hd.ls, rfl, hd.lp.trans h.lp.symm, hd.rp.trans h.rp.symm,
    hd.lt, hd.rt, hd.cm, rfl, hd.lpm.trans h.lpm.symm,
    hd.rpm.trans h.rpm.symm⟩

private theorem beforeSuppress_factor :
    beforeSuppressAuth hp κ cfg l r =
      postClean hp κ (cleanCut hp κ l r).1 (cleanCut hp κ l r).2 := by
  rfl

private theorem pipeline_cut :
    PPLLAuthF.pipeline hp κ cfg l r =
      let c := cleanCut hp κ l r
      PPLLAuthCheckPostCleanHole.afterCleanToFinal hp κ cfg l r c.1 c.2 := by
  rfl

theorem pipeline_unsupported_or_hole (h : Boundary l r j bl br γ) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    PairHole q ∨ Released l r q := by
  dsimp only
  rcases cleanCut_hole_or_boundary hp κ l r h with hh | hc
  · left
    rw [pipeline_cut hp κ l r]
    exact PPLLAuthCheckPostCleanHole.afterCleanToFinal_pairHole
      hp κ cfg l r (cleanCut hp κ l r).1 (cleanCut hp κ l r).2 hh
  · have hs := postClean_released hp κ
      (cleanCut hp κ l r).1 (cleanCut hp κ l r).2 hc
    have hf := pipeline_FV hp κ cfg l r h.ll h.rl h.lr h.rr
    simp only [beforeSuppress_factor hp κ l r] at hf
    generalize cleanCut hp κ l r = c at hc hs hf
    generalize postClean hp κ c.1 c.2 = z at hs hf
    generalize PPLLAuthF.pipeline hp κ cfg l r = out at hf ⊢
    rcases hf with ⟨hL, hR⟩
    rcases hs with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩
    right
    refine ⟨(FV_state hL).trans s1, (FV_state hR).trans s2,
      (FV_path hL).trans (s3.trans (hc.lp.trans h.lp.symm)),
      (FV_path hR).trans (s4.trans (hc.rp.trans h.rp.symm)),
      (FV_path2 hL).trans s5, (FV_path2 hR).trans s6, ?_, ?_,
      (FV_pm hL).trans (s9.trans (hc.lpm.trans h.lpm.symm)),
      (FV_pm hR).trans (s10.trans (hc.rpm.trans h.rpm.symm))⟩
    · rw [FV_ctrl hL, FV_pm hL]
      exact s7
    · rw [FV_ctrl hR, FV_pm hR]
      exact s8

/-- Same exact Continuing interface as ready_step/equal_step, with a new
entrance rather than a post-CLEAN or suffix assumption. Its existing Released
field gives both depart states, both ORIGINAL paths, both absent tokens,
both ctrl=path stamps, and both ORIGINAL path marks. The remaining fields
preserve ORIGINAL endpoint labels and give reset-free follower endpoints.
No separate ReadyReleased alias or MixedAt definition is assumed or changed. -/
theorem unsupported_wave_step (j bl br : Nat) (γ : ProvColor)
    (h : Boundary l r j bl br γ) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    Target q ∨ Continuing l r q := by
  let q := PPLLAuthF.pipeline hp κ cfg l r
  by_cases hl : q.1.core.leader = true
  · exact Or.inl (Or.inl hl)
  by_cases hr : q.2.core.leader = true
  · exact Or.inl (Or.inr (Or.inl hr))
  have hlf : q.1.core.leader = false := by
    cases he : q.1.core.leader <;> simp_all
  have hrf : q.2.core.leader = false := by
    cases he : q.2.core.leader <;> simp_all
  rcases pipeline_unsupported_or_hole hp κ l r h with hh | hc
  · exact Or.inl (Or.inr (Or.inr hh))
  · have hn : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩ := by
      apply Fin.ext
      change r.core.label.val = (l.core.label.val + 1) % ψ
      rw [h.rk, h.lk]
      have hi : j + 1 < ψ := by have := h.interior; omega
      exact (Nat.mod_eq_of_lt hi).symm
    have hs := row_std hp κ cfg l r h.ll h.rl h.lr h.rr hn hrf
    exact Or.inr ⟨hc, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hlf, hrf⟩

#print axioms cleanCut_hole_or_boundary
#print axioms maintain_unsupported
#print axioms pipeline_unsupported_or_hole
#print axioms unsupported_wave_step

end PPLLAuthCheckUnsupportedWave
