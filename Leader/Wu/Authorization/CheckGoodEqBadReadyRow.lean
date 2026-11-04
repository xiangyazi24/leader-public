import Leader.Wu.Authorization.GenerationDrain
import Leader.Wu.Authorization.CheckGoodEqBadReady
import Leader.Wu.Authorization.CheckSuffixPathFrame

/-!
# Full AuthF row: GoodEq / wrong-stamp CHECK_ready

The local CHECK-only field module is accepted. Its compiled exact equality
is used only as internal proof support; this does not claim that its separate
whole-record pattern scan completed. The advertised result is the full row.

No CLEAN/writer/echo/p/p_carry premise is added.  In particular the CHECK
verdict is tied to the actual pre-CHECK physical bit, not the later WRITE bit.
-/

namespace PPLLAuthGoodEqBadReadyRow

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState

set_option autoImplicit false

def cfg : PPLLAuthF.Cfg :=
  { retire := true, markClean := true, claimCheck := true }

structure BoundaryBase {ψ : Nat}
    (l r : AuthState ψ) (j br : Nat) (γ ρ : ProvColor) : Prop where
  interior : j + 2 < ψ
  llabel : l.core.label.val = j
  rlabel : r.core.label.val = j + 1
  rpath : r.core.path = .some (j + 1) br
  lstate : l.core.state = .equal
  rstate : r.core.state = .CHECK_ready
  lp2 : l.core.path2 = none
  rp2 : r.core.path2 = none
  lleader : l.core.leader = false
  rleader : r.core.leader = false
  lreset : l.core.reset_cmd = false
  rreset : r.core.reset_cmd = false
  lpm : l.path_mark = γ
  rpm : r.path_mark = γ
  lctrl : l.ctrl_mark = γ
  rctrl : r.ctrl_mark = ρ
  bad : ρ ≠ γ

def Entrance {ψ : Nat}
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor) : Prop :=
  BoundaryBase l r j br γ ρ ∧ l.core.path = .some j bl

private def HoleBoundary {ψ : Nat}
    (l r : AuthState ψ) (j br : Nat) (γ ρ : ProvColor) : Prop :=
  BoundaryBase l r j br γ ρ ∧ l.core.path = .bot

private def preClean {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2 (pPsiProbeWall hp) l r
  genSigAuth hp κ q.1 q.2

private def afterClean {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

/-- Exact cut in PPLLAuthF.beforeElimination immediately before checkSourceAuth. -/
def checkCut {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := preClean hp κ l r
  let q := cleanSourceAuth hp cfg q.1 q.2
  afterClean hp q.1 q.2

private def checkSuffix {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := checkSourceAuth hp cfg l r
  let q := disappearAuth hp q.1 q.2
  let q := repairAuth q.1 q.2
  compareLifecycleAuth κ q.1 q.2

private def checkedRight {ψ : Nat} (r : AuthState ψ) (br : Nat) : AuthState ψ :=
  { r with core := { r.core with state := checkBit r.core.bit br } }

def Target {ψ : Nat} (q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.leader = true ∨
  q.2.core.leader = true ∨
  q.1.core.path = .bot ∨
  q.2.core.path = .bot

def Continue {ψ : Nat}
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (cut q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.leader = false ∧
  q.2.core.leader = false ∧
  q.1.core.label = l.core.label ∧
  q.2.core.label = r.core.label ∧
  q.1.core.reset_cmd = false ∧
  q.2.core.reset_cmd = false ∧
  q.1.core.path = .some j bl ∧
  q.2.core.path = .some (j + 1) br ∧
  q.1.path_mark = γ ∧
  q.2.path_mark = γ ∧
  q.1.core.state = .equal ∧
  q.1.core.path2 = none ∧
  q.1.ctrl_mark = γ ∧
  q.1.ctrl_mark = q.1.path_mark ∧
  q.2.core.state = checkBit cut.2.core.bit br ∧
  (q.2.core.state = .equal ∨ q.2.core.state = .larger ∨
    q.2.core.state = .less) ∧
  q.2.core.path2 = none ∧
  q.2.ctrl_mark = ρ ∧
  q.2.ctrl_mark ≠ q.2.path_mark

private theorem checkBit_cases (b : Bool) (x : Nat) :
    checkBit b x = .equal ∨ checkBit b x = .larger ∨ checkBit b x = .less := by
  unfold checkBit
  dsimp only
  by_cases he : (if b then 1 else 0) = x
  · simp [he]
  · by_cases hgt : (if b then 1 else 0) > x
    · simp [he, hgt]
    · simp [he, hgt]

private theorem lctrl_pm {ψ : Nat} {l r : AuthState ψ} {j br : Nat} {γ ρ : ProvColor}
    (h : BoundaryBase l r j br γ ρ) : l.ctrl_mark = l.path_mark :=
  h.lctrl.trans h.lpm.symm

private theorem pm_eq {ψ : Nat} {l r : AuthState ψ} {j br : Nat} {γ ρ : ProvColor}
    (h : BoundaryBase l r j br γ ρ) : l.path_mark = r.path_mark :=
  h.lpm.trans h.rpm.symm

private theorem ctrl_ne {ψ : Nat} {l r : AuthState ψ} {j br : Nat} {γ ρ : ProvColor}
    (h : BoundaryBase l r j br γ ρ) : l.ctrl_mark ≠ r.ctrl_mark := by
  intro e
  apply h.bad
  exact h.rctrl.symm.trans (e.symm.trans h.lctrl)

private theorem gen_boundary {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h : Entrance l r j bl br γ ρ) :
    genSigAuth hp κ l r = lift2 (waitSaturated hp κ) l r := by
  rcases h with ⟨h, hlp⟩
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  unfold genSigAuth
  generalize lift2 (waitSaturated hp κ) l r = q
    at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 ⊢
  rcases q with ⟨a,b⟩
  simp only at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7
  simp [AuthState.st, a1, a2, b1, hlp, h.lstate, h.rstate]

private theorem wait_entrance {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    Entrance (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 j bl br γ ρ := by
  rcases h0 with ⟨h, hlp⟩
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  have hd := PPLLAuthResetDrain.wait_dv hp κ l.core r.core
  simp only [PPLLAuthResetDrain.dv, Prod.mk.injEq] at hd
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  rcases hd with ⟨⟨ar,_,_,_⟩,⟨brs,_,_,_⟩⟩
  refine ⟨?_, ?_⟩
  · constructor <;> simp_all [h.interior,h.llabel,h.rlabel,h.rpath,
      h.lstate,h.rstate,h.lp2,h.rp2,h.lleader,h.rleader,h.lreset,h.rreset,
      h.lpm,h.rpm,h.lctrl,h.rctrl,h.bad,lift2]
  · simp_all [lift2, hlp]

private theorem preClean_entrance {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    Entrance (preClean hp κ l r).1 (preClean hp κ l r).2 j bl br γ ρ := by
  rcases h0 with ⟨h, hlp⟩
  have hmod : r.core.label.val = (l.core.label.val + 1) % ψ := by
    have hinterior := h.interior
    rw [h.rlabel, h.llabel, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨x,y,hp0⟩ :=
    PPLLAuthGenDrain.P0_frame hp l r h.lleader h.rleader hmod
  let a := PPLLAuthGenDrain.withProbe l x
  let b := PPLLAuthGenDrain.withProbe r y
  have hp0' : lift2 (pPsiProbeWall hp) l r = (a,b) := by
    simpa [PPLLAuthGenDrain.P0,a,b,PPLLAuthGenDrain.withProbe] using hp0
  have hab : Entrance a b j bl br γ ρ := by
    refine ⟨?_, ?_⟩
    · constructor <;> simp [a,b,PPLLAuthGenDrain.withProbe,h.interior,h.llabel,
        h.rlabel,h.rpath,h.lstate,h.rstate,h.lp2,h.rp2,h.lleader,h.rleader,
        h.lreset,h.rreset,h.lpm,h.rpm,h.lctrl,h.rctrl,h.bad]
    · simpa [a,PPLLAuthGenDrain.withProbe] using hlp
  unfold preClean
  rw [hp0']
  rw [gen_boundary hp κ a b j bl br γ ρ hab]
  exact wait_entrance hp κ a b j bl br γ ρ hab

private theorem clean_right_path {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    (cleanSourceAuth hp cfg l r).2.core.path = r.core.path := by
  rcases h0 with ⟨h, hlp⟩
  have hpm : r.path_mark = l.path_mark := (pm_eq h).symm
  have hjT : j ≠ ψ - 1 := by have := h.interior; omega
  have hrT : j + 1 ≠ ψ - 1 := by have := h.interior; omega
  have hji : (j : Int) ≠ -1 := by omega
  have hri : (j : Int) + 1 ≠ -1 := by omega
  by_cases hj0 : j = 0
  · subst j
    cases ht : l.core.path4 with
    | none =>
        simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
          step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,hlp,h.rpath,hpm,
          ht,hjT,hrT]
    | some t =>
        rcases t with ⟨v,bit⟩
        by_cases hv : v = -1 <;>
          simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
            step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,hlp,h.rpath,hpm,
            ht,hjT,hrT,hv]
  · simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
      step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,hlp,h.rpath,hpm,
      hj0,hjT,hrT,hji,hri]

private theorem clean_split {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    let q := cleanSourceAuth hp cfg l r
    HoleBoundary q.1 q.2 j br γ ρ ∨ Entrance q.1 q.2 j bl br γ ρ := by
  rcases h0 with ⟨h, hlp⟩
  dsimp only
  have hv := PPLLAuthGenDrain.T1_cv hp cfg (l,r)
  have ha := PPLLAuthGenDrain.T1_pa hp cfg (l,r)
  have hrp := clean_right_path hp l r j bl br γ ρ ⟨h,hlp⟩
  simp only [PPLLAuthGenDrain.T1] at hv ha
  rcases hv with ⟨vl,vr,pl,_⟩
  simp only [PPLLAuthGenDrain.cv,Prod.mk.injEq] at vl vr
  simp only [PPLLAuthGenDrain.PA,PPLLAuthResetDrain.av,PPLLAuthResetDrain.dv,
    Prod.mk.injEq] at ha
  rcases vl with ⟨a1,_,a3,a4,a5⟩
  rcases vr with ⟨b1,_,b3,b4,b5⟩
  rcases ha with ⟨⟨a6,_,a7,a8⟩,⟨b6,_,b7,b8⟩⟩
  have hb : BoundaryBase (cleanSourceAuth hp cfg l r).1
      (cleanSourceAuth hp cfg l r).2 j br γ ρ := by
    constructor <;> simp_all [h.interior,h.llabel,h.rlabel,h.rpath,h.lstate,
      h.rstate,h.lp2,h.rp2,h.lleader,h.rleader,h.lreset,h.rreset,h.lpm,h.rpm,
      h.lctrl,h.rctrl,h.bad]
  rcases pl with pl | pl
  · exact Or.inr ⟨hb, pl.trans hlp⟩
  · exact Or.inl ⟨hb, pl⟩

private theorem move_full {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    moveSourceAuth hp cfg l r = (l,r) := by
  rcases h0 with ⟨h, hlp⟩
  have hj1 : j + 1 ≠ 0 := by omega
  have hlm := lctrl_pm h
  simp [moveSourceAuth,validateCheck,headBad,checkState,verdict,isHead,aligned,
    sanitizeP2,p2Valid,step1Auth,moveTokensAuth,leaderWallAuth,applyControlAuth,
    AuthState.st,hlp,h.rpath,h.llabel,h.rlabel,h.lstate,h.rstate,h.lp2,h.rp2,
    h.lleader,h.rleader,hlm,hj1]

private theorem move_hole {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j br : Nat) (γ ρ : ProvColor)
    (h0 : HoleBoundary l r j br γ ρ) :
    moveSourceAuth hp cfg l r = (l,r) := by
  rcases h0 with ⟨h, hlp⟩
  have hj1 : j + 1 ≠ 0 := by omega
  have hlm := lctrl_pm h
  simp [moveSourceAuth,validateCheck,headBad,checkState,verdict,isHead,aligned,
    sanitizeP2,p2Valid,step1Auth,moveTokensAuth,leaderWallAuth,applyControlAuth,
    AuthState.st,hlp,h.rpath,h.llabel,h.rlabel,h.lstate,h.rstate,h.lp2,h.rp2,
    h.lleader,h.rleader,hlm,hj1]

private theorem afterClean_full {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) : afterClean hp l r = (l,r) := by
  have hm := move_full hp l r j bl br γ ρ h0
  rcases h0 with ⟨h, hlp⟩
  simp only [afterClean,lift2Life,releaseSource,h.rstate,h.lstate]
  simp [lift2,eliminateSig,h.rstate,hm,liftLife,dropStale,aligned,
    preCheckResetAuth,normalizeReady,normalizeOrphan,normalizeCarrier,releaseCongest,
    h.llabel,h.rlabel,hlp,h.rpath,h.lstate,h.rstate,h.lp2,h.rp2,h.lleader,
    h.rleader,h.lreset,h.rreset]

private theorem afterClean_hole {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j br : Nat) (γ ρ : ProvColor)
    (h0 : HoleBoundary l r j br γ ρ) : afterClean hp l r = (l,r) := by
  have hm := move_hole hp l r j br γ ρ h0
  rcases h0 with ⟨h, hlp⟩
  simp only [afterClean,lift2Life,releaseSource,h.rstate,h.lstate]
  simp [lift2,eliminateSig,h.rstate,hm,liftLife,dropStale,aligned,
    preCheckResetAuth,normalizeReady,normalizeOrphan,normalizeCarrier,releaseCongest,
    h.llabel,h.rlabel,hlp,h.rpath,h.lstate,h.rstate,h.lp2,h.rp2,h.lleader,
    h.rleader,h.lreset,h.rreset]

/-- Bridge the identical suffix definitions on symbolic inputs. -/
private theorem checkSuffix_eq {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (u v : AuthState ψ) :
    checkSuffix hp κ u v =
      PPLLAuthCheckSuffixPathFrame.checkSuffixC hp κ cfg u v := by
  rfl

/-- The accepted exact path frame transports this left hole through the
entire original CHECK-to-COMPARE suffix. -/
private theorem suffix_left_hole {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (j br : Nat) (γ ρ : ProvColor)
    (h0 : HoleBoundary l r j br γ ρ) :
    (checkSuffix hp κ l r).1.core.path = .bot := by
  rw [checkSuffix_eq]
  exact (PPLLAuthCheckSuffixPathFrame.checkSuffixC_path hp κ cfg l r).1.trans h0.2

/-- Internal exact CHECK equality from the accepted CHECK field module. -/
private theorem check_full {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    checkSourceAuth hp cfg l r = (l, checkedRight r br) := by
  rcases h0 with ⟨h, hlp⟩
  have hpm := pm_eq h
  have hlcm := lctrl_pm h
  have hrcm : r.ctrl_mark ≠ r.path_mark := by
    intro e
    apply h.bad
    exact h.rctrl.symm.trans (e.trans h.rpm)
  have hx :=
    PPLLAuthCheckGoodEqBadReady.checkSource_goodEq_badReady_exact
      (hp := hp) (hj := h.interior) (l := l) (r := r)
      (hll := h.llabel) (hrl := h.rlabel) (hlp := hlp) (hrp := h.rpath)
      (hls := h.lstate) (hrs := h.rstate) (hlt := h.lp2) (hrt := h.rp2)
      (hpm := hpm) (hlcm := hlcm) (hrcm := hrcm)
  simpa [cfg,PPLLAuthCheckGoodEqBadReady.cfg,checkedRight] using hx

private theorem suffix_full_fv {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    let rv := checkedRight r br
    let q := checkSuffix hp κ l r
    PPLLAuthGenDrain.FV q.1 = PPLLAuthGenDrain.FV l ∧
    PPLLAuthGenDrain.FV q.2 = PPLLAuthGenDrain.FV rv := by
  dsimp only
  have hx := check_full hp l r j bl br γ ρ h0
  rcases h0 with ⟨h, hlp⟩
  have hlm := lctrl_pm h
  have hpm := pm_eq h
  have hcr := ctrl_ne h
  have hrt : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    rw [h.rlabel] at hv
    have := h.interior
    omega
  unfold checkSuffix
  rw [hx]
  dsimp only
  dsimp only [checkedRight]
  rcases checkBit_cases r.core.bit br with hs | hs | hs
  all_goals
    rw [hs]
    cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
      simp [checkedRight,disappearAuth,disappearStartL,disappearCarry,lift2,
        repairAuth,liftLife,normalizeOrphan,normalizeCarrier,releaseCongest,
        lift2Life,releaseReadySuffix,ackTailAuth,ackTail,lockedState,
        compareLifecycleAuth,maintainAuth,completeWaveAuth,waveAuth,
        PPLLFableDesignR1.dropStray,landBackwardAuth,landForwardAuth,
        PPLLAuthGenDrain.FV,AuthState.st,AuthState.setState,AuthState.withCore,
        AuthState.lineage,hlp,h.rpath,h.llabel,h.rlabel,h.lstate,h.rstate,
        h.lp2,h.rp2,h.lleader,h.rleader,hlm,hpm,hcr,hc,hb,hrt]

private theorem beforeSuppress_checkSuffix {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) :
    PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r =
      checkSuffix hp κ (checkCut hp κ l r).1 (checkCut hp κ l r).2 := by
  rfl

/-- Full original AuthF row.  Either the row has already produced a leader,
CLEAN (or a later stage) leaves a final main-path hole, or the exact
GoodEq/wrong-stamp verdict continuation is retained. -/
theorem pipeline_goodEq_badReady_target_or_continue
    {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (j bl br : Nat) (γ ρ : ProvColor)
    (h0 : Entrance l r j bl br γ ρ) :
    let cut := checkCut hp κ l r
    let out := PPLLAuthF.pipeline hp κ cfg l r
    Target out ∨ Continue l r j bl br γ ρ cut out := by
  dsimp only
  let cut := checkCut hp κ l r
  let out := PPLLAuthF.pipeline hp κ cfg l r
  change Target out ∨ Continue l r j bl br γ ρ cut out
  have h := h0.1
  let g := preClean hp κ l r
  have hg : Entrance g.1 g.2 j bl br γ ρ := preClean_entrance hp κ l r j bl br γ ρ h0
  let c := cleanSourceAuth hp cfg g.1 g.2
  have hc : HoleBoundary c.1 c.2 j br γ ρ ∨ Entrance c.1 c.2 j bl br γ ρ := by
    simpa [c] using clean_split hp g.1 g.2 j bl br γ ρ hg
  have hcut0 : cut = afterClean hp c.1 c.2 := by rfl
  have hf0 := PPLLAuthGenDrain.pipeline_FV hp κ cfg l r
    h.lleader h.rleader h.lreset h.rreset
  have hf :
      PPLLAuthGenDrain.FV out.1 =
        PPLLAuthGenDrain.FV (PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r).1 ∧
      PPLLAuthGenDrain.FV out.2 =
        PPLLAuthGenDrain.FV (PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r).2 := by
    simpa [out] using hf0
  rcases hc with hh | hk
  · have ha := afterClean_hole hp c.1 c.2 j br γ ρ hh
    have hcut : cut = (c.1,c.2) := hcut0.trans ha
    have hbs :
        PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r =
          checkSuffix hp κ c.1 c.2 := by
      have hcut' : checkCut hp κ l r = (c.1,c.2) := hcut
      rw [beforeSuppress_checkSuffix, hcut']
    have hz := suffix_left_hole hp κ c.1 c.2 j br γ ρ hh
    have hpre :
        (PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r).1.core.path = .bot := by
      rw [hbs]
      exact hz
    left
    unfold Target
    exact Or.inr (Or.inr (Or.inl ((PPLLAuthGenDrain.FV_path hf.1).trans hpre)))
  · have ha := afterClean_full hp c.1 c.2 j bl br γ ρ hk
    have hcut : cut = (c.1,c.2) := hcut0.trans ha
    have hbs :
        PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r =
          checkSuffix hp κ c.1 c.2 := by
      have hcut' : checkCut hp κ l r = (c.1,c.2) := hcut
      rw [beforeSuppress_checkSuffix, hcut']
    have hs := suffix_full_fv hp κ c.1 c.2 j bl br γ ρ hk
    dsimp only at hs
    have hp1 :
        PPLLAuthGenDrain.FV
            (PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r).1 =
          PPLLAuthGenDrain.FV c.1 := by
      rw [hbs]
      exact hs.1
    have hp2 :
        PPLLAuthGenDrain.FV
            (PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r).2 =
          PPLLAuthGenDrain.FV (checkedRight c.2 br) := by
      rw [hbs]
      exact hs.2
    have f1 : PPLLAuthGenDrain.FV out.1 = PPLLAuthGenDrain.FV c.1 :=
      hf.1.trans hp1
    have f2 : PPLLAuthGenDrain.FV out.2 =
        PPLLAuthGenDrain.FV (checkedRight c.2 br) :=
      hf.2.trans hp2
    cases hL : out.1.core.leader with
    | true =>
        left
        unfold Target
        exact Or.inl hL
    | false =>
        cases hR : out.2.core.leader with
        | true =>
            left
            unfold Target
            exact Or.inr (Or.inl hR)
        | false =>
            right
            have hnext : r.core.label =
                ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩ := by
              apply Fin.ext
              simp only
              have hinterior := h.interior
              rw [h.rlabel,h.llabel,Nat.mod_eq_of_lt (by omega)]
            have hstd := PPLLAuthGenDrain.row_std hp κ cfg l r
              h.lleader h.rleader h.lreset h.rreset hnext hR
            rcases hstd with ⟨ol,or,orl,orr⟩
            have lp : out.1.core.path = .some j bl :=
              (PPLLAuthGenDrain.FV_path f1).trans hk.2
            have rp : out.2.core.path = .some (j + 1) br := by
              rw [PPLLAuthGenDrain.FV_path f2]
              simpa [checkedRight] using hk.1.rpath
            have lpm : out.1.path_mark = γ :=
              (PPLLAuthGenDrain.FV_pm f1).trans hk.1.lpm
            have rpm : out.2.path_mark = γ := by
              rw [PPLLAuthGenDrain.FV_pm f2]
              simpa [checkedRight] using hk.1.rpm
            have ls : out.1.core.state = .equal :=
              (PPLLAuthGenDrain.FV_state f1).trans hk.1.lstate
            have lt : out.1.core.path2 = none :=
              (PPLLAuthGenDrain.FV_path2 f1).trans hk.1.lp2
            have lc : out.1.ctrl_mark = γ :=
              (PPLLAuthGenDrain.FV_ctrl f1).trans hk.1.lctrl
            have lline : out.1.ctrl_mark = out.1.path_mark :=
              lc.trans lpm.symm
            have rt : out.2.core.path2 = none := by
              rw [PPLLAuthGenDrain.FV_path2 f2]
              simpa [checkedRight] using hk.1.rp2
            have rc : out.2.ctrl_mark = ρ := by
              rw [PPLLAuthGenDrain.FV_ctrl f2]
              simpa [checkedRight] using hk.1.rctrl
            have rbad : out.2.ctrl_mark ≠ out.2.path_mark := by
              intro e
              apply hk.1.bad
              exact rc.symm.trans (e.trans rpm)
            have rs0 : out.2.core.state = checkBit c.2.core.bit br := by
              simpa [checkedRight] using PPLLAuthGenDrain.FV_state f2
            have hcbit : cut.2.core.bit = c.2.core.bit :=
              congrArg (fun z => z.2.core.bit) hcut
            have rs : out.2.core.state = checkBit cut.2.core.bit br := by
              rw [hcbit]
              exact rs0
            have rv :
                out.2.core.state = .equal ∨ out.2.core.state = .larger ∨
                  out.2.core.state = .less := by
              rcases checkBit_cases cut.2.core.bit br with e | e | e
              · exact Or.inl (rs.trans e)
              · exact Or.inr (Or.inl (rs.trans e))
              · exact Or.inr (Or.inr (rs.trans e))
            unfold Continue
            exact ⟨hL,hR,ol,or,orl,orr,lp,rp,lpm,rpm,ls,lt,lc,lline,
              rs,rv,rt,rc,rbad⟩

#print axioms pipeline_goodEq_badReady_target_or_continue

end PPLLAuthGoodEqBadReadyRow
