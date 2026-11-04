import Leader.L3.Top.SuffixBridge
import Leader.L3.Top.PinnedPrepareCells

/-!
# Q7 (preparation, lemma 1, concrete links): pending-or-settled outputs of one service

`TopFinalMobileJoint.qi_joint` links a PENDING output of the first-match input row to the input it
comes from and to its audit atom.  A settled output has the same provenance: it is the settled
input of the same register (framed), or the pending input that settled in place; in both cases
the audit atom stays.  This module states the link for outputs that are pending or settled
(`qi_joint_settled`), lifts it to the fixed trace (`src_link_settled`, `resp_link_settled`), and
gives the flag lemmas of the pending-or-settled labelled window (`src_flag_settled`,
`resp_flag_settled`, `away_flag_settled`).

Consumer: `Leader/L3/Top/PinnedPrepareBridge.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The pending token of a pending or settled token: a settled token is read as the pending
token with the same value and tail.

Consumer: `SiteLabSettled`. -/
def puTok {A : Nat} : InTok A → InTok A
  | .S v t => .P v t
  | q => q

/-- The input token holds a pending or a settled input.

Consumer: `FlagAtSettled`. -/
def tokNonE {A : Nat} (q : InTok A) : Bool := q.isP || q.isS

/-- The input rows (`inputs`) of `digitLaneReplay`, verbatim with their look flags. -/
private def pinReplayInputs {c : Compiled} {n : Nat}
    (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) : DigitInputGhost n × Bool :=
  let stamp : DigitStamp n :=
    { time := time, site := source, lane := lane }
  let roots := x.leader || y.leader
  let terminal := y.leader || y.marker
  let success :=
    x.carryLive && !terminal && !y.carryLive && y.input.isS
  let launch :=
    !x.leader && x.marker && !x.carryLive &&
      x.input.isS && !y.leader
  let offer := x.out.isD && y.marker
  let inputs : DigitInputGhost n × Bool :=
    if roots then
      ({ x := none, y := none, fx := true, fy := true }, false)
    else
      let s : DigitInputGhost n :=
        { x := gx.input, y := gy.input, fx := false, fy := false }
      let s :=
        if !s.fx && x.carryLive then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fy && y.carryLive then
          { s with y := none, fy := true }
        else s
      let s :=
        if !s.fx && x.input.isS && inT x.input && !x.marker then
          { s with x := gx.input, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isX then
          let s := { s with x := none, fx := true }
          if !s.fy && !y.leader && !y.marker && y.input.isS then
            { s with y := gx.input, fy := true }
          else s
        else s
      let s :=
        if success && !s.fy then
          { s with y := none, fy := true }
        else s
      let s :=
        if launch && !s.fx then
          { s with x := none, fx := true }
        else s
      let s :=
        if !s.fx && x.input.isP then
          if terminal then
            if !inT x.input then
              { s with x := gx.input, fx := true }
            else if !x.marker then
              { s with x := none, fx := true }
            else s
          else if !y.leader && !y.marker &&
              y.input.isE && !y.carryLive && !s.fy then
            { x := none, y := gx.input, fx := true, fy := true }
          else if y.input.isS && !y.carryLive then
            { s with x := gx.input, fx := true }
          else s
        else s
      let accepted :=
        !s.fy && offer && y.input.isE && !y.carryLive
      let s :=
        if accepted then
          { s with y := gx.out.atom, fy := true }
        else s
      (s, accepted)
  inputs

private theorem pinReplay_x_input {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).x.input =
      (pinReplayInputs lane time source destination x y gx gy).1.x := rfl

private theorem pinReplay_y_input {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n) :
    (digitLaneReplay lane time source destination x y gx gy).y.input =
      (pinReplayInputs lane time source destination x y gx gy).1.y := rfl


/-- **Joint link of the input row for pending or settled outputs.**  A pending or settled
source output is the source input (or the pending source input settled in place) and keeps its
audit atom; a pending or settled responder output is the responder input, or the source input
moved into an empty carry-free interior responder, or the packet accepted at a marker.

Consumer: `src_link_settled`, `resp_link_settled`. -/
theorem qi_joint_settled {c : Compiled} {n : Nat} (time : Nat) (src dst : Fin n)
    (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (gx gy : DigitLaneGhost c n) :
    (tokNonE (qiPhys c x y).1.iX = true →
      puTok (qiPhys c x y).1.iX = puTok x.qIn ∧ tokNonE x.qIn = true ∧
      (digitLaneReplay .comparison time src dst
        (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
        (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).x.input = gx.input) ∧
    (tokNonE (qiPhys c x y).1.iY = true →
      (tokNonE y.qIn = true ∧ puTok (qiPhys c x y).1.iY = puTok y.qIn ∧
        (digitLaneReplay .comparison time src dst
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
          (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.input = gy.input) ∨
      (y.beta = false ∧ y.qIn = .E ∧ y.qCarry = .OFF ∧ x.qIn.isP = true ∧
        (qiPhys c x y).1.iY = x.qIn ∧
        (digitLaneReplay .comparison time src dst
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
          (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.input = gx.input) ∨
      (y.beta = true ∧ y.qIn = .E ∧ y.qCarry = .OFF ∧ (qiPhys c x y).2 = true ∧
        (qiPhys c x y).1.iY = .P (outV c x.qOut) (outT x.qOut) ∧
        (digitLaneReplay .comparison time src dst
          (digitLaneView .comparison (ProjD.ofAgent x) x.beta)
          (digitLaneView .comparison (ProjD.ofAgent y) y.beta) gx gy).y.input = gx.out.atom)) := by
  simp only [pinReplay_x_input, pinReplay_y_input]
  -- Split the carries, the source input and both markers first and simplify once; the guards of
  -- both rows that read them are then decided, and the remaining splits work on the residual.
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  cases hxb : x.beta <;> cases hyb : y.beta <;>
  (try simp
    [qiPhys, pinReplayInputs, digitLaneView, ProjD.ofAgent, ProjW.ofAgent, hxl, hyl, hxq,
     hxk, hyk, hxb, hyb, topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL,
     InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, Agent.certNative, tokNonE, puTok]) <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  cases hd : x.qOut.isD <;>
  (try cases xt) <;> (try cases yt) <;>
  simp
    [qiPhys, pinReplayInputs, digitLaneView, ProjD.ofAgent, ProjW.ofAgent, hxl, hyl, hxq, hyq,
     hxk, hyk, hxb, hyb, hd, topTerminal, topInternal, topBorder, QCarry.isOff, QCarry.isL,
     InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV, Agent.certNative, tokNonE, puTok]

/-- **A pending or settled source output is the source input.**

Consumer: `src_flag_settled`. -/
theorem src_link_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hP : tokNonE ((topFixedTraceNext ring C Z e).1.1 e).qIn = true) :
    tokNonE (Z.1.1 e).qIn = true ∧
      puTok ((topFixedTraceNext ring C Z e).1.1 e).qIn = puTok (Z.1.1 e).qIn ∧
      ((topFixedTraceNext ring C Z e).1.2.current e).comparison.input =
        (Z.1.2.current e).comparison.input := by
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hsrc := topPortLiteralSourceFields ring C Z.1.1 e
  have hphys : (topFixedTraceNext ring C Z e).1.1 e = topFixedPublicNext ring C Z.1.1 e e := rfl
  have hq1 : ((topFixedTraceNext ring C Z e).1.1 e).qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))).1.iX := by
    rw [hphys, hsrc.1, hq.1]
  rw [hq1] at hP
  obtain ⟨j1, j2, j3⟩ := (qi_joint_settled (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
    (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison).1 hP
  refine ⟨j2, by rw [hq1]; exact j1, ?_⟩
  rw [next_input_source]
  exact j3

/-- **A pending or settled responder output is the responder input, the source input moved in,
or the accepted packet.**

Consumer: `resp_flag_settled`, `port_bridge_settled`. -/
theorem resp_link_settled {n : Nat} (ring : DirectedRing n) (hn2 : 2 ≤ n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hP : tokNonE ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = true) :
    (tokNonE (Z.1.1 (ring.rightNeighbor e)).qIn = true ∧
      puTok ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn =
        puTok (Z.1.1 (ring.rightNeighbor e)).qIn ∧
      ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
        (Z.1.2.current (ring.rightNeighbor e)).comparison.input) ∨
    ((Z.1.1 (ring.rightNeighbor e)).beta = false ∧
      (Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧ (Z.1.1 e).qIn.isP = true ∧
      ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = (Z.1.1 e).qIn ∧
      ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
        (Z.1.2.current e).comparison.input) ∨
    ((Z.1.1 (ring.rightNeighbor e)).beta = true ∧ (Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
      (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF ∧
      ∃ ex, (traceReplay ring Z e).exported = some ex ∧
        ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = .P ex.value ex.tail ∧
        ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
          ex.operand ∧
        ex.time = Z.1.2.clock + 1 ∧ ex.source = e ∧ ex.destination = ring.rightNeighbor e) := by
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hresp := topPortLiteralResponderFields ring hn2 C Z.1.1 e
  have hne := rightNeighbor_ne ring hn2 e
  have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
  have hq2 : ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))).1.iY := by
    rw [hphys, hresp.1, hq.2]
  rw [hq2] at hP
  have hj := qi_joint (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
    (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
  have hjs := (qi_joint_settled (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
    (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison).2 hP
  rw [hq2, next_input_responder ring C Z e hne]
  rcases hjs with ⟨d1, d2, d3⟩ | ⟨d1, d2, d3, d4, d5, d6⟩ | ⟨d1, d2, d3, d4, d5, d6⟩
  · exact Or.inl ⟨d1, d2, d3⟩
  · right; left
    refine ⟨d1, d2, d4, ?_, d6⟩
    rw [d5]
  · right; right
    refine ⟨d1, d2, d3, ?_⟩
    have hP' : ((qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
        (Z.1.1 (ring.rightNeighbor e))).1.iY).isP = true := by
      rw [d5]; rfl
    have hne' : (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e))) 
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported ≠ none :=
      hj.2.2.mpr d4
    obtain ⟨ex, hex⟩ := Option.ne_none_iff_exists'.1 hne'
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := replay_exported_fields _ _ _ _ _ _ _ _ ex hex
    refine ⟨ex, hex, ?_, ?_, f3, f1, f2⟩
    · rw [d5, f5, f6]; rfl
    · rw [d6, f4]

/-- The register `v` holds a pending or settled input whose atom is post-anchor.

Consumer: `paFlagSettled`, `src_flag_settled`. -/
def FlagAtSettled {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (v : Fin n) :
    Prop :=
  tokNonE (Z.1.1 v).qIn = true ∧ topClockPostAnchor s Z τ ((Z.1.2.current v).comparison.input)

/-- The label of a register: its audit atom and its pending-read token.

Consumer: `paLabSettled`, `away_flag_settled`. -/
def SiteLabSettled {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) : PaLabel n :=
  ((Z.1.2.current v).comparison.input, puTok (Z.1.1 v).qIn)

/-- Window register `j` holds a pending or settled input whose atom is post-anchor.

Consumer: `PuAgree`, `PuLinv`. -/
noncomputable def paFlagSettled {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat)
    (j : Nat) : Bool :=
  decide (j < topClockSpan n ∧ tokNonE (Y.1.1 (winSite s j)).qIn = true ∧
    topClockPostAnchor s Y τ ((Y.1.2.current (winSite s j)).comparison.input))

/-- The label of window register `j`.

Consumer: `PuAgree`, `PuLinv`. -/
def paLabSettled {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (j : Nat) : PaLabel n :=
  ((Y.1.2.current (winSite s j)).comparison.input, puTok (Y.1.1 (winSite s j)).qIn)

/-- A flagged register is in the window, pending or settled, and post-anchor.

Consumer: `paFlag_settled_site`. -/
theorem paFlagSettled_iff {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat) (j : Nat) :
    paFlagSettled s Y τ j = true ↔ j < topClockSpan n ∧ tokNonE (Y.1.1 (winSite s j)).qIn = true ∧
      topClockPostAnchor s Y τ ((Y.1.2.current (winSite s j)).comparison.input) := by
  unfold paFlagSettled
  simp

/-- Auxiliary fact of the pending-or-settled bridge.

Consumer: `window_bridge_settled`, `port_bridge_settled`. -/
theorem paFlag_settled_site {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (j : Nat) :
    paFlagSettled s Z τ j = true ↔ j < topClockSpan n ∧ FlagAtSettled s τ Z (winSite s j) := by
  rw [paFlagSettled_iff]
  unfold FlagAtSettled
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Auxiliary fact of the pending-or-settled bridge.

Consumer: `window_bridge_settled`, `port_bridge_settled`. -/
theorem paLab_settled_site {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) :
    paLabSettled s Z j = SiteLabSettled Z (winSite s j) := rfl

/-- The cell of a register is pending or settled exactly when its token is.

Consumer: `window_bridge_settled`, `port_bridge_settled`. -/
theorem cell_nonE_iff {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) :
    puNonE (cellOf s Z j).i = tokNonE (Z.1.1 (winSite s j)).qIn := by
  unfold cellOf siteCell tokNonE
  rcases (Z.1.1 (winSite s j)).qIn with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;>
    (try cases t) <;>
    simp [absIn, puNonE, Inp.isP, Inp.isS, InTok.isP, InTok.isS]

/-- The flag of the source of an edge that keeps the post-anchor test on input atoms.

Consumer: `window_bridge_settled`, `term_bridge_settled`. -/
theorem src_flag_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hpost : PostIn ring C s Z e τ) :
    FlagAtSettled s τ (topFixedTraceNext ring C Z e) e ↔
      (FlagAtSettled s τ Z e ∧ tokNonE ((topFixedTraceNext ring C Z e).1.1 e).qIn = true) := by
  unfold FlagAtSettled
  constructor
  · rintro ⟨hP, hp⟩
    obtain ⟨j1, _, j3⟩ := src_link_settled ring C Z e hxl hyl hP
    rw [j3] at hp
    exact ⟨⟨j1, (hpost e).1 hp⟩, hP⟩
  · rintro ⟨⟨hx, hp⟩, hP⟩
    obtain ⟨_, _, j3⟩ := src_link_settled ring C Z e hxl hyl hP
    rw [j3]
    exact ⟨hP, (hpost e).2 hp⟩

/-- The flag of an interior responder of an edge that keeps the post-anchor test.

Consumer: `window_bridge_settled`. -/
theorem resp_flag_settled {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hb : (Z.1.1 (ring.rightNeighbor e)).beta = false)
    (hpost : PostIn ring C s Z e τ) :
    FlagAtSettled s τ (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) ↔
      ((FlagAtSettled s τ Z (ring.rightNeighbor e) ∧
          tokNonE ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = true) ∨
        (FlagAtSettled s τ Z e ∧ tokNonE (Z.1.1 (ring.rightNeighbor e)).qIn = false ∧
          tokNonE ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = true)) := by
  unfold FlagAtSettled
  constructor
  · rintro ⟨hP, hp⟩
    rcases resp_link_settled ring hn C Z e hxl hyl hP with ⟨d1, _, d3⟩ | ⟨_, d2, d3, _, d5⟩ | ⟨d1, _⟩
    · rw [d3] at hp
      exact Or.inl ⟨⟨d1, (hpost _).1 hp⟩, hP⟩
    · rw [d5] at hp
      refine Or.inr ⟨⟨?_, (hpost _).1 hp⟩, by rw [d2]; rfl, hP⟩
      simp [tokNonE, d3]
    · rw [hb] at d1; exact absurd d1 (by decide)
  · rintro (⟨⟨hy, hp⟩, hP⟩ | ⟨⟨hx, hp⟩, hn', hP⟩)
    · rcases resp_link_settled ring hn C Z e hxl hyl hP with ⟨_, _, d3⟩ | ⟨_, d2, _, _, _⟩ | ⟨d1, _⟩
      · rw [d3]; exact ⟨hP, (hpost _).2 hp⟩
      · rw [d2] at hy; exact absurd hy (by simp [tokNonE, InTok.isP, InTok.isS])
      · rw [hb] at d1; exact absurd d1 (by decide)
    · rcases resp_link_settled ring hn C Z e hxl hyl hP with ⟨d1, _, _⟩ | ⟨_, _, _, _, d5⟩ | ⟨d1, _⟩
      · rw [hn'] at d1; exact absurd d1 (by decide)
      · rw [d5]; exact ⟨hP, (hpost _).2 hp⟩
      · rw [hb] at d1; exact absurd d1 (by decide)

/-- A register that is neither source nor responder keeps its flag, label and input.

Consumer: `window_bridge_settled`, `term_bridge_settled`, `port_bridge_settled`,
`frame_bridge_settled`. -/
theorem away_flag_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e v : Fin n) (τ : Nat) (hx : v ≠ e)
    (hy : v ≠ ring.rightNeighbor e) (hpost : PostIn ring C s Z e τ) :
    (FlagAtSettled s τ (topFixedTraceNext ring C Z e) v ↔ FlagAtSettled s τ Z v) ∧
      SiteLabSettled (topFixedTraceNext ring C Z e) v = SiteLabSettled Z v := by
  have haway := topPortLiteralAwayFields ring C Z.1.1 e v hx hy
  have hg := next_ghost_away ring C Z e v hx hy
  have hphys : (topFixedTraceNext ring C Z e).1.1 v = topFixedPublicNext ring C Z.1.1 e v := rfl
  have hq : ((topFixedTraceNext ring C Z e).1.1 v).qIn = (Z.1.1 v).qIn := by
    rw [hphys, haway.1]
  refine ⟨?_, ?_⟩
  · unfold FlagAtSettled
    rw [hq, hg]
    exact ⟨fun h => ⟨h.1, (hpost v).1 h.2⟩, fun h => ⟨h.1, (hpost v).2 h.2⟩⟩
  · unfold SiteLabSettled
    rw [hq, hg]

end MarkedCells
end L3

#print axioms L3.MarkedCells.qi_joint_settled
#print axioms L3.MarkedCells.src_link_settled
#print axioms L3.MarkedCells.resp_link_settled
#print axioms L3.MarkedCells.src_flag_settled
#print axioms L3.MarkedCells.resp_flag_settled
#print axioms L3.MarkedCells.away_flag_settled
