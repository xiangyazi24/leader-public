import Leader.L3.Top.FinalMobileLabels
import Leader.L3.Top.FinalMobileJoint
import Leader.L3.Top.FinalMobileLinStep
import Leader.L3.Top.OldFlagsStep
import Leader.L3.Top.RepairedMarked

/-!
# Q7: the audit window follows the physical window

For a fixed-trace state `Y` and a time `τ`, every edge acts on the labelled window
`(cellOf, paFlag, paLab, paQ)` as one step of the abstract labelled window (`LStep`): a window
edge moves a flagged input with its label, the terminal edge cannot consume a flagged input,
the port edge cleans or accepts, and the accepted packet is appended to the queue of exports
after `τ` with its operand as the label.  Hence the labelled window invariant `LInv` holds at
every reached state whose exports after `τ` have an operand.

Consumer: `Leader/L3/Top/SuffixLinv.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- The comparison replay of the edge `e` of a fixed-trace state, in the form used by the
physical-ghost links.

Consumer: `replay_exported_fields`, `port_bridge`. -/
def traceReplay {n : Nat} (ring : DirectedRing n) (Z : TopFixedTraceState n) (e : Fin n) :
    DigitLaneReplay (compileAdvice (ceilLogTwo n)) n :=
  digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
    (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
      (Z.1.1 (ring.rightNeighbor e)).beta)
    (Z.1.2.current e).comparison
    (Z.1.2.current (ring.rightNeighbor e)).comparison

/-- The fields of an exported packet.

Consumer: `exportsAfter_step`, `post_step_in_acc`. -/
theorem replay_exported_fields {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat)
    (src dst : Fin n) (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (ex : DigitExport c n)
    (h : (digitLaneReplay lane time src dst x y gx gy).exported = some ex) :
    ex.source = src ∧ ex.destination = dst ∧ ex.time = time ∧ ex.operand = gx.out.atom ∧
      ex.value = outV c x.out ∧ ex.tail = outT x.out ∧ ex.lane = lane := by
  rw [replay_exported_eq] at h
  by_cases ha : (replayChain x y gx gy).2 = true
  · rw [if_pos ha] at h
    have := Option.some.inj h
    rw [← this]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg ha] at h
    exact absurd h (by simp)

/-- The exports after `τ` after one edge, with the explicit new part.

Consumer: `port_bridge`. -/
theorem exportsAfter_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) :
    topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ =
      topClockConcreteExportsAfter s Z τ ++
        ((traceReplay ring Z e).exported.toList.filter
          (fun ex => if τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
            ex.destination = certSite s (topClockSpan n) then true else false)) := by
  obtain ⟨F, hF1, hF2⟩ : ∃ F : DigitFrame (compileAdvice (ceilLogTwo n)) n,
      (topFixedTraceNext ring C Z e).1.2.frames = F :: Z.1.2.frames ∧
      (digitReceiptLane .comparison F.receipt).exported = (traceReplay ring Z e).exported :=
    ⟨_, rfl, rfl⟩
  unfold topClockConcreteExportsAfter
  rw [hF1]
  have := exports_cons Z.1.2.frames F (fun frame => (digitReceiptLane .comparison frame.receipt).exported)
    (fun exported => if τ < exported.time ∧ exported.source = certSite s (topClockSpan n - 1) ∧
          exported.destination = certSite s (topClockSpan n) then true else false)
  rw [this, hF2]

/-- The new part of the exports is empty unless the edge is the port edge.

Consumer: `window_bridge`, `frame_bridge`. -/
theorem exportsAfter_step_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ =
      topClockConcreteExportsAfter s Z τ := by
  rw [exportsAfter_step]
  have : ((traceReplay ring Z e).exported.toList.filter
          (fun ex => if τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
            ex.destination = certSite s (topClockSpan n) then true else false)) = [] := by
    rcases hh : (traceReplay ring Z e).exported with _ | ex
    · rfl
    · have hf : ex.source = e := (replay_exported_fields _ _ _ _ _ _ _ _ ex hh).1
      simp only [Option.toList, List.filter_cons]
      have : ¬ (τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
          ex.destination = certSite s (topClockSpan n)) := fun h => hb (hf ▸ h.2.1)
      simp [this]
  rw [this, List.append_nil]

/-- The register `v` holds a pending input whose atom is post-anchor.

Consumer: `paFlag_site`, `src_flag`. -/
def FlagAt {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (v : Fin n) : Prop :=
  (Z.1.1 v).qIn.isP = true ∧ topClockPostAnchor s Z τ ((Z.1.2.current v).comparison.input)

/-- The label (atom and physical input) of a register.

Consumer: `paLab_site`, `away_flag`. -/
def SiteLab {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) : PaLabel n :=
  ((Z.1.2.current v).comparison.input, (Z.1.1 v).qIn)

/-- Auxiliary fact `paFlag_site` of the labelled-window bridge.

Consumer: `window_bridge`, `port_bridge`. -/
theorem paFlag_site {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) (j : Nat) :
    paFlag s Z τ j = true ↔ j < topClockSpan n ∧ FlagAt s τ Z (winSite s j) := by
  rw [paFlag_iff]
  unfold FlagAt
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Auxiliary fact `paLab_site` of the labelled-window bridge.

Consumer: `window_bridge`, `port_bridge`. -/
theorem paLab_site {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) :
    paLab s Z j = SiteLab Z (winSite s j) := rfl

/-- The post-anchor test after one edge: the old test, or the operand of the new export.

Consumer: `post_step_in_acc`. -/
theorem post_step_iff {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) (a : Option (DigitAtom n)) :
    topClockPostAnchor s (topFixedTraceNext ring C Z e) τ a ↔
      topClockPostAnchor s Z τ a ∨ ∃ ex, (traceReplay ring Z e).exported = some ex ∧
        τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
        ex.destination = certSite s (topClockSpan n) ∧ ex.operand = a := by
  obtain ⟨extra, hl, hex⟩ := exportsAfter_next ring C s Z e τ
  unfold topClockPostAnchor
  rw [hl]
  constructor
  · rintro ⟨ex, hmem, hop⟩
    rcases List.mem_append.1 hmem with h | h
    · exact Or.inl ⟨ex, h, hop⟩
    · obtain ⟨h1, h2, h3, h4⟩ := (hex ex).1 h
      exact Or.inr ⟨ex, h1, h2, h3, h4, hop⟩
  · rintro (⟨ex, hmem, hop⟩ | ⟨ex, h1, h2, h3, h4, hop⟩)
    · exact ⟨ex, List.mem_append_left _ hmem, hop⟩
    · exact ⟨ex, List.mem_append_right _ ((hex ex).2 ⟨h1, h2, h3, h4⟩), hop⟩

/-- Away from the port edge the post-anchor test does not change.

Consumer: `window_bridge`, `frame_bridge`. -/
theorem post_step_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (hb : e ≠ certSite s (topClockSpan n - 1)) (a : Option (DigitAtom n)) :
    topClockPostAnchor s (topFixedTraceNext ring C Z e) τ a ↔ topClockPostAnchor s Z τ a := by
  unfold topClockPostAnchor
  rw [exportsAfter_step_away ring C s Z e τ hb]

/-- **A pending source output is the pending source input.**

Consumer: `window_bridge`, `term_bridge`. -/
theorem src_link {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hP : ((topFixedTraceNext ring C Z e).1.1 e).qIn.isP = true) :
    (Z.1.1 e).qIn.isP = true ∧
      ((topFixedTraceNext ring C Z e).1.1 e).qIn = (Z.1.1 e).qIn ∧
      ((topFixedTraceNext ring C Z e).1.2.current e).comparison.input =
        (Z.1.2.current e).comparison.input := by
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hsrc := topPortLiteralSourceFields ring C Z.1.1 e
  have hphys : (topFixedTraceNext ring C Z e).1.1 e = topFixedPublicNext ring C Z.1.1 e e := rfl
  have hq1 : ((topFixedTraceNext ring C Z e).1.1 e).qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))).1.iX := by
    rw [hphys, hsrc.1, hq.1]
  rw [hq1] at hP
  obtain ⟨j1, j2, j3⟩ := (qi_joint (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
    (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison).1 hP
  refine ⟨j2, by rw [hq1]; exact j1, ?_⟩
  rw [next_input_source]
  exact j3

/-- **A pending responder output is the responder input, the source input moved in, or the
accepted packet.**

Consumer: `window_bridge`, `port_bridge`. -/
theorem resp_link {n : Nat} (ring : DirectedRing n) (hn2 : 2 ≤ n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hP : ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn.isP = true) :
    ((Z.1.1 (ring.rightNeighbor e)).qIn.isP = true ∧
      ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn =
        (Z.1.1 (ring.rightNeighbor e)).qIn ∧
      ((topFixedTraceNext ring C Z e).1.2.current (ring.rightNeighbor e)).comparison.input =
        (Z.1.2.current (ring.rightNeighbor e)).comparison.input) ∨
    ((Z.1.1 (ring.rightNeighbor e)).beta = false ∧
      (Z.1.1 (ring.rightNeighbor e)).qIn.isP = false ∧ (Z.1.1 e).qIn.isP = true ∧
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
  rw [hq2, next_input_responder ring C Z e hne]
  rcases hj.2.1 hP with ⟨d1, d2, d3⟩ | ⟨d1, d2, d3, d4, d5, d6⟩ | ⟨d1, d2, d3, d4, d5, d6⟩
  · exact Or.inl ⟨d1, d2, d3⟩
  · right; left
    refine ⟨d1, ?_, d4, d5, d6⟩
    rw [d2]; rfl
  · right; right
    refine ⟨d1, d2, d3, ?_⟩
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

/-- The registers of a reached state have no leader.

Consumer: `window_bridge`, `term_bridge`, `port_bridge`. -/
theorem agent_l {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (hreach : topClockReached ring C Y)
    (v : Fin n) : (Y.1.1 v).l = false := by
  have hfrz := publicFrozen_reached ring C Y hreach
  rw [(hfrz v).1]
  exact hg.hl _

/-- The marker field of a reached state is the configuration's.

Consumer: `window_bridge`, `port_bridge`. -/
theorem agent_beta {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Y : TopFixedTraceState n) (hreach : topClockReached ring C Y) (v : Fin n) :
    (Y.1.1 v).beta = (C v).beta :=
  (publicFrozen_reached ring C Y hreach v).2

/-- The post-anchor test on the input atoms of the registers does not change along an edge.

Consumer: `src_flag`, `away_flag`. -/
def PostIn {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) : Prop :=
  ∀ v : Fin n,
    topClockPostAnchor s (topFixedTraceNext ring C Z e) τ ((Z.1.2.current v).comparison.input) ↔
      topClockPostAnchor s Z τ ((Z.1.2.current v).comparison.input)

/-- An edge that records no export keeps the post-anchor test.

Consumer: `port_bridge`. -/
theorem post_step_noexp {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (h : (traceReplay ring Z e).exported = none) (a : Option (DigitAtom n)) :
    topClockPostAnchor s (topFixedTraceNext ring C Z e) τ a ↔ topClockPostAnchor s Z τ a := by
  unfold topClockPostAnchor
  rw [exportsAfter_step, h]
  simp

/-- An accepting edge does not change the post-anchor test on input atoms: the exported operand
is the output atom of the source, which no input atom equals.

Consumer: `port_bridge`. -/
theorem post_step_in_acc {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) (hlin : Lin Z.1.2)
    (ex : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hex : (traceReplay ring Z e).exported = some ex) (hop : ex.operand ≠ none) :
    PostIn ring C s Z e τ := by
  unfold PostIn
  intro v
  rw [post_step_iff]
  constructor
  · rintro (h | ⟨ex', hex', _, _, _, hop'⟩)
    · exact h
    · exfalso
      rw [hex] at hex'
      have hee : ex = ex' := Option.some.inj hex'
      rw [← hee] at hop'
      have hf := (replay_exported_fields (c := compileAdvice (ceilLogTwo n)) _ _ _ _ _ _ _ _ ex hex).2.2.2.1
      rcases hz : ex.operand with _ | z
      · exact hop hz
      · have h1 : cmpOut Z.1.2 e = some z := by
          unfold cmpOut
          rw [← hf]
          exact hz
        rw [hz] at hop'
        exact hlin.disj e v z h1 hop'.symm
  · intro h
    exact Or.inl h

/-- A pending output of an accepting service has all the physical accept conditions.

Consumer: `port_bridge`. -/
theorem qi_acc {c : Compiled} (x y : Agent c) (hxl : x.l = false) (hyl : y.l = false)
    (h : (qiPhys c x y).2 = true) :
    y.beta = true ∧ y.qIn = .E ∧ y.qCarry = .OFF ∧
      (qiPhys c x y).1.iY = .P (outV c x.qOut) (outT x.qOut) := by
  rcases hxq : x.qIn with _ | _ | ⟨xv, xt⟩ | ⟨xv, xt⟩ <;>
  rcases hyq : y.qIn with _ | _ | ⟨yv, yt⟩ | ⟨yv, yt⟩ <;>
  rcases hxk : x.qCarry with _ | ⟨xcc, xce⟩ <;>
  rcases hyk : y.qCarry with _ | ⟨ycc, yce⟩ <;>
  cases hxb : x.beta <;> cases hyb : y.beta <;>
  cases hd : x.qOut.isD <;>
  (try cases xt) <;> (try cases yt) <;>
  simp (config := { decide := true })
    [qiPhys, hxl, hyl, hxq, hyq, hxk, hyk, hxb, hyb, hd, topTerminal, topInternal, topBorder,
     QCarry.isOff, QCarry.isL, InTok.isP, InTok.isS, InTok.isX, InTok.isE, inT, inV] at h ⊢

/-- A register with an empty input and no carry is the empty cell.

Consumer: `port_bridge`. -/
theorem siteCell_empty {n : Nat} (Z : TopFixedTraceState n) (v : Fin n)
    (h1 : (Z.1.1 v).qIn = .E) (h2 : (Z.1.1 v).qCarry = .OFF) :
    siteCell Z v = { i := .e, c := .off } := by
  unfold siteCell
  rw [h1, h2]
  simp [absIn, absCar]

/-- The flag of the source of an edge that keeps the post-anchor test on input atoms.

Consumer: `window_bridge`, `term_bridge`. -/
theorem src_flag {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hpost : PostIn ring C s Z e τ) :
    FlagAt s τ (topFixedTraceNext ring C Z e) e ↔
      (FlagAt s τ Z e ∧ ((topFixedTraceNext ring C Z e).1.1 e).qIn.isP = true) := by
  unfold FlagAt
  constructor
  · rintro ⟨hP, hp⟩
    obtain ⟨j1, _, j3⟩ := src_link ring C Z e hxl hyl hP
    rw [j3] at hp
    exact ⟨⟨j1, (hpost e).1 hp⟩, hP⟩
  · rintro ⟨⟨hx, hp⟩, hP⟩
    obtain ⟨_, _, j3⟩ := src_link ring C Z e hxl hyl hP
    rw [j3]
    exact ⟨hP, (hpost e).2 hp⟩

/-- The flag of an interior responder of an edge that keeps the post-anchor test.

Consumer: `window_bridge`. -/
theorem resp_flag {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false)
    (hb : (Z.1.1 (ring.rightNeighbor e)).beta = false)
    (hpost : PostIn ring C s Z e τ) :
    FlagAt s τ (topFixedTraceNext ring C Z e) (ring.rightNeighbor e) ↔
      ((FlagAt s τ Z (ring.rightNeighbor e) ∧
          ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn.isP = true) ∨
        (FlagAt s τ Z e ∧ (Z.1.1 (ring.rightNeighbor e)).qIn.isP = false ∧
          ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn.isP = true)) := by
  unfold FlagAt
  constructor
  · rintro ⟨hP, hp⟩
    rcases resp_link ring hn C Z e hxl hyl hP with ⟨d1, _, d3⟩ | ⟨_, d2, d3, _, d5⟩ | ⟨d1, _⟩
    · rw [d3] at hp
      exact Or.inl ⟨⟨d1, (hpost _).1 hp⟩, hP⟩
    · rw [d5] at hp
      exact Or.inr ⟨⟨d3, (hpost _).1 hp⟩, d2, hP⟩
    · rw [hb] at d1; exact absurd d1 (by decide)
  · rintro (⟨⟨hy, hp⟩, hP⟩ | ⟨⟨hx, hp⟩, hn', hP⟩)
    · rcases resp_link ring hn C Z e hxl hyl hP with ⟨_, _, d3⟩ | ⟨_, d2, _, _, _⟩ | ⟨d1, _⟩
      · rw [d3]; exact ⟨hP, (hpost _).2 hp⟩
      · rw [d2] at hy; exact absurd hy (by decide)
      · rw [hb] at d1; exact absurd d1 (by decide)
    · rcases resp_link ring hn C Z e hxl hyl hP with ⟨d1, _, _⟩ | ⟨_, _, _, _, d5⟩ | ⟨d1, _⟩
      · rw [hn'] at d1; exact absurd d1 (by decide)
      · rw [d5]; exact ⟨hP, (hpost _).2 hp⟩
      · rw [hb] at d1; exact absurd d1 (by decide)

/-- A register that is neither source nor responder keeps its flag, label and input.

Consumer: `window_bridge`, `term_bridge`, `port_bridge`, `frame_bridge`. -/
theorem away_flag {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e v : Fin n) (τ : Nat) (hx : v ≠ e)
    (hy : v ≠ ring.rightNeighbor e) (hpost : PostIn ring C s Z e τ) :
    (FlagAt s τ (topFixedTraceNext ring C Z e) v ↔ FlagAt s τ Z v) ∧
      SiteLab (topFixedTraceNext ring C Z e) v = SiteLab Z v := by
  have haway := topPortLiteralAwayFields ring C Z.1.1 e v hx hy
  have hg := next_ghost_away ring C Z e v hx hy
  have hphys : (topFixedTraceNext ring C Z e).1.1 v = topFixedPublicNext ring C Z.1.1 e v := rfl
  have hq : ((topFixedTraceNext ring C Z e).1.1 v).qIn = (Z.1.1 v).qIn := by
    rw [hphys, haway.1]
  refine ⟨?_, ?_⟩
  · unfold FlagAt
    rw [hq, hg]
    exact ⟨fun h => ⟨h.1, (hpost v).1 h.2⟩, fun h => ⟨h.1, (hpost v).2 h.2⟩⟩
  · unfold SiteLab
    rw [hq, hg]

/-- The labelled window of `Z` is the abstract data `(c', o', ℓ', Q')` on the target
registers.

Consumer: `bridge_step`. -/
def PaAgree {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (c' : Nat → Cell) (o' : Nat → Bool) (ℓ' : Nat → PaLabel n) (Q' : List (PaLabel n)) : Prop :=
  (∀ j, j < topClockSpan n → cellOf s Z j = c' j) ∧
  (∀ j, j < topClockSpan n → paFlag s Z τ j = o' j) ∧
  (∀ j, j < topClockSpan n → o' j = true → paLab s Z j = ℓ' j) ∧
  paQ s Z τ = Q'

/-- Auxiliary fact `cell_isP_iff` of the labelled-window bridge.

Consumer: `window_bridge`, `port_bridge`. -/
theorem cell_isP_iff {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) :
    (cellOf s Z j).i.isP = (Z.1.1 (winSite s j)).qIn.isP := by
  unfold cellOf; exact siteCell_isP Z _

/-- Auxiliary fact `win_ne_port` of the labelled-window bridge.

Consumer: `window_bridge`, `term_bridge`. -/
theorem win_ne_port {n : Nat} (hn : 5 ≤ n) (s : Fin n) (j : Nat) (hj : j < topClockSpan n) :
    winSite s j ≠ certSite s (topClockSpan n - 1) := by
  intro h
  have hr3 := span_ge_three hn
  have hrn := span_lt_n hn
  unfold winSite at h
  have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + j) (by omega)
    (by omega) h.symm
  omega

/-- **A window edge is an abstract labelled edge.**

Consumer: `bridge_step`. -/
theorem window_bridge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (p : Nat) (hp1 : p + 1 < topClockSpan n) :
    ∃ c' o' ℓ' Q', LStep (topClockSpan n) (cellOf s Y) (paFlag s Y τ) (paLab s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PaAgree s (topFixedTraceNext ring C Y (winSite s p)) τ c' o' ℓ' Q' := by
  have hp : p < topClockSpan n := by omega
  refine ⟨_, _, _, _, LStep.edge p hp1, ?_⟩
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hxl : (Y.1.1 (winSite s p)).l = false := agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor (winSite s p))).l = false :=
    agent_l ring C s hg Y hreach _
  have hag := link_window ring C s Y hg hreach p hp
  have hb : winSite s p ≠ certSite s (topClockSpan n - 1) := win_ne_port hg.hn s p hp
  have hpost0 := post_step_away ring C s Y (winSite s p) τ hb
  have hpost : PostIn ring C s Y (winSite s p) τ := fun v => hpost0 _
  have hrn : ring.rightNeighbor (winSite s p) = winSite s (p + 1) := winSite_next ring s p
  have hyb : (Y.1.1 (ring.rightNeighbor (winSite s p))).beta = false := by
    rw [hrn, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad (p + 1) hp1]
    simp
  have hcp : cellOf s (topFixedTraceNext ring C Y (winSite s p)) p =
      (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).1 := by
    rw [hag p hp]; simp [edgeStep, hp1, setTwo]
  have hcq : cellOf s (topFixedTraceNext ring C Y (winSite s p)) (p + 1) =
      (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).2 := by
    rw [hag (p + 1) hp1]; simp [edgeStep, hp1, setTwo]
  have hdisj : ∀ j, j < topClockSpan n → j ≠ p → j ≠ p + 1 →
      winSite s j ≠ winSite s p ∧ winSite s j ≠ ring.rightNeighbor (winSite s p) := by
    intro j hj hjp hjq
    refine ⟨fun h => hjp (winSite_inj hg.hn s j p (by omega) (by omega) h), ?_⟩
    rw [hrn]
    intro h
    exact hjq (winSite_inj hg.hn s j (p + 1) (by omega) (by omega) h)
  have hflags : ∀ j, j < topClockSpan n →
      paFlag s (topFixedTraceNext ring C Y (winSite s p)) τ j =
        flagsEdge (topClockSpan n) (cellOf s Y) (paFlag s Y τ) p j := by
    intro j hj
    apply Bool.eq_iff_iff.2
    unfold flagsEdge
    by_cases hjp : j = p
    · subst hjp
      simp only [if_true, oldX, Bool.and_eq_true, paFlag_site]
      rw [← hcp, cell_isP_iff]
      constructor
      · rintro ⟨hj', hF⟩
        obtain ⟨hF1, hF2⟩ := (src_flag ring C s Y _ τ hxl hyl hpost).1 hF
        exact ⟨⟨hj', hF1⟩, hF2⟩
      · rintro ⟨⟨hj', hF1⟩, hF2⟩
        exact ⟨hj', (src_flag ring C s Y _ τ hxl hyl hpost).2 ⟨hF1, hF2⟩⟩
    · simp only [if_neg hjp]
      by_cases hjq : j = p + 1
      · subst hjq
        simp only [if_true, oldY, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
          paFlag_site]
        rw [← hcq]
        simp only [cell_isP_iff]
        rw [← hrn]
        have hrf := resp_flag ring hn2 C s Y (winSite s p) τ hxl hyl hyb hpost
        rw [hrf]
        constructor
        · rintro ⟨hj', hF | hF⟩
          · exact Or.inl ⟨⟨⟨hj', hF.1⟩, hF.2⟩, hF.1.1⟩
          · exact Or.inr ⟨⟨⟨⟨hp, hF.1⟩, hF.1.1⟩, hF.2.1⟩, hF.2.2⟩
        · rintro (⟨⟨⟨hj', hF⟩, hP'⟩, _⟩ | ⟨⟨⟨⟨_, hF⟩, _⟩, hn⟩, hP'⟩)
          · exact ⟨hj', Or.inl ⟨hF, hP'⟩⟩
          · exact ⟨hj, Or.inr ⟨hF, hn, hP'⟩⟩
      · simp only [if_neg hjq, paFlag_site]
        obtain ⟨hd1, hd2⟩ := hdisj j hj hjp hjq
        rw [(away_flag ring C s Y _ _ τ hd1 hd2 hpost).1]
  refine ⟨?_, hflags, ?_, ?_⟩
  · intro j hj
    rw [hag j hj]
    unfold edgeStep
    rw [if_pos hp1]
  · intro j hj hoj
    have hF : paFlag s (topFixedTraceNext ring C Y (winSite s p)) τ j = true := by
      rw [hflags j hj]; exact hoj
    by_cases hjp : j = p
    · have hF' := (paFlag_site s τ _ j).1 hF
      rw [hjp] at hF'
      obtain ⟨_, hF2⟩ := hF'
      obtain ⟨_, j2, j3⟩ := src_link ring C Y (winSite s p) hxl hyl hF2.1
      have hnq : ¬ j = p + 1 := by omega
      unfold labEdge
      rw [if_neg hnq]
      rw [hjp, paLab_site, paLab_site]
      unfold SiteLab
      rw [j2, j3]
    · by_cases hjq : j = p + 1
      · have hF' := (paFlag_site s τ _ j).1 hF
        obtain ⟨_, hF2⟩ := hF'
        rw [hjq, ← hrn] at hF2
        have hPn := hF2.1
        have hcellP : (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).2.i.isP
            = true := by
          rw [← hcq, cell_isP_iff, ← hrn]
          exact hPn
        unfold labEdge
        rw [if_pos hjq]
        rw [hjq, paLab_site, ← hrn]
        rcases resp_link ring hn2 C Y (winSite s p) hxl hyl hPn with
          ⟨d1, d2, d3⟩ | ⟨_, d2, d3, d4, d5⟩ | ⟨d1, _⟩
        · have hcond : (paFlag s Y τ (p + 1) &&
              (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).2.i.isP &&
              (cellOf s Y (p + 1)).i.isP) = true := by
            simp only [Bool.and_eq_true]
            refine ⟨⟨?_, hcellP⟩, ?_⟩
            · rw [paFlag_site]
              refine ⟨hp1, ?_⟩
              rw [← hrn]
              refine ⟨d1, ?_⟩
              have := hF2.2
              rw [d3] at this
              exact (hpost _).1 this
            · rw [cell_isP_iff, ← hrn]; exact d1
          rw [if_pos hcond, paLab_site, ← hrn]
          unfold SiteLab
          rw [d2, d3]
        · have hcond : (paFlag s Y τ (p + 1) &&
              (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).2.i.isP &&
              (cellOf s Y (p + 1)).i.isP) = false := by
            have : (cellOf s Y (p + 1)).i.isP = false := by
              rw [cell_isP_iff, ← hrn]; exact d2
            rw [this]; simp
          rw [hcond]
          simp only [Bool.false_eq_true, if_false]
          rw [paLab_site]
          unfold SiteLab
          rw [d5, d4]
        · rw [hyb] at d1; exact absurd d1 (by decide)
      · unfold labEdge
        rw [if_neg hjq]
        obtain ⟨hd1, hd2⟩ := hdisj j hj hjp hjq
        rw [paLab_site, paLab_site]
        exact (away_flag ring C s Y _ _ τ hd1 hd2 hpost).2
  · unfold paQ
    rw [exportsAfter_step_away ring C s Y _ τ hb]


/-- **The terminal edge is an abstract labelled edge.**

Consumer: `bridge_step`. -/
theorem term_bridge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) :
    ∃ c' o' ℓ' Q', LStep (topClockSpan n) (cellOf s Y) (paFlag s Y τ) (paLab s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PaAgree s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) τ c' o' ℓ' Q' := by
  have hr3 := span_ge_three hg.hn
  have hp : topClockSpan n - 1 < topClockSpan n := by omega
  have hnl : ¬ (topClockSpan n - 1 + 1 < topClockSpan n) := by omega
  refine ⟨_, _, _, _, LStep.term, ?_⟩
  have hxl : (Y.1.1 (winSite s (topClockSpan n - 1))).l = false :=
    agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor (winSite s (topClockSpan n - 1)))).l = false :=
    agent_l ring C s hg Y hreach _
  have hag := link_window ring C s Y hg hreach (topClockSpan n - 1) hp
  have hb : winSite s (topClockSpan n - 1) ≠ certSite s (topClockSpan n - 1) :=
    win_ne_port hg.hn s (topClockSpan n - 1) hp
  have hpost0 := post_step_away ring C s Y (winSite s (topClockSpan n - 1)) τ hb
  have hpost : PostIn ring C s Y (winSite s (topClockSpan n - 1)) τ := fun v => hpost0 _
  have hrn : ring.rightNeighbor (winSite s (topClockSpan n - 1)) = winSite s (topClockSpan n) := by
    rw [winSite_next]
    have : topClockSpan n - 1 + 1 = topClockSpan n := by omega
    rw [this]
  have hcp : cellOf s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1)))
      (topClockSpan n - 1) =
      (pair false true (cellOf s Y (topClockSpan n - 1)) { i := .e, c := .off }).1 := by
    rw [hag _ hp]
    unfold edgeStep
    rw [if_neg hnl]
    simp [setOne]
  have hdisj : ∀ j, j < topClockSpan n → j ≠ topClockSpan n - 1 →
      winSite s j ≠ winSite s (topClockSpan n - 1) ∧
        winSite s j ≠ ring.rightNeighbor (winSite s (topClockSpan n - 1)) := by
    intro j hj hjp
    refine ⟨fun h => hjp (winSite_inj hg.hn s j _ (by omega) (by omega) h), ?_⟩
    rw [hrn]
    intro h
    have := winSite_inj hg.hn s j (topClockSpan n) (by omega) (by omega) h
    omega
  have hflags : ∀ j, j < topClockSpan n →
      paFlag s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) τ j =
        flagsTerm (topClockSpan n) (cellOf s Y) (paFlag s Y τ) j := by
    intro j hj
    apply Bool.eq_iff_iff.2
    unfold flagsTerm
    by_cases hjp : j = topClockSpan n - 1
    · subst hjp
      simp only [if_true, oldX, Bool.and_eq_true, paFlag_site]
      rw [← hcp, cell_isP_iff]
      constructor
      · rintro ⟨hj', hF⟩
        obtain ⟨hF1, hF2⟩ := (src_flag ring C s Y _ τ hxl hyl hpost).1 hF
        exact ⟨⟨hj', hF1⟩, hF2⟩
      · rintro ⟨⟨hj', hF1⟩, hF2⟩
        exact ⟨hj', (src_flag ring C s Y _ τ hxl hyl hpost).2 ⟨hF1, hF2⟩⟩
    · simp only [if_neg hjp, paFlag_site]
      obtain ⟨hd1, hd2⟩ := hdisj j hj hjp
      rw [(away_flag ring C s Y _ _ τ hd1 hd2 hpost).1]
  refine ⟨?_, hflags, ?_, ?_⟩
  · intro j hj
    rw [hag j hj]
    unfold edgeStep
    rw [if_neg hnl]
  · intro j hj hoj
    have hF : paFlag s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) τ j = true := by
      rw [hflags j hj]; exact hoj
    by_cases hjp : j = topClockSpan n - 1
    · have hF' := (paFlag_site s τ _ j).1 hF
      rw [hjp] at hF'
      obtain ⟨_, hF2⟩ := hF'
      obtain ⟨_, j2, j3⟩ := src_link ring C Y _ hxl hyl hF2.1
      rw [hjp, paLab_site, paLab_site]
      unfold SiteLab
      rw [j2, j3]
    · obtain ⟨hd1, hd2⟩ := hdisj j hj hjp
      rw [paLab_site, paLab_site]
      exact (away_flag ring C s Y _ _ τ hd1 hd2 hpost).2
  · unfold paQ
    rw [exportsAfter_step_away ring C s Y _ τ hb]

/-- The sites of the window are away from an edge that is neither in the window nor the port.

Consumer: `frame_bridge`. -/
theorem frame_sites {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) (s e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) (j : Nat) (hj : j < topClockSpan n) :
    winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
  have hr3 := span_ge_three hn
  have h1 : winSite s j ≠ e := fun h => hnw ⟨j, hj, h.symm⟩
  have h2 : winSite s j ≠ ring.rightNeighbor e := by
    intro h
    by_cases hj0 : j = 0
    · subst hj0
      apply hb
      apply certSite_pred ring s e (topClockSpan n - 1)
      rw [← h]
      unfold winSite
      congr 1
      omega
    · apply hnw
      refine ⟨j - 1, by omega, ?_⟩
      apply certSite_pred ring s e (topClockSpan n + (j - 1))
      rw [← h]
      unfold winSite
      congr 1
      omega
  exact ⟨h1, h2⟩

/-- **An edge off the window and off the port is the identity on the labelled window.**

Consumer: `bridge_step`. -/
theorem frame_bridge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n) (e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    ∃ c' o' ℓ' Q', LStep (topClockSpan n) (cellOf s Y) (paFlag s Y τ) (paLab s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PaAgree s (topFixedTraceNext ring C Y e) τ c' o' ℓ' Q' := by
  refine ⟨_, _, _, _, LStep.frame, ?_⟩
  have hag := frame_cells ring C s hg Y e hnw hb
  have hpost0 := post_step_away ring C s Y e τ hb
  have hpost : PostIn ring C s Y e τ := fun v => hpost0 _
  refine ⟨hag, ?_, ?_, ?_⟩
  · intro j hj
    apply Bool.eq_iff_iff.2
    rw [paFlag_site, paFlag_site]
    obtain ⟨h1, h2⟩ := frame_sites ring hg.hn s e hnw hb j hj
    rw [(away_flag ring C s Y e _ τ h1 h2 hpost).1]
  · intro j hj _
    obtain ⟨h1, h2⟩ := frame_sites ring hg.hn s e hnw hb j hj
    rw [paLab_site, paLab_site]
    exact (away_flag ring C s Y e _ τ h1 h2 hpost).2
  · unfold paQ
    rw [exportsAfter_step_away ring C s Y e τ hb]

/-- **The port edge cleans or accepts the labelled packet.**  The accepted packet is the export
recorded in the same service: its operand is the label, and no other register changes its
post-anchor status, because the exported operand is the source output atom, which no input atom
equals (`Lin`).

Consumer: `bridge_step`. -/
theorem port_bridge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (hlin : Lin Y.1.2)
    (e : Fin n) (hb : e = certSite s (topClockSpan n - 1))
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none) :
    ∃ c' o' ℓ' Q', LStep (topClockSpan n) (cellOf s Y) (paFlag s Y τ) (paLab s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PaAgree s (topFixedTraceNext ring C Y e) τ c' o' ℓ' Q' := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  have hy : ring.rightNeighbor e = winSite s 0 := by
    rw [hb, rn_certSite]
    unfold winSite
    congr 1
    omega
  have hdst : ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hy]; rfl
  have hxl : (Y.1.1 e).l = false := agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Y hreach _
  have hyb : (Y.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hy, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have hresp := siteCell_responder_terminal ring hn2 C Y e hxl hyl hyb
  rw [hy] at hresp
  have hresp' : cellOf s (topFixedTraceNext ring C Y e) 0 = portClean (cellOf s Y 0) ∨
      ∃ t, cellOf s (topFixedTraceNext ring C Y e) 0 = portAccept t (cellOf s Y 0) := hresp
  have hdisj0 : ∀ j, 0 < j → j < topClockSpan n →
      winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
    intro j h0 hj
    refine ⟨?_, ?_⟩
    · intro h
      rw [hb] at h
      unfold winSite at h
      have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + j) (by omega)
        (by omega) h.symm
      omega
    · rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
  have haway : ∀ j, 0 < j → j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Y e) j = cellOf s Y j := by
    intro j h0 hj
    unfold cellOf
    exact siteCell_away ring C Y e _ (hdisj0 j h0 hj).1 (hdisj0 j h0 hj).2
  have hq := owner_qIn ring Y.1.1 e hxl hyl
  have hresp0 := topPortLiteralResponderFields ring hn2 C Y.1.1 e
  have hphys : (topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Y.1.1 e (ring.rightNeighbor e) := rfl
  have hq2 : ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (Y.1.1 e) (Y.1.1 (ring.rightNeighbor e))).1.iY := by
    rw [hphys, hresp0.1, hq.2]
  rcases hR : (traceReplay ring Y e).exported with _ | ex
  · -- no packet is accepted
    have hpostAll := post_step_noexp ring C s Y e τ hR
    have hpost : PostIn ring C s Y e τ := fun v => hpostAll _
    have hkeep : ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn.isP = true →
        (Y.1.1 (ring.rightNeighbor e)).qIn.isP = true ∧
        ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn =
          (Y.1.1 (ring.rightNeighbor e)).qIn ∧
        ((topFixedTraceNext ring C Y e).1.2.current (ring.rightNeighbor e)).comparison.input =
          (Y.1.2.current (ring.rightNeighbor e)).comparison.input := by
      intro hP
      rcases resp_link ring hn2 C Y e hxl hyl hP with ⟨d1, d2, d3⟩ | ⟨d1, _⟩ |
        ⟨d1, _, _, ex, hex, _⟩
      · exact ⟨d1, d2, d3⟩
      · rw [hyb] at d1; exact absurd d1 (by decide)
      · rw [hR] at hex; exact absurd hex (by simp)
    have hF0 : paFlag s (topFixedTraceNext ring C Y e) τ 0 = true ↔
        (paFlag s Y τ 0 = true ∧ (cellOf s (topFixedTraceNext ring C Y e) 0).i.isP = true) := by
      rw [paFlag_site, paFlag_site, cell_isP_iff]
      unfold FlagAt
      rw [← hy]
      constructor
      · rintro ⟨h0, hP, hp⟩
        obtain ⟨d1, d2, d3⟩ := hkeep hP
        rw [d3] at hp
        exact ⟨⟨h0, d1, (hpost _).1 hp⟩, hP⟩
      · rintro ⟨⟨h0, d1', hp⟩, hP⟩
        obtain ⟨d1, d2, d3⟩ := hkeep hP
        rw [d3]
        exact ⟨h0, hP, (hpost _).2 hp⟩
    have hL0 : paFlag s (topFixedTraceNext ring C Y e) τ 0 = true →
        paLab s (topFixedTraceNext ring C Y e) 0 = paLab s Y 0 := by
      intro hF
      have hF' := ((paFlag_site s τ _ 0).1 hF).2
      unfold FlagAt at hF'
      rw [← hy] at hF'
      obtain ⟨d1, d2, d3⟩ := hkeep hF'.1
      rw [paLab_site, paLab_site, ← hy]
      unfold SiteLab
      rw [d2, d3]
    have hFj : ∀ j, 0 < j → j < topClockSpan n →
        paFlag s (topFixedTraceNext ring C Y e) τ j = paFlag s Y τ j := by
      intro j h0 hj
      apply Bool.eq_iff_iff.2
      rw [paFlag_site, paFlag_site]
      obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
      rw [(away_flag ring C s Y e _ τ hd1 hd2 hpost).1]
    have hLj : ∀ j, 0 < j → j < topClockSpan n →
        paLab s (topFixedTraceNext ring C Y e) j = paLab s Y j := by
      intro j h0 hj
      obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
      rw [paLab_site, paLab_site]
      exact (away_flag ring C s Y e _ τ hd1 hd2 hpost).2
    have hQ : paQ s (topFixedTraceNext ring C Y e) τ = paQ s Y τ := by
      unfold paQ
      rw [exportsAfter_step, hR]
      simp
    rcases hresp' with hc | ⟨t, hc⟩
    · refine ⟨_, _, _, _, LStep.clean, ?_⟩
      have hflg : ∀ j, j < topClockSpan n →
          paFlag s (topFixedTraceNext ring C Y e) τ j =
            (if j = 0 then paFlag s Y τ 0 && (portClean (cellOf s Y 0)).i.isP
              else paFlag s Y τ j) := by
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [if_true]
          apply Bool.eq_iff_iff.2
          rw [hF0, Bool.and_eq_true, ← hc]
        · simp only [if_neg hj0]
          exact hFj j (by omega) hj
      refine ⟨?_, hflg, ?_, hQ⟩
      · intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [setOne, if_true]
          exact hc
        · simp only [setOne, if_neg hj0]
          exact haway j (by omega) hj
      · intro j hj hoj
        have hF : paFlag s (topFixedTraceNext ring C Y e) τ j = true := by
          rw [hflg j hj]; exact hoj
        by_cases hj0 : j = 0
        · subst hj0
          exact hL0 hF
        · exact hLj j (by omega) hj
    · by_cases hemp : cellOf s Y 0 = { i := .e, c := .off }
      · exfalso
        have hnewP : (cellOf s (topFixedTraceNext ring C Y e) 0).i.isP = true := by
          rw [hc]
          cases t <;> simp [portAccept, hemp, Inp.isP]
        rw [cell_isP_iff, ← hy] at hnewP
        obtain ⟨d1, _, _⟩ := hkeep hnewP
        have : (cellOf s Y 0).i.isP = true := by
          rw [cell_isP_iff, ← hy]; exact d1
        rw [hemp] at this
        exact absurd this (by simp [Inp.isP])
      · have hca : cellOf s (topFixedTraceNext ring C Y e) 0 = cellOf s Y 0 := by
          rw [hc]
          unfold portAccept
          rw [if_neg hemp]
        refine ⟨_, _, _, _, LStep.frame, ?_⟩
        have hflg : ∀ j, j < topClockSpan n →
            paFlag s (topFixedTraceNext ring C Y e) τ j = paFlag s Y τ j := by
          intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            apply Bool.eq_iff_iff.2
            rw [hF0]
            constructor
            · rintro ⟨h, _⟩; exact h
            · intro h
              refine ⟨h, ?_⟩
              have hF' := ((paFlag_site s τ _ 0).1 h).2
              unfold FlagAt at hF'
              rw [hca, cell_isP_iff]
              exact hF'.1
          · exact hFj j (by omega) hj
        refine ⟨?_, hflg, ?_, hQ⟩
        · intro j hj
          by_cases hj0 : j = 0
          · subst hj0; exact hca
          · exact haway j (by omega) hj
        · intro j hj hoj
          have hF : paFlag s (topFixedTraceNext ring C Y e) τ j = true := by
            rw [hflg j hj]; exact hoj
          by_cases hj0 : j = 0
          · subst hj0
            exact hL0 hF
          · exact hLj j (by omega) hj
  · -- a packet is accepted
    have hnex : (traceReplay ring Y e).exported ≠ none := by rw [hR]; simp
    have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Y.1.2.clock + 1) e
      (ring.rightNeighbor e) (Y.1.1 e) (Y.1.1 (ring.rightNeighbor e)) hxl hyl
      (Y.1.2.current e).comparison (Y.1.2.current (ring.rightNeighbor e)).comparison
    have hacc : (qiPhys (compileAdvice (ceilLogTwo n)) (Y.1.1 e)
        (Y.1.1 (ring.rightNeighbor e))).2 = true := hjoint.2.2.1 hnex
    obtain ⟨_, hyE, hyOFF, hiY⟩ := qi_acc _ _ hxl hyl hacc
    have hnewP : ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn.isP = true := by
      simp [hq2, hiY, InTok.isP]
    rcases resp_link ring hn2 C Y e hxl hyl hnewP with ⟨d1, _⟩ | ⟨d1, _⟩ |
      ⟨_, _, _, ex', hex', hqIn, hinp, htime, hsrc, hdst'⟩
    · rw [hyE] at d1; simp [InTok.isP] at d1
    · rw [hyb] at d1; exact absurd d1 (by decide)
    · have hee : ex = ex' := by
        rw [hR] at hex'
        exact Option.some.inj hex'
      rw [← hee] at hqIn hinp htime hsrc hdst'
      have hemp : cellOf s Y 0 = { i := .e, c := .off } := by
        have := siteCell_empty Y (ring.rightNeighbor e) hyE hyOFF
        rw [hy] at this
        exact this
      have hcond : τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
          ex.destination = certSite s (topClockSpan n) :=
        ⟨by omega, by rw [hsrc, hb], by rw [hdst', hdst]⟩
      have hQex : topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ =
          topClockConcreteExportsAfter s Y τ ++ [ex] := by
        rw [exportsAfter_step, hR]
        simp [hcond]
      have hmem : ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ := by
        rw [hQex]; simp
      have hopne : ex.operand ≠ none := hnone ex hmem
      have hpost : PostIn ring C s Y e τ := post_step_in_acc ring C s Y e τ hlin ex hR hopne
      have hpacc : topClockPostAnchor s (topFixedTraceNext ring C Y e) τ ex.operand :=
        post_accept ring C s Y e τ hτ hb hdst ex hR htime hsrc hdst'
      have hcellP : (cellOf s (topFixedTraceNext ring C Y e) 0).i.isP = true := by
        rw [cell_isP_iff, ← hy]; exact hnewP
      have hFlag0 : paFlag s (topFixedTraceNext ring C Y e) τ 0 = true := by
        rw [paFlag_site]
        refine ⟨by omega, ?_⟩
        unfold FlagAt
        rw [← hy]
        refine ⟨hnewP, ?_⟩
        rw [hinp]
        exact hpacc
      have hFj : ∀ j, 0 < j → j < topClockSpan n →
          paFlag s (topFixedTraceNext ring C Y e) τ j = paFlag s Y τ j := by
        intro j h0 hj
        apply Bool.eq_iff_iff.2
        rw [paFlag_site, paFlag_site]
        obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
        rw [(away_flag ring C s Y e _ τ hd1 hd2 hpost).1]
      have hLj : ∀ j, 0 < j → j < topClockSpan n →
          paLab s (topFixedTraceNext ring C Y e) j = paLab s Y j := by
        intro j h0 hj
        obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
        rw [paLab_site, paLab_site]
        exact (away_flag ring C s Y e _ τ hd1 hd2 hpost).2
      rcases hresp' with hc | ⟨t, hc⟩
      · exfalso
        rw [hc, hemp] at hcellP
        simp [portClean, Inp.isP] at hcellP
      · refine ⟨_, _, _, _, LStep.accept t (ex.operand, InTok.P ex.value ex.tail) hemp, ?_⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            simp only [setOne, if_true]
            exact hc
          · simp only [setOne, if_neg hj0]
            exact haway j (by omega) hj
        · intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            simp only [if_true]
            exact hFlag0
          · simp only [if_neg hj0]
            exact hFj j (by omega) hj
        · intro j hj hoj
          by_cases hj0 : j = 0
          · subst hj0
            show paLab s (topFixedTraceNext ring C Y e) 0 = (ex.operand, InTok.P ex.value ex.tail)
            rw [paLab_site, ← hy]
            unfold SiteLab
            rw [hinp, hqIn]
          · simp only [if_neg hj0]
            exact hLj j (by omega) hj
        · unfold paQ
          rw [hQex]
          simp

/-- **Every edge is an abstract labelled edge.**

Consumer: `linv_step`. -/
theorem bridge_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (e : Fin n)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none) :
    ∃ c' o' ℓ' Q', LStep (topClockSpan n) (cellOf s Y) (paFlag s Y τ) (paLab s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PaAgree s (topFixedTraceNext ring C Y e) τ c' o' ℓ' Q' := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  by_cases ha : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := ha
    by_cases hp1 : p + 1 < topClockSpan n
    · exact window_bridge ring C s hg τ Y hreach p hp1
    · have hpe : p = topClockSpan n - 1 := by omega
      subst hpe
      exact term_bridge ring C s hg τ Y hreach
  · by_cases hb : e = certSite s (topClockSpan n - 1)
    · exact port_bridge ring C s hg τ Y hreach hτ (lin_reached ring C hn2 Y hreach) e hb hnone
    · exact frame_bridge ring C s hg τ Y e ha hb

/-- The labelled window of a state agrees with an abstract labelled window that satisfies the
invariant.

Consumer: `linv_step`. -/
theorem linv_of_agree {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (c' : Nat → Cell) (o' : Nat → Bool) (ℓ' : Nat → PaLabel n) (Q' : List (PaLabel n))
    (hag : PaAgree s Z τ c' o' ℓ' Q') (h : LInv (topClockSpan n) Q' c' o' ℓ') :
    LInv (topClockSpan n) (paQ s Z τ) (cellOf s Z) (paFlag s Z τ) (paLab s Z) := by
  obtain ⟨hc, hf, hl, hq⟩ := hag
  obtain ⟨hP, hB, k, hk, hlist⟩ := h
  refine ⟨?_, ?_, k, ?_, ?_⟩
  · intro j hj hoj
    rw [hf j hj] at hoj
    rw [hc j hj]
    exact hP j hj hoj
  · intro j i hj hi hoj hob
    rw [hf j hj] at hoj
    rw [hc i hi] at hob
    exact hB j i hj hi hoj hob
  · rw [hq]; exact hk
  · rw [hq, ← hlist]
    exact ordLab_congr _ _ _ _ _ (fun j hj => hf j hj)
      (fun j hj hoj => hl j hj (by rw [← hf j hj]; exact hoj))

/-- **The labelled window invariant is preserved by every edge** of a reached state, whenever
the exports after `τ` have operands.

Consumer: `linv_word`. -/
theorem linv_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (e : Fin n)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none)
    (h : LInv (topClockSpan n) (paQ s Y τ) (cellOf s Y) (paFlag s Y τ) (paLab s Y)) :
    LInv (topClockSpan n) (paQ s (topFixedTraceNext ring C Y e) τ)
      (cellOf s (topFixedTraceNext ring C Y e)) (paFlag s (topFixedTraceNext ring C Y e) τ)
      (paLab s (topFixedTraceNext ring C Y e)) := by
  obtain ⟨c', o', ℓ', Q', hst, hag⟩ := bridge_step ring C s hg τ Y hreach hτ e hnone
  have hr3 := span_ge_three hg.hn
  exact linv_of_agree s _ τ c' o' ℓ' Q' hag (lstep_inv _ (by omega) _ _ _ _ _ _ _ _ h hst)

end MarkedCells
end L3

#print axioms L3.MarkedCells.window_bridge
#print axioms L3.MarkedCells.term_bridge
#print axioms L3.MarkedCells.port_bridge
#print axioms L3.MarkedCells.frame_bridge
#print axioms L3.MarkedCells.linv_step
