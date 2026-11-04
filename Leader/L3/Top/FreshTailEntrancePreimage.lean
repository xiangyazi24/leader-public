import Leader.L3.Top.FreshTailEntrance

/-!
Q7c P.3 J5 entrance: historical comparison-sample preimage.

A recorded sample is an actual member of the fixed trace's audit
frames. The unique new frame of a snoc step either contains the
sample, in which case the comparison replay identifies the OLD U
source, or the witness was already in the preceding audit.

Consumer: the historical source-zero input to
topFreshTailEntranceOfFactorization in TopClockBundle.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A comparison replay can issue a sample only in its OLD
unread-output branch. This inverts the literal sample field of
digitLaneReplay, without making any assumption about inherited
ghost registers.

Consumer: topFreshTailEntranceCurrentFrameSampleUnread. -/
private theorem topFreshTailEntranceReplaySampleUnread
    {c : Compiled} {n : Nat}
    (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (sigma : DigitSample c n)
    (hsample :
      (digitLaneReplay .comparison time source destination
        x y gx gy).sample = some sigma) :
    x.out = .U := by
  cases hxo : x.out with
  | E =>
      cases hxl : x.leader <;>
      cases hyl : y.leader <;>
      cases hxm : x.marker <;>
      cases hym : y.marker <;>
      cases hyo : y.out <;>
      simp [digitLaneReplay, hxo, hxl, hyl, hxm, hym, hyo,
        OutTok.isD, OutTok.isU, OutTok.isE] at hsample
  | U =>
      rfl
  | D value tail =>
      cases hxl : x.leader <;>
      cases hyl : y.leader <;>
      cases hym : y.marker <;>
      cases hyo : y.out <;>
      simp [digitLaneReplay, hxo, hxl, hyl, hym, hyo,
        OutTok.isD, OutTok.isU, OutTok.isE] at hsample

/-- If the newly prepended selected frame issued a comparison
sample, the OLD physical source of that service held U.
This is the physical/audit interface used by the historical
sample-preimage induction.

Consumer: topFreshTailEntranceSamplePreimage. -/
private theorem topFreshTailEntranceCurrentFrameSampleUnread
    {n : Nat} (ring : DirectedRing n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hsample :
      (topFreshTailPostAnchorCurrentFrame ring Z e).receipt.comparison.sample =
        some sigma) :
    (Z.1.1 e).qOut = .U := by
  have hu :=
    topFreshTailEntranceReplaySampleUnread
      (Z.1.2.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison
        (piD Z.1.1 e) (piD Z.1.1 e).word.beta)
      (digitLaneView .comparison
        (piD Z.1.1 (ring.rightNeighbor e))
        (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
      (Z.1.2.current e).comparison
      (Z.1.2.current (ring.rightNeighbor e)).comparison
      sigma (by exact hsample)
  change (Z.1.1 e).qOut = .U at hu
  exact hu

/-- A recorded source-zero comparison sample in a reached fixed
trace has a real historical source-zero service preimage. The
service was an OLD U-to-sample service, not a marker bootstrap,
transport, blocked D, or port receipt. Its audit stamp is
exactly the predecessor clock plus one.

This is the sample half of S in Q7c P.3 J5.
Consumer: topFreshTailEntranceOfFactorization in TopClockBundle. -/
theorem topFreshTailEntranceSamplePreimage
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Y : TopFixedTraceState n) (w : List (Fin n))
    (hY : Y = topFixedTraceRun ring C w)
    (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hrecord : DigitRecordedSample Y.1.2 sigma)
    (hlane : sigma.id.lane = .comparison)
    (hsite : sigma.id.site = certSite s 0) :
    ∃ u v : List (Fin n),
      w = (u ++ [certSite s 0]) ++ v ∧
      ((topFixedTraceRun ring C u).1.1
        (certSite s 0)).qOut = .U ∧
      sigma.id.time =
        (topFixedTraceRun ring C u).1.2.clock + 1 := by
  rw [hY] at hrecord
  have hreverse :
      ∀ r : List (Fin n),
        ∀ tau : DigitSample (compileAdvice (ceilLogTwo n)) n,
          DigitRecordedSample
            (topFixedTraceRun ring C r.reverse).1.2 tau →
          tau.id.lane = .comparison →
          tau.id.site = certSite s 0 →
          ∃ u v : List (Fin n),
            r.reverse = (u ++ [certSite s 0]) ++ v ∧
            ((topFixedTraceRun ring C u).1.1
              (certSite s 0)).qOut = .U ∧
            tau.id.time =
              (topFixedTraceRun ring C u).1.2.clock + 1 := by
    intro r
    induction r with
    | nil =>
        intro tau hrec hl hs
        obtain ⟨frame, hmem, _, _, _, _⟩ := hrec
        change frame ∈
          ([] : List (DigitFrame
            (compileAdvice (ceilLogTwo n)) n)) at hmem
        cases hmem
    | cons edge rest ih =>
        intro tau hrec hl hs
        rw [List.reverse_cons] at hrec ⊢
        rw [topFreshTailFifoRunSnoc ring C rest.reverse edge] at hrec
        obtain ⟨frame, hmem, htime, hsource, hreceipt, hvalue⟩ :=
          hrec
        rw [topFreshTailPostAnchorCurrentFrameNext] at hmem
        rcases List.mem_cons.mp hmem with hnew | hold
        · have hedge : edge = certSite s 0 := by
            rw [hnew] at hsource
            change edge = tau.id.site at hsource
            exact hsource.trans hs
          have hnewSample :
              (topFreshTailPostAnchorCurrentFrame ring
                (topFixedTraceRun ring C rest.reverse)
                edge).receipt.comparison.sample = some tau := by
            rw [hnew, hl] at hreceipt
            exact hreceipt
          have hunread :=
            topFreshTailEntranceCurrentFrameSampleUnread
              ring (topFixedTraceRun ring C rest.reverse)
              edge tau hnewSample
          have hstamp :
              tau.id.time =
                (topFixedTraceRun ring C rest.reverse).1.2.clock + 1 := by
            rw [hnew] at htime
            change
              (topFixedTraceRun ring C rest.reverse).1.2.clock + 1 =
                tau.id.time at htime
            exact htime.symm
          refine ⟨rest.reverse, [], ?_, ?_, hstamp⟩
          · rw [hedge]
            simp only [List.append_nil]
          · rw [← hedge]
            exact hunread
        · have hrecordOld :
              DigitRecordedSample
                (topFixedTraceRun ring C rest.reverse).1.2 tau := by
            exact ⟨frame, hold, htime, hsource, hreceipt, hvalue⟩
          obtain ⟨u, v, hfactor, hunread, hstamp⟩ :=
            ih tau hrecordOld hl hs
          refine ⟨u, v ++ [edge], ?_, hunread, hstamp⟩
          rw [hfactor]
          simp only [List.append_assoc]
  have hresult := hreverse w.reverse sigma
  rw [List.reverse_reverse] at hresult
  exact hresult hrecord hlane hsite

end L3
#print axioms L3.topFreshTailEntranceSamplePreimage
