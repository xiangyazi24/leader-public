import Leader.L4.RearPhaseBudget
import Leader.L4.RearSweptTrack

/-!
# Literal phase movement bound
Initial and protected leader phases do not supply arbitrarily many rear
steps. The only non-ghost displacement outside the initial allowance
can be the actual loss and pinning marks.
-/

namespace L4.RearTrace
open TaggedTrace

theorem localPhaseFacts_of_physical {p c n d0 : Nat} (hn : 4 ≤ n)
    (i e b : Fin n) (s : Observer p c n)
    (hm : MCOV s.tag.config) (hb : s.tag.carrier = some b)
    (hg : LiveGeometry d0 s b) (hS : LiveSweep s b) (hP : PhasePhysical s b) :
    LocalPhaseFacts i s e := by
  constructor
  · intro hIL hIL'
    cases hg with
    | pinned hp hmark => rw [hp] at hIL; contradiction
    | tracking hp d hr hf hgap =>
      let r := back b d
      let t := rearAdvance i s e
      have hF := post_fields i e r s hr
      have hpin : (s.phase == Phase.pinned) = false := by rw [hIL]; rfl
      dsimp only at hF
      by_cases hs : rearShifts s e r = true
      · exfalso
        have hs' : e = predecessor r :=
          ((paid_moves_rear_iff hm i e r s rfl).mp hs).1
        simp only [hpin,Bool.not_false,Bool.true_and,hs,if_true] at hF
        by_cases hd0 : d = 0
        · have hco : s.tag.carrier = s.rear := by rw [hb,hr,hd0,back_zero]
          have hp : t.phase = .pinned := hF.2.2.trans
            ((phaseAfter_pinned _ _ _ _).mpr (Or.inr ⟨rfl,hco⟩))
          rw [hIL'] at hp
          contradiction
        · have hn : (t.tag.config (rightNeighbor r)).leader = false := by
            change ((rearAdvance i s e).tag.config (rightNeighbor r)).leader = false
            rw [rearAdvance_tag,projection_step,hs']
            exact rear_shift_landing_nonleader (by omega) hm b hf (by omega)
          have hnot : s.tag.carrier ≠ s.rear := by
            intro he
            have he' := Option.some.inj (hb.symm.trans (he.trans hr))
            have hx : (s.tag.config (predecessor (back b 0))).mark = true := by
              rw [back_zero,he']; exact hf.marked
            exact hf.before 0 (by omega) hx
          have hnot' : (s.tag.carrier == s.rear) = false := by
            cases hc : (s.tag.carrier == s.rear)
            · rfl
            · exact (hnot (beq_iff_eq.mp hc)).elim
          have hp : t.phase = .ghost := by
            change (rearAdvance i s e).phase = .ghost
            rw [hF.2.2]
            have hLeader : ((advance s.tag e).config (rightNeighbor r)).leader = false := by
              change ((rearAdvance i s e).tag.config (rightNeighbor r)).leader = false at hn
              rwa [rearAdvance_tag] at hn
            simp [phaseAfter,hIL,hnot',hLeader,show (Phase.initialLeader == Phase.pinned) = false from rfl]
          rw [hIL'] at hp
          contradiction
      · have hs' := Bool.eq_false_iff.mpr hs
        simpa only [hpin,Bool.not_false,Bool.true_and,hs',Bool.toNat_false,Nat.add_zero] using hF.2.1
  · intro hFinal
    obtain ⟨hp,hcut,d,hd,hf,hr,hL,hshield,hno⟩ := hP.2.2.2 hFinal
    have hdn : d ≤ s.tag.moveCount := by have := hf.lt; omega
    have hs := (hS.resolve_left (by rw [hp]; exact Phase.noConfusion)) d hf
    exact (final_rear_protected hn i e b s hm hr hf hs hd hdn hp hL hshield hno).2.2.1

theorem covered_prefix {p c n : Nat} {x : Config p c n} {i : Fin n}
    {u v : List (Fin n)} (h : LiveCoveredTrace x i (u++v)) :
    LiveCoveredTrace x i u := by
  obtain ⟨hp,hc,hn,hnd,hm,hc',hl⟩ := h
  refine ⟨hp,hc,hn,hnd,hm,hc',?_⟩
  intro he
  apply hl
  rw [track_append]
  exact ended_run _ _ he

theorem covered_rear_state {p c n : Nat} {x : Config p c n} {i : Fin n}
    {w : List (Fin n)} (h : LiveCoveredTrace x i w) :
    MCOV (rearTrack x i w).tag.config := by
  rw [rearTrack_tag,projection_run]
  exact (cover_run h.2.2.1 x ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩ w).1

theorem literal_phaseFacts {p c n : Nat} {x : Config p c n} {i e : Fin n}
    {w : List (Fin n)} (h : LiveCoveredTrace x i (w++[e])) :
    LocalPhaseFacts i (rearTrack x i w) e := by
  have hh := covered_prefix h
  have ha : ¬ ended (rearTrack x i w).tag := by
    rw [rearTrack_tag]
    exact hh.2.2.2.2.2.2
  cases hb : (rearTrack x i w).tag.carrier with
  | none => exact (ha hb).elim
  | some b =>
    obtain ⟨d,hg,hs⟩ := liveSweep_track x i b w hh hb
    have hP := phasePhysical_track x i b w hh hb
    exact localPhaseFacts_of_physical h.2.2.1 i e b _ (covered_rear_state hh) hb hg hs hP

theorem literal_ghostMovement_bound {p c n : Nat} (x : Config p c n) (i : Fin n)
    (w : List (Fin n)) (h : LiveCoveredTrace x i w) :
    (rearTrack x i w).tag.moveCount ≤ 5*n + ghostAdvances i (rearInit x i) w := by
  obtain ⟨hp,hc,hn,hnd,hm,hc',hl⟩ := h
  obtain ⟨d0,hd,hr⟩ := rearInit_has_nearest i hnd
  have hi : (rearInit x i).tag.carrier = some i := by
    by_cases hb : ((x i).bullet == .live) = true
    · simp [rearInit,init,hb]
    · exfalso; exact hl (ended_run _ w (by simp [init,ended,hb]))
  have hg : LiveGeometry d0 (rearInit x i) i :=
    .tracking (by change Phase.initial ≠ Phase.pinned; decide) d0 hr hd (by simp [rearInit,init])
  have hh (u : List (Fin n)) (e : Fin n) :
      ¬ ended (rearFold i (rearInit x i) (u++[e])).tag →
      LocalPhaseFacts i (rearFold i (rearInit x i) u) e := by
    intro hu
    change ¬ ended (rearTrack x i (u++[e])).tag at hu
    rw [rearTrack_tag] at hu
    exact literal_phaseFacts (x := x) (i := i) (e := e) (w := u) ⟨hp,hc,hn,hnd,hm,hc',hu⟩
  have hA : ¬ ended (rearFold i (rearInit x i) w).tag := by
    change ¬ ended (rearTrack x i w).tag
    rw [rearTrack_tag]; exact hl
  have hN : PhaseCost d0 0 (rearInit x i) := by
    change 0 < 2*n
    omega
  have hmove : (rearInit x i).tag.moveCount ≤ 5*n+0 := by change 0 ≤ 5*n+0; omega
  have hout := (phase_account_fold hn i (rearInit x i) w hm i hi hd.lt hg hN hmove hh hA).2
  simpa only [rearTrack,Nat.zero_add] using hout

end L4.RearTrace

#print axioms L4.RearTrace.localPhaseFacts_of_physical

#print axioms L4.RearTrace.literal_phaseFacts
#print axioms L4.RearTrace.literal_ghostMovement_bound
