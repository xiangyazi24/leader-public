import Leader.L4.RearMovement
import Leader.L4.RearRefillTrack

namespace L4.RearTrace
open TaggedTrace RearFrontStock

/-- The actual clock's filled-advance count, retaining one observer across
the entire raw word. Initial/final/terminal-pin events credit zero. -/
def globalFilled {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → Nat
  | [] => 0
  | e::w => eventFilled (clockEvent i s e) + globalFilled i (rearAdvance i s e) w

/-- Per-mark facts used in splitting a physical trace into one ghost block.
There is no hypothesis on the number of ghost marks. -/
def GhostSplitFacts {p c n : Nat} (i : Fin n) (s : Observer p c n) :
    List (Fin n) → Prop
  | [] => True
  | e::w =>
    LocalPhaseFacts i s e ∧
    (s.phase = .ghost → ∀ r, s.rear = some r → (s.tag.config r).leader = false) ∧
    GhostSplitFacts i (rearAdvance i s e) w

private theorem filled_before_or_after {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (h : s.phase ≠ .ghost) : eventFilled (clockEvent i s e) = 0 := by
  simp [clockEvent,h,eventFilled]

private theorem filled_at_pin {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (h : (rearAdvance i s e).phase = .pinned) : eventFilled (clockEvent i s e) = 0 := by
  by_cases hg : s.phase = .ghost
  · cases hr : s.rear with
    | none => simp [clockEvent,hg,hr,eventFilled]
    | some r =>
      by_cases he : e = rearBond i s <;> cases hPay : payer (s.tag.config (predecessor r)) <;>
        first | (simp [clockEvent,hg,hr,h,eventFilled,if_pos he,hPay]; done) | simp [clockEvent,hg,hr,h,eventFilled,if_neg he,hPay]
  · exact filled_before_or_after i e s hg

private theorem cast_filled_ghost {p c n : Nat} (i e : Fin n) (s : Observer p c n)
    (hg : s.phase = .ghost) (hp : (rearAdvance i s e).phase ≠ .pinned) :
    (eventFilled (clockEvent i s e) : Int) = filledRearMark s e := by
  cases hr : s.rear with
  | none => simp [clockEvent,hg,hr,eventFilled,filledRearMark]
  | some r =>
    have hu : (rearAdvance i s e).phase ≠ Phase.pinned := hp
    cases hs : rearShifts s e r
    · by_cases he : e = rearBond i s <;> cases hPay : payer (s.tag.config (predecessor r)) <;>
        first | (simp [clockEvent,hg,hr,eventFilled,filledRearMark,hs,if_pos he,hPay]; done) | simp [clockEvent,hg,hr,eventFilled,filledRearMark,hs,if_neg he,hPay]
    · cases hS : (s.tag.config r).stock <;>
        simp [clockEvent,hg,hr,eventFilled,filledRearMark,hs,hu,hS,stockBit]

/-- On a certified ghost block, the clock's integer filled count is
exactly the physical stock departure count. -/
theorem globalFilled_eq_departures {p c n : Nat} (i : Fin n) (s : Observer p c n)
    (w : List (Fin n)) (h : GhostPremarks i s w) :
    (globalFilled i s w : Int) = filledRearDepartures i s w := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    rw [globalFilled, Int.natCast_add, filledRearDepartures,
      cast_filled_ghost i e s h.1 h.2.2.1, ih (rearAdvance i s e) h.2.2.2]

private theorem step_final_or_pin {a b : Phase} {dx : Nat}
    (h : PhaseStep a b dx) (ha : a = .finalLeader ∨ a = .pinned) :
    b = .finalLeader ∨ b = .pinned := by
  cases h <;> simp_all

private theorem step_ghost {a b : Phase} {dx : Nat}
    (h : PhaseStep a b dx) (ha : a = .ghost) :
    b = .ghost ∨ b = .finalLeader ∨ b = .pinned := by
  cases h <;> simp_all

private theorem filled_after_ghost {p c n : Nat} (i : Fin n) (s : Observer p c n)
    (w : List (Fin n)) (h : GhostSplitFacts i s w)
    (hp : s.phase = .finalLeader ∨ s.phase = .pinned) : globalFilled i s w = 0 := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    obtain ⟨dx,_,_,hph⟩ := phase_step_of_local i e s h.1
    have hn : s.phase ≠ .ghost := by rcases hp with hp|hp <;> simp [hp]
    rw [globalFilled,filled_before_or_after i e s hn,
      ih (rearAdvance i s e) h.2.2 (step_final_or_pin hph hp)]

private theorem filled_in_ghost_prefix {p c n : Nat} (i : Fin n) (s : Observer p c n)
    (w : List (Fin n)) (h : GhostSplitFacts i s w) (hp : s.phase = .ghost) :
    ∃ g rest, w = g++rest ∧ GhostPremarks i s g ∧
      globalFilled i s w = globalFilled i s g := by
  induction w generalizing s with
  | nil => exact ⟨[],[],rfl,trivial,rfl⟩
  | cons e w ih =>
    let t := rearAdvance i s e
    obtain ⟨dx,_,_,hs⟩ := phase_step_of_local i e s h.1
    rcases step_ghost hs hp with ht | ht | ht
    · obtain ⟨g,rest,hW,hG,hE⟩ := ih t h.2.2 ht
      refine ⟨e::g,rest,congrArg (List.cons e) hW,⟨hp,h.2.1 hp,?_,hG⟩,?_⟩
      · rw [ht]; decide
      · rw [globalFilled,globalFilled,hE]
    · refine ⟨[e],w,rfl,⟨hp,h.2.1 hp,?_,trivial⟩,?_⟩
      · rw [ht]; decide
      · rw [globalFilled,globalFilled,filled_after_ghost i t w h.2.2 (Or.inl ht)]
        rfl
    · refine ⟨[],e::w,rfl,trivial,?_⟩
      change eventFilled (clockEvent i s e) + globalFilled i t w = 0
      rw [filled_at_pin i e s ht,filled_after_ghost i t w h.2.2 (Or.inr ht)]

/-- All charged filled events lie in the same contiguous physical ghost
block, retaining the mark of a terminal birth and omitting a terminal pin. -/
theorem globalFilled_split {p c n : Nat} (i : Fin n) (s : Observer p c n)
    (w : List (Fin n)) (h : GhostSplitFacts i s w) :
    ∃ before g after, w = before ++ g ++ after ∧
      GhostPremarks i (rearFold i s before) g ∧
      globalFilled i s w = globalFilled i (rearFold i s before) g := by
  induction w generalizing s with
  | nil => exact ⟨[],[],[],rfl,trivial,rfl⟩
  | cons e w ih =>
    by_cases hp : s.phase = .ghost
    · obtain ⟨g,after,hw,hg,he⟩ := filled_in_ghost_prefix i s (e::w) h hp
      exact ⟨[],g,after,hw,hg,he⟩
    · obtain ⟨before,g,after,hw,hg,he⟩ := ih (rearAdvance i s e) h.2.2
      refine ⟨e::before,g,after,congrArg (List.cons e) hw,hg,?_⟩
      rw [globalFilled,filled_before_or_after i e s hp, Nat.zero_add,he]
      rfl


/-- Global filled count from the exact section-2 clock. The local phase
facts are the only remaining account premise, not a stock premise. -/
theorem globalFilled_bound_of_facts {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (i : Fin n) (w : List (Fin n)) (hm : MCOV x)
    (hnd : (∃ j : Fin n, (x j).mark = true)) (ha : ¬ ended (track (init x i) w))
    (h : GhostSplitFacts i (rearInit x i) w) :
    globalFilled i (rearInit x i) w ≤ 2*n+1 := by
  obtain ⟨before,g,after,hw,hg,he⟩ := globalFilled_split i (rearInit x i) w h
  change GhostPremarks i (rearTrack x i before) g at hg
  change globalFilled i (rearInit x i) w =
    globalFilled i (rearTrack x i before) g at he
  rw [he]
  cases g with
  | nil => simp [globalFilled]
  | cons e g =>
    have hphase : (rearTrack x i before).phase = .ghost := hg.1
    have haG : ¬ ended (track (init x i) (before++(e::g))) := by
      intro hD
      apply ha
      rw [hw, track_append]
      exact ended_run _ after hD
    have haB : ¬ ended (rearTrack x i before).tag := by
      intro hh
      apply haG
      rw [track_append,← rearTrack_tag]
      exact ended_run _ (e::g) hh
    obtain ⟨b,hb⟩ : ∃ b, (rearTrack x i before).tag.carrier = some b := by
      cases hs : (rearTrack x i before).tag.carrier
      · exact False.elim (haB hs)
      · exact ⟨_,rfl⟩
    obtain ⟨d0,_,hgeom⟩ := concrete_geometry hn x i b before hm hnd hb
    cases hgeom with
    | pinned hp _ => rw [hphase] at hp; contradiction
    | tracking _ d hr hf _ =>
      have hF := filledRearDepartures_bound hn x i before (e::g) hm hnd haG b d hb hr hf hg
      have hEq := globalFilled_eq_departures i (rearTrack x i before) (e::g) hg
      omega

end L4.RearTrace

#print axioms L4.RearTrace.globalFilled_split
#print axioms L4.RearTrace.globalFilled_eq_departures
#print axioms L4.RearTrace.globalFilled_bound_of_facts

namespace L4.RearTrace
open TaggedTrace

/-- Covered survival supplies the literal phase facts at every premark,
including the physical nonleader test inside the ghost phase. -/
theorem ghostSplitFacts_of_live {p c n : Nat} {x : Config p c n} {i : Fin n}
    {w : List (Fin n)} (h : LiveCoveredTrace x i w) :
    GhostSplitFacts i (rearInit x i) w := by
  have loop (rest prior : List (Fin n)) (hL : LiveCoveredTrace x i (prior++rest)) :
      GhostSplitFacts i (rearTrack x i prior) rest := by
    induction rest generalizing prior with
    | nil => trivial
    | cons e rest ih =>
      have hB : LiveCoveredTrace x i prior := covered_prefix hL
      have hOne : LiveCoveredTrace x i (prior++[e]) := by
        apply covered_prefix (v := rest)
        simpa only [List.append_assoc,List.singleton_append] using hL
      have hAlive : ¬ ended (rearTrack x i prior).tag := by
        rw [rearTrack_tag]
        exact hB.2.2.2.2.2.2
      obtain ⟨b,hb⟩ : ∃ b, (rearTrack x i prior).tag.carrier = some b := by
        cases hB : (rearTrack x i prior).tag.carrier
        · exact False.elim (hAlive hB)
        · exact ⟨_,rfl⟩
      have hP := phasePhysical_track x i b prior hB hb
      refine ⟨literal_phaseFacts hOne, ?_, ?_⟩
      · intro hG r hr
        obtain ⟨_,z,hz,hl⟩ := hP.2.2.1 hG
        exact (Option.some.inj (hz.symm.trans hr)) ▸ hl
      · have heq : rearTrack x i (prior++[e]) = rearAdvance i (rearTrack x i prior) e := by
          unfold rearTrack
          rw [rearFold_append]
          rfl
        rw [← heq]
        exact ih (prior++[e]) (by simpa only [List.append_assoc,List.singleton_append] using hL)
  exact loop w [] h

/-- The all-word rear service clock charges at most 2n+1 filled advances,
with no abstract phase or stock premise. -/
theorem globalFilled_bound_of_live {p c n : Nat} {x : Config p c n} {i : Fin n}
    {w : List (Fin n)} (h : LiveCoveredTrace x i w) :
    globalFilled i (rearInit x i) w ≤ 2*n+1 := by
  exact globalFilled_bound_of_facts h.2.2.1 x i w h.2.2.2.2.1
    h.2.2.2.1 h.2.2.2.2.2.2 (ghostSplitFacts_of_live h)

end L4.RearTrace

#print axioms L4.RearTrace.ghostSplitFacts_of_live
#print axioms L4.RearTrace.globalFilled_bound_of_live

namespace L4.RearTrace

/-- The chronological clock-event list and the streaming global count
charge precisely the same filled advances. -/
theorem globalFilled_eq_event_sum {p c n : Nat} (i : Fin n) (s : Observer p c n)
    (w : List (Fin n)) :
    globalFilled i s w = ((clockEvents i s w).map eventFilled).sum := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih => simp [globalFilled,clockEvents,ih]

/-- Filled term in the literal refill inequality, already in event-list form. -/
theorem eventFilled_sum_le_twice_size_add_one {p c n : Nat}
    {x : Config p c n} {i : Fin n} {w : List (Fin n)} (h : TaggedTrace.LiveCoveredTrace x i w) :
    ((clockEvents i (rearInit x i) w).map eventFilled).sum ≤ 2*n+1 := by
  rw [← globalFilled_eq_event_sum]
  exact globalFilled_bound_of_live h

end L4.RearTrace

#print axioms L4.RearTrace.eventFilled_sum_le_twice_size_add_one
