import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Safety.CorrectedFormulation
import Leader.Wu.Scheduler.BoundedToRepairedLift
import Leader.Wu.Safety.ReversedPathWriterLeaders
import Leader.Wu.Safety.ReversedPathWriterFrame
import Leader.Wu.Safety.ReversedPathPrefixFrame
import Leader.Wu.Safety.ReversedPathCleanFrame
import Leader.Wu.Safety.ReversedPathMiddleQuiet
import Leader.Wu.Safety.ReversedPathCompareFrame
import Leader.Wu.Safety.ReversedPathSuppressEliminateFrame
import Leader.Wu.Safety.ReversedPathViewAdapters

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4Reversed

open PopulationProtocol

private theorem hψ2 : 0 < 2 := by decide

def ring4 : DirectedRing 4 := PPLLCounterexample.ring4

def Raw : PopulationProtocol := PPLLRepair.protocol hψ2 10

/-- Reversed main-path seed.  The path label is opposite
    to the host label at each site; the live bullet is parked at site 1. -/
def reversedPathSafeRaw : Fin 4 → AgentState 2
  | 0 =>
      { PPLLCounterexample.state2 0 true .congest with
          path := .some 1 0
          shield := true }
  | 1 =>
      { PPLLCounterexample.state2 1 false .congest with
          path := .some 0 0
          bullet := 2
          shield := true }
  | 2 =>
      { PPLLCounterexample.state2 0 false .congest with
          path := .some 1 0
          shield := true }
  | _ =>
      { PPLLCounterexample.state2 1 false .congest with
          path := .some 0 0
          shield := true }

/-- First falsifiable gate: every one of the four directed ring edges preserves
    the physical leader vector at this seed.  This is not yet a reachability
    closure theorem. -/
theorem reversedPathSafeRaw_oneStep_frozen :
    ∀ e i : Fin 4,
      (Raw.step ring4 reversedPathSafeRaw e i).leader =
        (reversedPathSafeRaw i).leader := by
  decide +kernel

#print axioms reversedPathSafeRaw_oneStep_frozen

 /-- The protected part of an even site.  Auxiliary clock and writer fields
    are intentionally left open; they do not determine the leader output. -/
def EvenSite (leader : Bool) (s : AgentState 2) : Prop :=
  s.leader = leader ∧ s.label = 0 ∧
  s.probe = false ∧ s.phase = false ∧ s.path = .some 1 0 ∧
  s.path2 = none ∧ s.p = false ∧ s.p_carry = false ∧
  (s.state = .congest ∨ s.state = .lock) ∧ s.signal_B = 0 ∧
  s.bullet = 0 ∧ s.shield = true ∧
  (s.path4 = none ∨ s.path4 = some (1, 1)) ∧ s.path5 = none

/-- The protected part of an odd site. -/
def OddSite (bullet : Fin 3) (s : AgentState 2) : Prop :=
  s.leader = false ∧ s.label = 1 ∧
  s.probe = false ∧ s.phase = false ∧ s.path = .some 0 0 ∧
  s.path2 = none ∧ s.p = false ∧ s.p_carry = false ∧
  s.state = .congest ∧ s.signal_B = 0 ∧ s.bullet = bullet ∧
  s.shield = true ∧ s.path4 = none ∧
  (s.path5 = none ∨ s.path5 = some (0, 1))

def ReversedCore (C : Fin 4 → AgentState 2) : Prop :=
  EvenSite true (C 0) ∧ OddSite 2 (C 1) ∧
  EvenSite false (C 2) ∧ OddSite 0 (C 3)

theorem reversedPathSafeRaw_core : ReversedCore reversedPathSafeRaw := by
  simp [ReversedCore, EvenSite, OddSite, reversedPathSafeRaw,
    PPLLCounterexample.state2]

#print axioms reversedPathSafeRaw_core

open PPLL PPLLRepair

private structure WriterFrame (u v : AgentState 2) : Prop where
  label : u.label = v.label
  probe : u.probe = v.probe
  phase : u.phase = v.phase
  path : u.path = v.path
  path2 : u.path2 = v.path2
  p : u.p = v.p
  p_carry : u.p_carry = v.p_carry
  state : u.state = v.state
  signal_B : u.signal_B = v.signal_B
  bullet : u.bullet = v.bullet
  shield : u.shield = v.shield
  path4 : u.path4 = v.path4
  path5 : u.path5 = v.path5

private theorem writerFrame_of_view
    {u v : AgentState 2}
    (h : ZZSafeN4WriterViewGPT.WriterProtectedView.ofState u =
      ZZSafeN4WriterViewGPT.WriterProtectedView.ofState v) :
    WriterFrame u v := by
  exact
    { label := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.label h
      probe := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.probe h
      phase := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.phase h
      path := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.path h
      path2 := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.path2 h
      p := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.p h
      p_carry := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.p_carry h
      state := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.state h
      signal_B := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.signal_B h
      bullet := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.bullet h
      shield := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.shield h
      path4 := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.path4 h
      path5 := congrArg ZZSafeN4WriterViewGPT.WriterProtectedView.path5 h }

private theorem writerFrames_of_pair
    {q : AgentState 2 × AgentState 2} {l r : AgentState 2}
    (h : ZZSafeN4WriterViewGPT.pairView q =
      ZZSafeN4WriterViewGPT.pairView (l, r)) :
    WriterFrame q.1 l ∧ WriterFrame q.2 r := by
  exact
    ⟨writerFrame_of_view (congrArg Prod.fst h),
     writerFrame_of_view (congrArg Prod.snd h)⟩

private theorem writer_A_of_frame
    (leaderBit : Bool) {u v : AgentState 2}
    (hleader : u.leader = v.leader)
    (f : WriterFrame u v)
    (hv : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit v) :
    ZZSafeN4ReversedMiddleGPT.AProtected leaderBit u := by
  rcases hv with
    ⟨hq, hvLeader, hvProbe, hvPhase, hvSignal, hvBullet,
      hvShield, hvPath4, hvPath5⟩
  rcases hq with
    ⟨hvLabel, hvPath, hvPath2, hvP, hvPCarry, hvState⟩
  refine ⟨?_, hleader.trans hvLeader, f.probe.trans hvProbe,
    f.phase.trans hvPhase, f.signal_B.trans hvSignal,
    f.bullet.trans hvBullet, f.shield.trans hvShield, ?_,
    f.path5.trans hvPath5⟩
  · refine ⟨f.label.trans hvLabel, f.path.trans hvPath,
      f.path2.trans hvPath2, f.p.trans hvP,
      f.p_carry.trans hvPCarry, ?_⟩
    rcases hvState with hs | hs
    · exact Or.inl (f.state.trans hs)
    · exact Or.inr (f.state.trans hs)
  · rcases hvPath4 with hp | hp
    · exact Or.inl (f.path4.trans hp)
    · exact Or.inr (f.path4.trans hp)

private theorem writer_B_of_frame
    (bulletVal : Fin 3) {u v : AgentState 2}
    (hleader : u.leader = v.leader)
    (f : WriterFrame u v)
    (hv : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal v) :
    ZZSafeN4ReversedMiddleGPT.BProtected bulletVal u := by
  rcases hv with
    ⟨hq, hvLeader, hvProbe, hvPhase, hvSignal, hvBullet,
      hvShield, hvPath4, hvPath5⟩
  rcases hq with
    ⟨hvLabel, hvPath, hvPath2, hvP, hvPCarry, hvState⟩
  refine ⟨?_, hleader.trans hvLeader, f.probe.trans hvProbe,
    f.phase.trans hvPhase, f.signal_B.trans hvSignal,
    f.bullet.trans hvBullet, f.shield.trans hvShield,
    f.path4.trans hvPath4, ?_⟩
  · exact ⟨f.label.trans hvLabel, f.path.trans hvPath,
      f.path2.trans hvPath2, f.p.trans hvP,
      f.p_carry.trans hvPCarry, f.state.trans hvState⟩
  · rcases hvPath5 with hp | hp
    · exact Or.inl (f.path5.trans hp)
    · exact Or.inr (f.path5.trans hp)

private theorem writeSeq_AB_protected
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2) (q : AgentState 2 × AgentState 2)
    (hq : q = PPLL.writeSeq hψ2 l r)
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal r) :
    ZZSafeN4ReversedMiddleGPT.AProtected leaderBit q.1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected bulletVal q.2 := by
  have hv := ZZSafeN4WriterComposeCoreGPT.writeSeq_view l r
  have hvq : ZZSafeN4WriterViewGPT.pairView q =
      ZZSafeN4WriterViewGPT.pairView (l, r) := by
    simpa [hq] using hv
  have hleaders :=
    @ZZSafeN4WriterFrame.writeSeq_leaders_eq_of_responder_follower_or_zero
      2 hψ2 l r (Or.inl hr.2.1)
  have hleadersq : q.1.leader = l.leader ∧ q.2.leader = r.leader := by
    simpa [hq] using hleaders
  have hf := writerFrames_of_pair hvq
  exact
    ⟨writer_A_of_frame leaderBit hleadersq.1 hf.1 hl,
     writer_B_of_frame bulletVal hleadersq.2 hf.2 hr⟩

private theorem writeSeq_BA_protected
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2) (q : AgentState 2 × AgentState 2)
    (hq : q = PPLL.writeSeq hψ2 l r)
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected bulletVal l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected leaderBit r)
    (hgate : r.leader = false ∨ r.label = (0 : Fin 2)) :
    ZZSafeN4ReversedMiddleGPT.BProtected bulletVal q.1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected leaderBit q.2 := by
  have hv := ZZSafeN4WriterComposeCoreGPT.writeSeq_view l r
  have hvq : ZZSafeN4WriterViewGPT.pairView q =
      ZZSafeN4WriterViewGPT.pairView (l, r) := by
    simpa [hq] using hv
  have hleaders :=
    @ZZSafeN4WriterFrame.writeSeq_leaders_eq_of_responder_follower_or_zero
      2 hψ2 l r hgate
  have hleadersq : q.1.leader = l.leader ∧ q.2.leader = r.leader := by
    simpa [hq] using hleaders
  have hf := writerFrames_of_pair hvq
  exact
    ⟨writer_B_of_frame bulletVal hleadersq.1 hf.1 hl,
     writer_A_of_frame leaderBit hleadersq.2 hf.2 hr⟩

private theorem compare_AB_protected
    {b : Bool} {d : Fin 3}
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected b l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected d r) :
    let q := PPLL.compareSig hψ2 l r
    ZZSafeN4ReversedMiddleGPT.AProtected b q.1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected d q.2 := by
  have hl' := hl
  have hr' := hr
  rcases hl' with
    ⟨⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩,
      hlLeader, hlProbe, hlPhase, hlSignal, hlBullet, hlShield,
      hlPath4, hlPath5⟩
  rcases hr' with
    ⟨⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩,
      hrLeader, hrProbe, hrPhase, hrSignal, hrBullet, hrShield,
      hrPath4, hrPath5⟩
  have heq := ZZSafeN4ReversedCompareGPT.compareSig_AB_exact l r
    hlLabel hlPath hlState hlPath2
    hrLabel hrPath hrState hrPath2
  dsimp only at heq ⊢
  rw [heq]
  simpa [ZZSafeN4ReversedMiddleGPT.AProtected,
    ZZSafeN4ReversedMiddleGPT.AQuiet,
    ZZSafeN4ReversedMiddleGPT.BProtected,
    ZZSafeN4ReversedMiddleGPT.BQuiet,
    hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlProbe, hlPhase,
    hlSignal, hlBullet, hlShield, hlPath4, hlPath5, hlLeader, hrLeader,
    hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrProbe, hrPhase,
    hrSignal, hrBullet, hrShield, hrPath4, hrPath5] using And.intro hl hr

private theorem compare_BA_protected
    {b : Bool} {d : Fin 3}
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected d l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected b r) :
    let q := PPLL.compareSig hψ2 l r
    ZZSafeN4ReversedMiddleGPT.BProtected d q.1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected b q.2 := by
  have hl' := hl
  have hr' := hr
  rcases hl' with
    ⟨⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩,
      hlLeader, hlProbe, hlPhase, hlSignal, hlBullet, hlShield,
      hlPath4, hlPath5⟩
  rcases hr' with
    ⟨⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩,
      hrLeader, hrProbe, hrPhase, hrSignal, hrBullet, hrShield,
      hrPath4, hrPath5⟩
  have heq := ZZSafeN4ReversedCompareGPT.compareSig_BA_exact l r
    hlLabel hlPath hlState hlPath2
    hrLabel hrPath hrState hrPath2
  dsimp only at heq ⊢
  rw [heq]
  simpa [ZZSafeN4ReversedMiddleGPT.AProtected,
    ZZSafeN4ReversedMiddleGPT.AQuiet,
    ZZSafeN4ReversedMiddleGPT.BProtected,
    ZZSafeN4ReversedMiddleGPT.BQuiet,
    hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState, hlProbe,
    hlPhase, hlSignal, hlBullet, hlShield, hlPath4, hlPath5, hlLeader, hrLeader,
    hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrProbe, hrPhase,
    hrSignal, hrBullet, hrShield, hrPath4, hrPath5] using And.intro hl hr

private theorem even_to_AProtected
    {b : Bool} {s : AgentState 2} (h : EvenSite b s) :
    ZZSafeN4ReversedMiddleGPT.AProtected b s := by
  rcases h with
    ⟨hleader, hlabel, hprobe, hphase, hpath, hpath2, hp, hpc,
      hstate, hsignal, hbullet, hshield, hpath4, hpath5⟩
  exact ⟨⟨hlabel, hpath, hpath2, hp, hpc, hstate⟩,
    hleader, hprobe, hphase, hsignal, hbullet, hshield, hpath4, hpath5⟩

private theorem odd_to_BProtected
    {b : Fin 3} {s : AgentState 2} (h : OddSite b s) :
    ZZSafeN4ReversedMiddleGPT.BProtected b s := by
  rcases h with
    ⟨hleader, hlabel, hprobe, hphase, hpath, hpath2, hp, hpc,
      hstate, hsignal, hbullet, hshield, hpath4, hpath5⟩
  exact ⟨⟨hlabel, hpath, hpath2, hp, hpc, hstate⟩,
    hleader, hprobe, hphase, hsignal, hbullet, hshield, hpath4, hpath5⟩

private theorem AProtected_to_even
    {b : Bool} {s : AgentState 2}
    (h : ZZSafeN4ReversedMiddleGPT.AProtected b s) : EvenSite b s := by
  rcases h with
    ⟨⟨hlabel, hpath, hpath2, hp, hpc, hstate⟩,
      hleader, hprobe, hphase, hsignal, hbullet, hshield, hpath4, hpath5⟩
  exact ⟨hleader, hlabel, hprobe, hphase, hpath, hpath2, hp, hpc,
    hstate, hsignal, hbullet, hshield, hpath4, hpath5⟩

private theorem BProtected_to_odd
    {b : Fin 3} {s : AgentState 2}
    (h : ZZSafeN4ReversedMiddleGPT.BProtected b s) : OddSite b s := by
  rcases h with
    ⟨⟨hlabel, hpath, hpath2, hp, hpc, hstate⟩,
      hleader, hprobe, hphase, hsignal, hbullet, hshield, hpath4, hpath5⟩
  exact ⟨hleader, hlabel, hprobe, hphase, hpath, hpath2, hp, hpc,
    hstate, hsignal, hbullet, hshield, hpath4, hpath5⟩

private theorem even_odd_to_ABPrefixRole
    {b : Bool} {d : Fin 3} {l r : AgentState 2}
    (hl : EvenSite b l) (hr : OddSite d r) :
    ZZSafeN4ReversedPrefixGPT.ABPrefixRole l r := by
  rcases hl with
    ⟨_, hlLabel, hlProbe, hlPhase, hlPath, _, _, _, hlState, _, _, _, _, _⟩
  rcases hr with
    ⟨_, hrLabel, hrProbe, hrPhase, hrPath, _, _, _, hrState, _, _, _, _, _⟩
  exact {
    leftLabel := hlLabel, rightLabel := hrLabel,
    leftProbe := hlProbe, rightProbe := hrProbe,
    leftPhase := hlPhase, rightPhase := hrPhase,
    leftPath := hlPath, rightPath := hrPath,
    leftState := hlState, rightState := hrState }

private theorem odd_even_to_BAPrefixRole
    {b : Fin 3} {d : Bool} {l r : AgentState 2}
    (hl : OddSite b l) (hr : EvenSite d r) :
    ZZSafeN4ReversedPrefixGPT.BAPrefixRole l r := by
  rcases hl with
    ⟨_, hlLabel, hlProbe, hlPhase, hlPath, _, _, _, hlState, _, _, _, _, _⟩
  rcases hr with
    ⟨_, hrLabel, hrProbe, hrPhase, hrPath, _, _, _, hrState, _, _, _, _, _⟩
  exact {
    leftLabel := hlLabel, rightLabel := hrLabel,
    leftProbe := hlProbe, rightProbe := hrProbe,
    leftPhase := hlPhase, rightPhase := hrPhase,
    leftPath := hlPath, rightPath := hrPath,
    leftState := hlState, rightState := hrState }

private theorem pack_A {b : Bool} {s : AgentState 2}
    (hLabel : s.label = 0) (hPath : s.path = .some 1 0)
    (hPath2 : s.path2 = none) (hP : s.p = false)
    (hPCarry : s.p_carry = false)
    (hState : s.state = .congest ∨ s.state = .lock)
    (hLeader : s.leader = b) (hProbe : s.probe = false)
    (hPhase : s.phase = false) (hSignal : s.signal_B = 0)
    (hBullet : s.bullet = 0) (hShield : s.shield = true)
    (hPath4 : s.path4 = none ∨ s.path4 = some (1, 1))
    (hPath5 : s.path5 = none) :
    ZZSafeN4ReversedMiddleGPT.AProtected b s := by
  exact ⟨⟨hLabel, hPath, hPath2, hP, hPCarry, hState⟩,
    hLeader, hProbe, hPhase, hSignal, hBullet, hShield, hPath4, hPath5⟩

private theorem pack_B {d : Fin 3} {s : AgentState 2}
    (hLabel : s.label = 1) (hPath : s.path = .some 0 0)
    (hPath2 : s.path2 = none) (hP : s.p = false)
    (hPCarry : s.p_carry = false) (hState : s.state = .congest)
    (hLeader : s.leader = false) (hProbe : s.probe = false)
    (hPhase : s.phase = false) (hSignal : s.signal_B = 0)
    (hBullet : s.bullet = d) (hShield : s.shield = true)
    (hPath4 : s.path4 = none)
    (hPath5 : s.path5 = none ∨ s.path5 = some (0, 1)) :
    ZZSafeN4ReversedMiddleGPT.BProtected d s := by
  exact ⟨⟨hLabel, hPath, hPath2, hP, hPCarry, hState⟩,
    hLeader, hProbe, hPhase, hSignal, hBullet, hShield, hPath4, hPath5⟩

private theorem assemble_AB
    {b : Bool} {d : Fin 3} {l r u v : AgentState 2}
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected b l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected d r)
    (h4 :
      u.leader = b ∧ v.leader = false ∧
      u.bullet = 0 ∧ v.bullet = d ∧
      u.shield = true ∧ v.shield = true ∧
      u.signal_B = 0 ∧ v.signal_B = 0 ∧
      u.label = l.label ∧ v.label = r.label ∧
      u.probe = l.probe ∧ v.probe = r.probe ∧
      u.phase = l.phase ∧ v.phase = r.phase ∧
      u.state = l.state ∧ v.state = r.state ∧
      u.path = l.path ∧ v.path = r.path ∧
      u.path2 = l.path2 ∧ v.path2 = r.path2 ∧
      u.p = l.p ∧ v.p = r.p ∧
      u.p_carry = l.p_carry ∧ v.p_carry = r.p_carry ∧
      u.path4 = l.path4 ∧ v.path4 = r.path4 ∧
      u.path5 = l.path5 ∧ v.path5 = r.path5) :
    ZZSafeN4ReversedMiddleGPT.AProtected b u ∧
      ZZSafeN4ReversedMiddleGPT.BProtected d v := by
  rcases hl with ⟨hlq, _, hlProbe, hlPhase, _, _, _, hlPath4, hlPath5⟩
  rcases hlq with ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with ⟨hrq, _, hrProbe, hrPhase, _, _, _, hrPath4, hrPath5⟩
  rcases hrq with ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  rcases h4 with
    ⟨huLeader, hvLeader, huBullet, hvBullet, huShield, hvShield,
      huSignal, hvSignal, huLabel, hvLabel, huProbe, hvProbe,
      huPhase, hvPhase, huState, hvState, huPath, hvPath,
      huPath2, hvPath2, huP, hvP, huPCarry, hvPCarry,
      huPath4, hvPath4, huPath5, hvPath5⟩
  refine ⟨?_, ?_⟩
  · exact ⟨⟨huLabel.trans hlLabel, huPath.trans hlPath,
        huPath2.trans hlPath2, huP.trans hlP,
        huPCarry.trans hlPCarry,
        Or.elim hlState (fun hs => Or.inl (huState.trans hs))
          (fun hs => Or.inr (huState.trans hs))⟩,
      huLeader, huProbe.trans hlProbe, huPhase.trans hlPhase,
      huSignal, huBullet, huShield,
      Or.elim hlPath4 (fun hp => Or.inl (huPath4.trans hp))
        (fun hp => Or.inr (huPath4.trans hp)),
      huPath5.trans hlPath5⟩
  · exact ⟨⟨hvLabel.trans hrLabel, hvPath.trans hrPath,
        hvPath2.trans hrPath2, hvP.trans hrP,
        hvPCarry.trans hrPCarry, hvState.trans hrState⟩,
      hvLeader, hvProbe.trans hrProbe, hvPhase.trans hrPhase,
      hvSignal, hvBullet, hvShield, hvPath4.trans hrPath4,
      Or.elim hrPath5 (fun hp => Or.inl (hvPath5.trans hp))
        (fun hp => Or.inr (hvPath5.trans hp))⟩

private theorem assemble_BA
    {b : Bool} {d : Fin 3} {l r u v : AgentState 2}
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected d l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected b r)
    (h4 :
      u.leader = false ∧ v.leader = b ∧
      u.bullet = d ∧ v.bullet = 0 ∧
      u.shield = true ∧ v.shield = true ∧
      u.signal_B = 0 ∧ v.signal_B = 0 ∧
      u.label = l.label ∧ v.label = r.label ∧
      u.probe = l.probe ∧ v.probe = r.probe ∧
      u.phase = l.phase ∧ v.phase = r.phase ∧
      u.state = l.state ∧ v.state = r.state ∧
      u.path = l.path ∧ v.path = r.path ∧
      u.path2 = l.path2 ∧ v.path2 = r.path2 ∧
      u.p = l.p ∧ v.p = r.p ∧
      u.p_carry = l.p_carry ∧ v.p_carry = r.p_carry ∧
      u.path4 = l.path4 ∧ v.path4 = r.path4 ∧
      u.path5 = l.path5 ∧ v.path5 = r.path5) :
    ZZSafeN4ReversedMiddleGPT.BProtected d u ∧
      ZZSafeN4ReversedMiddleGPT.AProtected b v := by
  rcases hl with ⟨hlq, _, hlProbe, hlPhase, _, _, _, hlPath4, hlPath5⟩
  rcases hlq with ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with ⟨hrq, _, hrProbe, hrPhase, _, _, _, hrPath4, hrPath5⟩
  rcases hrq with ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  rcases h4 with
    ⟨huLeader, hvLeader, huBullet, hvBullet, huShield, hvShield,
      huSignal, hvSignal, huLabel, hvLabel, huProbe, hvProbe,
      huPhase, hvPhase, huState, hvState, huPath, hvPath,
      huPath2, hvPath2, huP, hvP, huPCarry, hvPCarry,
      huPath4, hvPath4, huPath5, hvPath5⟩
  refine ⟨?_, ?_⟩
  · exact ⟨⟨huLabel.trans hlLabel, huPath.trans hlPath,
        huPath2.trans hlPath2, huP.trans hlP,
        huPCarry.trans hlPCarry, huState.trans hlState⟩,
      huLeader, huProbe.trans hlProbe, huPhase.trans hlPhase,
      huSignal, huBullet, huShield, huPath4.trans hlPath4,
      Or.elim hlPath5 (fun hp => Or.inl (huPath5.trans hp))
        (fun hp => Or.inr (huPath5.trans hp))⟩
  · exact ⟨⟨hvLabel.trans hrLabel, hvPath.trans hrPath,
        hvPath2.trans hrPath2, hvP.trans hrP,
        hvPCarry.trans hrPCarry,
        Or.elim hrState (fun hs => Or.inl (hvState.trans hs))
          (fun hs => Or.inr (hvState.trans hs))⟩,
      hvLeader, hvProbe.trans hrProbe, hvPhase.trans hrPhase,
      hvSignal, hvBullet, hvShield,
      Or.elim hrPath4 (fun hp => Or.inl (hvPath4.trans hp))
        (fun hp => Or.inr (hvPath4.trans hp)),
      hvPath5.trans hrPath5⟩

private theorem prewrite_AB_01
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected true l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) r) :
    let q := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
    ZZSafeN4ReversedMiddleGPT.AProtected true q.1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q.2 := by
  let q0 := ZZSafeN4ReversedPrefixGPT.afterGenSig l r
  have h0view := ZZSafeN4ReversedPrefixGPT.afterGenSig_AB_frame l r
    (ZZSafeN4ReversedViewAdaptersGPT.protected_to_ABPrefixRole
      true (2 : Fin 3) l r hl hr)
  have h0 :
      ZZSafeN4ReversedMiddleGPT.AProtected true q0.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q0.2 := by
    apply ZZSafeN4ReversedViewAdaptersGPT.prefixPairView_transport_AB
      true (2 : Fin 3) q0 l r
    · simpa [q0] using h0view
    · exact ⟨hl, hr⟩
  let q1 := PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 q0.1 q0.2
  have h1 :
      ZZSafeN4ReversedMiddleGPT.AProtected true q1.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q1.2 := by
    simpa [q1] using
      (ZZSafeN4ReversedViewAdaptersGPT.clean_AB_protected
        true (2 : Fin 3) q0.1 q0.2 h0.1 h0.2)
  let q2 := ZZSafeN4ReversedMiddleGPT.middleBeforeCompare q1.1 q1.2
  have h2 := ZZSafeN4ReversedMiddleGPT.middle_AB_protected
    true (2 : Fin 3) q1.1 q1.2 h1.1 h1.2
  have h2eq : q2 = (q1.1, q1.2) := by
    simpa [q2] using h2.1
  let q3 := PPLL.compareSig hψ2 q2.1 q2.2
  have h3 :
      ZZSafeN4ReversedMiddleGPT.AProtected true q3.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q3.2 := by
    dsimp [q3]
    rw [h2eq]
    exact compare_AB_protected q1.1 q1.2 h1.1 h1.2
  have h3a := h3.1
  have h3b := h3.2
  rcases h3a with
    ⟨⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩,
      hlLeader, hlProbe, hlPhase, hlSignal, hlBullet, hlShield,
      hlPath4, hlPath5⟩
  rcases h3b with
    ⟨⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩,
      hrLeader, hrProbe, hrPhase, hrSignal, hrBullet, hrShield,
      hrPath4, hrPath5⟩
  have h4 := ZZSafeN4ReversedEliminateGPT.pair01_A0_B1_protected
    q3.1 q3.2 hlLeader hrLeader hlLabel hrLabel
    hlBullet hrBullet hlShield hrShield hlSignal hrSignal
  rcases h4 with
    ⟨hLL, hRL, hBulL, hBulR, hShL, hShR, hSigL, hSigR,
      hLabL, hLabR, hPrL, hPrR, hPhL, hPhR, hStL, hStR,
      hPathL, hPathR, hPath2L, hPath2R, hPL, hPR, hPCL, hPCR,
      hPath4L, hPath4R, hPath5L, hPath5R⟩
  have hfL : WriterFrame
      (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).1 q3.1 :=
    { label := hLabL, probe := hPrL, phase := hPhL, path := hPathL,
      path2 := hPath2L, p := hPL, p_carry := hPCL, state := hStL,
      signal_B := hSigL.trans hlSignal.symm,
      bullet := hBulL.trans hlBullet.symm,
      shield := hShL.trans hlShield.symm,
      path4 := hPath4L, path5 := hPath5L }
  have hfR : WriterFrame
      (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).2 q3.2 :=
    { label := hLabR, probe := hPrR, phase := hPhR, path := hPathR,
      path2 := hPath2R, p := hPR, p_carry := hPCR, state := hStR,
      signal_B := hSigR.trans hrSignal.symm,
      bullet := hBulR.trans hrBullet.symm,
      shield := hShR.trans hrShield.symm,
      path4 := hPath4R, path5 := hPath5R }
  have hout :
      ZZSafeN4ReversedMiddleGPT.AProtected true
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3)
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).2 :=
    ⟨writer_A_of_frame true (hLL.trans hlLeader.symm) hfL h3.1,
     writer_B_of_frame (2 : Fin 3) (hRL.trans hrLeader.symm) hfR h3.2⟩
  change
    ZZSafeN4ReversedMiddleGPT.AProtected true
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3)
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).2
  have hactual :
        PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r =
          ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2 := by
    rfl
  rw [hactual]
  exact hout

private theorem prewrite_AB_23
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.AProtected false l)
    (hr : ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) r) :
    let q := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
    ZZSafeN4ReversedMiddleGPT.AProtected false q.1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q.2 := by
  let q0 := ZZSafeN4ReversedPrefixGPT.afterGenSig l r
  have h0view := ZZSafeN4ReversedPrefixGPT.afterGenSig_AB_frame l r
    (ZZSafeN4ReversedViewAdaptersGPT.protected_to_ABPrefixRole
      false (0 : Fin 3) l r hl hr)
  have h0 :
      ZZSafeN4ReversedMiddleGPT.AProtected false q0.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q0.2 := by
    apply ZZSafeN4ReversedViewAdaptersGPT.prefixPairView_transport_AB
      false (0 : Fin 3) q0 l r
    · simpa [q0] using h0view
    · exact ⟨hl, hr⟩
  let q1 := PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 q0.1 q0.2
  have h1 :
      ZZSafeN4ReversedMiddleGPT.AProtected false q1.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q1.2 := by
    simpa [q1] using
      (ZZSafeN4ReversedViewAdaptersGPT.clean_AB_protected
        false (0 : Fin 3) q0.1 q0.2 h0.1 h0.2)
  let q2 := ZZSafeN4ReversedMiddleGPT.middleBeforeCompare q1.1 q1.2
  have h2 := ZZSafeN4ReversedMiddleGPT.middle_AB_protected
    false (0 : Fin 3) q1.1 q1.2 h1.1 h1.2
  have h2eq : q2 = (q1.1, q1.2) := by
    simpa [q2] using h2.1
  let q3 := PPLL.compareSig hψ2 q2.1 q2.2
  have h3 :
      ZZSafeN4ReversedMiddleGPT.AProtected false q3.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q3.2 := by
    dsimp [q3]
    rw [h2eq]
    exact compare_AB_protected q1.1 q1.2 h1.1 h1.2
  have h3a := h3.1
  have h3b := h3.2
  rcases h3a with
    ⟨⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩,
      hlLeader, hlProbe, hlPhase, hlSignal, hlBullet, hlShield,
      hlPath4, hlPath5⟩
  rcases h3b with
    ⟨⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩,
      hrLeader, hrProbe, hrPhase, hrSignal, hrBullet, hrShield,
      hrPath4, hrPath5⟩
  have h4 := ZZSafeN4ReversedEliminateGPT.pair23_A2_B3_protected
    q3.1 q3.2 hlLeader hrLeader hlLabel hrLabel
    hlBullet hrBullet hlShield hrShield hlSignal hrSignal
  have hout :
      ZZSafeN4ReversedMiddleGPT.AProtected false
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3)
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).2 := by
    exact assemble_AB h3.1 h3.2 h4
  change
    ZZSafeN4ReversedMiddleGPT.AProtected false
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).1 ∧
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3)
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).2
  have hactual :
      PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r =
        ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2 := by
    rfl
  rw [hactual]
  exact hout

private theorem prewrite_BA_12
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected false r) :
    let q := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
    ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q.1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected false q.2 := by
  let q0 := ZZSafeN4ReversedPrefixGPT.afterGenSig l r
  have h0view := ZZSafeN4ReversedPrefixGPT.afterGenSig_BA_frame l r
    (ZZSafeN4ReversedViewAdaptersGPT.protected_to_BAPrefixRole
      false (2 : Fin 3) l r hl hr)
  have h0 :
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q0.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected false q0.2 := by
    apply ZZSafeN4ReversedViewAdaptersGPT.prefixPairView_transport_BA
      false (2 : Fin 3) q0 l r
    · simpa [q0] using h0view
    · exact ⟨hl, hr⟩
  let q1 := PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 q0.1 q0.2
  have h1 :
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q1.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected false q1.2 := by
    simpa [q1] using
      (ZZSafeN4ReversedViewAdaptersGPT.clean_BA_protected
        false (2 : Fin 3) q0.1 q0.2 h0.1 h0.2)
  let q2 := ZZSafeN4ReversedMiddleGPT.middleBeforeCompare q1.1 q1.2
  have h2 := ZZSafeN4ReversedMiddleGPT.middle_BA_protected
    false (2 : Fin 3) q1.1 q1.2 h1.1 h1.2
  have h2eq : q2 = (q1.1, q1.2) := by
    simpa [q2] using h2.1
  let q3 := PPLL.compareSig hψ2 q2.1 q2.2
  have h3 :
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) q3.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected false q3.2 := by
    dsimp [q3]
    rw [h2eq]
    exact compare_BA_protected q1.1 q1.2 h1.1 h1.2
  have h3a := h3.1
  have h3b := h3.2
  rcases h3a with
    ⟨⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩,
      hlLeader, hlProbe, hlPhase, hlSignal, hlBullet, hlShield,
      hlPath4, hlPath5⟩
  rcases h3b with
    ⟨⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩,
      hrLeader, hrProbe, hrPhase, hrSignal, hrBullet, hrShield,
      hrPath4, hrPath5⟩
  have h4 := ZZSafeN4ReversedEliminateGPT.pair12_B1_A2_protected
    q3.1 q3.2 hlLeader hrLeader hlLabel hrLabel
    hlBullet hrBullet hlShield hrShield hlSignal hrSignal
  have hout :
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3)
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected false
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).2 := by
    exact assemble_BA h3.1 h3.2 h4
  change
    ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3)
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected false
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).2
  have hactual :
      PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r =
        ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2 := by
    rfl
  rw [hactual]
  exact hout
private theorem prewrite_BA_30
    (l r : AgentState 2)
    (hl : ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) l)
    (hr : ZZSafeN4ReversedMiddleGPT.AProtected true r) :
    let q := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
    ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q.1 ∧
    ZZSafeN4ReversedMiddleGPT.AProtected true q.2 := by
  let q0 := ZZSafeN4ReversedPrefixGPT.afterGenSig l r
  have h0view := ZZSafeN4ReversedPrefixGPT.afterGenSig_BA_frame l r
    (ZZSafeN4ReversedViewAdaptersGPT.protected_to_BAPrefixRole
      true (0 : Fin 3) l r hl hr)
  have h0 :
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q0.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected true q0.2 := by
    apply ZZSafeN4ReversedViewAdaptersGPT.prefixPairView_transport_BA
      true (0 : Fin 3) q0 l r
    · simpa [q0] using h0view
    · exact ⟨hl, hr⟩
  let q1 := PPLL.cleanSig ZZSafeN4ReversedCleanGPT.hpsi2 q0.1 q0.2
  have h1 :
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q1.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected true q1.2 := by
    simpa [q1] using
      (ZZSafeN4ReversedViewAdaptersGPT.clean_BA_protected
        true (0 : Fin 3) q0.1 q0.2 h0.1 h0.2)
  let q2 := ZZSafeN4ReversedMiddleGPT.middleBeforeCompare q1.1 q1.2
  have h2 := ZZSafeN4ReversedMiddleGPT.middle_BA_protected
    true (0 : Fin 3) q1.1 q1.2 h1.1 h1.2
  have h2eq : q2 = (q1.1, q1.2) := by
    simpa [q2] using h2.1
  let q3 := PPLL.compareSig hψ2 q2.1 q2.2
  have h3 :
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) q3.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected true q3.2 := by
    dsimp [q3]
    rw [h2eq]
    exact compare_BA_protected q1.1 q1.2 h1.1 h1.2
  have h3a := h3.1
  have h3b := h3.2
  rcases h3a with
    ⟨⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩,
      hlLeader, hlProbe, hlPhase, hlSignal, hlBullet, hlShield,
      hlPath4, hlPath5⟩
  rcases h3b with
    ⟨⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩,
      hrLeader, hrProbe, hrPhase, hrSignal, hrBullet, hrShield,
      hrPath4, hrPath5⟩
  have h4 := ZZSafeN4ReversedEliminateGPT.pair30_B3_A0_protected
    q3.1 q3.2 hlLeader hrLeader hlLabel hrLabel
    hlBullet hrBullet hlShield hrShield hlSignal hrSignal
  have hout :
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3)
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected true
          (ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2).2 := by
    exact assemble_BA h3.1 h3.2 h4
  change
    ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3)
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).1 ∧
      ZZSafeN4ReversedMiddleGPT.AProtected true
        (PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r).2
  have hactual :
      PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r =
        ZZSafeN4ReversedEliminateGPT.suppressThenEliminate q3.1 q3.2 := by
    rfl
  rw [hactual]
  exact hout

theorem fullRow_01
    (l r : AgentState 2)
    (hl : EvenSite true l)
    (hr : OddSite (2 : Fin 3) r) :
    let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r
    EvenSite true q.1 ∧ OddSite (2 : Fin 3) q.2 := by
  let p := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
  have hp :
      ZZSafeN4ReversedMiddleGPT.AProtected true p.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) p.2 := by
    simpa only [p] using
      (prewrite_AB_01 l r (even_to_AProtected hl) (odd_to_BProtected hr))
  let w := PPLL.writeSeq hψ2 p.1 p.2
  have hpsiEq : ZZSafeN4WriterViewGPT.hpsi2 = hψ2 :=
    Subsingleton.elim _ _
  have hv :
      ZZSafeN4WriterViewGPT.pairView w =
        ZZSafeN4WriterViewGPT.pairView (p.1, p.2) := by
    simpa only [w, hpsiEq] using
      (ZZSafeN4WriterComposeCoreGPT.writeSeq_view p.1 p.2)
  have hleaders :
      w.1.leader = p.1.leader ∧ w.2.leader = p.2.leader := by
    simpa only [w] using
      (@ZZSafeN4WriterFrame.writeSeq_leaders_eq_of_responder_follower_or_zero
        2 hψ2 p.1 p.2 (Or.inl hp.2.2.1))
  have hf := writerFrames_of_pair hv
  have hwA := writer_A_of_frame true hleaders.1 hf.1 hp.1
  have hwB := writer_B_of_frame (2 : Fin 3) hleaders.2 hf.2 hp.2
  have hout : EvenSite true w.1 ∧ OddSite (2 : Fin 3) w.2 :=
    ⟨AProtected_to_even hwA, BProtected_to_odd hwB⟩
  have hrow :
      PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r = w := by
    rfl
  rw [hrow]
  exact hout

theorem fullRow_12
    (l r : AgentState 2)
    (hl : OddSite (2 : Fin 3) l)
    (hr : EvenSite false r) :
    let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r
    OddSite (2 : Fin 3) q.1 ∧ EvenSite false q.2 := by
  let p := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
  have hp :
      ZZSafeN4ReversedMiddleGPT.BProtected (2 : Fin 3) p.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected false p.2 := by
    simpa only [p] using
      (prewrite_BA_12 l r (odd_to_BProtected hl) (even_to_AProtected hr))
  let w := PPLL.writeSeq hψ2 p.1 p.2
  have hpsiEq : ZZSafeN4WriterViewGPT.hpsi2 = hψ2 :=
    Subsingleton.elim _ _
  have hv :
      ZZSafeN4WriterViewGPT.pairView w =
        ZZSafeN4WriterViewGPT.pairView (p.1, p.2) := by
    simpa only [w, hpsiEq] using
      (ZZSafeN4WriterComposeCoreGPT.writeSeq_view p.1 p.2)
  have hleaders :
      w.1.leader = p.1.leader ∧ w.2.leader = p.2.leader := by
    simpa only [w] using
      (@ZZSafeN4WriterFrame.writeSeq_leaders_eq_of_responder_follower_or_zero
        2 hψ2 p.1 p.2 (Or.inl hp.2.2.1))
  have hf := writerFrames_of_pair hv
  have hwB := writer_B_of_frame (2 : Fin 3) hleaders.1 hf.1 hp.1
  have hwA := writer_A_of_frame false hleaders.2 hf.2 hp.2
  have hout : OddSite (2 : Fin 3) w.1 ∧ EvenSite false w.2 :=
    ⟨BProtected_to_odd hwB, AProtected_to_even hwA⟩
  have hrow :
      PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r = w := by
    rfl
  rw [hrow]
  exact hout

theorem fullRow_23
    (l r : AgentState 2)
    (hl : EvenSite false l)
    (hr : OddSite (0 : Fin 3) r) :
    let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r
    EvenSite false q.1 ∧ OddSite (0 : Fin 3) q.2 := by
  let p := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
  have hp :
      ZZSafeN4ReversedMiddleGPT.AProtected false p.1 ∧
        ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) p.2 := by
    simpa only [p] using
      (prewrite_AB_23 l r (even_to_AProtected hl) (odd_to_BProtected hr))
  let w := PPLL.writeSeq hψ2 p.1 p.2
  have hpsiEq : ZZSafeN4WriterViewGPT.hpsi2 = hψ2 :=
    Subsingleton.elim _ _
  have hv :
      ZZSafeN4WriterViewGPT.pairView w =
        ZZSafeN4WriterViewGPT.pairView (p.1, p.2) := by
    simpa only [w, hpsiEq] using
      (ZZSafeN4WriterComposeCoreGPT.writeSeq_view p.1 p.2)
  have hleaders :
      w.1.leader = p.1.leader ∧ w.2.leader = p.2.leader := by
    simpa only [w] using
      (@ZZSafeN4WriterFrame.writeSeq_leaders_eq_of_responder_follower_or_zero
        2 hψ2 p.1 p.2 (Or.inl hp.2.2.1))
  have hf := writerFrames_of_pair hv
  have hwA := writer_A_of_frame false hleaders.1 hf.1 hp.1
  have hwB := writer_B_of_frame (0 : Fin 3) hleaders.2 hf.2 hp.2
  have hout : EvenSite false w.1 ∧ OddSite (0 : Fin 3) w.2 :=
    ⟨AProtected_to_even hwA, BProtected_to_odd hwB⟩
  have hrow :
      PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r = w := by
    rfl
  rw [hrow]
  exact hout

theorem fullRow_30
    (l r : AgentState 2)
    (hl : OddSite (0 : Fin 3) l)
    (hr : EvenSite true r) :
    let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r
    OddSite (0 : Fin 3) q.1 ∧ EvenSite true q.2 := by
  let p := PPLLRepair.ppllSaturatedBeforeWrite hψ2 10 l r
  have hp :
      ZZSafeN4ReversedMiddleGPT.BProtected (0 : Fin 3) p.1 ∧
        ZZSafeN4ReversedMiddleGPT.AProtected true p.2 := by
    simpa only [p] using
      (prewrite_BA_30 l r (odd_to_BProtected hl) (even_to_AProtected hr))
  let w := PPLL.writeSeq hψ2 p.1 p.2
  have hpsiEq : ZZSafeN4WriterViewGPT.hpsi2 = hψ2 :=
    Subsingleton.elim _ _
  have hv :
      ZZSafeN4WriterViewGPT.pairView w =
        ZZSafeN4WriterViewGPT.pairView (p.1, p.2) := by
    simpa only [w, hpsiEq] using
      (ZZSafeN4WriterComposeCoreGPT.writeSeq_view p.1 p.2)
  have hp2zero : p.2.label = (0 : Fin 2) := hp.2.1.1
  have hleaders :
      w.1.leader = p.1.leader ∧ w.2.leader = p.2.leader := by
    simpa only [w] using
      (@ZZSafeN4WriterFrame.writeSeq_leaders_eq_of_responder_follower_or_zero
        2 hψ2 p.1 p.2 (Or.inr hp2zero))
  have hf := writerFrames_of_pair hv
  have hwB := writer_B_of_frame (0 : Fin 3) hleaders.1 hf.1 hp.1
  have hwA := writer_A_of_frame true hleaders.2 hf.2 hp.2
  have hout : OddSite (0 : Fin 3) w.1 ∧ EvenSite true w.2 :=
    ⟨BProtected_to_odd hwB, AProtected_to_even hwA⟩
  have hrow :
      PPLLRepair.ppllSaturatedNoCollision hψ2 10 l r = w := by
    rfl
  rw [hrow]
  exact hout

private theorem ring4_rightNeighbor_0 :
    ring4.rightNeighbor (0 : Fin 4) = (1 : Fin 4) := by
  apply Fin.ext
  decide


private theorem ring4_rightNeighbor_1 :
    ring4.rightNeighbor (1 : Fin 4) = (2 : Fin 4) := by
  apply Fin.ext
  decide


private theorem ring4_rightNeighbor_2 :
    ring4.rightNeighbor (2 : Fin 4) = (3 : Fin 4) := by
  apply Fin.ext
  decide


private theorem ring4_rightNeighbor_3 :
    ring4.rightNeighbor (3 : Fin 4) = (0 : Fin 4) := by
  apply Fin.ext
  decide


private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega


private theorem step_left
    (C : Fin 4 → AgentState 2) (e : Fin 4)
    (q : AgentState 2 × AgentState 2)
    (h : Raw.transition (C e) (C (ring4.rightNeighbor e)) = q) :
    PopulationProtocol.step Raw ring4 C e e = q.1 := by
  rcases q with ⟨ql, qr⟩
  simp [PopulationProtocol.step, h] <;> rfl


private theorem step_right
    (C : Fin 4 → AgentState 2) (e : Fin 4)
    (q : AgentState 2 × AgentState 2)
    (h : Raw.transition (C e) (C (ring4.rightNeighbor e)) = q)
    (hne : ring4.rightNeighbor e ≠ e) :
    PopulationProtocol.step Raw ring4 C e (ring4.rightNeighbor e) = q.2 := by
  rcases q with ⟨ql, qr⟩
  simp [PopulationProtocol.step, h, hne] <;> rfl


private theorem step_frame
    (C : Fin 4 → AgentState 2) (e k : Fin 4)
    (hke : k ≠ e) (hkr : k ≠ ring4.rightNeighbor e) :
    PopulationProtocol.step Raw ring4 C e k = C k := by
  cases h :
      Raw.transition (C e) (C (ring4.rightNeighbor e)) with
  | mk ql qr =>
      simp [PopulationProtocol.step, h, hke, hkr] <;> rfl



theorem reversedCore_step_01 {C : Raw.Configuration 4}
    (hC : ReversedCore C) :
    ReversedCore (PopulationProtocol.step Raw ring4 C 0) := by
  change EvenSite true (C 0) ∧ OddSite 2 (C 1) ∧
    EvenSite false (C 2) ∧ OddSite 0 (C 3) at hC
  rcases hC with ⟨h0, h1, h2, h3⟩
  let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 (C 0) (C 1)
  have hr := fullRow_01 (C 0) (C 1) h0 h1
  change EvenSite true q.1 ∧ OddSite 2 q.2 at hr
  have ht :
      Raw.transition (C 0) (C (ring4.rightNeighbor 0)) = q := by
    rw [ring4_rightNeighbor_0]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [step_left C 0 q ht]
    exact hr.1
  · rw [← ring4_rightNeighbor_0,
      step_right C 0 q ht (by
        rw [ring4_rightNeighbor_0]
        decide)]
    exact hr.2
  · rw [step_frame C 0 2 (by decide) (by
      rw [ring4_rightNeighbor_0]
      decide)]
    exact h2
  · rw [step_frame C 0 3 (by decide) (by
      rw [ring4_rightNeighbor_0]
      decide)]
    exact h3


theorem reversedCore_step_12 {C : Raw.Configuration 4}
    (hC : ReversedCore C) :
    ReversedCore (PopulationProtocol.step Raw ring4 C 1) := by
  change EvenSite true (C 0) ∧ OddSite 2 (C 1) ∧
    EvenSite false (C 2) ∧ OddSite 0 (C 3) at hC
  rcases hC with ⟨h0, h1, h2, h3⟩
  let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 (C 1) (C 2)
  have hr := fullRow_12 (C 1) (C 2) h1 h2
  change OddSite 2 q.1 ∧ EvenSite false q.2 at hr
  have ht :
      Raw.transition (C 1) (C (ring4.rightNeighbor 1)) = q := by
    rw [ring4_rightNeighbor_1]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [step_frame C 1 0 (by decide) (by
      rw [ring4_rightNeighbor_1]
      decide)]
    exact h0
  · rw [step_left C 1 q ht]
    exact hr.1
  · rw [← ring4_rightNeighbor_1,
      step_right C 1 q ht (by
        rw [ring4_rightNeighbor_1]
        decide)]
    exact hr.2
  · rw [step_frame C 1 3 (by decide) (by
      rw [ring4_rightNeighbor_1]
      decide)]
    exact h3


theorem reversedCore_step_23 {C : Raw.Configuration 4}
    (hC : ReversedCore C) :
    ReversedCore (PopulationProtocol.step Raw ring4 C 2) := by
  change EvenSite true (C 0) ∧ OddSite 2 (C 1) ∧
    EvenSite false (C 2) ∧ OddSite 0 (C 3) at hC
  rcases hC with ⟨h0, h1, h2, h3⟩
  let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 (C 2) (C 3)
  have hr := fullRow_23 (C 2) (C 3) h2 h3
  change EvenSite false q.1 ∧ OddSite 0 q.2 at hr
  have ht :
      Raw.transition (C 2) (C (ring4.rightNeighbor 2)) = q := by
    rw [ring4_rightNeighbor_2]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [step_frame C 2 0 (by decide) (by
      rw [ring4_rightNeighbor_2]
      decide)]
    exact h0
  · rw [step_frame C 2 1 (by decide) (by
      rw [ring4_rightNeighbor_2]
      decide)]
    exact h1
  · rw [step_left C 2 q ht]
    exact hr.1
  · rw [← ring4_rightNeighbor_2,
      step_right C 2 q ht (by
        rw [ring4_rightNeighbor_2]
        decide)]
    exact hr.2


theorem reversedCore_step_30 {C : Raw.Configuration 4}
    (hC : ReversedCore C) :
    ReversedCore (PopulationProtocol.step Raw ring4 C 3) := by
  change EvenSite true (C 0) ∧ OddSite 2 (C 1) ∧
    EvenSite false (C 2) ∧ OddSite 0 (C 3) at hC
  rcases hC with ⟨h0, h1, h2, h3⟩
  let q := PPLLRepair.ppllSaturatedNoCollision hψ2 10 (C 3) (C 0)
  have hr := fullRow_30 (C 3) (C 0) h3 h0
  change OddSite 0 q.1 ∧ EvenSite true q.2 at hr
  have ht :
      Raw.transition (C 3) (C (ring4.rightNeighbor 3)) = q := by
    rw [ring4_rightNeighbor_3]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← ring4_rightNeighbor_3,
      step_right C 3 q ht (by
        rw [ring4_rightNeighbor_3]
        decide)]
    exact hr.2
  · rw [step_frame C 3 1 (by decide) (by
      rw [ring4_rightNeighbor_3]
      decide)]
    exact h1
  · rw [step_frame C 3 2 (by decide) (by
      rw [ring4_rightNeighbor_3]
      decide)]
    exact h2
  · rw [step_left C 3 q ht]
    exact hr.1


theorem reversedCore_step_any
    (C : Raw.Configuration 4) (hC : ReversedCore C) (e : Fin 4) :
    ReversedCore (PopulationProtocol.step Raw ring4 C e) := by
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact reversedCore_step_01 hC
  · exact reversedCore_step_12 hC
  · exact reversedCore_step_23 hC
  · exact reversedCore_step_30 hC


#print axioms ZZSafeN4Reversed.reversedCore_step_any



private theorem raw_isLeader_output (s : AgentState 2) :
    isLeaderOutput (Raw.output s) = s.leader := by
  change isLeaderOutput (AgentState.outputFn s) = s.leader
  cases h : s.leader <;>
    simp [AgentState.outputFn, isLeaderOutput, h]


private theorem raw_output_eq_of_leader_eq
    (a b : AgentState 2) (h : a.leader = b.leader) :
    Raw.output a = Raw.output b := by
  change AgentState.outputFn a = AgentState.outputFn b
  simp [AgentState.outputFn, h]


theorem reversedCore_unique_output
    (C : Raw.Configuration 4) (hC : ReversedCore C) :
    PPLLResearchFormulation.UniqueLeaderOutput Raw 4 C isLeaderOutput := by
  rcases hC with ⟨h0, h1, h2, h3⟩
  refine ⟨0, ?_, ?_⟩
  · change isLeaderOutput (AgentState.outputFn (C 0)) = true
    simp [AgentState.outputFn, isLeaderOutput, h0.1]
  · intro i hi
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · rfl
    · change isLeaderOutput (AgentState.outputFn (C 1)) = true at hi
      have hfalse : False := by
        simpa [AgentState.outputFn, isLeaderOutput, h1.1] using hi
      exact False.elim hfalse
    · change isLeaderOutput (AgentState.outputFn (C 2)) = true at hi
      have hfalse : False := by
        simpa [AgentState.outputFn, isLeaderOutput, h2.1] using hi
      exact False.elim hfalse
    · change isLeaderOutput (AgentState.outputFn (C 3)) = true at hi
      have hfalse : False := by
        simpa [AgentState.outputFn, isLeaderOutput, h3.1] using hi
      exact False.elim hfalse


private theorem reachable_preserved_of_step
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    {S : P.Configuration n → Prop}
    (hstepAny : ∀ C, S C → ∀ e : Fin n,
      S (PopulationProtocol.step P ring C e))
    {C C' : P.Configuration n} (hC : S C)
    (hreach : PopulationProtocol.Reachable P ring C C') : S C' := by
  induction hreach
  · exact hC
  · rename_i C₂ C₃ _ hone ih
    obtain ⟨e, rfl⟩ := hone
    exact hstepAny C₂ ih e


theorem reversedCore_reachable
    {C C' : Raw.Configuration 4}
    (hC : ReversedCore C)
    (hreach : PopulationProtocol.Reachable Raw ring4 C C') :
    ReversedCore C' := by
  exact reachable_preserved_of_step reversedCore_step_any hC hreach


private theorem reversedCore_output_eq
    (C D : Raw.Configuration 4)
    (hC : ReversedCore C) (hD : ReversedCore D)
    (i : Fin 4) :
    Raw.output (C i) = Raw.output (D i) := by
  rcases hC with ⟨hC0, hC1, hC2, hC3⟩
  rcases hD with ⟨hD0, hD1, hD2, hD3⟩
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · exact raw_output_eq_of_leader_eq _ _
      (hC0.1.trans hD0.1.symm)
  · exact raw_output_eq_of_leader_eq _ _
      (hC1.1.trans hD1.1.symm)
  · exact raw_output_eq_of_leader_eq _ _
      (hC2.1.trans hD2.1.symm)
  · exact raw_output_eq_of_leader_eq _ _
      (hC3.1.trans hD3.1.symm)


theorem reversedPathSafeRaw_isSafe :
    PopulationProtocol.IsSafe
      Raw ring4 reversedPathSafeRaw isLeaderOutput := by
  constructor
  · exact reversedCore_unique_output
      reversedPathSafeRaw reversedPathSafeRaw_core
  · intro C' hreach i
    have hC' : ReversedCore C' :=
      reversedCore_reachable reversedPathSafeRaw_core hreach
    exact reversedCore_output_eq
      C' reversedPathSafeRaw hC' reversedPathSafeRaw_core i


private def raw0 : AgentState 2 :=
  { PPLLCounterexample.state2 0 true .congest with path := .some 1 0, shield := true }
private def raw1 : AgentState 2 :=
  { PPLLCounterexample.state2 1 false .congest with path := .some 0 0, bullet := 2, shield := true }
private def raw2 : AgentState 2 :=
  { PPLLCounterexample.state2 0 false .congest with path := .some 1 0, shield := true }
private def raw3 : AgentState 2 :=
  { PPLLCounterexample.state2 1 false .congest with path := .some 0 0, shield := true }

private theorem raw0_domain : raw0.inProtocolDomain 10 := by
  unfold raw0 PPLLCounterexample.state2 AgentState.inProtocolDomain
  decide
private theorem raw1_domain : raw1.inProtocolDomain 10 := by
  unfold raw1 PPLLCounterexample.state2 AgentState.inProtocolDomain
  decide
private theorem raw2_domain : raw2.inProtocolDomain 10 := by
  unfold raw2 PPLLCounterexample.state2 AgentState.inProtocolDomain
  decide
private theorem raw3_domain : raw3.inProtocolDomain 10 := by
  unfold raw3 PPLLCounterexample.state2 AgentState.inProtocolDomain
  decide

theorem reversedPathSafeRaw_domain :
    ∀ i : Fin 4, (reversedPathSafeRaw i).inProtocolDomain 10 := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have := i.isLt
    omega
  rcases hi with rfl | rfl | rfl | rfl
  · change raw0.inProtocolDomain 10
    exact raw0_domain
  · change raw1.inProtocolDomain 10
    exact raw1_domain
  · change raw2.inProtocolDomain 10
    exact raw2_domain
  · change raw3.inProtocolDomain 10
    exact raw3_domain


theorem exists_bounded_safe_n4_psi2_k10 :
    ∃ B : (PPLLRepair.boundedProtocol hψ2 10).Configuration 4,
      PopulationProtocol.IsSafe
        (PPLLRepair.boundedProtocol hψ2 10)
        ring4 B isLeaderOutput := by
  refine ⟨ZZLiftToRepaired.reifyConfig
    reversedPathSafeRaw reversedPathSafeRaw_domain, ?_⟩
  exact
    (ZZLiftToRepaired.isSafe_reify_iff
      hψ2 ring4 reversedPathSafeRaw reversedPathSafeRaw_domain).2
      reversedPathSafeRaw_isSafe


#print axioms ZZSafeN4Reversed.reversedCore_unique_output
#print axioms ZZSafeN4Reversed.reversedCore_reachable
#print axioms ZZSafeN4Reversed.reversedCore_output_eq
#print axioms ZZSafeN4Reversed.reversedPathSafeRaw_isSafe
#print axioms ZZSafeN4Reversed.exists_bounded_safe_n4_psi2_k10

end ZZSafeN4Reversed
