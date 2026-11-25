import Leader.L4.Height.FreshAdmissionStart

namespace L4.Height.FreshWonAttempt
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongWork BStarLongCommand BStarSteeredLikelihood BStarResetChartTouch
open FreshFirstAcquire FreshAcquireReceipt

/-- Any fresh target RREL without an earlier publication necessarily contains
a real granted ACQUIRE. Its three winning samples and the ISSUE6 source are
located on the unchanged prefix of the emitted word. -/
theorem to_issue_six {s n : Nat} {x : Raw s n} (g : CustodyWitness x) (P : Production g)
    (target : Owners (oldH6 (rows s) g.base)) (base w after candidates : Word n) (nextR : Fin n)
    (cuts : Releases g target 5 base) (nextRelease : accepted g target (base++w) nextR)
    (tape : emit (chooseBy (RivalLedger.mask g target)) [] candidates=(base++w)++after)
    (miss : ¬RawServiceCore.publishes x (endpoint (oldH6 (rows s) g.base) g.hh target 1).1 ((base++w)++after)) :
    ∃ u e v S len fall,w=u++e::v ∧
      Chart (show 0<2 by decide) g.base g.hh target S len fall ∧
      Itinerary g.base (rawRun x base) S len fall u e ∧
      BStarResetControllerEntry.snapshot
        (rawNext s (rawRun x (base++u)) e (RivalLedger.source g target)).long=
        ((.empty,1),BitVec.ofNat 9 6) := by
  obtain ⟨u,e,v,S,len,fall,W,_,C,joined⟩ :=
    FreshAdmissionStart.first_itinerary_between_releases g P target base w after candidates nextR
      cuts nextRelease tape miss
  refine ⟨u,e,v,S,len,fall,W,C,joined,?_⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,receipt⟩ := joined
  have root : (S.getD 0 fall).1=RivalLedger.source g target := congrArg Prod.fst C.root
  have runEq : rawRun x (base++u)=rawRun (rawRun x base) u :=
    BStarResetSchedule.run_append (rawNext s) x base u
  rw [runEq,←root]
  exact receipt

#print axioms to_issue_six
end L4.Height.FreshWonAttempt

