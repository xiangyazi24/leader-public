import Leader.L4.Height.ProductionInvariant
import Leader.L4.BStarFreshReleaseCut

namespace L4.Height.ReleaseGrantReceipt
open AllSizeProtocol BStarAcquireAnchors PhysicalCustody ProductionCustody ProductionCycles BStarH6WordChart
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner BStarSteeredLikelihood

/-- The recovered RESET2 extraction on the actual tape supplies the target's
clean starting chart and all its grant zeros at the precise release mark. -/
theorem released_chart {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
    (P : Production g) (o : Owners (oldH6 (rows s) g.base))
    (a : Word n) (e : Fin n) (acceptedMark : accepted g o a e) :
    ∃ S len fall,Chart (show 0<2 by decide) g.base g.hh o S len fall ∧
      Current (show 0<2 by decide) g.base (fun j=>S.getD j fall) len
        (rawNext s (rawRun x a) e) .idle ∧
      ∀ i j, commandOwner (oldH6 (rows s) g.base) i (BStarResetNoAcquire.slot j)=o.val →
        BStarGrantBirth.bit (rawNext s (rawRun x a) e) i j=0 := by
  let hp : 0<2 := by decide
  obtain ⟨pre,mid,tail,S,len,fall,tape,_,C,_,m,G,cur⟩ :=
    generated_at_every_history P o a
  let origin := rawRun (rawRun g.initial pre) mid
  let w := tail++(g.past++a)
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  have rootID : root=(endpoint (oldH6 (rows s) g.base) g.hh o 0).1 := congrArg Prod.fst C.root
  have joined (z : Raw s n) (u v : Word n) : rawRun z (u++v)=rawRun (rawRun z u) v :=
    BStarResetSchedule.run_append (rawNext s) z u v
  have replay : rawRun origin w=rawRun x a := by
    change rawRun (rawRun (rawRun g.initial pre) mid) (tail++(g.past++a))=rawRun x a
    rw [←joined (rawRun g.initial pre) mid (tail++(g.past++a)),
      ←joined g.initial pre (mid++(tail++(g.past++a)))]
    rw [show pre++(mid++(tail++(g.past++a)))=((g.u++g.v)++g.past)++a by
      simp only [tape,List.append_assoc]]
    rw [joined g.initial ((g.u++g.v)++g.past) a,g.here]
  have qOrigin : g.Q origin := ProductionCustody.keep g _ mid (ProductionCustody.keep g _ pre g.init)
  unfold accepted at acceptedMark
  rw [←rootID] at acceptedMark
  obtain ⟨_,oldPC,newPC⟩ := acceptedMark
  have atStart : Current hp g.base addr len origin .idle := BStarGeneratedTapeCuts.at_start hp G
  have atCut (state : Raw s n) :
      BStarGeneratedBandScan.pc state root = (BStarLongDoor.ctrlOp.read (state root).long).toNat := rfl
  have beforePC : BStarGeneratedBandScan.pc (rawRun origin w) root=2 := by rw [atCut,replay]; exact oldPC
  have afterPC : BStarGeneratedBandScan.pc (rawNext s (rawRun origin w) e) root=3 := by rw [atCut,replay]; exact newPC
  obtain ⟨_,endMode,zeros⟩ := BStarFreshReleaseCut.stage_two_of_pc hp C (separation P) g.Q qOrigin
    g.fiber (fun z q f => g.closed z f q) atStart w e beforePC afterPC
  change Current hp g.base addr len (rawNext s (rawRun origin w) e) .idle at endMode
  rw [replay] at endMode
  refine ⟨S,len,fall,C,endMode,?_⟩
  intro i j owner
  have post : BStarGrantBirth.bit (rawNext s (rawRun origin w) e) i j=0 := (zeros i j owner).2
  rwa [replay] at post

end L4.Height.ReleaseGrantReceipt

