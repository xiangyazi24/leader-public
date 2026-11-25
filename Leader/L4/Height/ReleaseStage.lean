import Leader.L4.Height.ProductionCycles
import Leader.L4.Height.ReleaseCycle
import Leader.L4.Height.ReleaseTapeProjection

namespace L4.Height.ReleaseStage

open Classical
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles BStarSteeredLikelihood
open BStarLongClaims BStarLongDoor BStarLongWork BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder
open BStarAcquireAnchors BStarAcquireLiteralChain BStarResetChartTouch BStarGeneratedOwner
open BStarLongFixedRouting BStarClearanceOffset BStarParkedSteering BStarSteeringSupport
open ReleaseCycle

noncomputable section

open ReleaseTapeProjection

private theorem raw_append {s n : Nat} (x : Raw s n) (u v : Word n) :
    rawRun x (u++v)=rawRun (rawRun x u) v :=
  BStarResetSchedule.run_append (rawNext s) x u v

private theorem mark_releases {s n : Nat} {base origin x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true} {o : Owners (oldH6 (rows s) base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart (by decide : 0<2) base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {w : Word n} (replay : x=rawRun origin w)
    {m d : Mode} (e : Fin n)
    (hist : GeneratedOwner (by decide : 0<2) base (fun j => S.getD j fall) len origin .idle w m)
    (cur : Current (by decide : 0<2) base (fun j => S.getD j fall) len x m)
    (ev : Event (by decide : 0<2) (fun j => S.getD j fall) len x e m d)
    (paid : releaseEvent m d=true) :
    let root := (S.getD 0 fall).1
    e=RearTrace.predecessor root ∧ (ctrlOp.read (x root).long).toNat=2 ∧
      (ctrlOp.read (rawNext s x e root).long).toNat=3 := by
  cases ev with
  | idle_hold | bad_issue | launch | transit | arrived_hold => simp [releaseEvent] at paid
  | consume op own cleared =>
    have eq : op=2 := by simpa [releaseEvent] using paid
    subst op
    exact ⟨own,cur.1.2.2.2,generated_reset_receipt (by decide : 0<2) C sep replay 2 (by decide)
      e hist cur (.consume 2 own cleared)⟩

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "h" => oldH6 (rows s) g.base
local notation "hp" => (show 0<2 by decide)

/-- The actual next RREL receipt of any credited owner at an arbitrary
stopped production history. The local controller preserves the original
query's admission credit and the global history's physical marks. -/
theorem release_owner (P : Production g) (i : Header h) (o : Owners h) (y : History s n)
    (ok : Consistent x (policy g i) i.val y) :
    Cycle g i y (fun z => Consistent x (policy g i) i.val z ∧
      ∃ gap e,z.emitted=(y.emitted++gap)++[e] ∧ accepted g o (y.emitted++gap) e) := by
  let target := ProductionClients.serviceOwner g i
  let live := liveAll g target
  let redirect := ProductionClients.redirect g target live
  let c := chooseBy redirect
  let shifted := fun a => redirect (y.emitted++a)
  let pick := chooseBy shifted
  let tape := emit pick []
  let fresh (a : Word n) (v : Fin n) := ∃ j, v=ProductionClients.gate g target j ∧ live j a ∧
    AdmissionMask.credit (ProductionClients.issue g target j)
      (AdmissionMask.hitAt (ProductionClients.gate g target j) (live j)) a=true
  let localFresh := fun a v => fresh (y.emitted++a) v
  let nextGlobal : History s n → Fin n → History s n := next c i.val
  have c_ok : Consistent x c i.val y := ok
  have trace (a : Word n) :
      (runWord nextGlobal y a).emitted=y.emitted++tape a ∧
      (runWord nextGlobal y a).physical=rawRun y.physical (tape a) := by
    have q := after_tape c i.val y a
    have e : tape a=emit c y.emitted a := by
      change emit (fun b => c (y.emitted++b)) [] a = _
      simpa only [List.append_nil] using ReleaseTapeProjection.emit_shifted c y.emitted [] a
    simpa only [e] using q
  have play (a : Word n) :
      tape a=emit c y.emitted a := by
    change emit (fun b => c (y.emitted++b)) [] a = _
    simpa only [List.append_nil] using ReleaseTapeProjection.emit_shifted c y.emitted [] a
  have relation (a : Word n) :
      emit c [] (y.candidates++a)=y.emitted++tape a := by
    rw [ReleaseTapeProjection.emit_append, List.nil_append, ←c_ok.1, play]
  have two : OpenFenceLine.Twice (candidatePlay pick) := by
    have baseTwo : OpenFenceLine.Twice (fun a => c (emit c [] a)) :=
      CandidateResidence.candidates_supply_bonds P target (fun _ _ => True)
    have lifted := ReleaseTapeProjection.shifted_twice c y.candidates baseTwo
    rw [←c_ok.1] at lifted
    exact lifted
  obtain ⟨pre,mid,tail,S,len,fall,tapes,_,C,_,m,G,_⟩ := generated_at_every_history P o []
  let origin := rawRun (rawRun g.initial pre) mid
  let prior := tail++(g.past++y.emitted)
  let addr := fun k => S.getD k fall
  let root := (addr 0).1
  have originalRoot : root=(endpoint h g.hh o 0).1 := congrArg Prod.fst C.root
  have replay : rawRun origin prior=y.physical := by
    change rawRun (rawRun (rawRun g.initial pre) mid) (tail++(g.past++y.emitted))=y.physical
    rw [←raw_append, ←raw_append]
    rw [show pre++(mid++(tail++(g.past++y.emitted)))=((g.u++g.v)++g.past)++y.emitted by
      simp only [tapes,List.append_assoc]]
    rw [raw_append, g.here, c_ok.2.1]
  have fiber (z : Raw s n) (qz : Ready g z) (p : Fin n) :
      Layout (rows s) g.base p=Layout (rows s) z p := g.fiber z qz.1 p
  have stable (z : Raw s n) (qz : Ready g z) (e : Fin n) : Ready g (rawNext s z e) :=
    ready_next P qz e
  have offsets (z : Raw s n) (qz : Ready g z) : correct h g.hh 5 z := qz.2
  have readyWord (z : Raw s n) (q : Ready g z) (a : Word n) : Ready g (rawRun z a) := by
    induction a generalizing z with
    | nil => exact q
    | cons f a ih => exact ih _ (stable z q f)
  have originReady : Ready g origin := readyWord _ (readyWord _ ⟨g.init,g.offset⟩ pre) mid
  have clean : Current hp g.base addr len origin .idle := BStarGeneratedTapeCuts.at_start hp G
  obtain ⟨u,v,L,R,join,leftSize,rightSize⟩ := FenceEmbedding.two_strips hp C (radWidth s) (width g)
    (radius_pos P) g.flags g.notShort (terminal_le_width g) g.charts
  have inside (j : Fin n) : (longGeometry (rows s) (g.base j)).inside =
      decide (oldOrdinal (rows s) g.base g.hh j<radWidth s) := (g.flags j).1
  have oldMask : FreshOnly h g.hh fresh redirect := redirectTo_isFresh _ _ _ _
  have shiftedMask : FreshOnly h g.hh localFresh shifted := by
    intro a e f q
    exact oldMask (y.emitted++a) e f q
  have physical (a : Word n) (j : Fin n) (old : localFresh a j) :
      firstAdmission hp (base:=g.base) (hh:=g.hh) (rawRun y.physical a) j := by
    obtain ⟨k,rfl,eligible,_⟩ := old
    have prior := eligible.2.2
    change firstAdmission hp (base:=g.base) (hh:=g.hh) (rawRun x (y.emitted++a))
      (ProductionClients.gate g target k) at prior
    rw [raw_append, ←c_ok.2.1] at prior
    exact prior
  obtain ⟨D,z,mode,initial,q,cap,current,append,latch,stop⟩ :=
    released_owner_data hp C g.heads g.cont (Ready g) fiber stable (separation P) g.baseOffset offsets
      originReady clean prior replay L R join inside
      leftSize rightSize (width_bounds g).1 (Nat.le_refl _) (chart_sizes g C).1 shiftedMask physical two
  let project := fun (u : FenceEscrow.State (FenceEscrow.State (Tape n) n) n) => runWord nextGlobal y u.1.1.candidates
  have projectNext (u : FenceEscrow.State (FenceEscrow.State (Tape n) n) n) (e : Fin n) :
      project (D.next u e) = nextGlobal (project u) e := by
    change runWord nextGlobal y (D.next u e).1.1.candidates = _
    rw [append]
    simp only [project,runWord,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have projectInitial : project z=y := by simp only [project,initial,runWord,List.foldl_nil]
  refine ⟨_,D,project,z,projectInitial,q,cap,fun u _ _ e => projectNext u e,?_ ,?_⟩
  · intro done
    have impossible := (stop z).mp done
    rw [initial] at impossible
    contradiction
  · intro u _ no e done
    let a := u.1.1.candidates
    let before := runWord nextGlobal y a
    let f := c before.emitted e
    have openNow : u.1.1.released=false := Bool.eq_false_iff.mpr (fun t => no ((stop u).mpr t))
    have physicalRelease := (stop (D.next u e)).mp done
    rw [latch,openNow,Bool.false_or] at physicalRelease
    have stepGlobal : runWord nextGlobal y (a++[e])=nextGlobal before e := by
      simp only [before,runWord,List.foldl_append,List.foldl_cons,List.foldl_nil]
    have new : Current hp g.base addr len (rawNext s before.physical f) (mode (a++[e])) := by
      have Eq := (trace (a++[e])).2
      rw [stepGlobal] at Eq
      change rawNext s before.physical f = rawRun y.physical (tape (a++[e])) at Eq
      rw [Eq]
      exact current (a++[e])
    have on := (trace a).2
    have old : Current hp g.base addr len before.physical (mode a) := on.symm ▸ current a
    have genReplay : rawRun origin (prior++tape a)=before.physical := by
      rw [raw_append, replay, on]
    have reached := readyWord _ originReady (prior++tape a)
    rw [genReplay] at reached
    obtain ⟨oldMode,gen,_,oldCur⟩ :=
      generated_word hp C (Ready g) fiber stable (separation P) (prior++tape a) .idle originReady clean
    have oldCur' : Current hp g.base addr len before.physical oldMode := by
      rw [←genReplay]
      exact oldCur
    have sameMode : oldMode=mode a :=
      current_mode_unique hp _ _ oldCur' old
    have hist : GeneratedOwner hp g.base addr len origin .idle (prior++tape a) (mode a) :=
      sameMode ▸ gen
    obtain ⟨d,ev,curD⟩ := current_step hp C (Ready g) fiber stable (separation P) reached f (mode a) old
    have sameNew : d=mode (a++[e]) := current_mode_unique hp _ _ curD new
    have paid := mark_releases C (separation P) genReplay.symm f hist old (sameNew ▸ ev) physicalRelease
    have hc := consistency_after c_ok a
    have out : Consistent x c i.val (nextGlobal before e) := consistent_next x c i.val before hc e
    rw [projectNext]
    refine ⟨out,tape a,f,?_ ,?_⟩
    · change before.emitted++[f]=(y.emitted++tape a)++[f]
      rw [(trace a).1]
    · unfold accepted
      rw [←originalRoot,←(trace a).1,←hc.2.1]
      exact paid

/-- Supplies the five release-cycle premise of the global block theorem. -/
theorem release (P : Production g) (i : Header h) (j : Nat)
    (y : History s n) (ok : Consistent x (policy g i) i.val y) :
    Cycle g i y (fun z => z.published ∨ Consistent x (policy g i) i.val z ∧
      ∃ gap e,z.emitted=(y.emitted++gap)++[e] ∧
        accepted g (releaseClient g (ProductionClients.serviceOwner g i) j) (y.emitted++gap) e) :=
  Cycle.mono g (release_owner g P i (releaseClient g (ProductionClients.serviceOwner g i) j) y ok)
    (fun _ hgood => Or.inr hgood)

#print axioms release_owner
#print axioms release

end
end L4.Height.ReleaseStage
