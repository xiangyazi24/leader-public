import Leader.L4.WindowA0ReleaseFailure
import Leader.L4.WindowA0ReturnCheck
import Leader.L4.WindowA0EntryJoin

/-! Assemble the literal closed A0 trial from the approach/release and
return checkers. All raw marks, including between cuts, are retained. -/
namespace L4.WindowA0Uniform

open WindowA0SpliceTrial WindowA0Leg FixedResidual WindowFiveStages RootedAssembly TripleRenewal
open WindowA0ApproachJoin WindowA0ReturnHandoff
open Classical

abbrev Phys := WindowA0ClosedEntry.State

def goal {p c n : Nat} (x : Phys p c n) : Prop := WindowA0Ledger.done x.tag

def Start {p c n : Nat} (initial : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H j : Nat) (x : Phys p c n) : Prop :=
  goal x ∨ ∃ q : Trip (2*c), ordinal q=j ∧
    ApproachGood initial S J H q (⟨x,x.gap-1⟩ : AState p c n)

private theorem ord_le {Q : Nat} (q : Trip Q) : ordinal q≤Q := by
  cases q with
  | init => exact Nat.zero_le _
  | count k => exact k.isLt

private theorem ord_eq_rank {Q : Nat} (q : Trip Q) :
    ordinal q=WindowA0GapOneJoin.tripRank q := by cases q <;> rfl

private theorem doneBypass {n : Nat} (w : Word n)
    (h : FirstExit (acceptNow n).stop w) : w=[] := by
  cases w with
  | nil => rfl
  | cons e es => exact (h.1 0 (by simp) True.intro).elim

private theorem meanBypass (n B : Nat) :
    IIDExpectedHittingTimeAtMost wordNext (acceptNow n).stop [] B := by
  intro t
  rw [iidHitCost_of_target _ _ _ (show (acceptNow n).stop [] from trivial)]
  exact Nat.zero_le _

private theorem massBypass (n D t : Nat) :
    D*terminalMass wordNext (acceptNow n).stop (acceptNow n).bad t []≤(D-1)*n^t := by
  cases t <;> simp [acceptNow,terminalMass]

/-- Local stage stops at a spoiler/contact or at the next exact
accepted ordinal. An intermediate success is not the final physical D. -/
structure Phase {p c n : Nat} (initial : Config p c n) (S : WindowA0Ledger.Scope n)
    (J : Fin n) (H j : Nat) (x : Phys p c n) (B D : Nat) where
  check : Check n
  mean : IIDExpectedHittingTimeAtMost wordNext check.stop [] B
  mass : ∀ t, D*terminalMass wordNext check.stop check.bad t []≤(D-1)*n^t
  bad : ∀ w, FirstExit check.stop w → check.bad w → ¬goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w)
  pass : ∀ w, FirstExit check.stop w → ¬check.bad w →
    Start initial S J H j (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w)

def bypass {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H j B D : Nat} {x : Phys p c n} (h : Start initial S J H j x) :
    Phase initial S J H j x B D where
  check := acceptNow n
  mean := meanBypass n B
  mass := massBypass n D
  bad _ _ h := False.elim h
  pass w hw _ := (doneBypass w hw).symm ▸ h

private theorem leg_next {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H : Nat} {x : Phys p c n}
    {q : Trip (2*c)} {k : Fin (2*c)} {d : Nat}
    (ord : ordinal (.count k)=ordinal q+1)
    (had : WindowA0ClosedEntry.Admitted initial S J H x)
    (owned : WindowA0ApproachOwned.Physical J (.count k) x d) (atDoor : d+1=x.gap) :
    Start initial S J H (ordinal q+1) x := by
  have exactOffset : d=x.gap-1 := by omega
  refine .inr ⟨.count k,ord,had,.inr ⟨exactOffset ▸ owned,?_⟩⟩
  change x.gap-1=0 → x.gap=1
  omega

theorem gap_next {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H : Nat} {x : Phys p c n}
    {q : Trip (2*c)} (had : WindowA0ClosedEntry.Admitted initial S J H x)
    (hc : WindowA0GapOneJoin.continues J q x) : Start initial S J H (ordinal q+1) x := by
  obtain ⟨gap,k,rank,phys⟩ := hc
  apply leg_next (k:=k) (d:=0) ?_ had phys (by omega)
  change k.val+1=ordinal q+1
  rw [ord_eq_rank q]
  exact congrArg (·+1) rank

/-- Proof-selected suffix certificate. Pointwise use of the genuine
handoff means the continuation samples no additional edge. -/
noncomputable def connectPhase {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H j P B d D : Nat} {x : Phys p c n}
    (X : Check n) (hd : 0<d) (hD : 0<D)
    (meal : IIDExpectedHittingTimeAtMost wordNext X.stop [] P)
    (mass : ∀ t, d*terminalMass wordNext X.stop X.bad t []≤(d-1)*n^t)
    (bad : ∀ w, FirstExit X.stop w → X.bad w →
      ¬goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w))
    (Y : ∀ w, FirstExit X.stop w → ¬X.bad w →
      Phase initial S J H j (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w) B D) :
    Phase initial S J H j x (P+B) (d*D) := by
  let out (a : Word n) : Check n :=
    if ha : FirstExit X.stop a then
      if hb : ¬X.bad a then (Y a ha hb).check else acceptNow n
    else acceptNow n
  have out_eq (a : Word n) (ha : FirstExit X.stop a) (hb : ¬X.bad a) :
      out a=(Y a ha hb).check := by simp [out,ha,hb]
  refine ⟨join X out,?_,?_,?_,?_⟩
  · exact join_mean X out meal (fun a ha hb => out_eq a ha hb ▸ (Y a ha hb).mean)
  · apply join_failure X out hd hD mass
    intro a ha hb
    rw [out_eq a ha hb]
    exact (Y a ha hb).mass
  · intro w hw hb
    obtain ⟨a,u,E,ha,hle|hgt⟩ := join_first X out w hw
    · obtain ⟨hab,rfl,_⟩ := hle
      rw [E,List.append_nil]
      exact bad a ha hab
    · obtain ⟨hab,hs,hb'⟩ := hgt
      have ht := hb'.mp hb
      rw [out_eq a ha hab] at hs ht
      rw [E,GGTiming.runMarks_append]
      exact (Y a ha hab).bad u hs ht
  · intro w hw hb
    obtain ⟨a,u,E,ha,hle|hgt⟩ := join_first X out w hw
    · exact (hb hle.2.2).elim
    · obtain ⟨hab,hs,hb'⟩ := hgt
      have ht := fun h => hb (hb'.mpr h)
      rw [out_eq a ha hab] at hs ht
      rw [E,GGTiming.runMarks_append]
      exact (Y a ha hab).pass u hs ht

noncomputable def fullReturn {p c n : Nat} (hn : 4≤n) (hQ : 0<2*c)
    {initial : Config p c n} {S : WindowA0Ledger.Scope n} {J : Fin n}
    {H : Nat} (hs : H+2<n) {x : Phys p c n} {q : Trip (2*c)}
    (h : WindowA0ReturnEntry.Ready initial S J H x q 1 true) :
    Phase initial S J H (ordinal q+1) x (n*(H+1)) 3 := by
  have hb : x.gap≤H := (h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])).1.bounded
  have short : x.gap+2<n := by omega
  refine ⟨WindowA0ReturnCheck.check S q x 1 true, ?_, ?_, ?_, ?_⟩
  · exact expected_mono (WindowA0ReturnCheck.mean hn hQ h short)
      (Nat.mul_le_mul_left n (by omega))
  · simpa only [show 3-1=2 by decide] using WindowA0ReturnCheck.failure hn hQ h short
  · exact WindowA0ReturnCheck.first_contact_not_done S q x 1 true
  · intro w hw hb
    obtain hbad|hof := WindowA0ReturnCheck.first_exit hn hQ h short w hw
    · exact (hb hbad.1).elim
    · rcases hof.2 with hd|⟨k,d,_,ord,atDoor,had,owned⟩
      · exact .inl hd
      · exact leg_next ord had owned atDoor

noncomputable def followingRelease {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    {initial : Config p c n} (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (q : Trip (2*c)) (z : AState p c n)
    (hz : ApproachGood initial S J H q z) (w : Word n)
    (hw : FirstExit (releaseDone S z) w) (hb : ¬releaseBad S z w) :
    Phase initial S J H (ordinal q+1) (GGTiming.runMarks (WindowA0ClosedEntry.next S) z.physical w)
      (n*(H+1)) 3 := by
  let y := GGTiming.runMarks (WindowA0ClosedEntry.next S) z.physical w
  have h := release_to_return hn hQ S J H q z hz w hw hb
  by_cases done : goal y
  · exact bypass (.inl done)
  by_cases immediate : WindowA0GapOneJoin.continues J q y
  · have had := WindowA0ClosedEntry.close_word (by omega) S J H z.physical w hz.1
    exact bypass (gap_next had immediate)
  exact fullReturn (by omega) hQ hshort ((h.resolve_left done).resolve_right immediate)

private theorem worker_bound {p c n : Nat} {initial : Config p c n} {S : WindowA0Ledger.Scope n}
    {J : Fin n} {H : Nat} {q : Trip (2*c)} {z : AState p c n}
    (hz : ApproachGood initial S J H q z) (h : ¬goal z.physical) :
    z.worker≤H+1 := by
  have bound := (hz.1.resolve_left h).1.bounded
  have worker := (hz.2.resolve_left h).1.2.1
  change z.physical.gap≤H at bound
  omega

def legBudget (n H : Nat) := n*(2*(H+1)+3)

noncomputable def literalLeg {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    {initial : Config p c n} (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (q : Trip (2*c)) (z : AState p c n)
    (hz : ApproachGood initial S J H q z) (h : ¬goal z.physical) :
    Phase initial S J H (ordinal q+1) z.physical (legBudget n H) 648 := by
  let X : Check n := ⟨releaseDone S z,releaseBad S z⟩
  have C := literal_approach_release (by omega) S J H q z hz
  have T := connectPhase X (d:=216) (D:=3) (by decide) (by decide) C.1 C.2
    (WindowA0ReleaseFailure.first_release_bad_not_done hn S J H q z hz)
    (followingRelease hn hQ S J H hshort q z hz)
  have B : n*z.worker+n*3+n*(H+1)≤legBudget n H := by
    calc
      _ ≤ n*(H+1)+n*3+n*(H+1) :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left n (worker_bound hz h)) _) _
      _ = _ := by
        unfold legBudget
        rw [show 2*(H+1)=((H+1)+(H+1)) by omega]
        simp only [Nat.mul_add]
        ac_rfl
  exact { T with mean := expected_mono T.mean B }

private noncomputable def phaseAt {p c n : Nat} {initial : Config p c n}
    {S : WindowA0Ledger.Scope n} {J : Fin n} {H j : Nat} {x : Phys p c n}
    (hn : 5≤n) (hQ : 0<2*c) (hshort : H+2<n) (h : Start initial S J H j x) :
    Phase initial S J H (j+1) x (legBudget n H) 648 := by
  by_cases hd : goal x
  · exact bypass (.inl hd)
  have ex := h.resolve_left hd
  let q := choose ex
  obtain ⟨ord,hz⟩ := choose_spec ex
  rw [←ord]
  exact literalLeg hn hQ S J H hshort q ⟨x,x.gap-1⟩ hz hd

noncomputable def family {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) :
    LegFamily (WindowA0ClosedEntry.next S) goal (Start initial S J H) (2*c+1)
      (legBudget n H) 648 where
  cut _ _ _ h := (phaseAt hn hQ hshort h).check
  mean _ _ _ h := (phaseAt hn hQ hshort h).mean
  mass _ _ _ h := (phaseAt hn hQ hshort h).mass
  bad _ _ _ h := (phaseAt hn hQ hshort h).bad
  pass _ _ _ h w hs hb := .inr ((phaseAt hn hQ hshort h).pass w hs hb)
  last _ h := h.resolve_right (by
    rintro ⟨q,hr,_⟩
    have hh := ord_le q
    omega)

private def cleanup {p c n : Nat} (S : WindowA0Ledger.Scope n) (x : Phys p c n) :
    Check n := ⟨WindowA0CleanupLaunch.hit S x,fun _ => False⟩

private noncomputable def postCleanup {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (x : Phys p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) (hl : ¬goal x)
    (w : Word n) (hw : FirstExit (cleanup S x).stop w) :
    Verified (fun v => goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) x (w++v)))
      ((2*c+1)*legBudget n H) (648^(2*c+1)) := by
  let y := GGTiming.runMarks (WindowA0ClosedEntry.next S) x w
  have had := WindowA0ClosedEntry.close_word (by omega) S J H x w hx
  have launch : Start initial S J H 0 y := by
    by_cases hd : goal y
    · exact .inl hd
    have h := WindowA0CleanupLaunch.first_launch (by omega) S J H x hx hl w hw hd
    have hp : 0<y.gap := (had.resolve_left hd).1.gapPos
    refine .inr ⟨.init,rfl,had,.inr ⟨h,?_⟩⟩
    change y.gap-1=0 → y.gap=1
    omega
  rw [show (fun v => goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) x (w++v))) =
      (fun v => goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) y v)) by
    funext; rw [GGTiming.runMarks_append]]
  exact certifyLegs (family hn hQ initial S J H hshort) (by decide) (2*c+1) 0 (Nat.zero_add _) y launch

noncomputable def wordCert {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (x : Phys p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) (hl : ¬goal x) :
    Verified (fun w => goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w))
      (n*((3*H+2)*(2*c)+4*H+2)+(2*c+1)*legBudget n H) (1*648^(2*c+1)) :=
  verifiedJoin _ (cleanup S x) (by decide) (Nat.pow_pos (by decide))
    (WindowA0CleanupLaunch.word_mean (by omega) S J H x hx)
    (fun t => by simp [cleanup,no_failure]) (fun _ _ h => h.elim)
    (fun w hw _ => postCleanup hn hQ initial S J H hshort x hx hl w hw)

theorem wordCert_proper {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (x : Phys p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) (hl : ¬goal x) :
    ¬(wordCert hn hQ initial S J H hshort x hx hl).check.stop [] := by
  intro h
  obtain ⟨a,u,E,ha,_⟩ := h
  have N : a=[] := (List.append_eq_nil_iff.mp E.symm).1
  subst a
  exact WindowA0CleanupLaunch.properStart S J H x hx hl ha.2

/-- The literal A0 uniform attempt. The physical map in stage.project
runs every original scheduler label; only the stochastic observer cuts
are stopped. No unstated release, return, or renewal hypothesis. -/
noncomputable def physicalAttempt {p c n : Nat} (hn : 5≤n) (hQ : 0<2*c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (x : Phys p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) (hl : ¬goal x) :
    UniformAttempt (WindowA0ClosedEntry.next S) goal (WindowA0ClosedEntry.Admitted initial S J H)
      (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) x where
  stage := WindowA0Trial.trialStage S x (wordCert hn hQ initial S J H hshort x hx hl).check.stop
  properStart := wordCert_proper hn hQ initial S J H hshort x hx hl
  restart w _ _ _ := WindowA0ClosedEntry.close_word (by omega) S J H x w hx
  mean := expected_mono (wordCert hn hQ initial S J H hshort x hx hl).mean
    (WindowA0Trial.clock_budget c n H)
  failBound t := by
    change WindowA0Restart.attempts c * terminalMass wordNext
      (wordCert hn hQ initial S J H hshort x hx hl).check.stop
      (fun w => ¬goal (GGTiming.runMarks (WindowA0ClosedEntry.next S) x w)) t [] ≤ _
    simpa only [WindowA0Restart.attempts,Nat.one_mul] using
      (wordCert hn hQ initial S J H hshort x hx hl).goalMass t

theorem physical_attempt {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (x : Phys p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) (hl : ¬goal x) :
    Nonempty (UniformAttempt (WindowA0ClosedEntry.next S) goal
      (WindowA0ClosedEntry.Admitted initial S J H) (WindowA0Restart.attemptCost c n H)
      (WindowA0Restart.attempts c) x) :=
  ⟨physicalAttempt hn (by omega) initial S J H hshort x hx hl⟩

/-- Concrete closed-state block restart, with no uniform-attempt
parameter. The native word remains the full ring scheduler. -/
theorem physical_block_mean {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (initial : Config p c n) (S : WindowA0Ledger.Scope n) (J : Fin n)
    (H : Nat) (hshort : H+2<n) (x : Phys p c n)
    (hx : WindowA0ClosedEntry.Admitted initial S J H x) :
    IIDExpectedHittingTimeAtMost (WindowA0ClosedEntry.next S) goal x
      (2*(4*(3*WindowA0Restart.attempts c)*WindowA0Restart.attemptCost c n H)) :=
  WindowA0Bridge.state_block_mean (by omega) initial S J H
    (fun z hz hl => physical_attempt hn hc initial S J H hshort z hz hl) x hx

open WindowA0EntryJoin WindowA0StockDrain WindowSpan in
/-- The printed ordinary short two-ghost entry bound, now with all
post-drain trial hypotheses instantiated. -/
theorem physical_entry_exit_mean {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let S := entryScope x i
    IIDExpectedHittingTimeAtMost wordNext
      (fun w => (tape S.group S.iTag S.jTag (entryBase x i) (entryCursor x i) w).exit.isSome=true)
      [] (WindowA0Restart.entryK c*n*(WindowSpan.span x i+1)) :=
  entry_exit_mean (by omega) x i hm hv short h1 h2 (fun J H h  z hz hl =>
    physical_attempt hn hc x (entryScope x i) J H (by omega) z hz hl)

end L4.WindowA0Uniform
