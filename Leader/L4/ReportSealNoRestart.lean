import Leader.L4.ReportCentreSealOwner

namespace L4.ReportSealNoRestart
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier ShortResetChart
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerCommandRail
open ReportGenerationAncestry ReportLeaseOwner ReportIngressOwnership
open ReportOwnerProvenanceTransport ReportOwnerIssueControl ReportCentreSealOwner
open ReportOwnerAcquireReturn

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def PendingBeforeCentre (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  Retry0 d C x ∨ ∃ k,k≤C.a ∧ FullActive d C x (.fwd k)

theorem pending_centre_zero (d : Sheet) (C : Chart h) (x : Raw s n)
    (A : PendingBeforeCentre d C x) : (readPC d C x).2=0 := by
  rcases A with H|⟨k,_,H⟩
  · exact H.1
  · exact congrArg Prod.snd (pc_fields d C x .wait0 (by decide) H.1.1.2.1)

theorem pending_centre_no_event_step (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (e : Fin n)
    (A : PendingBeforeCentre d (charter G r) x)
    (E : NoSealEvent d (charter G r) x e) :
    PendingBeforeCentre d (charter G r) (rawNext s x e) := by
  let C := charter G r
  let CF := cached_fibre d N hh Q F
  rcases A with I|⟨k,J,I⟩
  · by_cases D : e=door C
    · subst e
      have P : ownerPC d C x=.issue0 := by
        change pcView (readPC d C x)=.issue0
        rw [show readPC d C x=(1,0) from Prod.ext I.2.1 I.1]
        decide
      exact .inr ⟨0,Nat.zero_le _,full_launch d C x N (CF.mask x X) P⟩
    · have L : LegalIssue d C x := ⟨by rw [I.1]; exact Nat.zero_le _,I.2⟩
      obtain ⟨B,PC⟩ := nondoor_preserves d C hh G F N x X L e D
      exact .inl ⟨(congrArg Prod.snd PC).trans I.1,B.2⟩
  · change k≤C.a at J
    have W := full_active_step d C CF x X N e (.fwd k) (by intro H; contradiction) I
    by_cases D : e=out C k
    · subst e
      have O := canonical_centre G r
      have A0 : C.a<C.L := O.2.1
      have K : k<C.a := by
        by_cases K : k=C.a
        · subst k
          have H : h (out C C.a)=true := O.2.2.1
          have L : C.route.port C.a=1 := O.2.2.2.1
          have T := tok_of_slot d C x C.a .forward0 (by decide) I.1.1.2.2.1
          rw [predecessor_projection,H,L] at T
          have F0 : publicationToken (params d s) true
              (selectBytes d (x (centre C))) 1=reset0Forward := T
          apply False.elim (E.1 rfl ?_)
          unfold reportHeaderResetSeal
          rw [rankReady_iff,F0]
          refine ⟨⟨rfl,?_⟩,rfl,rfl⟩
          intro Q
          have A := Q.1.2.2
          change 0=admitOp (params d s) at A
          unfold admitOp at A
          omega
        · omega
      have V : k+1<C.L := by omega
      have Dst : nextStage C (out C k) (.fwd k)=.fwd (k+1) := by
        change (if out C k=out C k then if k+1<C.L then Stage.fwd (k+1)
          else Stage.rev k else Stage.fwd k)=_
        rw [if_pos rfl,if_pos V]
      rw [Dst] at W
      exact .inr ⟨k+1,Nat.succ_le_of_lt K,W⟩
    · have Dst : nextStage C e (.fwd k)=.fwd k := by
        change (if e=out C k then if k+1<C.L then Stage.fwd (k+1)
          else Stage.rev k else Stage.fwd k)=_
        rw [if_neg D]
      rw [Dst] at W
      exact .inr ⟨k,J,W⟩

private theorem nr_end (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (P : (readPC d C x).2≠0) (A : NoRestartTape d C x w) :
    (readPC d C (rawRun x w)).2≠0 := by
  induction w generalizing x with
  | nil => exact P
  | cons e w IH => exact IH _ A.1 A.2

private theorem nr_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (A : NoRestartTape d C x w)
    (B : (readPC d C (rawNext s (rawRun x w) e)).2≠0) :
    NoRestartTape d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨B,trivial⟩
  | cons a w IH => exact ⟨A.1,IH _ A.2 B⟩

/-- After the actual installation of a seal, a prefix with no centre
seal event cannot run a complete new generation and return to a
positive opcode: every RESET must pass the same centre. The proof
does not require the root grant to remain held across abort. -/
theorem no_restart_between_seal_events (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q) (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d (charter G r) x)
    (w : List (Fin n)) (T : NoSealTape d (charter G r) x w)
    (Pos : (readPC d (charter G r) x).2≠0)
    (End : (readPC d (charter G r) (rawRun x w)).2≠0) :
    NoRestartTape d (charter G r) x w := by
  let C := charter G r
  have A : NoRestartTape d C x w ∨ PendingBeforeCentre d C (rawRun x w) := by
    clear End
    induction T with
    | nil => exact .inl trivial
    | @snoc pre e T E IH =>
      let a := rawRun x pre
      let y := rawNext s a e
      have Z := strong_run d C N hh G F digit x X S pre
      rw [ShortOwnerEpochJS.raw_snoc]
      rcases IH with H|H
      · by_cases P : (readPC d C y).2=0
        · have R := zero_is_retry d C N hh G F digit a Z.1 Z.2.1 e
            (nr_end d C x pre Pos H) P
          exact .inr (.inl R.2)
        · exact .inl (nr_snoc d C x pre e H P)
      · exact .inr (pending_centre_no_event_step d G r N hh F a Z.1 e H E)
  exact A.elim id (fun H=>(End (pending_centre_zero d C _ H)).elim)

/-- At accepted COMMIT ingress the installed seal belongs to the
same nonrestart controller generation as the old token. This avoids a
circular need for the indexed staging history in detecting reset. -/
theorem accepted_commit_no_restart_since_seal (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (a : Raw s n) (A : Cached d hh Q a) (flight : List (Fin n))
    (R : Generated d (charter G r) a flight .done) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (e : Fin n)
    (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : let x := rawRun (rawRun a flight) w
      ancestryCommitOpportunity (params d s) (h e) true (selectBytes d (x e))
        (selectBytes d (x (centre (charter G r))))) :
    let C := charter G r
    let x0 := rawRun a flight
    let x := rawRun x0 w
    ∃ pre post : List (Fin n), w=pre++(centre C::post) ∧
      let old := rawRun x0 pre
      let sealed := rawNext s old (centre C)
      (readPC d C old).2=sealOp (params d s) ∧
      reportHeaderSetSeal (params d s) (selectBytes d (old (centre C))) ∧
      (tok d C old C.a).payload=(tok d C x (C.a-1)).payload ∧
      centreSeal d C sealed=some (tok d C x (C.a-1)).payload ∧
      NoSealTape d C sealed post ∧ NoRestartTape d C sealed post := by
  dsimp only
  let C := charter G r
  let x0 := rawRun a flight
  let x := rawRun x0 w
  let p := params d s
  obtain ⟨⟨pre,post,W,PC0,Guard,D,B,No⟩,_⟩ :=
    commit_uses_last_centre_seal d G r N hh F a A flight R digit w e atCentre Accept
  let old := rawRun x0 pre
  let sealed := rawNext s old (centre C)
  have X := (cached_genuine_full_parked d C N hh F a A flight R).1
  have S := seed_receipt d C N hh F a A flight R
  have P := strong_run d C N hh G F digit x0 X S pre
  have Z := strong_run d C N hh G F digit x0 X S w
  let CF := cached_fibre d N hh Q F
  have E0 : centre C≠door C :=
    Ne.symm (ReportChartPartition.door_not_outgoing C C.a (canonical_centre G r).2.1)
  have Pos : (readPC d C sealed).2≠0 := by
    rw [raw_nondoor_control d C old (centre C) N (CF.mask old P.1) E0,PC0]
    unfold sealOp
    omega
  have Ne : e≠centre C := fun H=>edge_sep N e (H.trans atCentre.symm)
  have Pc : (readPC d C x).2=commitOp p := by
    rcases centre_seal_marks d G r N x e (CF.mask _ Z.1) Z.2.1 with
      H|H|H|⟨K,_⟩
    · exact (Ne H.1).elim
    · exact (Ne H.1).elim
    · exact H.2.2.1
    · exact (K.2.2 atCentre Accept).elim
  have Replay : x=rawRun sealed post := by
    unfold x
    rw [W,ShortOwnerEpochJS.raw_append]
    rfl
  have End : (readPC d C (rawRun sealed post)).2≠0 := by
    rw [←Replay,Pc]
    unfold p commitOp
    omega
  exact ⟨pre,post,W,PC0,Guard,D,B,No,no_restart_between_seal_events
    d G r N hh F digit sealed (CF.closed _ _ P.1)
    (strong_step d C N hh G F old P.1 P.2.1 digit (centre C)) post No Pos End⟩

end L4.ReportSealNoRestart
