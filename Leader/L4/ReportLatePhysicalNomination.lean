import Leader.L4.ReportGeneratedTail
import Leader.L4.ReportSealReverse
import Leader.L4.ReportFastRawEvent
import Leader.L4.ResetReturnIID

namespace L4.ReportLatePhysicalNomination
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerForwardControl ReportOwnerIssueControl ReportOwnerReverseControl
open ReportByteRows ReportRawProjection ReportWriteSplit ReportSealCommitOrigin
open ReportLeaseOwner ReportIngressOwnership ReportGenerationAncestry ReportOwnerCommandRail
open ReportOwnerAcquireReturn ReportSealReverse ReportGuardedTailSuccess ReportGeneratedTail ReportSealDescriptor ReportFastRawEvent
open ReportOwnerAcquireProvenance (NoConsume)

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- Late identity-steering stages. Debts count only the nominated raw
labels up to the first ingress; no subsequent COMMIT ACK is charged. -/
inductive Stage where
  | sealIssue | sealForward (i : Nat) | sealBack (i : Nat)
  | commitIssue | commitForward (i : Nat) | done
  deriving DecidableEq

def debt (L a : Nat) : Stage→Nat
  | .sealIssue => a+2*L+3
  | .sealForward i => a+2+2*L-i
  | .sealBack i => a+2+i
  | .commitIssue => a+1
  | .commitForward i => a-i
  | .done => 0

def nomination (C : Chart h) : Stage → Option (Fin n)
  | .sealIssue | .commitIssue | .sealBack 0 => some (door C)
  | .sealBack (i+1) | .sealForward i | .commitForward i => some (out C i)
  | .done => none

/-- Rank arithmetic for precisely the physical cursor moves. -/
inductive Advance (L a : Nat) : Stage→Stage→Prop
  | sealIssue (P : 0<L) : Advance L a .sealIssue (.sealForward 0)
  | sealHop {i : Nat} (P : i+1<L) : Advance L a (.sealForward i) (.sealForward (i+1))
  | sealTurn {i : Nat} (P : i+1=L) : Advance L a (.sealForward i) (.sealBack i)
  | sealReturn {i : Nat} : Advance L a (.sealBack (i+1)) (.sealBack i)
  | sealConsume : Advance L a (.sealBack 0) .commitIssue
  | commitIssue (P : 0<a) : Advance L a .commitIssue (.commitForward 0)
  | commitHop {i : Nat} (P : i+1<a) : Advance L a (.commitForward i) (.commitForward (i+1))
  | commitIngress {i : Nat} (P : i+1=a) : Advance L a (.commitForward i) .done

theorem debt_strict {L a : Nat} {q q' : Stage} (H : Advance L a q q') :
    debt L a q'<debt L a q := by
  cases H <;> simp [debt] <;> omega

/-- The selected reverse label cannot be a hold: the old predecessor
literally becomes the unique canonical D. PC is unchanged. -/
theorem seal_reverse_nominated (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (j : Nat) (R : SealD d C x (j+1)) :
    SealD d C (rawNext s x (out C j)) j := by
  have J : j<C.L := Nat.lt_trans (Nat.lt_succ_self _) R.shape.2.1
  have ND := (ReportChartPartition.door_not_outgoing C j J).symm
  have T := raw_seal_reverse_hop d C x N ((cached_fibre d N hh Q F).mask x X) j R
  rcases seal_reverse_step d C hh G F N x X (j+1) R digit (out C j) (.inl ND)
    with A|⟨k,K,_,A⟩
  · have E := A.shape.2.2 j J
    rw [T] at E
    simp [Reply,ReportOwnerReverseShape.backTag] at E
  · have E : k=j := by omega
    exact E ▸ A

/-- A COMMIT at a non-ingress cursor makes the real nominated hop,
and the exact packet survives that hop. -/
theorem commit_forward_nominated (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (J : i+1<C.L)
    (t : Tok) (R : ForwardWait d C x i)
    (P : tok d C x i=t) (H : SealCommitForward (params d s) t)
    (O : t.opcode=commitOp (params d s))
    (Guard : BeforeCommitIngress C t.opcode (params d s) i) :
    let y := rawNext s x (out C i)
    ForwardWait d C y (i+1) ∧ tok d C y (i+1)=t ∧ readPC d C y=readPC d C x := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  have Z := commit_hop_without_ingress d C N x (CF.mask x X) i J t P H O Guard
  refine ⟨?_,Z,forward_step_control d C N hh F x X i R (out C i)⟩
  rcases ReportOwnerForwardControl.all_mark d C hh G F N x X i R (out C i)
    with A|⟨_,A|⟨K,_⟩⟩
  · have E := A.2.2 (i+1) J
    rw [Z,H.1] at E
    simp [frontTag,show ¬i+1<i by omega] at E
  · exact A
  · omega

/-- Forward labels other than the selected old front hold the cursor
and the source PC, regardless of the token's opcode. -/
theorem forward_nonnominated (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (i : Nat) (A : ForwardWait d C x i)
    (e : Fin n) (E : e≠out C i) :
    ForwardWait d C (rawNext s x e) i ∧ readPC d C (rawNext s x e)=readPC d C x := by
  refine ⟨?_,forward_step_control d C N hh F x X i A e⟩
  rcases ReportOwnerForwardControl.all_mark d C hh G F N x X i A e with R|⟨T,_⟩
  · exact R
  · exact (E T).elim

private theorem nc_rev (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (A : SealD d C x k) (e : Fin n)
    (E : e≠door C ∨ k≠0) : NoConsume d C x e := by
  rcases E with D|D
  · exact .inl D
  · right
    rw [A.shape.2.2 0 C.positive]
    simp [ReportOwnerReverseShape.backTag,show 0<k by omega]

theorem seal_reverse_nonnominated (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (A : SealD d C x k) (e : Fin n)
    (E : nomination C (.sealBack k)≠some e) :
    SealD d C (rawNext s x e) k := by
  have ND : e≠door C ∨ k≠0 := by
    cases k with
    | zero =>
      left
      intro H
      exact E (congrArg some H.symm)
    | succ k => exact .inr (by omega)
  rcases seal_reverse_step d C hh G F N x X k A digit e (nc_rev d C x k A e ND)
    with T|⟨j,K,B,T⟩
  · exact T
  · subst k
    exact (E (congrArg some B.symm)).elim

/-- Non-owner-door marks at either legal late ISSUE cannot introduce a
new token or a new source opcode. -/
theorem issue_nonnominated (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (e : Fin n) (E : e≠door C) :
    LegalIssue d C (rawNext s x e) ∧ readPC d C (rawNext s x e)=readPC d C x :=
  nondoor_preserves d C hh G F N x X I e E

def On (d : Sheet) (C : Chart h) (x : Raw s n) : Stage→Prop
  | .sealIssue => LegalIssue d C x ∧ readPC d C x=(1,sealOp (params d s))
  | .sealForward i => ForwardWait d C x i ∧ readPC d C x=(2,sealOp (params d s))
  | .sealBack i => SealD d C x i
  | .commitIssue => LegalIssue d C x ∧ readPC d C x=(1,commitOp (params d s))
  | .commitForward i =>
    i<C.a ∧ ForwardWait d C x i ∧ readPC d C x=(2,commitOp (params d s))
  | .done => True

private def sourceGood (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  let p := params d s
  let cmp := comparisonFile p (selectBytes d (x C.root))
  cmp/4≠3 ∧ cmp%4≠3

/-- Semantic side conditions already delivered separately by the
genuine arithmetic/held-lease and indexed suffix producer. -/
def Enabled (d : Sheet) (G : GapInput h) (r : Owner h) (x : Raw s n) : Stage→Prop :=
  let C := charter G r
  let p := params d s
  fun q => match q with
  | .sealIssue | .commitIssue => sourceGood d C x
  | .sealForward i =>
    let t := tok d C x i
    SealCommitForward p t ∧ t.opcode=sealOp p ∧
      (h (out C i)=true → C.route.port i=1 →
        reportOldGrant p (bytesL d x (out C i)) 1=true ∧
        publicationSelector p (bytesL d x (out C i))=t.payload/8)
  | .sealBack _ => True
  | .commitForward i =>
    let t := tok d C x i
    SealCommitForward p t ∧ t.opcode=commitOp p ∧
      (i+1=C.a → ∃ j : Owner h, j.val=centre C ∧ classify d h x (out C i)=some j)
  | .done => False

/-- Exact local nomination/no-stutter on identity steering. Every
non-nominated actual mark holds the physical pose. At the ingress,
the terminal result is an event on the old state and the actual mark. -/
theorem late_row (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (q : Stage) (I : On d (charter G r) x q) (E : Enabled d G r x q)
    (e : Fin n) :
    let C := charter G r
    let y := rawNext s x e
    (nomination C q≠some e ∧ On d C y q) ∨
      (nomination C q=some e ∧ ∃ q', On d C y q' ∧ Advance C.L C.a q q' ∧
        (q'=.done → ∃ j : Owner h, j.val=centre C ∧ classify d h x e=some j)) := by
  dsimp only
  let C := charter G r
  let p := params d s
  obtain ⟨Pos,_,_,_,_⟩ := canonical_centre G r
  have AS : 0<C.a := Pos
  cases q with
  | sealIssue =>
    by_cases D : e=door C
    · subst e
      have V := ReportSealCommitLaunch.launch d C hh G F N x X I.1 (sealOp p) (.inl rfl) I.2 E
      exact .inr ⟨rfl, .sealForward 0,⟨V.2.1,V.2.2.1⟩,.sealIssue C.positive,fun H=>by cases H⟩
    · exact .inl ⟨fun H=>D (Option.some.inj H).symm,
        ⟨(issue_nonnominated d C N hh G F x X I.1 e D).1,
         (issue_nonnominated d C N hh G F x X I.1 e D).2.trans I.2⟩⟩
  | sealForward i =>
    by_cases D : e=out C i
    · subst e
      by_cases J : i+1<C.L
      · have B := seal_step_success d C N hh G F x X i J I.1 _ rfl E.1 E.2.1 E.2.2
        exact .inr ⟨rfl,.sealForward (i+1),⟨B.2.1,B.2.2.1.trans I.2⟩,.sealHop J,fun H=>by cases H⟩
      · have H := I.1.2.1
        have K : i+1=C.L := by change i<C.L at H; omega
        have B := healthy_seal_terminal d C N hh G F x X i K I.1 I.2 E.1 E.2.1
        exact .inr ⟨rfl,.sealBack i,B.2,.sealTurn K,fun H=>by cases H⟩
    · have B := forward_nonnominated d C N hh G F x X i I.1 e D
      exact .inl ⟨fun H=>D (Option.some.inj H).symm,⟨B.1,B.2.trans I.2⟩⟩
  | sealBack i =>
    by_cases D : nomination C (.sealBack i)=some e
    · cases i with
      | zero =>
        have H : door C=e := Option.some.inj D
        subst e
        have V := seal_root_consume d C hh G F N x X I digit
        have J : LegalIssue d C (rawNext s x (door C)) := by
          refine ⟨?_,V.2.1⟩
          rw [V.2.2]
          exact Nat.le_refl _
        exact .inr ⟨rfl,.commitIssue,⟨J,V.2.2⟩,.sealConsume,fun H=>by cases H⟩
      | succ j =>
        have H : out C j=e := Option.some.inj D
        subst e
        exact .inr ⟨rfl,.sealBack j,seal_reverse_nominated d C N hh G F digit x X j I,
          .sealReturn,fun H=>by cases H⟩
    · exact .inl ⟨D,seal_reverse_nonnominated d C N hh G F digit x X i I e D⟩
  | commitIssue =>
    by_cases D : e=door C
    · subst e
      have V := ReportSealCommitLaunch.launch d C hh G F N x X I.1 (commitOp p) (.inr rfl) I.2 E
      exact .inr ⟨rfl,.commitForward 0,⟨AS,V.2.1,V.2.2.1⟩,.commitIssue AS,fun H=>by cases H⟩
    · have V := issue_nonnominated d C N hh G F x X I.1 e D
      exact .inl ⟨fun H=>D (Option.some.inj H).symm,⟨V.1,V.2.trans I.2⟩⟩
  | commitForward i =>
    by_cases D : e=out C i
    · subst e
      by_cases J : i+1<C.a
      · have A := (canonical_centre G r).2.1
        have H : i+1<C.L := Nat.lt_trans J A
        have Before : BeforeCommitIngress C (tok d C x i).opcode p i := by
          apply ReportLateIngressSplit.no_prior_ingress
          intro _
          omega
        have V := commit_forward_nominated d C N hh G F x X i H _ I.2.1 rfl E.1 E.2.1 Before
        exact .inr ⟨rfl,.commitForward (i+1),⟨J,V.1,V.2.2.trans I.2.2⟩,.commitHop J,fun H=>by cases H⟩
      · have K : i+1=C.a := by have H := I.1; change i<C.a at H; omega
        exact .inr ⟨rfl,.done,trivial,.commitIngress K,fun _=>E.2.2 K⟩
    · have V := forward_nonnominated d C N hh G F x X i I.2.1 e D
      exact .inl ⟨fun H=>D (Option.some.inj H).symm,⟨I.1,V.1,V.2.trans I.2.2⟩⟩
  | done => exact E.elim

def paidPhase (L a : Nat) : Stage→Stage
  | .sealIssue => .sealForward 0
  | .sealForward i => if i+1<L then .sealForward (i+1) else .sealBack i
  | .sealBack 0 => .commitIssue
  | .sealBack (i+1) => .sealBack i
  | .commitIssue => .commitForward 0
  | .commitForward i => if i+1<a then .commitForward (i+1) else .done
  | .done => .done

theorem paid_eq (L a : Nat) {q q' : Stage} (H : Advance L a q q') :
    paidPhase L a q=q' := by
  cases H with
  | sealIssue _ | sealReturn | sealConsume | commitIssue _ => rfl
  | sealHop H => simp [paidPhase,H]
  | sealTurn H => simp [paidPhase,H]
  | commitHop H => simp [paidPhase,H]
  | commitIngress H => simp [paidPhase,H]

def nextPhase (C : Chart h) (q : Stage) (e : Fin n) : Stage :=
  if nomination C q=some e then paidPhase C.L C.a q else q

theorem next_value (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (q : Stage) (I : On d (charter G r) x q) (E : Enabled d G r x q)
    (e : Fin n) :
    let C := charter G r
    let q' := nextPhase C q e
    On d C (rawNext s x e) q' ∧ debt C.L C.a q'≤debt C.L C.a q ∧
      (nomination C q=some e → debt C.L C.a q'<debt C.L C.a q) ∧
      (q'=.done → ∃ j : Owner h, j.val=centre C ∧ classify d h x e=some j) := by
  dsimp only
  let C := charter G r
  rcases late_row d N hh G r F digit x X q I E e with ⟨NE,Hold⟩|⟨Is,V,A,R,Hit⟩
  · have Q' : q≠.done := by intro M; subst q; exact E
    rw [nextPhase,if_neg NE]
    exact ⟨Hold,Nat.le_refl _,fun H=>(NE H).elim,fun H=>(Q' H).elim⟩
  · rw [nextPhase,if_pos Is,paid_eq _ _ R]
    have L := debt_strict R
    exact ⟨A,Nat.le_of_lt L,fun _=>L,Hit⟩

theorem debt_positive (d : Sheet) (C : Chart h) (x : Raw s n) (q : Stage)
    (I : On d C x q) (Q : q≠.done) : 0<debt C.L C.a q := by
  cases q with
  | sealIssue | sealBack _ | commitIssue => simp [debt] <;> omega
  | sealForward i =>
    have V := I.1.2.1
    simp only [debt]
    omega
  | commitForward i =>
    have K := I.1
    simp only [debt]
    omega
  | done => exact (Q rfl).elim

theorem nomination_exists (C : Chart h) (q : Stage) (Q : q≠.done) :
    ∃ e, nomination C q=some e := by
  cases q with
  | sealIssue | commitIssue => exact ⟨door C,rfl⟩
  | sealForward k | commitForward k => exact ⟨out C k,rfl⟩
  | sealBack k => cases k with
    | zero => exact ⟨door C,rfl⟩
    | succ k => exact ⟨out C k,rfl⟩
  | done => exact (Q rfl).elim

def monitor (_d : Sheet) (C : Chart h) (z : Raw s n × Stage) (e : Fin n) :
    Raw s n × Stage := (rawNext s z.1 e,nextPhase C z.2 e)

def Finished (z : Raw s n × Stage) : Prop := z.2=.done

/-- History invariant supplier only: pose and progress are literal rows. -/
theorem expected_with_enabled_producer (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (Inv : Raw s n × Stage→Prop)
    (Base : ∀ z, Inv z → Cached d hh Q z.1 ∧ On d (charter G r) z.1 z.2 ∧ Enabled d G r z.1 z.2)
    (Keep : ∀ z e, Inv z → ¬Finished (monitor d (charter G r) z e) →
      Inv (monitor d (charter G r) z e))
    (x : Raw s n) (Initial : Inv (x,.sealIssue)) :
    Height.IIDExpectedHittingTimeAtMost (monitor d (charter G r)) Finished (x,.sealIssue)
      (n*((charter G r).a+2*(charter G r).L+3)) := by
  let C := charter G r
  let live (z : Raw s n × Stage) (b : Nat) := Inv z ∧ debt C.L C.a z.2=b
  have Pos (z : Raw s n × Stage) (b : Nat) (H : live z b) : 0<b := by
    rw [←H.2]
    apply debt_positive d C z.1 z.2 (Base z H.1).2.1
    intro E
    have H' := (Base z H.1).2.2
    rw [E] at H'
    exact H'
  have Step (z : Raw s n × Stage) (b : Nat) (H : live z b) :
      ∃ a : Fin n, ∀ e, Finished (monitor d C z e) ∨
        ∃ b',live (monitor d C z e) b' ∧ b'≤b ∧ (e=a→b'<b) := by
    obtain ⟨Cache,Pose,En⟩ := Base z H.1
    have ND : z.2≠.done := by intro E; rw [E] at En; exact En
    obtain ⟨a,A⟩ := nomination_exists C z.2 ND
    refine ⟨a,fun e=>?_⟩
    by_cases D : Finished (monitor d C z e)
    · exact .inl D
    · have R := next_value d N hh G r F digit z.1 Cache z.2 Pose En e
      refine .inr ⟨_,⟨Keep z e H.1 D,rfl⟩,?_ ,?_⟩
      · rw [←H.2]
        exact R.2.1
      · intro E
        subst e
        rw [←H.2]
        exact R.2.2.1 A
  exact ResetReturnIID.iid_of_relational_rank (monitor d C) Finished live Pos Step
    (x,.sealIssue) _ (.inr ⟨Initial,rfl⟩)

/-- Terminal credit on the monitor's same raw word, not after-the-fact
selection of an unrelated accepting state. -/
theorem finished_has_classified_mark (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (Inv : Raw s n × Stage→Prop)
    (Base : ∀ z, Inv z → Cached d hh Q z.1 ∧ On d (charter G r) z.1 z.2 ∧ Enabled d G r z.1 z.2)
    (Keep : ∀ z e, Inv z → ¬Finished (monitor d (charter G r) z e) →
      Inv (monitor d (charter G r) z e))
    (z : Raw s n × Stage) (Initial : Inv z) (w : List (Fin n))
    (Done : Finished (w.foldl (monitor d (charter G r)) z)) :
    ∃ u v : List (Fin n), ∃ e : Fin n, ∃ j : Owner h,
      w=u++e::v ∧ j.val=centre (charter G r) ∧
      classify d h (rawRun z.1 u) e=some j := by
  let C := charter G r
  induction w generalizing z with
  | nil =>
    have En := (Base z Initial).2.2
    change z.2=.done at Done
    rw [Done] at En
    exact En.elim
  | cons e w IH =>
    let y := monitor d C z e
    by_cases D : Finished y
    · obtain ⟨X,I,E⟩ := Base z Initial
      have Val := next_value d N hh G r F digit z.1 X z.2 I E e
      obtain ⟨j,A,B⟩ := Val.2.2.2 D
      exact ⟨[],w,e,j,rfl,A,B⟩
    · obtain ⟨u,v,a,j,W,E,B⟩ := IH y (Keep z e Initial D) Done
      exact ⟨e::u,v,a,j,by rw [W]; rfl,E,B⟩

end L4.ReportLatePhysicalNomination
