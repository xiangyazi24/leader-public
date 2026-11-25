import Leader.L4.ReportLatePhysicalNomination

namespace L4.ReportLateEnabledInvariant
open AllSizeProtocol PhysicalCustody ShortResetChart ReportResetBarrier
open ShortResetCycle (Chart edge_sep)
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerForwardControl ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerReverseShape ReportOwnerSerial
open ReportByteRows ReportRawProjection ReportWriteSplit ReportSealCommitOrigin
open ReportLeaseOwner ReportIngressOwnership ReportGenerationAncestry ReportOwnerCommandRail
open ReportOwnerAcquireReturn ReportSealReverse ReportGuardedTailSuccess ReportGeneratedTail
open ReportSealDescriptor ReportFastRawEvent ReportIndexedSourcePrefix ReportSealDescriptorTransport
open ReportLatePhysicalNomination ReportLeaseGrants ReportCentreSealOwner
open ReportOwnerAcquireProvenance (BeforeConsume NoConsume)

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

noncomputable def target (G : GapInput h) (r : Owner h) : Owner h :=
  ⟨centre (charter G r), (canonical_centre G r).2.2.1⟩

def sealToken (p : Params) (desc : Nat) : Tok :=
  {tag:=2,opcode:=sealOp p,payload:=desc}

def commitToken (p : Params) (desc : Nat) : Tok :=
  {tag:=2,opcode:=commitOp p,payload:=desc}

def PayloadOn (d : Sheet) (C : Chart h) (x : Raw s n) (desc : Nat) : Stage→Prop
  | .sealIssue => True
  | .sealForward i => tok d C x i=sealToken (params d s) desc ∧
      (C.a<i→centreSeal d C x=some desc)
  | .sealBack _ | .commitIssue => centreSeal d C x=some desc
  | .commitForward i => tok d C x i=commitToken (params d s) desc ∧
      centreSeal d C x=some desc
  | .done => False

structure Live (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop)
    (G : GapInput h) (r : Owner h) (seed : Raw s n) (z : Raw s n × Stage) : Prop where
  cached : Cached d hh Q z.1
  serial : StrongSerial d (charter G r) z.1
  pose : On d (charter G r) z.1 z.2
  original : file d (charter G r) z.1=file d (charter G r) seed
  compat : Compatible (rawGrant d z.1 (centre (charter G r)))
  hold : rawGrant d z.1 (centre (charter G r)) 1=true
  selector : rawSelector d z.1 (centre (charter G r))=
    descriptor (params d s) (selectBytes d (seed (charter G r).root))/8
  data : PayloadOn d (charter G r) z.1
    (descriptor (params d s) (selectBytes d (seed (charter G r).root))) z.2

theorem enabled_of_live (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (seed : Raw s n)
    (Good : let C := charter G r; let c := comparisonFile (params d s) (selectBytes d (seed C.root))
      c/4≠3 ∧ c%4≠3)
    (x : Raw s n) (q : Stage) (H : Live d hh Q G r seed (x,q)) :
    Enabled d G r x q := by
  let C := charter G r
  let p := params d s
  let desc := descriptor p (selectBytes d (seed C.root))
  have Eq := comparison_of_file_eq p (selectBytes d (x C.root)) _ H.original
  have Gd : let c := comparisonFile p (selectBytes d (x C.root)); c/4≠3 ∧ c%4≠3 := by
    dsimp only
    rw [Eq]
    exact Good
  cases q with
  | sealIssue | commitIssue => exact Gd
  | sealBack _ => trivial
  | done => exact H.data
  | sealForward i =>
    have T : tok d C x i=sealToken p desc := H.data.1
    have P : ForwardWait d C x i := H.pose.1
    unfold Enabled
    dsimp only
    rw [T]
    refine ⟨ReportSealCommitLaunch.descriptor_forward p _ _ (.inl rfl),rfl,?_⟩
    intro Hd Ln
    have E := (ReportOwnerAcquireProvenance.centre_geometry C G).2 i P.2.1 |>.mp ⟨Hd,Ln⟩
    subst i
    exact ⟨H.hold,H.selector⟩
  | commitForward i =>
    have T : tok d C x i=commitToken p desc := H.data.1
    unfold Enabled
    dsimp only
    rw [T]
    refine ⟨ReportSealCommitLaunch.descriptor_forward p _ _ (.inr rfl),rfl,?_⟩
    intro At
    let e := out C i
    have E : i=C.a-1 := by change i+1=C.a at At; omega
    have R : rightNeighbor e=centre C := by
      change rightNeighbor (out C i)=centre C
      rw [chart_succ,At]
      rfl
    let j := target G r
    have M := (cached_fibre d N hh Q F).mask x H.cached
    refine ⟨j,rfl,(classify_iff d h x e j).mpr ⟨R,?_,?_⟩⟩
    · rw [M,R]
      exact j.property
    · have Port : C.route.port i=0 := by rw [E]; exact (canonical_centre G r).2.2.2.2
      rw [predecessor_projection,Port] at T
      rw [M e,R]
      change CommitGuard p (h e) (selectBytes d (x e)) (selectBytes d (x (centre C)))
        (oldReportToken p (h e) (selectBytes d (x e)) 0).payload
      have P : oldReportToken p (h e) (selectBytes d (x e)) 0=commitToken p desc := T
      rw [P]
      exact ⟨P,H.hold,H.selector,H.data.2⟩


private theorem off_front (d : Sheet) (C : Chart h) (x : Raw s n) (k i : Nat)
    (R : ForwardWait d C x k) (I : i<C.L) (H : k≠i) : (tok d C x i).tag≠2 := by
  rw [R.2.2 i I]
  unfold frontTag
  split
  · decide
  · rw [if_neg H.symm]
    decide

private theorem rev_not_front (d : Sheet) (C : Chart h) (x : Raw s n) (k i : Nat)
    (R : ReverseWait d C x k) (I : i<C.L) : (tok d C x i).tag≠2 := by
  rw [R.2.2 i I]
  unfold backTag
  split <;> try decide
  split <;> decide

private theorem old_pos {d : Sheet} {G : GapInput h} {r : Owner h}
    {x : Raw s n} {q : Stage} (I : On d (charter G r) x q)
    (E : q≠.done) : (readPC d (charter G r) x).2≠0 := by
  cases q with
  | sealIssue | sealForward _ =>
    rw [I.2]
    change sealOp (params d s)≠0
    unfold sealOp
    omega
  | sealBack _ =>
    rw [I.pc]
    change sealOp (params d s)≠0
    unfold sealOp
    omega
  | commitIssue =>
    rw [I.2]
    change commitOp (params d s)≠0
    unfold commitOp
    omega
  | commitForward _ =>
    rw [I.2.2]
    change commitOp (params d s)≠0
    unfold commitOp
    omega
  | done => exact (E rfl).elim

private theorem no_commit_old (d : Sheet) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (q : Stage) (I : On d (charter G r) x q)
    (Done : q≠.done) (e : Fin n)
    (Next : nextPhase (charter G r) q e≠.done) :
    let C := charter G r
    e=out C (C.a-1) → (readPC d C x).2≠commitOp (params d s) ∨
      (tok d C x (C.a-1)).tag≠2 := by
  dsimp only
  let C := charter G r
  have N : sealOp (params d s)≠commitOp (params d s) := by unfold sealOp commitOp; omega
  obtain ⟨P,K,_,_,_⟩ := canonical_centre G r
  change C.a<C.L at K
  have L : C.a-1<C.L := by omega
  intro Mark
  cases q with
  | sealIssue | sealForward _ => exact .inl (fun B=>N ((congrArg Prod.snd I.2).symm.trans B))
  | sealBack _ => exact .inl (fun B=>N ((congrArg Prod.snd I.pc).symm.trans B))
  | commitIssue => exact .inr (by rw [I.1.2.2 _ L]; decide)
  | commitForward i =>
    right
    apply off_front d C x i (C.a-1) I.2.1 L
    intro EI
    subst i
    have M : nomination C (.commitForward (C.a-1))=some e := congrArg some Mark.symm
    have A : C.a-1+1=C.a := by change 0<C.a at P; omega
    apply Next
    change nextPhase C (.commitForward (C.a-1)) e=.done
    rw [nextPhase,if_pos M]
    simp [paidPhase,A]
  | done => exact (Done rfl).elim

private theorem stable_selector (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (x : Raw s n) (e : Fin n)
    (M : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (S : StrongSerial d (charter G r) x)
    (No : let C := charter G r; e=out C (C.a-1) →
      (readPC d C x).2≠commitOp (params d s) ∨ (tok d C x (C.a-1)).tag≠2) :
    rawSelector d (rawNext s x e) (centre (charter G r))=rawSelector d x (centre (charter G r)) := by
  apply Classical.byContradiction
  intro Change
  let C := charter G r
  obtain ⟨_,P,_,_⟩ := changed_centre_owns_ingress d G r x e N M Change
  have E : out C (C.a-1)=e := congrArg Prod.fst P
  have A := switch_implies_commit d G r N x e M S Change
  have Old : oldCommitAt d x e := by
    apply Classical.byContradiction
    intro Bad
    exact Change (raw_selector_frame d x e _ N (fun Z=>Bad Z.2))
  have Ready := Old.2.1
  rw [M e] at Ready
  have Tag : (tok d C x (C.a-1)).tag=2 := by
    rw [predecessor_projection,E,(canonical_centre G r).2.2.2.2]
    exact ((rankReady_iff _ _ _ _).mp Ready).1
  exact (No E.symm).elim (fun X=>X A) (fun X=>X Tag)

private theorem wait_file (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (S : Serial d C x) (L : LegalWait d C x)
    (A : (tok d C x 0).tag≠3) :
    file d C (rawNext s x (door C))=file d C x :=
  (wait_file_before_first_consume d C N hh G F digit x X S L [door C]
    (.snoc (door C) .nil (.inr A))).2.2.2

private theorem front_root_no_reply (d : Sheet) (C : Chart h) (x : Raw s n)
    (i : Nat) (F : ForwardWait d C x i) : (tok d C x 0).tag≠3 := by
  rw [F.2.2 0 C.positive]
  unfold frontTag
  split <;> try decide
  split <;> decide

private theorem file_frame (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (S : StrongSerial d (charter G r) x)
    (q : Stage) (I : On d (charter G r) x q) (E : Enabled d G r x q)
    (e : Fin n) :
    file d (charter G r) (rawNext s x e)=file d (charter G r) x := by
  let C := charter G r
  let p := params d s
  have M := (cached_fibre d N hh Q F).mask x X
  by_cases D : e=door C
  · subst e
    have Go (op : Nat) (Choices : op=sealOp p ∨ op=commitOp p)
        (A : LegalIssue d C x) (PC : readPC d C x=(1,op))
        (Good : let c := comparisonFile p (selectBytes d (x C.root)); c/4≠3 ∧ c%4≠3) :
        file d C (rawNext s x (door C))=file d C x := by
      have H := ReportSealCommitLaunch.launch d C hh G F N x X A op Choices PC Good
      have P : 0<op := by rcases Choices with E|E <;> rw [E] <;> simp only [sealOp,commitOp] <;> omega
      apply healthy_issue_keeps_file d C N x M A
      · rw [PC]; exact P
      · rw [H.2.2.1]; exact Nat.ne_of_gt P
    cases q with
    | sealIssue => exact Go _ (.inl rfl) I.1 I.2 E
    | commitIssue => exact Go _ (.inr rfl) I.1 I.2 E
    | sealForward i => exact wait_file d C N hh G F digit x X S.1 I.1.1 (front_root_no_reply d C x i I.1)
    | commitForward i => exact wait_file d C N hh G F digit x X S.1 I.2.1.1 (front_root_no_reply d C x i I.2.1)
    | sealBack i =>
      cases i with
      | zero => exact seal_ack_keeps_entire_file d C N x M I
      | succ j =>
        apply wait_file d C N hh G F digit x X S.1 I.shape.1
        rw [I.shape.2.2 0 C.positive]
        simp [backTag]
    | done => exact E.elim
  · exact nondoor_file d C x e N M D

private theorem payload_step (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (seed x : Raw s n) (q : Stage) (H : Live d hh Q G r seed (x,q))
    (E : Enabled d G r x q) (e : Fin n)
    (Next : nextPhase (charter G r) q e≠.done) :
    PayloadOn d (charter G r) (rawNext s x e)
      (descriptor (params d s) (selectBytes d (seed (charter G r).root)))
      (nextPhase (charter G r) q e) := by
  let C := charter G r
  let p := params d s
  let delta := descriptor p (selectBytes d (seed C.root))
  let CF := cached_fibre d N hh Q F
  have X := H.cached
  have I := H.pose
  have P := H.data
  have M := CF.mask x X
  have ND : q≠.done := by intro B; subst q; exact E
  have Pos := old_pos I ND
  have NCommit := no_commit_old d G r x q I ND e Next
  have Keep (Z : e=centre C → (readPC d C x).2≠sealOp p ∨ (tok d C x C.a).tag≠2) :
      centreSeal d C (rawNext s x e)=centreSeal d C x :=
    (centre_frame_before_ingress d G r N x e M H.serial Pos Z NCommit).1
  obtain ⟨Ap,Bound,_,_,_⟩ := canonical_centre G r
  change C.a<C.L at Bound
  have Room := (ReportOwnerAcquireProvenance.centre_geometry C G).1
  have Desc : descriptor p (selectBytes d (x C.root))=delta :=
    descriptor_of_file_eq p _ _ H.original
  have notSeal : commitOp p≠sealOp p := by unfold commitOp sealOp; omega
  cases q with
  | sealIssue =>
    by_cases D : e=door C
    · subst e
      have Q0 : nomination C .sealIssue=some (door C) := rfl
      rw [nextPhase,if_pos Q0]
      change tok d C (rawNext s x (door C)) 0=sealToken p delta ∧ _
      have B := (ReportSealCommitLaunch.launch d C hh G F N x X I.1 (sealOp p) (.inl rfl) I.2 E).2.2.2.1
      rw [Desc] at B
      exact ⟨B,fun A=>(Nat.not_lt_zero _ A).elim⟩
    · have Q0 : nomination C .sealIssue≠some e := fun A=>D (Option.some.inj A).symm
      rw [nextPhase,if_neg Q0]
      trivial
  | sealForward i =>
    let t := sealToken p delta
    have R : ForwardWait d C x i := I.1
    have T : tok d C x i=t := P.1
    have State : Flight d C x i t :=
      ⟨R,T ▸ E.1,.inl T⟩
    have NoSeal (N0 : i≠C.a) :
        centreSeal d C (rawNext s x e)=centreSeal d C x :=
      Keep (fun _ => .inr (off_front d C x i C.a R Bound N0))
    by_cases D : e=out C i
    · subst e
      have Q0 : nomination C (.sealForward i)=some (out C i) := rfl
      rw [nextPhase,if_pos Q0]
      by_cases J : i+1<C.L
      · simp only [paidPhase,if_pos (show i+1<(charter G r).L from J)]
        have Guard : h (out C i)=true → C.route.port i=1 →
            reportOldGrant p (bytesL d x (out C i)) 1=true ∧
            publicationSelector p (bytesL d x (out C i))=t.payload/8 := by
          rw [←T]
          exact E.2.2
        have B := seal_step_success d C N hh G F x X i J R t T State.origin rfl Guard
        refine ⟨B.2.2.2.2,?_⟩
        intro Past
        by_cases V : i=C.a
        · subst i
          exact (seal_centre_step_installs d hh G r F N x X t R T State.origin rfl J H.hold H.selector).2.2
        · exact (NoSeal V).trans (P.2 (by change C.a<i+1 at Past; change C.a<i; omega))
      · simp only [paidPhase,if_neg (show ¬i+1<(charter G r).L from J)]
        have K := R.2.1
        have Past : C.a<i := by change i<(charter G r).L at K; change C.a<i; change (charter G r).a+1<(charter G r).L at Room; change ¬i+1<(charter G r).L at J; change (charter G r).a<i; omega
        exact (NoSeal (Nat.ne_of_gt Past)).trans (P.2 Past)
    · have Q0 : nomination C (.sealForward i)≠some e := fun A=>D (Option.some.inj A).symm
      rw [nextPhase,if_neg Q0]
      refine ⟨(late_forward_hold d C hh G F N x X i t State e D).trans T,?_⟩
      intro Past
      exact (NoSeal (Nat.ne_of_gt Past)).trans (P.2 Past)
  | sealBack i =>
    have R : SealD d C x i := I
    have B := (Keep (fun _=>.inr (rev_not_front d C x i C.a R.shape Bound))).trans P
    unfold nextPhase
    split
    · cases i <;> exact B
    · exact B
  | commitIssue =>
    have B := (Keep (fun _=>.inl (fun V=>notSeal ((congrArg Prod.snd I.2).symm.trans V)))).trans P
    by_cases D : e=door C
    · subst e
      have Q0 : nomination C .commitIssue=some (door C) := rfl
      rw [nextPhase,if_pos Q0]
      change tok d C (rawNext s x (door C)) 0=commitToken p delta ∧ _
      have J := (ReportSealCommitLaunch.launch d C hh G F N x X I.1 (commitOp p) (.inr rfl) I.2 E).2.2.2.1
      rw [Desc] at J
      exact ⟨J,B⟩
    · have Q0 : nomination C .commitIssue≠some e := fun A=>D (Option.some.inj A).symm
      rw [nextPhase,if_neg Q0]
      exact B
  | commitForward i =>
    let t := commitToken p delta
    have R : ForwardWait d C x i := I.2.1
    have T : tok d C x i=t := P.1
    have State : Flight d C x i t := ⟨R,T ▸ E.1,.inl T⟩
    have B := (Keep (fun _=>.inl (fun V=>notSeal ((congrArg Prod.snd I.2.2).symm.trans V)))).trans P.2
    by_cases D : e=out C i
    · subst e
      have Q0 : nomination C (.commitForward i)=some (out C i) := rfl
      have J : i+1<C.a := by
        by_cases K : i+1<C.a
        · exact K
        · apply False.elim (Next ?_)
          change nextPhase C (.commitForward i) (out C i)=.done
          rw [nextPhase,if_pos Q0]
          simp [paidPhase,K]
      rw [nextPhase,if_pos Q0]
      simp only [paidPhase,if_pos (show i+1<(charter G r).a from J)]
      have Before : BeforeCommitIngress C t.opcode p i := by
        apply ReportLateIngressSplit.no_prior_ingress
        intro _
        omega
      exact ⟨commit_hop_without_ingress d C N x M i (Nat.lt_trans J Bound) t T State.origin rfl Before,B⟩
    · have Q0 : nomination C (.commitForward i)≠some e := fun A=>D (Option.some.inj A).symm
      rw [nextPhase,if_neg Q0]
      exact ⟨(late_forward_hold d C hh G F N x X i t State e D).trans T,B⟩
  | done => exact E.elim

/-- Complete all-mark post-arithmetic phase invariant. On the one
terminal option, the actual old classifier fires at the target centre. -/
theorem live_next (d : Sheet) (N : 1<n) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (seed : Raw s n)
    (Good : let C := charter G r; let c := comparisonFile (params d s) (selectBytes d (seed C.root))
      c/4≠3 ∧ c%4≠3)
    (z : Raw s n × Stage) (H : Live d hh Q G r seed z) (e : Fin n) :
    let y := monitor d (charter G r) z e
    (Finished y ∧ classify d h z.1 e=some (target G r)) ∨ Live d hh Q G r seed y := by
  rcases z with ⟨x,q⟩
  dsimp only
  let C := charter G r
  let p := params d s
  let CF := cached_fibre d N hh Q F
  let y := rawNext s x e
  have En := enabled_of_live d N hh G r F seed Good x q H
  have V := next_value d N hh G r F digit x H.cached q H.pose En e
  by_cases D : nextPhase C q e=.done
  · obtain ⟨j,J,Eq⟩ := V.2.2.2 D
    have A : j=target G r := Subtype.ext J
    exact .inl ⟨D,A ▸ Eq⟩
  · have ND : q≠.done := by intro J; subst q; exact En
    have M := CF.mask x H.cached
    have NCommit := no_commit_old d G r x q H.pose ND e D
    have Cmp := raw_compatible_step d x e (centre C) (edge_sep N e) H.compat
    have Pos := old_pos H.pose ND
    obtain ⟨_,K,Head,Lane,_⟩ := canonical_centre G r
    have Held := held_incidence_step d C N x e M H.serial Pos C.a K Head H.compat
      (by rw [Lane]; exact H.hold)
    rw [Lane] at Held
    exact .inr ⟨CF.closed x e H.cached,strong_step d C N hh G F x H.cached H.serial digit e,V.1,
      (file_frame d N hh G r F digit x H.cached H.serial q H.pose En e).trans H.original,
      Cmp,Held,(stable_selector d G r N x e M H.serial NCommit).trans H.selector,
      payload_step d N hh G r F seed x q H En e D⟩

theorem live_seed (d : Sheet) (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h)
    (x : Raw s n) (X : Cached d hh Q x)
    (S : StrongSerial d (charter G r) x)
    (I : On d (charter G r) x .sealIssue)
    (Compat : Compatible (rawGrant d x (centre (charter G r))))
    (Held : rawGrant d x (centre (charter G r)) 1=true)
    (Sel : rawSelector d x (centre (charter G r))=
      descriptor (params d s) (selectBytes d (x (charter G r).root))/8) :
    Live d hh Q G r x (x,.sealIssue) :=
  ⟨X,S,I,rfl,Compat,Held,Sel,trivial⟩

#print axioms payload_step
#print axioms live_next
#print axioms live_seed
#print axioms enabled_of_live
end L4.ReportLateEnabledInvariant
