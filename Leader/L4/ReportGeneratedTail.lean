import Leader.L4.ReportSealDescriptorTransport
import Leader.L4.ReportGuardedTailFrameTape
import Leader.L4.ReportFastRawEvent

namespace L4.ReportGeneratedTail
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerForwardControl ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerReverseShape
open ReportByteRows ReportRawProjection ReportWriteSplit ReportSealCommitOrigin
open ReportCommitAppliedIngress ReportLeaseOwner ReportIngressOwnership
open ReportCentreSealOwner ReportGenerationAncestry ReportOwnerCommandRail
open ReportGuardedTailSuccess ReportGuardedTailFrameTape ReportFastRawEvent ReportLeaseGrants
open ReportOwnerAcquireReturn ReportSealDescriptor ReportSealDescriptorTransport
open ReportOwnerAcquireProvenance (BeforeConsume)
open ReportSealReverse (SealD healthy_seal_terminal seal_reverse_run)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem commit_hop_without_ingress (d : Sheet) (C : Chart h) (N : 1<n)
    (x : Raw s n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (k : Nat) (J : k+1<C.L) (t : Tok)
    (T : tok d C x k=t) (H : SealCommitForward (params d s) t)
    (O : t.opcode=commitOp (params d s))
    (Before : BeforeCommitIngress C t.opcode (params d s) k) :
    tok d C (rawNext s x (out C k)) (k+1)=t := by
  let p := params d s
  let e := out C k
  let u := bytesL d x e
  let v := bytesR d x e
  let j := C.route.port k
  let l := C.route.port (k+1)
  have P : publicationToken p (h e) u j=t := by rwa [predecessor_projection] at T
  have W := raw_pair_wire d C x N mask k
  rw [tok_wire,W.2,workR]
  have A := (seal_commit_hop_pair p (h e) (h (rightNeighbor e)) u v j l
    (internal_dest C k J) (P.symm ▸ H) (chartGate d C (rawNext s x e) (k+1))).2.2
  rw [P] at A
  rw [A]
  rw [commit_effect_token p _ _ u v j l _ t O H.2.2.2.2.2.2.1,if_neg (Before O)]

/-- Generated positive COMMIT never faults before its guarded ingress.
The tape is the physical serial prefix, not a second sampled flight. -/
theorem commit_healthy_before_ingress (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok)
    (A : Flight d C x 0 t) (T : tok d C x 0=t)
    (O : t.opcode=commitOp (params d s))
    (w : List (Fin n)) (k : Nat) (B : BeforeLateIngress d C (s:=s) t.opcode w k) :
    tok d C (rawRun x w) k=t := by
  let CF := cached_fibre d N hh Q F
  induction B with
  | nil => exact T
  | @hold u j e B NE IH =>
    obtain ⟨Y,V,_⟩ := late_origin_run d C hh G F N x X t A u j B
    rw [ShortOwnerEpochJS.raw_snoc]
    exact (late_forward_hold d C hh G F N _ Y j t V e NE).trans IH
  | @hop u j B J No IH =>
    obtain ⟨Y,_,_⟩ := late_origin_run d C hh G F N x X t A u j B
    rw [ShortOwnerEpochJS.raw_snoc]
    exact commit_hop_without_ingress d C N _ (CF.mask _ Y) j J t IH A.origin O No

private theorem no_restart_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (A : NoRestartTape d C x w)
    (B : (readPC d C (rawNext s (rawRun x w) e)).2≠0) :
    NoRestartTape d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨B,trivial⟩
  | cons a w IH => exact ⟨A.1,IH _ A.2 B⟩

theorem commit_prefix_no_restart (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok)
    (A : Flight d C x 0 t) (Pos : (readPC d C x).2≠0)
    (w : List (Fin n)) (k : Nat) (B : BeforeLateIngress d C (s:=s) t.opcode w k) :
    NoRestartTape d C x w := by
  have positive (v : List (Fin n)) (j : Nat)
      (B : BeforeLateIngress d C (s:=s) t.opcode v j) :
      (readPC d C (rawRun x v)).2≠0 :=
    fun H=>Pos ((congrArg Prod.snd (late_origin_run d C hh G F N x X t A v j B).2.2).symm.trans H)
  induction B with
  | nil => trivial
  | @hold u j e B NE IH =>
    apply no_restart_snoc d C x u e IH
    rw [←ShortOwnerEpochJS.raw_snoc]
    exact positive _ j (.hold e B NE)
  | @hop u j B J No IH =>
    apply no_restart_snoc d C x u (out C j) IH
    rw [←ShortOwnerEpochJS.raw_snoc]
    exact positive _ (j+1) (.hop B J No)


/-- Once the same descriptor is installed at centre, the actual
generated pre-ingress COMMIT prefix yields a classified trigger at the
very next nominated ingress. Grant and selector are framed over the
entire unfiltered original prefix. -/
theorem commit_prefix_classifies (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (Serial : StrongSerial d (charter G r) x)
    (desc : Nat)
    (Packet : tok d (charter G r) x 0=({tag:=2,opcode:=commitOp (params d s),payload:=desc}:Tok))
    (H : SealCommitForward (params d s) ({tag:=2,opcode:=commitOp (params d s),payload:=desc}:Tok))
    (Fw : ForwardWait d (charter G r) x 0)
    (PC : readPC d (charter G r) x=(2,commitOp (params d s)))
    (Compat : ReportLeaseGrants.Compatible (rawGrant d x (centre (charter G r))))
    (Held : rawGrant d x (centre (charter G r)) 1=true)
    (Prior : rawSelector d x (centre (charter G r))=desc/8)
    (Installed : centreSeal d (charter G r) x=some desc)
    (w : List (Fin n))
    (B : BeforeLateIngress d (charter G r) (s:=s) (commitOp (params d s)) w ((charter G r).a-1)) :
    let C := charter G r
    let z := rawRun x w
    ∃ j : Owner h, j.val=centre C ∧
      classify d h z (out C (C.a-1))=some j := by
  dsimp only
  let C := charter G r
  let p := params d s
  let t : Tok := {tag:=2,opcode:=commitOp p,payload:=desc}
  let z := rawRun x w
  let k := C.a-1
  let e := out C k
  let CF := cached_fibre d N hh Q F
  have A : Flight d C x 0 t := ⟨Fw,H,.inl Packet⟩
  have Pos : (readPC d C x).2≠0 := by rw [PC]; change commitOp p≠0; unfold commitOp; omega
  have NR := commit_prefix_no_restart d C N hh G F x X t A Pos w k B
  have WF := commit_prefix_writerfree d N G r hh F x X t A PC rfl w k B
  obtain ⟨Hold,Seal,Sel⟩ :=
    centre_held_framed_run d G r N hh F digit x X Serial Compat Held Pos w NR WF
  have Y := (late_origin_run d C hh G F N x X t A w k B).1
  have M := CF.mask z Y
  obtain ⟨Cp,_,Head,_,Lane⟩ := canonical_centre G r
  have Right : rightNeighbor e=centre C := by
    have K : k+1=C.a := by
      change 0<C.a at Cp
      dsimp [k]
      omega
    change rightNeighbor (out C k)=centre C
    rw [chart_succ,K]
    rfl
  let j : Owner h := ⟨centre C,Head⟩
  refine ⟨j,rfl,(classify_iff d h z e j).mpr ⟨Right,?_,?_⟩⟩
  · rw [M,Right]
    exact Head
  · have T := commit_healthy_before_ingress d C N hh G F x X t A Packet rfl w k B
    rw [predecessor_projection,Lane] at T
    rw [M e,Right]
    change CommitGuard p (h e) (selectBytes d (z e)) (selectBytes d (z (centre C)))
      (oldReportToken p (h e) (selectBytes d (z e)) 0).payload
    have Old : oldReportToken p (h e) (selectBytes d (z e)) 0=t := T
    rw [Old]
    exact ⟨Old,Hold,Sel.trans Prior,Seal.trans Installed⟩


private theorem seal_not_commit (p : Params) : sealOp p≠commitOp p := by
  unfold sealOp commitOp
  omega

private theorem off_front (d : Sheet) (C : Chart h) (x : Raw s n) (k i : Nat)
    (F : ForwardWait d C x k) (I : i<C.L) (E : k≠i) :
    (tok d C x i).tag≠2 := by
  rw [F.2.2 i I]
  unfold frontTag
  split
  · decide
  · rw [if_neg E.symm]
    decide

private theorem seal_lease_step (d : Sheet) (N : 1<n) (G : GapInput h)
    (r : Owner h) (x : Raw s n) (e : Fin n)
    (M : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (S : StrongSerial d (charter G r) x)
    (PC : (readPC d (charter G r) x).2=sealOp (params d s))
    (Comp : Compatible (rawGrant d x (centre (charter G r))))
    (Hold : rawGrant d x (centre (charter G r)) 1=true) :
    let C := charter G r
    let z := rawNext s x e
    Compatible (rawGrant d z (centre C)) ∧ rawGrant d z (centre C) 1=true ∧
      rawSelector d z (centre C)=rawSelector d x (centre C) := by
  dsimp only
  let C := charter G r
  obtain ⟨_,K,Head,Lane,_⟩ := canonical_centre G r
  have Pos : (readPC d C x).2≠0 := by rw [PC]; unfold sealOp; omega
  have A := held_incidence_step d C N x e M S Pos C.a K Head Comp
    (by rw [Lane]; exact Hold)
  rw [Lane] at A
  refine ⟨raw_compatible_step d x e (centre C) (edge_sep N e) Comp,A,?_⟩
  apply Classical.byContradiction
  intro Change
  have Op := switch_implies_commit d G r N x e M S Change
  exact seal_not_commit _ (PC.symm.trans Op)

/-- Every generated outward SEAL is healthy. The unique guarded hop
is the target's centre, where the held lease and prior selector
authorize the literal descriptor installation. -/
theorem generated_seal_forward (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (Serial : StrongSerial d (charter G r) x)
    (t : Tok)
    (Packet : tok d (charter G r) x 0=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=sealOp (params d s))
    (Fw : ForwardWait d (charter G r) x 0)
    (PC : readPC d (charter G r) x=(2,sealOp (params d s)))
    (Compat : Compatible (rawGrant d x (centre (charter G r))))
    (Held : rawGrant d x (centre (charter G r)) 1=true)
    (Prior : rawSelector d x (centre (charter G r))=t.payload/8)
    (w : List (Fin n)) (k : Nat)
    (B : BeforeLateIngress d (charter G r) (s:=s) t.opcode w k) :
    let C := charter G r
    let z := rawRun x w
    Cached d hh Q z ∧ ForwardWait d C z k ∧ readPC d C z=(2,sealOp (params d s)) ∧
      tok d C z k=t ∧ Compatible (rawGrant d z (centre C)) ∧
      rawGrant d z (centre C) 1=true ∧ rawSelector d z (centre C)=t.payload/8 ∧
      (C.a<k → centreSeal d C z=some t.payload) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let CF := cached_fibre d N hh Q F
  have R0 : Flight d C x 0 t := ⟨Fw,H,.inl Packet⟩
  have Geometry := ReportOwnerAcquireProvenance.centre_geometry C G
  have Bound : C.a<C.L := by have := Geometry.1; omega
  have no_commit (z : Raw s n) (P : readPC d C z=(2,sealOp p)) :
      (readPC d C z).2≠commitOp p := fun E=>seal_not_commit p ((congrArg Prod.snd P).symm.trans E)
  have pos (z : Raw s n) (P : readPC d C z=(2,sealOp p)) :
      (readPC d C z).2≠0 := by rw [P]; change sealOp p≠0; unfold sealOp; omega
  have strong (u : List (Fin n)) : StrongSerial d C (rawRun x u) :=
    (strong_run d C N hh G F digit x X Serial u).2.1
  induction B with
  | nil => exact ⟨X,Fw,PC,Packet,Compat,Held,Prior,fun K => (Nat.not_lt_zero _ K).elim⟩
  | @hold u k e B NE IH =>
    obtain ⟨Y,A,P,T,Comp,Hold,Sel,Set⟩ := IH
    let z := rawRun x u
    have V := (late_origin_run d C hh G F N x X t R0 (u++[e]) k (.hold e B NE)).2.1.shape
    rw [ShortOwnerEpochJS.raw_snoc] at V ⊢
    have M := CF.mask z Y
    have ⟨Comp',Hold',Sel'⟩ := seal_lease_step d N G r z e M (strong u)
      (congrArg Prod.snd P) Comp Hold
    refine ⟨CF.closed z e Y,V,(forward_step_control d C N hh F z Y k A e).trans P,
      (late_forward_hold d C hh G F N z Y k t ⟨A,H,.inl T⟩ e NE).trans T,
      Comp',Hold',Sel'.trans Sel,?_⟩
    intro Past
    have Q0 := centre_frame_before_ingress d G r N z e M (strong u) (pos z P)
      (fun _=>.inr (off_front d C z k C.a A Bound (Nat.ne_of_gt Past)))
      (fun _=>.inl (no_commit z P))
    exact Q0.1.trans (Set Past)
  | @hop u k B J No IH =>
    obtain ⟨Y,A,P,T,Comp,Hold,Sel,Set⟩ := IH
    let z := rawRun x u
    let e := out C k
    have M := CF.mask z Y
    have Guard (Header : h e=true) (Lane : C.route.port k=1) :
        reportOldGrant p (bytesL d z e) 1=true ∧ publicationSelector p (bytesL d z e)=t.payload/8 := by
      have E := (Geometry.2 k A.2.1).mp ⟨Header,Lane⟩
      subst k
      exact ⟨Hold,Sel⟩
    have V := seal_step_success d C N hh G F z Y k J A t T H O Guard
    have ⟨Comp',Hold',Sel'⟩ := seal_lease_step d N G r z e M (strong u)
      (congrArg Prod.snd P) Comp Hold
    rw [ShortOwnerEpochJS.raw_snoc]
    refine ⟨V.1,V.2.1,V.2.2.1.trans P,V.2.2.2.2,Comp',Hold',Sel'.trans Sel,?_⟩
    intro Past
    by_cases K : k=C.a
    · subst k
      exact (seal_centre_step_installs d hh G r F N z Y t A T H O J Hold Sel).2.2
    · have Q0 := centre_frame_before_ingress d G r N z e M (strong u) (pos z P)
        (fun _=>.inr (off_front d C z k C.a A Bound K))
        (fun _=>.inl (no_commit z P))
      exact Q0.1.trans (Set (by change C.a<k+1 at Past; change C.a<k; omega))


private theorem seal_reverse_positive (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (D : SealD d C x k)
    (w : List (Fin n)) (T : BeforeConsume d C x w) : NoRestartTape d C x w := by
  induction T with
  | nil => trivial
  | @snoc u e T NC IH =>
    have W := seal_reverse_run d C hh G F N x X k D digit (u++[e]) (.snoc e T NC)
    apply no_restart_snoc d C x u e IH
    rw [←ShortOwnerEpochJS.raw_snoc]
    obtain ⟨_,j,_,A⟩ := W
    rw [A.pc]
    change sealOp (params d s)≠0
    unfold sealOp
    omega

/-- On the original terminal mark and reverse word, the healthy ACK
reaches the real root with the installed descriptor, held centre
grant and old selector all intact. -/
theorem generated_seal_root (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (Serial : StrongSerial d (charter G r) x)
    (k : Nat) (K : k+1=(charter G r).L)
    (A : ForwardWait d (charter G r) x k)
    (PC : readPC d (charter G r) x=(2,sealOp (params d s)))
    (t : Tok) (Packet : tok d (charter G r) x k=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=sealOp (params d s))
    (Compat : Compatible (rawGrant d x (centre (charter G r))))
    (Held : rawGrant d x (centre (charter G r)) 1=true)
    (Prior : rawSelector d x (centre (charter G r))=t.payload/8)
    (Installed : centreSeal d (charter G r) x=some t.payload)
    (w : List (Fin n))
    (B : BeforeConsume d (charter G r) (rawNext s x (out (charter G r) k)) w)
    (Arrived : (tok d (charter G r) (rawRun (rawNext s x (out (charter G r) k)) w) 0).tag=3) :
    let C := charter G r
    let z := rawRun (rawNext s x (out C k)) w
    Cached d hh Q z ∧ SealD d C z 0 ∧
      rawGrant d z (centre C) 1=true ∧ rawSelector d z (centre C)=t.payload/8 ∧
      centreSeal d C z=some t.payload := by
  dsimp only
  let C := charter G r
  let p := params d s
  let e := out C k
  let y := rawNext s x e
  let z := rawRun y w
  let CF := cached_fibre d N hh Q F
  have M := CF.mask x X
  have Bound := (ReportOwnerAcquireProvenance.centre_geometry C G).1
  have Past : C.a<k := by change k+1=C.L at K; omega
  have Pos : (readPC d C x).2≠0 := by rw [PC]; change sealOp p≠0; unfold sealOp; omega
  obtain ⟨Y,D⟩ := healthy_seal_terminal d C N hh G F x X k K A PC
    (Packet.symm ▸ H) (Packet.symm ▸ O)
  have P := postcentre_seal_front_writerfree d G r x k Past A (congrArg Prod.snd PC) e
  have Fr := centre_frame_before_ingress d G r N x e M Serial Pos P.1 P.2.1
  have ⟨Comp,Hold,Sel⟩ := seal_lease_step d N G r x e M Serial
    (congrArg Prod.snd PC) Compat Held
  have S' := strong_step d C N hh G F x X Serial digit e
  have NR := seal_reverse_positive d C N hh G F digit y Y k D w B
  have Pos' : (readPC d C y).2≠0 := by rw [D.pc]; change sealOp p≠0; unfold sealOp; omega
  have WF := seal_reverse_writerfree d N G r hh F digit y Y k D w B
  have ⟨Hold',Seal',Sel'⟩ :=
    centre_held_framed_run d G r N hh F digit y Y S' Comp Hold Pos' w NR WF
  obtain ⟨Z,j,_,R⟩ := seal_reverse_run d C hh G F N y Y k D digit w B
  have Eq : j=0 := by
    by_cases J : j=0
    · exact J
    · have T := R.shape.2.2 0 C.positive
      change (tok d C z 0).tag=backTag j 0 at T
      rw [Arrived] at T
      simp [backTag,show 0<j by omega] at T
  exact ⟨Z,Eq ▸ R,Hold',Sel'.trans (Sel.trans Prior),Seal'.trans (Fr.1.trans Installed)⟩


private theorem issue_nondoor_writerfree (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d (charter G r) x)
    (Pos : (readPC d (charter G r) x).2≠0) (w : List (Fin n))
    (E : ∀ e∈w,e≠door (charter G r)) :
    CentreWriterFree d (charter G r) x w ∧ NoRestartTape d (charter G r) x w := by
  let C := charter G r
  let CF := cached_fibre d N hh Q F
  have ⟨_,K,_,_,_⟩ := canonical_centre G r
  change C.a<C.L at K
  have K' : C.a-1<C.L := by omega
  induction w generalizing x with
  | nil => exact ⟨trivial,trivial⟩
  | cons e w IH =>
    let z := rawNext s x e
    have H := E e List.mem_cons_self
    have Z := CF.closed x e X
    obtain ⟨A,F0⟩ := nondoor_preserves d C hh G F N x X I e H
    have NZ : (readPC d C z).2≠0 := fun B=>Pos ((congrArg Prod.snd F0).symm.trans B)
    obtain ⟨B,R⟩ := IH z Z A NZ (fun e M=>E e (List.mem_cons_of_mem _ M))
    refine ⟨⟨fun _=>.inr ?_,fun _=>.inr ?_,B⟩,NZ,R⟩
    · rw [I.2.2 C.a K]
      decide
    · rw [I.2.2 (C.a-1) K']
      decide

/-- Post-SEAL root to classified COMMIT on the same raw tape.
The initial descriptor is read only at ISSUE(SEAL); no free later
comparison, selector or payload equality is introduced. -/
theorem seal_root_to_classified_ingress (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (S : StrongSerial d (charter G r) x)
    (I : LegalIssue d (charter G r) x)
    (PC : readPC d (charter G r) x=(1,sealOp (params d s)))
    (Good : let C := charter G r
      comparisonFile (params d s) (selectBytes d (x C.root))/4≠3 ∧
      comparisonFile (params d s) (selectBytes d (x C.root))%4≠3)
    (before : List (Fin n))
    (B : let C := charter G r; BeforeConsume d C (rawNext s x (door C)) before)
    (Ready : let C := charter G r; SealD d C (rawRun (rawNext s x (door C)) before) 0)
    (Initial : let C := charter G r; let z := rawRun (rawNext s x (door C)) before
      Compatible (rawGrant d z (centre C)) ∧ rawGrant d z (centre C) 1=true ∧
        rawSelector d z (centre C)=descriptor (params d s) (selectBytes d (x C.root))/8 ∧
        centreSeal d C z=some (descriptor (params d s) (selectBytes d (x C.root))))
    (between : List (Fin n)) (NoDoor : ∀ e∈between,e≠door (charter G r))
    (w : List (Fin n))
    (W : let C := charter G r
      BeforeLateIngress d C (s:=s) (commitOp (params d s)) w (C.a-1)) :
    let C := charter G r
    let old := rawRun (rawNext s x (door C)) before
    let launch := rawNext s (rawRun (rawNext s old (door C)) between) (door C)
    let z := rawRun launch w
    ∃ j : Owner h, j.val=centre C ∧ classify d h z (out C (C.a-1))=some j := by
  dsimp only
  let C := charter G r
  let p := params d s
  let old := rawRun (rawNext s x (door C)) before
  let after := rawNext s old (door C)
  let issue := rawRun after between
  let launch := rawNext s issue (door C)
  let desc := descriptor p (selectBytes d (x C.root))
  let CF := cached_fibre d N hh Q F
  obtain ⟨X',Legal,IssuePC,_,Packet,Fw,LaunchPC⟩ :=
    seal_to_commit_source d C N hh G F digit x X I PC Good before B Ready between NoDoor
  have X0 := CF.closed x (door C) X
  have S0 := strong_step d C N hh G F x X S digit (door C)
  obtain ⟨Y,So,_⟩ := strong_run d C N hh G F digit _ X0 S0 before
  obtain ⟨Za,Ea,PCa⟩ := ReportSealReverse.seal_root_consume d C hh G F N old Y Ready digit
  have Sa := strong_step d C N hh G F old Y So digit (door C)
  have Si := (strong_run d C N hh G F digit after Za Sa between).2.1
  have Sl := strong_step d C N hh G F issue X' Si digit (door C)
  have Pos (z : Raw s n) (A : (readPC d C z).2=commitOp p) : (readPC d C z).2≠0 := by
    rw [A]
    unfold commitOp
    omega
  have Po := Ready.pc
  have ⟨Co,Ho,So'⟩ := seal_lease_step d N G r old (door C) (CF.mask _ Y) So
    (congrArg Prod.snd Po) Initial.1 Initial.2.1
  have Po' : (readPC d C old).2≠0 := by rw [Po]; change sealOp p≠0; unfold sealOp; omega
  have F0 := door_writerfree d G r old
  have Er := (centre_frame_before_ingress d G r N old (door C) (CF.mask _ Y) So Po' F0.1 F0.2.1).1
  have Leg : LegalIssue d C after := by
    refine ⟨?_,Ea⟩
    rw [PCa]
    exact Nat.le_refl _
  have N0 := Pos after (congrArg Prod.snd PCa)
  obtain ⟨WF,NR⟩ := issue_nondoor_writerfree d N hh G r F after Za Leg N0 between NoDoor
  have ⟨Hi,Seal,Sel⟩ := centre_held_framed_run d G r N hh F digit after Za Sa Co Ho N0 between NR WF
  have Ci : Compatible (rawGrant d issue (centre C)) := by
    have run (z : Raw s n) (u : List (Fin n)) (K : Compatible (rawGrant d z (centre C))) :
        Compatible (rawGrant d (rawRun z u) (centre C)) := by
      induction u generalizing z with
      | nil => exact K
      | cons e u IH =>
        exact IH _ (raw_compatible_step d z e (centre C) (edge_sep N e) K)
    exact run after between Co
  have LPos := Pos issue (congrArg Prod.snd IssuePC)
  have LN := Pos launch (congrArg Prod.snd LaunchPC)
  have F1 := door_writerfree d G r issue
  obtain ⟨Hl,St,Sc⟩ := centre_held_framed_run d G r N hh F digit issue X' Si Ci Hi LPos
    [door C] (show NoRestartTape d C issue [door C] from ⟨LN,trivial⟩) F1
  have Cl := raw_compatible_step d issue (door C) (centre C) (edge_sep N (door C)) Ci
  exact commit_prefix_classifies d N hh G r F digit launch (CF.closed issue (door C) X') Sl desc
    Packet (ReportSealCommitLaunch.descriptor_forward p _ (commitOp p) (.inr rfl))
    Fw LaunchPC Cl Hl (Sc.trans (Sel.trans (So'.trans Initial.2.2.1)))
    (St.trans (Seal.trans (Er.trans Initial.2.2.2))) w W

#print axioms seal_root_to_classified_ingress
#print axioms generated_seal_root
#print axioms generated_seal_forward
#print axioms commit_prefix_classifies
#print axioms commit_hop_without_ingress
#print axioms commit_healthy_before_ingress
#print axioms commit_prefix_no_restart
end L4.ReportGeneratedTail
