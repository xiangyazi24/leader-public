import Leader.L4.ReportCommitAppliedIngress
import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportFirstCutGrant
import Leader.L4.ReportCentreSealOwner

namespace L4.ReportGuardedTailSuccess
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerForwardLocations
open ReportOwnerForwardControl ReportOwnerIssueControl ReportOwnerReverseControl
open ReportByteRows ReportRawProjection ReportWriteSplit ReportSealCommitOrigin
open ReportCommitAppliedIngress ReportLeaseOwner ReportIngressOwnership
open ReportCentreSealOwner ReportJoinedSealFrame
open ReportGenerationAncestry ReportOwnerCommandRail ReportOwnerAcquireReturn ReportLeaseGrants

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem seal_step_success (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (J : k+1<C.L)
    (R : ForwardWait d C x k) (t : Tok) (T : tok d C x k=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=sealOp (params d s))
    (Accept : h (out C k)=true → C.route.port k=1 →
      reportOldGrant (params d s) (bytesL d x (out C k)) 1=true ∧
      publicationSelector (params d s) (bytesL d x (out C k))=t.payload/8) :
    let y := rawNext s x (out C k)
    Cached d hh Q y ∧ ForwardWait d C y (k+1) ∧ readPC d C y=readPC d C x ∧
      tok d C y k=MISByteCodec.T ∧ tok d C y (k+1)=t := by
  dsimp only
  let p := params d s
  let e := out C k
  let y := rawNext s x e
  let u := bytesL d x e
  let v := bytesR d x e
  let CF := cached_fibre d N hh Q F
  have P : publicationToken p (h e) u (C.route.port k)=t := by
    rwa [predecessor_projection] at T
  have W := raw_pair_wire d C x N (CF.mask x X) k
  have E := seal_commit_hop_pair p (h e) (h (rightNeighbor e)) u v
    (C.route.port k) (C.route.port (k+1)) (internal_dest C k J)
    (P.symm ▸ H) (chartGate d C y (k+1))
  dsimp only at E
  have In (win : Bool) : (effect p u v (h e) (h (rightNeighbor e)) (C.route.port k)
      (some (C.route.port (k+1))) win (publicationToken p (h e) u (C.route.port k))).2.2=t := by
    rw [P,seal_effect_token p _ _ u v _ _ _ t O H.2.2.2.2.2.2.1,if_neg]
    rintro ⟨B,L,C0⟩
    exact C0 (Accept B L)
  have Trail : tok d C y k=MISByteCodec.T := by
    change tok d C (rawNext s x (out C k)) k=_
    rw [tok_wire,W.1,workL,E.1]
    exact drain_decode_T p _
  have Pkt : tok d C y (k+1)=t := by
    change tok d C (rawNext s x (out C k)) (k+1)=_
    rw [tok_wire,W.2,workR,E.2.2]
    exact In _
  have PC := forward_step_control d C N hh F x X k R e
  refine ⟨CF.closed x e X,?_,PC,Trail,Pkt⟩
  rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k R e with A|⟨_,A|⟨E0,_⟩⟩
  · have B := A.2.2 k R.2.1
    change (tok d C y k).tag=frontTag k k at B
    rw [Trail] at B
    simp [MISByteCodec.T,frontTag] at B
  · exact A
  · omega

theorem commit_guard_of_matching_seal (p : Params) (v : BitVec p.w) (t : Tok)
    (U : t.applied=false) (G : reportOldGrant p v 1=true)
    (P : publicationSelector p v=t.payload/8)
    (W : reportOldSeal p v=some t.payload) :
    packetCommitGuard p v t=true := by
  change (!t.applied && reportOldGrant p v 1 &&
    publicationSelector p v==t.payload/8 && reportOldSeal p v==some t.payload)=true
  simp [U,G,P,W]

theorem commit_step_from_matching_seal (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (t : Tok)
    (R : ForwardWait d (charter G r) x ((charter G r).a-1))
    (T : tok d (charter G r) x ((charter G r).a-1)=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=commitOp (params d s))
    (U : t.applied=false)
    (Held : reportOldGrant (params d s) (selectBytes d (x (centre (charter G r)))) 1=true)
    (Sel : publicationSelector (params d s) (selectBytes d (x (centre (charter G r))))=t.payload/8)
    (W : centreSeal d (charter G r) x=some t.payload) :
    let C := charter G r
    let y := rawNext s x (out C (C.a-1))
    Cached d hh Q y ∧ ForwardWait d C y C.a ∧ readPC d C y=readPC d C x ∧
      tok d C y (C.a-1)=MISByteCodec.T ∧ tok d C y C.a={t with applied:=true} := by
  let C := charter G r
  have ingress : rightNeighbor (out C (C.a-1))=centre C := by
    have A : 0<C.a := (canonical_centre G r).1
    rw [chart_succ,show C.a-1+1=C.a by omega]
    rfl
  apply applied_ingress d hh G r F N x X t R T H O
  change packetCommitGuard (params d s) (selectBytes d (x (rightNeighbor (out C (C.a-1))))) t=true
  rw [ingress]
  exact commit_guard_of_matching_seal _ _ _ U Held Sel W

theorem seal_centre_step_installs (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (r : Owner h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x)
    (t : Tok) (R : ForwardWait d (charter G r) x (charter G r).a)
    (T : tok d (charter G r) x (charter G r).a=t)
    (H : SealCommitForward (params d s) t) (O : t.opcode=sealOp (params d s))
    (room : (charter G r).a+1<(charter G r).L)
    (Held : reportOldGrant (params d s) (selectBytes d (x (centre (charter G r)))) 1=true)
    (Sel : publicationSelector (params d s) (selectBytes d (x (centre (charter G r))))=t.payload/8) :
    let C := charter G r
    let y := rawNext s x (centre C)
    ForwardWait d C y (C.a+1) ∧ tok d C y (C.a+1)=t ∧
      centreSeal d C y=some t.payload := by
  dsimp only
  let C := charter G r
  let p := params d s
  let u := selectBytes d (x (centre C))
  let CF := cached_fibre d N hh Q F
  obtain ⟨_,_,Hd,Lane,_⟩ := canonical_centre G r
  have P : publicationToken p true u 1=t := by
    rw [predecessor_projection,Hd,Lane] at T
    exact T
  have Ready : rankReady p true u 1=true := by
    rw [rankReady_iff,P]
    refine ⟨H.1,?_⟩
    intro Bad
    have E := Bad.1.2.2
    change t.opcode=admitOp p at E
    change t.opcode=sealOp p at O
    rw [O] at E
    unfold sealOp admitOp at E
    omega
  have Guard : reportHeaderSetSeal p u :=
    ⟨Ready,(congrArg MISByteCodec.Token.fault P).trans H.2.2.2.2.2.2.1,
      (congrArg MISByteCodec.Token.opcode P).trans O,Held,
      Sel.trans (congrArg (fun a : Tok => a.payload/8) P).symm⟩
  have Seal := (raw_header_left_seal_step d x (centre C) N (CF.mask x X) Hd).2.1 Guard
  have Hop := seal_step_success d C N hh G F x X C.a room R t T H O
    (fun _ _ => ⟨Held,Sel⟩)
  exact ⟨Hop.2.1,Hop.2.2.2.2,Seal.trans (congrArg (fun a : Tok => some a.payload) P)⟩

/-- Old cursor exclusions block the only local writers. This frame
applies even at COMMIT opcode, before this flight's centre ingress. -/
theorem centre_frame_before_ingress (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (x : Raw s n) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (S : StrongSerial d (charter G r) x)
    (Pos : (readPC d (charter G r) x).2≠0)
    (NoSeal : let C := charter G r
       e=centre C → (readPC d C x).2≠sealOp (params d s) ∨
        (tok d C x C.a).tag≠2)
    (NoCommit : let C := charter G r
       e=out C (C.a-1) → (readPC d C x).2≠commitOp (params d s) ∨
        (tok d C x (C.a-1)).tag≠2) :
    let C := charter G r
    centreSeal d C (rawNext s x e)=centreSeal d C x ∧
      rawSelector d (rawNext s x e) (centre C)=rawSelector d x (centre C) := by
  dsimp only at NoSeal NoCommit ⊢
  let C := charter G r
  let p := params d s
  have E0 : ∀ a, rightNeighbor a=centre C → e=a → out C (C.a-1)=e := by
    intro a A Ea
    exact (congrArg Prod.fst (ingress_cell G r a A).2).trans Ea.symm
  have NoHit (J : e=out C (C.a-1)) (A : (readPC d C x).2=commitOp p)
      (T : (tok d C x (C.a-1)).tag=2) : False :=
    (NoCommit J).elim (fun h0=>h0 A) (fun h0=>h0 T)
  constructor
  · rcases centre_seal_marks d G r N x e mask S with A|A|A|A
    · exact (Pos A.2.2.1).elim
    · have F0 := (NoSeal A.1)
      rcases F0 with F0|F0
      · exact (F0 A.2.2.1).elim
      · obtain ⟨_,_,Head,Lane,_⟩ := canonical_centre G r
        have T : (tok d C x C.a).tag=2 := by
          rw [predecessor_projection,Head,Lane]
          exact ((rankReady_iff p true (bytesL d x (out C C.a)) 1).mp A.2.1.1).1
        exact (F0 T).elim
    · have E : out C (C.a-1)=e := E0 e A.1 rfl
      have T : (tok d C x (C.a-1)).tag=2 := by
        rw [predecessor_projection,E,(canonical_centre G r).2.2.2.2]
        exact ((rankReady_iff p (h e) (bytesL d x e) 0).mp A.2.1.2.1).1
      exact (NoHit E.symm A.2.2.1 T).elim
    · exact A.2
  · apply Classical.byContradiction
    intro Change
    have ⟨K,F0,H,OP⟩ := changed_centre_owns_ingress d G r x e N mask Change
    have E : out C (C.a-1)=e := congrArg Prod.fst F0
    -- The public accepted-ingress token is an old ready F.
    have Old : oldCommitAt d x e := by
      apply Classical.byContradiction
      intro Nope
      apply Change
      exact raw_selector_frame d x e _ N (fun Z=>Nope Z.2)
    have Good := Old.2.1
    rw [mask e] at Good
    have T : (tok d C x (C.a-1)).tag=2 := by
      rw [predecessor_projection,E,(canonical_centre G r).2.2.2.2]
      exact ((rankReady_iff p (h e) (bytesL d x e) 0).mp Good).1
    exact NoHit E.symm (switch_implies_commit d G r N x e mask S Change) T

/-- Markwise condition on the sampled tape. There is no requirement
that another chart be idle. SEAL and COMMIT can be in flight: only
their own respective physical writer marks are excluded. -/
def CentreWriterFree (d : Sheet) (C : Chart h) :
    Raw s n → List (Fin n) → Prop
  | _, [] => True
  | x, e::w =>
    (e=centre C → (readPC d C x).2≠sealOp (params d s) ∨
      (tok d C x C.a).tag≠2) ∧
    (e=out C (C.a-1) → (readPC d C x).2≠commitOp (params d s) ∨
      (tok d C x (C.a-1)).tag≠2) ∧
    CentreWriterFree d C (rawNext s x e) w

theorem centre_held_framed_run (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (S : StrongSerial d (charter G r) x)
    (Compat : Compatible (rawGrant d x (centre (charter G r))))
    (Held : rawGrant d x (centre (charter G r)) 1=true)
    (Pos : (readPC d (charter G r) x).2≠0)
    (w : List (Fin n)) (NR : NoRestartTape d (charter G r) x w)
    (Frame : CentreWriterFree d (charter G r) x w) :
    let C := charter G r
    let y := rawRun x w
    rawGrant d y (centre C) 1=true ∧
    centreSeal d C y=centreSeal d C x ∧
    rawSelector d y (centre C)=rawSelector d x (centre C) := by
  dsimp only
  let C := charter G r
  let CF := cached_fibre d N hh Q F
  have ⟨_,K,H,P,_⟩ := canonical_centre G r
  induction w generalizing x with
  | nil => exact ⟨Held,rfl,rfl⟩
  | cons e w IH =>
    let y := rawNext s x e
    have Y := CF.closed x e X
    have S' := strong_step d C N hh G F x X S digit e
    have M := CF.mask x X
    have Hold : rawGrant d y (centre C) 1=true := by
      have A := held_incidence_step d C N x e M S Pos C.a K H Compat
        (by change rawGrant d x (centre C) (C.route.port C.a)=true; rw [P]; exact Held)
      change rawGrant d y (centre C) (C.route.port C.a)=true at A
      rw [P] at A
      exact A
    have C' := raw_compatible_step d x e (centre C) (edge_sep N e) Compat
    have ⟨Seal,Sel⟩ := centre_frame_before_ingress d G r N x e M S Pos Frame.1 Frame.2.1
    obtain ⟨A,B,D⟩ := IH y Y S' C' Hold NR.1 NR.2 Frame.2.2
    exact ⟨A,B.trans Seal,D.trans Sel⟩

end L4.ReportGuardedTailSuccess
