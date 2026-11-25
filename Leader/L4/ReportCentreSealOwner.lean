import Leader.L4.ReportGoodEightCut
import Leader.L4.ReportJoinedSealFrame
import Leader.L4.ReportOwnerCommandRail
import Leader.L4.ReportIngressOwnership

namespace L4.ReportCentreSealOwner
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerCommandRail
open ReportGenerationAncestry ReportLeaseOwner ReportJoinedSealFrame
open ReportIngressOwnership ReportOwnerProvenanceTransport ReportRawProjection

variable {s n : Nat} {h : Fin n→Bool}

def centreSeal (d : Sheet) (C : Chart h) (x : Raw s n) : Option Nat :=
  reportOldSeal (params d s) (selectBytes d (x (centre C)))

/-- No event touching the centre's seal on this actual old mark. -/
def NoSealEvent (d : Sheet) (C : Chart h) (x : Raw s n) (e : Fin n) : Prop :=
  let p := params d s
  let a := centre C
  let u := selectBytes d (x a)
  (e=a → ¬reportHeaderResetSeal p u) ∧ (e=a → ¬reportHeaderSetSeal p u) ∧
    (rightNeighbor e=a → ¬ancestryCommitOpportunity p (h e) true (selectBytes d (x e)) u)

/-- The exact cases which can update one chart centre's seal, pegged
to its own outgoing K1 or incoming K0 occurrence. No unrelated
owner or post-ACK state is used. -/
theorem centre_seal_marks (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (x : Raw s n) (e : Fin n)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (S : StrongSerial d (charter G r) x) :
    let C := charter G r
    let p := params d s
    let a := centre C
    let u := selectBytes d (x a)
    let y := rawNext s x e
    (e=a ∧ reportHeaderResetSeal p u ∧
       (readPC d C x).2=0 ∧ centreSeal d C y=none) ∨
    (e=a ∧ reportHeaderSetSeal p u ∧
       (readPC d C x).2=sealOp p ∧
       centreSeal d C y=some (tok d C x C.a).payload) ∨
    (rightNeighbor e=a ∧
       ancestryCommitOpportunity p (h e) true (selectBytes d (x e)) u ∧
       (readPC d C x).2=commitOp p ∧ centreSeal d C y=none) ∨
    (NoSealEvent d C x e ∧ centreSeal d C y=centreSeal d C x) := by
  dsimp only
  let C := charter G r
  let p := params d s
  let a := centre C
  let u := selectBytes d (x a)
  obtain ⟨_,A,H,J,_⟩ := canonical_centre G r
  have T : tok d C x C.a=publicationToken p true u 1 := by
    rw [predecessor_projection,H,J]
    rfl
  by_cases E : e=a
  · subst e
    have R := raw_header_left_seal_step d x a N mask H
    by_cases B : reportHeaderResetSeal p u
    · have Tag := ((rankReady_iff p true u 1).mp B.1).1
      have pc := S.2 C.a A (.inl ((congrArg MISByteCodec.Token.tag T).trans Tag))
        ((congrArg MISByteCodec.Token.fault T).trans B.2.1)
      exact .inl ⟨rfl,B,pc.symm.trans ((congrArg MISByteCodec.Token.opcode T).trans B.2.2),R.1 B⟩
    · by_cases D : reportHeaderSetSeal p u
      · have Tag := ((rankReady_iff p true u 1).mp D.1).1
        have pc := S.2 C.a A (.inl ((congrArg MISByteCodec.Token.tag T).trans Tag))
          ((congrArg MISByteCodec.Token.fault T).trans D.2.1)
        exact .inr (.inl ⟨rfl,D,pc.symm.trans ((congrArg MISByteCodec.Token.opcode T).trans D.2.2.1),
          (R.2.1 D).trans (congrArg (fun t : Tok => some t.payload) T).symm⟩)
      · exact .inr (.inr (.inr ⟨⟨fun _=>B,fun _=>D,fun Z=>(edge_sep N a Z.symm).elim⟩,
          R.2.2 B D⟩))
  · by_cases W : rightNeighbor e=a
    · have R := raw_header_right_seal_step d x e N mask (W.symm ▸ H)
      rw [W] at R
      by_cases D : ancestryCommitOpportunity p (h e) true (selectBytes d (x e)) u
      · obtain ⟨K,F⟩ := ingress_cell G r e W
        have P : out C (C.a-1)=e := congrArg Prod.fst F
        have Port : C.route.port (C.a-1)=0 := congrArg Prod.snd F
        have T0 : tok d C x (C.a-1)=publicationToken p (h e) (selectBytes d (x e)) 0 := by
          rw [predecessor_projection,P,Port]
          rfl
        have Tag := ((rankReady_iff p (h e) (selectBytes d (x e)) 0).mp D.2.1).1
        have pc := S.2 (C.a-1) K (.inl ((congrArg MISByteCodec.Token.tag T0).trans Tag))
          ((congrArg MISByteCodec.Token.fault T0).trans D.2.2.1)
        exact .inr (.inr (.inl ⟨W,D,pc.symm.trans ((congrArg MISByteCodec.Token.opcode T0).trans D.2.2.2.1),R.1 D⟩))
      · exact .inr (.inr (.inr ⟨⟨fun K=>(E K).elim,fun K=>(E K).elim,fun _=>D⟩,R.2 D⟩))
    · have R := raw_header_seal_hold_of_no_event d x a e N mask H
        (fun K=>False.elim (E K)) (fun K=>False.elim (E K))
        (fun K=>False.elim (W K.symm))
      exact .inr (.inr (.inr ⟨⟨fun K=>(E K).elim,fun K=>(E K).elim,fun K=>(W K).elim⟩,R⟩))

inductive NoSealTape (d : Sheet) (C : Chart h) (x : Raw s n) : List (Fin n) → Prop
  | nil : NoSealTape d C x []
  | snoc {w : List (Fin n)} (e : Fin n) :
      NoSealTape d C x w → NoSealEvent d C (rawRun x w) e →
      NoSealTape d C x (w++[e])

def SealOrigin (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (delta : Nat) : Prop :=
  ∃ pre post : List (Fin n), w=pre++(centre C::post) ∧
    let old := rawRun x pre
    let y := rawNext s old (centre C)
    (readPC d C old).2=sealOp (params d s) ∧
    reportHeaderSetSeal (params d s) (selectBytes d (old (centre C))) ∧
    (tok d C old C.a).payload=delta ∧ centreSeal d C y=some delta ∧
    NoSealTape d C y post

private theorem snoc_ind {P : List (Fin n) → Prop}
    (nil : P []) (snoc : ∀ w e,P w→P (w++[e])) (w : List (Fin n)) : P w := by
  have aux : ∀ u v, P u → P (u++v) := by
    intro u v
    induction v generalizing u with
    | nil => simp
    | cons e v IH =>
      intro H
      simpa [List.append_assoc] using IH (u++[e]) (snoc u e H)
  exact aux [] w nil

/-- No inherited seal after a genuine RESET. On the actual suffix,
each usable seal has an own real SEAL mark and no intervening centre
event. This proves seal-header custody, not source-issue ancestry. -/
theorem seal_origin_after_receipt (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q)
    (a : Raw s n) (A : Cached d hh Q a) (flight : List (Fin n))
    (R : Generated d (charter G r) a flight .done) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (delta : Nat)
    (H : centreSeal d (charter G r) (rawRun (rawRun a flight) w)=some delta) :
    SealOrigin d (charter G r) (rawRun a flight) w delta := by
  let C := charter G r
  let x := rawRun a flight
  have X := (cached_genuine_full_parked d C N hh F a A flight R).1
  have S := seed_receipt d C N hh F a A flight R
  have CF := cached_fibre d N hh Q F
  have Empty : centreSeal d C x=none := by
    obtain ⟨g,T,_,_,_,_,_,_,Z⟩ :=
      ReportGoodEightCut.generation_seed d C N hh G F a A flight R 0
    exact T.sealBytes.trans Z
  refine snoc_ind (P:=fun w => centreSeal d C (rawRun x w)=some delta→
    SealOrigin d C x w delta) ?_ ?_ w H
  · intro H0
    change centreSeal d C x=some delta at H0
    rw [Empty] at H0
    contradiction
  · intro pre e IH H0
    have B := strong_run d C N hh G F digit x X S pre
    rw [ShortOwnerEpochJS.raw_snoc] at H0
    rcases centre_seal_marks d G r N (rawRun x pre) e (CF.mask _ B.1) B.2.1 with
      Z|Z|Z|⟨No,Frame⟩
    · rw [Z.2.2.2] at H0
      contradiction
    · obtain ⟨E,Set,PC,V⟩ := Z
      change e=centre C at E
      subst e
      have D := Option.some.inj (V.symm.trans H0)
      exact ⟨pre,[],rfl,PC,Set,D,H0,.nil⟩
    · rw [Z.2.2.2] at H0
      contradiction
    · obtain ⟨u,v,W,PC,Set,D,Y,M⟩ := IH (Frame.symm.trans H0)
      refine ⟨u,v++[e],by rw [W]; simp [List.append_assoc],PC,Set,D,Y,.snoc e M ?_⟩
      rw [W,ShortOwnerEpochJS.raw_append] at No
      exact No

/-- An accepted COMMIT actually consumes the descriptor installed
by the last own SEAL since the genuine receipt. This does not read a
descriptor from the terminal reply, which need not retain it. -/
theorem commit_uses_last_centre_seal (d : Sheet) (G : GapInput h) (r : Owner h)
    (N : 1<n) (hh : ∃ i,h i=true) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q)
    (a : Raw s n) (A : Cached d hh Q a) (flight : List (Fin n))
    (R : Generated d (charter G r) a flight .done) (digit : 0<(params d s).digits)
    (w : List (Fin n)) (e : Fin n)
    (atCentre : rightNeighbor e=centre (charter G r))
    (Accept : let x := rawRun (rawRun a flight) w
      ancestryCommitOpportunity (params d s) (h e) true (selectBytes d (x e))
        (selectBytes d (x (centre (charter G r))))) :
    let C := charter G r
    let x := rawRun (rawRun a flight) w
    let delta := (tok d C x (C.a-1)).payload
    SealOrigin d C (rawRun a flight) w delta ∧ centreSeal d C (rawNext s x e)=none := by
  dsimp only
  let C := charter G r
  let x := rawRun (rawRun a flight) w
  let p := params d s
  let u := selectBytes d (x e)
  let v := selectBytes d (x (centre C))
  let t := publicationToken p (h e) u 0
  obtain ⟨_,L⟩ := ingress_cell G r e atCentre
  have P : out C (C.a-1)=e := congrArg Prod.fst L
  have J : C.route.port (C.a-1)=0 := congrArg Prod.snd L
  have T : tok d C x (C.a-1)=t := by
    rw [predecessor_projection,P,J]
    rfl
  have B := Accept.2.2.2.2
  change (!t.applied && reportOldGrant p v 1 &&
    (publicationSelector p v==t.payload/8) &&
    (reportOldSeal p v==some t.payload))=true at B
  simp only [Bool.and_eq_true,beq_iff_eq] at B
  have S := B.2
  have Cap : centreSeal d C x=some (tok d C x (C.a-1)).payload := by
    rw [T]
    exact S
  have X := (cached_genuine_full_parked d C N hh F a A flight R).1
  have SS := seed_receipt d C N hh F a A flight R
  have Z := (strong_run d C N hh G F digit _ X SS w).1
  have H := (canonical_centre G r).2.2.1
  have W := (raw_header_right_seal_step d x e N ((cached_fibre d N hh Q F).mask _ Z)
      (atCentre.symm ▸ H)).1
  rw [atCentre] at W
  exact ⟨seal_origin_after_receipt d G r N hh F a A flight R digit w _ Cap,W Accept⟩

#print axioms commit_uses_last_centre_seal
#print axioms seal_origin_after_receipt
#print axioms centre_seal_marks
end L4.ReportCentreSealOwner
