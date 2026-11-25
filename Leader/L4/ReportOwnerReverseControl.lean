import Leader.L4.ReportOwnerReverseShape

namespace L4.ReportOwnerReverseControl
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport ReportOwnerReverseShape
open ReportPrelaunchClock ReportPrelaunchDoorLift ReportOwnerDoorProjection
open ReportByteRows ReportRawProjection

variable {s n : Nat} {h : Fin n→Bool}

def LegalWait (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  (readPC d C x).1=2 ∧ (readPC d C x).2≤commitOp (params d s)

def ReverseWait (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  LegalWait d C x ∧ Reverse d C x k

def EmptyIssueShape (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  (readPC d C x).1=1 ∧ ∀ i,i<C.L→(tok d C x i).tag=0

private theorem tok_root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

/-- WAIT root trail: no advance to a new source instruction while
the D is still deeper in the chart. The root tag may be proved after
literal normalization; the theorem does not assume wire byte equality. -/
theorem door_holds_noneroot (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (K : 0<k)
    (R : ReverseWait d C x k) : ReverseWait d C (rawNext s x (door C)) k := by
  let p := params d s
  let y := rawNext s x (door C)
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x _ X
  have H : t.tag=1 := by
    dsimp [t,p,v]
    rw [←tok_root_pub d C x,R.2.2 0 C.positive]
    simp [backTag,K]
  have P : sourcePhase p v=2 := R.1.1
  have O : sourceOpcode p v≤commitOp p := R.1.2
  have W := raw_door_final d C x N (CF.mask x X)
  have CP := W.1.trans (prelaunch_hold_controls p v t P O (.inl H))
  have WR := W.2
  change resetTokenRead p (selectBytes d (y C.root)) 0=
    (match (source p v t).2 with
    | none => prelaunchDoorNormWire p v
    | some q => resetTokenWire p q) at WR
  rw [prelaunch_wait_hold p v t P O (.inl H)] at WR
  have RT : (tok d C y 0).tag=(tok d C x 0).tag := by
    rw [root_tok d C y,tok_root_pub d C x,WR]
    exact prelaunch_door_norm_tag p v
  refine ⟨⟨?_,?_⟩,R.2.1,?_⟩
  · exact (congrArg Prod.fst CP).trans P
  · change (controlWork p (selectBytes d (y C.root))).2≤commitOp p
    rw [CP]
    exact O
  · intro i I
    by_cases Z : i=0
    · subst i
      exact RT.trans (R.2.2 0 I)
    · have Pos : 0<i := by omega
      rw [decoded_frame d C hh G x y X Y i I (raw_door_frame d C x i Pos I)]
      exact R.2.2 i I

/-- D at the root: the real source mark returns to ISSUE and wipes
the only live occurrence. This includes a failed or fault reply,
without crediting it as a successful next arithmetic instruction. -/
theorem door_consumes_root (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (digit : 0<(params d s).digits) : EmptyIssueShape d C (rawNext s x (door C)) := by
  let p := params d s
  let y := rawNext s x (door C)
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x _ X
  have H : t.tag=3 := by
    dsimp [t,p,v]
    rw [←tok_root_pub d C x,R.2.2 0 C.positive]
    rfl
  have P : sourcePhase p v=2 := R.1.1
  have O : sourceOpcode p v≤commitOp p := R.1.2
  have NT : t.tag≠1 := by rw [H]; decide
  have NF : t.tag≠2 := by rw [H]; decide
  have W := raw_door_final d C x N (CF.mask x X)
  have C0 := prelaunch_wait_controls p v t P O NT NF digit
  have WR := W.2
  change resetTokenRead p (selectBytes d (y C.root)) 0=
    (match (source p v t).2 with
    | none => prelaunchDoorNormWire p v
    | some q => resetTokenWire p q) at WR
  rw [prelaunch_wait_clears_token p v t P O NT NF] at WR
  refine ⟨?_,?_⟩
  · rcases C0 with S|⟨_,_,S⟩
    · exact congrArg Prod.fst (W.1.trans S)
    · exact congrArg Prod.fst (W.1.trans S)
  · intro i I
    by_cases Z : i=0
    · subst i
      rw [root_tok,WR]
      exact prelaunch_empty_wire_tag p
    · have Pos : 0<i := by omega
      rw [decoded_frame d C hh G x y X Y i I (raw_door_frame d C x i Pos I),R.2.2 i I]
      simp [backTag,Z]

/-- Every physical mark in the structural reverse branch either holds
it, transports one D backwards, or consumes at the unique owner door. -/
theorem all_mark (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : ReverseWait d C x k)
    (digit : 0<(params d s).digits) (e : Fin n) :
    let y := rawNext s x e
    ReverseWait d C y k ∨ (∃ j,k=j+1 ∧ e=out C j ∧ ReverseWait d C y j) ∨
      (k=0 ∧ e=door C ∧ EmptyIssueShape d C y) := by
  dsimp only
  by_cases D : e=door C
  · subst e
    by_cases K : k=0
    · subst k
      exact .inr (.inr ⟨rfl,rfl,door_consumes_root d C hh G F N x X R digit⟩)
    · exact .inl (door_holds_noneroot d C hh G F N x X k (by omega) R)
  · have CF := cached_fibre d N hh Q F
    have P : LegalWait d C (rawNext s x e) := by
      unfold LegalWait
      rw [raw_nondoor_control d C x e N (CF.mask x X) D]
      exact R.1
    rcases non_door_step d C hh G F N x X k R.2 e D with S|⟨j,J,E,S⟩
    · exact .inl ⟨P,S⟩
    · exact .inr (.inl ⟨j,J,E,P,S⟩)

end L4.ReportOwnerReverseControl
