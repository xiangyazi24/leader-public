import Leader.L4.ReportOwnerForwardControl

namespace L4.ReportOwnerIssueControl
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport ReportOwnerForwardLocations ReportOwnerReverseControl
open ReportOwnerForwardControl ReportPrelaunchClock ReportPrelaunchDoorLift ReportOwnerDoorProjection
open ReportByteRows ReportRawProjection

variable {s n : Nat} {h : Fin n→Bool}

def LegalIssue (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  (readPC d C x).2≤commitOp (params d s) ∧ EmptyIssueShape d C x

def Retry0 (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  (readPC d C x).2=0 ∧ EmptyIssueShape d C x

/-- The actual door mark from clean legal ISSUE either retries at
clean ISSUE0 or launches exactly one new F at the chart root. -/
theorem door_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : LegalIssue d C x) :
    let y := rawNext s x (door C)
    Retry0 d C y ∨ (ForwardWait d C y 0 ∧ (readPC d C y).2=(readPC d C x).2) := by
  dsimp only
  let p := params d s
  let y := rawNext s x (door C)
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have CF := cached_fibre d N hh Q F
  have Y := CF.closed x (door C) X
  have H (i : Nat) (I : i<C.L) (Z : 0<i) : (tok d C y i).tag=0 := by
    rw [decoded_frame d C hh G x y X Y i I (raw_door_frame d C x i Z I)]
    exact R.2.2 i I
  have O : sourceOpcode p v≤commitOp p := R.1
  have P : sourcePhase p v=1 := R.2.1
  have W := raw_door_final d C x N (CF.mask x X)
  have WR := W.2
  change resetTokenRead p (selectBytes d (y C.root)) 0=
    (match (source p v t).2 with
    | none => prelaunchDoorNormWire p v
    | some q => resetTokenWire p q) at WR
  rcases source_issue_joint p v t P O with ⟨CP,RW⟩|⟨CP,z,RW,Z,F0⟩
  · have CT := W.1.trans CP
    rw [RW] at WR
    left
    refine ⟨congrArg Prod.snd CT,congrArg Prod.fst CT,?_⟩
    intro i I
    by_cases K : i=0
    · subst i
      rw [root_tok,WR]
      exact prelaunch_empty_wire_tag p
    · exact H i I (by omega)
  · have CT := W.1.trans CP
    rw [RW] at WR
    right
    have CP2 := congrArg Prod.snd CT
    refine ⟨⟨⟨congrArg Prod.fst CT,?_⟩,C.positive,?_⟩,CP2⟩
    · change (controlWork p (selectBytes d (y C.root))).2≤commitOp p
      rw [CP2]
      exact O
    · intro i I
      by_cases K : i=0
      · subst i
        rw [root_tok,WR]
        exact (rank_encode_tag p false z F0).trans Z
      · simpa [frontTag,K] using H i I (by omega)

/-- No off-door mark can create an F or D on an all-E chart or change
its owner source PC. Local E stays E in each old-pair routing case. -/
theorem nondoor_preserves (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (R : LegalIssue d C x)
    (e : Fin n) (D0 : e≠door C) :
    let y := rawNext s x e
    LegalIssue d C y ∧ readPC d C y=readPC d C x := by
  dsimp only
  let CF := cached_fibre d N hh Q F
  have Y := CF.closed x e X
  have PC := raw_nondoor_control d C x e N (CF.mask x X) D0
  refine ⟨⟨?_,?_,?_⟩,PC⟩
  · rw [PC]; exact R.1
  · rw [PC]; exact R.2.1
  · by_cases A : ∃ j,j<C.L ∧ e=out C j
    · obtain ⟨j,J,rfl⟩ := A
      have loc (i : Nat) (I : i<C.L) (L : i≠j) (K : i≠j+1) :
          (tok d C (rawNext s x (out C j)) i).tag=0 := by
        rw [decoded_frame d C hh G x _ X Y i I (raw_link_frame d C x j i J I L K)]
        exact R.2.2 i I
      have LF : (tok d C x j).tag≠2 := by rw [R.2.2 j J]; decide
      have LT : (tok d C x j).tag≠1 := by rw [R.2.2 j J]; decide
      by_cases K : j+1<C.L
      · obtain ⟨L,B⟩ := idle_internal_tags d C hh G F N x X j K LF
          (by rw [R.2.2 (j+1) K]; decide) (fun A=>LT A.1)
        intro i I
        by_cases E : i=j
        · subst i; exact L.trans (R.2.2 _ J)
        · by_cases E' : i=j+1
          · subst i; exact B.trans (R.2.2 _ K)
          · exact loc i I E E'
      · have L := idle_end_tag d C hh G F N x X j (by omega) LF LT
        intro i I
        by_cases E : i=j
        · subst i; exact L.trans (R.2.2 _ J)
        · exact loc i I E (by omega)
    · intro i I
      rw [decoded_frame d C hh G x _ X Y i I
        (raw_off_frame d C x e D0 (fun j J U=>A ⟨j,J,U⟩) i I)]
      exact R.2.2 i I

end L4.ReportOwnerIssueControl
