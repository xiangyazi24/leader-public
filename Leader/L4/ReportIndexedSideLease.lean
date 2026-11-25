import Leader.L4.ReportAcquireAllCaptures
import Leader.L4.ReportIndexedLaunchData

namespace L4.ReportIndexedSideLease
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl ReportGrantTimeline
open ReportOwnerAcquireReturn
open ReportOwnerAcquireProvenance (BeforeConsume)
open ReportAcquireAllCaptures ReportLeaseGrants ReportIndexedLaunchData

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem held_end (d : Sheet) (i : Fin n) (j : Fin 3) (x : Raw s n) (w : List (Fin n))
    (H : HeldAlong d i j x w) : rawGrant d (rawRun x w) i j=true := by
  induction w generalizing x with
  | nil => exact H
  | cons e w IH => exact IH _ H.2

theorem no_restart_left (d : Sheet) (C : Chart h) (x : Raw s n)
    (w tail : List (Fin n)) (H : NoRestartTape d C x (w++tail)) :
    NoRestartTape d C x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w IH => exact ⟨H.1,IH _ H.2⟩

/-- The bank read out of the actual literal seed agrees with the source
capture index for the selected side port. -/
theorem seeded_reader_bank (p : Params) (v : BitVec p.w) (op : Nat)
    (R : op<writeOp p) (j : Fin 3) (Side : j=0 ∨ j=2) :
    (if j=0 then (concreteSeed p v op).banks/2 else (concreteSeed p v op).banks%2)=
      acqCaptureIndex p v/2^(2-j.val)%2 := by
  have B : acqCaptureIndex p v<8 :=
    (v.extractLsb' (sourceBase p+(16+2*d p)) 3).isLt
  rcases Side with rfl|rfl
  · simp only [concreteSeed,if_pos R,readSeed]
    change (2*(acqCaptureIndex p v/4)+acqCaptureIndex p v%2)/2 =
      acqCaptureIndex p v/4%2
    omega
  · simp only [concreteSeed,if_pos R,if_neg (by decide : (2:Fin 3)≠0),readSeed]
    change (2*(acqCaptureIndex p v/4)+acqCaptureIndex p v%2)%2 = acqCaptureIndex p v/1%2
    omega

/-- The actual old READ/CMP sample can be a nonheader. Its lease is at the unique
header incidence with the same chart port, not at the sampled site itself.
The two supplied splits are of the exact, uncommuted nonrestart tape. -/
theorem read_sample_side_lease (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (issue : Raw s n) (X : Cached d hh Q issue)
    (I : LegalIssue d C issue) (P : readPC d C issue=(1,acqOp (params d s)))
    (Compat : ∀ i,h i=true→Compatible (rawGrant d issue i))
    (digit : 0<(params d s).digits)
    (w : List (Fin n)) (T : BeforeConsume d C (rawNext s issue (door C)) w)
    (Tag : (tok d C (rawRun (rawNext s issue (door C)) w) 0).tag=3)
    (ND : (tok d C (rawRun (rawNext s issue (door C)) w) 0).outcome≠1)
    (lead fly pre tail : List (Fin n)) (k : Nat)
    (Split : fly=pre++out C k::tail)
    (op : Nat) (Read : op<writeOp (params d s))
    (Side : C.route.port k=0 ∨ C.route.port k=2)
    (NR : NoRestartTape d C (rawNext s (rawRun (rawNext s issue (door C)) w) (door C))
      (lead++door C::fly)) :
    let x0 := rawNext s issue (door C)
    let after := rawNext s (rawRun x0 w) (door C)
    let upto := lead++[door C]++pre
    let old := rawRun (rawNext s (rawRun after lead) (door C)) pre
    ∃ i, i<C.L ∧ h (out C i)=true ∧ C.route.port i=C.route.port k ∧
      (∀ j,j<C.L→h (out C j)=true→C.route.port j=C.route.port k→j=i) ∧
      CapturedAt d C x0 w i (ownerCaptureSix d C old) ∧
      HeldAlong d (out C i) (C.route.port k) after upto ∧
      rawGrant d old (out C i) (C.route.port k)=true ∧
      Compatible (rawGrant d old (out C i)) ∧
      let launch := rawRun after lead
      let sent := concreteSeed (params d s) (selectBytes d (launch C.root)) op
      ∃ u v : List (Fin n), ∃ r : Nat,
        w=u++out C i::v ∧
        let cap := rawRun x0 u
        let bytes := selectBytes d (cap (out C i))
        ReportOwnerAcquireProvenance.FState d C cap i r ∧
        acqFlightWin (params d s) true bytes (C.route.port i)=true ∧
        rawGrant d (rawNext s cap (out C i)) (out C i) (C.route.port i)=true ∧
        (if C.route.port k=0 then sent.banks/2 else sent.banks%2)=
          publicationSelector (params d s) bytes := by
  dsimp only
  let x0 := rawNext s issue (door C)
  let after := rawNext s (rawRun x0 w) (door C)
  let upto := lead++[door C]++pre
  let old := rawRun (rawNext s (rawRun after lead) (door C)) pre
  have E : rawRun after upto=old := by
    rw [show upto=(lead++[door C])++pre from rfl,ShortOwnerEpochJS.raw_append,
      ShortOwnerEpochJS.raw_snoc]
  have V : lead++door C::fly=upto++out C k::tail := by
    rw [Split]
    simp [upto,List.append_assoc]
  have NP : NoRestartTape d C after upto :=
    no_restart_left d C after upto (out C k::tail) (V ▸ NR)
  obtain ⟨i,B,H,Lane⟩ := (header_lane_geometry C G).2 (C.route.port k)
  have Unique : ∀ j,j<C.L→h (out C j)=true→C.route.port j=C.route.port k→j=i :=
    fun j J HJ EQ => (header_lane_geometry C G).1 j i J B HJ H (EQ.trans Lane.symm)
  have S := (all_captures_after_consume d C hh G F N issue X I P Compat digit
    w T Tag ND upto NP).2.2.2 i B H
  have End : rawGrant d old (out C i) (C.route.port i)=true :=
    E ▸ held_end d (out C i) (C.route.port i) after upto S.2
  have C0 := ReportAcquireWinHold.compatible_run d N issue (out C i) (Compat (out C i) H)
    ([door C]++w++[door C]++upto)
  rw [ShortOwnerEpochJS.raw_append,ShortOwnerEpochJS.raw_snoc,ShortOwnerEpochJS.raw_append] at C0
  rw [ShortOwnerEpochJS.raw_snoc] at C0
  change Compatible (rawGrant d old (out C i)) at C0
  have Cap := S.1
  rw [E] at Cap
  refine ⟨i,B,H,Lane,Unique,Cap,Lane ▸ S.2,Lane ▸ End,C0,?_⟩
  let launch := rawRun after lead
  have NL := no_restart_left d C after lead (door C::fly) NR
  have LS := (all_captures_after_consume d C hh G F N issue X I P Compat digit
    w T Tag ND lead NL).2.2.2 i B H
  obtain ⟨u,v,r,Split0,Old,Win,Post,Index,_⟩ :=
    captured_file_fields d C x0 launch w i LS.1
  have Seed := seeded_reader_bank (params d s) (selectBytes d (launch C.root)) op Read
    (C.route.port k) Side
  rw [←Lane] at Seed
  exact ⟨u,v,r,Split0,Old,Win,Post,Lane ▸ Seed.trans Index⟩

#print axioms seeded_reader_bank
#print axioms read_sample_side_lease
end L4.ReportIndexedSideLease
