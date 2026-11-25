import Leader.L4.ReportWriteSplit
import Leader.L4.ReportOwnerAcquireProvenance

namespace L4.ReportIssuedSegment
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportPrelaunchDoorLift ReportOwnerCommandRail
open ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerForwardControl
open ReportOwnerDoorProjection ReportOwnerForwardLocations ReportOwnerReverseShape
open ReportOwnerSerial
open ReportOwnerAcquireProvenance (NoConsume BeforeConsume)

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem serial_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (S : Serial d C x) (w : List (Fin n)) :
    Cached d hh Q (rawRun x w) ∧ Serial d C (rawRun x w) := by
  let CF := cached_fibre d N hh Q F
  induction w generalizing x with
  | nil => exact ⟨X,S⟩
  | cons e w IH =>
    exact IH _ (CF.closed x e X) (ReportOwnerSerial.all_mark d C N hh G F x X S digit e)

theorem forward_no_consume (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (I : ForwardWait d C x k) (e : Fin n) :
    NoConsume d C x e := by
  right
  rw [I.2.2 0 C.positive]
  by_cases H : k=0
  · subst k; decide
  · simp [frontTag,show 0<k by omega]

theorem reverse_step_held (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (I : ReverseWait d C x k) (e : Fin n) (H : NoConsume d C x e) :
    readPC d C (rawNext s x e)=readPC d C x := by
  let M := (cached_fibre d N hh Q F).mask x X
  by_cases E : e=door C
  · subst e
    have K : 0<k := by
      by_cases B : k=0
      · subst k
        have Tag : (tok d C x 0).tag=3 := I.2.2 0 C.positive
        exact (H.elim (fun Z=>Z rfl) (fun Z=>Z Tag)).elim
      · omega
    let p := params d s
    let v := selectBytes d (x C.root)
    let t := publicationToken p true v 0
    have D : tok d C x 0=t := by rw [root_tok]; exact (prelaunch_root_decode p v).symm
    have Tag : t.tag=1 := by rw [←D,I.2.2 0 C.positive]; simp [backTag,K]
    exact (raw_door_final d C x N M).1.trans (prelaunch_hold_controls p v t I.1.1 I.1.2 (.inl Tag))
  · exact raw_nondoor_control d C x e N M E

theorem reverse_still_waiting_no_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (I : ReverseWait d C x k) (e : Fin n)
    (P : (readPC d C (rawNext s x e)).1=2) : NoConsume d C x e := by
  by_cases E : e=door C
  · subst e
    right
    intro T
    have Do : k=0 := by
      by_cases H : k=0
      · exact H
      · rw [I.2.2 0 C.positive] at T
        simp [backTag,show 0<k by omega] at T
    subst k
    have P1 : (readPC d C (rawNext s x (door C))).1=1 := (door_consumes_root d C hh G F N x X I digit).1
    omega
  · exact .inl E

/-- An actual WAIT state has an active, unconsumed historical
segment from a physical issue. No opcode arithmetic, tape appeal or
command-specific data is assumed by this structural extraction. -/
theorem waiting_issued_segment (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (I : LegalIssue d C x) (w : List (Fin n))
    (Wait : (readPC d C (rawRun x w)).1=2) :
    ∃ pre fly : List (Fin n), w=pre++door C::fly ∧
      let a := rawRun x pre
      let y := rawNext s a (door C)
      Cached d hh Q a ∧ LegalIssue d C a ∧ ForwardWait d C y 0 ∧
      (readPC d C a).2=(readPC d C (rawRun x w)).2 ∧
      BeforeConsume d C y fly := by
  revert Wait
  rw [←List.reverse_reverse w]
  induction w.reverse with
  | nil =>
    intro P
    change (readPC d C x).1=2 at P
    have I0 := I.2.1
    omega
  | cons e rev IH =>
    rw [List.reverse_cons,ShortOwnerEpochJS.raw_snoc]
    intro Wait
    let u := rev.reverse
    let z := rawRun x u
    change (readPC d C (rawNext s z e)).1=2 at Wait
    obtain ⟨Z,S⟩ := serial_run d C N hh G F digit x X (.inl I) u
    have keep (P : (readPC d C z).1=2)
        (Hold : readPC d C (rawNext s z e)=readPC d C z)
        (No : NoConsume d C z e) :
        ∃ pre fly : List (Fin n), u++[e]=pre++door C::fly ∧
          let a := rawRun x pre
          let y := rawNext s a (door C)
          Cached d hh Q a ∧ LegalIssue d C a ∧ ForwardWait d C y 0 ∧
          (readPC d C a).2=(readPC d C (rawNext s z e)).2 ∧
          BeforeConsume d C y fly := by
      obtain ⟨pre,fly,W,A,L,B,P0,V⟩ := IH P
      have WW : u++[e]=pre++door C::(fly++[e]) := by
        change u=pre++door C::fly at W
        rw [W,List.append_assoc]
        rfl
      have Z0 : z=rawRun (rawNext s (rawRun x pre) (door C)) fly := by
        dsimp only [z,u]
        rw [W,ShortOwnerEpochJS.raw_append]
        rfl
      exact ⟨pre,fly++[e],WW,A,L,B,P0.trans (congrArg Prod.snd Hold).symm,.snoc e V (Z0 ▸ No)⟩
    rcases S with J|⟨k,J⟩|⟨k,J⟩
    · by_cases E : e=door C
      · subst e
        rcases door_step d C hh G F N z Z J with U|⟨B,P⟩
        · have B : (readPC d C (rawNext s z (door C))).1=1 := U.2.1
          omega
        · exact ⟨u,[],rfl,Z,J,B,P.symm,.nil⟩
      · have P : (readPC d C (rawNext s z e)).1=1 := (nondoor_preserves d C hh G F N z Z J e E).1.2.1
        omega
    · exact keep J.1.1 (ReportWriteSplit.forward_step_control d C N hh F z Z k J e)
        (forward_no_consume d C z k J e)
    · have No := reverse_still_waiting_no_consume d C N hh G F digit z Z k J e Wait
      exact keep J.1.1 (reverse_step_held d C N hh F z Z k J e No) No

#print axioms reverse_still_waiting_no_consume
#print axioms waiting_issued_segment
end L4.ReportIssuedSegment
