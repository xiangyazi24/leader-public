import Leader.L4.ReportAcqExtract
import Leader.L4.ReportWriteOrigin
import Leader.L4.ReportGoodEightBank

namespace L4.ReportWriteBankClosure
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerIssueControl
open ReportOwnerAcquireReturn ReportGenerationAncestry ReportLeaseOwner
open ReportGoodEightBank ReportAcqExtract ReportWriteOrigin

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private theorem nr_snoc (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (e : Fin n) (A : NoRestartTape d C x w)
    (B : (readPC d C (rawNext s (rawRun x w) e)).2≠0) :
    NoRestartTape d C x (w++[e]) := by
  induction w generalizing x with
  | nil => exact ⟨B,trivial⟩
  | cons a w IH => exact ⟨A.1, IH _ A.2 B⟩

private theorem nr_append (d : Sheet) (C : Chart h) (x : Raw s n)
    (u v : List (Fin n)) (A : NoRestartTape d C x u)
    (B : NoRestartTape d C (rawRun x u) v) :
    NoRestartTape d C x (u++v) := by
  induction u generalizing x with
  | nil => exact B
  | cons a w IH => exact ⟨A.1, IH _ A.2 B⟩

theorem no_restart_on_write_flight (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (A : WriteF d C x 0 t)
    (Pos : (readPC d C x).2≠0)
    (w : List (Fin n)) (k : Nat) (T : BeforeWriteTurn d C x w k) :
    NoRestartTape d C x w := by
  induction T with
  | nil => trivial
  | @hold u j e U H IH =>
    apply nr_snoc d C x u e IH
    rw [←ShortOwnerEpochJS.raw_snoc]
    rw [write_origin_pc d C hh G F N x X t A (u++[e]) j (.hold e U H)]
    exact Pos
  | @hop u j U H IH =>
    apply nr_snoc d C x u (out C j) IH
    rw [←ShortOwnerEpochJS.raw_snoc]
    rw [write_origin_pc d C hh G F N x X t A _ _ (.hop U H)]
    exact Pos

/-- Actual issued WRITE cut + its forward trace give the existing
conditional BankSafe consumer's complete WriteOrigin witness. Both
ACQ cuts are reconstructed from the same genuine RESET receipt. -/
theorem write_origin_from_issue_cut (d : Sheet) (hh : ∃ i,h i=true)
    (G : GapInput h) (F : Fibre (h:=h) d Q) (N : 1<n)
    (r : Owner h) (a : Raw s n) (X : Cached d hh Q a) (reset : List (Fin n))
    (R : Generated d (charter G r) a reset .done) (digit : 0<(params d s).digits)
    (pre post : List (Fin n)) (k : Nat) (t : Tok)
    (I : LegalIssue d (charter G r) (rawRun (rawRun a reset) pre))
    (P : let x := rawRun (rawRun a reset) pre
      sourcePhase (params d s) (selectBytes d (x (charter G r).root))=1)
    (L : let x := rawRun (rawRun a reset) pre
      writeOp (params d s)≤sourceOpcode (params d s) (selectBytes d (x (charter G r).root)))
    (U : let x := rawRun (rawRun a reset) pre
      sourceOpcode (params d s) (selectBytes d (x (charter G r).root))<sealOp (params d s))
    (S : let v := selectBytes d (rawRun (rawRun a reset) pre (charter G r).root)
      (source (params d s) v (publicationToken (params d s) true v 0)).2=some t)
    (T : t.tag=2)
    (Trace : let C := charter G r
      BeforeWriteTurn d C (rawNext s (rawRun (rawRun a reset) pre) (door C)) post k)
    (Live : let C := charter G r
      (tok d C (rawRun (rawRun a reset) (pre++door C::post)) k).fault=false) :
    WriteOrigin d G r (rawRun a reset) (pre++door (charter G r)::post) k := by
  let C := charter G r
  let p := params d s
  let b := rawRun a reset
  let x := rawRun b pre
  let y := rawNext s x (door C)
  have B := (cached_genuine_full_parked d C N hh F a X reset R).1
  have X' := ReportGoodEightCut.cached_run d N hh F b B pre
  have Y := (cached_fibre d N hh Q F).closed x (door C) X'
  have Bound : cmpOp p≤(readPC d C x).2 := by
    change writeOp p≤(readPC d C x).2 at L
    unfold writeOp at L
    unfold cmpOp
    omega
  have H : AcqHistory d C b pre := acq_history_after_receipt d C N hh G F digit a X reset pre R
    (logical_after_acq_of_preseal p _ Bound U)
  obtain ⟨lead,fly,q,W,J,K,TC,Tag,ND,NR⟩ := H
  let acq := rawRun b lead
  let after := rawNext s (rawRun (rawNext s acq (door C)) fly) (door C)
  have E : x=rawRun after q := by
    unfold x
    rw [W,ShortOwnerEpochJS.raw_append]
    change rawRun (rawNext s acq (door C)) (fly++door C::q)=rawRun after q
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  have A := write_launch d C hh G F N x X' I t P L U S T
  have Q0 : (readPC d C y).2=(readPC d C x).2 := by
    rcases ReportOwnerIssueControl.door_step d C hh G F N x X' I with D|⟨_,D⟩
    · have Z := D.2.1
      rw [A.shape.1.1] at Z
      contradiction
    · exact D
  have Pos : (readPC d C y).2≠0 := by
    rw [Q0]
    unfold cmpOp at Bound
    omega
  have FNR := no_restart_on_write_flight d C hh G F N y Y t A Pos post k Trace
  have NR' : NoRestartTape d C after (q++door C::post) := by
    apply nr_append d C after q (door C::post) NR
    rw [←E]
    exact ⟨Pos,FNR⟩
  have X0 := ReportGoodEightCut.cached_run d N hh F b B lead
  have Rail0 := rail_after_history_consume d C N hh G F digit acq X0 J K fly TC Tag ND q
  have Rail1 := rail_after_history_consume d C N hh G F digit acq X0 J K fly TC Tag ND (q++door C::post)
  have M : rawRun b (pre++door C::post)=rawRun y post := by
    rw [ShortOwnerEpochJS.raw_append]
    rfl
  change (tok d C (rawRun b (pre++door C::post)) k).fault=false at Live
  rw [M] at Live
  obtain ⟨Z,PC⟩ := healthy_origin_from_issue d C hh G F N x X' I t P L U S T post k Trace Live
  have Match : tok d C (rawRun b (pre++door C::post)) k=t := M ▸ Z
  have End : (readPC d C (rawRun b (pre++door C::post))).2<sealOp p := by
    rw [M,PC]
    exact U
  dsimp only [WriteOrigin]
  refine ⟨lead,fly,q,post,t,?_,J,K,TC,Tag,ND,NR,Rail0,NR',Rail1,?_,?_,?_,?_,T,Match,End⟩
  · rw [W]
    simp [List.append_assoc,C]
  · rw [←E]
    exact P
  · rw [←E]
    exact L
  · rw [←E]
    exact U
  · rw [←E]
    exact S

#print axioms no_restart_on_write_flight
#print axioms write_origin_from_issue_cut
end L4.ReportWriteBankClosure
