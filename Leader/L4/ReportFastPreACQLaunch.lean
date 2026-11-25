import Leader.L4.ReportFastAcqWins
import Leader.L4.ReportFastFreshReset
namespace L4.ReportFastAcqWins
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain
open ReportPrelaunchK1Geometry ReportPrelaunchClock ReportOwnerCommandRail
open ReportOwnerIssueControl ReportOwnerAcquireProvenance
open ReportFastFreshReset ReportByteRows ReportRawProjection
open ReportJoinedGrants ReportOwnerProvenanceTransport

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem preacq_first_issue_prefix (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (H : FirstACQIssueTape d C x w) :
    PreACQPrefix d C x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w IH =>
    refine ⟨?_,IH _ H.2.2⟩
    rcases H.1.2 with B|B
    · exact Nat.ne_of_lt B
    · exact False.elim (H.2.1 B)

theorem preacq_prefix_append (d : Sheet) (C : Chart h)
    (x : Raw s n) (u v : List (Fin n)) :
    PreACQPrefix d C x (u++v) ↔
      PreACQPrefix d C x u ∧ PreACQPrefix d C (rawRun x u) v := by
  induction u generalizing x with
  | nil => simp [PreACQPrefix,rawRun,BStarResetSchedule.run]
  | cons e u IH =>
    change ((readPC d C x).2≠acqOp (params d s) ∧
        PreACQPrefix d C (rawNext s x e) (u++v)) ↔
      ((readPC d C x).2≠acqOp (params d s) ∧
        PreACQPrefix d C (rawNext s x e) u) ∧
        PreACQPrefix d C (rawRun (rawNext s x e) u) v
    rw [IH]
    exact and_assoc.symm

theorem preacq_prefix_counterexample (d : Sheet) (C : Chart h)
    (x : Raw s n) (P : AtACQIssue d C x) (e : Fin n) (v : List (Fin n)) :
    ¬PreACQPrefix d C x (e::v) := by
  intro H
  exact H.1 (congrArg Prod.snd P)

theorem preacq_empty_clear_step (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (O : OwnClear d C x) (e : Fin n) :
    OwnClear d C (rawNext s x e) := by
  intro i _ K H
  apply absent_step d x e (out C i) (C.route.port i) N
    (((cached_fibre d N hh Q F).mask x X _).trans H)
    (O i (Nat.zero_le _) K H)
  intro _
  have A : tok d C x i = publicationToken (params d s) true
      (selectBytes d (x (out C i))) (C.route.port i) := by
    rw [predecessor_projection,H]
    rfl
  change (((publicationToken (params d s) true (selectBytes d (x (out C i)))
      (C.route.port i)).tag==2) &&
    !(publicationToken (params d s) true (selectBytes d (x (out C i)))
      (C.route.port i)).fault &&
    (publicationToken (params d s) true (selectBytes d (x (out C i)))
      (C.route.port i)).opcode==acqOp (params d s))=false
  simp [←A,I.2.2 i K]

theorem preacq_empty_wait_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (PC : AtACQIssue d C x) (O : OwnClear d C x)
    (v : List (Fin n)) (ND : ∀ e∈v,e≠door C) :
    Cached d hh Q (rawRun x v) ∧ LegalIssue d C (rawRun x v) ∧
      AtACQIssue d C (rawRun x v) ∧ OwnClear d C (rawRun x v) := by
  induction v generalizing x with
  | nil => exact ⟨X,I,PC,O⟩
  | cons e v IH =>
    have Y := (cached_fibre d N hh Q F).closed x e X
    obtain ⟨J,E⟩ := nondoor_preserves d C hh G F N x X I e (ND e (by simp))
    have P : AtACQIssue d C (rawNext s x e) := E.trans PC
    have A := preacq_empty_clear_step d C N hh F x X I O e
    exact IH _ Y J P A (fun a K=>ND a (by simp [K]))

theorem preacq_cached_serial_run (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n)
    (X : Cached d hh Q x) (S : StrongSerial d C x) (w : List (Fin n)) :
    Cached d hh Q (rawRun x w) ∧ StrongSerial d C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact ⟨X,S⟩
  | cons e w IH =>
    exact IH _ ((cached_fibre d N hh Q F).closed x e X)
      (strong_step d C N hh G F x X S digit e)

theorem preacq_launch_from_split (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (reset u v : List (Fin n)) (R : Generated d C x reset .done)
    (T : FirstACQIssueTape d C (rawRun x reset) u)
    (ND : ∀ e∈v,e≠door C) :
    let b := rawRun (rawRun x reset) u
    let y := rawRun b v
    PreACQPrefix d C (rawRun x reset) u ∧
      OwnClear d C y ∧ AtACQIssue d C y ∧
      FState d C (rawNext s y (door C)) 0 64 ∧
      OwnClear d C (rawNext s y (door C)) := by
  dsimp only
  let a := rawRun x reset
  let b := rawRun a u
  let y := rawRun b v
  have U := preacq_first_issue_prefix d C a u T
  have PC := first_issue_tape_end d C a u T
  have A := (cached_genuine_full_parked d C N hh F x X reset R).1
  have S := seed_receipt d C N hh F x X reset R
  obtain ⟨B,SB⟩ := preacq_cached_serial_run d C N hh G F digit a A S u
  have I := preACQ_legal_issue d C b SB PC
  have O := own_clear_from_receipt d C N hh G F digit x X reset u R U
  obtain ⟨Y,J,PCY,OY⟩ := preacq_empty_wait_run d C N hh G F b B I PC O v ND
  have L := (ReportOwnerAcquireProvenance.launch d C hh G F N y Y J PCY).2
  exact ⟨U,OY,PCY,L,issue_clear d C N hh F y Y J OY⟩

end L4.ReportFastAcqWins
