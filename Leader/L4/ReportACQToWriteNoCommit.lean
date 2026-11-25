import Leader.L4.ReportOwnerAcquireReturn
import Leader.L4.ReportReaderRailNoRelease
import Leader.L4.ReportPreCommitSelector

namespace L4.ReportACQToWriteNoCommit
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchClock
open ReportOwnerDoorProjection ReportByteRows ReportOwnerAcquireReturn

variable {s n : Nat} {h : Fin n→Bool}

theorem no_preview_from_commit (p : Params) (b : Nat) :
    ¬PreviewNextOp p.digits (commitOp p) b := by
  intro P
  generalize E : commitOp p=a at P
  have C : a=4*p.digits+4 := E.symm
  cases P <;> omega

/-- The COMMIT PC can only hold/launch the same opcode, or restart.
In particular no positive command follows it on a no-restart mark. -/
theorem commit_pc_step (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (e : Fin n) (N : 1<n) (mask : ∀ i,lower sheet (oldHeaders (rows s) (x i))=h i)
    (H : PostAcqPC (params sheet s) (readPC sheet C x))
    (Op : (readPC sheet C x).2=commitOp (params sheet s))
    (digit : 0<(params sheet s).digits)
    (NZ : (readPC sheet C (rawNext s x e)).2≠0) :
    (readPC sheet C (rawNext s x e)).2=commitOp (params sheet s) := by
  by_cases D : e=door C
  · subst e
    let p := params sheet s
    let v := selectBytes sheet (x C.root)
    let t := publicationToken p true v 0
    have W := (raw_door_final sheet C x N mask).1
    have O : sourceOpcode p v=commitOp p := Op
    have Pos : 0<sourceOpcode p v := by
      rw [O]
      unfold commitOp
      omega
    rcases H.1 with I|I
    · have V : sourcePhase p v=1 := I
      rcases prelaunch_positive_issue_controls p v t V H.2.2 Pos with R|R
      · exact (NZ (congrArg Prod.snd (W.trans R))).elim
      · exact (congrArg Prod.snd (W.trans R)).trans O
    · have V : sourcePhase p v=2 := I
      by_cases T : t.tag=1 ∨ t.tag=2
      · exact (congrArg Prod.snd (W.trans (prelaunch_hold_controls p v t V H.2.2 T))).trans O
      · rcases prelaunch_wait_controls p v t V H.2.2
          (fun H=>T (.inl H)) (fun H=>T (.inr H)) digit with R|⟨b,P,_⟩
        · exact (NZ (congrArg Prod.snd (W.trans R))).elim
        · rw [O] at P
          exact (no_preview_from_commit p b P).elim
  · rw [raw_nondoor_control sheet C x e N mask D]
    exact Op

def NoCommitThrough (sheet : Sheet) (C : Chart h) : Raw s n→List (Fin n)→Prop
  | x,[] => (readPC sheet C x).2≠commitOp (params sheet s)
  | x,e::w => (readPC sheet C x).2≠commitOp (params sheet s) ∧
      NoCommitThrough sheet C (rawNext s x e) w

/-- Exclude COMMIT on every prefix using the actual non-COMMIT
endpoint, not just no-restart. A WRITE endpoint is a special case. -/
theorem no_commit_before_noncommit_end (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (digit : 0<(params sheet s).digits) (x : Raw s n) (w : List (Fin n))
    (X : Cached sheet hh Q x) (H : PostAcqPC (params sheet s) (readPC sheet C x))
    (NR : NoRestartTape sheet C x w)
    (End : (readPC sheet C (rawRun x w)).2≠commitOp (params sheet s)) :
    NoCommitThrough sheet C x w := by
  induction w generalizing x with
  | nil => exact End
  | cons e w IH =>
      have A : (readPC sheet C (rawNext s x e)).2≠0 ∧
        NoRestartTape sheet C (rawNext s x e) w := NR
      obtain ⟨X',H',_⟩ := raw_postacq_step sheet C hh F N x X e H digit A.1
      have V := IH _ X' H' A.2 End
      have NC : (readPC sheet C (rawNext s x e)).2≠commitOp (params sheet s) := by
        cases w
        · exact V
        · exact V.1
      change (readPC sheet C x).2≠commitOp (params sheet s) ∧ _
      refine ⟨fun P => NC (commit_pc_step sheet C x e N
        ((cached_fibre sheet N hh Q F).mask x X) H P digit A.1),V⟩

open ReportGenerationAncestry ReportReaderRailNoRelease
open ReportPreCommitSelector ReportLeaseOwner ReportPrelaunchK1Geometry

/-- Every ghost snapshot belongs to the corresponding old raw state.
The opcode is read from that state's actual owner rail. -/
def OwnerRailTape (sheet : Sheet) (C : Chart h) :
    Raw s n→List (Fin n)→Prop
  | _,[] => True
  | x,e::w => (∃ g,railState sheet C x g) ∧
      OwnerRailTape sheet C (rawNext s x e) w

theorem selector_through_no_commit (sheet : Sheet)
    (G : GapInput h) (r : Owner h) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (x : Raw s n) (w : List (Fin n)) (X : Cached sheet hh Q x)
    (Rail : OwnerRailTape sheet (charter G r) x w)
    (Safe : NoCommitThrough sheet (charter G r) x w) :
    rawSelector sheet (rawRun x w) (centre (charter G r))=
      rawSelector sheet x (centre (charter G r)) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w IH =>
      let C := charter G r
      let y := rawNext s x e
      have R : (∃ g,railState sheet C x g) ∧ OwnerRailTape sheet C y w := Rail
      obtain ⟨⟨g,Gr⟩,R'⟩ := R
      have S : (readPC sheet C x).2≠commitOp (params sheet s) ∧
        NoCommitThrough sheet C y w := Safe
      have Cnot := fun Eq : g.op=commitOp (params sheet s) =>
        S.1 ((rail_opcode sheet C x g Gr).trans Eq)
      have CF := cached_fibre sheet N hh Q F
      have Frame := selector_frame_noncommit sheet G r x g Gr Cnot e N (CF.mask x X)
      exact (IH y (CF.closed x e X) R' S.2).trans Frame

/-- Actual post-ACQ suffix ending at a WRITE. The endpoint excludes a
latent COMMIT earlier on the same no-restart generation. -/
theorem selector_before_write (sheet : Sheet) (G : GapInput h) (r : Owner h)
    (hh : ∃ i,h i=true) {Q : Raw s n→Prop} (F : Fibre (h:=h) sheet Q) (N : 1<n)
    (digit : 0<(params sheet s).digits) (x : Raw s n) (w : List (Fin n))
    (X : Cached sheet hh Q x)
    (H : PostAcqPC (params sheet s) (readPC sheet (charter G r) x))
    (NR : NoRestartTape sheet (charter G r) x w)
    (Rail : OwnerRailTape sheet (charter G r) x w)
    (End : (readPC sheet (charter G r) (rawRun x w)).2<sealOp (params sheet s)) :
    rawSelector sheet (rawRun x w) (centre (charter G r))=
      rawSelector sheet x (centre (charter G r)) := by
  have E : (readPC sheet (charter G r) (rawRun x w)).2≠commitOp (params sheet s) := by
    intro R
    rw [R] at End
    unfold sealOp commitOp at End
    omega
  exact selector_through_no_commit sheet G r hh F N x w X Rail
    (no_commit_before_noncommit_end sheet (charter G r) hh F N digit x w X H NR E)

#print axioms selector_through_no_commit
#print axioms selector_before_write
#print axioms no_preview_from_commit
#print axioms commit_pc_step
#print axioms no_commit_before_noncommit_end
end L4.ReportACQToWriteNoCommit
