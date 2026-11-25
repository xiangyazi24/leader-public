import Leader.L4.ReportSealCommitOrigin
import Leader.L4.ReportWriteSplit

namespace L4.ReportLateIngressSplit
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerDoorProjection ReportOwnerProvenanceTransport
open ReportOwnerForwardLocations ReportOwnerForwardControl ReportOwnerIssueControl
open ReportByteRows ReportRawProjection ReportWriteSplit ReportSealCommitOrigin
open ReportSealDescriptor

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

/-- The route cannot enter lane 1 before its first header offset.
Thus a COMMIT prefix ending at the ingress cursor has not applied. -/
theorem no_prior_ingress (C : Chart h) (p : Params) (op k : Nat)
    (K : op=commitOp p → k+1≤C.a-1) : BeforeCommitIngress C op p k := by
  intro O A
  have L : C.a≤k+1 := by
    have R := A.2.2
    change lane C.a C.b (k+1)=1 at R
    exact Nat.le_of_not_gt ((lane1 C.a C.b (k+1)).mp R).1
  have J := K O
  omega

private theorem late_ready (d : Sheet) (C : Chart h) (x : Raw s n)
    (k : Nat) (t : Tok) (A : Flight d C x k t) : readyAt d C x k=true := by
  unfold readyAt
  rw [rankReady_iff,←predecessor_projection]
  rcases A.packet with P|P
  · rw [P]
    refine ⟨A.origin.1,?_⟩
    intro R
    have E := R.1.2.2
    rcases A.origin.2.1 with L|L <;>
      rw [L] at E <;> simp only [sealOp,commitOp,admitOp] at E <;> omega
  · rw [P]
    simp [MISByteCodec.faultToken,healthyAdmit]

/-- Relift the real extracted flight. An apparent hold cannot hide a
label at its own ready front. -/
theorem before_turn_as_late (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (t : Tok) (W : Flight d C x 0 t)
    (u : List (Fin n)) (k : Nat) (R : BeforeTurn d C x u k)
    (K : t.opcode=commitOp (params d s) → k≤C.a-1) :
    BeforeLateIngress d C (s:=s) t.opcode u k := by
  induction R with
  | nil _ => exact .nil
  | @hold w j R e S IH =>
    have H := IH K
    apply BeforeLateIngress.hold e H
    intro E
    subst e
    have A := late_origin_run d C hh G F N x X t W w j H
    let z := rawRun x w
    have M := (cached_fibre d N hh Q F).mask z A.1
    have J := A.2.1.shape.2.1
    have RD := late_ready d C z j t A.2.1
    have Tag : (tok d C (rawNext s z (out C j)) j).tag=2 := by
      rw [S.2.2 j S.2.1]
      simp [frontTag]
    by_cases I : j+1<C.L
    · have F0 := (ready_locations d C z N M j I RD).1
      rw [F0] at Tag
      contradiction
    · have T := ready_turn_tag d C z N M j (by omega) RD
      omega
  | @hop w j R S IH =>
    exact .hop (IH (fun U=>Nat.le_trans (by omega) (K U))) S.2.1
      (no_prior_ingress C _ _ _ K)

theorem healthy_late_origin_from_real_split (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (I : LegalIssue d C x)
    (op : Nat) (Op : op=sealOp (params d s) ∨ op=commitOp (params d s))
    (P : readPC d C x=(1,op))
    (Good : comparisonFile (params d s) (selectBytes d (x C.root))/4≠3 ∧
      comparisonFile (params d s) (selectBytes d (x C.root))%4≠3)
    (u : List (Fin n)) (k : Nat) (R : BeforeTurn d C (rawNext s x (door C)) u k)
    (K : op=commitOp (params d s) → k≤C.a-1)
    (Healthy : (tok d C (rawRun (rawNext s x (door C)) u) k).fault=false) :
    let y := rawRun (rawNext s x (door C)) u
    Cached d hh Q y ∧ ForwardWait d C y k ∧ readPC d C y=(2,op) ∧
      tok d C y k=({tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (x C.root))}:Tok) := by
  let t : Tok := {tag:=2,opcode:=op,payload:=descriptor (params d s) (selectBytes d (x C.root))}
  obtain ⟨Y,S,_,Eq,_⟩ := ReportSealCommitLaunch.launch d C hh G F N x X I op Op P Good
  have B := before_turn_as_late d C N hh G F _ Y t
    ⟨S,ReportSealCommitLaunch.descriptor_forward _ _ op Op,.inl Eq⟩ u k R K
  exact healthy_late_origin_from_issue d C hh G F N x X I op Op P Good u k B Healthy

end L4.ReportLateIngressSplit
