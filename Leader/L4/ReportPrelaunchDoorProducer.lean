import Leader.L4.ReportOwnerDoorProjection
import Leader.L4.ReportPrelaunchDoorLift

namespace L4.ReportPrelaunchDoorProducer
open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ShortResetCycle ShortResetChart ReportResetBarrier
open ReportByteRows ReportRawProjection ReportPrelaunchClock ReportPrelaunchRank
open ReportOwnerDoorProjection ReportPrelaunchDoorLift

variable {s n : Nat} {h : Fin n→Bool}

private theorem properNext {t a b : Nat} (E : PreviewNextOp t a b) :
    NextOp t a b := by
  cases E with
  | linear H => exact .linear H
  | cmpLast H => exact .cmpLast H
  | readWrite H => exact .readWrite H
  | writeRead H => exact .writeRead H
  | writeSeal H => exact .writeSeal H
  | sealCommit => exact .sealCommit

private theorem root_tok (sheet : Sheet) (C : Chart h) (x : Raw s n) :
    ReportOwnerResetDrain.tok sheet C x 0 =
      publicationToken (params sheet s) true (selectBytes sheet (x C.root)) 0 := by
  change publicationToken (params sheet s) (h C.root) (selectBytes sheet (x C.root))
    (ShortResetChart.lane C.a C.b 0)=_
  rw [C.rootHeader,C.rootPort]

private theorem same_weight (d : Sheet) (C : Chart h) (x y : Raw s n)
    (E : (ReportOwnerResetDrain.tok d C y 0).tag=(ReportOwnerResetDrain.tok d C x 0).tag) :
    weight d C y ⟨0,C.positive⟩=weight d C x ⟨0,C.positive⟩ := by
  unfold weight label
  dsimp only
  rw [E]
  by_cases H : (ReportOwnerResetDrain.tok d C x 0).tag=2
  · simp [H,rank,extra]
  · simp only [if_neg H]

/-- Every non-launch door mark either strictly pays source debt or
holds a live T/F root. The latter uses the exact normalized K0 wire. -/
theorem local_cases (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (digit : 0<(params d s).digits)
    (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (NL : ¬Launch d C x (door C)) :
    let y := rawNext s x (door C)
    debtOf d C y<debtOf d C x ∨
      (debtOf d C y=debtOf d C x ∧
       (ReportOwnerResetDrain.tok d C y 0).tag=(ReportOwnerResetDrain.tok d C x 0).tag ∧
       ((ReportOwnerResetDrain.tok d C x 0).tag=1 ∨ (ReportOwnerResetDrain.tok d C x 0).tag=2)) := by
  let y := rawNext s x (door C)
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  let P := sourcePhase p v
  let O := sourceOpcode p v
  have VN : ¬(P=1 ∧ O=0) := by
    intro E
    apply NL
    exact (launch_at_door_iff d C x).mpr (Prod.ext E.1 E.2)
  have W := raw_door_final d C x N mask
  change controlWork p (selectBytes d (y C.root)) =
    controlWork p ((liftSourcePatch p (source p v t).1).apply v) ∧
    resetTokenRead p (selectBytes d (y C.root)) 0 =
      (match (source p v t).2 with
      | none => prelaunchDoorNormWire p v
      | some q => resetTokenWire p q) at W
  have debt_y (ph op : Nat) (E : controlWork p ((liftSourcePatch p (source p v t).1).apply v)=(ph,op)) :
      debtOf d C y=pcDebt p.digits ph op := by
    have A := W.1.trans E
    change controlWork p (selectBytes d (y C.root)) = (ph,op) at A
    unfold debtOf readPC
    rw [A]
  have debt_x : debtOf d C x=pcDebt p.digits P O := rfl
  have pay_restart (R : controlWork p ((liftSourcePatch p (source p v t).1).apply v)=(1,0)) :
      debtOf d C y<debtOf d C x := by
    rw [debt_y 1 0 R,debt_x]
    exact pc_debt_restart VN
  change debtOf d C y<debtOf d C x ∨ _
  by_cases bad : P=0 ∨ P=3 ∨ commitOp p<O
  · have R := prelaunch_invalid_source p v t bad
    exact .inl (pay_restart (by rw [R]; exact prelaunch_restart_controls p v))
  have phase : P=1 ∨ P=2 := by
    have A : P<4 := prelaunch_phase_bound p v
    omega
  have op : O≤commitOp p := by omega
  rcases phase with Ph|Ph
  · have pos : 0<O := by omega
    rcases prelaunch_positive_issue_controls p v t Ph op pos with Reset|Issued
    · exact .inl (pay_restart Reset)
    · left
      rw [debt_y 2 O Issued,debt_x,Ph]
      exact pc_debt_issue pos (by unfold commitOp at op; omega)
  · by_cases Hold : t.tag=1 ∨ t.tag=2
    · right
      have R := prelaunch_wait_hold p v t Ph op Hold
      have controls := prelaunch_hold_controls p v t Ph op Hold
      refine ⟨(debt_y P O controls).trans debt_x.symm,?_,?_⟩
      · have Wire := W.2
        rw [R] at Wire
        rw [root_tok,root_tok,prelaunch_root_decode p (selectBytes d (y C.root)),Wire]
        exact prelaunch_door_norm_tag p v
      · simpa only [root_tok d C x] using Hold
    · rcases prelaunch_wait_controls p v t Ph op (fun E=>Hold (.inl E))
        (fun E=>Hold (.inr E)) digit with Reset|⟨b,B,Next⟩
      · exact .inl (pay_restart Reset)
      · left
        rw [debt_y 1 b Next,debt_x,Ph]
        exact nextOp_pays (properNext B)

theorem rootRows (d : Sheet) (C : Chart h) (Q : Raw s n→Prop) (N : 1<n)
    (digit : 0<(params d s).digits)
    (mask : ∀ x,Q x→∀ i,lower d (oldHeaders (rows s) (x i))=h i) :
    RootRows d C Q where
  casesAt := by
    intro x X H
    rcases local_cases d C x N digit (mask x X) H with P|⟨D,E,_⟩
    · exact .inr (.inl P)
    · exact .inl ⟨D,Nat.le_of_eq (same_weight d C x _ E)⟩
  reply := by
    intro x X T
    by_cases L : Launch d C x (door C)
    · exact .inl L
    · rcases local_cases d C x N digit (mask x X) L with P|⟨_,_,H⟩
      · exact .inr (.inl P)
      · rw [T] at H
        omega
  empty := by
    intro x X T
    by_cases L : Launch d C x (door C)
    · exact .inl L
    · rcases local_cases d C x N digit (mask x X) L with P|⟨_,_,H⟩
      · exact .inr (.inl P)
      · rw [T] at H
        omega

/-- Both production reports carry at least one digit. -/
theorem digits_positive (d : Sheet) (S : 0<s) : 0<(params d s).digits := by
  cases d with
  | first => exact Nat.zero_lt_one
  | second =>
    change 0<ell (radiusTwo s+1)
    have H : 0<radiusTwo s := by
      unfold radiusTwo
      apply Nat.div_pos _ S
      have T : 0<2^s := Nat.two_pow_pos _
      omega
    apply Nat.pos_of_ne_zero
    intro E
    have T := (ell_le_iff (radiusTwo s+1) 0).mp (Nat.le_of_eq E)
    simp only [Nat.pow_zero] at T
    omega

/-- All three actual door obligations on the closed cached fibre. -/
theorem doorCases_cached (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : ReportPrelaunchK1Geometry.GapInput h) (Q : Raw s n→Prop)
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q) (N : 1<n) (S : 0<s) :
    ReportPrelaunchK1.DoorCases d C (ReportOwnerResetDrain.Cached d hh Q) :=
  doorCases d C hh B F N
    (rootRows d C _ N (digits_positive d S)
      (ReportOwnerResetDrain.cached_fibre d N hh Q F).mask)

/-- Complete local rows for both reports, including source and
non-door transit. This still assumes chart, cached fibre and spacing;
it does not assert Good8 or the all-owner cover terminal invariant. -/
theorem rowCases_cached (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : ReportPrelaunchK1Geometry.GapInput h) (Q : Raw s n→Prop)
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q) (N : 1<n) (S : 0<s) :
    RowCases d C (ReportOwnerResetDrain.Cached d hh Q) :=
  ReportPrelaunchK1.rowCases d C hh B Q F N (doorCases_cached d C hh B Q F N S)

#print axioms doorCases_cached
#print axioms rowCases_cached
#print axioms local_cases
#print axioms rootRows
end L4.ReportPrelaunchDoorProducer
