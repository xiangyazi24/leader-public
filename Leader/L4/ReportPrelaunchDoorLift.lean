import Leader.L4.ReportPrelaunchK1

/-! Turn private K0 source equations into the three exact physical
door obligations. The cached gate frame is used on both pre and post. -/
namespace L4.ReportPrelaunchDoorLift
open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ShortResetCycle ReportResetBarrier
open ReportPrelaunchClock ReportPrelaunchK1Geometry ReportPrelaunchK1

variable {s n : Nat} {h : Fin n → Bool}

/-- Local test at the unique changed occurrence of this owner. -/
def RootWeak (d : Sheet) (C : Chart h) (x y : Raw s n) : Prop :=
  debtOf d C y=debtOf d C x ∧ weight d C y ⟨0,C.positive⟩≤weight d C x ⟨0,C.positive⟩

def RootPaid (d : Sheet) (C : Chart h) (x y : Raw s n) : Prop :=
  debtOf d C y<debtOf d C x ∨
  (debtOf d C y=debtOf d C x ∧ weight d C y ⟨0,C.positive⟩<weight d C x ⟨0,C.positive⟩)

/-- None of these hypotheses claims a global rank decrease. Each is
naturally supplied by the literal K0 plus phase/opcode row. -/
structure RootRows (d : Sheet) (C : Chart h) (Q : Raw s n → Prop) : Prop where
  casesAt : ∀ x,Q x→¬Launch d C x (door C)→
    RootWeak d C x (rawNext s x (door C)) ∨ RootPaid d C x (rawNext s x (door C))
  reply : ∀ x,Q x→(ReportOwnerResetDrain.tok d C x 0).tag=3→
    Launch d C x (door C) ∨ RootPaid d C x (rawNext s x (door C))
  empty : ∀ x,Q x→(ReportOwnerResetDrain.tok d C x 0).tag=0→
    Launch d C x (door C) ∨ RootPaid d C x (rawNext s x (door C))

theorem other_weights (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : ReportOwnerResetDrain.Cached d hh Q x)
    (i : Fin C.L) (I : 0<i.val) :
    weight d C (rawNext s x (door C)) i=weight d C x i := by
  have Y := (ReportOwnerResetDrain.cached_fibre d N hh Q F).closed x (door C) X
  exact weight_frame d C hh B x _ X Y i (raw_door_frame d C x i.val I i.isLt)

theorem weak_of_root (d : Sheet) (C : Chart h) (x y : Raw s n)
    (F : ∀ i : Fin C.L,0<i.val→weight d C y i=weight d C x i)
    (R : RootWeak d C x y) : Weak d C x y := by
  refine ⟨R.1,?_⟩
  intro i
  by_cases E : i.val=0
  · have Z : i=(⟨0,C.positive⟩ : Fin C.L) := Fin.ext E
    exact Z.symm ▸ R.2
  · exact Nat.le_of_eq (F i (Nat.pos_of_ne_zero E))

theorem paid_of_root (d : Sheet) (C : Chart h) (x y : Raw s n)
    (F : ∀ i : Fin C.L,0<i.val→weight d C y i=weight d C x i)
    (R : RootPaid d C x y) : Paid d C x y := by
  rcases R with H | ⟨D,W⟩
  · exact .inr ⟨H,F⟩
  · refine .inl ⟨D,.inl ⟨⟨0,C.positive⟩,?_,W⟩⟩
    intro i H
    exact F i (Nat.pos_of_ne_zero (fun E=>H (Fin.ext E)))

/-- The source lane is K0, hence its decoder does not use the ADMIT
    gate even if the old cache bits at that site are arbitrary. -/
theorem root_tok (d : Sheet) (C : Chart h) (x : Raw s n) :
    ReportOwnerResetDrain.tok d C x 0 =
      ReportByteRows.decode (params d s) false
        (ReportByteRows.resetTokenRead (params d s) (selectBytes d (x C.root)) 0) := by
  have P : C.route.port 0=0 := C.rootPort
  have E : out C 0=C.root := by
    unfold out ShortResetChart.nextAt
    simp
  rw [tok_wire]
  simp [chartGate,wire,E,P,rawGate]

theorem root_normalization (p : ReportByteRows.Params)
    (w : BitVec (ReportByteRows.tokenW p)) :
    ReportByteRows.decode p false (ReportByteRows.rankNormWire p 2 false w)
      =ReportByteRows.decode p false w := by
  rcases ReportByteRows.rank_norm_cases p false w 2 (.inl rfl) with E|⟨H,_⟩
  · exact E
  · contradiction

theorem root_weight_zero (d : Sheet) (C : Chart h) (x : Raw s n)
    (Z : (ReportOwnerResetDrain.tok d C x 0).tag=0) :
    weight d C x ⟨0,C.positive⟩=0 := by
  simp [weight,label,Z,ReportPrelaunchRank.rank]

theorem root_weight_reply (d : Sheet) (C : Chart h) (x : Raw s n)
    (D : (ReportOwnerResetDrain.tok d C x 0).tag=3) :
    weight d C x ⟨0,C.positive⟩=1 := by
  simp [weight,label,D,ReportPrelaunchRank.rank]

theorem launch_at_door_iff (d : Sheet) (C : Chart h) (x : Raw s n) :
    Launch d C x (door C) ↔ readPC d C x=(1,0) := by
  constructor
  · intro L
    exact ReportOwnerResetDrain.pc_fields d C x .issue0 (by decide) L.1
  · intro R
    refine ⟨?_,rfl⟩
    change ReportOwnerResetDrain.pcView (readPC d C x)=.issue0
    rw [R]
    decide

theorem root_tag_lt (d : Sheet) (C : Chart h) (x : Raw s n) :
    (ReportOwnerResetDrain.tok d C x 0).tag<4 := by
  rw [tok_wire]
  exact ReportByteRows.rank_tag_lt _ _ _

theorem doorCases (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) d Q) (N : 1<n)
    (R : RootRows d C (ReportOwnerResetDrain.Cached d hh Q)) :
    DoorCases d C (ReportOwnerResetDrain.Cached d hh Q) where
  casesAt := by
    intro x X H
    rcases R.casesAt x X H with W|P
    · exact .inl (weak_of_root d C x _ (other_weights d C hh B F N x X) W)
    · exact .inr (paid_of_root d C x _ (other_weights d C hh B F N x X) P)
  reply := by
    intro x X _ T
    rcases R.reply x X T with L|P
    · exact .inl L
    · exact .inr (paid_of_root d C x _ (other_weights d C hh B F N x X) P)
  empty := by
    intro x X NF ND NT
    have E : (ReportOwnerResetDrain.tok d C x 0).tag=0 := by
      have L := root_tag_lt d C x
      have A := NF 0 C.positive
      have D := ND 0 C.positive
      have T := NT 0 C.positive
      omega
    rcases R.empty x X E with L|P
    · exact .inl L
    · exact .inr (paid_of_root d C x _ (other_weights d C hh B F N x X) P)

#print axioms root_tok
#print axioms root_normalization
#print axioms launch_at_door_iff
#print axioms other_weights
#print axioms paid_of_root
#print axioms doorCases
end L4.ReportPrelaunchDoorLift
