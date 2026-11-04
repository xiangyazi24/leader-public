import Leader.Wu.Birth.ShortWait

set_option autoImplicit false

namespace BirthShortWaitDomainWitness

open PPLL PPLLRepair PPLLDomain PPLLWallSweepRepair
open BirthGenerationControlRepair BirthShortWait

/-! ## GEN tail domain: path/path2 writers plus an unchanged residual frame -/

structure GenTailFrame (psi : Nat) where
  count : Nat
  path3 : Option Path3Info
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)

namespace GenTailFrame

def ofState {psi : Nat} (u : AgentState psi) : GenTailFrame psi :=
  ⟨u.count, u.path3, u.path4, u.path5⟩

def Valid {psi : Nat} (kappa : Nat) (v : GenTailFrame psi) : Prop :=
  v.count <= kappa ∧
    PayloadView.Path3Valid psi v.path3 ∧
    PayloadView.CleanPathValid psi v.path4 ∧
    PayloadView.CleanPathValid psi v.path5

end GenTailFrame

private theorem inProtocolDomain_iff_genTail {psi kappa : Nat}
    (u : AgentState psi) :
    u.inProtocolDomain kappa ↔
      PayloadView.PathValid psi u.path ∧
      PayloadView.Path2Valid psi u.path2 ∧
      (GenTailFrame.ofState u).Valid kappa := by
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔
    _ ∧ _ ∧ (_ ∧ _ ∧ _ ∧ _)
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2.1,
      ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  · intro h
    exact ⟨h.2.2.1, h.1, h.2.1,
      h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem domain_of_genTail {psi kappa : Nat}
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hpath : PayloadView.PathValid psi output.path)
    (hpath2 : PayloadView.Path2Valid psi output.path2)
    (hframe : GenTailFrame.ofState output = GenTailFrame.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff_genTail] at hin ⊢
  exact ⟨hpath, hpath2, hframe.symm ▸ hin.2.2⟩

private theorem genStart_range_frame {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := genSigSaturatedStart hpsi l r
    (q.1.path = l.path ∧ q.1.path2 = l.path2 ∧
      GenTailFrame.ofState q.1 = GenTailFrame.ofState l) ∧
    (q.2.path = r.path ∧ q.2.path2 = r.path2 ∧
      GenTailFrame.ofState q.2 = GenTailFrame.ofState r) := by
  simp only [genSigSaturatedStart, GenTailFrame.ofState]
  repeat (first | constructor | rfl | split)

private theorem genFinish_range_frame {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := genSigSaturatedFinish hpsi l r
    (q.1.path = l.path ∧ q.1.path2 = l.path2 ∧
      GenTailFrame.ofState q.1 = GenTailFrame.ofState l) ∧
    (q.2.path = r.path ∧ q.2.path2 = r.path2 ∧
      GenTailFrame.ofState q.2 = GenTailFrame.ofState r) := by
  simp only [genSigSaturatedFinish, GenTailFrame.ofState]
  repeat (first | constructor | rfl | split)

private theorem genCleanEmit_frame {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := genCleanEmit hpsi l r
    GenTailFrame.ofState q.1 = GenTailFrame.ofState l ∧
      GenTailFrame.ofState q.2 = GenTailFrame.ofState r := by
  simp only [genCleanEmit, GenTailFrame.ofState]
  repeat (first | constructor | rfl | split)

private theorem genCleanPropagate_frame {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := genCleanPropagate hpsi l r
    GenTailFrame.ofState q.1 = GenTailFrame.ofState l ∧
      GenTailFrame.ofState q.2 = GenTailFrame.ofState r := by
  simp only [genCleanPropagate, GenTailFrame.ofState]
  repeat (first | constructor | rfl | split)

private theorem genCleanEmit_path_path2 {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi)
    (hlp : PayloadView.PathValid psi l.path)
    (hl2 : PayloadView.Path2Valid psi l.path2)
    (hrp : PayloadView.PathValid psi r.path)
    (hr2 : PayloadView.Path2Valid psi r.path2) :
    let q := genCleanEmit hpsi l r
    (PayloadView.PathValid psi q.1.path ∧
      PayloadView.Path2Valid psi q.1.path2) ∧
    (PayloadView.PathValid psi q.2.path ∧
      PayloadView.Path2Valid psi q.2.path2) := by
  simp only [genCleanEmit]
  constructor
  · exact ⟨hlp, hl2⟩
  · split
    · constructor
      · change r.label.val < psi ∧ (if r.bit then 1 else 0) <= 1
        exact ⟨r.label.isLt, by cases r.bit <;> decide⟩
      · trivial
    · exact ⟨hrp, hr2⟩

private theorem genCleanPropagate_path_path2 {psi : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hlp : PayloadView.PathValid psi l.path)
    (hl2 : PayloadView.Path2Valid psi l.path2)
    (hrp : PayloadView.PathValid psi r.path)
    (hr2 : PayloadView.Path2Valid psi r.path2) :
    let q := genCleanPropagate hpsi l r
    (PayloadView.PathValid psi q.1.path ∧
      PayloadView.Path2Valid psi q.1.path2) ∧
    (PayloadView.PathValid psi q.2.path ∧
      PayloadView.Path2Valid psi q.2.path2) := by
  simp only [genCleanPropagate]
  split
  · constructor
    · constructor
      · change l.label.val < psi ∧ (if l.bit then 1 else 0) <= 1
        exact ⟨l.label.isLt, by cases l.bit <;> decide⟩
      · trivial
    · exact ⟨hrp, hr2⟩
  · exact ⟨⟨hlp, hl2⟩, ⟨hrp, hr2⟩⟩

private theorem genStart_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genSigSaturatedStart hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hf := genStart_range_frame hpsi l r
  have hld := (inProtocolDomain_iff_genTail l).1 hl
  have hrd := (inProtocolDomain_iff_genTail r).1 hr
  exact ⟨
    domain_of_genTail l _ hl
      (hf.1.1.symm ▸ hld.1)
      (hf.1.2.1.symm ▸ hld.2.1) hf.1.2.2,
    domain_of_genTail r _ hr
      (hf.2.1.symm ▸ hrd.1)
      (hf.2.2.1.symm ▸ hrd.2.1) hf.2.2.2⟩

private theorem genFinish_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genSigSaturatedFinish hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hf := genFinish_range_frame hpsi l r
  have hld := (inProtocolDomain_iff_genTail l).1 hl
  have hrd := (inProtocolDomain_iff_genTail r).1 hr
  exact ⟨
    domain_of_genTail l _ hl
      (hf.1.1.symm ▸ hld.1)
      (hf.1.2.1.symm ▸ hld.2.1) hf.1.2.2,
    domain_of_genTail r _ hr
      (hf.2.1.symm ▸ hrd.1)
      (hf.2.2.1.symm ▸ hrd.2.1) hf.2.2.2⟩

private theorem genEmit_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genCleanEmit hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hld := (inProtocolDomain_iff_genTail l).1 hl
  have hrd := (inProtocolDomain_iff_genTail r).1 hr
  have hp := genCleanEmit_path_path2 hpsi l r
    hld.1 hld.2.1 hrd.1 hrd.2.1
  have hf := genCleanEmit_frame hpsi l r
  exact ⟨domain_of_genTail l _ hl hp.1.1 hp.1.2 hf.1,
    domain_of_genTail r _ hr hp.2.1 hp.2.2 hf.2⟩

private theorem genPropagate_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genCleanPropagate hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hld := (inProtocolDomain_iff_genTail l).1 hl
  have hrd := (inProtocolDomain_iff_genTail r).1 hr
  have hp := genCleanPropagate_path_path2 hpsi l r
    hld.1 hld.2.1 hrd.1 hrd.2.1
  have hf := genCleanPropagate_frame hpsi l r
  exact ⟨domain_of_genTail l _ hl hp.1.1 hp.1.2 hf.1,
    domain_of_genTail r _ hr hp.2.1 hp.2.2 hf.2⟩

/-- The unchanged full-psi GEN tail preserves the declared finite domain
starting from any already-domain-closed WAIT output. -/
theorem genCleanAfterWait_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genCleanAfterWait hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let q0 := genSigSaturatedStart hpsi l r
  have h0 := genStart_inProtocolDomain hpsi l r hl hr
  let q1 := genCleanEmit hpsi q0.1 q0.2
  have h1 := genEmit_inProtocolDomain hpsi q0.1 q0.2 h0.1 h0.2
  let q2 := genCleanPropagate hpsi q1.1 q1.2
  have h2 := genPropagate_inProtocolDomain hpsi q1.1 q1.2 h1.1 h1.2
  exact genFinish_inProtocolDomain hpsi q2.1 q2.2 h2.1 h2.2

/-- Missing full-domain law for the shortened-WAIT generation row. -/
theorem genCleanWidth_inProtocolDomain {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := genCleanWidth hpsi hwidth hle kappa l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let w := waitWidth hpsi hwidth hle kappa l r
  have hw := waitWidth_inProtocolDomain hpsi hwidth hle l r hl hr
  exact genCleanAfterWait_inProtocolDomain hpsi w.1 w.2 hw.1 hw.2

/-! ## SUPPRESS domain -/

private theorem domain_of_count_payload_eq {psi kappa : Nat}
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hc : output.count = input.count)
    (hp : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hc ▸ hin.1, hp ▸ hin.2⟩

private theorem domain_of_count_payload_bound {psi kappa : Nat}
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hc : output.count <= kappa)
    (hp : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hc, hp ▸ hin.2⟩

private theorem suppressStart_frame {psi : Nat} (l r : AgentState psi) :
    let q := suppressSigStart l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigStart]
  repeat (first | constructor | rfl | split)

private theorem suppressMove_frame {psi : Nat} (l r : AgentState psi) :
    let q := suppressSigMoveReset l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigMoveReset]
  repeat (first | constructor | rfl | split)

private theorem suppressTerminal_frame {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := suppressSigTerminal hpsi l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      ((q.2.count = r.count ∨ q.2.count = 0) ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigTerminal]
  split
  · exact ⟨⟨rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩⟩
  · exact ⟨⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩⟩

private theorem suppressEcho_frame {psi : Nat} (l r : AgentState psi) :
    let q := suppressSigEcho l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigEcho]
  repeat (first | constructor | rfl | split)

private theorem suppressFinish_frame {psi : Nat} (l r : AgentState psi) :
    let q := suppressSigFinish l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigFinish]
  repeat (first | constructor | rfl | split)

private theorem suppressStart_inProtocolDomain {psi kappa : Nat}
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigStart l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have h := suppressStart_frame l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressMove_inProtocolDomain {psi kappa : Nat}
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigMoveReset l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have h := suppressMove_frame l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressTerminal_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := suppressSigTerminal hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have h := suppressTerminal_frame hpsi l r
  constructor
  · exact domain_of_count_payload_eq l _ hl h.1.1 h.1.2
  · have hc : (suppressSigTerminal hpsi l r).2.count <= kappa := by
      rcases h.2.1 with heq | hzero
      · exact heq ▸ hr.1
      · rw [hzero]
        exact Nat.zero_le _
    exact domain_of_count_payload_bound r _ hr hc h.2.2

private theorem suppressEcho_inProtocolDomain {psi kappa : Nat}
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigEcho l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have h := suppressEcho_frame l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressFinish_inProtocolDomain {psi kappa : Nat}
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigFinish l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have h := suppressFinish_frame l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressPrefix_inProtocolDomain {psi kappa : Nat}
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressPrefix l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let q0 := suppressSigStart l r
  have h0 := suppressStart_inProtocolDomain l r hl hr
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  have h0k : q0k.1.inProtocolDomain kappa ∧ q0k.2.inProtocolDomain kappa :=
    ⟨resetKillComparison_inProtocolDomain q0.1 h0.1,
      resetKillComparison_inProtocolDomain q0.2 h0.2⟩
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  have h1 := suppressMove_inProtocolDomain q0k.1 q0k.2 h0k.1 h0k.2
  let q1k := (resetKillComparison q1.1, resetKillComparison q1.2)
  have h1k : q1k.1.inProtocolDomain kappa ∧ q1k.2.inProtocolDomain kappa :=
    ⟨resetKillComparison_inProtocolDomain q1.1 h1.1,
      resetKillComparison_inProtocolDomain q1.2 h1.2⟩
  simpa only [suppressPrefix, q0, q0k, q1, q1k] using h1k

/-- Missing full-domain law for shortened SUPPRESS.  The inserted write is only
`count := 0`; the physical full-terminal echo stage remains the published one. -/
theorem suppressSigResetKillWidth_inProtocolDomain {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := suppressSigResetKillWidth hpsi hwidth hle l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let p := suppressPrefix l r
  have hp := suppressPrefix_inProtocolDomain l r hl hr
  let s := shortCountReset hwidth hle p.1 p.2
  have hs := shortCountReset_inProtocolDomain hwidth hle
    p.1 p.2 hp.1 hp.2
  let t := suppressSigTerminal hpsi s.1 s.2
  have ht := suppressTerminal_inProtocolDomain hpsi s.1 s.2 hs.1 hs.2
  let e := suppressSigEcho t.1 t.2
  have he := suppressEcho_inProtocolDomain t.1 t.2 ht.1 ht.2
  exact suppressFinish_inProtocolDomain e.1 e.2 he.1 he.2

/-! ## Literal psi=4 / width=2 / kappa=4 witnesses -/

private def witnessBase {psi : Nat} (i : Fin psi) : AgentState psi where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := i
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

structure WaitRegs where
  h_field : Bool
  carry : Bool
  reset : Bool
  count : Nat
  deriving DecidableEq, Repr

def WaitRegs.ofState {psi : Nat} (u : AgentState psi) : WaitRegs :=
  ⟨u.h_field, u.carry, u.reset, u.count⟩

def waitRegsPair {psi : Nat} (q : AgentState psi × AgentState psi) :
    WaitRegs × WaitRegs :=
  (WaitRegs.ofState q.1, WaitRegs.ofState q.2)

def carryLeft4 : AgentState 4 :=
  { witnessBase (0 : Fin 4) with carry := true }

def carryRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with h_field := true, count := 3 }

/-- Width-two terminal carry increments at physical label one, not label three. -/
theorem carry_width2_terminal4 :
    waitWidthCarry (psi := 4) (width := 2)
      (by decide) (by decide) 4 carryLeft4 carryRight4 =
      ({ carryLeft4 with carry := false },
       { carryRight4 with h_field := false, count := 4 }) := by
  decide

def resetLeft4 : AgentState 4 :=
  { witnessBase (0 : Fin 4) with reset := true }

def resetRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with h_field := true }

/-- Width-two reset stops propagation at physical label one. -/
theorem reset_width2_terminal4 :
    waitWidthReset (psi := 4) (width := 2)
      (by decide) (by decide) resetLeft4 resetRight4 =
      ({ resetLeft4 with reset := false },
       { resetRight4 with h_field := false }) := by
  decide

def finishBoundaryLeft4 : AgentState 4 :=
  { witnessBase (3 : Fin 4) with wait := true }

def finishBoundaryRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with wait := true, count := 4 }

/-- The shortened cap is label one, but WAIT movement still tests the real
full-psi left boundary label three. -/
theorem finish_keeps_full_psi_boundary4 :
    waitWidthFinish (psi := 4) (width := 2)
      (by decide) (by decide) (by decide) 4
      finishBoundaryLeft4 finishBoundaryRight4 =
      (finishBoundaryLeft4, { finishBoundaryRight4 with wait := false }) := by
  decide

def shortResetLeft4 : AgentState 4 := witnessBase (0 : Fin 4)

def shortResetRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with reset_cmd := true, count := 4 }

/-- Literal inserted SUPPRESS cut: width-two terminal count is reset. -/
theorem shortCountReset_width2_terminal4 :
    shortCountReset (psi := 4) (width := 2)
      (by decide) (by decide) shortResetLeft4 shortResetRight4 =
      (shortResetLeft4, { shortResetRight4 with count := 0 }) := by
  decide

def movingSuppressLeft4 : AgentState 4 :=
  { witnessBase (0 : Fin 4) with reset_cmd := true }

def movingSuppressRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with count := 4 }

/-- The real repaired prefix moves reset_cmd to label one, the inserted cut
zeros count there, and the unchanged physical terminal/echo suffix remains live. -/
theorem suppress_width2_moving_reset4 :
    suppressSigResetKillWidth (psi := 4) (width := 2)
      (by decide) (by decide) (by decide)
      movingSuppressLeft4 movingSuppressRight4 =
      ({ movingSuppressLeft4 with reset_cmd := false },
       { movingSuppressRight4 with reset_cmd := true, count := 0 }) := by
  decide

def genQuietLeft4 : AgentState 4 :=
  { witnessBase (0 : Fin 4) with wait := true }

def genQuietRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with wait := true }

/-- Full-psi GEN writers are unchanged: on this quiet row only the published
WAIT prepare toggles the root h_field. -/
theorem genCleanWidth_quiet4 :
    genCleanWidth (psi := 4) (width := 2)
      (by decide) (by decide) (by decide) 4 genQuietLeft4 genQuietRight4 =
      ({ genQuietLeft4 with h_field := true }, genQuietRight4) := by
  decide

def waitRowLeft4 : AgentState 4 :=
  { witnessBase (0 : Fin 4) with wait := true, h_field := true, reset := true }

def waitRowRight4 : AgentState 4 :=
  { witnessBase (1 : Fin 4) with wait := true, h_field := true, count := 3 }

/-- Actual shortened internal WAIT four-register row. -/
theorem waitWidth_regs_row4 :
    waitRegsPair
      (waitWidth (psi := 4) (width := 2)
        (by decide) (by decide) (by decide) 4 waitRowLeft4 waitRowRight4) =
      (⟨false, false, false, 0⟩, ⟨false, false, false, 4⟩) := by
  decide

def waitRowLeft2 : AgentState 2 :=
  { witnessBase (0 : Fin 2) with wait := true, h_field := true, reset := true }

def waitRowRight2 : AgentState 2 :=
  { witnessBase (1 : Fin 2) with wait := true, h_field := true, count := 3 }

/-- Concrete width-sized correspondence: the four internal registers agree
with the published waitSaturated run at psi=2.  This does not identify the
`wait` field or alter the full-psi movement guard in waitWidth. -/
theorem waitWidth_regs_matches_waitSaturated_width2 :
    waitRegsPair
      (waitWidth (psi := 4) (width := 2)
        (by decide) (by decide) (by decide) 4 waitRowLeft4 waitRowRight4) =
    waitRegsPair
      (waitSaturated (ψ := 2) (by decide) 4 waitRowLeft2 waitRowRight2) := by
  decide

end BirthShortWaitDomainWitness
