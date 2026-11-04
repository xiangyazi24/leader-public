import Leader.Wu.Protocol.Repairs

/-!
# Value-range closure of the explicit repaired transition

This module proves that the separately named repaired audit transition stays
inside the numeric domains represented by `BoundedAgentState`.  These are only
field-range theorems; they do not assert signal provenance, safe closedness, or
convergence.
-/

namespace PPLLDomain

open PPLL PPLLRepair

/-- The six raw payload fields constrained by `AgentState.inProtocolDomain`. -/
structure PayloadView (ψ : Nat) where
  path : PathInfo
  path2 : Option Path2Info
  path3 : Option Path3Info
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  deriving DecidableEq, Repr

namespace PayloadView

def ofState {ψ : Nat} (s : AgentState ψ) : PayloadView ψ :=
  ⟨s.path, s.path2, s.path3, s.path4, s.path5⟩

def PathValid (ψ : Nat) : PathInfo → Prop
  | .bot => True
  | .some label bit => label < ψ ∧ bit ≤ 1

def Path2Valid (ψ : Nat) : Option Path2Info → Prop
  | none => True
  | some p => p.label < ψ ∧ p.bit ≤ 1 ∧ p.position ≤ ψ ∧
      1 ≤ p.action ∧ p.action ≤ 6

def Path3Valid (ψ : Nat) : Option Path3Info → Prop
  | none => True
  | some p => p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1

def CleanPathValid (ψ : Nat) : Option (Int × Nat) → Prop
  | none => True
  | some (label, bit) => (-1 : Int) ≤ label ∧
      label < Int.ofNat ψ ∧ bit ≤ 1

def Valid {ψ : Nat} (v : PayloadView ψ) : Prop :=
  PathValid ψ v.path ∧ Path2Valid ψ v.path2 ∧
    Path3Valid ψ v.path3 ∧ CleanPathValid ψ v.path4 ∧
    CleanPathValid ψ v.path5

end PayloadView

/-- Domain-constrained fields other than `path`; useful for algorithms that
create a fresh path while leaving every other bounded payload unchanged. -/
structure FrameView (ψ : Nat) where
  count : Nat
  path2 : Option Path2Info
  path3 : Option Path3Info
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  deriving DecidableEq, Repr

namespace FrameView

def ofState {ψ : Nat} (s : AgentState ψ) : FrameView ψ :=
  ⟨s.count, s.path2, s.path3, s.path4, s.path5⟩

def Valid {ψ : Nat} (κ : Nat) (v : FrameView ψ) : Prop :=
  v.count ≤ κ ∧ PayloadView.Path2Valid ψ v.path2 ∧
    PayloadView.Path3Valid ψ v.path3 ∧
    PayloadView.CleanPathValid ψ v.path4 ∧
    PayloadView.CleanPathValid ψ v.path5

end FrameView

/-- Domain-constrained fields other than `path2`. -/
structure Path2FrameView (ψ : Nat) where
  count : Nat
  path : PathInfo
  path3 : Option Path3Info
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  deriving DecidableEq, Repr

namespace Path2FrameView

def ofState {ψ : Nat} (s : AgentState ψ) : Path2FrameView ψ :=
  ⟨s.count, s.path, s.path3, s.path4, s.path5⟩

def Valid {ψ : Nat} (κ : Nat) (v : Path2FrameView ψ) : Prop :=
  v.count ≤ κ ∧ PayloadView.PathValid ψ v.path ∧
    PayloadView.Path3Valid ψ v.path3 ∧
    PayloadView.CleanPathValid ψ v.path4 ∧
    PayloadView.CleanPathValid ψ v.path5

end Path2FrameView

/-- Domain-constrained fields other than `path3`. -/
structure Path3FrameView (ψ : Nat) where
  count : Nat
  path : PathInfo
  path2 : Option Path2Info
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  deriving DecidableEq, Repr

namespace Path3FrameView

def ofState {ψ : Nat} (s : AgentState ψ) : Path3FrameView ψ :=
  ⟨s.count, s.path, s.path2, s.path4, s.path5⟩

def Valid {ψ : Nat} (κ : Nat) (v : Path3FrameView ψ) : Prop :=
  v.count ≤ κ ∧ PayloadView.PathValid ψ v.path ∧
    PayloadView.Path2Valid ψ v.path2 ∧
    PayloadView.CleanPathValid ψ v.path4 ∧
    PayloadView.CleanPathValid ψ v.path5

end Path3FrameView

/-- The existing domain predicate is exactly a counter bound plus payload
validity. -/
theorem inProtocolDomain_iff {ψ κ : Nat} (s : AgentState ψ) :
    s.inProtocolDomain κ ↔
      s.count ≤ κ ∧ (PayloadView.ofState s).Valid := by
  rfl

/-- Equivalent decomposition with the path bound separated from all other
numeric fields. -/
theorem inProtocolDomain_iff_path_frame {ψ κ : Nat} (s : AgentState ψ) :
    s.inProtocolDomain κ ↔
      PayloadView.PathValid ψ s.path ∧
        (FrameView.ofState s).Valid κ := by
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔
    _ ∧ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  constructor
  · intro h
    exact ⟨h.2.1, ⟨h.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  · intro h
    exact ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Equivalent decomposition with the path2 bound separated. -/
theorem inProtocolDomain_iff_path2_frame {ψ κ : Nat} (s : AgentState ψ) :
    s.inProtocolDomain κ ↔
      PayloadView.Path2Valid ψ s.path2 ∧
        (Path2FrameView.ofState s).Valid κ := by
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔
    _ ∧ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  constructor
  · intro h
    exact ⟨h.2.2.1, ⟨h.1, h.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  · intro h
    exact ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Equivalent decomposition with the path3 bound separated. -/
theorem inProtocolDomain_iff_path3_frame {ψ κ : Nat} (s : AgentState ψ) :
    s.inProtocolDomain κ ↔
      PayloadView.Path3Valid ψ s.path3 ∧
        (Path3FrameView.ofState s).Valid κ := by
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔
    _ ∧ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  constructor
  · intro h
    exact ⟨h.2.2.2.1, ⟨h.1, h.2.1, h.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  · intro h
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem domain_of_count_payload {ψ κ : Nat} (s : AgentState ψ)
    (hc : s.count ≤ κ) (hp : (PayloadView.ofState s).Valid) :
    s.inProtocolDomain κ :=
  (inProtocolDomain_iff s).2 ⟨hc, hp⟩

/-- Algorithm 2 changes no domain-constrained field. -/
theorem pPsi_count_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := pPsi hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
    (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [pPsi]
  repeat (first | constructor | rfl | split)

theorem pPsi_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := pPsi hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := pPsi hψ l r
  have hv := pPsi_count_payload hψ l r
  change q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  change (q.1.count ≤ κ ∧ (PayloadView.ofState q.1).Valid) ∧
    (q.2.count ≤ κ ∧ (PayloadView.ofState q.2).Valid)
  change (l.count ≤ κ ∧ (PayloadView.ofState l).Valid) at hl
  change (r.count ≤ κ ∧ (PayloadView.ofState r).Valid) at hr
  exact ⟨⟨hv.1.1 ▸ hl.1, hv.1.2 ▸ hl.2⟩,
    ⟨hv.2.1 ▸ hr.1, hv.2.2 ▸ hr.2⟩⟩

private theorem waitSaturatedPrepare_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := waitSaturatedPrepare hψ l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  simp only [waitSaturatedPrepare]
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedCarry_payload {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := waitSaturatedCarry hψ κ l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  simp only [waitSaturatedCarry]
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedReset_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := waitSaturatedReset hψ l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  simp only [waitSaturatedReset]
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedFinish_payload {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := waitSaturatedFinish hψ κ l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  simp only [waitSaturatedFinish]
  repeat (first | constructor | rfl | split)

/-- Saturating WAIT changes only the counter among domain-constrained fields. -/
theorem waitSaturated_payload {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := waitSaturated hψ κ l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  let q0 := waitSaturatedPrepare hψ l r
  let q1 := waitSaturatedCarry hψ κ q0.1 q0.2
  let q2 := waitSaturatedReset hψ q1.1 q1.2
  let q3 := waitSaturatedFinish hψ κ q2.1 q2.2
  have h0 := waitSaturatedPrepare_payload hψ l r
  have h1 := waitSaturatedCarry_payload (κ := κ) hψ q0.1 q0.2
  have h2 := waitSaturatedReset_payload hψ q1.1 q1.2
  have h3 := waitSaturatedFinish_payload (κ := κ) hψ q2.1 q2.2
  change PayloadView.ofState q3.1 = PayloadView.ofState l ∧
    PayloadView.ofState q3.2 = PayloadView.ofState r
  constructor
  · exact h3.1.trans (h2.1.trans (h1.1.trans h0.1))
  · exact h3.2.trans (h2.2.trans (h1.2.trans h0.2))

theorem waitSaturated_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := waitSaturated hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := waitSaturated hψ κ l r
  have hc := waitSaturated_count_closed hψ l r hl.1 hr.1
  have hp := waitSaturated_payload (κ := κ) hψ l r
  change q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  change (q.1.count ≤ κ ∧ (PayloadView.ofState q.1).Valid) ∧
    (q.2.count ≤ κ ∧ (PayloadView.ofState q.2).Valid)
  change (_ ∧ (PayloadView.ofState l).Valid) at hl
  change (_ ∧ (PayloadView.ofState r).Valid) at hr
  exact ⟨⟨hc.1, hp.1 ▸ hl.2⟩, ⟨hc.2, hp.2 ▸ hr.2⟩⟩

private theorem domain_of_path_frame_eq {ψ κ : Nat}
    (input output : AgentState ψ) (hin : input.inProtocolDomain κ)
    (hpath : PayloadView.PathValid ψ output.path)
    (hframe : FrameView.ofState output = FrameView.ofState input) :
    output.inProtocolDomain κ := by
  rw [inProtocolDomain_iff_path_frame] at hin ⊢
  exact ⟨hpath, hframe ▸ hin.2⟩

private theorem genSigSaturatedStart_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := genSigSaturatedStart hψ l r
    FrameView.ofState q.1 = FrameView.ofState l ∧
      FrameView.ofState q.2 = FrameView.ofState r := by
  simp only [genSigSaturatedStart]
  repeat (first | constructor | rfl | split)

private theorem genSigSaturatedStart_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : PayloadView.PathValid ψ l.path)
    (hr : PayloadView.PathValid ψ r.path) :
    let q := genSigSaturatedStart hψ l r
    PayloadView.PathValid ψ q.1.path ∧
      PayloadView.PathValid ψ q.2.path := by
  simp only [genSigSaturatedStart]
  repeat (first | constructor | exact hl | exact hr | split)

private theorem genSigSaturatedEmit_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := genSigSaturatedEmit hψ l r
    FrameView.ofState q.1 = FrameView.ofState l ∧
      FrameView.ofState q.2 = FrameView.ofState r := by
  simp only [genSigSaturatedEmit]
  repeat (first | constructor | rfl | split)

private theorem genSigSaturatedEmit_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : PayloadView.PathValid ψ l.path)
    (hr : PayloadView.PathValid ψ r.path) :
    let q := genSigSaturatedEmit hψ l r
    PayloadView.PathValid ψ q.1.path ∧
      PayloadView.PathValid ψ q.2.path := by
  simp only [genSigSaturatedEmit]
  constructor
  · exact hl
  · split
    · simp only [PayloadView.PathValid]
      exact ⟨r.label.isLt, by split <;> omega⟩
    · exact hr

private theorem genSigSaturatedPropagate_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := genSigSaturatedPropagate hψ l r
    FrameView.ofState q.1 = FrameView.ofState l ∧
      FrameView.ofState q.2 = FrameView.ofState r := by
  simp only [genSigSaturatedPropagate]
  repeat (first | constructor | rfl | split)

private theorem genSigSaturatedPropagate_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : PayloadView.PathValid ψ l.path)
    (hr : PayloadView.PathValid ψ r.path) :
    let q := genSigSaturatedPropagate hψ l r
    PayloadView.PathValid ψ q.1.path ∧
      PayloadView.PathValid ψ q.2.path := by
  simp only [genSigSaturatedPropagate]
  split
  · constructor
    · simp only [PayloadView.PathValid]
      exact ⟨l.label.isLt, by split <;> omega⟩
    · exact hr
  · exact ⟨hl, hr⟩

private theorem genSigSaturatedFinish_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := genSigSaturatedFinish hψ l r
    FrameView.ofState q.1 = FrameView.ofState l ∧
      FrameView.ofState q.2 = FrameView.ofState r := by
  simp only [genSigSaturatedFinish]
  repeat (first | constructor | rfl | split)

private theorem genSigSaturatedFinish_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : PayloadView.PathValid ψ l.path)
    (hr : PayloadView.PathValid ψ r.path) :
    let q := genSigSaturatedFinish hψ l r
    PayloadView.PathValid ψ q.1.path ∧
      PayloadView.PathValid ψ q.2.path := by
  simp only [genSigSaturatedFinish]
  repeat (first | constructor | exact hl | exact hr | split)

private theorem genSigStart_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := genSigSaturatedStart hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := genSigSaturatedStart_frame hψ l r
  have hp := genSigSaturatedStart_path hψ l r
    ((inProtocolDomain_iff_path_frame l).1 hl).1
    ((inProtocolDomain_iff_path_frame r).1 hr).1
  exact ⟨domain_of_path_frame_eq l _ hl hp.1 hf.1,
    domain_of_path_frame_eq r _ hr hp.2 hf.2⟩

private theorem genSigEmit_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := genSigSaturatedEmit hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := genSigSaturatedEmit_frame hψ l r
  have hp := genSigSaturatedEmit_path hψ l r
    ((inProtocolDomain_iff_path_frame l).1 hl).1
    ((inProtocolDomain_iff_path_frame r).1 hr).1
  exact ⟨domain_of_path_frame_eq l _ hl hp.1 hf.1,
    domain_of_path_frame_eq r _ hr hp.2 hf.2⟩

private theorem genSigPropagate_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := genSigSaturatedPropagate hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := genSigSaturatedPropagate_frame hψ l r
  have hp := genSigSaturatedPropagate_path hψ l r
    ((inProtocolDomain_iff_path_frame l).1 hl).1
    ((inProtocolDomain_iff_path_frame r).1 hr).1
  exact ⟨domain_of_path_frame_eq l _ hl hp.1 hf.1,
    domain_of_path_frame_eq r _ hr hp.2 hf.2⟩

private theorem genSigFinish_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := genSigSaturatedFinish hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := genSigSaturatedFinish_frame hψ l r
  have hp := genSigSaturatedFinish_path hψ l r
    ((inProtocolDomain_iff_path_frame l).1 hl).1
    ((inProtocolDomain_iff_path_frame r).1 hr).1
  exact ⟨domain_of_path_frame_eq l _ hl hp.1 hf.1,
    domain_of_path_frame_eq r _ hr hp.2 hf.2⟩

/-- Saturating Algorithm 4 preserves every declared numeric value range. -/
theorem genSigSaturated_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := genSigSaturated hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := waitSaturated hψ κ l r
  let q1 := genSigSaturatedStart hψ q0.1 q0.2
  let q2 := genSigSaturatedEmit hψ q1.1 q1.2
  let q3 := genSigSaturatedPropagate hψ q2.1 q2.2
  have h0 := waitSaturated_inProtocolDomain hψ l r hl hr
  have h1 := genSigStart_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := genSigEmit_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := genSigPropagate_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  exact genSigFinish_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2

private theorem domain_of_count_payload_eq {ψ κ : Nat}
    (input output : AgentState ψ) (hin : input.inProtocolDomain κ)
    (hcount : output.count = input.count)
    (hpayload : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain κ := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hcount ▸ hin.1, hpayload ▸ hin.2⟩

/-- Algorithm 9 only clears a path, which preserves its range. -/
theorem eliminateSig_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := eliminateSig hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf :
      let q := eliminateSig hψ l r
      FrameView.ofState q.1 = FrameView.ofState l ∧
        FrameView.ofState q.2 = FrameView.ofState r := by
    simp only [eliminateSig]
    repeat (first | constructor | rfl | split)
  have hp :
      let q := eliminateSig hψ l r
      PayloadView.PathValid ψ q.1.path ∧
        PayloadView.PathValid ψ q.2.path := by
    simp only [eliminateSig]
    split
    · constructor
      · split <;> exact ((inProtocolDomain_iff_path_frame l).1 hl).1
      · trivial
    · exact ⟨((inProtocolDomain_iff_path_frame l).1 hl).1,
        ((inProtocolDomain_iff_path_frame r).1 hr).1⟩
  exact ⟨domain_of_path_frame_eq l _ hl hp.1 hf.1,
    domain_of_path_frame_eq r _ hr hp.2 hf.2⟩

private theorem suppressSigStart_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := suppressSigStart l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigStart]
  repeat (first | constructor | rfl | split)

private theorem suppressSigMoveReset_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := suppressSigMoveReset l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigMoveReset]
  repeat (first | constructor | rfl | split)

private theorem suppressSigTerminal_count_payload {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := suppressSigTerminal hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      ((q.2.count = r.count ∨ q.2.count = 0) ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigTerminal]
  split
  · exact ⟨⟨rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩⟩
  · exact ⟨⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩⟩

private theorem suppressSigEcho_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := suppressSigEcho l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigEcho]
  repeat (first | constructor | rfl | split)

private theorem suppressSigFinish_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := suppressSigFinish l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [suppressSigFinish]
  repeat (first | constructor | rfl | split)

private theorem suppressSigStart_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigStart l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := suppressSigStart_count_payload l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressSigMoveReset_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigMoveReset l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := suppressSigMoveReset_count_payload l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressSigTerminal_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := suppressSigTerminal hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := suppressSigTerminal_count_payload hψ l r
  constructor
  · exact domain_of_count_payload_eq l _ hl h.1.1 h.1.2
  · have hc : (suppressSigTerminal hψ l r).2.count ≤ κ := by
      rcases h.2.1 with heq | hzero
      · exact heq ▸ hr.1
      · rw [hzero]
        exact Nat.zero_le _
    exact domain_of_count_payload _ hc (h.2.2 ▸ hr.2)

private theorem suppressSigEcho_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigEcho l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := suppressSigEcho_count_payload l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

private theorem suppressSigFinish_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSigFinish l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := suppressSigFinish_count_payload l r
  exact ⟨domain_of_count_payload_eq l _ hl h.1.1 h.1.2,
    domain_of_count_payload_eq r _ hr h.2.1 h.2.2⟩

/-- Algorithm 14 preserves all declared numeric ranges; its only constrained
write is the safe assignment `count := 0`. -/
theorem suppressSig_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := suppressSig hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [suppressSig_eq_staged]
  let q0 := suppressSigStart l r
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  have h0 := suppressSigStart_inProtocolDomain l r hl hr
  have h1 := suppressSigMoveReset_inProtocolDomain q0.1 q0.2 h0.1 h0.2
  have h2 := suppressSigTerminal_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := suppressSigEcho_inProtocolDomain q2.1 q2.2 h2.1 h2.2
  exact suppressSigFinish_inProtocolDomain q3.1 q3.2 h3.1 h3.2

private theorem eliminateLeadersNoCollisionFire_count_payload {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollisionFire hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionFire]
  repeat (first | constructor | rfl | split)

private theorem eliminateLeadersNoCollisionMove_count_payload {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollisionMove nextLabel l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionMove]
  repeat (first | constructor | rfl | split)

private theorem eliminateLeadersNoCollisionSignal_count_payload {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollisionSignal nextLabel l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionSignal]
  repeat (first | constructor | rfl | split)

private theorem
    eliminateLeadersNoCollisionSignalLeaderSink_count_payload {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  repeat (first | constructor | rfl | split)

private theorem unchangedStage_inProtocolDomain {ψ κ : Nat}
    (q : AgentState ψ × AgentState ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ)
    (h : (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r)) :
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ :=
  ⟨domain_of_count_payload_eq l q.1 hl h.1.1 h.1.2,
    domain_of_count_payload_eq r q.2 hr h.2.1 h.2.2⟩

/-- The no-collision Algorithm-15 candidate changes no field constrained by
`inProtocolDomain`. -/
theorem eliminateLeadersNoCollision_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := eliminateLeadersNoCollision hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  have h0 := unchangedStage_inProtocolDomain q0 l r hl hr
    (eliminateLeadersNoCollisionFire_count_payload hψ l r)
  have h1 := unchangedStage_inProtocolDomain q1 q0.1 q0.2 h0.1 h0.2
    (eliminateLeadersNoCollisionMove_count_payload nextLabel q0.1 q0.2)
  exact unchangedStage_inProtocolDomain
    (eliminateLeadersNoCollisionSignal nextLabel q1.1 q1.2)
    q1.1 q1.2 h1.1 h1.2
    (eliminateLeadersNoCollisionSignal_count_payload nextLabel q1.1 q1.2)

/-- The rooted leader-sink repair changes no field constrained by
`inProtocolDomain`. -/
theorem eliminateLeadersNoCollisionLeaderSink_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := eliminateLeadersNoCollisionLeaderSink hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  have h0 := unchangedStage_inProtocolDomain q0 l r hl hr
    (eliminateLeadersNoCollisionFire_count_payload hψ l r)
  have h1 := unchangedStage_inProtocolDomain q1 q0.1 q0.2 h0.1 h0.2
    (eliminateLeadersNoCollisionMove_count_payload nextLabel q0.1 q0.2)
  exact unchangedStage_inProtocolDomain
    (eliminateLeadersNoCollisionSignalLeaderSink nextLabel q1.1 q1.2)
    q1.1 q1.2 h1.1 h1.2
    (eliminateLeadersNoCollisionSignalLeaderSink_count_payload
      nextLabel q1.1 q1.2)

private theorem domain_of_path2_frame_eq {ψ κ : Nat}
    (input output : AgentState ψ) (hin : input.inProtocolDomain κ)
    (hpath2 : PayloadView.Path2Valid ψ output.path2)
    (hframe : Path2FrameView.ofState output = Path2FrameView.ofState input) :
    output.inProtocolDomain κ := by
  rw [inProtocolDomain_iff_path2_frame] at hin ⊢
  exact ⟨hpath2, hframe ▸ hin.2⟩

private theorem path2_zero_valid {ψ action : Nat} (hψ : ψ > 0)
    (ha1 : 1 ≤ action) (ha6 : action ≤ 6) :
    PayloadView.Path2Valid ψ (some ⟨0, 0, 0, action⟩) := by
  simp [PayloadView.Path2Valid]
  exact ⟨hψ, ha1, ha6⟩

private theorem checkSigSetReady_frame_path2 {ψ : Nat}
    (u : AgentState ψ) :
    Path2FrameView.ofState (checkSigSetReady u) =
        Path2FrameView.ofState u ∧
      (checkSigSetReady u).path2 = u.path2 := by
  simp only [checkSigSetReady]
  split <;> repeat (first | constructor | rfl | split)

private theorem checkSigCheckL_frame_path2 {ψ : Nat} (hψ : ψ > 0)
    (u : AgentState ψ) :
    Path2FrameView.ofState (checkSigCheckL hψ u) =
        Path2FrameView.ofState u ∧
      (checkSigCheckL hψ u).path2 = u.path2 := by
  simp only [checkSigCheckL]
  split <;> repeat (first | constructor | rfl | split)

private theorem checkSigCheckR_frame_path2 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    Path2FrameView.ofState (checkSigCheckR hψ l r) =
        Path2FrameView.ofState r ∧
      (checkSigCheckR hψ l r).path2 = r.path2 := by
  simp only [checkSigCheckR]
  split <;> repeat (first | constructor | rfl | split)

private theorem checkSigSetResult_frame {ψ : Nat} (u : AgentState ψ) :
    Path2FrameView.ofState (checkSigSetResult u) =
      Path2FrameView.ofState u := by
  simp only [checkSigSetResult]
  repeat (first | rfl | split)

private theorem checkSigSetResult_path2 {ψ : Nat} (hψ : ψ > 0)
    (u : AgentState ψ) (hu : PayloadView.Path2Valid ψ u.path2) :
    PayloadView.Path2Valid ψ (checkSigSetResult u).path2 := by
  cases h : u.state <;>
    simp [checkSigSetResult, h, PayloadView.Path2Valid] at *
  all_goals first | exact hu | exact hψ

private theorem checkSigSetLeader_frame_path2 {ψ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) :
    Path2FrameView.ofState (checkSigSetLeader hψ u) =
        Path2FrameView.ofState u ∧
      (checkSigSetLeader hψ u).path2 = u.path2 := by
  simp only [checkSigSetLeader]
  repeat (first | constructor | rfl | split)

private theorem checkSigSetReady_inProtocolDomain {ψ κ : Nat}
    (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (checkSigSetReady u).inProtocolDomain κ := by
  have h := checkSigSetReady_frame_path2 u
  exact domain_of_path2_frame_eq u _ hu
    (h.2 ▸ ((inProtocolDomain_iff_path2_frame u).1 hu).1) h.1

private theorem checkSigCheckL_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (checkSigCheckL hψ u).inProtocolDomain κ := by
  have h := checkSigCheckL_frame_path2 hψ u
  exact domain_of_path2_frame_eq u _ hu
    (h.2 ▸ ((inProtocolDomain_iff_path2_frame u).1 hu).1) h.1

private theorem checkSigCheckR_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) (hr : r.inProtocolDomain κ) :
    (checkSigCheckR hψ l r).inProtocolDomain κ := by
  have h := checkSigCheckR_frame_path2 hψ l r
  exact domain_of_path2_frame_eq r _ hr
    (h.2 ▸ ((inProtocolDomain_iff_path2_frame r).1 hr).1) h.1

private theorem checkSigSetResult_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (checkSigSetResult u).inProtocolDomain κ :=
  domain_of_path2_frame_eq u _ hu
    (checkSigSetResult_path2 hψ u
      ((inProtocolDomain_iff_path2_frame u).1 hu).1)
    (checkSigSetResult_frame u)

private theorem checkSigSetLeader_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (checkSigSetLeader hψ u).inProtocolDomain κ := by
  have h := checkSigSetLeader_frame_path2 hψ u
  exact domain_of_path2_frame_eq u _ hu
    (h.2 ▸ ((inProtocolDomain_iff_path2_frame u).1 hu).1) h.1

/-- Algorithm 11's constant action records remain in the declared path2
range, and all other constrained fields are unchanged. -/
theorem checkSig_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := checkSig hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [checkSig_eq_staged]
  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL hψ l0
  let r1 := checkSigCheckR hψ l1 r0
  let l2 := checkSigSetResult l1
  let r2 := checkSigSetResult r1
  have hl0 := checkSigSetReady_inProtocolDomain l hl
  have hr0 := checkSigSetReady_inProtocolDomain r hr
  have hl1 := checkSigCheckL_inProtocolDomain hψ l0 hl0
  have hr1 := checkSigCheckR_inProtocolDomain hψ l1 r0 hr0
  have hl2 := checkSigSetResult_inProtocolDomain hψ l1 hl1
  have hr2 := checkSigSetResult_inProtocolDomain hψ r1 hr1
  exact ⟨hl2, checkSigSetLeader_inProtocolDomain hψ r2 hr2⟩

private theorem disappearStartR_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := disappearStartR hψ l r
    Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      Path2FrameView.ofState q.2 = Path2FrameView.ofState r := by
  simp only [disappearStartR]
  repeat (first | constructor | rfl | split)

private theorem disappearStartR_path2 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : PayloadView.Path2Valid ψ l.path2)
    (hr : PayloadView.Path2Valid ψ r.path2) :
    let q := disappearStartR hψ l r
    PayloadView.Path2Valid ψ q.1.path2 ∧
      PayloadView.Path2Valid ψ q.2.path2 := by
  simp only [disappearStartR]
  constructor
  · exact hl
  · split
    · exact path2_zero_valid hψ (by omega) (by omega)
    · exact hr

private theorem disappearStartL_frame_path2 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := disappearStartL hψ l r
    (Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      q.1.path2 = l.path2) ∧
    (Path2FrameView.ofState q.2 = Path2FrameView.ofState r ∧
      q.2.path2 = r.path2) := by
  simp only [disappearStartL]
  repeat (first | constructor | rfl | split)

private theorem disappearCarry_frame_path2 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := disappearCarry hψ l r
    (Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      q.1.path2 = l.path2) ∧
    (Path2FrameView.ofState q.2 = Path2FrameView.ofState r ∧
      q.2.path2 = r.path2) := by
  simp only [disappearCarry]
  repeat (first | constructor | rfl | split)

private theorem disappearStartR_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := disappearStartR hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := disappearStartR_frame hψ l r
  have hp := disappearStartR_path2 hψ l r
    ((inProtocolDomain_iff_path2_frame l).1 hl).1
    ((inProtocolDomain_iff_path2_frame r).1 hr).1
  exact ⟨domain_of_path2_frame_eq l _ hl hp.1 hf.1,
    domain_of_path2_frame_eq r _ hr hp.2 hf.2⟩

private theorem disappearStartL_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := disappearStartL hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := disappearStartL_frame_path2 hψ l r
  exact ⟨domain_of_path2_frame_eq l _ hl
      (h.1.2 ▸ ((inProtocolDomain_iff_path2_frame l).1 hl).1) h.1.1,
    domain_of_path2_frame_eq r _ hr
      (h.2.2 ▸ ((inProtocolDomain_iff_path2_frame r).1 hr).1) h.2.1⟩

private theorem disappearCarry_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := disappearCarry hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := disappearCarry_frame_path2 hψ l r
  exact ⟨domain_of_path2_frame_eq l _ hl
      (h.1.2 ▸ ((inProtocolDomain_iff_path2_frame l).1 hl).1) h.1.1,
    domain_of_path2_frame_eq r _ hr
      (h.2.2 ▸ ((inProtocolDomain_iff_path2_frame r).1 hr).1) h.2.1⟩

/-- Algorithm 13 either preserves path2 or creates the bounded action-5
record; its carry stage changes no numeric payload. -/
theorem disappear_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := disappear hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [disappear_eq_staged]
  let q0 := disappearStartR hψ l r
  let q1 := disappearStartL hψ q0.1 q0.2
  have h0 := disappearStartR_inProtocolDomain hψ l r hl hr
  have h1 := disappearStartL_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  exact disappearCarry_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2

private theorem path_to_path2_valid {ψ label bit : Nat}
    (hp : PayloadView.PathValid ψ (.some label bit)) :
    PayloadView.Path2Valid ψ (some ⟨label, bit, ψ, 1⟩) := by
  change label < ψ ∧ bit ≤ 1 ∧ ψ ≤ ψ ∧ 1 ≤ 1 ∧ 1 ≤ 6
  exact ⟨hp.1, hp.2, Nat.le_refl _, by omega, by omega⟩

private theorem path2_backscan_valid {ψ action : Nat} (hψ : ψ > 0)
    (ha1 : 1 ≤ action) (ha6 : action ≤ 6) :
    PayloadView.Path2Valid ψ (some ⟨0, 0, ψ - 1, action⟩) := by
  change 0 < ψ ∧ 0 ≤ 1 ∧ ψ - 1 ≤ ψ ∧
    1 ≤ action ∧ action ≤ 6
  omega

private theorem cmpUpdatePropagate_frame_path2 {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := cmpUpdatePropagate hψ l r
    (Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      q.1.path2 = l.path2) ∧
    (Path2FrameView.ofState q.2 = Path2FrameView.ofState r ∧
      q.2.path2 = r.path2) := by
  simp only [cmpUpdatePropagate]
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_frame {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ) :
    Path2FrameView.ofState (cmpUpdateSetPath2 hψ l) =
      Path2FrameView.ofState l := by
  simp only [cmpUpdateSetPath2]
  repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_path2 {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ) (hp : PayloadView.PathValid ψ l.path)
    (h2 : PayloadView.Path2Valid ψ l.path2) :
    PayloadView.Path2Valid ψ (cmpUpdateSetPath2 hψ l).path2 := by
  cases heq : l.path with
  | bot => simpa [cmpUpdateSetPath2, heq] using h2
  | some label bit =>
    have hp' : PayloadView.PathValid ψ (.some label bit) := by
      rw [← heq]
      exact hp
    by_cases hg : l.label = ⟨0, hψ⟩ ∧ l.state = .compare2
    · simpa [cmpUpdateSetPath2, heq, hg] using path_to_path2_valid hp'
    · simpa [cmpUpdateSetPath2, heq, hg] using h2

private theorem compareBitUpdateL_frame {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ) :
    Path2FrameView.ofState (compareBitUpdateL hψ l) =
      Path2FrameView.ofState l := by
  simp only [compareBitUpdateL]
  repeat (first | rfl | split)

private theorem compareBitUpdateL_path2 {ψ : Nat} (hψ : ψ > 0)
    (l : AgentState ψ) (hp : PayloadView.PathValid ψ l.path)
    (h2 : PayloadView.Path2Valid ψ l.path2) :
    PayloadView.Path2Valid ψ (compareBitUpdateL hψ l).path2 := by
  cases h2eq : l.path2 with
  | none => simpa [compareBitUpdateL, h2eq] using h2
  | some p2 =>
    cases hpeq : l.path with
    | bot => simpa [compareBitUpdateL, h2eq, hpeq] using h2
    | some label bit =>
      have hp' : PayloadView.PathValid ψ (.some label bit) := by
        rw [← hpeq]
        exact hp
      by_cases hg : p2.action = 2 ∧ p2.position = 0
      · simpa [compareBitUpdateL, h2eq, hpeq, hg] using
          path_to_path2_valid hp'
      · simpa [compareBitUpdateL, h2eq, hpeq, hg] using h2

private theorem compareBitUpdateR_frame {ψ : Nat} (hψ : ψ > 0)
    (r : AgentState ψ) :
    Path2FrameView.ofState (compareBitUpdateR hψ r) =
      Path2FrameView.ofState r := by
  simp only [compareBitUpdateR]
  repeat (first | rfl | split)

private theorem compareBitUpdateR_path2 {ψ : Nat} (hψ : ψ > 0)
    (r : AgentState ψ) (h2 : PayloadView.Path2Valid ψ r.path2) :
    PayloadView.Path2Valid ψ (compareBitUpdateR hψ r).path2 := by
  cases heq : r.path2 with
  | none => simpa [compareBitUpdateR, heq] using h2
  | some p2 =>
    by_cases hp : p2.position = 0
    · cases hb : r.bit
      · by_cases hlt : 0 < p2.bit
        · simpa [compareBitUpdateR, heq, hp, hb, hlt] using
            path2_zero_valid (action := 4) hψ (by omega) (by omega)
        · by_cases hend : r.label = ⟨ψ - 1, by omega⟩
          · simpa [compareBitUpdateR, heq, hp, hb, hlt, hend] using
              path2_zero_valid (action := 3) hψ (by omega) (by omega)
          · simpa [compareBitUpdateR, heq, hp, hb, hlt, hend] using
              path2_backscan_valid (action := 2) hψ (by omega) (by omega)
      · by_cases hgt : 1 > p2.bit
        · simpa [compareBitUpdateR, heq, hp, hb, hgt] using
            path2_zero_valid (action := 3) hψ (by omega) (by omega)
        · by_cases hlt : 1 < p2.bit
          · simpa [compareBitUpdateR, heq, hp, hb, hgt, hlt] using
              path2_zero_valid (action := 4) hψ (by omega) (by omega)
          · by_cases hend : r.label = ⟨ψ - 1, by omega⟩
            · simpa [compareBitUpdateR, heq, hp, hb, hgt, hlt, hend] using
                path2_zero_valid (action := 3) hψ (by omega) (by omega)
            · simpa [compareBitUpdateR, heq, hp, hb, hgt, hlt, hend] using
                path2_backscan_valid (action := 2) hψ (by omega) (by omega)
    · simpa [compareBitUpdateR, heq, hp] using h2

private theorem cmpUpdatePropagate_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := cmpUpdatePropagate hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have h := cmpUpdatePropagate_frame_path2 hψ l r
  exact ⟨domain_of_path2_frame_eq l _ hl
      (h.1.2 ▸ ((inProtocolDomain_iff_path2_frame l).1 hl).1) h.1.1,
    domain_of_path2_frame_eq r _ hr
      (h.2.2 ▸ ((inProtocolDomain_iff_path2_frame r).1 hr).1) h.2.1⟩

/-- Creating the bounded comparison-control payload preserves the declared
numeric domain whenever the source path was already bounded. -/
theorem cmpUpdateSetPath2_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l : AgentState ψ) (hl : l.inProtocolDomain κ) :
    (cmpUpdateSetPath2 hψ l).inProtocolDomain κ :=
  domain_of_path2_frame_eq l _ hl
    (cmpUpdateSetPath2_path2 hψ l
      ((inProtocolDomain_iff_path_frame l).1 hl).1
      ((inProtocolDomain_iff_path2_frame l).1 hl).1)
    (cmpUpdateSetPath2_frame hψ l)

private theorem cmpUpdate_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := cmpUpdate hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := if l.label = ⟨0, hψ⟩ then { l with state := .congest } else l
  have hl0 : l0.inProtocolDomain κ := by
    apply domain_of_count_payload_eq l l0 hl
    · dsimp only [l0]
      split <;> rfl
    · dsimp only [l0]
      split <;> rfl
  let q0 := cmpUpdatePropagate hψ l0 r
  have h0 := cmpUpdatePropagate_inProtocolDomain hψ l0 r hl0 hr
  exact ⟨cmpUpdateSetPath2_inProtocolDomain hψ q0.1 h0.1, h0.2⟩

private theorem compareBitUpdateL_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l : AgentState ψ) (hl : l.inProtocolDomain κ) :
    (compareBitUpdateL hψ l).inProtocolDomain κ :=
  domain_of_path2_frame_eq l _ hl
    (compareBitUpdateL_path2 hψ l
      ((inProtocolDomain_iff_path_frame l).1 hl).1
      ((inProtocolDomain_iff_path2_frame l).1 hl).1)
    (compareBitUpdateL_frame hψ l)

private theorem compareBitUpdateR_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (r : AgentState ψ) (hr : r.inProtocolDomain κ) :
    (compareBitUpdateR hψ r).inProtocolDomain κ :=
  domain_of_path2_frame_eq r _ hr
    (compareBitUpdateR_path2 hψ r
      ((inProtocolDomain_iff_path2_frame r).1 hr).1)
    (compareBitUpdateR_frame hψ r)

private theorem compareBit_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := compareBit hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let r0 := compareBitUpdateR hψ r
  have hr0 := compareBitUpdateR_inProtocolDomain hψ r hr
  exact ⟨compareBitUpdateL_inProtocolDomain hψ l hl, hr0⟩

/-- Algorithm-6 initialization changes only comparison state. -/
theorem compareSigInit_inProtocolDomain {ψ κ : Nat}
    (l : AgentState ψ) (hl : l.inProtocolDomain κ) :
    (compareSigInit l).inProtocolDomain κ := by
  apply domain_of_count_payload_eq l _ hl
  · simp only [compareSigInit]
    split <;> rfl
  · simp only [compareSigInit]
    split <;> rfl

/-- Algorithm-6's path2 dispatch preserves every declared range. -/
theorem compareSigDispatch_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := compareSigDispatch hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  cases hl2 : l.path2 <;> cases hr2 : r.path2 <;>
    simp only [compareSigDispatch, hl2, hr2]
  · exact ⟨hl, hr⟩
  · exact compareBit_inProtocolDomain hψ l r hl hr
  · exact compareBit_inProtocolDomain hψ l r hl hr
  · exact compareBit_inProtocolDomain hψ l r hl hr

/-- Algorithms 6–8 preserve every declared range. Fresh path2 records use
only bounded path payloads, positions `0`, `ψ-1`, or `ψ`, and actions 1–4. -/
theorem compareSig_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := compareSig hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := compareSigInit l
  have hl0 := compareSigInit_inProtocolDomain l hl
  change (match l0.path with
    | .bot => (l0, r)
    | .some _ _ =>
      match r.path with
      | .some _ _ =>
        let q := cmpUpdate hψ l0 r
        compareSigDispatch hψ q.1 q.2
      | .bot => (l0, r)).1.inProtocolDomain κ ∧
    (match l0.path with
    | .bot => (l0, r)
    | .some _ _ =>
      match r.path with
      | .some _ _ =>
        let q := cmpUpdate hψ l0 r
        compareSigDispatch hψ q.1 q.2
      | .bot => (l0, r)).2.inProtocolDomain κ
  cases hlp : l0.path with
  | bot => exact ⟨hl0, hr⟩
  | some ll lb =>
    cases hrp : r.path with
    | bot => exact ⟨hl0, hr⟩
    | some rl rb =>
      let q0 := cmpUpdate hψ l0 r
      have h0 := cmpUpdate_inProtocolDomain hψ l0 r hl0 hr
      exact compareSigDispatch_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2

private theorem sigMoveStep1_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := sigMoveStep1 l r
    FrameView.ofState q.1 = FrameView.ofState l ∧
      FrameView.ofState q.2 = FrameView.ofState r := by
  simp only [sigMoveStep1]
  repeat (first | constructor | rfl | split)

private theorem sigMoveStep1_path {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.PathValid ψ l.path)
    (hr : PayloadView.PathValid ψ r.path) :
    let q := sigMoveStep1 l r
    PayloadView.PathValid ψ q.1.path ∧
      PayloadView.PathValid ψ q.2.path := by
  cases hL : l.path <;> cases hR : r.path
  all_goals simp_all only [sigMoveStep1]
  all_goals repeat split
  all_goals simp_all [PayloadView.PathValid]

private theorem sigMoveStep1_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := sigMoveStep1 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := sigMoveStep1_frame l r
  have hp := sigMoveStep1_path l r
    ((inProtocolDomain_iff_path_frame l).1 hl).1
    ((inProtocolDomain_iff_path_frame r).1 hr).1
  exact ⟨domain_of_path_frame_eq l _ hl hp.1 hf.1,
    domain_of_path_frame_eq r _ hr hp.2 hf.2⟩

private theorem path2_decrement_valid {ψ : Nat} (p : Path2Info)
    (hp : PayloadView.Path2Valid ψ (some p)) :
    PayloadView.Path2Valid ψ
      (some { p with position := p.position - 1 }) := by
  change p.label < ψ ∧ p.bit ≤ 1 ∧ p.position ≤ ψ ∧
    1 ≤ p.action ∧ p.action ≤ 6 at hp
  change p.label < ψ ∧ p.bit ≤ 1 ∧ p.position - 1 ≤ ψ ∧
    1 ≤ p.action ∧ p.action ≤ 6
  omega

private theorem sigMoveStep2_path2 {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.Path2Valid ψ l.path2)
    (hr : PayloadView.Path2Valid ψ r.path2) :
    let q := sigMoveStep2 l r
    PayloadView.Path2Valid ψ q.1.path2 ∧
      PayloadView.Path2Valid ψ q.2.path2 := by
  cases h : l.path2
  · simp only [sigMoveStep2, h]
    exact ⟨trivial, hr⟩
  · rename_i p
    simp only [sigMoveStep2, h]
    split
    · constructor
      · trivial
      · apply path2_decrement_valid
        rw [← h]
        exact hl
    · simpa [h] using And.intro hl hr

private theorem sigMoveStep3_path2 {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.Path2Valid ψ l.path2)
    (hr : PayloadView.Path2Valid ψ r.path2) :
    let q := sigMoveStep3 l r
    PayloadView.Path2Valid ψ q.1.path2 ∧
      PayloadView.Path2Valid ψ q.2.path2 := by
  cases h : r.path2
  · simp only [sigMoveStep3, h]
    exact ⟨hl, trivial⟩
  · rename_i p
    simp only [sigMoveStep3, h]
    split
    · constructor
      · apply path2_decrement_valid
        rw [← h]
        exact hr
      · trivial
    · simpa [h] using And.intro hl hr

private theorem sigMoveStep4_path2 {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.Path2Valid ψ l.path2)
    (hr : PayloadView.Path2Valid ψ r.path2) :
    let q := sigMoveStep4 l r
    PayloadView.Path2Valid ψ q.1.path2 ∧
      PayloadView.Path2Valid ψ q.2.path2 := by
  cases h : r.path2
  · simp only [sigMoveStep4, h]
    exact ⟨hl, trivial⟩
  · simp only [sigMoveStep4, h]
    split
    · exact ⟨by rw [← h]; exact hr, trivial⟩
    · simpa [h] using And.intro hl hr

private theorem sigMoveStep5_path2 {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.Path2Valid ψ l.path2)
    (hr : PayloadView.Path2Valid ψ r.path2) :
    let q := sigMoveStep5 l r
    PayloadView.Path2Valid ψ q.1.path2 ∧
      PayloadView.Path2Valid ψ q.2.path2 := by
  cases h : l.path2
  · simp only [sigMoveStep5, h]
    exact ⟨trivial, hr⟩
  · simp only [sigMoveStep5, h]
    split
    · exact ⟨trivial, by rw [← h]; exact hl⟩
    · simpa [h] using And.intro hl hr

private theorem sigMoveStep2_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := sigMoveStep2 l r
    Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      Path2FrameView.ofState q.2 = Path2FrameView.ofState r := by
  simp only [sigMoveStep2]
  repeat (first | constructor | rfl | split)

private theorem sigMoveStep3_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := sigMoveStep3 l r
    Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      Path2FrameView.ofState q.2 = Path2FrameView.ofState r := by
  simp only [sigMoveStep3]
  repeat (first | constructor | rfl | split)

private theorem sigMoveStep4_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := sigMoveStep4 l r
    Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      Path2FrameView.ofState q.2 = Path2FrameView.ofState r := by
  simp only [sigMoveStep4]
  repeat (first | constructor | rfl | split)

private theorem sigMoveStep5_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := sigMoveStep5 l r
    Path2FrameView.ofState q.1 = Path2FrameView.ofState l ∧
      Path2FrameView.ofState q.2 = Path2FrameView.ofState r := by
  simp only [sigMoveStep5]
  repeat (first | constructor | rfl | split)

private theorem sigMoveStep2_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := sigMoveStep2 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := sigMoveStep2_frame l r
  have hp := sigMoveStep2_path2 l r
    ((inProtocolDomain_iff_path2_frame l).1 hl).1
    ((inProtocolDomain_iff_path2_frame r).1 hr).1
  exact ⟨domain_of_path2_frame_eq l _ hl hp.1 hf.1,
    domain_of_path2_frame_eq r _ hr hp.2 hf.2⟩

private theorem sigMoveStep3_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := sigMoveStep3 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := sigMoveStep3_frame l r
  have hp := sigMoveStep3_path2 l r
    ((inProtocolDomain_iff_path2_frame l).1 hl).1
    ((inProtocolDomain_iff_path2_frame r).1 hr).1
  exact ⟨domain_of_path2_frame_eq l _ hl hp.1 hf.1,
    domain_of_path2_frame_eq r _ hr hp.2 hf.2⟩

private theorem sigMoveStep4_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := sigMoveStep4 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := sigMoveStep4_frame l r
  have hp := sigMoveStep4_path2 l r
    ((inProtocolDomain_iff_path2_frame l).1 hl).1
    ((inProtocolDomain_iff_path2_frame r).1 hr).1
  exact ⟨domain_of_path2_frame_eq l _ hl hp.1 hf.1,
    domain_of_path2_frame_eq r _ hr hp.2 hf.2⟩

private theorem sigMoveStep5_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := sigMoveStep5 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := sigMoveStep5_frame l r
  have hp := sigMoveStep5_path2 l r
    ((inProtocolDomain_iff_path2_frame l).1 hl).1
    ((inProtocolDomain_iff_path2_frame r).1 hr).1
  exact ⟨domain_of_path2_frame_eq l _ hl hp.1 hf.1,
    domain_of_path2_frame_eq r _ hr hp.2 hf.2⟩

private theorem sigMoveApplyControl_count_payload {ψ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControl hψ u).count = u.count ∧
      PayloadView.ofState (sigMoveApplyControl hψ u) =
        PayloadView.ofState u := by
  simp only [sigMoveApplyControl]
  repeat (first | constructor | rfl | split)

private theorem sigMoveApplyControl_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (sigMoveApplyControl hψ u).inProtocolDomain κ := by
  have h := sigMoveApplyControl_count_payload hψ u
  exact domain_of_count_payload_eq u _ hu h.1 h.2

private theorem setState_inProtocolDomain {ψ κ : Nat}
    (s : AgentState ψ) (st : MainState) (h : s.inProtocolDomain κ) :
    ({ s with state := st }).inProtocolDomain κ := by
  change s.inProtocolDomain κ
  exact h

/-- Algorithm 10 preserves all declared ranges while moving/clearing path and
path2 payloads. Its only arithmetic update decrements a bounded position. -/
theorem sigMove_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := sigMove hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := sigMoveStep1 l r
  let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2
  let q3 := sigMoveStep4 q2.1 q2.2
  let q4 := sigMoveStep5 q3.1 q3.2
  have h0 := sigMoveStep1_inProtocolDomain l r hl hr
  have h1 := sigMoveStep2_inProtocolDomain q0.1 q0.2 h0.1 h0.2
  have h2 := sigMoveStep3_inProtocolDomain q1.1 q1.2 h1.1 h1.2
  have h3 := sigMoveStep4_inProtocolDomain q2.1 q2.2 h2.1 h2.2
  have h4 := sigMoveStep5_inProtocolDomain q3.1 q3.2 h3.1 h3.2
  let l5 := sigMoveApplyControl hψ q4.1
  let r5 := sigMoveApplyControl hψ q4.2
  have hl5 : l5.inProtocolDomain κ :=
    sigMoveApplyControl_inProtocolDomain hψ q4.1 h4.1
  have hr5 : r5.inProtocolDomain κ :=
    sigMoveApplyControl_inProtocolDomain hψ q4.2 h4.2
  let l6 :=
    if r5.state = .depart then
      if l5.label.val < ψ - 1 ∧ l5.state = .CHECK_ready then
        { l5 with state := .depart }
      else l5
    else l5
  have hl6 : l6.inProtocolDomain κ := by
    dsimp only [l6]
    split
    · split
      · exact setState_inProtocolDomain l5 .depart hl5
      · exact hl5
    · exact hl5
  change l6.inProtocolDomain κ ∧ r5.inProtocolDomain κ
  exact ⟨hl6, hr5⟩

private theorem domain_of_path3_frame_eq {ψ κ : Nat}
    (input output : AgentState ψ) (hin : input.inProtocolDomain κ)
    (hpath3 : PayloadView.Path3Valid ψ output.path3)
    (hframe : Path3FrameView.ofState output = Path3FrameView.ofState input) :
    output.inProtocolDomain κ := by
  rw [inProtocolDomain_iff_path3_frame] at hin ⊢
  exact ⟨hpath3, hframe ▸ hin.2⟩

private theorem fresh_path3_valid {ψ : Nat} (label : Fin ψ) (bit : Bool) :
    PayloadView.Path3Valid ψ
      (some ⟨label.val, if bit then 1 else 0, 1⟩) := by
  cases bit <;> simp [PayloadView.Path3Valid, label.isLt]

private theorem gensigWriteseqStart_frame_path3 {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := gensigWriteseqStart hψ l r
    (Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
      q.1.path3 = l.path3) ∧
    (Path3FrameView.ofState q.2 = Path3FrameView.ofState r ∧
      q.2.path3 = r.path3) := by
  simp only [gensigWriteseqStart]
  repeat (first | constructor | rfl | split)

private theorem gensigWriteseqEmit_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := gensigWriteseqEmit hψ l r
    Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
      Path3FrameView.ofState q.2 = Path3FrameView.ofState r := by
  simp only [gensigWriteseqEmit]
  repeat (first | constructor | rfl | split)

private theorem gensigWriteseqEmit_path3 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : PayloadView.Path3Valid ψ l.path3)
    (hr : PayloadView.Path3Valid ψ r.path3) :
    let q := gensigWriteseqEmit hψ l r
    PayloadView.Path3Valid ψ q.1.path3 ∧
      PayloadView.Path3Valid ψ q.2.path3 := by
  simp only [gensigWriteseqEmit]
  constructor
  · exact hl
  · split
    · cases hb : r.bit <;> simpa [hb] using fresh_path3_valid r.label r.bit
    · exact hr

private theorem gensigWriteseqPropagate_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := gensigWriteseqPropagate hψ l r
    Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
      Path3FrameView.ofState q.2 = Path3FrameView.ofState r := by
  simp only [gensigWriteseqPropagate]
  repeat (first | constructor | rfl | split)

private theorem gensigWriteseqPropagate_path3 {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : PayloadView.Path3Valid ψ l.path3)
    (hr : PayloadView.Path3Valid ψ r.path3) :
    let q := gensigWriteseqPropagate hψ l r
    PayloadView.Path3Valid ψ q.1.path3 ∧
      PayloadView.Path3Valid ψ q.2.path3 := by
  simp only [gensigWriteseqPropagate]
  split
  · constructor
    · cases hb : l.bit
      · by_cases hc : r.b_carry = true
        · simp [hc]
          exact fresh_path3_valid l.label false
        · simp [hc]
          exact fresh_path3_valid l.label false
      · by_cases hc : r.b_carry = true
        · simp [hc]
          exact fresh_path3_valid l.label true
        · simp [hc]
          exact fresh_path3_valid l.label true
    · by_cases hc : r.b_carry = true
      · simp [hc]
        exact hr
      · simp [hc]
        exact hr
  · simpa only using And.intro hl hr

private theorem gensigWriteseqFinish_frame_path3 {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := gensigWriteseqFinish hψ l r
    (Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
      q.1.path3 = l.path3) ∧
    (Path3FrameView.ofState q.2 = Path3FrameView.ofState r ∧
      q.2.path3 = r.path3) := by
  simp only [gensigWriteseqFinish]
  repeat (first | constructor | rfl | split)

private theorem unchangedPath3Stage_inProtocolDomain {ψ κ : Nat}
    (q : AgentState ψ × AgentState ψ) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ)
    (h : (Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
          q.1.path3 = l.path3) ∧
        (Path3FrameView.ofState q.2 = Path3FrameView.ofState r ∧
          q.2.path3 = r.path3)) :
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ :=
  ⟨domain_of_path3_frame_eq l q.1 hl
      (h.1.2 ▸ ((inProtocolDomain_iff_path3_frame l).1 hl).1) h.1.1,
    domain_of_path3_frame_eq r q.2 hr
      (h.2.2 ▸ ((inProtocolDomain_iff_path3_frame r).1 hr).1) h.2.1⟩

private theorem gensigWriteseqEmit_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := gensigWriteseqEmit hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := gensigWriteseqEmit_frame hψ l r
  have hp := gensigWriteseqEmit_path3 hψ l r
    ((inProtocolDomain_iff_path3_frame l).1 hl).1
    ((inProtocolDomain_iff_path3_frame r).1 hr).1
  exact ⟨domain_of_path3_frame_eq l _ hl hp.1 hf.1,
    domain_of_path3_frame_eq r _ hr hp.2 hf.2⟩

private theorem gensigWriteseqPropagate_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := gensigWriteseqPropagate hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := gensigWriteseqPropagate_frame hψ l r
  have hp := gensigWriteseqPropagate_path3 hψ l r
    ((inProtocolDomain_iff_path3_frame l).1 hl).1
    ((inProtocolDomain_iff_path3_frame r).1 hr).1
  exact ⟨domain_of_path3_frame_eq l _ hl hp.1 hf.1,
    domain_of_path3_frame_eq r _ hr hp.2 hf.2⟩

/-- Algorithm 18 creates only path3 payloads built from finite labels, Boolean
bits, and flag 1. -/
theorem gensigWriteseq_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := gensigWriteseq hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [gensigWriteseq_eq_staged]
  let q0 := gensigWriteseqStart hψ l r
  let q1 := gensigWriteseqEmit hψ q0.1 q0.2
  let q2 := gensigWriteseqPropagate hψ q1.1 q1.2
  have h0 := unchangedPath3Stage_inProtocolDomain q0 l r hl hr
    (gensigWriteseqStart_frame_path3 hψ l r)
  have h1 := gensigWriteseqEmit_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := gensigWriteseqPropagate_inProtocolDomain
    hψ q1.1 q1.2 h1.1 h1.2
  exact unchangedPath3Stage_inProtocolDomain
    (gensigWriteseqFinish hψ q2.1 q2.2) q2.1 q2.2 h2.1 h2.2
    (gensigWriteseqFinish_frame_path3 hψ q2.1 q2.2)

private theorem writeActionApplyOverwrite_frame {ψ : Nat}
    (r : AgentState ψ) :
    Path3FrameView.ofState (writeActionApplyOverwrite r) =
      Path3FrameView.ofState r := by
  simp only [writeActionApplyOverwrite]
  repeat (first | rfl | split)

private theorem writeActionApplyOverwrite_path3 {ψ : Nat}
    (r : AgentState ψ) (hr : PayloadView.Path3Valid ψ r.path3) :
    PayloadView.Path3Valid ψ (writeActionApplyOverwrite r).path3 := by
  cases h : r.path3
  · simpa [writeActionApplyOverwrite, h] using hr
  · rename_i p
    rw [h] at hr
    change p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1 at hr
    simp [writeActionApplyOverwrite, h, PayloadView.Path3Valid]
    omega

private theorem writeActionApplyMoveFlip_frame {ψ : Nat}
    (r : AgentState ψ) :
    Path3FrameView.ofState (writeActionApplyMoveFlip r) =
      Path3FrameView.ofState r := by
  simp only [writeActionApplyMoveFlip]
  repeat (first | rfl | split)

private theorem writeActionApplyMoveFlip_path3 {ψ : Nat}
    (r : AgentState ψ) (hr : PayloadView.Path3Valid ψ r.path3) :
    PayloadView.Path3Valid ψ (writeActionApplyMoveFlip r).path3 := by
  cases h : r.path3
  · simpa [writeActionApplyMoveFlip, h] using hr
  · rename_i p
    rw [h] at hr
    change p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1 at hr
    simp [writeActionApplyMoveFlip, h, PayloadView.Path3Valid]
    omega

private theorem writeActionApplyOverwrite_inProtocolDomain {ψ κ : Nat}
    (r : AgentState ψ) (hr : r.inProtocolDomain κ) :
    (writeActionApplyOverwrite r).inProtocolDomain κ :=
  domain_of_path3_frame_eq r _ hr
    (writeActionApplyOverwrite_path3 r
      ((inProtocolDomain_iff_path3_frame r).1 hr).1)
    (writeActionApplyOverwrite_frame r)

private theorem writeActionApplyMoveFlip_inProtocolDomain {ψ κ : Nat}
    (r : AgentState ψ) (hr : r.inProtocolDomain κ) :
    (writeActionApplyMoveFlip r).inProtocolDomain κ :=
  domain_of_path3_frame_eq r _ hr
    (writeActionApplyMoveFlip_path3 r
      ((inProtocolDomain_iff_path3_frame r).1 hr).1)
    (writeActionApplyMoveFlip_frame r)

private theorem writeActionActivate_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (writeActionActivate hψ u).inProtocolDomain κ := by
  apply domain_of_count_payload_eq u _ hu
  · simp only [writeActionActivate]
    split <;> rfl
  · simp only [writeActionActivate]
    split <;> rfl

private theorem writeActionExecute_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := writeActionExecute hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  simp only [writeActionExecute]
  split
  · let r0 := if r.write_state = .overwrite then
        writeActionApplyOverwrite r else r
    let r1 := if r0.write_state = .move_flip then
        writeActionApplyMoveFlip r0 else r0
    let r2 := if r1.write_state = .increment_group then
        if r1.bit = true then { r1 with bit := false }
        else { r1 with bit := true, write_state := .depart }
      else r1
    let l0 := if r2.label ≠ ⟨0, hψ⟩ then
        { l with write_state := r2.write_state } else l
    have hr0 : r0.inProtocolDomain κ := by
      dsimp only [r0]
      split
      · exact writeActionApplyOverwrite_inProtocolDomain r hr
      · exact hr
    have hr1 : r1.inProtocolDomain κ := by
      dsimp only [r1]
      split
      · exact writeActionApplyMoveFlip_inProtocolDomain r0 hr0
      · exact hr0
    have hr2 : r2.inProtocolDomain κ := by
      apply domain_of_count_payload_eq r1 r2 hr1
      · dsimp only [r2]
        repeat (first | rfl | split)
      · dsimp only [r2]
        repeat (first | rfl | split)
    have hl0 : l0.inProtocolDomain κ := by
      apply domain_of_count_payload_eq l l0 hl
      · dsimp only [l0]
        split <;> rfl
      · dsimp only [l0]
        split <;> rfl
    change l0.inProtocolDomain κ ∧
      ({ r2 with write_state := .depart }).inProtocolDomain κ
    exact ⟨hl0, setState_inProtocolDomain r2 r2.state hr2⟩
  · exact ⟨hl, hr⟩

/-- Algorithm 19 preserves every raw range. Its flag complement remains in
`{0,1}` and all other writes affect finite enums or Booleans. -/
theorem writeAction_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := writeAction hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [writeAction_eq_staged]
  exact writeActionExecute_inProtocolDomain hψ
    (writeActionActivate hψ l) (writeActionActivate hψ r)
    (writeActionActivate_inProtocolDomain hψ l hl)
    (writeActionActivate_inProtocolDomain hψ r hr)

private theorem moveWsigCheckGenWs_path3 {ψ : Nat}
    (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).path3 = r.path3 := by
  simp only [moveWsigCheckGenWs]
  repeat (first | rfl | split)

private theorem moveWsigStart_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := moveWsigStart l r
    Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
      Path3FrameView.ofState q.2 = Path3FrameView.ofState r := by
  simp only [moveWsigStart, moveWsigCheckGenWs]
  repeat (first | constructor | rfl | split)

private theorem moveWsigStart_path3 {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.Path3Valid ψ l.path3)
    (hr : PayloadView.Path3Valid ψ r.path3) :
    let q := moveWsigStart l r
    PayloadView.Path3Valid ψ q.1.path3 ∧
      PayloadView.Path3Valid ψ q.2.path3 := by
  simp only [moveWsigStart]
  split
  · exact ⟨trivial, moveWsigCheckGenWs_path3 l r ▸ hr⟩
  · exact ⟨hl, hr⟩

private theorem moveWsigCheckLast_frame {ψ : Nat} (l : AgentState ψ) :
    Path3FrameView.ofState (moveWsigCheckLast l) =
      Path3FrameView.ofState l := by
  simp only [moveWsigCheckLast]
  repeat (first | rfl | split)

private theorem moveWsigCheckLast_path3 {ψ : Nat} (l : AgentState ψ)
    (hl : PayloadView.Path3Valid ψ l.path3) :
    PayloadView.Path3Valid ψ (moveWsigCheckLast l).path3 := by
  cases h : l.path3
  · simpa [moveWsigCheckLast, h] using hl
  · simp only [moveWsigCheckLast, h]
    split
    · trivial
    · exact hl

private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    let q := moveWsigTransfer l r
    Path3FrameView.ofState q.1 = Path3FrameView.ofState l ∧
      Path3FrameView.ofState q.2 = Path3FrameView.ofState r := by
  simp only [moveWsigTransfer]
  repeat (first | constructor | rfl | split)

private theorem moveWsigTransfer_path3 {ψ : Nat} (l r : AgentState ψ)
    (hl : PayloadView.Path3Valid ψ l.path3)
    (hr : PayloadView.Path3Valid ψ r.path3) :
    let q := moveWsigTransfer l r
    PayloadView.Path3Valid ψ q.1.path3 ∧
      PayloadView.Path3Valid ψ q.2.path3 := by
  cases hL : l.path3 <;> cases hR : r.path3
  all_goals simp_all only [moveWsigTransfer]
  all_goals repeat split
  all_goals simp_all [PayloadView.Path3Valid]

private theorem moveWsigStart_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := moveWsigStart l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := moveWsigStart_frame l r
  have hp := moveWsigStart_path3 l r
    ((inProtocolDomain_iff_path3_frame l).1 hl).1
    ((inProtocolDomain_iff_path3_frame r).1 hr).1
  exact ⟨domain_of_path3_frame_eq l _ hl hp.1 hf.1,
    domain_of_path3_frame_eq r _ hr hp.2 hf.2⟩

private theorem moveWsigCheckLast_inProtocolDomain {ψ κ : Nat}
    (l : AgentState ψ) (hl : l.inProtocolDomain κ) :
    (moveWsigCheckLast l).inProtocolDomain κ :=
  domain_of_path3_frame_eq l _ hl
    (moveWsigCheckLast_path3 l
      ((inProtocolDomain_iff_path3_frame l).1 hl).1)
    (moveWsigCheckLast_frame l)

private theorem moveWsigTransfer_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := moveWsigTransfer l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  have hf := moveWsigTransfer_frame l r
  have hp := moveWsigTransfer_path3 l r
    ((inProtocolDomain_iff_path3_frame l).1 hl).1
    ((inProtocolDomain_iff_path3_frame r).1 hr).1
  exact ⟨domain_of_path3_frame_eq l _ hl hp.1 hf.1,
    domain_of_path3_frame_eq r _ hr hp.2 hf.2⟩

private theorem moveWsigMoveWrite_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := moveWsigMoveWrite l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [moveWsigMoveWrite]
  repeat (first | constructor | rfl | split)

private theorem moveWsigLeaderSignal_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := moveWsigLeaderSignal l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [moveWsigLeaderSignal]
  repeat (first | constructor | rfl | split)

private theorem moveWsigSignalMove_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := moveWsigSignalMove l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [moveWsigSignalMove]
  repeat (first | constructor | rfl | split)

private theorem moveWsigEchoMove_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := moveWsigEchoMove l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [moveWsigEchoMove]
  repeat (first | constructor | rfl | split)

private theorem moveWsigFinish_inProtocolDomain {ψ κ : Nat}
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := moveWsigFinish l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := moveWsigMoveWrite l r
  let q1 := moveWsigLeaderSignal q0.1 q0.2
  let q2 := moveWsigSignalMove q1.1 q1.2
  have h0 := unchangedStage_inProtocolDomain q0 l r hl hr
    (moveWsigMoveWrite_count_payload l r)
  have h1 := unchangedStage_inProtocolDomain q1 q0.1 q0.2 h0.1 h0.2
    (moveWsigLeaderSignal_count_payload q0.1 q0.2)
  have h2 := unchangedStage_inProtocolDomain q2 q1.1 q1.2 h1.1 h1.2
    (moveWsigSignalMove_count_payload q1.1 q1.2)
  exact unchangedStage_inProtocolDomain
    (moveWsigEchoMove q2.1 q2.2) q2.1 q2.2 h2.1 h2.2
    (moveWsigEchoMove_count_payload q2.1 q2.2)

/-- Algorithm 20 preserves every raw range while clearing or transporting
path3 payloads. -/
theorem moveWsig_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := moveWsig hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [moveWsig_eq_staged]
  let q0 := moveWsigStart l r
  let l1 := moveWsigCheckLast q0.1
  let q1 := moveWsigTransfer l1 q0.2
  have h0 := moveWsigStart_inProtocolDomain l r hl hr
  have hl1 := moveWsigCheckLast_inProtocolDomain q0.1 h0.1
  have h1 := moveWsigTransfer_inProtocolDomain l1 q0.2 hl1 h0.2
  exact moveWsigFinish_inProtocolDomain q1.1 q1.2 h1.1 h1.2

private theorem writeSeqLeaderMove_count_payload {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := writeSeqLeaderMove hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqLeaderMove]
  repeat (first | constructor | rfl | split)

private theorem groupInfoStart_count_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := groupInfoStart hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [groupInfoStart]
  repeat (first | constructor | rfl | split)

private theorem groupInfoSet_count_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := groupInfoSet hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [groupInfoSet]
  repeat (first | constructor | rfl | split)

private theorem groupInfoUnset_count_payload {ψ : Nat}
    (l r : AgentState ψ) :
    let q := groupInfoUnset l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [groupInfoUnset]
  repeat (first | constructor | rfl | split)

private theorem groupInfo_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := groupInfo hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hψ l r
  let q1 := groupInfoSet hψ q0.1 q0.2
  have h0 := unchangedStage_inProtocolDomain q0 l r hl hr
    (groupInfoStart_count_payload hψ l r)
  have h1 := unchangedStage_inProtocolDomain q1 q0.1 q0.2 h0.1 h0.2
    (groupInfoSet_count_payload hψ q0.1 q0.2)
  exact unchangedStage_inProtocolDomain
    (groupInfoUnset q1.1 q1.2) q1.1 q1.2 h1.1 h1.2
    (groupInfoUnset_count_payload q1.1 q1.2)

private theorem writeSeqReady_count_payload {ψ : Nat} (l r : AgentState ψ) :
    let q := writeSeqReady l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqReady, writeSeqSetWriteReady]
  repeat (first | constructor | rfl | split)

private theorem writeSeqCompare_count_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqCompare hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqCompare, writeSeqCheckBit]
  repeat (first | constructor | rfl | split)

private theorem writeSeqCommands_count_payload {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := writeSeqCommands hψ l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [writeSeqCommands, writeSeqSetWriteAct, writeSeqFinalR]
  repeat (first | constructor | rfl | split)

private theorem writeSeqPrepare_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := writeSeqPrepare hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := writeSeqReady l r
  let q1 := writeSeqCompare hψ q0.1 q0.2
  have h0 := unchangedStage_inProtocolDomain q0 l r hl hr
    (writeSeqReady_count_payload l r)
  have h1 := unchangedStage_inProtocolDomain q1 q0.1 q0.2 h0.1 h0.2
    (writeSeqCompare_count_payload hψ q0.1 q0.2)
  exact unchangedStage_inProtocolDomain
    (writeSeqCommands hψ q1.1 q1.2) q1.1 q1.2 h1.1 h1.2
    (writeSeqCommands_count_payload hψ q1.1 q1.2)

private theorem writeSeqLeaderMove_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := writeSeqLeaderMove hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ :=
  unchangedStage_inProtocolDomain (writeSeqLeaderMove hψ l r)
    l r hl hr (writeSeqLeaderMove_count_payload hψ l r)

private theorem writeSeqGenerate_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := writeSeqGenerate hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  simp only [writeSeqGenerate]
  split
  · exact gensigWriteseq_inProtocolDomain hψ l r hl hr
  · exact ⟨hl, hr⟩

/-- Algorithms 16–20 preserve every declared numeric range. -/
theorem writeSeq_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := writeSeq hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := writeSeqLeaderMove hψ l r
  let q1 := groupInfo hψ q0.1 q0.2
  let q2 := writeSeqGenerate hψ q1.1 q1.2
  let q3 := writeSeqPrepare hψ q2.1 q2.2
  let q4 := writeAction hψ q3.1 q3.2
  have h0 := writeSeqLeaderMove_inProtocolDomain hψ l r hl hr
  have h1 := groupInfo_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := writeSeqGenerate_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := writeSeqPrepare_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  have h4 := writeAction_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2
  exact moveWsig_inProtocolDomain hψ q4.1 q4.2 h4.1 h4.2


private theorem domain_of_clean_parts {ψ κ : Nat}
    (input output : AgentState ψ) (hin : input.inProtocolDomain κ)
    (hcount : output.count = input.count)
    (hpath : PayloadView.PathValid ψ output.path)
    (hpath2 : output.path2 = input.path2)
    (hpath3 : output.path3 = input.path3)
    (hpath4 : PayloadView.CleanPathValid ψ output.path4)
    (hpath5 : PayloadView.CleanPathValid ψ output.path5) :
    output.inProtocolDomain κ := by
  change input.count ≤ κ ∧
      PayloadView.PathValid ψ input.path ∧
      PayloadView.Path2Valid ψ input.path2 ∧
      PayloadView.Path3Valid ψ input.path3 ∧
      PayloadView.CleanPathValid ψ input.path4 ∧
      PayloadView.CleanPathValid ψ input.path5 at hin
  change output.count ≤ κ ∧
      PayloadView.PathValid ψ output.path ∧
      PayloadView.Path2Valid ψ output.path2 ∧
      PayloadView.Path3Valid ψ output.path3 ∧
      PayloadView.CleanPathValid ψ output.path4 ∧
      PayloadView.CleanPathValid ψ output.path5
  constructor
  · rw [hcount]
    exact hin.1
  constructor
  · exact hpath
  constructor
  · rw [hpath2]
    exact hin.2.2.1
  constructor
  · rw [hpath3]
    exact hin.2.2.2.1
  exact ⟨hpath4, hpath5⟩

private theorem pathValid_of_domain {ψ κ : Nat} {u : AgentState ψ}
    (hu : u.inProtocolDomain κ) : PayloadView.PathValid ψ u.path := by
  change u.count ≤ κ ∧
      PayloadView.PathValid ψ u.path ∧
      PayloadView.Path2Valid ψ u.path2 ∧
      PayloadView.Path3Valid ψ u.path3 ∧
      PayloadView.CleanPathValid ψ u.path4 ∧
      PayloadView.CleanPathValid ψ u.path5 at hu
  exact hu.2.1

private theorem cleanPath4Valid_of_domain {ψ κ : Nat} {u : AgentState ψ}
    (hu : u.inProtocolDomain κ) : PayloadView.CleanPathValid ψ u.path4 := by
  change u.count ≤ κ ∧
      PayloadView.PathValid ψ u.path ∧
      PayloadView.Path2Valid ψ u.path2 ∧
      PayloadView.Path3Valid ψ u.path3 ∧
      PayloadView.CleanPathValid ψ u.path4 ∧
      PayloadView.CleanPathValid ψ u.path5 at hu
  exact hu.2.2.2.2.1

private theorem cleanPath5Valid_of_domain {ψ κ : Nat} {u : AgentState ψ}
    (hu : u.inProtocolDomain κ) : PayloadView.CleanPathValid ψ u.path5 := by
  change u.count ≤ κ ∧
      PayloadView.PathValid ψ u.path ∧
      PayloadView.Path2Valid ψ u.path2 ∧
      PayloadView.Path3Valid ψ u.path3 ∧
      PayloadView.CleanPathValid ψ u.path4 ∧
      PayloadView.CleanPathValid ψ u.path5 at hu
  exact hu.2.2.2.2.2

private theorem cleanFlipSentinel_valid {ψ bit : Nat} (hψ : ψ > 0) :
    PayloadView.CleanPathValid ψ
      (some ((-1 : Int), 1 - bit)) := by
  simp only [PayloadView.CleanPathValid]
  have hz : (0 : Int) < Int.ofNat ψ := Int.natCast_pos.mpr hψ
  omega

private theorem cleanPath_zeroBit_valid {ψ : Nat} {label : Int} {bit : Nat}
    (h : PayloadView.CleanPathValid ψ (some (label, bit))) :
    PayloadView.CleanPathValid ψ (some (label, 0)) := by
  simp only [PayloadView.CleanPathValid] at h ⊢
  exact ⟨h.1, h.2.1, by omega⟩

/-! ### `cleanSigGenConnect` -/

private theorem cleanSigGenConnect_fixed {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).count = u.count ∧
      (cleanSigGenConnect u).path2 = u.path2 ∧
      (cleanSigGenConnect u).path3 = u.path3 := by
  simp only [cleanSigGenConnect]
  repeat (first | apply And.intro | rfl | split)

private theorem cleanSigGenConnect_ranges {ψ : Nat} (u : AgentState ψ)
    (hp : PayloadView.PathValid ψ u.path)
    (h4 : PayloadView.CleanPathValid ψ u.path4)
    (h5 : PayloadView.CleanPathValid ψ u.path5) :
    PayloadView.PathValid ψ (cleanSigGenConnect u).path ∧
      PayloadView.CleanPathValid ψ (cleanSigGenConnect u).path4 ∧
      PayloadView.CleanPathValid ψ (cleanSigGenConnect u).path5 := by
  cases hpath : u.path with
  | bot =>
    simpa [cleanSigGenConnect, hpath] using And.intro hp (And.intro h4 h5)
  | some label bit =>
    have hp' : label < ψ ∧ bit ≤ 1 := by
      rw [hpath] at hp
      exact hp
    have hfresh :
        PayloadView.CleanPathValid ψ (some (Int.ofNat label, 1)) := by
      simp only [PayloadView.CleanPathValid]
      exact ⟨by simp, Int.ofNat_lt.mpr hp'.1, by omega⟩
    by_cases h0 : label ≠ 0
    · by_cases hlast : label ≠ ψ - 1
      · simpa [cleanSigGenConnect, hpath, h0, hlast] using
          (show PayloadView.PathValid ψ u.path ∧
              PayloadView.CleanPathValid ψ (some (Int.ofNat label, 1)) ∧
              PayloadView.CleanPathValid ψ (some (Int.ofNat label, 1)) from
            ⟨hp, hfresh, hfresh⟩)
      · simpa [cleanSigGenConnect, hpath, h0, hlast] using
          (show PayloadView.PathValid ψ u.path ∧
              PayloadView.CleanPathValid ψ (some (Int.ofNat label, 1)) ∧
              PayloadView.CleanPathValid ψ u.path5 from ⟨hp, hfresh, h5⟩)
    · by_cases hlast : label ≠ ψ - 1
      · simpa [cleanSigGenConnect, hpath, h0, hlast] using
          (show PayloadView.PathValid ψ u.path ∧
              PayloadView.CleanPathValid ψ u.path4 ∧
              PayloadView.CleanPathValid ψ (some (Int.ofNat label, 1)) from
            ⟨hp, h4, hfresh⟩)
      · simpa [cleanSigGenConnect, hpath, h0, hlast] using
          (show PayloadView.PathValid ψ u.path ∧
              PayloadView.CleanPathValid ψ u.path4 ∧
              PayloadView.CleanPathValid ψ u.path5 from ⟨hp, h4, h5⟩)

private theorem cleanSigGenConnect_inProtocolDomain {ψ κ : Nat}
    (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (cleanSigGenConnect u).inProtocolDomain κ := by
  have hf := cleanSigGenConnect_fixed u
  have hv := cleanSigGenConnect_ranges u
    (pathValid_of_domain hu)
    (cleanPath4Valid_of_domain hu)
    (cleanPath5Valid_of_domain hu)
  exact domain_of_clean_parts u _ hu hf.1 hv.1 hf.2.1 hf.2.2
    hv.2.1 hv.2.2

/-! ### Step 3 -/

private theorem cleanSigStep3_fst_eq {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1 = l := by
  simp only [cleanSigStep3]
  repeat (first | rfl | split)

private theorem cleanSigStep3_snd_fixed {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).2.count = r.count ∧
      (cleanSigStep3 l r).2.path = r.path ∧
      (cleanSigStep3 l r).2.path2 = r.path2 ∧
      (cleanSigStep3 l r).2.path3 = r.path3 := by
  simp only [cleanSigStep3]
  repeat (first | apply And.intro | rfl | split)

private theorem cleanSigStep3_snd_clean {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hr4 : PayloadView.CleanPathValid ψ r.path4)
    (hr5 : PayloadView.CleanPathValid ψ r.path5) :
    PayloadView.CleanPathValid ψ (cleanSigStep3 l r).2.path4 ∧
      PayloadView.CleanPathValid ψ (cleanSigStep3 l r).2.path5 := by
  cases hp4 : r.path4 with
  | none =>
      simpa [cleanSigStep3, hp4] using And.intro hr4 hr5
  | some p4 =>
      rcases p4 with ⟨lbl, bit⟩
      cases hlp : l.path with
      | bot =>
          simpa [cleanSigStep3, hp4, hlp] using And.intro hr4 hr5
      | some lLabel lBit =>
          by_cases hsent : lbl ≠ (-1 : Int)
          · by_cases hmatch : lbl ≠ (lLabel : Int) + 1
            · have hnone : PayloadView.CleanPathValid ψ
                  (none : Option (Int × Nat)) := by trivial
              have hnew := cleanFlipSentinel_valid (ψ := ψ) (bit := bit) hψ
              simpa [cleanSigStep3, hp4, hlp, hsent, hmatch] using
                And.intro hnone hnew
            · have hnone : PayloadView.CleanPathValid ψ
                  (none : Option (Int × Nat)) := by trivial
              simpa [cleanSigStep3, hp4, hlp, hsent, hmatch] using
                And.intro hnone hr5
          · simpa [cleanSigStep3, hp4, hlp, hsent] using And.intro hr4 hr5

private theorem cleanSigStep3_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := cleanSigStep3 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := cleanSigStep3 l r
  have hleft : q.1 = l := cleanSigStep3_fst_eq l r
  have hf := cleanSigStep3_snd_fixed l r
  have hc := cleanSigStep3_snd_clean hψ l r
    (cleanPath4Valid_of_domain hr) (cleanPath5Valid_of_domain hr)
  have hp : PayloadView.PathValid ψ q.2.path := by
    rw [hf.2.1]
    exact pathValid_of_domain hr
  change q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  constructor
  · rw [hleft]
    exact hl
  · exact domain_of_clean_parts r q.2 hr hf.1 hp hf.2.2.1 hf.2.2.2
      hc.1 hc.2

/-! ### Step 4 -/

private theorem cleanSigStep4_snd_eq {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).2 = r := by
  simp only [cleanSigStep4]
  repeat (first | rfl | split)

private theorem cleanSigStep4_fst_fixed {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.count = l.count ∧
      (cleanSigStep4 l r).1.path = l.path ∧
      (cleanSigStep4 l r).1.path2 = l.path2 ∧
      (cleanSigStep4 l r).1.path3 = l.path3 := by
  simp only [cleanSigStep4]
  repeat (first | apply And.intro | rfl | split)

private theorem cleanSigStep4_fst_clean {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl4 : PayloadView.CleanPathValid ψ l.path4)
    (hl5 : PayloadView.CleanPathValid ψ l.path5) :
    PayloadView.CleanPathValid ψ (cleanSigStep4 l r).1.path4 ∧
      PayloadView.CleanPathValid ψ (cleanSigStep4 l r).1.path5 := by
  cases hp5 : l.path5 with
  | none =>
      simpa [cleanSigStep4, hp5] using And.intro hl4 hl5
  | some p5 =>
      rcases p5 with ⟨lbl, bit⟩
      cases hrp : r.path with
      | bot =>
          simpa [cleanSigStep4, hp5, hrp] using And.intro hl4 hl5
      | some rLabel rBit =>
          by_cases hsent : lbl ≠ (-1 : Int)
          · by_cases hmatch : lbl ≠ (rLabel : Int) - 1
            · have hnone : PayloadView.CleanPathValid ψ
                  (none : Option (Int × Nat)) := by trivial
              have hnew := cleanFlipSentinel_valid (ψ := ψ) (bit := bit) hψ
              simpa [cleanSigStep4, hp5, hrp, hsent, hmatch] using
                And.intro hnew hnone
            · have hnone : PayloadView.CleanPathValid ψ
                  (none : Option (Int × Nat)) := by trivial
              simpa [cleanSigStep4, hp5, hrp, hsent, hmatch] using
                And.intro hl4 hnone
          · simpa [cleanSigStep4, hp5, hrp, hsent] using And.intro hl4 hl5

private theorem cleanSigStep4_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := cleanSigStep4 l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := cleanSigStep4 l r
  have hright : q.2 = r := cleanSigStep4_snd_eq l r
  have hf := cleanSigStep4_fst_fixed l r
  have hc := cleanSigStep4_fst_clean hψ l r
    (cleanPath4Valid_of_domain hl) (cleanPath5Valid_of_domain hl)
  have hp : PayloadView.PathValid ψ q.1.path := by
    rw [hf.2.1]
    exact pathValid_of_domain hl
  change q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  constructor
  · exact domain_of_clean_parts l q.1 hl hf.1 hp hf.2.2.1 hf.2.2.2
      hc.1 hc.2
  · rw [hright]
    exact hr

/-! ### Step 5 -/

private theorem cleanSigStep5_fixed {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    ((cleanSigStep5 hψ l r).1.count = l.count ∧
      (cleanSigStep5 hψ l r).1.path = l.path ∧
      (cleanSigStep5 hψ l r).1.path2 = l.path2 ∧
      (cleanSigStep5 hψ l r).1.path3 = l.path3 ∧
      (cleanSigStep5 hψ l r).1.path5 = l.path5) ∧
    ((cleanSigStep5 hψ l r).2.count = r.count ∧
      (cleanSigStep5 hψ l r).2.path = r.path ∧
      (cleanSigStep5 hψ l r).2.path2 = r.path2 ∧
      (cleanSigStep5 hψ l r).2.path3 = r.path3 ∧
      (cleanSigStep5 hψ l r).2.path5 = r.path5) := by
  simp only [cleanSigStep5]
  repeat (first | apply And.intro | rfl | split)

private theorem cleanSigStep5_path4 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl4 : PayloadView.CleanPathValid ψ l.path4)
    (hr4 : PayloadView.CleanPathValid ψ r.path4) :
    PayloadView.CleanPathValid ψ (cleanSigStep5 hψ l r).1.path4 ∧
      PayloadView.CleanPathValid ψ (cleanSigStep5 hψ l r).2.path4 := by
  cases hp4 : r.path4 with
  | none =>
      simpa [cleanSigStep5, hp4] using And.intro hl4 hr4
  | some p4 =>
      rcases p4 with ⟨lbl, bit⟩
      have hsame : PayloadView.CleanPathValid ψ (some (lbl, bit)) := by
        simpa [hp4] using hr4
      have hzero := cleanPath_zeroBit_valid hsame
      have hnone : PayloadView.CleanPathValid ψ
          (none : Option (Int × Nat)) := by trivial
      by_cases hlabel : l.label = (⟨0, hψ⟩ : Fin ψ)
      · by_cases hbit : bit = 1
        · simpa [cleanSigStep5, hp4, hlabel, hbit] using
            And.intro hzero hnone
        · simpa [cleanSigStep5, hp4, hlabel, hbit] using
            And.intro hnone hnone
      · simpa [cleanSigStep5, hp4, hlabel] using
          And.intro hsame hnone

private theorem cleanSigStep5_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := cleanSigStep5 hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := cleanSigStep5 hψ l r
  have hf := cleanSigStep5_fixed hψ l r
  have h4 := cleanSigStep5_path4 hψ l r
    (cleanPath4Valid_of_domain hl) (cleanPath4Valid_of_domain hr)
  have hp1 : PayloadView.PathValid ψ q.1.path := by
    rw [hf.1.2.1]
    exact pathValid_of_domain hl
  have hp2 : PayloadView.PathValid ψ q.2.path := by
    rw [hf.2.2.1]
    exact pathValid_of_domain hr
  have h51 : PayloadView.CleanPathValid ψ q.1.path5 := by
    rw [hf.1.2.2.2.2]
    exact cleanPath5Valid_of_domain hl
  have h52 : PayloadView.CleanPathValid ψ q.2.path5 := by
    rw [hf.2.2.2.2.2]
    exact cleanPath5Valid_of_domain hr
  change q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  exact ⟨
    domain_of_clean_parts l q.1 hl hf.1.1 hp1 hf.1.2.2.1
      hf.1.2.2.2.1 h4.1 h51,
    domain_of_clean_parts r q.2 hr hf.2.1 hp2 hf.2.2.2.1
      hf.2.2.2.2.1 h4.2 h52⟩

/-! ### Step 6 -/

private theorem cleanSigStep6_fixed {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    ((cleanSigStep6 hψ l r).1.count = l.count ∧
      (cleanSigStep6 hψ l r).1.path = l.path ∧
      (cleanSigStep6 hψ l r).1.path2 = l.path2 ∧
      (cleanSigStep6 hψ l r).1.path3 = l.path3 ∧
      (cleanSigStep6 hψ l r).1.path4 = l.path4) ∧
    ((cleanSigStep6 hψ l r).2.count = r.count ∧
      (cleanSigStep6 hψ l r).2.path = r.path ∧
      (cleanSigStep6 hψ l r).2.path2 = r.path2 ∧
      (cleanSigStep6 hψ l r).2.path3 = r.path3 ∧
      (cleanSigStep6 hψ l r).2.path4 = r.path4) := by
  simp only [cleanSigStep6]
  repeat (first | apply And.intro | rfl | split)

private theorem cleanSigStep6_path5 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl5 : PayloadView.CleanPathValid ψ l.path5)
    (hr5 : PayloadView.CleanPathValid ψ r.path5) :
    PayloadView.CleanPathValid ψ (cleanSigStep6 hψ l r).1.path5 ∧
      PayloadView.CleanPathValid ψ (cleanSigStep6 hψ l r).2.path5 := by
  cases hp5 : l.path5 with
  | none =>
      simpa [cleanSigStep6, hp5] using And.intro hl5 hr5
  | some p5 =>
      rcases p5 with ⟨lbl, bit⟩
      have hsame : PayloadView.CleanPathValid ψ (some (lbl, bit)) := by
        simpa [hp5] using hl5
      have hzero := cleanPath_zeroBit_valid hsame
      have hnone : PayloadView.CleanPathValid ψ
          (none : Option (Int × Nat)) := by trivial
      by_cases hlabel : r.label = (⟨ψ - 1, by omega⟩ : Fin ψ)
      · by_cases hbit : bit = 1
        · simpa [cleanSigStep6, hp5, hlabel, hbit] using
            And.intro hnone hzero
        · simpa [cleanSigStep6, hp5, hlabel, hbit] using
            And.intro hnone hnone
      · simpa [cleanSigStep6, hp5, hlabel] using
          And.intro hnone hsame

private theorem cleanSigStep6_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := cleanSigStep6 hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q := cleanSigStep6 hψ l r
  have hf := cleanSigStep6_fixed hψ l r
  have h5 := cleanSigStep6_path5 hψ l r
    (cleanPath5Valid_of_domain hl) (cleanPath5Valid_of_domain hr)
  have hp1 : PayloadView.PathValid ψ q.1.path := by
    rw [hf.1.2.1]
    exact pathValid_of_domain hl
  have hp2 : PayloadView.PathValid ψ q.2.path := by
    rw [hf.2.2.1]
    exact pathValid_of_domain hr
  have h41 : PayloadView.CleanPathValid ψ q.1.path4 := by
    rw [hf.1.2.2.2.2]
    exact cleanPath4Valid_of_domain hl
  have h42 : PayloadView.CleanPathValid ψ q.2.path4 := by
    rw [hf.2.2.2.2.2]
    exact cleanPath4Valid_of_domain hr
  change q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ
  exact ⟨
    domain_of_clean_parts l q.1 hl hf.1.1 hp1 hf.1.2.2.1
      hf.1.2.2.2.1 h41 h5.1,
    domain_of_clean_parts r q.2 hr hf.2.1 hp2 hf.2.2.2.1
      hf.2.2.2.2.1 h42 h5.2⟩

/-! ### `cleanSigCleanApply`: path may clear -/

private theorem cleanSigCleanApply_fixed {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).count = u.count ∧
      (cleanSigCleanApply u).path2 = u.path2 ∧
      (cleanSigCleanApply u).path3 = u.path3 := by
  simp only [cleanSigCleanApply]
  repeat (first | apply And.intro | rfl | split)

private theorem cleanSigCleanApply_shape {ψ : Nat} (u : AgentState ψ) :
    ((cleanSigCleanApply u).path = u.path ∨
        (cleanSigCleanApply u).path = .bot) ∧
      ((cleanSigCleanApply u).path4 = u.path4 ∨
        (cleanSigCleanApply u).path4 = none) ∧
      ((cleanSigCleanApply u).path5 = u.path5 ∨
        (cleanSigCleanApply u).path5 = none) := by
  simp only [cleanSigCleanApply]
  repeat (first
    | apply And.intro
    | exact Or.inl rfl
    | exact Or.inr rfl
    | split)

private theorem cleanSigCleanApply_ranges {ψ : Nat} (u : AgentState ψ)
    (hp : PayloadView.PathValid ψ u.path)
    (h4 : PayloadView.CleanPathValid ψ u.path4)
    (h5 : PayloadView.CleanPathValid ψ u.path5) :
    PayloadView.PathValid ψ (cleanSigCleanApply u).path ∧
      PayloadView.CleanPathValid ψ (cleanSigCleanApply u).path4 ∧
      PayloadView.CleanPathValid ψ (cleanSigCleanApply u).path5 := by
  have hs := cleanSigCleanApply_shape u
  constructor
  · rcases hs.1 with heq | hbot
    · rw [heq]
      exact hp
    · rw [hbot]
      trivial
  constructor
  · rcases hs.2.1 with heq | hnone
    · rw [heq]
      exact h4
    · rw [hnone]
      trivial
  · rcases hs.2.2 with heq | hnone
    · rw [heq]
      exact h5
    · rw [hnone]
      trivial

private theorem cleanSigCleanApply_inProtocolDomain {ψ κ : Nat}
    (u : AgentState ψ) (hu : u.inProtocolDomain κ) :
    (cleanSigCleanApply u).inProtocolDomain κ := by
  have hf := cleanSigCleanApply_fixed u
  have hv := cleanSigCleanApply_ranges u
    (pathValid_of_domain hu)
    (cleanPath4Valid_of_domain hu)
    (cleanPath5Valid_of_domain hu)
  exact domain_of_clean_parts u _ hu hf.1 hv.1 hf.2.1 hf.2.2
    hv.2.1 hv.2.2

/-- Algorithm 5 preserves the declared numeric ranges.  In particular,
`cleanSigCleanApply` is allowed to clear `path`; no path-unchanged hypothesis
is used. -/
theorem cleanSig_inProtocolDomain {ψ κ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (hl : l.inProtocolDomain κ)
    (hr : r.inProtocolDomain κ) :
    let q := cleanSig hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  let q1 := cleanSigStep3 l0 r0
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hψ q2.1 q2.2
  let q4 := cleanSigStep6 hψ q3.1 q3.2
  have hl0 := cleanSigGenConnect_inProtocolDomain l hl
  have hr0 := cleanSigGenConnect_inProtocolDomain r hr
  have h1 := cleanSigStep3_inProtocolDomain hψ l0 r0 hl0 hr0
  have h2 := cleanSigStep4_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := cleanSigStep5_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  have h4 := cleanSigStep6_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2
  change (cleanSigCleanApply q4.1).inProtocolDomain κ ∧
    (cleanSigCleanApply q4.2).inProtocolDomain κ
  exact ⟨cleanSigCleanApply_inProtocolDomain q4.1 h4.1,
    cleanSigCleanApply_inProtocolDomain q4.2 h4.2⟩

private theorem ppllSaturatedBeforeCheck_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllSaturatedBeforeCheck hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := pPsi hψ l r
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  have h0 := pPsi_inProtocolDomain hψ l r hl hr
  have h1 := genSigSaturated_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := cleanSig_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := eliminateSig_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  exact sigMove_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2

private theorem ppllSaturatedBeforeEliminate_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllSaturatedBeforeEliminate hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := ppllSaturatedBeforeCheck hψ κ l r
  let q1 := checkSig hψ q0.1 q0.2
  let q2 := disappear hψ q1.1 q1.2
  let q3 := compareSig hψ q2.1 q2.2
  have h0 := ppllSaturatedBeforeCheck_inProtocolDomain hψ l r hl hr
  have h1 := checkSig_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := disappear_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  have h3 := compareSig_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2
  exact suppressSig_inProtocolDomain hψ q3.1 q3.2 h3.1 h3.2

private theorem ppllSaturatedBeforeWrite_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllSaturatedBeforeWrite hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := ppllSaturatedBeforeEliminate hψ κ l r
  have h0 := ppllSaturatedBeforeEliminate_inProtocolDomain hψ l r hl hr
  exact eliminateLeadersNoCollision_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2

/-- The complete explicit repaired audit transition is closed on Algorithm 1's
numeric value domain. This theorem is independent of the future bounded
transition and is the noncircular premise used to define it. -/
theorem ppllSaturatedNoCollision_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllSaturatedNoCollision hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := ppllSaturatedBeforeWrite hψ κ l r
  have h0 := ppllSaturatedBeforeWrite_inProtocolDomain hψ l r hl hr
  exact writeSeq_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2

/-! ## Domain closure of the integrated T9 candidate -/

private theorem cmpUpdateNoSourceRearm_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := cmpUpdateNoSourceRearm hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := if l.label = ⟨0, hψ⟩ ∧ l.state ≠ .depart then
    { l with state := .congest } else l
  have hl0 : l0.inProtocolDomain κ := by
    apply domain_of_count_payload_eq l l0 hl
    · dsimp only [l0]
      split <;> rfl
    · dsimp only [l0]
      split <;> rfl
  let q0 := cmpUpdatePropagate hψ l0 r
  have h0 := cmpUpdatePropagate_inProtocolDomain hψ l0 r hl0 hr
  exact ⟨cmpUpdateSetPath2_inProtocolDomain hψ q0.1 h0.1, h0.2⟩

/-- The no-source-rearm COMPARE candidate preserves every numeric range. -/
theorem compareSigNoSourceRearm_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := compareSigNoSourceRearm hψ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let l0 := compareSigInit l
  have hl0 := compareSigInit_inProtocolDomain l hl
  change (match l0.path with
    | .bot => (l0, r)
    | .some _ _ =>
      match r.path with
      | .some _ _ =>
        let q := cmpUpdateNoSourceRearm hψ l0 r
        compareSigDispatch hψ q.1 q.2
      | .bot => (l0, r)).1.inProtocolDomain κ ∧
    (match l0.path with
    | .bot => (l0, r)
    | .some _ _ =>
      match r.path with
      | .some _ _ =>
        let q := cmpUpdateNoSourceRearm hψ l0 r
        compareSigDispatch hψ q.1 q.2
      | .bot => (l0, r)).2.inProtocolDomain κ
  cases hlp : l0.path with
  | bot => exact ⟨hl0, hr⟩
  | some _ _ =>
    cases hrp : r.path with
    | bot => exact ⟨hl0, hr⟩
    | some _ _ =>
      let q0 := cmpUpdateNoSourceRearm hψ l0 r
      have h0 := cmpUpdateNoSourceRearm_inProtocolDomain hψ l0 r hl0 hr
      exact compareSigDispatch_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2

private theorem ppllIntegratedBeforeSuppress_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllIntegratedBeforeSuppress hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := ppllSaturatedBeforeCheck hψ κ l r
  let q1 := checkSig hψ q0.1 q0.2
  let q2 := disappear hψ q1.1 q1.2
  have h0 := ppllSaturatedBeforeCheck_inProtocolDomain hψ l r hl hr
  have h1 := checkSig_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := disappear_inProtocolDomain hψ q1.1 q1.2 h1.1 h1.2
  exact compareSigNoSourceRearm_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2

/-- The integrated T9 candidate remains closed on the exact bounded value
domain. -/
theorem ppllIntegratedRepair_inProtocolDomain {ψ κ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := ppllIntegratedRepair hψ κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let q0 := ppllIntegratedBeforeSuppress hψ κ l r
  let q1 := suppressSig hψ q0.1 q0.2
  let q2 := eliminateLeadersNoCollision hψ q1.1 q1.2
  have h0 := ppllIntegratedBeforeSuppress_inProtocolDomain hψ l r hl hr
  have h1 := suppressSig_inProtocolDomain hψ q0.1 q0.2 h0.1 h0.2
  have h2 := eliminateLeadersNoCollision_inProtocolDomain
    hψ q1.1 q1.2 h1.1 h1.2
  exact writeSeq_inProtocolDomain hψ q2.1 q2.2 h2.1 h2.2

end PPLLDomain
