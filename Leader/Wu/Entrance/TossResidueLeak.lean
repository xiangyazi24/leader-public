import Leader.Wu.Birth.CheckPermitRepair

/-! The action-6 residue leak under the R1 row at the parameter witness psi = 3, kappa = 3, tau = 48.

`u0`: the tossing label-0 carrier of segment j+1 with the action-6 `path2` its CHECK result created.  The R1 row on the
edge (label 2 of segment j, u0) moves the residue into the label-2 cell (SIGMOVE step 4 runs before DISAPPEAR) while
u0 becomes `toss_done` (`r1_leak_first`); two further R1 rows carry it to segment j's label-0 cell, which is left in
`toss` with the residue (`r1_leak_third`): a lottery game in a segment whose own comparison never produced `less`.
This is the failure mode of the front edge seen in run/verification/b6-r1-ready-episodes.txt.
-/

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthWaitPassive

set_option autoImplicit false

namespace B6TossResidueLeakR1

def tossCore : AgentState 3 :=
  { BirthCheckPermitRepair.withPath 0 true with state := .toss, path2 := some ⟨0, 0, 0, 6⟩ }

theorem dom_toss : tossCore.inProtocolDomain 3 := by
  simp [tossCore, BirthCheckPermitRepair.withPath, cell, BirthCheckPermitRepair.regsB, AgentState.inProtocolDomain]

def u0 : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain tossCore dom_toss, false⟩, Fin.last 48⟩

theorem r1_leak_first :
    let q := BirthCheckPermitRepair.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (BirthCheckPermitRepair.tok 2 false false) u0
    q.1.core.core.erase.path2 = some ⟨0, 0, 0, 6⟩ ∧ q.2.core.core.state = .toss_done := by
  decide +kernel

theorem r1_leak_third :
    let q1 := BirthCheckPermitRepair.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (BirthCheckPermitRepair.tok 2 false false) u0
    let q2 := BirthCheckPermitRepair.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (BirthCheckPermitRepair.tok 1 true false) q1.1
    let q3 := BirthCheckPermitRepair.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (BirthCheckPermitRepair.tok 0 true false) q2.1
    q3.1.core.core.state = .toss ∧ q3.1.core.core.erase.path2 = some ⟨0, 0, 0, 6⟩ := by
  decide +kernel

/-! ## Two further escape variants of the same SIGMOVE order -/

/-- A `less` result just written at label 0 (Algorithm 11 line 13), before any SIGMOVE application. -/
def lessCore : AgentState 3 :=
  { BirthCheckPermitRepair.withPath 0 true with state := .less, path2 := some ⟨0, 0, 0, 6⟩ }

theorem dom_less : lessCore.inProtocolDomain 3 := by
  simp [lessCore, BirthCheckPermitRepair.withPath, cell, BirthCheckPermitRepair.regsB, AgentState.inProtocolDomain]

def lessU0 : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain lessCore dom_less, false⟩, Fin.last 48⟩

/-- Escape before application: when the fresh action-6 signal's first interaction has u0 as responder, SIGMOVE moves
it into the previous segment's label-2 cell and u0 never tosses. -/
theorem r1_less_escapes_before_toss :
    let q := BirthCheckPermitRepair.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      (BirthCheckPermitRepair.tok 2 false false) lessU0
    q.1.core.core.erase.path2 = some ⟨0, 0, 0, 6⟩ ∧ q.2.core.core.state ≠ .toss := by
  decide +kernel

/-- An action-4 residue on a pathless label-2 cell (the observed back failure): as initiator it moves the signal right
into the next segment's label-0 carrier. -/
def elimCore : AgentState 3 :=
  { cell (BirthCheckPermitRepair.regsB 2 false) with state := .eliminate_signal, path2 := some ⟨0, 0, 0, 4⟩ }

theorem dom_elim : elimCore.inProtocolDomain 3 := by
  simp [elimCore, cell, BirthCheckPermitRepair.regsB, AgentState.inProtocolDomain]

def elimBack : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain elimCore dom_elim, false⟩, Fin.last 48⟩

theorem r1_eliminate_residue_escapes_right :
    let q := BirthCheckPermitRepair.row (ψ := 3) (κ := 3) (τ := 48) (width := 2) (by decide) (by decide) (by decide)
      elimBack (BirthCheckPermitRepair.tok 0 true false)
    q.2.core.core.erase.path2 = some ⟨0, 0, 0, 4⟩ := by
  decide +kernel

end B6TossResidueLeakR1
