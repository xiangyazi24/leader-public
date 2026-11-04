import Leader.Wu.ZeroDivisible.CheckRepair

/-! The exact R5 cut immediately before R1 `wave`, with its original inputs. -/

namespace PPLLAstraR5SelectedWave

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
open PPLLPostElectionGuard PPLLFableDesignR1
open PPLLAstraDesign2 PPLLAstraDesign3

set_option autoImplicit false

def HasToken {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.path2 ≠ none ∨ q.2.path2 ≠ none

def CutShape {ψ : Nat} (q : AgentState ψ × AgentState ψ) : Prop :=
  q.1.state = .compare2 ∧
    (q.2.state = .lock ∨ q.2.state = .compare1)

/-- Literal R5 prefix through ReadyAck repair, immediately before comparison. -/
def beforeCompare {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hψ l r
  let q := PPLLFableZDiv.genSigOverwrite hψ κ true 0 q.1 q.2
  let q := cleanSource hψ q.1 q.2
  let q := releaseSource hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := PPLLFableZDiv.moveSourceF hψ PPLLAstraR5Repair.sourceCfg q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  let q := PPLLAstraR5Repair.checkSource hψ c q.1 q.2
  let q := disappear hψ q.1 q.2
  repair .readyAck q.1 q.2

structure RowCut (ψ : Nat) where
  originalL : AgentState ψ
  originalR : AgentState ψ
  pair : AgentState ψ × AgentState ψ

/-- Stop after maintain/completeWave, immediately before R1.wave. -/
def rowCut {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l0 r0 : AgentState ψ) : RowCut ψ :=
  let a := beforeCompare hψ κ c l0 r0
  let l :=
    match a.1.path with
    | .bot => if a.1.state = .produce then a.1
              else { a.1 with state := .none }
    | .some _ _ => a.1
  let b := maintain l a.2
  let d := completeWave b.1 b.2
  { originalL := l0, originalR := r0, pair := d }

/-- Exact actual suffix from the cut, including conserve on original inputs. -/
def finishCut {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (x : RowCut ψ) : AgentState ψ × AgentState ψ :=
  let q := wave x.pair.1 x.pair.2
  let q := dropStray q.1 q.2
  let q := (landBackward q.1, landForward κ false true q.2)
  let q := suppressSigResetKill hψ q.1 q.2
  let q := k4Kernel hψ q.1 q.2
  let q := writeWithBundle hψ q.1 q.2
  conserve .head x.originalL x.originalR q

section Factor

-- Keep unchanged protocol stages opaque while checking the structural cut.
-- This prevents kernel comparison from expanding nested AgentState records.
attribute [local irreducible] PPLLPostElectionGuard.pPsiProbeWall
  PPLLFableZDiv.genSigOverwrite PPLLAstraDesign3.cleanSource
  PPLLAstraDesign3.releaseSource PPLL.eliminateSig
  PPLLFableZDiv.moveSourceF PPLLBirthPatchM2.dropStale
  PPLLPostElectionGuard.preCheckReset PPLLAstraDesign3.normalizeReady
  PPLLAstraR5Repair.checkSource PPLL.disappear
  PPLLAstraDesign3.repair PPLLFableDesignR1.maintain
  PPLLAstraDesign3.completeWave PPLLFableDesignR1.wave
  PPLLFableDesignR1.dropStray PPLLFableDesignR1.landBackward
  PPLLFableDesignR1.landForward PPLLPostElectionGuard.suppressSigResetKill
  PPLLPostElectionGuard.k4Kernel PPLLAstraDesign2.writeWithBundle
  PPLLAstraDesign2.conserve

private theorem beforeElimination_eq_cut {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    PPLLAstraR5Repair.beforeElimination hψ κ c l r =
      let x := rowCut hψ κ c l r
      let q := wave x.pair.1 x.pair.2
      let q := dropStray q.1 q.2
      let q := (landBackward q.1, landForward κ false true q.2)
      suppressSigResetKill hψ q.1 q.2 := by
  rfl

theorem pipeline_eq_finishCut {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    PPLLAstraR5Repair.pipeline hψ κ c l r =
      finishCut hψ κ (rowCut hψ κ c l r) := by
  rw [PPLLAstraR5Repair.pipeline, beforeElimination_eq_cut]
  rfl

end Factor

/-- The boundary C2/head wave is exactly inert when either token slot is live.
The saved token fields and all other agent fields remain arbitrary. -/
theorem wave_eq_of_selected_cut {ψ : Nat} (_hψ : 0 < ψ)
    (q : AgentState ψ × AgentState ψ)
    (hlp : ∃ bl, q.1.path = .some (ψ - 1) bl)
    (hrp : ∃ br, q.2.path = .some 0 br)
    (hs : CutShape q) (ht : HasToken q) :
    wave q.1 q.2 = q := by
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  rcases hs with ⟨hC2, hR⟩
  rcases hR with hR | hR
  · rcases ht with ht | ht
    · cases htok : q.1.path2 with
      | none => exact False.elim (ht htok)
      | some t => simp [wave, hlp, hrp, hC2, hR, htok,
          lockedState, lockerState]
    · cases htok : q.2.path2 with
      | none => exact False.elim (ht htok)
      | some t => simp [wave, hlp, hrp, hC2, hR, htok,
          lockedState, lockerState]
  · rcases ht with ht | ht
    · cases htok : q.1.path2 with
      | none => exact False.elim (ht htok)
      | some t => simp [wave, hlp, hrp, hC2, hR, htok,
          lockedState, lockerState]
    · cases htok : q.2.path2 with
      | none => exact False.elim (ht htok)
      | some t => simp [wave, hlp, hrp, hC2, hR, htok,
          lockedState, lockerState]

#check pipeline_eq_finishCut
#check wave_eq_of_selected_cut
#print axioms pipeline_eq_finishCut
#print axioms wave_eq_of_selected_cut

end PPLLAstraR5SelectedWave
