import Leader.Wu.ZeroDivisible.OverwritingGeneration

/-!
An exact local bootstrap fact for the original comparison stage. The carried
main paths are at the last/zero boundary, the states are compare2/compare1,
and both comparison-token slots are empty. No physical-label, leader, or
other ancillary-field assumptions are made. This is a statement about
`compareLifecycle` alone, before any other full-pipeline stage.
-/

namespace PPLLAstraR5BootstrapCompare

open PPLL PPLLFableDesignR1 PPLLAstraDesign3

set_option autoImplicit false

def canonicalA2 (ψ : Nat) : Path2Info := ⟨0, 0, ψ - 1, 2⟩

private theorem pred_mod_self {ψ : Nat} (h2 : 2 ≤ ψ) :
    (ψ - 1) % ψ = ψ - 1 := by
  apply Nat.mod_eq_of_lt
  omega

private theorem preclear_bootstrap {ψ : Nat} (l : AgentState ψ)
    (hlp : ∃ bl : Nat, l.path = .some (ψ - 1) bl) :
    (match l.path with
      | .bot => if l.state = .produce then l else { l with state := .none }
      | .some _ _ => l) = l := by
  rcases hlp with ⟨bl, hlp⟩
  simp [hlp]

private theorem maintain_bootstrap {ψ : Nat} (h2 : 2 ≤ ψ)
    (l r : AgentState ψ)
    (hlp : ∃ bl : Nat, l.path = .some (ψ - 1) bl)
    (hrp : ∃ br : Nat, r.path = .some 0 br)
    (hls : l.state = .compare2) (hrs : r.state = .compare1) :
    maintain l r = (l, r) := by
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  have hm : (ψ - 1) % ψ = ψ - 1 := pred_mod_self h2
  simp [maintain, hlp, hrp, hls, hrs, lockedState, lockerState, hm]

private theorem completeWave_bootstrap {ψ : Nat} (l r : AgentState ψ)
    (hlp : ∃ bl : Nat, l.path = .some (ψ - 1) bl)
    (hrp : ∃ br : Nat, r.path = .some 0 br)
    (hls : l.state = .compare2) (hrs : r.state = .compare1) :
    completeWave l r = (l, r) := by
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  simp [completeWave, hlp, hrp, hls, hrs, lockedState]

private theorem wave_bootstrap {ψ : Nat} (l r : AgentState ψ)
    (hlp : ∃ bl : Nat, l.path = .some (ψ - 1) bl)
    (hrp : ∃ br : Nat, r.path = .some 0 br)
    (hls : l.state = .compare2) (hrs : r.state = .compare1)
    (hlt : l.path2 = none) (hrt : r.path2 = none) :
    wave l r = ({ l with path2 := some (canonicalA2 ψ) }, r) := by
  rcases hlp with ⟨bl, hlp⟩
  rcases hrp with ⟨br, hrp⟩
  simp [wave, canonicalA2, hlp, hrp, hls, hrs, hlt, hrt,
    lockedState, lockerState]

private theorem dropStray_bootstrap {ψ : Nat} (l r : AgentState ψ)
    (hrt : r.path2 = none) :
    dropStray { l with path2 := some (canonicalA2 ψ) } r =
      ({ l with path2 := some (canonicalA2 ψ) }, r) := by
  simp [dropStray, canonicalA2, hrt]

private theorem landBackward_bootstrap {ψ : Nat} (h2 : 2 ≤ ψ)
    (l : AgentState ψ) :
    landBackward { l with path2 := some (canonicalA2 ψ) } =
      { l with path2 := some (canonicalA2 ψ) } := by
  have hne : ψ - 1 ≠ 0 := by omega
  cases l.path <;> simp [landBackward, canonicalA2, hne]

private theorem landForward_none {ψ : Nat} (κ : Nat) (r : AgentState ψ)
    (hrt : r.path2 = none) :
    landForward κ false true r = r := by
  simp [landForward, hrt]

/-- Exact output of the original local comparison lifecycle at the last/zero
boundary. In particular, arbitrary physical labels and leader bits are
preserved because the only change is the left `path2` field. -/
theorem compareLifecycle_bootstrap {ψ : Nat} (h4 : 4 ≤ ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hlp : ∃ bl : Nat, l.path = .some (ψ - 1) bl)
    (hrp : ∃ br : Nat, r.path = .some 0 br)
    (hls : l.state = .compare2) (hrs : r.state = .compare1)
    (hlt : l.path2 = none) (hrt : r.path2 = none) :
    compareLifecycle κ l r =
      ({ l with path2 := some (canonicalA2 ψ) }, r) := by
  have h2 : 2 ≤ ψ := by omega
  have hm := maintain_bootstrap h2 l r hlp hrp hls hrs
  have hc := completeWave_bootstrap l r hlp hrp hls hrs
  have hw := wave_bootstrap l r hlp hrp hls hrs hlt hrt
  have hs := dropStray_bootstrap l r hrt
  have hb := landBackward_bootstrap h2 l
  have hf := landForward_none κ r hrt
  rcases hlp with ⟨bl, hlp⟩
  simp [compareLifecycle, hlp, hm, hc, hw, hs, hb, hf]
  have hne : ψ - 1 ≠ 0 := by omega
  simp [dropStray, landBackward, landForward, canonicalA2, hrt, hne]

#check @compareLifecycle_bootstrap
#print axioms compareLifecycle_bootstrap

end PPLLAstraR5BootstrapCompare
