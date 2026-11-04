import Leader.Wu.Birth.CheckChainStages

set_option autoImplicit false

/-! # CHECK rows of a train at a smaller group: the `less` outcome

A train aligned at a group whose identifier is smaller at the first differing label `k` meets, at that label, a cell
whose own bit is `0` while the carried path bit is `1`.  On the CHECK stage (Algorithm 11):
* `checkSig_less_row`: an `equal` initiator below the terminal and a responder at label `k` with a mismatched path
  (cell bit smaller than path bit) give an unchanged initiator and a responder in `less` holding the action-6
  signal `⟨0, 0, 0, 6⟩`, with path and label unchanged;
* `checkSig_less_first`: at label 0 a `CHECK_ready` initiator with a mismatched path bit turns `less` with the
  action-6 signal, the responder being readied or left alone as in the first chain row.
These are the first steps of a passage (less, action 6 to label 0, toss, toss_done with action 5, departure).
-/

namespace BirthCheckChainR1Less

open PPLL

variable {ψ : Nat}

private theorem checkBit_less (b : Bool) (pb : Nat) (h : (if b then 1 else 0) < pb) : checkBit b pb = .less := by
  unfold checkBit
  have h1 : (if b then 1 else 0) ≠ pb := by omega
  have h2 : ¬ (if b then 1 else 0) > pb := by omega
  simp [h1, h2]

theorem checkSig_less_row (hψ : ψ > 0) (l r : AgentState ψ) (k pb : Nat)
    (hl : l.state = .equal) (hlab : l.label.val < ψ - 1)
    (hrp : r.path = .some k pb) (hrlab : r.label.val = k)
    (hrd : r.state ≠ .depart) (hre : r.state ≠ .equal) (hrg : r.state ≠ .larger) (hrs : r.state ≠ .less)
    (hbit : (if r.bit then 1 else 0) < pb) :
    (checkSig hψ l r).1 = l ∧ (checkSig hψ l r).2.state = .less ∧
      (checkSig hψ l r).2.path2 = some ⟨0, 0, 0, 6⟩ ∧ (checkSig hψ l r).2.path = r.path ∧
      (checkSig hψ l r).2.label = r.label := by
  have hless := checkBit_less r.bit pb hbit
  refine ⟨?_, ?_⟩
  · cases hpath : l.path with
    | bot =>
        simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigSetResult, hpath, hl]
    | some a b =>
        simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigSetResult, hpath, hl]
        split <;> simp_all
  · have hready : checkSigSetReady r = { r with state := .CHECK_ready } := by
      unfold checkSigSetReady; rw [hrp]; simp [hrlab, hrd, hre, hrg, hrs]
    have hL : checkSigCheckL hψ (checkSigSetReady l) = checkSigSetReady l := by
      cases hpath : l.path with
      | bot => simp [checkSigSetReady, checkSigCheckL, hpath]
      | some a b =>
          simp [checkSigSetReady, checkSigCheckL, hpath, hl]
          split <;> simp_all
    have hLst : (checkSigSetReady l).state = .equal := by
      cases hpath : l.path with
      | bot => simp [checkSigSetReady, hpath, hl]
      | some a b => simp [checkSigSetReady, hpath, hl]
    have hLlab : (checkSigSetReady l).label = l.label := by
      unfold checkSigSetReady; split <;> (try split) <;> rfl
    have hR : checkSigCheckR hψ (checkSigSetReady l) { r with state := .CHECK_ready } =
        { r with state := .less } := by
      unfold checkSigCheckR
      simp [hrp, hLst, hLlab, hlab, hless]
    unfold checkSig
    simp only [hready, hL, hR]
    simp [checkSigSetResult]

theorem checkSig_less_first (hψ : ψ > 0) (l r : AgentState ψ) (pb : Nat)
    (hl0 : l.label = ⟨0, hψ⟩) (hlp : l.path = .some 0 pb)
    (hld : l.state ≠ .depart) (hle : l.state ≠ .equal) (hlg : l.state ≠ .larger) (hls : l.state ≠ .less)
    (hbit : (if l.bit then 1 else 0) < pb) :
    (checkSig hψ l r).1.state = .less ∧ (checkSig hψ l r).1.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (checkSig hψ l r).1.path = l.path ∧ (checkSig hψ l r).1.label = l.label := by
  have hless := checkBit_less l.bit pb hbit
  have hl0v : l.label.val = 0 := by rw [hl0]
  have hready : checkSigSetReady l = { l with state := .CHECK_ready } := by
    unfold checkSigSetReady; rw [hlp]; simp [hl0v, hld, hle, hlg, hls]
  have hL : checkSigCheckL hψ { l with state := .CHECK_ready } = { l with state := .less } := by
    unfold checkSigCheckL; simp [hlp, hl0, hless]
  unfold checkSig
  simp only [hready, hL]
  simp [checkSigSetResult]

end BirthCheckChainR1Less
