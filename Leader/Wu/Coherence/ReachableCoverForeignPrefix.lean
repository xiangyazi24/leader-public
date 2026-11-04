import Leader.Wu.Coherence.ReachableCover

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableCover2

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableScrubL R2CoherenceV31ReachableScrubL3
open R2CoherenceV31ReachableCover R2CoherenceV31PhaseMainClear

variable {n ψ κ τ : Nat}

private theorem modL_c2 (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem modR_c2 (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem prefixPos_eq_groupPos_c2
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat)
    (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k =
      R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by dsimp [a]; exact Nat.mod_lt _ hn
  have hb : b < n := by dsimp [b]; exact Nat.mod_lt _ hn
  have hA : n ≤ A := by dsimp [A]; omega
  have hmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n = (((A - (L % n)) % n + k) % n)
  symm
  by_cases hs : a + b < n
  · have hm : L % n = a + b := hmod.trans (Nat.mod_eq_of_lt hs)
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n := modL_c2 _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_c2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have hx : A - (a + b) + b = A - a := by omega
        rw [hx]
  · have hge : n ≤ a + b := by omega
    have hlt : a + b - n < n := by omega
    have hm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hge
        _ = a + b - n := Nat.mod_eq_of_lt hlt
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n := modL_c2 _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_c2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have hx : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hx, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

private theorem back_zero_c2 (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.back ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem pending_successor_groupStart_c2
    (ring : DirectedRing n) (D : FC n ψ κ τ) (owner : Fin n)
    (hp : PendingOpenROwnerV31 ring D owner) :
    R2Coherence.groupStart ring (eraseCfgV3 D)
      (ring.rightNeighbor owner) = owner := by
  have h0 : (raw (D owner)).label.val = 0 := by
    simpa [atRootB] using hp.2.2
  have h1 : (raw (D (ring.rightNeighbor owner))).label.val =
      (raw (D owner)).label.val + 1 := by
    simpa [successorB] using hp.2.1
  unfold R2Coherence.groupStart
  change R2Coherence.back ring (ring.rightNeighbor owner)
      (raw (D (ring.rightNeighbor owner))).label.val = owner
  rw [h1, h0]
  calc
    R2Coherence.back ring (ring.rightNeighbor owner) (0 + 1) =
        R2Coherence.back ring owner 0 := by
      simpa using
        (R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
          ring owner 0)
    _ = owner := back_zero_c2 ring owner

/-- Exact remaining incoming-overlap debt.  Only prefix reads whose computed
root is foreign and which are not already in the new scrubL successor group
are required to be main-clear. -/
def ScrubLContinuationForeignPrefixMainClearV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLContinuationNewPendingV31 hψ h2 ring C e owner →
    let D := stepV3 hψ h2 ring C e
    ∀ (j : Fin n) (ko q : Fin ψ),
      R2Coherence.groupPos ring (eraseCfgV3 D) j ko.val = owner →
      ∀ k : Fin ((raw (D
        (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val + 1),
        R2Coherence.groupStart ring (eraseCfgV3 D)
          (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) ≠ owner →
        ¬ InGroupOwnedFootprintV31 ring D e
          (R2Coherence.prefixPos ring (eraseCfgV3 D)
            (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) k.val) →
        MainClearV3 (D
          (R2Coherence.prefixPos ring (eraseCfgV3 D)
            (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val) k.val))

theorem scrubLContinuation_new_successor_groupOwnedClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hNew : ScrubLContinuationNewPendingV31 hψ h2 ring C e owner) :
    GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) e := by
  have hc := (scrubLContinuationNewPending_iff
    hψ h2 ring C e owner hGeom hPlus hb).1 hNew
  have hFacts := R2CoherenceV31ReachableScrubL.reachablePhaseFacts_scrubL_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  have ht : (stepV3 hψ h2 ring C e e).ctl.tok = .scrubL := by
    have hx := hNew.1.1
    simpa [hc.1] using hx
  exact (hFacts.2.2.2.2.1 e ht).2.2

/-- Everything except the foreign incoming prefix is arithmetic. -/
theorem scrubLContinuationNewPendingCover_of_foreignPrefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hForeign : ScrubLContinuationForeignPrefixMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    ScrubLContinuationNewPendingCoverV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e owner hGeom hTrace hPlus hb hNew
  let D := stepV3 hψ h2 ring C e
  have hc := (scrubLContinuationNewPending_iff
    hψ h2 ring C e owner hGeom hPlus hb).1 hNew
  have hPendD : PendingOpenROwnerV31 ring D owner := by
    simpa [D] using hNew.1
  have hStartE :
      R2Coherence.groupStart ring (eraseCfgV3 D) e = owner := by
    rw [← hc.1]
    exact pending_successor_groupStart_c2 ring D owner hPendD
  have hFD := hForeign C e owner hGeom hTrace hPlus hb hNew
  dsimp only at hFD
  intro p hFoot
  change InOpenRFreshFootprintV31 ring D owner p at hFoot
  rcases hFoot with ⟨j, ko, q, hOwner, k, hPrefix⟩
  let front := R2Coherence.groupPos ring (eraseCfgV3 D) j q.val
  have hPrefixFront :
      R2Coherence.prefixPos ring (eraseCfgV3 D) front k.val = p := by
    simpa [front] using hPrefix
  by_cases hs : R2Coherence.groupStart ring (eraseCfgV3 D) front = owner
  · have hk : k.val ≤ (raw (D front)).label.val :=
      Nat.le_of_lt_succ k.isLt
    have hpg := prefixPos_eq_groupPos_c2
      ring (eraseCfgV3 D) front k.val hk
    have hp : R2Coherence.groupPos ring (eraseCfgV3 D) front k.val = p :=
      hpg.symm.trans hPrefixFront
    have hkψ : k.val < ψ := by
      have hl := (raw (D front)).label.isLt
      omega
    let kk : Fin ψ := ⟨k.val, hkψ⟩
    have hg : InGroupOwnedFootprintV31 ring D e p := by
      refine ⟨kk, ?_⟩
      change R2Coherence.groupPos ring (eraseCfgV3 D) e k.val = p
      calc
        R2Coherence.groupPos ring (eraseCfgV3 D) e k.val =
            R2Coherence.groupPos ring (eraseCfgV3 D) front k.val := by
          unfold R2Coherence.groupPos
          rw [hStartE, hs]
        _ = p := hp
    exact Or.inr (by simpa [hc.1] using hg)
  · by_cases hg : InGroupOwnedFootprintV31 ring D e p
    · exact Or.inr (by simpa [hc.1] using hg)
    · left
      have hOut : ¬ InGroupOwnedFootprintV31 ring D e
          (R2Coherence.prefixPos ring (eraseCfgV3 D) front k.val) := by
        rw [hPrefixFront]
        exact hg
      have hm := hFD j ko q hOwner k
        (by simpa [front] using hs)
        (by simpa [front] using hOut)
      simpa [D, front, hPrefixFront] using hm

end R2CoherenceV31ReachableCover2
