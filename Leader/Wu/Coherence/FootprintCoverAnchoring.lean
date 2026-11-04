import Leader.Wu.Coherence.ReachableFreshSeekWindow
import Leader.Wu.Coherence.ReachableCoverForeignPrefix
import Leader.Wu.Coherence.ReachableBirthLabelProfile

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31FootprintCover

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableFreshSeek
open R2CoherenceV31ReachableRootSpacing
open R2CoherenceV31ReachableRootSpacing2
open R2CoherenceV31ReachableAdjacentRoot

variable {n ψ κ τ : Nat}

private theorem modL_fc (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem modR_fc (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem back_zero_fc
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.back ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem fwd_succ_fc
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.fwd ring i (d + 1) =
      ring.rightNeighbor (R2Coherence.fwd ring i d) := by
  apply Fin.ext
  unfold R2Coherence.fwd DirectedRing.rightNeighbor
  dsimp only
  rw [modL_fc]
  congr 1

private theorem back_fwd_cancel_fc
    (ring : DirectedRing n) (i : Fin n) (d : Nat) :
    R2Coherence.back ring (R2Coherence.fwd ring i d) d = i := by
  induction d with
  | zero =>
      rw [back_zero_fc]
      apply Fin.ext
      simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
      rw [fwd_succ_fc ring i d]
      rw [R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach]
      exact ih

private theorem prefixPos_eq_groupPos_fc
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
          (A - (L % n) + k) % n := modL_fc _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_fc (A - (L % n)) k n).symm
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
          (A - (L % n) + k) % n := modL_fc _ _ _
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR_fc (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have hx : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hx, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

/-- Exact true arithmetic statement: if the site at physical offset `d < ψ`
from `root` actually carries label `d`, then its computed group start is
`root`, and every legal prefix offset stays in that same physical group. -/
theorem rootOffset_sameGroupStart_and_prefixPos
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (root : Fin n) (d : Fin ψ)
    (hLabel :
      (R2Coherence.raw
        (C (R2Coherence.fwd ring root d.val))).label.val = d.val) :
    R2Coherence.groupStart ring C
        (R2Coherence.fwd ring root d.val) = root ∧
    ∀ k : Fin (d.val + 1),
      R2Coherence.prefixPos ring C
          (R2Coherence.fwd ring root d.val) k.val =
        R2Coherence.fwd ring root k.val := by
  have hs : R2Coherence.groupStart ring C
      (R2Coherence.fwd ring root d.val) = root := by
    unfold R2Coherence.groupStart
    rw [hLabel]
    exact back_fwd_cancel_fc ring root d.val
  refine ⟨hs, ?_⟩
  intro k
  have hk : k.val ≤
      (R2Coherence.raw
        (C (R2Coherence.fwd ring root d.val))).label.val := by
    rw [hLabel]
    omega
  rw [prefixPos_eq_groupPos_fc ring C _ _ hk]
  unfold R2Coherence.groupPos
  rw [hs]

/-- Reachable anchoring is the exact stronger invariant that turns the true
arithmetic lemma into the old strong containment target. -/
def PendingOwnerWindowAnchoredReachableV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
      PendingOwnerWindowAnchoredV31 ring C

theorem pendingFootprintContainmentReachable_of_anchoring
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hAnchor : PendingOwnerWindowAnchoredReachableV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PendingFootprintContainmentReachableV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C hTrace _hGeom
  exact pendingOpenRFootprintInScrubGroup_of_anchored
    ring C (hAnchor C hTrace)

namespace ElectionP5Counterexample

private theorem h3 : 0 < 3 := by decide
private def ring6 : DirectedRing 6 := ⟨by decide⟩

private def literal (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def cell
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩

/-- Labels are 0,1,0,1,0,1.  Site 3 is the scrubL successor of owner 2. -/
private def bad : FC 6 3 3 48 := fun i =>
  match i.val with
  | 0 => cell (literal 0) .closing .none
  | 1 => cell (literal 1) .closing .none
  | 2 => cell (literal 0) .closing .none
  | 3 => cell (literal 1) .releasing .scrubL
  | 4 => cell (literal 0) .closing .none
  | _ => cell (literal 1) .closing .none

theorem geometry : ElectionGeometryV31 ring6 bad := by
  decide +kernel

/-- Stronger than merely assuming P5: the full six-field reachable payload
holds in this source state.  No reachability claim is made. -/
theorem phaseFacts : ReachablePhaseFactsV31 ring6 bad := by
  decide +kernel

theorem scrubL_P5 : GroupOwnedClearV31 ring6 bad 3 := by
  decide +kernel

/-- Failing offset: at physical offset 2 from root 0 the label has reset to 0,
so the computed group start is 2 rather than 0. -/
theorem offset_two_breaks_same_start :
    R2Coherence.groupStart ring6 (eraseCfgV3 bad)
        (R2Coherence.groupPos ring6 (eraseCfgV3 bad) 0 2) ≠
      R2Coherence.groupStart ring6 (eraseCfgV3 bad) 0 := by
  decide +kernel

theorem owner_pending :
    PendingOpenROwnerV31 ring6 bad 2 := by
  unfold PendingOpenROwnerV31
  decide +kernel

theorem zero_in_owner_footprint :
    InOpenRFreshFootprintV31 ring6 bad 2 0 := by
  unfold InOpenRFreshFootprintV31
  decide +kernel

theorem zero_not_in_scrub_group :
    ¬ InGroupOwnedFootprintV31 ring6 bad (ring6.rightNeighbor 2) 0 := by
  unfold InGroupOwnedFootprintV31
  decide +kernel

theorem not_containment :
    ¬ PendingOpenRFootprintInScrubGroupV31 ring6 bad := by
  intro h
  exact zero_not_in_scrub_group
    (h 2 0 owner_pending zero_in_owner_footprint)

/-- Therefore ElectionGeometry + even the full P5-containing payload does not
imply the strong footprint containment statement. -/
theorem election_p5_not_enough :
    ElectionGeometryV31 ring6 bad ∧
    ReachablePhaseFactsV31 ring6 bad ∧
    ¬ PendingOpenRFootprintInScrubGroupV31 ring6 bad :=
  ⟨geometry, phaseFacts, not_containment⟩

end ElectionP5Counterexample
end R2CoherenceV31FootprintCover
