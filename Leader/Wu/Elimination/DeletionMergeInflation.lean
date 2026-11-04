import Leader.Wu.Elimination.SinkAbsorbKernel
import Leader.Wu.Elimination.SinkGapServiceRank
import Init.Data.List.OfFn
import Init.Omega

/-!
# K2 deletion inflation and the scope of pointwise merge funding

This file audits the candidate against the production `sinkKernelC`, `sinkStepC`,
`GapInvariant`, and `gapWC`. Its finite checkers are linked to those definitions
by equivalences; they do not define a replacement protocol or invariant.

* The six-site witness has three legal, equally spaced gaps, a two-step
  prehistory from a clean recovery gap, and dynamic global rank `6 → 9`.
* `actual_deletion_merge` proves a general physical concatenation invariant
  and exact rebasing identity for every positive label modulus.
* The eight-site comb certifies every prefix and every cleanup service.
* The general credit and reserve results are arithmetic consequences of
  explicit pointwise funding premises, with natural-number coefficients.
  The parameterized rotated physical family and parameterized physical comb
  are not formalized here. No stochastic runtime lower bound is asserted.
-/

set_option autoImplicit false

namespace Leader.K2MergeInflation

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant PPLLRepair

/-- Configurations for the concrete witnesses use label modulus two. -/
abbrev Config (n : Nat) := Fin n → AgentState 2

theorem hpsi : 0 < 2 := by decide

/-- The actual K2 kernel, with its two-cell configuration update exposed. -/
def step {n : Nat} (hn : 0 < n) (C : Config n) (e : Fin n) : Config n :=
  let r : Fin n := ⟨(e.val + 1) % n, Nat.mod_lt _ hn⟩
  let q := sinkKernelC hpsi (C e) (C r)
  fun x => if x = e then q.1 else if x = r then q.2 else C x

theorem step_is_sinkStepC {n : Nat} (F : GapFrame n)
    (C : Config n) (e : Fin n) :
    step F.ring.hn C e = sinkStepC hpsi F C e := rfl

/-- Only observed fields of the retained real frame constructor are used. -/
def frame {n : Nat} (hn : 0 < n) (lo : Fin n) (dd : Nat)
    (hd : 2 ≤ dd) (hdn : dd < n) : GapFrame n where
  ring := ⟨hn⟩
  low := lo
  d := dd
  hd := hd
  hdn := hdn

/-- A finite test of all four imported invariant conjuncts. -/
def checkedInvariant {n : Nat} (F : GapFrame n) (C : Config n) : Prop :=
  ((C (F.pos 0)).leader = true ∧ (C (F.pos F.d)).leader = true) ∧
  (∀ k : Fin (F.d + 1), 1 ≤ k.val → k.val < F.d →
    (C (F.pos k.val)).leader = false) ∧
  (∀ k : Fin (F.d + 1), k.val < F.d →
    (C (F.pos (k.val + 1))).label = nextLabel hpsi (C (F.pos k.val))) ∧
  (∀ k j : Fin (F.d + 1), 1 ≤ k.val → k.val ≤ F.d →
    (C (F.pos k.val)).bullet ≠ (0 : Fin 3) →
    k.val ≤ j.val → j.val ≤ F.d → (C (F.pos j.val)).signal_B = (0 : Fin 2))

set_option synthInstance.maxSize 256 in
instance {n : Nat} (F : GapFrame n) (C : Config n) :
    Decidable (checkedInvariant F C) := by
  unfold checkedInvariant
  infer_instance

theorem checkedInvariant_actual {n : Nat} (F : GapFrame n) (C : Config n)
    (h : checkedInvariant F C) : GapInvariant hpsi F C := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro k hk hkd
    exact h.2.1 ⟨k, by omega⟩ hk hkd
  · intro k hkd
    exact h.2.2.1 ⟨k, by omega⟩ hkd
  · intro k j hk hkd hb hkj hjd
    exact h.2.2.2 ⟨k, by omega⟩ ⟨j, by omega⟩ hk hkd hb hkj hjd

/-- The finite checker is equivalent to the imported invariant, including all
its natural-number quantifiers. It is only a kernel-evaluation interface. -/
theorem checkedInvariant_iff {n : Nat} (F : GapFrame n) (C : Config n) :
    checkedInvariant F C ↔ GapInvariant hpsi F C := by
  refine ⟨checkedInvariant_actual F C, ?_⟩
  intro h
  exact ⟨h.1, fun k hk hkd => h.2.1 k.val hk hkd,
    fun k hkd => h.2.2.1 k.val hkd,
    fun k j hk hkd hb hkj hjd => h.2.2.2 k.val j.val hk hkd hb hkj hjd⟩

/-- Finite form of CleanReady; also meaningful for the raw full-ring boundary. -/
def readyAt {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Config n) : Prop :=
  (C (pos dd)).signal_B = (1 : Fin 2) ∧
    ∀ k : Fin (dd + 1), 1 ≤ k.val → k.val ≤ dd →
      (C (pos k.val)).bullet = (0 : Fin 3)

instance {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Config n) :
    Decidable (readyAt dd pos C) := by
  unfold readyAt
  infer_instance

/-- Executable form of the two imported K2 stopping disjuncts. -/
def doneAt {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Config n) : Prop :=
  readyAt dd pos C ∨
    (C (pos 0)).leader = false ∨ (C (pos dd)).leader = false

instance {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Config n) :
    Decidable (doneAt dd pos C) := by
  unfold doneAt readyAt
  infer_instance

/-- Executable K2 rank; on legal frames it equals the imported `gapWC`.
Raw full-ring uses below are kept separate from legal `GapFrame` claims. -/
def sectorWC {n : Nat} (dd : Nat) (pos : Nat → Fin n) (C : Config n) : Nat :=
  if doneAt dd pos C then 0
  else
    let bt := topIdx (fun k => decide (0 < (C (pos k)).bullet.val)) dd
    let st := topIdx (fun k => decide ((C (pos k)).signal_B.val = 1)) dd
    if bt = 0 then dd - st else dd + bt

theorem readyAt_iff {n : Nat} (F : GapFrame n) (C : Config n) :
    readyAt F.d F.pos C ↔ CleanReady F C := by
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, ?_⟩
    intro k hk hkd
    exact hb ⟨k, by omega⟩ hk hkd
  · rintro ⟨hs, hb⟩
    exact ⟨hs, fun k hk hkd => hb k.val hk hkd⟩

theorem doneAt_iff {n : Nat} (F : GapFrame n) (C : Config n) :
    doneAt F.d F.pos C ↔ GapDoneC F C := by
  change (readyAt F.d F.pos C ∨ EndpointDeleted F C) ↔
    (CleanReady F C ∨ EndpointDeleted F C)
  rw [readyAt_iff F C]

theorem sectorWC_is_gapWC {n : Nat} (F : GapFrame n) (C : Config n) :
    sectorWC F.d F.pos C = LDSinkGapServiceRank.gapWC F C := by
  classical
  unfold sectorWC
  change (if doneAt F.d F.pos C then 0
    else if bulletTop F C = 0 then F.d - signalTop F C
    else F.d + bulletTop F C) = LDSinkGapServiceRank.gapWC F C
  unfold LDSinkGapServiceRank.gapWC
  by_cases h : doneAt F.d F.pos C
  · rw [if_pos h, if_pos ((doneAt_iff F C).mp h)]
  · have hh : ¬ GapDoneC F C := fun hc => h ((doneAt_iff F C).mpr hc)
    rw [if_neg h, if_neg hh]

/-- A positive right scan dominates every index of the left sector. -/
theorem topIdx_append_nonzero (p : Nat → Bool) (a : Nat) :
    ∀ b, topIdx (fun k => p (a + k)) b ≠ 0 →
      topIdx p (a + b) = a + topIdx (fun k => p (a + k)) b := by
  intro b
  induction b with
  | zero =>
    intro h
    exact False.elim (h rfl)
  | succ b ih =>
    intro h
    change (if p (a + (b + 1)) then a + (b + 1) else topIdx p (a + b)) =
      a + (if p (a + (b + 1)) then b + 1 else topIdx (fun k => p (a + k)) b)
    cases hbit : p (a + (b + 1)) with
    | false =>
      have ht : topIdx (fun k => p (a + k)) b ≠ 0 := by
        intro hz
        apply h
        change (if p (a + (b + 1)) then b + 1
          else topIdx (fun k => p (a + k)) b) = 0
        rw [hbit]
        exact hz
      exact ih ht
    | true => rfl

/-- Scan/coordinate facts, not a postulated reserve or merge inequality. -/
theorem splice_rank_of_scans {n ψ : Nat} (L R M : GapFrame n)
    (C D : Fin n → AgentState ψ)
    (hd : M.d = L.d + R.d)
    (hp : ∀ k, M.pos (L.d + k) = R.pos k)
    (hbits : ∀ x, (0 < (D x).bullet.val) ↔ (0 < (C x).bullet.val))
    (hr : ¬ GapDoneC R C) (hm : ¬ GapDoneC M D)
    (hb : bulletTop R C ≠ 0) :
    LDSinkGapServiceRank.gapWC M D =
      2 * L.d + LDSinkGapServiceRank.gapWC R C := by
  classical
  let p : Nat → Bool := fun k => decide (0 < (D (M.pos k)).bullet.val)
  have he : (fun k => p (L.d + k)) =
      (fun k => decide (0 < (C (R.pos k)).bullet.val)) := by
    funext k
    change decide (0 < (D (M.pos (L.d + k))).bullet.val) =
      decide (0 < (C (R.pos k)).bullet.val)
    simp only [hp k, hbits (R.pos k)]
  have ht : topIdx (fun k => p (L.d + k)) R.d = bulletTop R C :=
    congrArg (fun f : Nat → Bool => topIdx f R.d) he
  have hnz : topIdx (fun k => p (L.d + k)) R.d ≠ 0 :=
    fun hz => hb (ht.symm.trans hz)
  have htop : bulletTop M D = L.d + bulletTop R C := by
    change topIdx p M.d = L.d + bulletTop R C
    rw [hd]
    exact (topIdx_append_nonzero p L.d R.d hnz).trans
      (congrArg (fun z : Nat => L.d + z) ht)
  have hmnz : bulletTop M D ≠ 0 := by
    intro hz
    have heq := htop.symm.trans hz
    apply hb
    omega
  unfold LDSinkGapServiceRank.gapWC
  rw [if_neg hm, if_neg hr, if_neg hmnz, if_neg hb, htop, hd]
  omega

theorem rebase_balance (a left right merged : Nat)
    (hm : merged = 2 * a + right) (hl : left ≤ 2 * a) :
    merged = left + right + (2 * a - left) := by omega

/-! ## Actual prepared deletion and concatenated gap geometry

The next results derive the physical update from K2 and the two original gap
invariants. The scan identity above then applies with no carried post-state,
nonzero-indicator conservation, or merged-invariant premise.
-/

/-- Concatenate adjacent gaps using the production modular coordinates. The
outer endpoints are distinct because `TwoGapFrame.length_lt` is strict. -/
def mergedFrame {n : Nat} (F : LDTwoGapFrame.TwoGapFrame n) : GapFrame n where
  ring := F.recovery.ring
  low := F.recovery.low
  d := F.recovery.d + F.attack.d
  hd := by have h := F.recovery.hd; omega
  hdn := F.length_lt

/-- The concatenated right sector uses the old attack coordinates. -/
theorem mergedFrame_right_pos {n : Nat} (F : LDTwoGapFrame.TwoGapFrame n)
    (k : Nat) : (mergedFrame F).pos (F.recovery.d + k) = F.attack.pos k :=
  (F.attack_pos_eq_recovery_offset k).symm

private theorem merged_pos_ne_shared {n : Nat} (F : LDTwoGapFrame.TwoGapFrame n)
    (k : Nat) (hk : k ≤ F.recovery.d + F.attack.d) (hne : k ≠ F.recovery.d) :
    (mergedFrame F).pos k ≠ F.attack.pos 0 := by
  intro he
  apply hne
  apply F.combined_pos_injective k F.recovery.d hk (by omega)
  exact he.trans F.shared.symm

private theorem prepared_kernel_row {ψ : Nat} (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hsh : l.shield = false) (hsl : l.signal_B = 0)
    (hb : r.bullet = 2) (hsr : r.signal_B = 0) :
    sinkKernelC hψ l r = ({ l with leader := false }, { r with bullet := 1 }) := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
    hl, hr, hsh, hsl, hb, hsr]
  intro _
  rfl

/-- Under the actual attack invariant, an unshielded zero-signal victim with
an incoming live bullet is deleted. Only its leader bit and the live bullet's
type change. Signal values and nonzero bullet locations are preserved. -/
theorem prepared_step_fields {n ψ : Nat} (hψ : 0 < ψ)
    (F : LDTwoGapFrame.TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hi : GapInvariant hψ F.attack C)
    (hsh : (C (F.attack.pos 0)).shield = false)
    (hsl : (C (F.attack.pos 0)).signal_B = 0)
    (hb : (C (F.attack.pos 1)).bullet = 2) :
    let D := sinkStepC hψ F.attack C (F.attack.pos 0)
    (∀ x, (D x).leader = if x = F.attack.pos 0 then false else (C x).leader) ∧
    (∀ x, (D x).label = (C x).label) ∧
    (∀ x, (D x).signal_B = (C x).signal_B) ∧
    (∀ x, (D x).bullet ≠ 0 ↔ (C x).bullet ≠ 0) := by
  have hd := F.attack.hd
  have hsr : (C (F.attack.pos 1)).signal_B = 0 :=
    hi.2.2.2 1 1 (by omega) (by omega) (by rw [hb]; decide) (by omega) (by omega)
  have hrow := prepared_kernel_row hψ (C (F.attack.pos 0)) (C (F.attack.pos 1))
    hi.1.1 (hi.2.1 1 (by omega) (by omega)) hsh hsl hb hsr
  have h10 : F.attack.pos 1 ≠ F.attack.pos 0 := by
    intro he
    have := F.attack_pos_injective 1 0 (by omega) (by omega) he
    omega
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x <;>
    by_cases hx : x = F.attack.pos 0 <;>
    by_cases hy : x = F.attack.pos 1 <;>
    simp [sinkStepC, updatePair, LDTwoGapFrame.gap_rightNeighbor_pos,
      hrow, hx, hy, h10, hb]

/-- A prepared K2 deletion preserves the actual four-conjunct invariant on
the newly concatenated gap. The appended sector has zero signals by the old
attack invariant and its parked live bullet; no extra signal-order premise
or post-state invariant is assumed. -/
theorem merged_invariant_of_prepared {n ψ : Nat} (hψ : 0 < ψ)
    (F : LDTwoGapFrame.TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hl : GapInvariant hψ F.recovery C) (hr : GapInvariant hψ F.attack C)
    (hsh : (C (F.attack.pos 0)).shield = false)
    (hsl : (C (F.attack.pos 0)).signal_B = 0)
    (hb : (C (F.attack.pos 1)).bullet = 2) :
    GapInvariant hψ (mergedFrame F) (sinkStepC hψ F.attack C (F.attack.pos 0)) := by
  let D := sinkStepC hψ F.attack C (F.attack.pos 0)
  obtain ⟨hld, hlabel, hsignal, hbullet⟩ := prepared_step_fields hψ F C hr hsh hsl hb
  have ha := F.recovery.hd
  have hbnd := F.attack.hd
  have hleft (k : Nat) : (mergedFrame F).pos k = F.recovery.pos k := rfl
  have hright := mergedFrame_right_pos F
  have htail (j : Nat) (hj : 1 ≤ j) (hjd : j ≤ F.attack.d) :
      (C (F.attack.pos j)).signal_B = 0 :=
    hr.2.2.2 1 j (by omega) (by omega) (by rw [hb]; decide) hj hjd
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hld, if_neg (merged_pos_ne_shared F 0 (by omega) (by omega))]
    exact hl.1.1
  · change (D ((mergedFrame F).pos (F.recovery.d + F.attack.d))).leader = true
    rw [hld, if_neg (merged_pos_ne_shared F (F.recovery.d + F.attack.d)
      (by omega) (by omega))]
    rw [hright]
    exact hr.1.2
  · intro k hk hkd
    change k < F.recovery.d + F.attack.d at hkd
    rw [hld]
    by_cases he : k = F.recovery.d
    · subst k
      rw [hleft, F.shared, if_pos rfl]
    · rw [if_neg (merged_pos_ne_shared F k (by omega) he)]
      by_cases hkl : k < F.recovery.d
      · exact hl.2.1 k hk hkl
      · have heq : k = F.recovery.d + (k - F.recovery.d) := by omega
        rw [heq, hright]
        exact hr.2.1 (k - F.recovery.d) (by omega) (by omega)
  · intro k hk
    change k < F.recovery.d + F.attack.d at hk
    have hnext (x : Fin n) : nextLabel hψ (D x) = nextLabel hψ (C x) := by
      apply Fin.ext
      change ((D x).label.val + 1) % ψ = ((C x).label.val + 1) % ψ
      rw [hlabel]
    rw [hlabel, hnext]
    by_cases hkl : k < F.recovery.d
    · exact hl.2.2.1 k hkl
    · have heq : k = F.recovery.d + (k - F.recovery.d) := by omega
      rw [heq, Nat.add_assoc, hright, hright]
      exact hr.2.2.1 (k - F.recovery.d) (by omega)
  · intro k j hk hkd hbk hkj hjd
    change k ≤ F.recovery.d + F.attack.d at hkd
    change j ≤ F.recovery.d + F.attack.d at hjd
    rw [hsignal]
    have hbC := (hbullet _).mp hbk
    by_cases hjl : j ≤ F.recovery.d
    · exact hl.2.2.2 k j hk (by omega) hbC hkj hjl
    · have heq : j = F.recovery.d + (j - F.recovery.d) := by omega
      rw [heq, hright]
      exact htail (j - F.recovery.d) (by omega) (by omega)

private theorem not_doneC_of_bullet {n ψ : Nat} (F : GapFrame n)
    (C : Fin n → AgentState ψ) (he : GapEndpointsPresent F C)
    (j : Nat) (hj : 1 ≤ j) (hjd : j ≤ F.d) (hb : (C (F.pos j)).bullet ≠ 0) :
    ¬ GapDoneC F C := by
  rintro (hc | hd)
  · exact hb (hc.2 j hj hjd)
  · rcases hd with hd | hd
    · rw [he.1] at hd
      cases hd
    · rw [he.2] at hd
      cases hd

/-- Exact dynamic rank law for a prepared deletion in the real K2 process.
The scan rebases by the recovery length, giving twice that length in `gapWC`.
Every post-state premise of `splice_rank_of_scans` is discharged physically. -/
theorem merged_rank_of_prepared {n ψ : Nat} (hψ : 0 < ψ)
    (F : LDTwoGapFrame.TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hl : GapInvariant hψ F.recovery C) (hr : GapInvariant hψ F.attack C)
    (hsh : (C (F.attack.pos 0)).shield = false)
    (hsl : (C (F.attack.pos 0)).signal_B = 0)
    (hb : (C (F.attack.pos 1)).bullet = 2) :
    LDSinkGapServiceRank.gapWC (mergedFrame F)
        (sinkStepC hψ F.attack C (F.attack.pos 0)) =
      2 * F.recovery.d + LDSinkGapServiceRank.gapWC F.attack C := by
  let D := sinkStepC hψ F.attack C (F.attack.pos 0)
  obtain ⟨_, _, _, hbullet⟩ := prepared_step_fields hψ F C hr hsh hsl hb
  have hm := merged_invariant_of_prepared hψ F C hl hr hsh hsl hb
  have ha := F.recovery.hd
  have hd := F.attack.hd
  have hbn : (C (F.attack.pos 1)).bullet ≠ 0 := by rw [hb]; decide
  have hmb : (D ((mergedFrame F).pos (F.recovery.d + 1))).bullet ≠ 0 := by
    rw [mergedFrame_right_pos]
    exact (hbullet _).mpr hbn
  have hnr := not_doneC_of_bullet F.attack C hr.1 1 (by omega) (by omega) hbn
  have hnm := not_doneC_of_bullet (mergedFrame F) D hm.1 (F.recovery.d + 1)
    (by omega) (by change F.recovery.d + 1 ≤ F.recovery.d + F.attack.d; omega) hmb
  have htop := bulletTop_ge_of F.attack C (by omega) hbn
  have hbits (x : Fin n) : (0 < (D x).bullet.val) ↔ (0 < (C x).bullet.val) := by
    have hp (b : Fin 3) : 0 < b.val ↔ b ≠ 0 := by
      rcases fin3_cases b with h | h | h <;> rw [h] <;> decide
    rw [hp, hp]
    exact hbullet x
  exact splice_rank_of_scans F.recovery F.attack (mergedFrame F) C D rfl
    (mergedFrame_right_pos F) hbits hnr hnm (by omega)

/-- The actual rebasing charge is `2a - W_left`, and is at most `2a - 1`.
This is an identity for dynamic coordinates, not a payment by old span keys. -/
theorem merged_rebase_balance {n ψ : Nat} (hψ : 0 < ψ)
    (F : LDTwoGapFrame.TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hl : GapInvariant hψ F.recovery C) (hr : GapInvariant hψ F.attack C)
    (hsh : (C (F.attack.pos 0)).shield = false)
    (hsl : (C (F.attack.pos 0)).signal_B = 0)
    (hb : (C (F.attack.pos 1)).bullet = 2) :
    LDSinkGapServiceRank.gapWC (mergedFrame F)
        (sinkStepC hψ F.attack C (F.attack.pos 0)) =
      LDSinkGapServiceRank.gapWC F.recovery C + LDSinkGapServiceRank.gapWC F.attack C +
        (2 * F.recovery.d - LDSinkGapServiceRank.gapWC F.recovery C) ∧
    2 * F.recovery.d - LDSinkGapServiceRank.gapWC F.recovery C ≤ 2 * F.recovery.d - 1 := by
  have heq := merged_rank_of_prepared hψ F C hl hr hsh hsl hb
  have hle := LDSinkGapServiceRank.gapWC_le_two_d hψ F.recovery C hl
  have hs : (C (F.recovery.pos F.recovery.d)).signal_B = 0 := by rw [F.shared]; exact hsl
  have ha := F.recovery.hd
  have hnd : ¬ GapDoneC F.recovery C := by
    rintro (hc | hd)
    · have hc := hc.1
      rw [hs] at hc
      cases hc
    · rcases hd with hd | hd
      · rw [hl.1.1] at hd
        cases hd
      · rw [hl.1.2] at hd
        cases hd
  have hst := signalTop_le F.recovery C
  have hstlt : signalTop F.recovery C < F.recovery.d := by
    by_cases he : signalTop F.recovery C = F.recovery.d
    · have hsig := signalTop_one_at F.recovery C (by omega)
      rw [he, hs] at hsig
      cases hsig
    · omega
  have hpos : 0 < LDSinkGapServiceRank.gapWC F.recovery C := by
    unfold LDSinkGapServiceRank.gapWC
    rw [if_neg hnd]
    split <;> omega
  exact ⟨rebase_balance _ _ _ _ heq hle, by omega⟩

private theorem prepared_of_kernel_deletion {ψ : Nat} (hψ : 0 < ψ)
    (l r : AgentState ψ) (hl : l.leader = true) (hr : r.leader = false)
    (hd : (sinkKernelC hψ l r).1.leader = false) :
    l.shield = false ∧ l.signal_B = 0 ∧ r.bullet = 2 := by
  rcases fin2_cases l.signal_B with hs | hs <;>
    cases hsh : l.shield <;>
    rcases fin3_cases r.bullet with hb | hb | hb <;>
    simp_all [sinkKernelC, eliminateLeadersNoCollisionFire,
      absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]

/-- Any successful K2 deletion of the shared leader produces the new actual
gap invariant and the exact rank rebasing law. Local preparation is inferred
from that deletion, including the FIRE guard, rather than assumed. -/
theorem actual_deletion_merge {n ψ : Nat} (hψ : 0 < ψ)
    (F : LDTwoGapFrame.TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hl : GapInvariant hψ F.recovery C) (hr : GapInvariant hψ F.attack C)
    (hdelete : (sinkStepC hψ F.attack C (F.attack.pos 0) (F.attack.pos 0)).leader = false) :
    let D := sinkStepC hψ F.attack C (F.attack.pos 0)
    GapInvariant hψ (mergedFrame F) D ∧
    LDSinkGapServiceRank.gapWC (mergedFrame F) D =
      2 * F.recovery.d + LDSinkGapServiceRank.gapWC F.attack C ∧
    LDSinkGapServiceRank.gapWC (mergedFrame F) D =
      LDSinkGapServiceRank.gapWC F.recovery C + LDSinkGapServiceRank.gapWC F.attack C +
        (2 * F.recovery.d - LDSinkGapServiceRank.gapWC F.recovery C) ∧
    2 * F.recovery.d - LDSinkGapServiceRank.gapWC F.recovery C ≤ 2 * F.recovery.d - 1 := by
  have hd := F.attack.hd
  have hkernel : (sinkKernelC hψ (C (F.attack.pos 0)) (C (F.attack.pos 1))).1.leader = false := by
    simpa [sinkStepC, updatePair, LDTwoGapFrame.gap_rightNeighbor_pos] using hdelete
  obtain ⟨hsh, hsl, hb⟩ := prepared_of_kernel_deletion hψ (C (F.attack.pos 0))
    (C (F.attack.pos 1)) hr.1.1 (hr.2.1 1 (by omega) (by omega)) hkernel
  exact ⟨merged_invariant_of_prepared hψ F C hl hr hsh hsl hb,
    merged_rank_of_prepared hψ F C hl hr hsh hsl hb,
    merged_rebase_balance hψ F C hl hr hsh hsl hb⟩

/-- Fixed physical idle fields; no ghost field is inserted into AgentState. -/
def atom (lab : Fin 2) (ld sh : Bool) (bt : Fin 3) (sb : Fin 2) : AgentState 2 where
  leader := ld
  probe := false
  phase := false
  bit := false
  wait := true
  state := MainState.none
  path := PathInfo.bot
  reset := false
  carry := false
  count := 0
  label := lab
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := sb
  bullet := bt
  shield := sh
  write_state := WriteState.none
  write := WriteAction.none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-! ## A minimal fully spaced physical witness and its clean prehistory -/

/-- Shared physical pattern for the six-site witness and smaller boundary tests. -/
def smallPre {n : Nat} (x : Fin n) : AgentState 2 :=
  atom ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
    (decide (x.val = 0 ∨ x.val = 2 ∨ x.val = 4)) false
    (if x.val = 3 then 2 else 0) (if x.val = 1 then 1 else 0)

/-- The pattern after deletion at edge two: leader two becomes a follower,
and the live bullet at three becomes a dummy. -/
def smallPost {n : Nat} (x : Fin n) : AgentState 2 :=
  atom ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
    (decide (x.val = 0 ∨ x.val = 4)) false
    (if x.val = 3 then 1 else 0) (if x.val = 1 then 1 else 0)

def pre6 : Config 6 := smallPre
def post6 : Config 6 := smallPost
def L6 : GapFrame 6 := frame (by decide) ⟨0, by decide⟩ 2 (by decide) (by decide)
def R6 : GapFrame 6 := frame (by decide) ⟨2, by decide⟩ 2 (by decide) (by decide)
def T6 : GapFrame 6 := frame (by decide) ⟨4, by decide⟩ 2 (by decide) (by decide)
def M6 : GapFrame 6 := frame (by decide) ⟨0, by decide⟩ 4 (by decide) (by decide)

theorem kernel_delete_row :
    sinkKernelC hpsi (atom 0 true false 0 0) (atom 1 false false 2 0) =
      (atom 0 false false 0 0, atom 1 false false 1 0) := by decide

/-- Equality of complete configurations after the production K2 step. -/
theorem six_step : sinkStepC hpsi L6 pre6 ⟨2, by decide⟩ = post6 :=
  funext (by decide)

/-- All old gaps and both new dynamic gaps satisfy the imported invariant. -/
theorem six_invariants :
    GapInvariant hpsi L6 pre6 ∧ GapInvariant hpsi R6 pre6 ∧
    GapInvariant hpsi T6 pre6 ∧ GapInvariant hpsi M6 post6 ∧
    GapInvariant hpsi T6 post6 :=
  ⟨checkedInvariant_actual L6 pre6 (by decide),
   checkedInvariant_actual R6 pre6 (by decide),
   checkedInvariant_actual T6 pre6 (by decide),
   checkedInvariant_actual M6 post6 (by decide),
   checkedInvariant_actual T6 post6 (by decide)⟩

/-- Frozen deleted frames vanish while the new merged frame has rank seven. -/
theorem six_ranks :
    LDSinkGapServiceRank.gapWC L6 pre6 = 1 ∧
    LDSinkGapServiceRank.gapWC R6 pre6 = 3 ∧
    LDSinkGapServiceRank.gapWC L6 post6 = 0 ∧
    LDSinkGapServiceRank.gapWC R6 post6 = 0 ∧
    LDSinkGapServiceRank.gapWC M6 post6 = 7 ∧
    LDSinkGapServiceRank.gapWC T6 pre6 = 2 ∧
    LDSinkGapServiceRank.gapWC T6 post6 = 2 := by
  rw [← sectorWC_is_gapWC L6 pre6, ← sectorWC_is_gapWC R6 pre6,
    ← sectorWC_is_gapWC L6 post6, ← sectorWC_is_gapWC R6 post6,
    ← sectorWC_is_gapWC M6 post6, ← sectorWC_is_gapWC T6 pre6,
    ← sectorWC_is_gapWC T6 post6]
  decide

/-- Exact dynamic global sum on all gaps before and after the deletion. -/
theorem six_dynamic_sum :
    LDSinkGapServiceRank.gapWC L6 pre6 + LDSinkGapServiceRank.gapWC R6 pre6 +
      LDSinkGapServiceRank.gapWC T6 pre6 = 6 ∧
    LDSinkGapServiceRank.gapWC M6 post6 + LDSinkGapServiceRank.gapWC T6 post6 = 9 := by
  obtain ⟨hL, hR, _, _, hM, hT, hT'⟩ := six_ranks
  omega

/-- These are the complete leader sets, not a chosen subset of frames. -/
theorem six_leader_layout :
    (∀ x : Fin 6, (pre6 x).leader = true ↔ x.val = 0 ∨ x.val = 2 ∨ x.val = 4) ∧
    (∀ x : Fin 6, (post6 x).leader = true ↔ x.val = 0 ∨ x.val = 4) := by decide

theorem six_geometry :
    L6.pos L6.d = R6.pos 0 ∧ R6.pos R6.d = T6.pos 0 ∧
    T6.pos T6.d = L6.pos 0 ∧ M6.d = L6.d + R6.d ∧
    (∀ x : Fin 6, (pre6 x).bullet ≠ 0 ↔ x.val = 3) ∧
    (∀ x : Fin 6, (post6 x).bullet ≠ 0 ↔ x.val = 3) ∧
    (∀ x : Fin 6, (post6 x).signal_B = (pre6 x).signal_B) := by decide

theorem six_minimal_under_spacing (a b c n : Nat)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hs : a + b + c ≤ n) :
    6 ≤ n := by omega

/-- A clean recovery entrance obtained by setting the shared leader shield
and signal. No stronger global active-set membership is claimed. -/
def entrance6 (x : Fin 6) : AgentState 2 :=
  if x.val = 2 then { pre6 x with shield := true, signal_B := 1 } else pre6 x

def middle6 : Config 6 := step (by decide) entrance6 ⟨1, by decide⟩

/-- The second step of the actual edge-one, edge-zero prehistory. -/
theorem history6_to_before : step (by decide) middle6 ⟨0, by decide⟩ = pre6 :=
  funext (by decide)

/-- Both prehistory states satisfy all three old gap invariants; the first
state also satisfies the production `CleanReady` predicate on the recovery gap. -/
theorem history6_invariants :
    GapInvariant hpsi L6 entrance6 ∧ GapInvariant hpsi R6 entrance6 ∧
    GapInvariant hpsi T6 entrance6 ∧ CleanReady L6 entrance6 ∧
    GapInvariant hpsi L6 middle6 ∧ GapInvariant hpsi R6 middle6 ∧
    GapInvariant hpsi T6 middle6 :=
  ⟨checkedInvariant_actual L6 entrance6 (by decide),
   checkedInvariant_actual R6 entrance6 (by decide),
   checkedInvariant_actual T6 entrance6 (by decide),
   (readyAt_iff L6 entrance6).mp (by decide),
   checkedInvariant_actual L6 middle6 (by decide),
   checkedInvariant_actual R6 middle6 (by decide),
   checkedInvariant_actual T6 middle6 (by decide)⟩

/-! ## A concrete comb with repeated genuine cleanup service -/

/-- Legal frames on the eight-site ring. -/
def F8 (lo dd : Nat) (hl : lo < 8) (hd : 2 ≤ dd) (ht : dd < 8) : GapFrame 8 :=
  frame (by decide) ⟨lo, hl⟩ dd hd ht

def pre8 (x : Fin 8) : AgentState 2 :=
  atom ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
    (decide (x.val = 0 ∨ x.val = 2 ∨ x.val = 4 ∨ x.val = 6)) false
    (if x.val = 3 ∨ x.val = 5 then 2 else 0) (if x.val = 1 then 1 else 0)

def next8 (x : Fin 8) : AgentState 2 :=
  atom ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
    (decide (x.val = 0 ∨ x.val = 4 ∨ x.val = 6)) false
    (if x.val = 5 then 2 else 0) (if 1 ≤ x.val ∧ x.val ≤ 3 then 1 else 0)

def final8 (x : Fin 8) : AgentState 2 :=
  atom ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
    (decide (x.val = 0 ∨ x.val = 6)) false
    (if x.val = 5 then 1 else 0) (if 1 ≤ x.val ∧ x.val ≤ 3 then 1 else 0)

/-- One successful deletion followed by a backward dummy sweep and forward
signal sweep, using the actual physical edge identities. -/
def word8 : List (Fin 8) :=
  [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩,
   ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-- Iterate the actual K2 update along an explicitly supplied scheduler word. -/
def run {n : Nat} (hn : 0 < n) (C : Config n) (es : List (Fin n)) : Config n :=
  es.foldl (step hn) C

theorem comb8_to_next : run (by decide) pre8 word8 = next8 := funext (by decide)

def prefixInvariant8 (t : Fin 7) : Prop :=
  let C := run (by decide) pre8 (word8.take t.val)
  if t.val = 0 then
    checkedInvariant (F8 0 2 (by decide) (by decide) (by decide)) C ∧
    checkedInvariant (F8 2 2 (by decide) (by decide) (by decide)) C ∧
    checkedInvariant (F8 4 2 (by decide) (by decide) (by decide)) C ∧
    checkedInvariant (F8 6 2 (by decide) (by decide) (by decide)) C
  else
    checkedInvariant (F8 0 4 (by decide) (by decide) (by decide)) C ∧
    checkedInvariant (F8 4 2 (by decide) (by decide) (by decide)) C ∧
    checkedInvariant (F8 6 2 (by decide) (by decide) (by decide)) C

instance (t : Fin 7) : Decidable (prefixInvariant8 t) := by
  unfold prefixInvariant8
  infer_instance

theorem comb8_prefix_invariants : ∀ t : Fin 7, prefixInvariant8 t := by decide

/-- Every dynamic gap at every prefix of the eight-site execution satisfies
the imported invariant, with all its original quantified obligations. -/
theorem comb8_actual_prefix_invariants (t : Fin 7) :
    let C := run (by decide) pre8 (word8.take t.val)
    if t.val = 0 then
      GapInvariant hpsi (F8 0 2 (by decide) (by decide) (by decide)) C ∧
      GapInvariant hpsi (F8 2 2 (by decide) (by decide) (by decide)) C ∧
      GapInvariant hpsi (F8 4 2 (by decide) (by decide) (by decide)) C ∧
      GapInvariant hpsi (F8 6 2 (by decide) (by decide) (by decide)) C
    else
      GapInvariant hpsi (F8 0 4 (by decide) (by decide) (by decide)) C ∧
      GapInvariant hpsi (F8 4 2 (by decide) (by decide) (by decide)) C ∧
      GapInvariant hpsi (F8 6 2 (by decide) (by decide) (by decide)) C := by
  have h := comb8_prefix_invariants t
  simpa only [prefixInvariant8, checkedInvariant_iff] using h

/-- The next actual deletion has a larger rebasing charge. -/
theorem comb8_next_deletion : step (by decide) next8 ⟨4, by decide⟩ = final8 :=
  funext (by decide)

theorem comb8_ranks :
    LDSinkGapServiceRank.gapWC (F8 0 4 (by decide) (by decide) (by decide)) next8 = 1 ∧
    LDSinkGapServiceRank.gapWC (F8 4 2 (by decide) (by decide) (by decide)) next8 = 3 ∧
    LDSinkGapServiceRank.gapWC (F8 0 6 (by decide) (by decide) (by decide)) final8 = 11 := by
  rw [← sectorWC_is_gapWC, ← sectorWC_is_gapWC, ← sectorWC_is_gapWC]
  decide

/-- Every cleanup service in the concrete comb lowers the actual merged gap
rank. The repeated edges are not idle padding of the execution word. -/
theorem comb8_services_strict : ∀ t : Fin 5,
    LDSinkGapServiceRank.gapWC (F8 0 4 (by decide) (by decide) (by decide))
        (run (by decide) pre8 (word8.take (t.val + 2))) + 1 ≤
      LDSinkGapServiceRank.gapWC (F8 0 4 (by decide) (by decide) (by decide))
        (run (by decide) pre8 (word8.take (t.val + 1))) := by
  simp only [← sectorWC_is_gapWC]
  decide

/-- Both untouched gaps are included in the concrete comb's global sum. -/
theorem comb8_global_ranks :
    LDSinkGapServiceRank.gapWC (F8 0 2 (by decide) (by decide) (by decide)) pre8 +
      LDSinkGapServiceRank.gapWC (F8 2 2 (by decide) (by decide) (by decide)) pre8 +
      LDSinkGapServiceRank.gapWC (F8 4 2 (by decide) (by decide) (by decide)) pre8 +
      LDSinkGapServiceRank.gapWC (F8 6 2 (by decide) (by decide) (by decide)) pre8 = 9 ∧
    LDSinkGapServiceRank.gapWC (F8 0 4 (by decide) (by decide) (by decide)) next8 +
      LDSinkGapServiceRank.gapWC (F8 4 2 (by decide) (by decide) (by decide)) next8 +
      LDSinkGapServiceRank.gapWC (F8 6 2 (by decide) (by decide) (by decide)) next8 = 6 := by
  simp only [← sectorWC_is_gapWC]
  decide

/-- First-use edge identities in an explicit finite execution word. -/
def freshVisits (seen : List Nat) : List Nat → Nat
  | [] => 0
  | e :: es => (if e ∈ seen then 0 else 1) + freshVisits (e :: seen) es

def repeatVisits (seen : List Nat) : List Nat → Nat
  | [] => 0
  | e :: es => (if e ∈ seen then 1 else 0) + repeatVisits (e :: seen) es

theorem visits_split (es : List Nat) :
    ∀ seen, freshVisits seen es + repeatVisits seen es = es.length := by
  induction es with
  | nil => intro seen; rfl
  | cons e es ih =>
    intro seen
    have ht := ih (e :: seen)
    by_cases h : e ∈ seen
    · simp only [freshVisits, repeatVisits, if_pos h, List.length_cons]
      omega
    · simp only [freshVisits, repeatVisits, if_neg h, List.length_cons]
      omega

theorem comb8_fresh_and_repeat :
    (word8.map Fin.val).length = 6 ∧ freshVisits [] (word8.map Fin.val) = 3 ∧
    repeatVisits [] (word8.map Fin.val) = 3 := by decide

/-! ## Conditional arithmetic for a specified pointwise funding model

The site coefficients and leader coefficient are fixed natural numbers.
The current dynamic rank and each deletion payment are scaled by the ring
size. A deletion may spend both scheduled sites, while retaining every other
credit key. These hypotheses do not describe row-averaged expected drift.
-/

/-- Necessary numeric condition on the claimed local credit-funded payment.
`hspend` bounds the total reserve spent by the two scheduled site weights. -/
theorem local_credit_demand (a beta z z' c0 c1 : Nat)
    (hspend : z ≤ z' + c0 + c1)
    (hpay : 1 + (2 * a + 3) + 2 * beta + z' ≤ 4 + 3 * beta + z) :
    2 * a ≤ c0 + c1 + beta := by omega

/-- Sum of the first fixed nonnegative physical-site credit weights. -/
def creditPrefix (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => creditPrefix c t + c t

/-- Sum the adjacent-site funding demands along an initial segment. -/
theorem cycle_prefix_bound (c : Nat → Nat) (need bonus : Nat) :
    ∀ q, (∀ i, i < q → need ≤ c i + c (i + 1) + bonus) →
      q * need + c 0 ≤ 2 * creditPrefix c q + c q + q * bonus := by
  intro q
  induction q with
  | zero =>
    intro h
    simpa only [creditPrefix, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      using Nat.le_refl (c 0)
  | succ q ih =>
    intro h
    have hp := ih (fun i hi => h i (by omega))
    have hl := h q (by omega)
    change (q + 1) * need + c 0 ≤
      2 * (creditPrefix c q + c q) + c (q + 1) + (q + 1) * bonus
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega

/-- Cyclic summation counts every fixed site weight twice. -/
theorem cycle_budget_lower (c : Nat → Nat) (need bonus n : Nat)
    (hc : c n = c 0) (h : ∀ i, i < n → need ≤ c i + c (i + 1) + bonus) :
    n * need ≤ 2 * creditPrefix c n + n * bonus := by
  have hp := cycle_prefix_bound c need bonus n h
  rw [hc] at hp
  omega

/-- With n=2r, even the reserve alone has a cubic scaled lower bound. -/
theorem even_scaled_reserve_lower (c : Nat → Nat) (r beta : Nat)
    (hc : c (2 * r) = c 0)
    (h : ∀ i, i < 2 * r → 4 * r ≤ c i + c (i + 1) + (beta + 8)) :
    (2 * r) * ((2 * r) * (2 * r)) ≤
      (2 * r) * (creditPrefix c (2 * r) + r * beta) +
        4 * ((2 * r) * (2 * r)) := by
  have hp := cycle_budget_lower c (4 * r) (beta + 8) (2 * r) hc h
  have hl : (2 * r) * (4 * r) = 2 * ((2 * r) * (2 * r)) := by
    calc
      (2 * r) * (4 * r) = (2 * r) * ((2 * 2) * r) := rfl
      _ = 2 * ((2 * r) * (2 * r)) := by ac_rfl
  have hr : (2 * r) * (beta + 8) = 2 * (r * beta) + 16 * r := by
    calc
      (2 * r) * (beta + 8) = (2 * r) * beta + (2 * r) * 8 := Nat.mul_add _ _ _
      _ = 2 * (r * beta) + (2 * 8) * r := by ac_rfl
      _ = 2 * (r * beta) + 16 * r := rfl
  rw [hl, hr] at hp
  have hs : (2 * r) * (2 * r) ≤ creditPrefix c (2 * r) + r * beta + 4 * (2 * r) := by
    omega
  have hmul : (2 * r) * (4 * (2 * r)) = 4 * ((2 * r) * (2 * r)) := by ac_rfl
  calc
    (2 * r) * ((2 * r) * (2 * r)) ≤
        (2 * r) * (creditPrefix c (2 * r) + r * beta + 4 * (2 * r)) :=
      Nat.mul_le_mul_left (2 * r) hs
    _ = (2 * r) * (creditPrefix c (2 * r) + r * beta) +
        4 * ((2 * r) * (2 * r)) := by rw [Nat.mul_add, hmul]

/-- Under the same local numeric funding demands, adding the dense layout's
raw rank `n` gives the total lower bound `n^3 ≤ V_initial + 3n^2`. Coefficients
here are natural numbers; the hypotheses are the funding model being tested. -/
theorem even_scaled_total_lower (c : Nat → Nat) (r beta : Nat)
    (hc : c (2 * r) = c 0)
    (h : ∀ i, i < 2 * r → 4 * r ≤ c i + c (i + 1) + (beta + 8)) :
    (2 * r) * ((2 * r) * (2 * r)) ≤
      (2 * r) * (2 * r + creditPrefix c (2 * r) + r * beta) +
        3 * ((2 * r) * (2 * r)) := by
  have he := even_scaled_reserve_lower c r beta hc h
  simp only [Nat.mul_add] at he ⊢
  omega

/-- Decreasing physical edge indices, including the leader's sink edge. -/
def downToZero : Nat → List Nat
  | 0 => [0]
  | k + 1 => (k + 1) :: downToZero k

/-- Increasing physical edge indices for the forward signal sweep. -/
def upFromOne : Nat → List Nat
  | 0 => []
  | k + 1 => upFromOne k ++ [k + 1]

/-- The cleanup portion of the proposed general comb cycle. -/
def cleanupWord (j : Nat) : List Nat := downToZero (2 * j) ++ upFromOne (2 * j)

/-- Arithmetic scheduler-word schema; physical execution is certified above
only for the eight-site instance. -/
def combWord : Nat → List Nat
  | 0 => []
  | q + 1 => combWord q ++ ((2 * (q + 1)) :: cleanupWord (q + 1))

/-- Total number of proposed cleanup services in the first cycles. -/
def serviceCount : Nat → Nat
  | 0 => 0
  | q + 1 => serviceCount q + (cleanupWord (q + 1)).length

theorem down_length (k : Nat) : (downToZero k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [downToZero, List.length_cons, ih]

theorem up_length (k : Nat) : (upFromOne k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [upFromOne, List.length_append, List.length_singleton, ih]

theorem cleanup_length (j : Nat) : (cleanupWord j).length = 4 * j + 1 := by
  unfold cleanupWord
  rw [List.length_append, down_length, up_length]
  omega

theorem service_count (q : Nat) : serviceCount q = 2 * q * q + 3 * q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [serviceCount, cleanup_length, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega

theorem comb_length (q : Nat) : (combWord q).length = serviceCount q + q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change (combWord q ++ ((2 * (q + 1)) :: cleanupWord (q + 1))).length =
      (serviceCount q + (cleanupWord (q + 1)).length) + (q + 1)
    rw [List.length_append, List.length_cons, ih]
    omega

/-- The premise is the charging claim being tested, not a supplied physical law. -/
theorem charge_telescope (V : Nat → Nat) :
    ∀ q, (∀ t, t < q → (cleanupWord (t + 1)).length + V (t + 1) ≤ V t) →
      serviceCount q + V q ≤ V 0 := by
  intro q
  induction q with
  | zero =>
    intro h
    simpa only [serviceCount, Nat.zero_add] using Nat.le_refl (V 0)
  | succ q ih =>
    intro h
    have hp := ih (fun t ht => h t (by omega))
    have hl := h q (by omega)
    change (serviceCount q + (cleanupWord (q + 1)).length) + V (q + 1) ≤ V 0
    omega

/-- Numeric consequence of the explicitly assumed cycle funding inequalities.
This theorem does not establish the parameterized physical comb execution;
`comb8_services_strict` certifies its concrete eight-site instance. -/
theorem comb_reserve_obstruction (q reserve0 : Nat) (V : Nat → Nat)
    (hstart : V 0 = 3 * q + 6 + reserve0) (hend : 6 ≤ V q)
    (hcharge : ∀ t, t < q → (cleanupWord (t + 1)).length + V (t + 1) ≤ V t) :
    2 * q * q ≤ reserve0 := by
  have ht := charge_telescope V q hcharge
  rw [service_count, hstart] at ht
  omega

theorem no_linear_bound (K : Nat) :
    ¬ (∀ q : Nat, 2 * q * q ≤ K * (2 * q + 6)) := by
  intro h
  have hb := h (K + 4)
  simp only [Nat.mul_add, Nat.add_mul] at hb
  have hh : K * (2 * K) = 2 * K * K := by ac_rfl
  rw [hh] at hb
  omega

/-- The five-site local witness leaves a unit third gap: not global spacing. -/
theorem five_site_local :
    let L : GapFrame 5 := frame (by decide) ⟨0, by decide⟩ 2 (by decide) (by decide)
    let R : GapFrame 5 := frame (by decide) ⟨2, by decide⟩ 2 (by decide) (by decide)
    let M : GapFrame 5 := frame (by decide) ⟨0, by decide⟩ 4 (by decide) (by decide)
    checkedInvariant L (smallPre : Config 5) ∧
    checkedInvariant R (smallPre : Config 5) ∧
    checkedInvariant M (smallPost : Config 5) ∧
    (∀ x : Fin 5, step (by decide) smallPre ⟨2, by decide⟩ x = smallPost x) ∧
    sectorWC 2 L.pos smallPre = 1 ∧ sectorWC 2 R.pos smallPre = 3 ∧
    sectorWC 4 M.pos smallPost = 7 := by decide

/-- With two leaders the merged sector is the whole ring, hence outside the
legal `GapFrame.d < n` interface, although its raw rank is still seven. -/
theorem two_leader_boundary :
    let L : GapFrame 4 := frame (by decide) ⟨0, by decide⟩ 2 (by decide) (by decide)
    let R : GapFrame 4 := frame (by decide) ⟨2, by decide⟩ 2 (by decide) (by decide)
    checkedInvariant L (smallPre : Config 4) ∧ checkedInvariant R (smallPre : Config 4) ∧
    (∀ x : Fin 4, step (by decide) smallPre ⟨2, by decide⟩ x = smallPost x) ∧
    (∀ x : Fin 4, (smallPost x).leader = true ↔ x.val = 0) ∧
    sectorWC 4 L.pos smallPost = 7 ∧ ¬ (4 < 4) := by decide

def pre2 (x : Fin 2) : AgentState 2 :=
  atom x true false (if x.val = 1 then 2 else 0) 0

def pos2 (k : Nat) : Fin 2 := ⟨(1 + k) % 2, Nat.mod_lt _ (by decide)⟩

/-- Unit pre-gaps are outside the spacing assumptions. This checks only the
actual two-site deletion and the raw full-ring rank. -/
theorem two_site_boundary :
    (∀ x : Fin 2, (step (by decide) pre2 ⟨0, by decide⟩ x).leader = true ↔ x.val = 1) ∧
    sectorWC 2 pos2 (step (by decide) pre2 ⟨0, by decide⟩) = 4 := by decide

theorem spacing_arithmetic (a b : Nat) :
    (2 ≤ a → 2 ≤ b → 4 ≤ a + b) ∧ (1 ≤ a → 1 ≤ b → 2 ≤ a + b) := by omega

end Leader.K2MergeInflation

#print axioms Leader.K2MergeInflation.hpsi
#print axioms Leader.K2MergeInflation.step_is_sinkStepC
#print axioms Leader.K2MergeInflation.checkedInvariant_actual
#print axioms Leader.K2MergeInflation.checkedInvariant_iff
#print axioms Leader.K2MergeInflation.readyAt_iff
#print axioms Leader.K2MergeInflation.doneAt_iff
#print axioms Leader.K2MergeInflation.sectorWC_is_gapWC
#print axioms Leader.K2MergeInflation.topIdx_append_nonzero
#print axioms Leader.K2MergeInflation.splice_rank_of_scans
#print axioms Leader.K2MergeInflation.rebase_balance
#print axioms Leader.K2MergeInflation.mergedFrame_right_pos
#print axioms Leader.K2MergeInflation.prepared_step_fields
#print axioms Leader.K2MergeInflation.merged_invariant_of_prepared
#print axioms Leader.K2MergeInflation.merged_rank_of_prepared
#print axioms Leader.K2MergeInflation.merged_rebase_balance
#print axioms Leader.K2MergeInflation.actual_deletion_merge
#print axioms Leader.K2MergeInflation.kernel_delete_row
#print axioms Leader.K2MergeInflation.six_step
#print axioms Leader.K2MergeInflation.six_invariants
#print axioms Leader.K2MergeInflation.six_ranks
#print axioms Leader.K2MergeInflation.six_dynamic_sum
#print axioms Leader.K2MergeInflation.six_leader_layout
#print axioms Leader.K2MergeInflation.six_geometry
#print axioms Leader.K2MergeInflation.six_minimal_under_spacing
#print axioms Leader.K2MergeInflation.history6_to_before
#print axioms Leader.K2MergeInflation.history6_invariants
#print axioms Leader.K2MergeInflation.comb8_to_next
#print axioms Leader.K2MergeInflation.comb8_prefix_invariants
#print axioms Leader.K2MergeInflation.comb8_actual_prefix_invariants
#print axioms Leader.K2MergeInflation.comb8_next_deletion
#print axioms Leader.K2MergeInflation.comb8_ranks
#print axioms Leader.K2MergeInflation.comb8_services_strict
#print axioms Leader.K2MergeInflation.comb8_global_ranks
#print axioms Leader.K2MergeInflation.visits_split
#print axioms Leader.K2MergeInflation.comb8_fresh_and_repeat
#print axioms Leader.K2MergeInflation.local_credit_demand
#print axioms Leader.K2MergeInflation.cycle_prefix_bound
#print axioms Leader.K2MergeInflation.cycle_budget_lower
#print axioms Leader.K2MergeInflation.even_scaled_reserve_lower
#print axioms Leader.K2MergeInflation.even_scaled_total_lower
#print axioms Leader.K2MergeInflation.down_length
#print axioms Leader.K2MergeInflation.up_length
#print axioms Leader.K2MergeInflation.cleanup_length
#print axioms Leader.K2MergeInflation.service_count
#print axioms Leader.K2MergeInflation.comb_length
#print axioms Leader.K2MergeInflation.charge_telescope
#print axioms Leader.K2MergeInflation.comb_reserve_obstruction
#print axioms Leader.K2MergeInflation.no_linear_bound
#print axioms Leader.K2MergeInflation.five_site_local
#print axioms Leader.K2MergeInflation.two_leader_boundary
#print axioms Leader.K2MergeInflation.two_site_boundary
#print axioms Leader.K2MergeInflation.spacing_arithmetic
