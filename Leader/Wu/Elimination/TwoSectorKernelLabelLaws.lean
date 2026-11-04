import Leader.Wu.Elimination.TwoSectorKernelLiteral

/-!
# Label alignment and the literal-kernel closure laws

`Leader.Wu.Elimination.TwoSectorKernelLiteral` builds an `LDKernelSpec.LDKernel` out of the
repository's literal Algorithm-15 repair
`PPLLRepair.eliminateLeadersNoCollision` and discharges three of the seven
`ClosureCaseLaws` rows outright, leaving four rows packaged as
`LDKernelInstance.MissingLDLemmas` and the credit step packaged as
`LDKernelInstance.MissingTargetCredit`.

This module attacks those four rows against the *literal* kernel.  It

* isolates the label-alignment hypothesis the MOVE and SIGNAL guards read,
  shows that the kernel never writes a `label`, and hence that alignment is an
  invariant of `ldStep` (`labelAligned_ldStep`);
* discharges `atkInterior` and `signalProp` from alignment;
* refutes `tgtInterior` and `middle`: they are *false* for the base kernel,
  because a dummy bullet parked at a leader initiator is not absorbed and the
  same interaction writes the absence signal onto that dummy's own cell;
* records the two remaining fidelity facts (`dummy_not_absorbed_base`,
  `fused_fire_move_phase`) as theorems about the base kernel, and states the
  credit interface for the fused start phase.
-/

namespace LDKernelLaws

set_option autoImplicit false

open LDKernelSpec
open LDKernelInstance
open PPLLRepair

variable {n a b ψ : Nat}

/-! ## The three stages, with their guards inverted

Everything below is stated against `PPLLRepair.eliminateLeadersNoCollision`
through its own staged form; no stage is re-implemented. -/

/-- The successor label that MOVE and SIGNAL compare the responder against. -/
def succLabel (hψ : ψ > 0) (l : AgentState ψ) : Fin ψ :=
  ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩

/-- The staged form with the `let`s eliminated. -/
theorem elim_eq (hψ : ψ > 0) (l r : AgentState ψ) :
    eliminateLeadersNoCollision hψ l r =
      eliminateLeadersNoCollisionSignal (succLabel hψ l)
        (eliminateLeadersNoCollisionMove (succLabel hψ l)
          (eliminateLeadersNoCollisionFire hψ l r).1
          (eliminateLeadersNoCollisionFire hψ l r).2).1
        (eliminateLeadersNoCollisionMove (succLabel hψ l)
          (eliminateLeadersNoCollisionFire hψ l r).1
          (eliminateLeadersNoCollisionFire hψ l r).2).2 := by
  rw [eliminateLeadersNoCollision_eq_staged]
  rfl

/-! ### FIRE -/

theorem fire_fst (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1 =
      if l.leader = true ∧ l.signal_B = (⟨1, by omega⟩ : Fin 2) then
        { l with bullet := (⟨2, by omega⟩ : Fin 3), shield := true,
                 signal_B := (⟨0, by omega⟩ : Fin 2) }
      else l := rfl

theorem fire_snd (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).2 =
      if r.leader = true ∧ r.signal_B = (⟨1, by omega⟩ : Fin 2) then
        { r with bullet := (⟨1, by omega⟩ : Fin 3), shield := false,
                 signal_B := (⟨0, by omega⟩ : Fin 2) }
      else r := rfl

theorem fire_fst_eq_of_not (hψ : ψ > 0) (l r : AgentState ψ)
    (h : ¬ (l.leader = true ∧ l.signal_B = (⟨1, by omega⟩ : Fin 2))) :
    (eliminateLeadersNoCollisionFire hψ l r).1 = l := by
  rw [fire_fst, if_neg h]

theorem fire_snd_eq_of_not (hψ : ψ > 0) (l r : AgentState ψ)
    (h : ¬ (r.leader = true ∧ r.signal_B = (⟨1, by omega⟩ : Fin 2))) :
    (eliminateLeadersNoCollisionFire hψ l r).2 = r := by
  rw [fire_snd, if_neg h]

theorem fire_fst_label (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.label = l.label := by
  rw [fire_fst]; split <;> rfl

theorem fire_snd_label (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).2.label = r.label := by
  rw [fire_snd]; split <;> rfl

theorem fire_snd_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  rw [fire_snd]; split <;> rfl

/-! ### MOVE -/

theorem move_eq_of_responder_zero (nl : Fin ψ) (l r : AgentState ψ)
    (h : r.bullet.val = 0) : eliminateLeadersNoCollisionMove nl l r = (l, r) := by
  unfold eliminateLeadersNoCollisionMove
  rw [if_neg (by omega : ¬ (r.bullet.val > 0 ∧ l.leader = true)),
    if_neg (by omega : ¬ (r.bullet.val > 0 ∧ l.leader = false))]

theorem move_eq_of_leader_not_kill (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true)
    (h : ¬ (r.bullet = (⟨2, by omega⟩ : Fin 3) ∧ l.shield = false)) :
    eliminateLeadersNoCollisionMove nl l r = (l, r) := by
  unfold eliminateLeadersNoCollisionMove
  by_cases hb : r.bullet.val > 0
  · rw [if_pos ⟨hb, hl⟩, if_neg h]
  · rw [if_neg (by omega : ¬ (r.bullet.val > 0 ∧ l.leader = true)),
      if_neg (by simp [hl] : ¬ (r.bullet.val > 0 ∧ l.leader = false))]

theorem move_kill (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hb : r.bullet = (⟨2, by omega⟩ : Fin 3))
    (hs : l.shield = false) :
    eliminateLeadersNoCollisionMove nl l r =
      ({ l with leader := false }, { r with bullet := (⟨1, by omega⟩ : Fin 3) }) := by
  unfold eliminateLeadersNoCollisionMove
  have hbv : r.bullet.val > 0 := by rw [hb]; decide
  rw [if_pos ⟨hbv, hl⟩, if_pos ⟨hb, hs⟩]

theorem move_transport (nl : Fin ψ) (l r : AgentState ψ)
    (hb : r.bullet.val > 0) (hl : l.leader = false) (ha : r.label = nl) :
    eliminateLeadersNoCollisionMove nl l r =
      ({ l with bullet := r.bullet, signal_B := (⟨0, by omega⟩ : Fin 2) },
       { r with bullet := (⟨0, by omega⟩ : Fin 3) }) := by
  unfold eliminateLeadersNoCollisionMove
  rw [if_neg (by simp [hl] : ¬ (r.bullet.val > 0 ∧ l.leader = true)),
    if_pos ⟨hb, hl⟩, if_pos ha]

theorem move_destroy (nl : Fin ψ) (l r : AgentState ψ)
    (hb : r.bullet.val > 0) (hl : l.leader = false) (ha : r.label ≠ nl) :
    eliminateLeadersNoCollisionMove nl l r =
      (l, { r with bullet := (⟨0, by omega⟩ : Fin 3) }) := by
  unfold eliminateLeadersNoCollisionMove
  rw [if_neg (by simp [hl] : ¬ (r.bullet.val > 0 ∧ l.leader = true)),
    if_pos ⟨hb, hl⟩, if_neg ha]

theorem move_fst_label (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove nl l r).1.label = l.label := by
  unfold eliminateLeadersNoCollisionMove
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

theorem move_snd_label (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove nl l r).2.label = r.label := by
  unfold eliminateLeadersNoCollisionMove
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

/-! ### SIGNAL -/

theorem signal_fst (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal nl l r).1 = l := rfl

theorem signal_snd_eq_of_closed (nl : Fin ψ) (l r : AgentState ψ)
    (h : ¬ (r.label = nl ∨ l.leader = true)) :
    (eliminateLeadersNoCollisionSignal nl l r).2 = r := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  rw [if_neg h]

theorem signal_snd_of_live (nl : Fin ψ) (l r : AgentState ψ)
    (h : r.label = nl ∨ l.leader = true)
    (hb : r.bullet = (⟨2, by omega⟩ : Fin 3)) :
    (eliminateLeadersNoCollisionSignal nl l r).2 =
      { r with signal_B := (⟨0, by omega⟩ : Fin 2) } := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  rw [if_pos h, if_pos hb]

theorem signal_snd_frame (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal nl l r).2.leader = r.leader ∧
    (eliminateLeadersNoCollisionSignal nl l r).2.label = r.label ∧
    (eliminateLeadersNoCollisionSignal nl l r).2.shield = r.shield ∧
    (eliminateLeadersNoCollisionSignal nl l r).2.bullet = r.bullet := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  split
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩


/-- The two inhabitants of `Fin 2`. -/
theorem fin2_cases (x : Fin 2) :
    x = (⟨0, by omega⟩ : Fin 2) ∨ x = (⟨1, by omega⟩ : Fin 2) := by
  have hx : x.val = 0 ∨ x.val = 1 := by omega
  rcases hx with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- A quiet initiator (follower, no absence signal) leaves the responder's
absence signal alone. -/
theorem signal_snd_signal_of_quiet (nl : Fin ψ) (l r : AgentState ψ)
    (hlf : l.leader = false) (hl0 : l.signal_B = (⟨0, by omega⟩ : Fin 2))
    (hb : r.bullet ≠ (⟨2, by omega⟩ : Fin 3)) :
    (eliminateLeadersNoCollisionSignal nl l r).2.signal_B = r.signal_B := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  by_cases hg : r.label = nl ∨ l.leader = true
  · rw [if_pos hg, if_neg hb]
    dsimp only
    rw [hl0, hlf]
    rcases fin2_cases r.signal_B with h2 | h2 <;> rw [h2] <;> decide
  · rw [if_neg hg]

/-- A leader initiator, or a present absence signal at either endpoint, writes
the absence signal at a non-live responder. -/
theorem signal_snd_signal_one (nl : Fin ψ) (l r : AgentState ψ)
    (hg : r.label = nl ∨ l.leader = true)
    (hb : r.bullet ≠ (⟨2, by omega⟩ : Fin 3))
    (hsrc : l.leader = true ∨ l.signal_B = (⟨1, by omega⟩ : Fin 2) ∨
      r.signal_B = (⟨1, by omega⟩ : Fin 2)) :
    (eliminateLeadersNoCollisionSignal nl l r).2.signal_B =
      (⟨1, by omega⟩ : Fin 2) := by
  unfold eliminateLeadersNoCollisionSignal
  dsimp only
  rw [if_pos hg, if_neg hb]
  dsimp only
  rcases fin2_cases l.signal_B with h1 | h1 <;>
    rcases fin2_cases r.signal_B with h2 | h2 <;>
    cases hL : l.leader <;>
    rw [h1, h2] <;>
    first
      | decide
      | (exfalso
         rcases hsrc with hs | hs | hs
         · rw [hL] at hs; exact Bool.noConfusion hs
         · rw [h1] at hs; exact absurd hs (by decide)
         · rw [h2] at hs; exact absurd hs (by decide))

/-! ## Labels are never written -/

theorem kernel_fst_label (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollision hψ l r).1.label = l.label := by
  rw [elim_eq, signal_fst, move_fst_label, fire_fst_label]

theorem kernel_snd_label (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollision hψ l r).2.label = r.label := by
  rw [elim_eq]
  rw [(signal_snd_frame (succLabel hψ l) _ _).2.1, move_snd_label,
    fire_snd_label]

/-- The literal kernel never writes a `label`, in any stage and at either
endpoint.  This is what makes label alignment an invariant rather than an
assumption that has to be re-established. -/
theorem ldStep_label (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e k : Fin n) : (ldStep F C e k).label = (C k).label := by
  by_cases h1 : k = e
  · subst h1
    show (updatePair C k (F.ring.rightNeighbor k) _ k).label = (C k).label
    rw [updatePair_initiator]
    exact kernel_fst_label F.hpsi _ _
  · by_cases h2 : k = F.ring.rightNeighbor e
    · show (updatePair C e (F.ring.rightNeighbor e) _ k).label = (C k).label
      rw [h2, updatePair_responder _ _ _ _ (by rw [← h2]; exact h1)]
      exact kernel_snd_label F.hpsi _ _
    · rw [ldStep_other F C e k h1 h2]

/-! ## Label alignment on the block -/

/-- The block's cells carry the successor-label sequence that the literal
MOVE and SIGNAL guards compare against.

This is the block-local form of the repository's `noFreeBarrier` geometry
(`Leader/Wu/Safety/SafeConfig.lean`).  `noFreeBarrier` forces successor labels *only* at
edges whose responder is a follower
(`successor_label_of_noFreeBarrier_of_right_not_leader`), so it is strictly
weaker than `LabelAligned`: the two block edges whose responder is a tagged
leader -- the edge `Lj` entering the target and the edge entering the attacker
-- are exactly the ones it does not constrain, and they are exactly the ones on
which the fused FIRE/MOVE of a responder dummy happens. -/
def LabelAligned (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ) : Prop :=
  ∀ s : Nat, s ≤ a + b →
    (C (F.pos (s + 1))).label.val = ((C (F.pos s)).label.val + 1) % ψ

/-- Alignment is preserved by every raw step, because no stage writes a
label. -/
theorem labelAligned_ldStep (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n) (h : LabelAligned F C) :
    LabelAligned F (ldStep F C e) := by
  intro s hs
  rw [ldStep_label, ldStep_label]
  exact h s hs

/-- Alignment on the edge whose initiator sits at block offset at most
`a + b`, in exactly the form the MOVE and SIGNAL guards test. -/
theorem aligned_edge (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (hal : LabelAligned F C) (e : Fin n) (hs : F.off e ≤ a + b) :
    (C (F.ring.rightNeighbor e)).label = succLabel F.hpsi (C e) := by
  have h := hal (F.off e) hs
  rw [← rightNeighbor_eq F e, F.pos_off e] at h
  exact Fin.ext h

/-- What the repository's Condition 3 does give: alignment at every edge whose
responder is a follower.  The complement of this statement inside the block is
the honest content of `LabelAligned`. -/
theorem aligned_edge_of_noFreeBarrier (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (hfree : noFreeBarrier F.hpsi F.ring C)
    (e : Fin n) (hr : (C (F.ring.rightNeighbor e)).leader = false) :
    (C (F.ring.rightNeighbor e)).label = succLabel F.hpsi (C e) :=
  successor_label_of_noFreeBarrier_of_right_not_leader F.hpsi F.ring C hfree e
    (by simp [AgentState.isLeader, hr])


/-! ## Observational transport of the sealed normal form

`AtkSealed`, `TgtSealed` and `MiddleShared` read exactly four of the thirty-odd
`AgentState` fields.  Transporting them therefore only needs those four to
agree, which is what the stage lemmas above deliver; `sealed_of_block_fixed`
of `LDKernelInstance` needs full cell equality and is too rigid for the
interior cases. -/

/-- The four fields the sealed two-sector normal form reads. -/
def sameObs (u v : AgentState ψ) : Prop :=
  u.leader = v.leader ∧ u.shield = v.shield ∧ u.bullet = v.bullet ∧
    u.signal_B = v.signal_B

theorem sameObs_of_eq {u v : AgentState ψ} (h : u = v) : sameObs u v := by
  subst h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem tgtBullet_obs (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ b → (D (F.pos t)).bullet = (C (F.pos t)).bullet) :
    tgtBullet F D = tgtBullet F C := by
  funext t
  simp only [tgtBullet]
  split
  · rename_i hh; rw [h t hh.1 hh.2]
  · rfl

theorem tgtSig_obs (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ b → (D (F.pos t)).signal_B = (C (F.pos t)).signal_B) :
    tgtSig F D = tgtSig F C := by
  funext t
  simp only [tgtSig]
  split
  · rename_i hh; rw [h t hh.1 hh.2]
  · rfl

theorem atkBullet_obs (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ a →
      (D (F.pos (b + t))).bullet = (C (F.pos (b + t))).bullet) :
    atkBullet F D = atkBullet F C := by
  funext t
  simp only [atkBullet]
  split
  · rename_i hh; rw [h t hh.1 hh.2]
  · rfl

theorem atkSig_obs (F : BlockFrame n a b ψ) (C D : Fin n → AgentState ψ)
    (h : ∀ t, 1 ≤ t → t ≤ a →
      (D (F.pos (b + t))).signal_B = (C (F.pos (b + t))).signal_B) :
    atkSig F D = atkSig F C := by
  funext t
  simp only [atkSig]
  split
  · rename_i hh; rw [h t hh.1 hh.2]
  · rfl

/-- The observational refinement of `LDKernelInstance.sealed_of_block_fixed`. -/
theorem sealed_of_block_obs (F : BlockFrame n a b ψ)
    (C D : Fin n → AgentState ψ)
    (hfix : ∀ s, 1 ≤ s → s ≤ a + b → sameObs (D (F.pos s)) (C (F.pos s)))
    (hV : (D F.victim).leader = true)
    (hJ : (D F.target).leader = true)
    (hA : (D F.attacker).leader = true)
    (hAtk : AtkSealed F C) (hTgt : TgtSealed F C) (hMid : MiddleShared F C) :
    AtkSealed F D ∧ TgtSealed F D ∧ MiddleShared F D := by
  have hb := F.hb
  have ha := F.ha
  have htcell : ∀ t, 1 ≤ t → t ≤ b → sameObs (D (F.pos t)) (C (F.pos t)) := by
    intro t h1 h2; exact hfix t h1 (by omega)
  have hacell : ∀ t, 1 ≤ t → t ≤ a →
      sameObs (D (F.pos (b + t))) (C (F.pos (b + t))) := by
    intro t h1 h2; exact hfix (b + t) (by omega) (by omega)
  have hJcell : sameObs (D F.target) (C F.target) := hfix b (by omega) (by omega)
  have hAcell : sameObs (D F.attacker) (C F.attacker) :=
    hfix (a + b) (by omega) (by omega)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [atkBullet_obs F C D (fun t h1 h2 => (hacell t h1 h2).2.2.1),
      atkSig_obs F C D (fun t h1 h2 => (hacell t h1 h2).2.2.2)]
    exact hAtk.1
  · intro t h1 h2
    rw [(hacell t h1 (by omega)).1]
    exact hAtk.2 t h1 h2
  · rw [tgtBullet_obs F C D (fun t h1 h2 => (htcell t h1 h2).2.2.1),
      tgtSig_obs F C D (fun t h1 h2 => (htcell t h1 h2).2.2.2)]
    exact hTgt.1
  · intro t h1 h2
    rw [(htcell t h1 (by omega)).1]
    exact hTgt.2 t h1 h2
  · refine ⟨hV, hJ, hA, ?_, ?_, ?_, ?_⟩
    · intro t h1 h2 hbul
      rw [hJcell.2.1]
      refine hMid.2.2.2.1 t h1 h2 ?_
      rw [← (htcell t h1 h2).2.2.1]; exact hbul
    · intro t h1 h2 hbul
      rw [hJcell.2.1]
      refine hMid.2.2.2.2.1 t h1 h2 ?_
      rw [← (htcell t h1 h2).2.2.1]; exact hbul
    · intro t h1 h2 hbul
      rw [hAcell.2.1]
      refine hMid.2.2.2.2.2.1 t h1 h2 ?_
      rw [← (hacell t h1 h2).2.2.1]; exact hbul
    · intro t h1 h2 hbul
      rw [hAcell.2.1]
      refine hMid.2.2.2.2.2.2 t h1 h2 ?_
      rw [← (hacell t h1 h2).2.2.1]; exact hbul

/-! ## Sector-level combinatorics of the sealed normal form -/

/-- A bullet stepping from sector index `k+1` to `k`, clearing the absence
signal at its new cell, keeps a sector sealed. -/
theorem sectorSealed_move (bv sv bv' sv' : Nat → Nat) (d k : Nat)
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ d)
    (hs : SectorSealed bv sv d) (hnz : bv (k + 1) ≠ 0)
    (hb' : ∀ t, 1 ≤ t → t ≤ d →
      bv' t = if t = k then bv (k + 1) else if t = k + 1 then 0 else bv t)
    (hv' : ∀ t, 1 ≤ t → t ≤ d → sv' t = if t = k then 0 else sv t) :
    SectorSealed bv' sv' d := by
  have honly : ∀ t, 1 ≤ t → t ≤ d → bv' t ≠ 0 → t = k := by
    intro t h1 h2 hne
    rw [hb' t h1 h2] at hne
    by_cases htk : t = k
    · exact htk
    rw [if_neg htk] at hne
    by_cases htk1 : t = k + 1
    · rw [if_pos htk1] at hne; exact absurd rfl hne
    rw [if_neg htk1] at hne
    exact absurd (hs.atMostOneBullet t (k + 1) h1 h2 (by omega) hk2 hne hnz) htk1
  refine ⟨?_, ?_, ?_⟩
  · intro t u h1 h2 h3 h4 hbt hbu
    rw [honly t h1 h2 hbt, honly u h3 h4 hbu]
  · intro s t h1 hst htd hsig
    rw [hv' t (by omega) htd] at hsig
    by_cases htk : t = k
    · rw [if_pos htk] at hsig; exact absurd hsig (by omega)
    rw [if_neg htk] at hsig
    have htlt : t < k := by
      rcases Nat.lt_or_ge t k with hlt | hge
      · exact hlt
      · exact absurd (hs.bulletClears (k + 1) t (by omega) hk2 (by omega) htd hnz)
          (by omega)
    rw [hv' s h1 (by omega), if_neg (by omega)]
    exact hs.signalDownSet s t h1 hst htd hsig
  · intro t s h1 h2 hts hsd hbt
    have htk := honly t h1 h2 hbt
    rw [hv' s (by omega) hsd]
    by_cases hsk : s = k
    · rw [if_pos hsk]
    rw [if_neg hsk]
    exact hs.bulletClears (k + 1) s (by omega) hk2 (by omega) hsd hnz

/-- Writing the absence signal at sector index `k` keeps a sector sealed,
provided every strictly lower cell already carries the signal and `k` itself
carries no bullet.  Those are exactly the two facts the `signalProp` guard and
the sealed hypothesis supply. -/
theorem sectorSealed_signal (bv sv sv' : Nat → Nat) (d k : Nat)
    (hk1 : 1 ≤ k) (hk2 : k ≤ d)
    (hs : SectorSealed bv sv d) (hbk : bv k = 0)
    (hdown : ∀ u, 1 ≤ u → u < k → sv u = 1)
    (hv' : ∀ t, 1 ≤ t → t ≤ d → sv' t = if t = k then 1 else sv t) :
    SectorSealed bv sv' d := by
  refine ⟨hs.atMostOneBullet, ?_, ?_⟩
  · intro s t h1 hst htd hsig
    rw [hv' s h1 (by omega)]
    by_cases hsk : s = k
    · rw [if_pos hsk]
    rw [if_neg hsk]
    by_cases hslt : s < k
    · exact hdown s h1 hslt
    · have hkt : k < t := by omega
      rw [hv' t (by omega) htd, if_neg (by omega)] at hsig
      exact hs.signalDownSet s t h1 hst htd hsig
  · intro t s h1 h2 hts hsd hbt
    rw [hv' s (by omega) hsd]
    by_cases hsk : s = k
    · exfalso
      have htk : t ≤ k := by omega
      by_cases hteq : t = k
      · rw [hteq, hbk] at hbt; exact hbt rfl
      · have h1' := hdown t h1 (by omega)
        have h2' := hs.bulletClears t t h1 h2 (Nat.le_refl t) h2 hbt
        omega
    rw [if_neg hsk]
    exact hs.bulletClears t s h1 h2 hts hsd hbt

/-- A leader that fires a responder dummy which is transported in the same
interaction leaves the sector sealed with the single dummy at index `d - 1`. -/
theorem sectorSealed_fire_move (bv sv bv' sv' : Nat → Nat) (d : Nat)
    (hd : 2 ≤ d) (hs : SectorSealed bv sv d)
    (hb' : ∀ t, 1 ≤ t → t ≤ d → bv' t = if t = d - 1 then 1 else 0)
    (hv' : ∀ t, 1 ≤ t → t ≤ d →
      sv' t = if t = d - 1 ∨ t = d then 0 else sv t) :
    SectorSealed bv' sv' d := by
  refine ⟨?_, ?_, ?_⟩
  · intro t u h1 h2 h3 h4 hbt hbu
    rw [hb' t h1 h2] at hbt
    rw [hb' u h3 h4] at hbu
    by_cases htk : t = d - 1
    · by_cases huk : u = d - 1
      · rw [htk, huk]
      · rw [if_neg huk] at hbu; exact absurd rfl hbu
    · rw [if_neg htk] at hbt; exact absurd rfl hbt
  · intro s t h1 hst htd hsig
    rw [hv' t (by omega) htd] at hsig
    by_cases htk : t = d - 1 ∨ t = d
    · rw [if_pos htk] at hsig; exact absurd hsig (by omega)
    rw [if_neg htk] at hsig
    rw [hv' s h1 (by omega), if_neg (by omega)]
    exact hs.signalDownSet s t h1 hst htd hsig
  · intro t s h1 h2 hts hsd hbt
    rw [hb' t h1 h2] at hbt
    by_cases htk : t = d - 1
    · rw [hv' s (by omega) hsd, if_pos (by omega)]
    · rw [if_neg htk] at hbt; exact absurd rfl hbt


/-! ## One interior transport step, literally -/

theorem block_two_le (F : BlockFrame n a b ψ) : 2 ≤ n := by
  have := F.hblock; have := F.ha; have := F.hb; omega

theorem rightNeighbor_ne (F : BlockFrame n a b ψ) (e : Fin n) :
    F.ring.rightNeighbor e ≠ e := by
  intro h
  have h2 := congrArg Fin.val h
  have hn2 := block_two_le F
  have hlt : e.val < n := e.isLt
  show False
  have : (e.val + 1) % n = e.val := h2
  by_cases hc : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hc] at this; omega
  · have he : e.val + 1 = n := by omega
    rw [he, Nat.mod_self] at this; omega

theorem move_transport_fst (nl : Fin ψ) (l r : AgentState ψ)
    (hb : r.bullet.val > 0) (hl : l.leader = false) (ha : r.label = nl) :
    (eliminateLeadersNoCollisionMove nl l r).1 =
      { l with bullet := r.bullet, signal_B := (⟨0, by omega⟩ : Fin 2) } := by
  rw [move_transport nl l r hb hl ha]

theorem move_transport_snd (nl : Fin ψ) (l r : AgentState ψ)
    (hb : r.bullet.val > 0) (hl : l.leader = false) (ha : r.label = nl) :
    (eliminateLeadersNoCollisionMove nl l r).2 =
      { r with bullet := (⟨0, by omega⟩ : Fin 3) } := by
  rw [move_transport nl l r hb hl ha]

/-- The literal effect of one *interior* interaction: a follower initiator, a
label-aligned responder carrying a bullet and no absence signal.  FIRE is
inert, MOVE transports the bullet and clears the initiator's signal, SIGNAL
leaves the responder's signal alone. -/
theorem ldStep_transport (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n)
    (hl : (C e).leader = false)
    (hbz : (C (F.ring.rightNeighbor e)).bullet.val ≠ 0)
    (hsz : (C (F.ring.rightNeighbor e)).signal_B = (⟨0, by omega⟩ : Fin 2))
    (hal : (C (F.ring.rightNeighbor e)).label = succLabel F.hpsi (C e)) :
    ldStep F C e e =
        { (C e) with bullet := (C (F.ring.rightNeighbor e)).bullet,
                     signal_B := (⟨0, by omega⟩ : Fin 2) } ∧
      (ldStep F C e (F.ring.rightNeighbor e)).leader =
        (C (F.ring.rightNeighbor e)).leader ∧
      (ldStep F C e (F.ring.rightNeighbor e)).shield =
        (C (F.ring.rightNeighbor e)).shield ∧
      (ldStep F C e (F.ring.rightNeighbor e)).bullet =
        (⟨0, by omega⟩ : Fin 3) ∧
      (ldStep F C e (F.ring.rightNeighbor e)).signal_B =
        (C (F.ring.rightNeighbor e)).signal_B := by
  have hne : F.ring.rightNeighbor e ≠ e := rightNeighbor_ne F e
  have h1 : (eliminateLeadersNoCollisionFire F.hpsi (C e)
      (C (F.ring.rightNeighbor e))).1 = C e :=
    fire_fst_eq_of_not _ _ _ (by rw [hl]; rintro ⟨hcon, -⟩; exact Bool.noConfusion hcon)
  have h2 : (eliminateLeadersNoCollisionFire F.hpsi (C e)
      (C (F.ring.rightNeighbor e))).2 = C (F.ring.rightNeighbor e) :=
    fire_snd_eq_of_not _ _ _
      (by rintro ⟨-, hcon⟩; rw [hsz] at hcon
          have hv : (0 : Nat) = 1 := congrArg Fin.val hcon
          omega)
  have hE := elim_eq F.hpsi (C e) (C (F.ring.rightNeighbor e))
  rw [h1, h2,
    move_transport_fst (succLabel F.hpsi (C e)) (C e) (C (F.ring.rightNeighbor e))
      (by omega) hl hal,
    move_transport_snd (succLabel F.hpsi (C e)) (C e) (C (F.ring.rightNeighbor e))
      (by omega) hl hal] at hE
  have hstep1 : ldStep F C e e =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).1 :=
    updatePair_initiator C e (F.ring.rightNeighbor e) _
  have hstep2 : ldStep F C e (F.ring.rightNeighbor e) =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).2 :=
    updatePair_responder C e (F.ring.rightNeighbor e) _ hne
  rw [hE] at hstep1 hstep2
  rw [signal_fst] at hstep1
  refine ⟨hstep1, ?_, ?_, ?_, ?_⟩
  · rw [hstep2]; exact (signal_snd_frame _ _ _).1
  · rw [hstep2]; exact (signal_snd_frame _ _ _).2.2.1
  · rw [hstep2]; exact (signal_snd_frame _ _ _).2.2.2
  · rw [hstep2]
    refine signal_snd_signal_of_quiet _ _ _ hl rfl ?_
    intro hcon
    have hv : (0 : Nat) = 2 := congrArg Fin.val hcon
    omega


/-! ## Inverting the remaining rows of the case split -/

theorem off_of_atkInterior (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hcase : ldCaseOf F C e = BlockRawCase.atkInterior) :
    F.off e + 1 ≠ n ∧ b < F.off e ∧ F.off e < a + b ∧
      (C (F.pos (F.off e + 1))).bullet.val ≠ 0 := by
  unfold ldCaseOf at hcase
  by_cases h1 : F.off e + 1 = n
  · rw [if_pos h1] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h1] at hcase
  by_cases h2 : a + b < F.off e
  · rw [if_pos h2] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h2] at hcase
  by_cases h3 : F.off e = a + b
  · rw [if_pos h3] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h3] at hcase
  by_cases h4 : F.off e + 1 = b ∨ F.off e = b
  · rw [if_pos h4] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h4] at hcase
  by_cases h5 : (C (F.pos (F.off e + 1))).bullet.val = 0
  · rw [if_pos h5] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h5] at hcase
  by_cases h6 : F.off e < b
  · rw [if_pos h6] at hcase; exact BlockRawCase.noConfusion hcase
  rw [if_neg h6] at hcase
  refine ⟨h1, ?_, by omega, h5⟩
  have : F.off e ≠ b := fun hh => h4 (Or.inr hh)
  omega

/-! ## `atkInterior`, discharged from label alignment -/

/-- A bullet move strictly inside the attacker's gap preserves the sealed
two-sector normal form.  This discharges `MissingLDLemmas.atkInterior` under
`LabelAligned`. -/
theorem atkInterior_of_aligned (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n) (hal : LabelAligned F C)
    (hcase : ldCaseOf F C e = BlockRawCase.atkInterior)
    (hAtk : AtkSealed F C) (hTgt : TgtSealed F C) (hMid : MiddleShared F C)
    (hsurv : ldDeleted F (ldStep F C e) ≠ true) :
    AtkSealed F (ldStep F C e) ∧ TgtSealed F (ldStep F C e) ∧
      MiddleShared F (ldStep F C e) := by
  obtain ⟨hn1, hgt, hlt, hbnz⟩ := off_of_atkInterior F C e hcase
  obtain ⟨hVl, hJl, hAl⟩ := leaders_of_survives F C e hsurv
  have ha := F.ha
  have hb := F.hb
  have hbl := F.hblock
  obtain ⟨k, hk⟩ : ∃ k, F.off e = b + k := ⟨F.off e - b, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hka : k + 1 ≤ a := by omega
  have hpe : F.pos (b + k) = e := by rw [← hk]; exact F.pos_off e
  have hre : F.ring.rightNeighbor e = F.pos (b + (k + 1)) := by
    rw [rightNeighbor_eq F e, hk]
    rfl
  -- the literal interaction
  have hlf : (C e).leader = false := by
    have := hAtk.2 k hk1 (by omega)
    rwa [hpe] at this
  have hrb : (C (F.ring.rightNeighbor e)).bullet.val ≠ 0 := by
    rw [rightNeighbor_eq F e]; exact hbnz
  have hbnzk : atkBullet F C (k + 1) ≠ 0 := by
    rw [atkBullet_val F C (k + 1) (by omega) hka, ← hre]; exact hrb
  have hrs : (C (F.ring.rightNeighbor e)).signal_B = (⟨0, by omega⟩ : Fin 2) := by
    have h0 := hAtk.1.bulletClears (k + 1) (k + 1) (by omega) hka
      (Nat.le_refl _) hka hbnzk
    rw [atkSig_val F C (k + 1) (by omega) hka] at h0
    rw [hre]
    exact Fin.ext h0
  have halign : (C (F.ring.rightNeighbor e)).label = succLabel F.hpsi (C e) :=
    aligned_edge F C hal e (by omega)
  obtain ⟨hDe, hDrl, hDrsh, hDrb, hDrsig⟩ :=
    ldStep_transport F C e hlf hrb hrs halign
  -- untouched block cells
  have hfix : ∀ s, s ≤ a + b → s ≠ b + k → s ≠ b + k + 1 →
      ldStep F C e (F.pos s) = C (F.pos s) := by
    intro s hs h1 h2
    exact ldStep_pos_eq F C e s (F.off e + 1) (by omega) (by omega)
      (rightNeighbor_eq F e) (by omega) (by omega)
  -- the target sector is untouched
  have htfix : ∀ t, 1 ≤ t → t ≤ b → ldStep F C e (F.pos t) = C (F.pos t) := by
    intro t h1 h2; exact hfix t (by omega) (by omega) (by omega)
  -- the attacker sector, cell by cell
  have hDatkB : ∀ t, 1 ≤ t → t ≤ a →
      atkBullet F (ldStep F C e) t =
        if t = k then atkBullet F C (k + 1)
        else if t = k + 1 then 0 else atkBullet F C t := by
    intro t h1 h2
    rw [atkBullet_val F _ t h1 h2]
    by_cases htk : t = k
    · rw [if_pos htk, htk, hpe, hDe, hre,
        atkBullet_val F C (k + 1) (by omega) hka]
    rw [if_neg htk]
    by_cases htk1 : t = k + 1
    · rw [if_pos htk1, htk1, ← hre, hDrb]
    · rw [if_neg htk1, hfix (b + t) (by omega) (by omega) (by omega),
        atkBullet_val F C t h1 h2]
  have hDatkS : ∀ t, 1 ≤ t → t ≤ a →
      atkSig F (ldStep F C e) t = if t = k then 0 else atkSig F C t := by
    intro t h1 h2
    rw [atkSig_val F _ t h1 h2]
    by_cases htk : t = k
    · rw [if_pos htk, htk, hpe, hDe]
    rw [if_neg htk]
    by_cases htk1 : t = k + 1
    · rw [htk1, ← hre, hDrsig, hre, ← htk1, atkSig_val F C t h1 h2]
    · rw [hfix (b + t) (by omega) (by omega) (by omega), atkSig_val F C t h1 h2]
  -- assemble
  have hJcell : ldStep F C e F.target = C F.target :=
    hfix b (by omega) (by omega) (by omega)
  have hAsh : (ldStep F C e F.attacker).shield = (C F.attacker).shield := by
    by_cases hka1 : a = k + 1
    · have hattr : F.attacker = F.ring.rightNeighbor e := by
        rw [hre]
        show F.pos (a + b) = F.pos (b + (k + 1))
        rw [← hka1]
        exact congrArg F.pos (by omega)
      rw [hattr]; exact hDrsh
    · have hfx : ldStep F C e F.attacker = C F.attacker :=
        hfix (a + b) (Nat.le_refl _) (by omega) (by omega)
      rw [hfx]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hVl, hJl, hAl, ?_, ?_, ?_, ?_⟩
  · exact sectorSealed_move (atkBullet F C) (atkSig F C)
      (atkBullet F (ldStep F C e)) (atkSig F (ldStep F C e)) a k hk1 hka
      hAtk.1 hbnzk hDatkB hDatkS
  · intro t h1 h2
    by_cases htk : t = k
    · rw [htk, hpe, hDe]; exact hlf
    by_cases htk1 : t = k + 1
    · rw [htk1, ← hre, hDrl, hre, ← htk1]
      exact hAtk.2 t h1 h2
    · rw [hfix (b + t) (by omega) (by omega) (by omega)]
      exact hAtk.2 t h1 h2
  · rw [tgtBullet_obs F C _ (fun t h1 h2 => by rw [htfix t h1 h2]),
      tgtSig_obs F C _ (fun t h1 h2 => by rw [htfix t h1 h2])]
    exact hTgt.1
  · intro t h1 h2
    rw [htfix t h1 (by omega)]
    exact hTgt.2 t h1 h2
  · intro t h1 h2 hbul
    rw [hJcell]
    refine hMid.2.2.2.1 t h1 h2 ?_
    rw [← htfix t h1 h2]; exact hbul
  · intro t h1 h2 hbul
    rw [hJcell]
    refine hMid.2.2.2.2.1 t h1 h2 ?_
    rw [← htfix t h1 h2]; exact hbul
  · intro t h1 h2 hbul
    rw [hAsh]
    rw [← atkBullet_val F _ t h1 h2, hDatkB t h1 h2] at hbul
    by_cases htk : t = k
    · rw [if_pos htk] at hbul
      refine hMid.2.2.2.2.2.1 (k + 1) (by omega) hka ?_
      rw [← atkBullet_val F C (k + 1) (by omega) hka]; exact hbul
    rw [if_neg htk] at hbul
    by_cases htk1 : t = k + 1
    · rw [if_pos htk1] at hbul; exact absurd hbul (by omega)
    rw [if_neg htk1] at hbul
    exact absurd (hAtk.1.atMostOneBullet t (k + 1) h1 h2 (by omega) hka
      (by omega) hbnzk) htk1
  · intro t h1 h2 hbul
    rw [hAsh]
    rw [← atkBullet_val F _ t h1 h2, hDatkB t h1 h2] at hbul
    by_cases htk : t = k
    · rw [if_pos htk] at hbul
      refine hMid.2.2.2.2.2.2 (k + 1) (by omega) hka ?_
      rw [← atkBullet_val F C (k + 1) (by omega) hka]; exact hbul
    rw [if_neg htk] at hbul
    by_cases htk1 : t = k + 1
    · rw [if_pos htk1] at hbul; exact absurd hbul (by omega)
    rw [if_neg htk1] at hbul
    exact absurd (hAtk.1.atMostOneBullet t (k + 1) h1 h2 (by omega) hka
      (by omega) hbnzk) htk1


/-! ## One interaction with no bullet to move -/

theorem fire_fst_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader := by
  rw [fire_fst]; split <;> rfl

theorem fire_fst_signal_of_follower (hψ : ψ > 0) (l r : AgentState ψ)
    (h : l.leader = false) :
    (eliminateLeadersNoCollisionFire hψ l r).1 = l :=
  fire_fst_eq_of_not _ _ _ (by rw [h]; rintro ⟨hcon, -⟩; exact Bool.noConfusion hcon)

/-- The literal effect of an interaction whose responder carries no bullet and
does not fire one: only the responder's absence signal can change. -/
theorem ldStep_no_move (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n)
    (hrb : (C (F.ring.rightNeighbor e)).bullet.val = 0)
    (hrnofire : ¬ ((C (F.ring.rightNeighbor e)).leader = true ∧
      (C (F.ring.rightNeighbor e)).signal_B = (⟨1, by omega⟩ : Fin 2))) :
    (ldStep F C e (F.ring.rightNeighbor e)).leader =
        (C (F.ring.rightNeighbor e)).leader ∧
      (ldStep F C e (F.ring.rightNeighbor e)).shield =
        (C (F.ring.rightNeighbor e)).shield ∧
      (ldStep F C e (F.ring.rightNeighbor e)).bullet =
        (C (F.ring.rightNeighbor e)).bullet ∧
      (((C (F.ring.rightNeighbor e)).label = succLabel F.hpsi (C e) ∨
          (C e).leader = true) →
        ((C e).leader = true ∨ (C e).signal_B = (⟨1, by omega⟩ : Fin 2) ∨
          (C (F.ring.rightNeighbor e)).signal_B = (⟨1, by omega⟩ : Fin 2)) →
        (ldStep F C e (F.ring.rightNeighbor e)).signal_B =
          (⟨1, by omega⟩ : Fin 2)) ∧
      ((C e).leader = false → (C e).signal_B = (⟨0, by omega⟩ : Fin 2) →
        (ldStep F C e (F.ring.rightNeighbor e)).signal_B =
            (C (F.ring.rightNeighbor e)).signal_B ∧
          ldStep F C e e = C e) := by
  have hne : F.ring.rightNeighbor e ≠ e := rightNeighbor_ne F e
  have h2 : (eliminateLeadersNoCollisionFire F.hpsi (C e)
      (C (F.ring.rightNeighbor e))).2 = C (F.ring.rightNeighbor e) :=
    fire_snd_eq_of_not _ _ _ hrnofire
  have hE := elim_eq F.hpsi (C e) (C (F.ring.rightNeighbor e))
  rw [h2] at hE
  rw [move_eq_of_responder_zero (succLabel F.hpsi (C e))
    (eliminateLeadersNoCollisionFire F.hpsi (C e)
      (C (F.ring.rightNeighbor e))).1 (C (F.ring.rightNeighbor e)) hrb] at hE
  have hstep1 : ldStep F C e e =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).1 :=
    updatePair_initiator C e (F.ring.rightNeighbor e) _
  have hstep2 : ldStep F C e (F.ring.rightNeighbor e) =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).2 :=
    updatePair_responder C e (F.ring.rightNeighbor e) _ hne
  rw [hE] at hstep1 hstep2
  rw [signal_fst] at hstep1
  have hnb : (C (F.ring.rightNeighbor e)).bullet ≠ (⟨2, by omega⟩ : Fin 3) := by
    intro hcon
    rw [hcon] at hrb
    have hv : (2 : Nat) = 0 := hrb
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep2]; exact (signal_snd_frame _ _ _).1
  · rw [hstep2]; exact (signal_snd_frame _ _ _).2.2.1
  · rw [hstep2]; exact (signal_snd_frame _ _ _).2.2.2
  · intro hg hs
    rw [hstep2]
    refine signal_snd_signal_one _ _ _ ?_ hnb ?_
    · rcases hg with hg | hg
      · exact Or.inl hg
      · exact Or.inr (by rw [fire_fst_leader]; exact hg)
    · rcases hs with hs | hs | hs
      · exact Or.inl (by rw [fire_fst_leader]; exact hs)
      · by_cases hlf : (C e).leader = true
        · exact Or.inl (by rw [fire_fst_leader]; exact hlf)
        · refine Or.inr (Or.inl ?_)
          have hlf2 : (C e).leader = false := by
            cases hcon : (C e).leader
            · rfl
            · exact absurd hcon hlf
          rw [fire_fst_signal_of_follower _ _ _ hlf2]
          exact hs
      · exact Or.inr (Or.inr hs)
  · intro h1 h2'
    have hfix1 : (eliminateLeadersNoCollisionFire F.hpsi (C e)
        (C (F.ring.rightNeighbor e))).1 = C e :=
      fire_fst_signal_of_follower _ _ _ h1
    constructor
    · rw [hstep2, hfix1]
      exact signal_snd_signal_of_quiet _ _ _ h1 h2' hnb
    · rw [hstep1, hfix1]

/-! ## G3: FIRE and MOVE fuse inside one interaction -/

/-- A responder leader that fires a dummy has that dummy transported in the
*same* interaction: the dummy never rests on the firing leader's own cell.
This is the literal-kernel form of obstruction G3. -/
theorem kernel_fire_move (hψ : ψ > 0) (l r : AgentState ψ)
    (hlf : l.leader = false) (hrl : r.leader = true)
    (hrs : r.signal_B = (⟨1, by omega⟩ : Fin 2))
    (hal : r.label = succLabel hψ l) :
    (eliminateLeadersNoCollision hψ l r).1 =
        { l with bullet := (⟨1, by omega⟩ : Fin 3),
                 signal_B := (⟨0, by omega⟩ : Fin 2) } ∧
      (eliminateLeadersNoCollision hψ l r).2.leader = true ∧
      (eliminateLeadersNoCollision hψ l r).2.shield = false ∧
      (eliminateLeadersNoCollision hψ l r).2.bullet = (⟨0, by omega⟩ : Fin 3) ∧
      (eliminateLeadersNoCollision hψ l r).2.signal_B =
        (⟨0, by omega⟩ : Fin 2) := by
  have h1 : (eliminateLeadersNoCollisionFire hψ l r).1 = l :=
    fire_fst_signal_of_follower _ _ _ hlf
  have h2 : (eliminateLeadersNoCollisionFire hψ l r).2 =
      { r with bullet := (⟨1, by omega⟩ : Fin 3), shield := false,
               signal_B := (⟨0, by omega⟩ : Fin 2) } := by
    rw [fire_snd, if_pos ⟨hrl, hrs⟩]
  have hE := elim_eq hψ l r
  rw [h1, h2] at hE
  rw [move_transport_fst (succLabel hψ l) l
      { r with bullet := (⟨1, by omega⟩ : Fin 3), shield := false,
               signal_B := (⟨0, by omega⟩ : Fin 2) }
      Nat.zero_lt_one hlf hal,
    move_transport_snd (succLabel hψ l) l
      { r with bullet := (⟨1, by omega⟩ : Fin 3), shield := false,
               signal_B := (⟨0, by omega⟩ : Fin 2) }
      Nat.zero_lt_one hlf hal] at hE
  rw [hE, signal_fst]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [(signal_snd_frame _ _ _).1]; exact hrl
  · rw [(signal_snd_frame _ _ _).2.2.1]
  · rw [(signal_snd_frame _ _ _).2.2.2]
  · refine signal_snd_signal_of_quiet _ _ _ hlf rfl ?_
    intro hcon
    have hv : (0 : Nat) = 2 := congrArg Fin.val hcon
    omega

/-- Block form of the fused FIRE/MOVE: a responder leader that fires a dummy on
the edge `e` has that dummy transported to `e`'s own cell inside the *same*
interaction.  Applied at `Lj` this says the reachable phase right after a clean
target dummy firing is `dummy 1`, never `dummy 0`. -/
theorem ldStep_fire_move (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n)
    (hlf : (C e).leader = false)
    (hrl : (C (F.ring.rightNeighbor e)).leader = true)
    (hrs : (C (F.ring.rightNeighbor e)).signal_B = (⟨1, by omega⟩ : Fin 2))
    (hal : (C (F.ring.rightNeighbor e)).label = succLabel F.hpsi (C e)) :
    ldStep F C e e =
        { (C e) with bullet := (⟨1, by omega⟩ : Fin 3),
                     signal_B := (⟨0, by omega⟩ : Fin 2) } ∧
      (ldStep F C e (F.ring.rightNeighbor e)).leader = true ∧
      (ldStep F C e (F.ring.rightNeighbor e)).shield = false ∧
      (ldStep F C e (F.ring.rightNeighbor e)).bullet =
        (⟨0, by omega⟩ : Fin 3) ∧
      (ldStep F C e (F.ring.rightNeighbor e)).signal_B =
        (⟨0, by omega⟩ : Fin 2) := by
  have hne : F.ring.rightNeighbor e ≠ e := rightNeighbor_ne F e
  have hstep1 : ldStep F C e e =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).1 :=
    updatePair_initiator C e (F.ring.rightNeighbor e) _
  have hstep2 : ldStep F C e (F.ring.rightNeighbor e) =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).2 :=
    updatePair_responder C e (F.ring.rightNeighbor e) _ hne
  obtain ⟨g1, g2, g3, g4, g5⟩ :=
    kernel_fire_move F.hpsi (C e) (C (F.ring.rightNeighbor e)) hlf hrl hrs hal
  exact ⟨by rw [hstep1]; exact g1, by rw [hstep2]; exact g2,
    by rw [hstep2]; exact g3, by rw [hstep2]; exact g4,
    by rw [hstep2]; exact g5⟩


/-! ## G2: the base kernel does not absorb a dummy at a leader initiator -/

/-- A dummy bullet standing at a leader initiator is *not* absorbed by the base
Algorithm-15 repair, and the same interaction writes the absence signal onto
that dummy's own cell.  Absorption exists only in `PPLLRepair.dummyBulletSink`,
which the base kernel does not run.  This is obstruction G2, and it is what
makes `MissingLDLemmas.tgtInterior` and `MissingLDLemmas.middle` false. -/
theorem dummy_not_absorbed_base (F : BlockFrame n a b ψ)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hl : (C e).leader = true)
    (hrf : (C (F.ring.rightNeighbor e)).leader = false)
    (hrd : (C (F.ring.rightNeighbor e)).bullet = (⟨1, by omega⟩ : Fin 3)) :
    (ldStep F C e (F.ring.rightNeighbor e)).bullet =
        (⟨1, by omega⟩ : Fin 3) ∧
      (ldStep F C e (F.ring.rightNeighbor e)).signal_B =
        (⟨1, by omega⟩ : Fin 2) := by
  have hne : F.ring.rightNeighbor e ≠ e := rightNeighbor_ne F e
  have hstep2 : ldStep F C e (F.ring.rightNeighbor e) =
      (eliminateLeadersNoCollision F.hpsi (C e) (C (F.ring.rightNeighbor e))).2 :=
    updatePair_responder C e (F.ring.rightNeighbor e) _ hne
  rw [hstep2]
  exact eliminateLeadersNoCollision_right_dummy_signal_of_left_leader F.hpsi
    (C e) (C (F.ring.rightNeighbor e)) hl hrf hrd


theorem kernel_leaders_of_dummy (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hrf : r.leader = false)
    (hrd : r.bullet = (⟨1, by omega⟩ : Fin 3)) :
    (eliminateLeadersNoCollision hψ l r).1.leader = l.leader ∧
      (eliminateLeadersNoCollision hψ l r).2.leader = r.leader := by
  have h2 : (eliminateLeadersNoCollisionFire hψ l r).2 = r :=
    fire_snd_eq_of_not _ _ _ (by rw [hrf]; rintro ⟨hcon, -⟩; exact Bool.noConfusion hcon)
  have hE := elim_eq hψ l r
  rw [h2] at hE
  rw [move_eq_of_leader_not_kill (succLabel hψ l)
      (eliminateLeadersNoCollisionFire hψ l r).1 r
      (by rw [fire_fst_leader]; exact hl)
      (by rintro ⟨hcon, -⟩
          rw [hrd] at hcon
          have hv : (1 : Nat) = 2 := congrArg Fin.val hcon
          omega)] at hE
  rw [hE, signal_fst, fire_fst_leader]
  exact ⟨rfl, (signal_snd_frame _ _ _).1⟩

/-! ## `tgtInterior` and `middle` are false for the base kernel

The two refutations below are the sharp form of obstruction G2.  Both are
instances of the same picture: a dummy bullet standing at a *leader* initiator
survives the interaction (no sink), and the same interaction's SIGNAL stage
writes the absence signal onto the dummy's own cell, so
`SectorSealed.bulletClears` fails at that cell.  No label hypothesis can repair
this: the SIGNAL guard is satisfied through the `l.leader = true` disjunct, so
the failure is independent of `LabelAligned`. -/
theorem tgtInterior_false (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (hb2 : 2 ≤ b) (hoe : F.off e = 0)
    (hMid : MiddleShared F C)
    (hrf : (C (F.ring.rightNeighbor e)).leader = false)
    (hrd : (C (F.ring.rightNeighbor e)).bullet = (⟨1, by omega⟩ : Fin 3)) :
    ldCaseOf F C e = BlockRawCase.tgtInterior ∧
      ldDeleted F (ldStep F C e) ≠ true ∧
      ¬ TgtSealed F (ldStep F C e) := by
  have ha := F.ha
  have hb := F.hb
  have hbl := F.hblock
  have hev : e = F.pos 0 := by rw [← hoe]; exact (F.pos_off e).symm
  have hvic : F.victim = e := by
    change F.pos 0 = e
    exact hev.symm
  have hlead : (C e).leader = true := by rw [← hvic]; exact hMid.1
  have hrn : F.ring.rightNeighbor e = F.pos 1 := by
    rw [rightNeighbor_eq F e, hoe]
  have hbul : (C (F.pos (F.off e + 1))).bullet.val ≠ 0 := by
    rw [hoe]
    show (C (F.pos 1)).bullet.val ≠ 0
    rw [← hrn, hrd]
    intro hcon
    have hv : (1 : Nat) = 0 := hcon
    omega
  refine ⟨?_, ?_, ?_⟩
  · unfold ldCaseOf
    rw [if_neg (by omega : ¬ (F.off e + 1 = n)),
      if_neg (by omega : ¬ (a + b < F.off e)),
      if_neg (by omega : ¬ (F.off e = a + b)),
      if_neg (by omega : ¬ (F.off e + 1 = b ∨ F.off e = b)),
      if_neg hbul, if_pos (by omega : F.off e < b)]
  · -- the three tagged leaders survive
    have hne : F.ring.rightNeighbor e ≠ e := rightNeighbor_ne F e
    obtain ⟨g1, _⟩ := kernel_leaders_of_dummy F.hpsi (C e)
      (C (F.ring.rightNeighbor e)) hlead hrf hrd
    have hVd : (ldStep F C e F.victim).leader = true := by
      rw [hvic]
      have hs1 : ldStep F C e e =
          (eliminateLeadersNoCollision F.hpsi (C e)
            (C (F.ring.rightNeighbor e))).1 :=
        updatePair_initiator C e (F.ring.rightNeighbor e) _
      rw [hs1, g1]; exact hlead
    have hJd : ldStep F C e F.target = C F.target := by
      have : ldStep F C e (F.pos b) = C (F.pos b) :=
        ldStep_pos_eq F C e b (F.off e + 1) (by omega) (by omega)
          (rightNeighbor_eq F e) (by omega) (by omega)
      exact this
    have hAd : ldStep F C e F.attacker = C F.attacker := by
      have : ldStep F C e (F.pos (a + b)) = C (F.pos (a + b)) :=
        ldStep_pos_eq F C e (a + b) (F.off e + 1) (by omega) (by omega)
          (rightNeighbor_eq F e) (by omega) (by omega)
      exact this
    unfold ldDeleted
    rw [hVd, hJd, hAd, hMid.2.1, hMid.2.2.1]
    exact (by decide : ¬ ((!(true && true && true)) = true))
  · intro hseal
    obtain ⟨hbull, hsig⟩ := dummy_not_absorbed_base F C e hlead hrf hrd
    rw [hrn] at hbull hsig
    have h1 : tgtBullet F (ldStep F C e) 1 ≠ 0 := by
      rw [tgtBullet_val F _ 1 (by omega) (by omega), hbull]
      intro hcon
      have hv : (1 : Nat) = 0 := hcon
      omega
    have h2 := hseal.1.bulletClears 1 1 (by omega) (by omega) (by omega)
      (by omega) h1
    rw [tgtSig_val F _ 1 (by omega) (by omega), hsig] at h2
    have hv : (1 : Nat) = 0 := h2
    omega


/-- `MissingLDLemmas.middle` is false, for the same reason, at the target's own
outgoing edge `Rj`: a parked attacker-sector dummy at attacker-sector index `1`
is neither absorbed nor shielded from the target's absence signal. -/
theorem middle_false (F : BlockFrame n a b ψ) (C : Fin n → AgentState ψ)
    (e : Fin n) (ha2 : 2 ≤ a) (hoe : F.off e = b)
    (hMid : MiddleShared F C)
    (hrf : (C (F.ring.rightNeighbor e)).leader = false)
    (hrd : (C (F.ring.rightNeighbor e)).bullet = (⟨1, by omega⟩ : Fin 3)) :
    ldCaseOf F C e = BlockRawCase.middle ∧
      ldDeleted F (ldStep F C e) ≠ true ∧
      ¬ AtkSealed F (ldStep F C e) := by
  have ha := F.ha
  have hb := F.hb
  have hbl := F.hblock
  have hev : e = F.pos b := by
    exact Eq.trans (F.pos_off e).symm (congrArg F.pos hoe)
  have htgt : F.target = e := by
    change F.pos b = e
    exact hev.symm
  have hlead : (C e).leader = true := by rw [← htgt]; exact hMid.2.1
  have hrn : F.ring.rightNeighbor e = F.pos (b + 1) := by
    rw [rightNeighbor_eq F e, hoe]
  refine ⟨?_, ?_, ?_⟩
  · unfold ldCaseOf
    rw [if_neg (by omega : ¬ (F.off e + 1 = n)),
      if_neg (by omega : ¬ (a + b < F.off e)),
      if_neg (by omega : ¬ (F.off e = a + b)),
      if_pos (by omega : F.off e + 1 = b ∨ F.off e = b)]
  · have hne : F.ring.rightNeighbor e ≠ e := rightNeighbor_ne F e
    obtain ⟨g1, _⟩ := kernel_leaders_of_dummy F.hpsi (C e)
      (C (F.ring.rightNeighbor e)) hlead hrf hrd
    have hJd : (ldStep F C e F.target).leader = true := by
      rw [htgt]
      have hs1 : ldStep F C e e =
          (eliminateLeadersNoCollision F.hpsi (C e)
            (C (F.ring.rightNeighbor e))).1 :=
        updatePair_initiator C e (F.ring.rightNeighbor e) _
      rw [hs1, g1]; exact hlead
    have hVd : ldStep F C e F.victim = C F.victim := by
      have : ldStep F C e (F.pos 0) = C (F.pos 0) :=
        ldStep_pos_eq F C e 0 (F.off e + 1) (by omega) (by omega)
          (rightNeighbor_eq F e) (by omega) (by omega)
      exact this
    have hAd : ldStep F C e F.attacker = C F.attacker := by
      have : ldStep F C e (F.pos (a + b)) = C (F.pos (a + b)) :=
        ldStep_pos_eq F C e (a + b) (F.off e + 1) (by omega) (by omega)
          (rightNeighbor_eq F e) (by omega) (by omega)
      exact this
    unfold ldDeleted
    rw [hVd, hJd, hAd, hMid.1, hMid.2.2.1]
    exact (by decide : ¬ ((!(true && true && true)) = true))
  · intro hseal
    obtain ⟨hbull, hsig⟩ := dummy_not_absorbed_base F C e hlead hrf hrd
    rw [hrn] at hbull hsig
    have h1 : atkBullet F (ldStep F C e) 1 ≠ 0 := by
      rw [atkBullet_val F _ 1 (by omega) (by omega), hbull]
      intro hcon
      have hv : (1 : Nat) = 0 := hcon
      omega
    have h2 := hseal.1.bulletClears 1 1 (by omega) (by omega) (by omega)
      (by omega) h1
    rw [atkSig_val F _ 1 (by omega) (by omega), hsig] at h2
    have hv : (1 : Nat) = 0 := h2
    omega

end LDKernelLaws

#print axioms LDKernelLaws.elim_eq
#print axioms LDKernelLaws.fire_fst
#print axioms LDKernelLaws.fire_snd
#print axioms LDKernelLaws.fire_fst_eq_of_not
#print axioms LDKernelLaws.fire_snd_eq_of_not
#print axioms LDKernelLaws.fire_fst_label
#print axioms LDKernelLaws.fire_snd_label
#print axioms LDKernelLaws.fire_snd_leader
#print axioms LDKernelLaws.move_eq_of_responder_zero
#print axioms LDKernelLaws.move_eq_of_leader_not_kill
#print axioms LDKernelLaws.move_kill
#print axioms LDKernelLaws.move_transport
#print axioms LDKernelLaws.move_destroy
#print axioms LDKernelLaws.move_fst_label
#print axioms LDKernelLaws.move_snd_label
#print axioms LDKernelLaws.signal_fst
#print axioms LDKernelLaws.signal_snd_eq_of_closed
#print axioms LDKernelLaws.signal_snd_of_live
#print axioms LDKernelLaws.signal_snd_frame
#print axioms LDKernelLaws.fin2_cases
#print axioms LDKernelLaws.signal_snd_signal_of_quiet
#print axioms LDKernelLaws.signal_snd_signal_one
#print axioms LDKernelLaws.kernel_fst_label
#print axioms LDKernelLaws.kernel_snd_label
#print axioms LDKernelLaws.ldStep_label
#print axioms LDKernelLaws.labelAligned_ldStep
#print axioms LDKernelLaws.aligned_edge
#print axioms LDKernelLaws.aligned_edge_of_noFreeBarrier
#print axioms LDKernelLaws.sameObs_of_eq
#print axioms LDKernelLaws.tgtBullet_obs
#print axioms LDKernelLaws.tgtSig_obs
#print axioms LDKernelLaws.atkBullet_obs
#print axioms LDKernelLaws.atkSig_obs
#print axioms LDKernelLaws.sealed_of_block_obs
#print axioms LDKernelLaws.sectorSealed_move
#print axioms LDKernelLaws.sectorSealed_signal
#print axioms LDKernelLaws.sectorSealed_fire_move
#print axioms LDKernelLaws.block_two_le
#print axioms LDKernelLaws.rightNeighbor_ne
#print axioms LDKernelLaws.move_transport_fst
#print axioms LDKernelLaws.move_transport_snd
#print axioms LDKernelLaws.ldStep_transport
#print axioms LDKernelLaws.off_of_atkInterior
#print axioms LDKernelLaws.atkInterior_of_aligned
#print axioms LDKernelLaws.fire_fst_leader
#print axioms LDKernelLaws.fire_fst_signal_of_follower
#print axioms LDKernelLaws.ldStep_no_move
#print axioms LDKernelLaws.kernel_fire_move
#print axioms LDKernelLaws.ldStep_fire_move
#print axioms LDKernelLaws.dummy_not_absorbed_base
#print axioms LDKernelLaws.kernel_leaders_of_dummy
#print axioms LDKernelLaws.tgtInterior_false
#print axioms LDKernelLaws.middle_false
