import Leader.L3.Native

namespace L3

set_option autoImplicit false

/-!
The first theorem uses the stronger fact that overwriting ANY site by
the L3 born record (true,0,true,false) preserves P. Its key is a
counterclockwise first-leader scan. This birth differs from the older
PPL pre-E born4 (true,2,true,false), whose proof is not reused here.

The latter half uses the exact native-owner chain in
Protocol.transition / Base.baseStep: E on OLD native fields,
FIRE on OLD requests/grants and post-E native fields, then the
optional complete born record. Other owners frame the four fields.
-/

/-- The scan used by PPL.dLLBy, with an arbitrary starting offset. -/
private def leftLeaderScan {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n)
    (fuel start : Nat) : Option Nat :=
  PPL.scanDistance (fun j => PPL.shiftLeft ring v j)
    (fun i => (N i).l) fuel start

/--
A sufficient, local first-leader safety scan.
When no leader was seen after n inspected positions, the base case
requires ALL n signals zero; this is the leaderless clause of
purification.tex:80-81. A first leader must be shielded and each
inspected signal (including its own and the bullet host's) must be 0.
-/
private def safeLeftScan {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) : Nat → Nat → Prop
  | 0, _ => ∀ k : Fin n, (N k).sg = false
  | fuel + 1, start =>
      (N (PPL.shiftLeft ring v start)).sg = false ∧
        if (N (PPL.shiftLeft ring v start)).l then
          (N (PPL.shiftLeft ring v start)).sh = true
        else safeLeftScan ring N v fuel (start + 1)

private theorem scan_some_ge {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) :
    ∀ fuel start d,
      leftLeaderScan ring N v fuel start = some d →
      start ≤ d := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h
      simp [leftLeaderScan, PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d h
      by_cases hl : (N (PPL.shiftLeft ring v start)).l = true
      · have hs : some start = some d := by
          simpa [leftLeaderScan, PPL.scanDistance, hl] using h
        have heq : start = d := Option.some.inj hs
        omega
      · have ht : leftLeaderScan ring N v fuel (start + 1) =
            some d := by
          simpa [leftLeaderScan, PPL.scanDistance, hl] using h
        have hs := ih (start + 1) d ht
        omega

private theorem safeScan_of_none {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) :
    ∀ fuel start,
      leftLeaderScan ring N v fuel start = none →
      (∀ k : Fin n, (N k).sg = false) →
      safeLeftScan ring N v fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start _ hs
      exact hs
  | succ fuel ih =>
      intro start hscan hs
      cases hl : (N (PPL.shiftLeft ring v start)).l with
      | true =>
          simp [leftLeaderScan, PPL.scanDistance, hl] at hscan
      | false =>
          have ht : leftLeaderScan ring N v fuel (start + 1) =
              none := by
            simpa [leftLeaderScan, PPL.scanDistance, hl] using hscan
          change (N (PPL.shiftLeft ring v start)).sg = false ∧
            (if (N (PPL.shiftLeft ring v start)).l then
              (N (PPL.shiftLeft ring v start)).sh = true
             else safeLeftScan ring N v fuel (start + 1))
          refine ⟨hs _, ?_⟩
          simpa [hl] using ih (start + 1) ht hs

private theorem safeScan_of_some {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) :
    ∀ fuel start d,
      leftLeaderScan ring N v fuel start = some d →
      (N (PPL.shiftLeft ring v d)).sh = true →
      (∀ j : Nat, start ≤ j → j ≤ d →
        (N (PPL.shiftLeft ring v j)).sg = false) →
      safeLeftScan ring N v fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h _ _
      simp [leftLeaderScan, PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d hscan hsh hsig
      by_cases hl : (N (PPL.shiftLeft ring v start)).l = true
      · have hs : some start = some d := by
          simpa [leftLeaderScan, PPL.scanDistance, hl] using hscan
        have hd : start = d := Option.some.inj hs
        subst d
        change (N (PPL.shiftLeft ring v start)).sg = false ∧
          (if (N (PPL.shiftLeft ring v start)).l then
             (N (PPL.shiftLeft ring v start)).sh = true
           else safeLeftScan ring N v fuel (start + 1))
        refine ⟨hsig start (Nat.le_refl _) (Nat.le_refl _), ?_⟩
        simpa [hl] using hsh
      · have ht : leftLeaderScan ring N v fuel (start + 1) =
            some d := by
          simpa [leftLeaderScan, PPL.scanDistance, hl] using hscan
        have hd : start + 1 ≤ d :=
          scan_some_ge ring N v fuel (start + 1) d ht
        change (N (PPL.shiftLeft ring v start)).sg = false ∧
          (if (N (PPL.shiftLeft ring v start)).l then
             (N (PPL.shiftLeft ring v start)).sh = true
           else safeLeftScan ring N v fuel (start + 1))
        refine ⟨hsig start (Nat.le_refl _) (by omega), ?_⟩
        simpa [hl] using
          ih (start + 1) d ht hsh
            (fun j hj hle => hsig j (by omega) hle)

private theorem safeScan_none {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) :
    ∀ fuel start,
      leftLeaderScan ring N v fuel start = none →
      safeLeftScan ring N v fuel start →
      ∀ k : Fin n, (N k).sg = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start _ h
      exact h
  | succ fuel ih =>
      intro start hscan hsafe
      cases hl : (N (PPL.shiftLeft ring v start)).l with
      | true =>
          simp [leftLeaderScan, PPL.scanDistance, hl] at hscan
      | false =>
          have ht : leftLeaderScan ring N v fuel (start + 1) =
              none := by
            simpa [leftLeaderScan, PPL.scanDistance, hl] using hscan
          have htail : safeLeftScan ring N v fuel (start + 1) := by
            have hh := hsafe.2
            simpa [safeLeftScan, hl] using hh
          exact ih (start + 1) ht htail

private theorem safeScan_some {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (v : Fin n) :
    ∀ fuel start d,
      leftLeaderScan ring N v fuel start = some d →
      safeLeftScan ring N v fuel start →
      (N (PPL.shiftLeft ring v d)).sh = true ∧
      ∀ j : Nat, start ≤ j → j ≤ d →
        (N (PPL.shiftLeft ring v j)).sg = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start d h _
      simp [leftLeaderScan, PPL.scanDistance] at h
  | succ fuel ih =>
      intro start d hscan hsafe
      have hhead : (N (PPL.shiftLeft ring v start)).sg =
          false := hsafe.1
      by_cases hl : (N (PPL.shiftLeft ring v start)).l = true
      · have hs : some start = some d := by
          simpa [leftLeaderScan, PPL.scanDistance, hl] using hscan
        have hd : start = d := Option.some.inj hs
        subst d
        constructor
        · simpa [safeLeftScan, hl] using hsafe.2
        · intro j hj hle
          have hj' : j = start := by omega
          simpa [hj'] using hhead
      · have ht : leftLeaderScan ring N v fuel (start + 1) =
            some d := by
          simpa [leftLeaderScan, PPL.scanDistance, hl] using hscan
        have hd : start + 1 ≤ d :=
          scan_some_ge ring N v fuel (start + 1) d ht
        have htail : safeLeftScan ring N v fuel (start + 1) := by
          simpa [safeLeftScan, hl] using hsafe.2
        obtain ⟨hsh, hsig⟩ := ih (start + 1) d ht htail
        constructor
        · exact hsh
        · intro j hj hle
          by_cases hj0 : j = start
          · simpa [hj0] using hhead
          · exact hsig j (by omega) hle

/-- PPL.PeacefulCore equals the safe first-leader scan, including
    the rootless global-zero terminal condition. -/
private theorem peacefulCore_iff_safeScan {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (v : Fin n) :
    PPL.PeacefulCore ring
      (fun i => (N i).l) (fun i => (N i).sh)
      (fun i => (N i).sg) v ↔
      safeLeftScan ring N v n 0 := by
  constructor
  · intro hcore
    unfold PPL.PeacefulCore at hcore
    change (match leftLeaderScan ring N v n 0 with
      | none => ∀ j : Fin n, (N j).sg = false
      | some d =>
          (N (PPL.shiftLeft ring v d)).sh = true ∧
          ∀ j : Fin (d + 1),
            (N (PPL.shiftLeft ring v j.val)).sg = false) at hcore
    cases hs : leftLeaderScan ring N v n 0 with
    | none =>
        rw [hs] at hcore
        exact safeScan_of_none ring N v n 0 hs hcore
    | some d =>
        rw [hs] at hcore
        exact safeScan_of_some ring N v n 0 d hs hcore.1
          (fun j _ hle => hcore.2 ⟨j, by omega⟩)
  · intro hsafe
    unfold PPL.PeacefulCore
    change (match leftLeaderScan ring N v n 0 with
      | none => ∀ j : Fin n, (N j).sg = false
      | some d =>
          (N (PPL.shiftLeft ring v d)).sh = true ∧
          ∀ j : Fin (d + 1),
            (N (PPL.shiftLeft ring v j.val)).sg = false)
    cases hs : leftLeaderScan ring N v n 0 with
    | none =>
        exact safeScan_none ring N v n 0 hs hsafe
    | some d =>
        obtain ⟨hsh, hsig⟩ :=
          safeScan_some ring N v n 0 d hs hsafe
        exact ⟨hsh, fun j =>
          hsig j.val (Nat.zero_le _) (by omega)⟩

/--
Inserting a new shielded zero-signal leader cannot spoil a
first-leader scan: before z the scan is unchanged; at z it
terminates successfully. In the no-leader case its base
condition is still valid since the birth cannot add a signal.
-/
private theorem safeScan_birth {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (z v : Fin n) :
    ∀ fuel start,
      safeLeftScan ring N v fuel start →
      safeLeftScan ring (canonicalBirth N z) v fuel start := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hsafe
      change ∀ k : Fin n, (canonicalBirth N z k).sg = false
      intro k
      by_cases hk : k = z
      · subst k
        simp [canonicalBirth, firedNative]
      · simpa [canonicalBirth, hk] using hsafe k
  | succ fuel ih =>
      intro start hsafe
      by_cases hz : PPL.shiftLeft ring v start = z
      · change
          (canonicalBirth N z (PPL.shiftLeft ring v start)).sg = false ∧
          (if (canonicalBirth N z (PPL.shiftLeft ring v start)).l then
             (canonicalBirth N z (PPL.shiftLeft ring v start)).sh = true
           else safeLeftScan ring (canonicalBirth N z) v fuel (start + 1))
        simp [canonicalBirth, hz, firedNative]
      · have hframe :
            canonicalBirth N z (PPL.shiftLeft ring v start) =
              N (PPL.shiftLeft ring v start) := by
          simp [canonicalBirth, hz]
        change
          (N (PPL.shiftLeft ring v start)).sg = false ∧
          (if (N (PPL.shiftLeft ring v start)).l then
             (N (PPL.shiftLeft ring v start)).sh = true
           else safeLeftScan ring N v fuel (start + 1)) at hsafe
        change
          (canonicalBirth N z (PPL.shiftLeft ring v start)).sg = false ∧
          (if (canonicalBirth N z (PPL.shiftLeft ring v start)).l then
             (canonicalBirth N z (PPL.shiftLeft ring v start)).sh = true
           else safeLeftScan ring (canonicalBirth N z) v fuel (start + 1))
        rw [hframe]
        refine ⟨hsafe.1, ?_⟩
        by_cases hl : (N (PPL.shiftLeft ring v start)).l = true
        · simpa [hl] using hsafe.2
        · have ht : safeLeftScan ring N v fuel (start + 1) := by
            simpa [hl] using hsafe.2
          simpa [hl] using ih (start + 1) ht

/-- Stronger than the required protected-birth lemma:
    any complete L3 canonical overwrite preserves P; no
    eligibility, selected-edge, or reachability condition.
    purification.tex:155-167,186-212. -/
theorem canonicalBirth_preserves_P {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (z : Fin n) (hP : P ring N) :
    P ring (canonicalBirth N z) := by
  intro v
  change LiveBullet (canonicalBirth N z) v →
    PPL.PeacefulCore ring
      (fun i => (canonicalBirth N z i).l)
      (fun i => (canonicalBirth N z i).sh)
      (fun i => (canonicalBirth N z i).sg) v
  intro hlive
  have hvz : v ≠ z := by
    intro hv
    subst v
    simp [LiveBullet, canonicalBirth, firedNative] at hlive
  have hold : LiveBullet N v := by
    simpa [LiveBullet, canonicalBirth, hvz] using hlive
  have hcore : PPL.PeacefulCore ring
      (fun i => (N i).l)
      (fun i => (N i).sh)
      (fun i => (N i).sg) v := hP v hold
  apply (peacefulCore_iff_safeScan ring (canonicalBirth N z) v).2
  exact safeScan_birth ring N z v n 0
    ((peacefulCore_iff_safeScan ring N v).1 hcore)

/-- The paper's post-E birth statement with the literal FIRE guards.
    Its endpoint/eligible premises link the stronger overwrite
    lemma to Base.fireSelect. purification.tex:186-212. -/
theorem birth_preserves_P {n : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (N : Fin n → CertNative) (e z : Fin n)
    (hP : P ring N)
    (_hz : z = e ∨ z = ring.rightNeighbor e)
    (_helig : BirthEligible (nativeE ring N e) z) :
    P ring (canonicalBirth (nativeE ring N e) z) := by
  exact canonicalBirth_preserves_P ring (nativeE ring N e) z
    (nativeE_preserves_P hn ring N e hP)

/-! ## Native projection of the *real* selected pair. -/

/-- The post-FIRE native row of the initiator site, as computed by
    `baseStep`: E on the OLD native fields, then the born record if
    FIRE selects site x. -/
private def nativeOutX {c : Compiled} (x y : Agent c) : CertNative :=
  if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true then firedNative
  else (certLiteralEPair x.certNative y.certNative).1

/-- The same for the responder site. -/
private def nativeOutY {c : Compiled} (x y : Agent c) : CertNative :=
  if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true then firedNative
  else (certLiteralEPair x.certNative y.certNative).2

private theorem agent_l_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).l = if p then a.l else b.l := by
  split <;> rfl

private theorem agent_b_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).b = if p then a.b else b.b := by
  split <;> rfl

private theorem agent_sh_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).sh = if p then a.sh else b.sh := by
  split <;> rfl

private theorem agent_sg_ite {c : Compiled} (p : Prop) [Decidable p]
    (a b : Agent c) :
    (if p then a else b).sg = if p then a.sg else b.sg := by
  split <;> rfl

private theorem baseStep_fst_l (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.l = (nativeOutX x y).l := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_l_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_l_ite]

private theorem baseStep_fst_b (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.b = (nativeOutX x y).b := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_b_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_b_ite]

private theorem baseStep_fst_sh (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.sh = (nativeOutX x y).sh := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]

private theorem baseStep_fst_sg (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.sg = (nativeOutX x y).sg := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteX
      = true
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]
  · simp [hF, nativeOutX, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]

private theorem baseStep_snd_l (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.l = (nativeOutY x y).l := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_l_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_l_ite]

private theorem baseStep_snd_b (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.b = (nativeOutY x y).b := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_b_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_b_ite]

private theorem baseStep_snd_sh (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.sh = (nativeOutY x y).sh := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sh_ite]

private theorem baseStep_snd_sg (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.sg = (nativeOutY x y).sg := by
  unfold baseStep
  by_cases hF : fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2) FireSite.siteY
      = true
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]
  · simp [hF, nativeOutY, Agent.setNative, Agent.setCPriv,
      agent_sg_ite]

/-- Structural native independence of certificate, PACK, BANK/SMALL,
    DCC, candidate, and token updates in baseStep. -/
private theorem baseStep_fst_native (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).1.certNative = nativeOutX x y := by
  have hl := baseStep_fst_l c ev x y
  have hb := baseStep_fst_b c ev x y
  have hsh := baseStep_fst_sh c ev x y
  have hsg := baseStep_fst_sg c ev x y
  show CertNative.mk (baseStep c ev x y).1.l (baseStep c ev x y).1.b
      (baseStep c ev x y).1.sh (baseStep c ev x y).1.sg = _
  rw [hl, hb, hsh, hsg]

private theorem baseStep_snd_native (c : Compiled) (ev : CertEvent)
    (x y : Agent c) :
    (baseStep c ev x y).2.certNative = nativeOutY x y := by
  have hl := baseStep_snd_l c ev x y
  have hb := baseStep_snd_b c ev x y
  have hsh := baseStep_snd_sh c ev x y
  have hsg := baseStep_snd_sg c ev x y
  show CertNative.mk (baseStep c ev x y).2.l (baseStep c ev x y).2.b
      (baseStep c ev x y).2.sh (baseStep c ev x y).2.sg = _
  rw [hl, hb, hsh, hsg]

/-- assemble retains the native fields of baseStep; cert/HK
    owners write disjoint fields (Protocol.lean:25-52). -/
private theorem transition_native_fst (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.certNative = nativeOutX x y := by
  have h : (transition c x y).1.certNative =
      (baseStep c (certificateStep c x y).2.2 x y).1.certNative := by
    first
      | rfl
      | simp [transition, assemble, Agent.certNative]
  rw [h]
  exact baseStep_fst_native c _ x y

private theorem transition_native_snd (c : Compiled)
    (x y : Agent c) :
    (transition c x y).2.certNative = nativeOutY x y := by
  have h : (transition c x y).2.certNative =
      (baseStep c (certificateStep c x y).2.2 x y).2.certNative := by
    first
      | rfl
      | simp [transition, assemble, Agent.certNative]
  rw [h]
  exact baseStep_snd_native c _ x y

/-- The physical two-site native replacement, with source priority.
    Using it avoids claiming two births or modifying nonselected sites. -/
private def updateTwo {n : Nat} (N : Fin n → CertNative)
    (e j : Fin n) (x y : CertNative) : Fin n → CertNative :=
  fun k => if k = e then x else if k = j then y else N k

private theorem updateTwo_birth_source {n : Nat}
    (N : Fin n → CertNative) (e j : Fin n)
    (x y : CertNative) :
    updateTwo N e j firedNative y =
      canonicalBirth (updateTwo N e j x y) e := by
  funext k
  by_cases h : k = e
  · simp [updateTwo, canonicalBirth, h]
  · simp [updateTwo, canonicalBirth, h]

private theorem updateTwo_birth_target {n : Nat}
    (N : Fin n → CertNative) (e j : Fin n)
    (hne : j ≠ e) (x y : CertNative) :
    updateTwo N e j x firedNative =
      canonicalBirth (updateTwo N e j x y) j := by
  funext k
  by_cases hj : k = j
  · subst hj
    simp [updateTwo, canonicalBirth, hne]
  · by_cases hx : k = e
    · subst hx
      simp [updateTwo, canonicalBirth, hj]
    · simp [updateTwo, canonicalBirth, hj, hx]

private theorem updateTwo_source {n : Nat}
    {N : Fin n → CertNative} {e j : Fin n} (x y : CertNative) :
    updateTwo N e j x y e = x := by
  simp [updateTwo]

private theorem updateTwo_target {n : Nat}
    {N : Fin n → CertNative} {e j : Fin n}
    (hne : j ≠ e) (x y : CertNative) :
    updateTwo N e j x y j = y := by
  simp [updateTwo, hne]

private theorem updateTwo_other {n : Nat}
    {N : Fin n → CertNative} {e j k : Fin n}
    (hx : k ≠ e) (hy : k ≠ j) (x y : CertNative) :
    updateTwo N e j x y k = N k := by
  simp [updateTwo, hx, hy]

private theorem rightNeighbor_ne_self_birth {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem step_at_source {P : PopulationProtocol} {n : Nat}
    (ring : DirectedRing n) (C : P.Configuration n) (e : Fin n) :
    PopulationProtocol.step P ring C e e =
      (P.transition (C e) (C (ring.rightNeighbor e))).1 := by
  first
    | exact if_pos rfl
    | simp [PopulationProtocol.step]

private theorem step_at_target {P : PopulationProtocol} {n : Nat}
    (ring : DirectedRing n) (C : P.Configuration n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    PopulationProtocol.step P ring C e (ring.rightNeighbor e) =
      (P.transition (C e) (C (ring.rightNeighbor e))).2 := by
  first
    | exact (if_neg hne).trans (if_pos rfl)
    | simp [PopulationProtocol.step, hne]

private theorem step_other {P : PopulationProtocol} {n : Nat}
    (ring : DirectedRing n) (C : P.Configuration n) (e k : Fin n)
    (hx : k ≠ e) (hy : k ≠ ring.rightNeighbor e) :
    PopulationProtocol.step P ring C e k = C k := by
  first
    | exact (if_neg hx).trans (if_neg hy)
    | simp [PopulationProtocol.step, hx, hy]

/-- The complete protocol step has exactly these four possible
    native fields on its selected pair. -/
private theorem native_step_pair {n q : Nat}
    (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n) :
    let j := ring.rightNeighbor e
    let N := nativeProjection C
    let es := certLiteralEPair (N e) (N j)
    let fire := fireSelect (C e) (C j) es.1 es.2
    nativeProjection
        (PopulationProtocol.step (protocol q) ring C e) =
      updateTwo N e j
        (if fireAtSite fire .siteX then firedNative else es.1)
        (if fireAtSite fire .siteY then firedNative else es.2) := by
  dsimp only
  funext k
  by_cases hx : k = e
  · rw [hx, updateTwo_source]
    exact (congrArg Agent.certNative
      (step_at_source ring C e)).trans
      (transition_native_fst (compileAdvice q) (C e)
        (C (ring.rightNeighbor e)))
  · by_cases hy : k = ring.rightNeighbor e
    · have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact hx (hy.trans h)
      rw [hy, updateTwo_target hne]
      exact (congrArg Agent.certNative
        (step_at_target ring C e hne)).trans
        (transition_native_snd (compileAdvice q) (C e)
          (C (ring.rightNeighbor e)))
    · rw [updateTwo_other hx hy]
      exact congrArg Agent.certNative (step_other ring C e k hx hy)

private theorem finThree_cases_birth (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨
      b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- `fireSelect` depends on its arguments only through the four request
    and grant bits and the `l`/`b` fields of the two post-E rows. -/
private def fireSelectB (rx gx ry gy lX : Bool) (bX : Fin 3)
    (lY : Bool) (bY : Fin 3) : Option FireSel :=
  let eligX := !lX && bX.val == 0
  let eligY := !lY && bY.val == 0
  if rx && gx && eligX then
    some { kind := .F0, site := .siteX, reqX := true, grantX := true }
  else if ry && gy && eligY then
    some { kind := .F1, site := .siteY, reqY := true, grantY := true }
  else if rx && gy && eligX then
    some { kind := .F2, site := .siteX, reqX := true, grantY := true }
  else none

private theorem fireSelect_eq_bool {c : Compiled}
    (x y : Agent c) (eX eY : CertNative) :
    fireSelect x y eX eY =
      fireSelectB x.req x.grant y.req y.grant eX.l eX.b eY.l eY.b := rfl

private theorem fireSelectB_x_eligible :
    ∀ (rx gx ry gy lX : Bool) (bX : Fin 3) (lY : Bool) (bY : Fin 3),
      fireAtSite (fireSelectB rx gx ry gy lX bX lY bY) .siteX = true →
        lX = false ∧ bX = (0 : Fin 3) := by
  intro rx gx ry gy lX bX lY bY
  rcases finThree_cases_birth bX with hb | hb | hb <;>
    rcases finThree_cases_birth bY with hc | hc | hc <;>
    subst hb <;> subst hc <;>
    cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lX <;> cases lY <;> decide

private theorem fireSelectB_y_eligible :
    ∀ (rx gx ry gy lX : Bool) (bX : Fin 3) (lY : Bool) (bY : Fin 3),
      fireAtSite (fireSelectB rx gx ry gy lX bX lY bY) .siteY = true →
        lY = false ∧ bY = (0 : Fin 3) := by
  intro rx gx ry gy lX bX lY bY
  rcases finThree_cases_birth bX with hb | hb | hb <;>
    rcases finThree_cases_birth bY with hc | hc | hc <;>
    subst hb <;> subst hc <;>
    cases rx <;> cases gx <;> cases ry <;> cases gy <;>
    cases lX <;> cases lY <;> decide

/-- The two FIRE eligibility implications are statements about
    literal fireSelect, not assumptions added to the machine. -/
private theorem fireSelect_x_eligible {c : Compiled}
    (x y : Agent c) (eX eY : CertNative)
    (h : fireAtSite (fireSelect x y eX eY) .siteX = true) :
    eX.l = false ∧ eX.b = (0 : Fin 3) := by
  rw [fireSelect_eq_bool] at h
  exact fireSelectB_x_eligible _ _ _ _ _ _ _ _ h

private theorem fireSelect_y_eligible {c : Compiled}
    (x y : Agent c) (eX eY : CertNative)
    (h : fireAtSite (fireSelect x y eX eY) .siteY = true) :
    eY.l = false ∧ eY.b = (0 : Fin 3) := by
  rw [fireSelect_eq_bool] at h
  exact fireSelectB_y_eligible _ _ _ _ _ _ _ _ h

/--
Reusable exact real/native commuting interface:
0 or 1 canonical birth, at one selected post-E eligible site.
No Cartesian scratch assumption is imposed, and the chosen
site depends on OLD request/grant and the POST-E native row.
-/
theorem native_step_eq {n q : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n) :
    ∃ z : Option (Fin n),
      (∀ v : Fin n, z = some v →
        (v = e ∨ v = ring.rightNeighbor e) ∧
          BirthEligible
            (nativeE ring (nativeProjection C) e) v) ∧
      nativeProjection
        (PopulationProtocol.step (protocol q) ring C e) =
        match z with
        | none => nativeE ring (nativeProjection C) e
        | some v => canonicalBirth
            (nativeE ring (nativeProjection C) e) v := by
  let N := nativeProjection C
  let j := ring.rightNeighbor e
  let es := certLiteralEPair (N e) (N j)
  let fire := fireSelect (C e) (C j) es.1 es.2
  have hne : j ≠ e := rightNeighbor_ne_self_birth
    (by omega : 2 ≤ n) ring e
  have hpost :
      nativeE ring N e = updateTwo N e j es.1 es.2 := rfl
  have hstep :
      nativeProjection
          (PopulationProtocol.step (protocol q) ring C e) =
        updateTwo N e j
          (if fireAtSite fire .siteX then firedNative else es.1)
          (if fireAtSite fire .siteY then firedNative else es.2) := by
    simpa [N, j, es, fire] using native_step_pair ring C e
  cases hf : fire with
  | none =>
      refine ⟨none, ?_, ?_⟩
      · intro v hv
        cases hv
      · calc
          nativeProjection
              (PopulationProtocol.step (protocol q) ring C e) =
              updateTwo N e j es.1 es.2 := by
                simpa [hf, fireAtSite] using hstep
          _ = nativeE ring N e := hpost.symm
  | some s =>
      cases hs : s.site with
      | siteX =>
          refine ⟨some e, ?_, ?_⟩
          · intro v hv
            have hev : e = v := Option.some.inj hv
            subst v
            have heX : es.1.l = false ∧
                es.1.b = (0 : Fin 3) :=
              fireSelect_x_eligible (C e) (C j) es.1 es.2
                (by
                  have hfx : fireAtSite fire .siteX = true := by
                    rw [hf]
                    simp [fireAtSite, hs]
                  exact hfx)
            refine ⟨Or.inl rfl, ?_⟩
            have hB : BirthEligible (nativeE ring N e) e := by
              rw [hpost]
              show (updateTwo N e j es.1 es.2 e).l = false ∧
                (updateTwo N e j es.1 es.2 e).b = (0 : Fin 3)
              rw [updateTwo_source]
              exact heX
            exact hB
          · calc
              nativeProjection
                  (PopulationProtocol.step (protocol q) ring C e) =
                  updateTwo N e j firedNative es.2 := by
                    simpa [hf, hs, fireAtSite] using hstep
              _ = canonicalBirth (updateTwo N e j es.1 es.2) e :=
                    updateTwo_birth_source N e j es.1 es.2
              _ = canonicalBirth (nativeE ring N e) e := by
                    rw [hpost]
      | siteY =>
          refine ⟨some j, ?_, ?_⟩
          · intro v hv
            have hjv : j = v := Option.some.inj hv
            subst v
            have heY : es.2.l = false ∧
                es.2.b = (0 : Fin 3) :=
              fireSelect_y_eligible (C e) (C j) es.1 es.2
                (by
                  have hfy : fireAtSite fire .siteY = true := by
                    rw [hf]
                    simp [fireAtSite, hs]
                  exact hfy)
            refine ⟨Or.inr rfl, ?_⟩
            have hB : BirthEligible (nativeE ring N e) j := by
              rw [hpost]
              show (updateTwo N e j es.1 es.2 j).l = false ∧
                (updateTwo N e j es.1 es.2 j).b = (0 : Fin 3)
              rw [updateTwo_target hne]
              exact heY
            exact hB
          · calc
              nativeProjection
                  (PopulationProtocol.step (protocol q) ring C e) =
                  updateTwo N e j es.1 firedNative := by
                    simpa [hf, hs, fireAtSite] using hstep
              _ = canonicalBirth (updateTwo N e j es.1 es.2) j :=
                    updateTwo_birth_target N e j hne es.1 es.2
              _ = canonicalBirth (nativeE ring N e) j := by
                    rw [hpost]

/-- The literal real transition never extinguishes the last
    protected leader. This theorem is for every advice q and
    every Cartesian configuration, not just generated scratch. -/
theorem lastLeader_not_deleted {n q : Nat}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (C : (protocol q).Configuration n) (e : Fin n)
    (hP : PPlus ring (nativeProjection C)) :
    ∃ v : Fin n,
      (nativeProjection
        (PopulationProtocol.step (protocol q) ring C e) v).l =
          true := by
  obtain ⟨z, _hz, hstep⟩ := native_step_eq hn ring C e
  have hE : PPlus ring
      (nativeE ring (nativeProjection C) e) :=
    nativeE_preserves_PPlus hn ring (nativeProjection C) e hP
  cases z with
  | none =>
      obtain ⟨v, hv⟩ := hE.1
      refine ⟨v, ?_⟩
      rw [hstep]
      exact hv
  | some z =>
      obtain ⟨v, hv⟩ :=
        canonicalBirth_has_leader
          (nativeE ring (nativeProjection C) e) z
      refine ⟨v, ?_⟩
      rw [hstep]
      exact hv

end L3
