import Leader.Wu.Splice.HostTable

set_option autoImplicit false
set_option Elab.async false

namespace B9SpliceHostQuiescence

open PPLL PPLLDomain PPLLResearchFormulation
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10hControllerRowsSafe
open B9Host (HostRow Phys PhysConfig hostStep r1Host)
open PopulationProtocol BirthCheckPermitRepairLeaf
open B9SpliceTableHost

variable {n psi kappa tau : Nat}

-- Open table layers only at their explicit proof steps.
attribute [local irreducible]
  row7H row8H row9H row10bH row10cH row10dgH row10gH rowB9 stepB9

def Neutral (u : Cell psi kappa tau) : Prop :=
  role u.carrier = .none ∧
  u.carrier.repairPending = false ∧ u.acquireTicket = false

def liftCell (u : Phys psi kappa tau) : Cell psi kappa tau :=
  ⟨⟨⟨u, .none⟩, false⟩, false⟩

def lift (B : PhysConfig n psi kappa tau) : Config n psi kappa tau :=
  fun i => liftCell (B i)

theorem erase_lift (B : PhysConfig n psi kappa tau) :
    erase (lift B) = B := rfl

theorem lift_neutral (B : PhysConfig n psi kappa tau) (i : Fin n) :
    Neutral (lift B i) := ⟨rfl, rfl, rfl⟩

theorem eq_lift_cell (u : Cell psi kappa tau) (h : Neutral u) :
    u = liftCell (base u) := by
  obtain ⟨⟨⟨b, ro⟩, p⟩, t⟩ := u
  obtain ⟨h1, h2, h3⟩ := h
  change ro = .none at h1
  change p = false at h2
  change t = false at h3
  subst h1; subst h2; subst h3
  rfl

theorem lift_erase_of_neutral (C : Config n psi kappa tau)
    (hN : ∀ i, Neutral (C i)) : lift (erase C) = C := by
  funext i
  exact (eq_lift_cell (C i) (hN i)).symm

/-- Clear tickets; inherit the input roles and pending bits. -/
def quietWrite (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) : Cell psi kappa tau × Cell psi kappa tau :=
  (⟨(ordinaryRowH host l.carrier r.carrier).1, false⟩,
    ⟨(ordinaryRowH host l.carrier r.carrier).2, false⟩)

theorem notRF_of_neutral (u : Cell psi kappa tau) (h : Neutral u) :
    ¬ ReservedFrontHoldGuard u.carrier := by
  intro hc
  have ht := hc.1
  rw [h.1] at ht
  cases ht

theorem physicalHold_quiet (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau) (hl : Neutral l) (hr : Neutral r)
    (hrel : rightFollowerRelabelledV7 r.carrier
      (ordinaryRowH host l.carrier r.carrier).2 = false) :
    physicalHoldH host l r = quietWrite host l r := by
  unfold physicalHoldH quietWrite
  dsimp only
  simp only [hrel, Bool.false_eq_true, if_false, hl.2.2, hr.2.2]

theorem ordinaryHost_quiet (host : HostRow (Phys psi kappa tau))
    (l r : Cell psi kappa tau)
    (hrel : rightFollowerRelabelledV7 r.carrier
      (ordinaryRowH host l.carrier r.carrier).2 = false) :
    ordinaryHostWriteH host l r = quietWrite host l r := by
  unfold ordinaryHostWriteH quietWrite
  dsimp only
  simp only [hrel, Bool.false_eq_true, if_false] <;> rfl

/-- Only controller fields and the selected-host deletion test are used. -/
theorem row7H_quiet (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (hl : Neutral l) (hr : Neutral r)
    (hdel : ¬ ldc host l.carrier r.carrier)
    (hrel : rightFollowerRelabelledV7 r.carrier
      (ordinaryRowH host l.carrier r.carrier).2 = false) :
    row7H host hpsi l r = quietWrite host l r := by
  classical
  have hlr := hl.1
  have hrr := hr.1
  have hfL : ¬ HostFenceShapeV7 l := fun h => by
    have ht := h.2.2; rw [hl.2.2] at ht; cases ht
  have hfR : ¬ HostFenceShapeV7 r := fun h => by
    have ht := h.2.2; rw [hr.2.2] at ht; cases ht
  have hRF := notRF_of_neutral r hr
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi l r :=
    fun h => hRF h.2.2.2.1
  have hA : ¬ ArmAGuardH host l.carrier r.carrier :=
    fun h => hdel h.2.2.2.2
  have hB : ¬ ArmBGuard l.carrier r.carrier := fun h => by
    have ht := h.2.2.1; rw [hrr] at ht; cases ht
  have hDel : ¬ DeleteGuardH host l.carrier r.carrier :=
    fun h => hdel h.2.2.2.2
  have hPH : ¬ PendingHoldGuardH host l.carrier r.carrier :=
    fun h => hdel h.2.2.2.2
  have hPA : ¬ PendingAbortGuardH host l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hMC : ¬ MoveCommitGuard l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hMS : ¬ MoveStopGuardV3 hpsi l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hSK : ¬ MoveSeekGuardV3 hpsi l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hSKH : ¬ MoveSeekHoldGuardV3 l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hPOA : ¬ PendingOwnerAbortGuardV3 l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hrr] at ht; cases ht
  have hPP : ¬ (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = true) := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hMAL : ¬ MoveAcquireLegacyGuardV6 l r := fun h => hRF h.1.2.2.2
  have hMAA : ¬ MoveAcquireAbortGuardV3 l.carrier r.carrier := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hORF : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier :=
    fun h => hRF h.1
  have hRFH : ¬ ReservedFrontHoldGuard l.carrier := notRF_of_neutral l hl
  have hVR : ¬ VictimRightScrubGuardV6 r := fun h => by
    have ht := h.1; rw [hrr] at ht; cases ht
  have hVL : ¬ VictimLeftScrubGuardV6 l := fun h => by
    have ht := h.1; rw [hlr] at ht; cases ht
  have hFR : ¬ FrontRightScrubGuardV6 r := fun h => by
    have ht := h.1; rw [hrr] at ht; cases ht
  have hML : ¬ MalformedLeftPendingGuardV6 l := fun h => by
    have ht := h.1; rw [hl.2.1] at ht; cases ht
  have hMR : ¬ MalformedRightPendingGuardV6 r := fun h => by
    have ht := h.1; rw [hr.2.1] at ht; cases ht
  have hpl : ¬ role l.carrier = .predecessorArmed := by rw [hlr]; decide
  have hlf : ¬ role l.carrier = .front := by rw [hlr]; decide
  have hmk : ¬ MarkedHoldGuardV6 l r := by
    rintro (h | ⟨h, _⟩)
    · exact h hlr
    · exact h hrr
  unfold row7H
  rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg hA, if_neg hB,
    if_neg hDel, if_neg hPH, if_neg hPA, if_neg hMC, if_neg hMS,
    if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL,
    if_neg hMAA, if_neg hORF, if_neg hRFH, if_neg hVR, if_neg hVL,
    if_neg hFR, if_neg hML, if_neg hMR, if_neg hpl, if_neg hlf, if_neg hmk]
  exact ordinaryHost_quiet host l r hrel

/-- No geometric law or birth-free hypothesis is needed. -/
theorem neutral_row (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) (hl : Neutral l) (hr : Neutral r)
    (hlead : l.carrier.splice.base.core.core.leader = false)
    (hrel : rightFollowerRelabelledV7 r.carrier
      (ordinaryRowH host l.carrier r.carrier).2 = false) :
    rowB9 host hpsi l r = quietWrite host l r := by
  classical
  have hdel : ¬ ldc host l.carrier r.carrier := by
    intro h
    have ht : l.carrier.splice.base.core.core.leader = true := h.1
    rw [hlead] at ht
    cases ht
  have hRF := notRF_of_neutral r hr
  have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier :=
    fun h => hRF h.1
  have hD2 : ¬ OrphanVictimGuard l r := fun h => by
    have ht := h.1; rw [hr.1] at ht; cases ht
  have hD3 : ¬ OwnedPendingVictimGuard l r := fun h => by
    have ht := h.1; rw [hl.1] at ht; cases ht
  have hD4 : ¬ OwnerlessPendingPredGuard l r := fun h => by
    have ht := h.2.1; rw [hr.1] at ht; cases ht
  have hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r := fun h => by
    have ht := h.1.2.2; rw [hl.2.2] at ht; cases ht
  have hBF : ¬ HostFenceBusyFrontGuardV9 hpsi l r := fun h => by
    have ht := h.1.2.2; rw [hl.2.2] at ht; cases ht
  have hSP8 : ¬ RightStalePredecessorHoldGuardV8 l r := fun h => by
    have ht := h.2.2.2.1; rw [hr.1] at ht; cases ht
  have hb : row10bH host hpsi l r = quietWrite host l r := by
    unfold row10bH
    rw [if_neg hHO]
    unfold row9H
    rw [if_neg hBF]
    unfold row8H
    rw [if_neg hSP8]
    exact row7H_quiet host hpsi l r hl hr hdel hrel
  have hc : row10cH host hpsi l r = (l, r) ∨
      row10cH host hpsi l r = quietWrite host l r := by
    unfold row10cH
    by_cases hz : ZeroRefreshOnlyGuardH host hpsi l r
    · rw [if_pos hz]; exact Or.inl rfl
    · rw [if_neg hz]; exact Or.inr hb
  have hdg : row10dgH host hpsi l r = row10cH host hpsi l r := by
    unfold row10dgH
    rw [if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4]
  unfold rowB9
  rw [if_neg hdel]
  unfold row10gH
  dsimp only
  by_cases hq : row10dgH host hpsi l r = (l, r)
  · rw [if_pos hq]
    have h0 : ¬ (role l.carrier = .predecessorArmed ∧
        l.carrier.repairPending = true) := fun h => by
      have ht := h.1; rw [hl.1] at ht; cases ht
    have h1 : ¬ VictimRightScrubGuardV6 r := fun h => by
      have ht := h.1; rw [hr.1] at ht; cases ht
    have h2 : ¬ FrontRightScrubGuardV6 r := fun h => by
      have ht := h.1; rw [hr.1] at ht; cases ht
    have h3 : ¬ MalformedRightPendingGuardV6 r := fun h => by
      have ht := h.1; rw [hr.2.1] at ht; cases ht
    have h4 : ¬ role r.carrier = .predecessorArmed := by rw [hr.1]; decide
    rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    exact physicalHold_quiet host l r hl hr hrel
  · rw [if_neg hq]
    rcases hc with hc0 | hc1
    · exact False.elim (hq (hdg.trans hc0))
    · exact hdg.trans hc1

private theorem rightNeighbor_ne (ring : DirectedRing n) (hn : 2 ≤ n)
    (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- Exactly the two served-pair premises of neutral_row on a neutral lift. -/
def QuietAt (host : HostRow (Phys psi kappa tau)) (ring : DirectedRing n)
    (B : PhysConfig n psi kappa tau) (e : Fin n) : Prop :=
  (B e).core.core.leader = false ∧
  rightFollowerRelabelledV7 (lift B (ring.rightNeighbor e)).carrier
    (ordinaryRowH host (lift B e).carrier
      (lift B (ring.rightNeighbor e)).carrier).2 = false

/-- This proof only evaluates the chosen output endpoint or an untouched cell. -/
theorem step_lift (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (B : PhysConfig n psi kappa tau) (e : Fin n)
    (hq : QuietAt host ring B e) :
    stepB9 host hpsi ring (lift B) e = lift (hostStep host ring B e) := by
  classical
  have hs := rightNeighbor_ne ring hn e
  have hrow := neutral_row host hpsi (lift B e) (lift B (ring.rightNeighbor e))
    (lift_neutral B e) (lift_neutral B _) hq.1 hq.2
  unfold stepB9
  rw [if_neg hs, hrow]
  funext i
  change writeAt ring (lift B) e
      (quietWrite host (lift B e) (lift B (ring.rightNeighbor e))) i =
    liftCell (hostStep host ring B e i)
  by_cases hi : i = e
  · subst i
    rw [writeAt_e, B9Host.hostStep_left] <;> rfl
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [writeAt_j ring (lift B) e _ hs,
        B9Host.hostStep_right host ring B e hs] <;> rfl
    · rw [writeAt_other ring (lift B) e _ i hi hj,
        B9Host.hostStep_other host ring B e i hi hj] <;> rfl

/-- The next premise is checked on the actual selected-host successor. -/
def QuietAlong (host : HostRow (Phys psi kappa tau)) (ring : DirectedRing n) :
    PhysConfig n psi kappa tau → List (Fin n) → Prop
  | _, [] => True
  | B, e :: es => QuietAt host ring B e ∧
      QuietAlong host ring (hostStep host ring B e) es

theorem quietAlong_cons (host : HostRow (Phys psi kappa tau))
    (ring : DirectedRing n) (B : PhysConfig n psi kappa tau)
    (e : Fin n) (es : List (Fin n)) :
    QuietAlong host ring B (e :: es) ↔
      QuietAt host ring B e ∧ QuietAlong host ring (hostStep host ring B e) es :=
  Iff.rfl

/-- Same original word, with no filtered subword or dropped letters. -/
theorem run_lift (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) :
    ∀ (w : List (Fin n)) (B : PhysConfig n psi kappa tau),
      QuietAlong host ring B w →
      w.foldl (stepB9 host hpsi ring) (lift B) =
        lift (w.foldl (hostStep host ring) B)
  | [], _, _ => rfl
  | e :: es, B, h => by
      change es.foldl (stepB9 host hpsi ring)
          (stepB9 host hpsi ring (lift B) e) =
        lift (es.foldl (hostStep host ring) (hostStep host ring B e))
      rw [step_lift host hpsi ring hn B e h.1]
      exact run_lift host hpsi ring hn es _ h.2

theorem quietAlong_take (host : HostRow (Phys psi kappa tau))
    (ring : DirectedRing n) :
    ∀ (t : Nat) (w : List (Fin n)) (B : PhysConfig n psi kappa tau),
      QuietAlong host ring B w → QuietAlong host ring B (w.take t)
  | 0, _, _, _ => True.intro
  | _ + 1, [], _, _ => True.intro
  | t + 1, e :: es, B, h =>
      ⟨h.1, quietAlong_take host ring t es (hostStep host ring B e) h.2⟩

theorem run_lift_prefix (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlong host ring B w) (t : Nat) :
    (w.take t).foldl (stepB9 host hpsi ring) (lift B) =
      lift ((w.take t).foldl (hostStep host ring) B) :=
  run_lift host hpsi ring hn (w.take t) B (quietAlong_take host ring t w B hq)

theorem run_erase (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlong host ring B w) :
    erase (w.foldl (stepB9 host hpsi ring) (lift B)) =
      w.foldl (hostStep host ring) B :=
  (congrArg (fun C : Config n psi kappa tau => erase C)
    (run_lift host hpsi ring hn w B hq)).trans (erase_lift _)

theorem run_erase_prefix (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlong host ring B w) (t : Nat) :
    erase ((w.take t).foldl (stepB9 host hpsi ring) (lift B)) =
      (w.take t).foldl (hostStep host ring) B :=
  (congrArg (fun C : Config n psi kappa tau => erase C)
    (run_lift_prefix host hpsi ring hn w B hq t)).trans (erase_lift _)

/-- An arbitrary initially neutral configuration, not just lift syntax. -/
theorem run_erase_of_neutral (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (C : Config n psi kappa tau) (hN : ∀ i, Neutral (C i))
    (hq : QuietAlong host ring (erase C) w) :
    erase (w.foldl (stepB9 host hpsi ring) C) =
      w.foldl (hostStep host ring) (erase C) := by
  have hC := lift_erase_of_neutral C hN
  calc
    erase (w.foldl (stepB9 host hpsi ring) C) =
        erase (w.foldl (stepB9 host hpsi ring) (lift (erase C))) :=
      congrArg (fun D : Config n psi kappa tau =>
        erase (w.foldl (stepB9 host hpsi ring) D)) hC.symm
    _ = _ := run_erase host hpsi ring hn w (erase C) hq

def QuietAtR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (B : PhysConfig n psi kappa tau) (e : Fin n) : Prop :=
  QuietAt (r1Host hpsi h2) ring B e

def QuietAlongR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (B : PhysConfig n psi kappa tau) (w : List (Fin n)) : Prop :=
  QuietAlong (r1Host hpsi h2) ring B w

/-- The recursive R1 premise really uses step1, including on class E. -/
theorem quietAlongR1_cons (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (B : PhysConfig n psi kappa tau)
    (e : Fin n) (es : List (Fin n)) :
    QuietAlongR1 hpsi h2 ring B (e :: es) ↔
      QuietAtR1 hpsi h2 ring B e ∧
      QuietAlongR1 hpsi h2 ring
        (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring B e) es := Iff.rfl

/-- Use function equality explicitly under foldl. -/
theorem hostStep_r1_fun_eq (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    hostStep (r1Host (kappa := kappa) (tau := tau) hpsi h2) ring =
      BirthCheckPermitRepairLeaf.step1 hpsi h2 ring := by
  funext B e
  exact B9Host.hostStep_r1_eq_step1 hpsi h2 ring B e

theorem step_lift_step1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (B : PhysConfig n psi kappa tau) (e : Fin n)
    (hq : QuietAtR1 hpsi h2 ring B e) :
    stepV10kR1 hpsi h2 ring (lift B) e =
      lift (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring B e) :=
  (step_lift (r1Host hpsi h2) hpsi ring hn B e hq).trans
    (congrArg (fun D : PhysConfig n psi kappa tau => lift D)
      (B9Host.hostStep_r1_eq_step1 hpsi h2 ring B e))

/-- Precisely the physical equality in stepV10kR1_project_trichotomy.
The identity/relabel alternatives need not be false: the disjunction overlaps. -/
theorem step_erase_step1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (B : PhysConfig n psi kappa tau) (e : Fin n)
    (hq : QuietAtR1 hpsi h2 ring B e) :
    erase (stepV10kR1 hpsi h2 ring (lift B) e) =
      BirthCheckPermitRepairLeaf.step1 hpsi h2 ring (erase (lift B)) e :=
  (congrArg (fun C : Config n psi kappa tau => erase C)
    (step_lift_step1 hpsi h2 ring hn B e hq)).trans (erase_lift _)

theorem run_lift_step1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlongR1 hpsi h2 ring B w) :
    w.foldl (stepV10kR1 hpsi h2 ring) (lift B) =
      lift (w.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring) B) := by
  change w.foldl (stepB9 (r1Host hpsi h2) hpsi ring) (lift B) = _
  have h := run_lift (r1Host hpsi h2) hpsi ring hn w B hq
  rw [hostStep_r1_fun_eq hpsi h2 ring] at h
  exact h

theorem run_erase_step1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlongR1 hpsi h2 ring B w) :
    erase (w.foldl (stepV10kR1 hpsi h2 ring) (lift B)) =
      w.foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring) B :=
  (congrArg (fun C : Config n psi kappa tau => erase C)
    (run_lift_step1 hpsi h2 ring hn w B hq)).trans (erase_lift _)

theorem run_lift_step1_prefix (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlongR1 hpsi h2 ring B w)
    (t : Nat) :
    (w.take t).foldl (stepV10kR1 hpsi h2 ring) (lift B) =
      lift ((w.take t).foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring) B) :=
  run_lift_step1 hpsi h2 ring hn (w.take t) B
    (quietAlong_take (r1Host hpsi h2) ring t w B hq)

theorem run_erase_step1_prefix (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (w : List (Fin n))
    (B : PhysConfig n psi kappa tau) (hq : QuietAlongR1 hpsi h2 ring B w)
    (t : Nat) :
    erase ((w.take t).foldl (stepV10kR1 hpsi h2 ring) (lift B)) =
      (w.take t).foldl (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring) B :=
  (congrArg (fun C : Config n psi kappa tau => erase C)
    (run_lift_step1_prefix hpsi h2 ring hn w B hq t)).trans (erase_lift _)

/-
PLAN -- outside this file's theorem claims.
A useful probabilistic family satisfying QuietAlongR1 still needs a producer.
The quiet-word hypothesis is not inferred from leaderlessness, no birth,
or the two guarded R1 SpliceLawsOn certificates.

No SpliceLaws field is used above. Consequently class E is not excluded:
its rows are covered whenever the explicit QuietAtR1 test holds. These
conditional equalities do not prove unrestricted R1 geometric safety,
positive quiet-word mass, or legitimacy closure.
-/

end B9SpliceHostQuiescence
