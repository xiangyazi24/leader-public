import Leader.Wu.Coherence.Controller
import Leader.Wu.Coherence.SixTokenBranches


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31Branches2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches


variable {n ψ κ τ : Nat}


/-! ## Closed one-cell collision witnesses for the two false closure branches -/


namespace CollisionClosureCounterexample


private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring1 : DirectedRing 1 := ⟨by decide⟩


/-- A completely main-clear label-zero leader.  The final R2 collision tail
can delete its left copy without changing bit, label, or main path. -/
private def leader0 : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) (0 : Fin 3)
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := true
      shield := true
      gen_ws := false
      label := 0
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
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩


private def sealedInput : FC 1 3 3 48 := fun _ =>
  ⟨leader0, ⟨.sealed, .none⟩⟩


private def openInput : FC 1 3 3 48 := fun _ =>
  ⟨leader0, ⟨.open, .none⟩⟩


private def sealedAfter : FC 1 3 3 48 :=
  stepV3 h3 h23 ring1 sealedInput 0


private def openAfter : FC 1 3 3 48 :=
  stepV3 h3 h23 ring1 openInput 0


private theorem sealedInput_shape : ControllerShapeV3 ring1 sealedInput := by
  decide +kernel


private theorem sealedAfter_shape : ControllerShapeV3 ring1 sealedAfter := by
  decide +kernel


private theorem openInput_shape : ControllerShapeV3 ring1 openInput := by
  decide +kernel


private theorem openAfter_shape : ControllerShapeV3 ring1 openAfter := by
  decide +kernel


/-- On the unique self-edge, after the first collision the sealed wrapper is
held by its relabel gate. -/
private theorem sealedAfter_fixed :
    stepV3 h3 h23 ring1 sealedAfter 0 = sealedAfter := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  decide +kernel


/-- The open witness is also fixed after its first left-leader deletion: the
next follower/follower mismatch is a responder relabel hazard, and the native
self-edge convention keeps the left output. -/
private theorem openAfter_fixed :
    stepV3 h3 h23 ring1 openAfter 0 = openAfter := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  decide +kernel


private theorem one_sound_of_fixed
    (C D : FC 1 3 3 48)
    (hC : ControllerShapeV3 ring1 C)
    (hD : ControllerShapeV3 ring1 D)
    (hCD : ∀ e : Fin 1, stepV3 h3 h23 ring1 C e = D)
    (hDD : ∀ e : Fin 1, stepV3 h3 h23 ring1 D e = D) :
    ControllerSoundV3 h3 h23 ring1 C := by
  intro w
  cases w with
  | nil => simpa using hC
  | cons e w =>
      simp only [List.foldl_cons]
      rw [hCD e]
      have hfold :
          w.foldl (stepV3 h3 h23 ring1) D = D := by
        induction w with
        | nil => rfl
        | cons a w ih =>
            simp only [List.foldl_cons, hDD a]
            exact ih
      rw [hfold]
      exact hD


private theorem sealedInput_sound :
    ControllerSoundV3 h3 h23 ring1 sealedInput := by
  apply one_sound_of_fixed sealedInput sealedAfter
    sealedInput_shape sealedAfter_shape
  · intro e
    have he : e = (0 : Fin 1) := Subsingleton.elim _ _
    subst e
    rfl
  · intro e
    have he : e = (0 : Fin 1) := Subsingleton.elim _ _
    subst e
    exact sealedAfter_fixed


private theorem openInput_sound :
    ControllerSoundV3 h3 h23 ring1 openInput := by
  apply one_sound_of_fixed openInput openAfter
    openInput_shape openAfter_shape
  · intro e
    have he : e = (0 : Fin 1) := Subsingleton.elim _ _
    subst e
    rfl
  · intro e
    have he : e = (0 : Fin 1) := Subsingleton.elim _ _
    subst e
    exact openAfter_fixed


private theorem sealedInput_geometry :
    AdmittedPostBirthGeometryV3 h3 ring1 sealedInput := by
  decide +kernel


private theorem sealedInput_coherent :
    CoherentPrefixesV3 ring1 sealedInput := by
  decide +kernel


private theorem sealedInput_branch :
    branchAtV3 h3 h23 (sealedInput 0)
      (sealedInput (ring1.rightNeighbor 0)) = .sealed := by
  decide +kernel


private theorem sealedAfter_not_geometry :
    ¬ AdmittedPostBirthGeometryV3 h3 ring1 sealedAfter := by
  decide +kernel


private theorem sealedInput_recovered :
    RecoveredV3 h3 h23 ring1 sealedInput :=
  ⟨sealedInput_geometry, sealedInput_coherent, sealedInput_sound⟩


theorem sealed_preservation_false :
    ¬ SealedPreservationObligationV3 (κ := 3) (τ := 48) h3 h23 ring1 := by
  intro h
  have hout := h sealedInput 0 sealedInput_recovered sealedInput_branch
  exact sealedAfter_not_geometry hout.1


private theorem openInput_geometry :
    AdmittedPostBirthGeometryV3 h3 ring1 openInput := by
  decide +kernel


private theorem openInput_coherent :
    CoherentPrefixesV3 ring1 openInput := by
  decide +kernel


private theorem openInput_branch :
    branchAtV3 h3 h23 (openInput 0)
      (openInput (ring1.rightNeighbor 0)) = .openNoHazard := by
  decide +kernel


private theorem openAfter_not_geometry :
    ¬ AdmittedPostBirthGeometryV3 h3 ring1 openAfter := by
  decide +kernel


private theorem openInput_recovered :
    RecoveredV3 h3 h23 ring1 openInput :=
  ⟨openInput_geometry, openInput_coherent, openInput_sound⟩


theorem openNoHazard_preservation_false :
    ¬ OpenNoHazardPreservationObligationV3
      (κ := 3) (τ := 48) h3 h23 ring1 := by
  intro h
  have hout := h openInput 0 openInput_recovered openInput_branch
  exact openAfter_not_geometry hout.1


end CollisionClosureCounterexample


/-! ## Generic physically-inert lifting helpers -/


private def SamePhysicalV3
    (C D : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, (D i).phys = (C i).phys


private def NonOpenMonotoneV3
    (C D : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    NonOpen (eraseCellV3 (C i)) →
      NonOpen (eraseCellV3 (D i))


private theorem admitted_of_samePhysicalV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    {C D : FC n ψ κ τ}
    (hSame : SamePhysicalV3 C D)
    (hC : AdmittedPostBirthGeometryV3 hψ ring C) :
    AdmittedPostBirthGeometryV3 hψ ring D := by
  change R2Coherence.AdmittedPostBirthGeometry hψ ring (eraseCfgV3 C) at hC
  change R2Coherence.AdmittedPostBirthGeometry hψ ring (eraseCfgV3 D)
  unfold R2Coherence.AdmittedPostBirthGeometry at hC ⊢
  have hRaw : ∀ i : Fin n,
      R2Coherence.raw (eraseCfgV3 D i) =
        R2Coherence.raw (eraseCfgV3 C i) := by
    intro i
    simp [eraseCfgV3, eraseCellV3, R2Coherence.raw, hSame i]
  constructor
  · intro i hi
    rw [hRaw i]
    apply hC.1 i
    rwa [← hRaw i]
  · intro i
    simpa only [hRaw i, hRaw (ring.rightNeighbor i)] using hC.2 i


private theorem coherent_of_samePhysical_nonOpenV3
    (ring : DirectedRing n)
    {C D : FC n ψ κ τ}
    (hSame : SamePhysicalV3 C D)
    (hMono : NonOpenMonotoneV3 C D)
    (hC : CoherentPrefixesV3 ring C) :
    CoherentPrefixesV3 ring D := by
  apply R2CoherenceBranches.coherentPrefixes_of_quarantineMutation ring ?_ hC
  intro i
  constructor
  · intro hchg
    exfalso
    apply hchg
    simpa [eraseCfgV3, eraseCellV3] using hSame i
  · exact hMono i


private theorem samePhysical_stepV3_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPair :
      (rowV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1.phys = (C e).phys ∧
      (rowV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2.phys =
          (C (ring.rightNeighbor e)).phys) :
    SamePhysicalV3 C (stepV3 hψ h2 ring C e) := by
  intro i
  by_cases hie : i = e
  · subst i
    simpa [stepV3, protocolV3, PopulationProtocol.step] using hPair.1
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [stepV3, protocolV3, PopulationProtocol.step, hie] using hPair.2
    · simp [stepV3, protocolV3, PopulationProtocol.step, hie, hij]


private theorem nonOpenMonotone_stepV3_of_pair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hL :
      NonOpen (eraseCellV3 (C e)) →
        NonOpen (eraseCellV3
          (rowV3 hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).1))
    (hR :
      NonOpen (eraseCellV3 (C (ring.rightNeighbor e))) →
        NonOpen (eraseCellV3
          (rowV3 hψ (by decide : 0 < 2) h2
            (C e) (C (ring.rightNeighbor e))).2)) :
    NonOpenMonotoneV3 C (stepV3 hψ h2 ring C e) := by
  intro i hi
  by_cases hie : i = e
  · subst i
    simpa [stepV3, protocolV3, PopulationProtocol.step] using hL hi
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simpa [stepV3, protocolV3, PopulationProtocol.step, hie] using hR hi
    · simpa [stepV3, protocolV3, PopulationProtocol.step, hie, hij] using hi


private theorem nonOpen_startClosingV3 (u : Cell ψ κ τ) :
    NonOpen (eraseCellV3 (startClosing u)) := by
  simp [NonOpen, eraseCellV3, startClosing, setControl, eraseTokenV3]


/-! ## OPEN-HAZARD -/


private theorem branch_openHazard_conditions
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true) := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all


private theorem rowV3_openHazard_physical
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    (rowV3 hψ (by decide : 0 < 2) h2 l r).1.phys = l.phys ∧
      (rowV3 hψ (by decide : 0 < 2) h2 l r).2.phys = r.phys := by
  rcases branch_openHazard_conditions hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  have hp := openStageV3_hazard_physical
    hψ (by decide : 0 < 2) h2 l r hHaz
  simpa [rowV3, ordinaryStageV3, hln, hrn, hlo, hro] using hp


private theorem rowV3_openHazard_nonOpen
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    (NonOpen (eraseCellV3 l) →
      NonOpen (eraseCellV3
        (rowV3 hψ (by decide : 0 < 2) h2 l r).1)) ∧
    (NonOpen (eraseCellV3 r) →
      NonOpen (eraseCellV3
        (rowV3 hψ (by decide : 0 < 2) h2 l r).2)) := by
  rcases branch_openHazard_conditions hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, _⟩
  constructor
  · intro h
    exfalso
    simpa [NonOpen, eraseCellV3, eraseTokenV3, hlo, hln] using h
  · intro h
    exfalso
    simpa [NonOpen, eraseCellV3, eraseTokenV3, hro, hrn] using h


theorem openHazard_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    OpenHazardPreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hPair := rowV3_openHazard_physical hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hSame := samePhysical_stepV3_of_pair hψ h2 ring C e hPair
  have hPairNon := rowV3_openHazard_nonOpen hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hMono := nonOpenMonotone_stepV3_of_pair
    hψ h2 ring C e hPairNon.1 hPairNon.2
  exact ⟨
    admitted_of_samePhysicalV3 hψ ring hSame hGeom,
    coherent_of_samePhysical_nonOpenV3 ring hSame hMono hCoh,
    controllerSoundV3_step hψ h2 ring C e hSound⟩


/-! ## MIXED -/


private theorem branch_mixed_priority_clear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all


private theorem passiveEdgeOK_of_admitted
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hGeom : AdmittedPostBirthGeometryV3 hψ ring C)
    (e : Fin n) :
    passiveEdgeOKV3 (C e) (C (ring.rightNeighbor e)) = true := by
  change R2Coherence.AdmittedPostBirthGeometry hψ ring (eraseCfgV3 C) at hGeom
  have hEdge := hGeom.2 e
  change
    (raw (C (ring.rightNeighbor e))).leader = true ∨
      (raw (C (ring.rightNeighbor e))).label =
        ⟨((raw (C e)).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ at hEdge
  rcases hEdge with hLeader | hSucc
  · have hLeader' :
        (R2Coherence.raw
          ((eraseCfgV3 C) (ring.rightNeighbor e))).leader = true := by
      change (raw (C (ring.rightNeighbor e))).leader = true
      exact hLeader
    have hZero := hGeom.1 (ring.rightNeighbor e) hLeader'
    change
      (raw (C (ring.rightNeighbor e))).label = ⟨0, hψ⟩ at hZero
    have hv : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
      simpa using congrArg Fin.val hZero
    simp [passiveEdgeOKV3, atRootB, hv]
  · have hv :
        (raw (C (ring.rightNeighbor e))).label.val =
          ((raw (C e)).label.val + 1) % ψ := by
      simpa using congrArg Fin.val hSucc
    by_cases hr0 : (raw (C (ring.rightNeighbor e))).label.val = 0
    · simp [passiveEdgeOKV3, atRootB, hr0]
    · have hle : (raw (C e)).label.val + 1 ≤ ψ := by
        omega
      have hne : (raw (C e)).label.val + 1 ≠ ψ := by
        intro heq
        have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
          calc
            (raw (C (ring.rightNeighbor e))).label.val =
                ((raw (C e)).label.val + 1) % ψ := hv
            _ = 0 := by rw [heq, Nat.mod_self]
        exact hr0 hz
      have hlt : (raw (C e)).label.val + 1 < ψ := by
        omega
      have hs :
          (raw (C (ring.rightNeighbor e))).label.val =
            (raw (C e)).label.val + 1 := by
        simpa [Nat.mod_eq_of_lt hlt] using hv
      simp [passiveEdgeOKV3, successorB, hs]



private theorem rowV3_mixed_form
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed)
    (hGood : passiveEdgeOKV3 l r = true) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) := by
  rcases branch_mixed_priority_clear hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR⟩
  by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
  · have hSeal : ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) := by
      intro hs
      have h := hb
      simp [branchAtV3, hSeek, hSweep, hCommit, hRelease,
        hScrub, hOpenR, hNone, hs] at h
    have hOpen : ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open) := by
      intro ho
      have h := hb
      unfold branchAtV3 at h
      simp [hSeek, hSweep, hCommit, hRelease,
        hScrub, hOpenR, hNone, hSeal, ho] at h
      split at h <;> simp_all
    right
    simpa [rowV3, ordinaryStageV3, hSeek, hSweep, hCommit,
      hRelease, hScrub, hOpenR, hNone, hSeal, hOpen] using
      (normalizePassiveV3_good_edge l r hGood)
  · left
    simp [rowV3, ordinaryStageV3, hSeek, hSweep, hCommit,
      hRelease, hScrub, hOpenR, hNone]


private theorem rowV3_mixed_physical_nonOpen
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed)
    (hGood : passiveEdgeOKV3 l r = true) :
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.phys = l.phys ∧
      (rowV3 hψ (by decide : 0 < 2) h2 l r).2.phys = r.phys) ∧
    (NonOpen (eraseCellV3 l) →
      NonOpen (eraseCellV3
        (rowV3 hψ (by decide : 0 < 2) h2 l r).1)) ∧
    (NonOpen (eraseCellV3 r) →
      NonOpen (eraseCellV3
        (rowV3 hψ (by decide : 0 < 2) h2 l r).2)) := by
  rcases rowV3_mixed_form hψ h2 l r hb hGood with hId | hClose
  · rw [hId]
    exact ⟨⟨rfl, rfl⟩, id, id⟩
  · rw [hClose]
    refine ⟨⟨rfl, ?_⟩, id, ?_⟩
    · simp [startClosing, setControl]
    · intro _
      exact nonOpen_startClosingV3 r


theorem mixed_preservation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    MixedPreservationObligationV3
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hRec hb
  rcases hRec with ⟨hGeom, hCoh, hSound⟩
  have hGood := passiveEdgeOK_of_admitted hψ ring C hGeom e
  have hLocal := rowV3_mixed_physical_nonOpen hψ h2
    (C e) (C (ring.rightNeighbor e)) hb hGood
  have hSame := samePhysical_stepV3_of_pair hψ h2 ring C e hLocal.1
  have hMono := nonOpenMonotone_stepV3_of_pair
    hψ h2 ring C e hLocal.2.1 hLocal.2.2
  exact ⟨
    admitted_of_samePhysicalV3 hψ ring hSame hGeom,
    coherent_of_samePhysical_nonOpenV3 ring hSame hMono hCoh,
    controllerSoundV3_step hψ h2 ring C e hSound⟩


end R2CoherenceV31Branches2
