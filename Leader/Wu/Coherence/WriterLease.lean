import Leader.Wu.Entrance.CheckWriteStateFrame
import Leader.Wu.WriteSeq.WriterProducerRepair
import Leader.Wu.Coherence.SixTokenController


set_option autoImplicit false
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalEntryCut BirthShortDoneCuts
  K2BirthDispatcher K2BirthLeaderNormalize


namespace R2F


open WriterProducerRepair
open BirthTwoStageEscape


variable {n ψ κ τ width : Nat}


def fuelCap (ψ : Nat) : Nat := 24 * ψ
abbrev Credit (ψ : Nat) := Fin (fuelCap ψ + 1)


structure WCell (ψ κ : Nat) where
  agent : AuthorizedBoundedAgentState ψ κ
  fuel : Credit ψ


structure Cell (ψ κ τ : Nat) where
  base : ExpiringAgentState ψ κ τ
  fuel : Credit ψ


abbrev FC (n ψ κ τ : Nat) := Fin n → Cell ψ κ τ


def freshFuel (ψ : Nat) : Credit ψ :=
  ⟨fuelCap ψ, Nat.lt_succ_self _⟩


def put (u : WCell ψ κ) (b : BoundedAgentState ψ κ) : WCell ψ κ :=
  { u with agent := ⟨b, reconcilePermit u.agent.erase b.erase⟩ }


def idleFuel (u : WCell ψ κ) : WCell ψ κ :=
  if producerActive u.agent.core then u else { u with fuel := 0 }


def tick (u : WCell ψ κ) : WCell ψ κ :=
  if producerActive u.agent.core then
    if u.fuel.val = 0 then
      let b := u.agent.core
      let cleared : BoundedAgentState ψ κ :=
        { b with
          write_state := .none
          path3 := none
          write := .none
          b_carry := false }
      let v : WCell ψ κ := put u cleared
      { v with fuel := 0 }
    else
      { u with
        fuel :=
          ⟨u.fuel.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) u.fuel.isLt⟩ }
  else
    { u with fuel := 0 }



def mint (u : WCell ψ κ) (carry : Bool) : WCell ψ κ :=
  let b := u.agent.core
  let b' : BoundedAgentState ψ κ :=
    { b with
      path3 := some {
        label := b.label
        bit := if b.bit then 1 else 0
        flag := 1 }
      write_state := .done
      write := .none
      bit := if carry then !b.bit else b.bit
      b_carry := carry && b.bit }
  put u b'



def producerStep (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  let l : WCell ψ κ :=
    if producerStarts l.agent.core then
      let b := l.agent.core
      let started : BoundedAgentState ψ κ :=
        { b with
          write_state := .produce
          write := .none
          b_carry := false }
      let v : WCell ψ κ := put l started
      { v with fuel := freshFuel ψ }
    else l
  let q : WCell ψ κ × WCell ψ κ :=
    if l.agent.core.write_state = .produce ∧
        l.agent.core.path3 = none ∧
        l.agent.core.label.val + 1 = r.agent.core.label.val ∧
        r.agent.core.leader = false ∧
        (l.agent.core.leader = false ∨ l.agent.core.label.val = 0) then
      let r : WCell ψ κ :=
        if r.agent.core.path3 = none ∧
            producerActive r.agent.core = false then
          let b := r.agent.core
          let started : BoundedAgentState ψ κ :=
            { b with
              write_state := .produce
              write := .none
              b_carry := false }
          let v : WCell ψ κ := put r started
          { v with fuel := l.fuel }
        else r
      let r : WCell ψ κ :=
        if r.agent.core.write_state = .produce ∧
            r.agent.core.path3 = none ∧
            r.agent.core.label.val + 1 = ψ then
          mint r true
        else r
      if ackReady r.agent.core then
        let b := r.agent.core
        let released : BoundedAgentState ψ κ :=
          { b with
            write_state := .depart
            write := .none
            b_carry := false }
        (mint l r.agent.core.b_carry, put r released)
      else (l, r)
    else (l, r)
  let l := q.1
  let l : WCell ψ κ :=
    if l.agent.core.leader = true ∧ l.agent.core.label.val = 0 ∧
        ackReady l.agent.core = true then
      let b := l.agent.core
      let finished : BoundedAgentState ψ κ :=
        { b with
          write_state := .depart
          write := .none
          gen_ws := false
          b_carry := false }
      put l finished
    else l
  (idleFuel l, idleFuel q.2)



def stationaryProducerRow (hψ : 0 < ψ) (l r : WCell ψ κ) :
    WCell ψ κ × WCell ψ κ :=
  let l := tick l
  let r := tick r
  if producerActive l.agent.core || producerActive r.agent.core ||
      producerStarts l.agent.core then
    producerStep l r
  else
    let q := BirthStationaryWrite.stationaryPersistentBoundedRow
      hψ l.agent r.agent
    (⟨q.1, 0⟩, ⟨q.2, 0⟩)


def ofAuth (u : AuthorizedAgentState ψ)
    (h : u.core.inProtocolDomain κ) : AuthorizedBoundedAgentState ψ κ :=
  ⟨BoundedAgentState.ofDomain u.core h, u.path0Crossed⟩


section Q13367R2FOrdinaryCuts
set_option Elab.async false

attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.permitFix
  BirthShortDoneCuts.beforeWriteWidth
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
  R2F.stationaryProducerRow

private def checkedBounded
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
  let hq := doneThroughCheckEntryWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2F.ofAuth q.1 hq.1, R2F.ofAuth q.2 hq.2)

private def permitBounded (u : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ :=
    BirthCheckPermitRepair.permitFix u.erase
  let hq : q.core.inProtocolDomain κ := by
    change (BirthCheckPermitRepair.permitFix u.erase).core.inProtocolDomain κ
    rw [BirthCheckPermitRepair.permitFix_core]
    exact u.core.erase_inProtocolDomain
  R2F.ofAuth q hq

private def beforeWriterBounded
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    beforeWriteWidth hψ hw hle l.erase r.erase
  let hq := beforeWriteWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2F.ofAuth q.1 hq.1, R2F.ofAuth q.2 hq.2)

private def markBounded
    (oldL oldR outL outR : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    (outL.erase, outR.erase)
  let ha : a.1.core.inProtocolDomain κ ∧ a.2.core.inProtocolDomain κ :=
    ⟨outL.core.erase_inProtocolDomain, outR.core.erase_inProtocolDomain⟩
  let born : Bool := authBirth oldL.erase oldR.erase a
  let m : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    markLeaderBirth born a
  let hm := markLeaderBirth_inProtocolDomain born a ha
  (R2F.ofAuth m.1 hm.1, R2F.ofAuth m.2 hm.2)

def ordinary (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  let c : AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
    checkedBounded hψ hw hle l.agent r.agent
  let f : AuthorizedBoundedAgentState ψ κ := permitBounded c.1
  let p : AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
    beforeWriterBounded hψ hw hle f c.2
  let z : WCell ψ κ × WCell ψ κ :=
    R2F.stationaryProducerRow hψ
      ⟨p.1, l.fuel⟩ ⟨p.2, r.fuel⟩
  let m : AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
    markBounded l.agent r.agent z.1.agent z.2.agent
  (⟨m.1, z.1.fuel⟩, ⟨m.2, z.2.fuel⟩)

end Q13367R2FOrdinaryCuts











def bounded (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  let l0 := normalizeDeletion l.agent.erase
  let r0 := normalizeDeletion r.agent.erase
  if deletionActive r0 || deletionActive l0 then
    let q := BirthCheckPermitRepair.bounded hψ hw hle l.agent r.agent
    (tick ⟨q.1, l.fuel⟩, tick ⟨q.2, r.fuel⟩)
  else
    let hl := (cleanup_helpers_inProtocolDomain
      l.agent.erase l.agent.core.erase_inProtocolDomain).1
    let hr := (cleanup_helpers_inProtocolDomain
      r.agent.erase r.agent.core.erase_inProtocolDomain).1
    ordinary hψ hw hle
      ⟨ofAuth l0 hl, l.fuel⟩ ⟨ofAuth r0 hr, r.fuel⟩


def row (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l.base
  let r0 := prepareExpiringDisposal hψ r.base
  let q := bounded hψ hw hle
    ⟨l0.core, l.fuel⟩ ⟨r0.core, r.fuel⟩
  let a := deletionPriorityExpireOne τ l0 ⟨q.1.agent, l0.stall⟩
  let b := deletionPriorityExpireOne τ r0 ⟨q.2.agent, r0.stall⟩
  let z := finalPhysical hψ l.base r.base
    (normalizeLeader hψ a) (normalizeLeader hψ b)
  (⟨z.1, q.1.fuel⟩, ⟨z.2, q.2.fuel⟩)


def protocol (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := Cell ψ κ τ
  Y := Bool
  transition := row hψ (by decide : 0 < 2) h2
  output := fun u => u.base.core.core.leader


def step (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (protocol hψ h2 κ τ).step ring C e


/-- The exact base-3 split used by inherited-credit recovery. -/
theorem base3_inherited_split (f : Nat) :
    2 * 3 ^ f < 3 ^ (f + 1) := by
  rw [Nat.pow_succ]
  have hp : 0 < 3 ^ f := Nat.pow_pos (by decide)
  omega


def Leaderless (C : FC n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless (fun i => (C i).base)


def NoProducer (C : FC n ψ κ τ) : Prop :=
  ∀ i, producerActive (C i).base.core.core = false


def producerWeight (u : Cell ψ κ τ) : Nat :=
  if producerActive u.base.core.core then 3 ^ (u.fuel.val + 1) else 0


def producerPotential (C : FC n ψ κ τ) : Nat :=
  ((List.finRange n).map (fun i => producerWeight (C i))).sum


def producerRecoveryB (n ψ : Nat) : Nat :=
  3 * n * (Nat.log2 (n * 3 ^ (fuelCap ψ + 1)) + 2)


noncomputable def ProducerRecoveryHalfMass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ, Leaderless C →
    2 * avoidCount (step hψ h2 ring) Leaderless NoProducer
      C (producerRecoveryB n ψ) ≤ n ^ (producerRecoveryB n ψ)


theorem producerRecovery_half_mass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (h : ProducerRecoveryHalfMass (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (hC : Leaderless C) :
    2 * avoidCount (step hψ h2 ring) Leaderless NoProducer
      C (producerRecoveryB n ψ) ≤ n ^ (producerRecoveryB n ψ) :=
  h C hC



section Q13367CutFrames


attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.permitFix
  BirthShortDoneCuts.beforeWriteWidth
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
  R2F.stationaryProducerRow


/-- The through-CHECK bounded cut preserves both writer-state coordinates. -/
theorem checkedBounded_writeState_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := checkedBounded hψ hw hle l r
    q.1.core.write_state = l.core.write_state ∧
      q.2.core.write_state = r.core.write_state := by
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
  let hq := doneThroughCheckEntryWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  have hchecked :
      checkedBounded hψ hw hle l r =
        (R2F.ofAuth q.1 hq.1, R2F.ofAuth q.2 hq.2) := by
    unfold checkedBounded
    rfl
  rw [hchecked]
  have h :=
    B6CheckWriteStateFrame.doneThroughCheckEntryWidth_writeState_frame
      hψ hw hle κ l.erase r.erase
  have hLout :
      (R2F.ofAuth q.1 hq.1).core.write_state =
        q.1.core.write_state := by
    rfl
  have hRout :
      (R2F.ofAuth q.2 hq.2).core.write_state =
        q.2.core.write_state := by
    rfl
  have hLin : l.erase.core.write_state = l.core.write_state := by
    rfl
  have hRin : r.erase.core.write_state = r.core.write_state := by
    rfl
  exact ⟨hLout.trans (h.1.trans hLin),
    hRout.trans (h.2.trans hRin)⟩


end Q13367CutFrames




end R2F


namespace R2FRegression


variable {ψ : Nat}


def cleanF (hψ : 0 < ψ) (old : Fin ψ → Bool) (i : Fin ψ) :
    R2F.Cell ψ ψ (16 * ψ) :=
  let q := WriterProducerRegression.clean hψ old i
  ⟨q.base, 0⟩


abbrev ProducedF (old : Fin ψ → Bool)
    (C : R2F.FC ψ ψ ψ (16 * ψ)) : Prop :=
  ∀ i : Fin ψ, let u := (C i).base.core.core
    u.path3 = some { label := i, bit := if old i then 1 else 0, flag := 1 } ∧
    u.bit = WriterProducerRegression.incrementBit old i ∧
    u.label = i ∧ u.leader = (i.val == 0) ∧
    u.write_state = .depart ∧ u.write = .none ∧
    u.b_carry = false ∧ u.gen_ws = false ∧ (C i).fuel = 0


def runF (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (old : Fin ψ → Bool)
    (w : List (Fin ψ)) : R2F.FC ψ ψ ψ (16 * ψ) :=
  w.foldl (R2F.step hψ h2 (⟨hψ⟩ : DirectedRing ψ))
    (cleanF hψ old)


deriving instance DecidableEq for R2F.Cell

section Q13367ProducerF000
set_option Elab.async false
set_option synthInstance.maxSize 4096

private abbrev Q13367Cfg := R2F.FC 3 3 3 48

private def q13367_seed : Q13367Cfg :=
  cleanF (by decide : 0 < 3) (fun _ => false)

private def q13367_step : Q13367Cfg → Fin 3 → Q13367Cfg :=
  R2F.step (by decide : 0 < 3) (by decide : 2 ≤ 3)
    (⟨by decide⟩ : DirectedRing 3)

private def q13367_payload (lab : Fin 3) :
    Option (BoundedPath3Info 3) :=
  some { label := lab, bit := 0, flag := 1 }

private def q13367_literal (i : Fin 3)
    (bit : Bool := false)
    (ws : WriteState := .none)
    (p3 : Option (BoundedPath3Info 3) := none)
    (fuel : R2F.Credit 3 := 0)
    (stall : Fin 49 := 0)
    (h : Bool := false)
    (resetCmd : Bool := false)
    (echo : Bool := false)
    (signal : Fin 2 := 0)
    (gen : Bool := i.val == 0) : R2F.Cell 3 3 48 :=
  let original := q13367_seed i
  let b := original.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      bit := bit
      write_state := ws
      path3 := p3
      h_field := h
      reset_cmd := resetCmd
      echo := echo
      signal_B := signal
      gen_ws := gen }
  let base : ExpiringAgentState 3 3 48 := ⟨⟨b', false⟩, stall⟩
  ⟨base, fuel⟩

-- Edge 0: root and label 1 are live producers with fresh R2F credit 24*3=72.
private def q13367_c1 : Q13367Cfg := fun i =>
  match i.val with
  | 0 => q13367_literal 0
      (ws := .produce) (fuel := 72) (stall := 48) (h := true)
  | 1 => q13367_literal 1
      (ws := .produce) (fuel := 72) (stall := 48)
      (resetCmd := true) (signal := 1)
  | _ => q13367_seed 2

-- Edge 1: terminal cell is released; label 1 holds the done acknowledgement.
private def q13367_c2 : Q13367Cfg := fun i =>
  match i.val with
  | 0 => q13367_c1 0
  | 1 => q13367_literal 1
      (ws := .done) (p3 := q13367_payload 1)
      (fuel := 71) (stall := 47) (echo := true) (signal := 1)
  | _ => q13367_literal 2
      (bit := true) (ws := .depart) (p3 := q13367_payload 2)
      (stall := 48) (resetCmd := true) (signal := 1)

-- Final edge 0: acknowledgement reaches the root and every producer fuel is idle-zero.
private def q13367_c3 : Q13367Cfg := fun i =>
  match i.val with
  | 0 => q13367_literal 0
      (ws := .depart) (p3 := q13367_payload 0)
      (stall := 47) (gen := false)
  | 1 => q13367_literal 1
      (ws := .depart) (p3 := q13367_payload 1)
      (stall := 46) (h := true) (signal := 1)
  | _ => q13367_c2 2

-- Closed one-service checks: no nested transition appears in an input record.
private theorem q13367_s1_point : ∀ i : Fin 3,
    q13367_step q13367_seed 0 i = q13367_c1 i := by
  decide +kernel

private theorem q13367_s2_point : ∀ i : Fin 3,
    q13367_step q13367_c1 1 i = q13367_c2 i := by
  decide +kernel

private theorem q13367_s3_point : ∀ i : Fin 3,
    q13367_step q13367_c2 0 i = q13367_c3 i := by
  decide +kernel

private theorem q13367_s1 :
    q13367_step q13367_seed 0 = q13367_c1 :=
  funext q13367_s1_point

private theorem q13367_s2 :
    q13367_step q13367_c1 1 = q13367_c2 :=
  funext q13367_s2_point

private theorem q13367_s3 :
    q13367_step q13367_c2 0 = q13367_c3 :=
  funext q13367_s3_point

section Q13367Composition
attribute [local irreducible] R2F.step R2F.row R2F.bounded R2F.ordinary

private theorem q13367_run_eq :
    runF (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (fun _ => false) ([0, 1, 0] : List (Fin 3)) = q13367_c3 := by
  simp only [runF, List.foldl_cons, List.foldl_nil]
  change q13367_step
    (q13367_step (q13367_step q13367_seed 0) 1) 0 = q13367_c3
  rw [q13367_s1, q13367_s2, q13367_s3]

end Q13367Composition

private abbrev Q13367Result (C : Q13367Cfg) : Prop :=
  ProducedF (fun _ => false) C ∧
    (C 0).base.core.core.bit = false ∧
    (C 1).base.core.core.bit = false ∧
    (C 2).base.core.core.bit = true

-- This decision sees only literal records and incrementBit, not a protocol run.
private theorem q13367_result_literal : Q13367Result q13367_c3 := by
  decide +kernel

private theorem q13367_result_run :
    Q13367Result
      (runF (by decide : 0 < 3) (by decide : 2 ≤ 3)
        (fun _ => false) ([0, 1, 0] : List (Fin 3))) := by
  exact Eq.mpr
    (congrArg Q13367Result q13367_run_eq)
    q13367_result_literal

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 65536 in
theorem producerF000 :
    let C := runF (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (fun _ => false) ([0, 1, 0] : List (Fin 3))
    ProducedF (fun _ => false) C ∧
      (C 0).base.core.core.bit = false ∧
      (C 1).base.core.core.bit = false ∧
      (C 2).base.core.core.bit = true := by
  exact q13367_result_run

end Q13367ProducerF000



end R2FRegression


namespace R2WriterLease


open WriterProducerRepair


variable {n ψ κ τ : Nat}


/-! ## Local writer-age arithmetic


These are the only three declarations used from the old
`PPLLWriterAgeExpiration` module.  They are copied here verbatim in behavior
and kept private to this file/namespace. -/


private def zeroWriterAge (ω : Nat) : Fin (ω + 1) :=
  ⟨0, by omega⟩


private def freshWriterAge (ω : Nat) : Fin (ω + 1) :=
  ⟨ω, by omega⟩


private def decWriterAge {ω : Nat}
    (a : Fin (ω + 1)) (h : 0 < a.val) : Fin (ω + 1) :=
  ⟨a.val - 1, by omega⟩


inductive Mode where
  | scrub
  | run
  deriving DecidableEq, Repr


def leaseCap (ψ : Nat) : Nat := 8 * ψ
abbrev Lease (ψ : Nat) := Fin (leaseCap ψ + 1)


/-- Extra lease alphabet over one R2Coherence physical cell:
2 modes × trusted × allowBirth × tainted × (8ψ+1) lease values. -/
def leaseMetadataStates (ψ : Nat) : Nat :=
  16 * (leaseCap ψ + 1)


theorem leaseMetadataStates_exact (ψ : Nat) :
    leaseMetadataStates ψ = 128 * ψ + 16 := by
  simp [leaseMetadataStates, leaseCap]
  omega


structure Cell (ψ κ τ : Nat) where
  phys : R2Coherence.Cell ψ κ τ
  lease : Lease ψ
  trusted : Bool
  allowBirth : Bool
  tainted : Bool
  mode : Mode
  deriving DecidableEq


abbrev FC (n ψ κ τ : Nat) := Fin n → Cell ψ κ τ


def raw (u : Cell ψ κ τ) : BoundedAgentState ψ κ :=
  R2Coherence.raw u.phys


def zeroLease (ψ : Nat) : Lease ψ :=
  zeroWriterAge (leaseCap ψ)


def freshLease (ψ : Nat) : Lease ψ :=
  freshWriterAge (leaseCap ψ)


def decLease (a : Lease ψ) (h : 0 < a.val) : Lease ψ :=
  decWriterAge a h


@[simp] theorem zeroLease_val (ψ : Nat) : (zeroLease ψ).val = 0 := rfl
@[simp] theorem freshLease_val (ψ : Nat) :
    (freshLease ψ).val = leaseCap ψ := rfl
@[simp] theorem decLease_val (a : Lease ψ) (h : 0 < a.val) :
    (decLease a h).val = a.val - 1 := rfl


/-- Producer produce/done is governed by R2F/R2 producer fuel, not this lease. -/
def writerMaterial (u : BoundedAgentState ψ κ) : Bool :=
  if producerActive u then false
  else decide (u.path3 ≠ none ∨ u.write ≠ .none ∨ u.write_state ≠ .none)


def NoWriterMaterial (u : BoundedAgentState ψ κ) : Prop :=
  u.path3 = none ∧ u.write = .none ∧ u.write_state = .none


def clearWriterRaw (u : BoundedAgentState ψ κ) : BoundedAgentState ψ κ :=
  { u with
    path3 := none
    write_state := .none
    write := .none
    b_carry := false }



@[simp] theorem writerMaterial_clearWriterRaw (u : BoundedAgentState ψ κ) :
    writerMaterial (clearWriterRaw u) = false := by
  simp [writerMaterial, clearWriterRaw, producerActive]


/-- Clear writer fields but preserve the complete R2C quarantine controller. -/
def clearWriterPhys (u : R2Coherence.Cell ψ κ τ) :
    R2Coherence.Cell ψ κ τ :=
  { u with
    phys := { u.phys with
      base := { u.phys.base with
        core := { u.phys.base.core with
          core := clearWriterRaw u.phys.base.core.core } } } }


@[simp] theorem coherenceRaw_clearWriterPhys
    (u : R2Coherence.Cell ψ κ τ) :
    R2Coherence.raw (clearWriterPhys u) =
      clearWriterRaw (R2Coherence.raw u) := by
  rfl


@[simp] theorem clearWriterPhys_bit (u : R2Coherence.Cell ψ κ τ) :
    (R2Coherence.raw (clearWriterPhys u)).bit =
      (R2Coherence.raw u).bit := by
  rfl


@[simp] theorem clearWriterPhys_leader (u : R2Coherence.Cell ψ κ τ) :
    (R2Coherence.raw (clearWriterPhys u)).leader =
      (R2Coherence.raw u).leader := by
  rfl


@[simp] theorem clearWriterPhys_label (u : R2Coherence.Cell ψ κ τ) :
    (R2Coherence.raw (clearWriterPhys u)).label =
      (R2Coherence.raw u).label := by
  rfl


def installPhys (u : Cell ψ κ τ) (p : R2Coherence.Cell ψ κ τ) :
    Cell ψ κ τ :=
  { u with phys := p }


/-- Physical premises already used by the B6/B7/R2C agreement lane.
Lease metadata is deliberately absent. -/
def AgreementCell (u : Cell ψ κ τ) : Prop :=
  R2Coherence.OpenControl u.phys ∧
    (raw u).leader = false ∧ NoWriterMaterial (raw u)


def AgreementPair (l r : Cell ψ κ τ) : Prop :=
  AgreementCell l ∧ AgreementCell r


private instance noWriterMaterialDecidable
    (u : BoundedAgentState ψ κ) : Decidable (NoWriterMaterial u) := by
  unfold NoWriterMaterial
  infer_instance

private instance agreementCellDecidable
    (u : Cell ψ κ τ) : Decidable (AgreementCell u) := by
  unfold AgreementCell R2Coherence.OpenControl NoWriterMaterial
  infer_instance

private instance agreementPairDecidable
    (l r : Cell ψ κ τ) : Decidable (AgreementPair l r) := by
  unfold AgreementPair
  infer_instance

def scrubCell (u : Cell ψ κ τ) : Cell ψ κ τ :=
  if hm : writerMaterial (raw u) = true then
    if hz : u.lease.val = 0 then
      { u with
        phys := clearWriterPhys u.phys
        lease := zeroLease ψ
        trusted := false
        allowBirth := false
        tainted := true }
    else
      { u with
        lease := decLease u.lease (Nat.pos_of_ne_zero hz)
        trusted := false
        allowBirth := false
        tainted := true }
  else
    { u with
      lease := zeroLease ψ
      trusted := false
      allowBirth := false }



def scrubRow (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  (scrubCell l, scrubCell r)


def WriterCleanCell (u : Cell ψ κ τ) : Prop :=
  writerMaterial (raw u) = false ∧ u.lease.val = 0 ∧ u.trusted = false


def WriterClean (C : FC n ψ κ τ) : Prop :=
  ∀ i, WriterCleanCell (C i)


/-- Payload identity: flag may change, source label/bit may not. -/
def sameWriterIdentity
    (a b : BoundedAgentState ψ κ) : Prop :=
  match a.path3, b.path3 with
  | some p, some q => p.label = q.label ∧ p.bit = q.bit
  | _, _ => False


def writerStutter (a b : BoundedAgentState ψ κ) : Prop :=
  a.path3 = b.path3 ∧ a.write_state = b.write_state ∧ a.write = b.write


def localProgress (a b : BoundedAgentState ψ κ) : Prop :=
  sameWriterIdentity a b ∧
    (a.path3 ≠ b.path3 ∨ a.write_state ≠ b.write_state ∨
      a.write ≠ b.write ∨ a.bit ≠ b.bit)


def path3Born (a b : BoundedAgentState ψ κ) : Prop :=
  a.path3 = none ∧ b.path3 ≠ none


def producerReleased (a b : BoundedAgentState ψ κ) : Prop :=
  a.write_state = .done ∧ b.write_state = .depart ∧
    sameWriterIdentity a b


def movedRight (l r ql qr : BoundedAgentState ψ κ) : Prop :=
  l.path3 ≠ none ∧ r.path3 = none ∧
    ql.path3 = none ∧ qr.path3 = l.path3


private instance sameWriterIdentityDecidable
    (a b : BoundedAgentState ψ κ) : Decidable (sameWriterIdentity a b) := by
  unfold sameWriterIdentity
  cases ha : a.path3 <;> cases hb : b.path3 <;> infer_instance

private instance writerStutterDecidable
    (a b : BoundedAgentState ψ κ) : Decidable (writerStutter a b) := by
  unfold writerStutter
  infer_instance

private instance localProgressDecidable
    (a b : BoundedAgentState ψ κ) : Decidable (localProgress a b) := by
  unfold localProgress
  infer_instance

private instance path3BornDecidable
    (a b : BoundedAgentState ψ κ) : Decidable (path3Born a b) := by
  unfold path3Born
  infer_instance

private instance producerReleasedDecidable
    (a b : BoundedAgentState ψ κ) : Decidable (producerReleased a b) := by
  unfold producerReleased
  infer_instance

private instance movedRightDecidable
    (l r ql qr : BoundedAgentState ψ κ) : Decidable (movedRight l r ql qr) := by
  unfold movedRight
  infer_instance

def abortOut (old : Cell ψ κ τ) (out : R2Coherence.Cell ψ κ τ) :
    Cell ψ κ τ :=
  { old with
    phys := R2Coherence.startClosing (clearWriterPhys out)
    lease := zeroLease ψ
    trusted := false
    allowBirth := false
    tainted := true }



def abortInput (u : Cell ψ κ τ) : Cell ψ κ τ := abortOut u u.phys


/-- Any untrusted live consumer, or trusted live consumer at age zero,
is killed before it can execute another writer action. -/
def preAbort (u : Cell ψ κ τ) : Bool :=
  writerMaterial (raw u) &&
    ((!u.trusted) || decide (u.lease.val = 0))


def postOne (old : Cell ψ κ τ) (out : R2Coherence.Cell ψ κ τ) :
    Cell ψ κ τ :=
  let a := raw old
  let b := R2Coherence.raw out
  if writerMaterial b = false then
    { old with
      phys := out
      lease := zeroLease ψ
      trusted := false }
  else if old.allowBirth && decide (path3Born a b ∨ producerReleased a b) then
    { old with
      phys := out
      lease := freshLease ψ
      trusted := true }
  else if old.trusted then
    if decide (localProgress a b) then
      { old with
        phys := out
        lease := freshLease ψ
        trusted := true }
    else if decide (writerStutter a b) then
      { old with phys := out }
    else
      abortOut old out
  else
    abortOut old out



def reseal (u : Cell ψ κ τ) : Cell ψ κ τ :=
  { u with phys := R2Coherence.setControl u.phys .sealed .none }


/-- Exact local release-launch guard of R2C, plus its mark/token context. -/
def releaseLaunchB (l r : Cell ψ κ τ) : Bool :=
  decide (l.phys.ctl.mark = .sealed ∧ l.phys.ctl.tok = .none ∧
    r.phys.ctl.mark = .sealed ∧ r.phys.ctl.tok = .none) &&
  R2Coherence.atRootB l.phys && R2Coherence.successorB l.phys r.phys &&
  R2Coherence.writerQuiet l.phys && R2Coherence.writerQuiet r.phys


/-- A tainted group cannot traverse release/reopen. -/
def taintMaintenanceB (l r : Cell ψ κ τ) : Bool :=
  (decide (l.phys.ctl.tok = .release) ||
    decide (r.phys.ctl.tok = .reopen)) && (l.tainted || r.tainted)


def runRow (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if preAbort l then (abortInput l, r)
  else if preAbort r then (l, abortInput r)
  else if taintMaintenanceB l r then (reseal l, reseal r)
  else if releaseLaunchB l r && (l.tainted || r.tainted) then (l, r)
  else
    let q := R2Coherence.row hψ (by decide : 0 < 2) h2 l.phys r.phys
    if hmove : movedRight (raw l) (raw r)
        (R2Coherence.raw q.1) (R2Coherence.raw q.2) then
      if l.trusted && !r.tainted && !(writerMaterial (raw r)) then
        let l' : Cell ψ κ τ :=
          { l with
            phys := q.1
            lease := zeroLease ψ
            trusted := false }
        let r' : Cell ψ κ τ :=
          { r with
            phys := q.2
            lease := freshLease ψ
            trusted := true }
        (l', r')
      else
        (postOne l q.1, postOne r q.2)
    else
      (postOne l q.1, postOne r q.2)



/-- Clean leaderless/open writer-idle pairs bypass all lease metadata and
execute exactly the current R2Coherence row. -/
def row (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  if hAgree : AgreementPair l r then
    let q := R2Coherence.row hψ (by decide : 0 < 2) h2 l.phys r.phys
    (installPhys l q.1, installPhys r q.2)
  else
    match l.mode, r.mode with
    | .scrub, .scrub => scrubRow l r
    | .run, .run => runRow hψ h2 l r
    | _, _ => (l, r)


/-- Release readiness is strengthened exactly by ¬tainted. -/
def ReleaseReady (u : Cell ψ κ τ) : Prop :=
  R2Coherence.writerQuiet u.phys = true ∧ u.tainted = false


theorem tainted_not_releaseReady (u : Cell ψ κ τ)
    (h : u.tainted = true) : ¬ ReleaseReady u := by
  intro hr
  have hf : true = false := by
    simpa [h] using hr.2
  exact Bool.noConfusion hf



/-- Expiry/abort itself is not a resident-bit write. -/
theorem lease_expiry_bit_frame
    (u : Cell ψ κ τ) : (raw (abortInput u)).bit = (raw u).bit := by
  rfl


end R2WriterLease


namespace R2WriterLease


open BirthTwoStageEscape


variable {n ψ κ τ : Nat}


/-- The wrapper's ordinary protocol. -/
def protocol (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := Cell ψ κ τ
  Y := Bool
  transition := row hψ h2
  output := fun u => (raw u).leader


def step (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (protocol hψ h2 κ τ).step ring C e


def project (C : FC n ψ κ τ) : R2Coherence.FC n ψ κ τ :=
  fun i => (C i).phys


theorem row_phys_eq_coherence_of_agreementPair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) (h : AgreementPair l r) :
    let q := row hψ h2 l r
    (q.1.phys, q.2.phys) =
      R2Coherence.row hψ (by decide : 0 < 2) h2 l.phys r.phys := by
  simp [row, h, installPhys]



private def pairStep {X : Type} (T : X → X → X × X)
    (ring : DirectedRing n) (C : Fin n → X) (e : Fin n) : Fin n → X :=
  let j := ring.rightNeighbor e
  let q := T (C e) (C j)
  fun k => if k = e then q.1 else if k = j then q.2 else C k


private theorem pairStep_project {X Y : Type}
    (f : X → Y) (T : X → X → X × X) (U : Y → Y → Y × Y)
    (ring : DirectedRing n) (C : Fin n → X) (e : Fin n)
    (hpair :
      let p := T (C e) (C (ring.rightNeighbor e))
      let q := U (f (C e)) (f (C (ring.rightNeighbor e)))
      f p.1 = q.1 ∧ f p.2 = q.2) :
    (fun k => f (pairStep T ring C e k)) =
      pairStep U ring (fun k => f (C k)) e := by
  dsimp only at hpair
  rcases hpair with ⟨hL, hR⟩
  funext k
  by_cases hke : k = e
  · subst k
    simp [pairStep, hL]
  · by_cases hkr : k = ring.rightNeighbor e
    · subst k
      simp [pairStep, hke, hR]
    · simp [pairStep, hke, hkr]


private theorem step_eq_pairStep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    step hψ h2 ring C e =
      pairStep (row hψ h2) ring C e := by
  rfl


private theorem coherence_step_eq_pairStep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2Coherence.FC n ψ κ τ) (e : Fin n) :
    R2Coherence.step hψ h2 ring C e =
      pairStep (R2Coherence.row hψ (by decide : 0 < 2) h2) ring C e := by
  rfl


/-- Exactly the physical leaderless/no-writer agreement domain; metadata
mode/trust/lease/taint/allowBirth are unrestricted. -/
def AgreementConfig (C : FC n ψ κ τ) : Prop :=
  ∀ i : Fin n, AgreementCell (C i)


theorem project_step_eq_coherence
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hC : AgreementConfig C) :
    project (step hψ h2 ring C e) =
      R2Coherence.step hψ h2 ring (project C) e := by
  have hp := row_phys_eq_coherence_of_agreementPair
    (κ := κ) (τ := τ) hψ h2
    (C e) (C (ring.rightNeighbor e)) ⟨hC e, hC (ring.rightNeighbor e)⟩
  have hpair :
      let p := row hψ h2 (C e) (C (ring.rightNeighbor e))
      let q := R2Coherence.row hψ (by decide : 0 < 2) h2
        (project C e) (project C (ring.rightNeighbor e))
      p.1.phys = q.1 ∧ p.2.phys = q.2 := by
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  rw [step_eq_pairStep hψ h2 ring C e,
    coherence_step_eq_pairStep hψ h2 ring (project C) e]
  change
    (fun k => (pairStep (row hψ h2) ring C e k).phys) =
      pairStep (R2Coherence.row hψ (by decide : 0 < 2) h2)
        ring (project C) e
  exact pairStep_project (fun u : Cell ψ κ τ => u.phys)
    (row hψ h2)
    (R2Coherence.row hψ (by decide : 0 < 2) h2) ring C e hpair


theorem postOne_trusted_progress_fresh
    (old : Cell ψ κ τ) (out : R2Coherence.Cell ψ κ τ)
    (hmat : writerMaterial (R2Coherence.raw out) = true)
    (hborn :
      (old.allowBirth && decide
        (path3Born (raw old) (R2Coherence.raw out) ∨
          producerReleased (raw old) (R2Coherence.raw out))) = false)
    (htrust : old.trusted = true)
    (hprog : decide (localProgress (raw old) (R2Coherence.raw out)) = true) :
    (postOne old out).lease = freshLease ψ ∧
      (postOne old out).trusted = true := by
  cases ha : old.allowBirth with
  | false =>
      simp [postOne, hmat, ha, htrust, hprog]
  | true =>
      have hb :
          decide
            (path3Born (raw old) (R2Coherence.raw out) ∨
              producerReleased (raw old) (R2Coherence.raw out)) = false := by
        simpa [ha] using hborn
      simp [postOne, hmat, ha, hb, htrust, hprog]



theorem postOne_trusted_stutter_keeps_lease
    (old : Cell ψ κ τ) (out : R2Coherence.Cell ψ κ τ)
    (hmat : writerMaterial (R2Coherence.raw out) = true)
    (hborn :
      (old.allowBirth && decide
        (path3Born (raw old) (R2Coherence.raw out) ∨
          producerReleased (raw old) (R2Coherence.raw out))) = false)
    (htrust : old.trusted = true)
    (hprog : decide (localProgress (raw old) (R2Coherence.raw out)) = false)
    (hstut : decide (writerStutter (raw old) (R2Coherence.raw out)) = true) :
    (postOne old out).lease = old.lease ∧
      (postOne old out).trusted = true := by
  cases ha : old.allowBirth with
  | false =>
      simp [postOne, hmat, ha, htrust, hprog, hstut]
  | true =>
      have hb :
          decide
            (path3Born (raw old) (R2Coherence.raw out) ∨
              producerReleased (raw old) (R2Coherence.raw out)) = false := by
        simpa [ha] using hborn
      simp [postOne, hmat, ha, hb, htrust, hprog, hstut]



inductive AuthEvent where
  | stutter
  | progress
  deriving DecidableEq, Repr


def authLeaseStep (a : Lease ψ) : AuthEvent → Lease ψ
  | .stutter => a
  | .progress => freshLease ψ


def authLeaseRun (es : List AuthEvent) : Lease ψ :=
  es.foldl authLeaseStep (freshLease ψ)


theorem authLeaseRun_fresh (es : List AuthEvent) :
    authLeaseRun (ψ := ψ) es = freshLease ψ := by
  unfold authLeaseRun
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.foldl_cons]
      cases e <;> simpa [authLeaseStep] using ih



theorem authenticatedCanonicalEpisode_never_expires
    (hψ : 0 < ψ) (es : List AuthEvent)
    (_hlen : es.length ≤ leaseCap ψ) :
    (authLeaseRun (ψ := ψ) es).val = leaseCap ψ ∧
      0 < (authLeaseRun (ψ := ψ) es).val := by
  rw [authLeaseRun_fresh]
  constructor
  · exact freshLease_val ψ
  · rw [freshLease_val]
    simpa [leaseCap] using Nat.mul_pos (by decide : 0 < 8) hψ



/-- Local scrub mass: final zero-age deletion opportunity is charged by +1. -/
def scrubMassOne (u : Cell ψ κ τ) : Nat :=
  if writerMaterial (raw u) then u.lease.val + 1 else 0


def scrubPairMass (l r : Cell ψ κ τ) : Nat :=
  scrubMassOne l + scrubMassOne r


def scrubMass (C : FC n ψ κ τ) : Nat :=
  (List.ofFn fun i => scrubMassOne (C i)).foldl (· + ·) 0


theorem scrubCell_lease_lt_of_material_pos
    (u : Cell ψ κ τ)
    (hm : writerMaterial (raw u) = true) (hp : 0 < u.lease.val) :
    (scrubCell u).lease.val < u.lease.val := by
  have hz : u.lease.val ≠ 0 := Nat.ne_of_gt hp
  simp [scrubCell, hm, hz]
  omega



theorem scrubCell_clears_of_material_zero
    (u : Cell ψ κ τ)
    (hm : writerMaterial (raw u) = true) (hz : u.lease.val = 0) :
    NoWriterMaterial (raw (scrubCell u)) ∧
      (scrubCell u).lease.val = 0 := by
  have hs : scrubCell u =
      { u with
        phys := clearWriterPhys u.phys
        lease := zeroLease ψ
        trusted := false
        allowBirth := false
        tainted := true } := by
    simp [scrubCell, hm, hz]
  rw [hs]
  constructor
  · change NoWriterMaterial (R2Coherence.raw (clearWriterPhys u.phys))
    rw [coherenceRaw_clearWriterPhys]
    simp [NoWriterMaterial, clearWriterRaw]
  · exact zeroLease_val ψ



/-- `scrubCell` keeps the physical field unless it clears expired material. -/
theorem scrubCell_raw (u : Cell ψ κ τ)
    (h : writerMaterial (raw u) = false ∨ ¬ u.lease.val = 0) :
    raw (scrubCell u) = raw u := by
  unfold scrubCell
  by_cases hm : writerMaterial (raw u) = true
  · have hz : ¬ u.lease.val = 0 := by
      rcases h with h | h
      · rw [hm] at h
        cases h
      · exact h
    rw [dif_pos hm, dif_neg hz]
    rfl
  · rw [dif_neg hm]
    rfl

theorem scrubMassOne_lt_of_material
    (u : Cell ψ κ τ) (hm : writerMaterial (raw u) = true) :
    scrubMassOne (scrubCell u) < scrubMassOne u := by
  by_cases hz : u.lease.val = 0
  · have hc := scrubCell_clears_of_material_zero u hm hz
    have hout : writerMaterial (raw (scrubCell u)) = false := by
      rcases hc.1 with ⟨hp3, hw, hs⟩
      simp [writerMaterial, hp3, hw, hs,
        WriterProducerRepair.producerActive]
    simp [scrubMassOne, hm, hout, hz]
  · have hp : 0 < u.lease.val := Nat.pos_of_ne_zero hz
    have hl := scrubCell_lease_lt_of_material_pos u hm hp
    have hraw : raw (scrubCell u) = raw u := scrubCell_raw u (Or.inr hz)
    simp [scrubMassOne, hraw, hm]
    omega



theorem scrubMassOne_le (u : Cell ψ κ τ) :
    scrubMassOne (scrubCell u) ≤ scrubMassOne u := by
  cases hm : writerMaterial (raw u) with
  | false =>
      have hraw : raw (scrubCell u) = raw u := scrubCell_raw u (Or.inl hm)
      simp [scrubMassOne, hraw, hm]
  | true =>
      exact Nat.le_of_lt (scrubMassOne_lt_of_material u hm)



theorem scrubRow_pairMass_lt_of_material
    (l r : Cell ψ κ τ)
    (h : writerMaterial (raw l) = true ∨ writerMaterial (raw r) = true) :
    scrubPairMass (scrubRow l r).1 (scrubRow l r).2 <
      scrubPairMass l r := by
  rcases h with hl | hr
  · have hL := scrubMassOne_lt_of_material l hl
    have hR := scrubMassOne_le r
    dsimp [scrubRow, scrubPairMass]
    omega
  · have hL := scrubMassOne_le l
    have hR := scrubMassOne_lt_of_material r hr
    dsimp [scrubRow, scrubPairMass]
    omega



/-- Pure scrub protocol used for the preparation-mass statement. -/
def scrubProtocol (ψ κ τ : Nat) : PopulationProtocol where
  Q := Cell ψ κ τ
  Y := Bool
  transition := scrubRow
  output := fun u => (raw u).leader


def scrubStep (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (scrubProtocol ψ κ τ).step ring C e


def scrubQ : Nat := 2


def scrubB (n ψ : Nat) : Nat :=
  4 * n * n * (leaseCap ψ + 1)


/-- Exact Q=2, B=4n²(8ψ+1) finite-word target. -/
noncomputable def ScrubHalfMassObligation (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    scrubQ * avoidCount (scrubStep ring) (fun _ => True) WriterClean
      C (scrubB n ψ) ≤
    (scrubQ - 1) * n ^ (scrubB n ψ)


theorem writerScrub_half_mass
    (ring : DirectedRing n)
    (h : ScrubHalfMassObligation (ψ := ψ) (κ := κ) (τ := τ) ring)
    (C : FC n ψ κ τ) :
    2 * avoidCount (scrubStep ring) (fun _ => True) WriterClean
      C (scrubB n ψ) ≤ n ^ (scrubB n ψ) := by
  have hc := h C
  simpa [scrubQ] using hc


end R2WriterLease
