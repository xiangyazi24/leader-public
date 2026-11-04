import Leader.Wu.Entrance.CheckWriteStateFrame
import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Entrance.LocalReverseFill

set_option autoImplicit false
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalEntryCut BirthShortDoneCuts
  K2BirthDispatcher K2BirthLeaderNormalize

namespace WriterProducerRepair
variable {ψ κ : Nat}
abbrev Credit (ψ : Nat) := Fin (4 * ψ + 1)
structure WCell (ψ κ : Nat) where
  agent : AuthorizedBoundedAgentState ψ κ
  fuel : Credit ψ

def producerActive (u : BoundedAgentState ψ κ) : Bool :=
  decide (u.write_state = .produce ∨ u.write_state = .done)

def producerStarts (u : BoundedAgentState ψ κ) : Bool :=
  u.leader && u.gen_ws && !(producerActive u) &&
    decide (u.label.val = 0 ∧ u.path3 = none)

def put (u : WCell ψ κ) (b : BoundedAgentState ψ κ) : WCell ψ κ :=
  { u with agent := ⟨b, reconcilePermit u.agent.erase b.erase⟩ }

def idleFuel (u : WCell ψ κ) : WCell ψ κ :=
  if producerActive u.agent.core then u else { u with fuel := 0 }

-- One tick per participating endpoint, INCLUDING metadata-priority bypasses.
-- At zero, discard the unfinished producer payload, not the main CHECK path.
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
        fuel := ⟨u.fuel.val - 1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) u.fuel.isLt⟩ }
  else
    { u with fuel := 0 }


-- Store the OLD bit, then perform this component's carry operation.
def mint (u : WCell ψ κ) (carry : Bool) : WCell ψ κ :=
  let b := u.agent.core
  put u { b with
    path3 := some { label := b.label, bit := if b.bit then 1 else 0, flag := 1 }
    write_state := .done, write := .none
    bit := if carry then !b.bit else b.bit
    b_carry := carry && b.bit }

def ackReady (u : BoundedAgentState ψ κ) : Bool :=
  decide (u.write_state = .done) &&
    (match u.path3 with
     | none => false
     | some p => decide (p.label = u.label ∧ p.flag = 1))

-- Inputs have already spent this service's credit. Only root initiation refills.
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
      { v with fuel := ⟨4 * ψ, Nat.lt_succ_self _⟩ }
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
end WriterProducerRepair

namespace R2
open WriterProducerRepair
variable {ψ κ τ width n : Nat}
structure Cell (ψ κ τ : Nat) where
  base : ExpiringAgentState ψ κ τ
  fuel : Credit ψ
abbrev FC (n ψ κ τ : Nat) := Fin n → Cell ψ κ τ

def ofAuth (u : AuthorizedAgentState ψ)
    (h : u.core.inProtocolDomain κ) : AuthorizedBoundedAgentState ψ κ :=
  ⟨BoundedAgentState.ofDomain u.core h, u.path0Crossed⟩

-- Same R1 cuts through CHECK, permitFix, DISAPPEAR/COMPARE/SUPPRESS.
section Q13267OrdinaryCuts
set_option Elab.async false

attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.permitFix
  BirthShortDoneCuts.beforeWriteWidth
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
  WriterProducerRepair.stationaryProducerRow

private def q13267_checkedBounded
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
  let hq := doneThroughCheckEntryWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2.ofAuth q.1 hq.1, R2.ofAuth q.2 hq.2)

private def q13267_permitBounded (u : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ :=
  let f : AuthorizedAgentState ψ := BirthCheckPermitRepair.permitFix u.erase
  let hf : f.core.inProtocolDomain κ := by
    change (BirthCheckPermitRepair.permitFix u.erase).core.inProtocolDomain κ
    rw [BirthCheckPermitRepair.permitFix_core]
    exact u.core.erase_inProtocolDomain
  R2.ofAuth f hf

private def q13267_beforeWriterBounded
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    beforeWriteWidth hψ hw hle l.erase r.erase
  let hq := beforeWriteWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2.ofAuth q.1 hq.1, R2.ofAuth q.2 hq.2)

private def q13267_markBounded
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
  (R2.ofAuth m.1 hm.1, R2.ofAuth m.2 hm.2)

def ordinary (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  let c : AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
    q13267_checkedBounded hψ hw hle l.agent r.agent
  let f : AuthorizedBoundedAgentState ψ κ := q13267_permitBounded c.1
  let p : AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
    q13267_beforeWriterBounded hψ hw hle f c.2
  let z : WCell ψ κ × WCell ψ κ :=
    WriterProducerRepair.stationaryProducerRow hψ
      ⟨p.1, l.fuel⟩ ⟨p.2, r.fuel⟩
  let m : AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
    q13267_markBounded l.agent r.agent z.1.agent z.2.agent
  (⟨m.1, z.1.fuel⟩, ⟨m.2, z.2.fuel⟩)

end Q13267OrdinaryCuts

section Q13267CutEquations

attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.permitFix
  BirthShortDoneCuts.beforeWriteWidth
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
  WriterProducerRepair.stationaryProducerRow


theorem q13267_checkedBounded_writeState
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let c := q13267_checkedBounded hψ hw hle l r
    c.1.core.write_state = l.core.write_state ∧
      c.2.core.write_state = r.core.write_state := by
  have h :=
    B6CheckWriteStateFrame.doneThroughCheckEntryWidth_writeState_frame
      hψ hw hle κ l.erase r.erase
  unfold q13267_checkedBounded
  dsimp only
  simpa only [R2.ofAuth, BoundedAgentState.ofDomain,
    AuthorizedBoundedAgentState.erase, BoundedAgentState.erase] using h


theorem q13267_checkedBounded_mainTriple
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
    let c := q13267_checkedBounded hψ hw hle l r
    (c.1.erase.core.state, c.1.erase.core.path, c.1.erase.core.label) =
        (q.1.core.state, q.1.core.path, q.1.core.label) ∧
      (c.2.erase.core.state, c.2.erase.core.path, c.2.erase.core.label) =
        (q.2.core.state, q.2.core.path, q.2.core.label) := by
  dsimp only
  constructor
  · simp only [q13267_checkedBounded, R2.ofAuth,
      AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]
  · simp only [q13267_checkedBounded, R2.ofAuth,
      AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]


theorem q13267_permitBounded_core
    (u : AuthorizedBoundedAgentState ψ κ) :
    (q13267_permitBounded u).core = u.core := by
  unfold q13267_permitBounded R2.ofAuth
  dsimp only
  apply BoundedAgentState.eraseToDomain_bijective.1
  apply Subtype.ext
  show
    BoundedAgentState.erase
        (BoundedAgentState.ofDomain
          (BirthCheckPermitRepair.permitFix u.erase).core _) =
      BoundedAgentState.erase u.core
  exact
    (BoundedAgentState.erase_ofDomain
      (BirthCheckPermitRepair.permitFix u.erase).core _).trans
      ((BirthCheckPermitRepair.permitFix_core u.erase).trans rfl)

theorem q13267_beforeWriterBounded_core
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      beforeWriteWidth hψ hw hle l.erase r.erase
    let p := q13267_beforeWriterBounded hψ hw hle l r
    p.1.erase.core = q.1.core ∧ p.2.erase.core = q.2.core := by
  dsimp only
  constructor
  · simp only [q13267_beforeWriterBounded, R2.ofAuth,
      AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]
  · simp only [q13267_beforeWriterBounded, R2.ofAuth,
      AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]


theorem q13267_markBounded_core
    (oldL oldR outL outR : AuthorizedBoundedAgentState ψ κ) :
    let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      (outL.erase, outR.erase)
    let born : Bool := authBirth oldL.erase oldR.erase a
    let m : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      markLeaderBirth born a
    let z := q13267_markBounded oldL oldR outL outR
    z.1.erase.core = m.1.core ∧ z.2.erase.core = m.2.core := by
  dsimp only
  constructor
  · simp only [q13267_markBounded, R2.ofAuth,
      AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]
  · simp only [q13267_markBounded, R2.ofAuth,
      AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

end Q13267CutEquations





-- Reuse R1's deletion/hold implementation ONLY on its exact priority gate.
-- Those branches skip the writer, but not the independent producer timer.
def bounded (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  let l0 : AuthorizedAgentState ψ := normalizeDeletion l.agent.erase
  let r0 : AuthorizedAgentState ψ := normalizeDeletion r.agent.erase
  if deletionActive r0 || deletionActive l0 then
    let q := BirthCheckPermitRepair.bounded hψ hw hle l.agent r.agent
    (WriterProducerRepair.tick ⟨q.1, l.fuel⟩,
      WriterProducerRepair.tick ⟨q.2, r.fuel⟩)
  else
    let hl := (cleanup_helpers_inProtocolDomain
      l.agent.erase l.agent.core.erase_inProtocolDomain).1
    let hr := (cleanup_helpers_inProtocolDomain
      r.agent.erase r.agent.core.erase_inProtocolDomain).1
    R2.ordinary hψ hw hle
      ⟨R2.ofAuth l0 hl, l.fuel⟩ ⟨R2.ofAuth r0 hr, r.fuel⟩


-- Original disposal preparation, main expiry, normalization and physical tail.
def row (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : Cell ψ κ τ) : Cell ψ κ τ × Cell ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l.base
  let r0 := prepareExpiringDisposal hψ r.base
  let q := bounded hψ hw hle ⟨l0.core, l.fuel⟩ ⟨r0.core, r.fuel⟩
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
end R2

namespace WriterProducerRegression
variable {ψ : Nat}

def clean (hψ : 0 < ψ) (old : Fin ψ → Bool) (i : Fin ψ) :
    R2.Cell ψ ψ (16 * ψ) :=
  let b : BoundedAgentState ψ ψ := {
    leader := i.val == 0, probe := false, phase := false
    bit := old i, wait := true, state := .none, path := .bot
    reset := false, carry := false, count := 0, label := i, h_field := false
    path2 := none, path3 := none, path4 := none, path5 := none
    p := false, p_carry := false, reset_cmd := false, echo := false
    signal_B := 0, bullet := 0, shield := i.val == 0
    write_state := .none, write := .none, last := false
    last_set := false, last_unset := false, b_carry := false
    gen_ws := i.val == 0, ws_echo := false, signal_ws := false }
  ⟨⟨⟨b, false⟩, 0⟩, 0⟩

def producerWord (hψ : 0 < ψ) : List (Fin ψ) :=
  ((List.range (ψ - 1)) ++ (List.range (ψ - 2)).reverse).map
    (fun k => ⟨k % ψ, Nat.mod_lt _ hψ⟩)

def incrementBit (old : Fin ψ → Bool) (i : Fin ψ) : Bool :=
  let carry := (List.finRange ψ).all
    (fun j => if i.val < j.val then old j else true)
  if carry then !(old i) else old i

abbrev Produced (old : Fin ψ → Bool) (C : R2.FC ψ ψ ψ (16 * ψ)) : Prop :=
  ∀ i : Fin ψ, let u := (C i).base.core.core
    u.path3 = some { label := i, bit := if old i then 1 else 0, flag := 1 } ∧
    u.bit = incrementBit old i ∧ u.label = i ∧
    u.leader = (i.val == 0) ∧ u.write_state = .depart ∧
    u.write = .none ∧ u.b_carry = false ∧ u.gen_ws = false ∧ (C i).fuel = 0

def run (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (old : Fin ψ → Bool)
    (w : List (Fin ψ)) : R2.FC ψ ψ ψ (16 * ψ) :=
  w.foldl (R2.step hψ h2 (⟨hψ⟩ : DirectedRing ψ)) (clean hψ old)

/- INFERENCE: exact regression targets, to prove rather than assume.
theorem producerWord_length (hψ : 0 < ψ) (h3 : 3 ≤ ψ) :
    (producerWord hψ).length = 2 * ψ - 3

theorem producer_general (hψ : 0 < ψ) (h3 : 3 ≤ ψ)
    (old : Fin ψ → Bool) :
    Produced old (run hψ (by omega) old (producerWord hψ))

theorem producer000 :
    let C := run (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (fun _ => false) ([0, 1, 0] : List (Fin 3))
    Produced (fun _ => false) C ∧
      (C 0).base.core.core.bit = false ∧
      (C 1).base.core.core.bit = false ∧
      (C 2).base.core.core.bit = true
-/
end WriterProducerRegression

namespace R2
open BirthTwoStageEscape
variable {n ψ κ τ : Nat}
def Leaderless (C : FC n ψ κ τ) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless (fun i => (C i).base)
def NoProducer (C : FC n ψ κ τ) : Prop :=
  ∀ i, WriterProducerRepair.producerActive (C i).base.core.core = false

def producerWeight (u : Cell ψ κ τ) : Nat :=
  if WriterProducerRepair.producerActive u.base.core.core then
    3 ^ (u.fuel.val + 1) else 0

def producerPotential (C : FC n ψ κ τ) : Nat :=
  ((List.finRange n).map (fun i => producerWeight (C i))).sum

def producerRecoveryB (n ψ : Nat) : Nat :=
  3 * n * (Nat.log2 (n * 3 ^ (4 * ψ + 1)) + 2)

/- INFERENCE: exact recovery/agreement targets for the included implementation.
theorem producer_recovery (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : FC n ψ κ τ) (hC : Leaderless C) :
    2 * avoidCount (step hψ h2 ring) Leaderless NoProducer
        C (producerRecoveryB n ψ) ≤ n ^ (producerRecoveryB n ψ)

theorem step_agrees_of_noProducer (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hC : Leaderless C) (hP : NoProducer C) (e : Fin n) :
    (fun i => (step hψ h2 ring C e i).base) =
      BirthCheckPermitRepairLeaf.step1 hψ h2 ring (fun i => (C i).base) e

theorem noProducer_next (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hC : Leaderless C) (hP : NoProducer C) (e : Fin n) :
    NoProducer (step hψ h2 ring C e)
-/
end R2
-- These are additional certificates, not replacements for clean/run/Produced.
deriving instance DecidableEq for R2.Cell

namespace WriterProducerRegression
section Q13267Certificates
set_option Elab.async false
set_option synthInstance.maxSize 4096

private abbrev Q13267Cfg := R2.FC 3 3 3 48

private def q13267_source (lastBit : Bool) : Fin 3 → Bool :=
  if lastBit then (fun i => i.val == 2) else (fun _ => false)

private def q13267_seed (lastBit : Bool) : Q13267Cfg :=
  clean (by decide : 0 < 3) (q13267_source lastBit)

private def q13267_step : Q13267Cfg → Fin 3 → Q13267Cfg :=
  R2.step (by decide : 0 < 3) (by decide : 2 ≤ 3)
    (⟨by decide⟩ : DirectedRing 3)

private def q13267_payload (lab : Fin 3) (b : Bool) :
    Option (BoundedPath3Info 3) :=
  some { label := lab, bit := if b then 1 else 0, flag := 1 }

-- A complete record template with NO call to any transition.
private def q13267_literal (lastBit : Bool) (i : Fin 3)
    (bit : Bool := q13267_source lastBit i)
    (ws : WriteState := .none)
    (p3 : Option (BoundedPath3Info 3) := none)
    (fuel : WriterProducerRepair.Credit 3 := 0)
    (stall : Fin 49 := 0)
    (h : Bool := false) (resetCmd : Bool := false)
    (echo : Bool := false) (signal : Fin 2 := 0)
    (gen : Bool := i.val == 0) : R2.Cell 3 3 48 :=
  let original := q13267_seed lastBit i
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

-- After edge 0: both producer phases are produce with credit 12.
private def q13267_c1 (lastBit : Bool) : Q13267Cfg := fun i =>
  match i.val with
  | 0 => q13267_literal lastBit 0
      (ws := .produce) (fuel := 12) (stall := 48) (h := true)
  | 1 => q13267_literal lastBit 1
      (ws := .produce) (fuel := 12) (stall := 48)
      (resetCmd := true) (signal := 1)
  | _ => q13267_seed lastBit 2

-- After edge 1: terminal minted/released; label 1 holds the done ACK.
-- For old 001 the terminal carry has already changed cell 1 to true.
private def q13267_c2 (lastBit : Bool) : Q13267Cfg := fun i =>
  match i.val with
  | 0 => q13267_c1 lastBit 0
  | 1 => q13267_literal lastBit 1
      (bit := lastBit) (ws := .done) (p3 := q13267_payload 1 false)
      (fuel := 11) (stall := 47) (echo := true) (signal := 1)
  | _ => q13267_literal lastBit 2
      (bit := !lastBit) (ws := .depart)
      (p3 := q13267_payload 2 lastBit) (stall := 48)
      (resetCmd := true) (signal := 1)

-- After the final edge 0: root minted; all producer credits are zero.
-- SUPPRESS has also consumed cell 1's echo/reset pair on this service.
private def q13267_c3 (lastBit : Bool) : Q13267Cfg := fun i =>
  match i.val with
  | 0 => q13267_literal lastBit 0
      (ws := .depart) (p3 := q13267_payload 0 false)
      (stall := 47) (gen := false)
  | 1 => q13267_literal lastBit 1
      (bit := lastBit) (ws := .depart) (p3 := q13267_payload 1 false)
      (stall := 46) (h := true) (signal := 1)
  | _ => q13267_c2 lastBit 2

-- Each goal is closed and checks ONE service on literal input records.
private theorem q13267_000_s1 : ∀ i : Fin 3,
    q13267_step (q13267_seed false) 0 i = q13267_c1 false i := by
  decide +kernel

private theorem q13267_000_s2 : ∀ i : Fin 3,
    q13267_step (q13267_c1 false) 1 i = q13267_c2 false i := by
  decide +kernel

private theorem q13267_000_s3 : ∀ i : Fin 3,
    q13267_step (q13267_c2 false) 0 i = q13267_c3 false i := by
  decide +kernel

private theorem q13267_001_s1 : ∀ i : Fin 3,
    q13267_step (q13267_seed true) 0 i = q13267_c1 true i := by
  decide +kernel

private theorem q13267_001_s2 : ∀ i : Fin 3,
    q13267_step (q13267_c1 true) 1 i = q13267_c2 true i := by
  decide +kernel

private theorem q13267_001_s3 : ∀ i : Fin 3,
    q13267_step (q13267_c2 true) 0 i = q13267_c3 true i := by
  decide +kernel

private theorem q13267_s1 (lastBit : Bool) :
    q13267_step (q13267_seed lastBit) 0 = q13267_c1 lastBit := by
  cases lastBit with
  | false => exact funext q13267_000_s1
  | true => exact funext q13267_001_s1

private theorem q13267_s2 (lastBit : Bool) :
    q13267_step (q13267_c1 lastBit) 1 = q13267_c2 lastBit := by
  cases lastBit with
  | false => exact funext q13267_000_s2
  | true => exact funext q13267_001_s2

private theorem q13267_s3 (lastBit : Bool) :
    q13267_step (q13267_c2 lastBit) 0 = q13267_c3 lastBit := by
  cases lastBit with
  | false => exact funext q13267_000_s3
  | true => exact funext q13267_001_s3

section Q13267Composition
-- Symbolic composition must not normalize the underlying physical row.
attribute [local irreducible] R2.step R2.row R2.bounded R2.ordinary

private theorem q13267_run_eq (lastBit : Bool) :
    run (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (q13267_source lastBit) ([0, 1, 0] : List (Fin 3)) =
        q13267_c3 lastBit := by
  simp only [run, List.foldl_cons, List.foldl_nil]
  change q13267_step
    (q13267_step (q13267_step (q13267_seed lastBit) 0) 1) 0 =
      q13267_c3 lastBit
  rw [q13267_s1 lastBit, q13267_s2 lastBit, q13267_s3 lastBit]
end Q13267Composition

private abbrev Q13267Result (lastBit : Bool) (C : Q13267Cfg) : Prop :=
  Produced (q13267_source lastBit) C ∧
    (C 0).base.core.core.bit = false ∧
    (C 1).base.core.core.bit = lastBit ∧
    (C 2).base.core.core.bit = !lastBit

-- This checks only literal data and incrementBit, not a protocol run.
private theorem q13267_result_literal (lastBit : Bool) :
    Q13267Result lastBit (q13267_c3 lastBit) := by
  cases lastBit <;> decide +kernel

private theorem q13267_result_run (lastBit : Bool) :
    Q13267Result lastBit
      (run (by decide : 0 < 3) (by decide : 2 ≤ 3)
        (q13267_source lastBit) ([0, 1, 0] : List (Fin 3))) := by
  exact Eq.mpr
    (congrArg (Q13267Result lastBit) (q13267_run_eq lastBit))
    (q13267_result_literal lastBit)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 65536 in
/-- Three actual R2 services: old 000 is retained in flag-one payloads,
while the source bits become 001 and the unique root stays at zero. -/
theorem producer000 :
    let C := run (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (fun _ => false) ([0, 1, 0] : List (Fin 3))
    Produced (fun _ => false) C ∧
      (C 0).base.core.core.bit = false ∧
      (C 1).base.core.core.bit = false ∧
      (C 2).base.core.core.bit = true := by
  exact q13267_result_run false

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 65536 in
/-- The terminal one carries left: old 001 becomes 010, while the
three flag-one payloads still encode 001, not the incremented word. -/
theorem producer001_regression :
    let old : Fin 3 → Bool := fun i => i.val == 2
    let C := run (by decide : 0 < 3) (by decide : 2 ≤ 3)
      old ([0, 1, 0] : List (Fin 3))
    Produced old C ∧
      (C 0).base.core.core.bit = false ∧
      (C 1).base.core.core.bit = true ∧
      (C 2).base.core.core.bit = false := by
  exact q13267_result_run true

end Q13267Certificates
end WriterProducerRegression
