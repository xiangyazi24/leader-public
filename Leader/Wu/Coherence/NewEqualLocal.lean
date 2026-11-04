import Leader.Wu.Coherence.OpenNoHazardFrame

set_option autoImplicit false
set_option Elab.async false

namespace R2NewEqualLocal

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure
open R2CoherenceV31OpenNoHazard

variable {ψ κ τ width : Nat}

/-- Freshness of exactly the component stored at an R2 endpoint's own label. -/
def R2FreshAtOwnLabel (u : R2.Cell ψ κ τ) : Prop :=
  match u.base.core.core.path with
  | .bot => False
  | .some lab b =>
      lab.val = u.base.core.core.label.val ∧
        b.val = (if u.base.core.core.bit then 1 else 0)

/-- The physical fields protected by the V3 open-no-hazard gate.  `state` is
intentionally omitted: CHECK is allowed to change it. -/
def R2MainCarrierFrame
    (l r : R2.Cell ψ κ τ)
    (q : R2.Cell ψ κ τ × R2.Cell ψ κ τ) : Prop :=
  q.1.base.core.core.label = l.base.core.core.label ∧
    q.1.base.core.core.bit = l.base.core.core.bit ∧
    q.1.base.core.core.path = l.base.core.core.path ∧
    q.2.base.core.core.label = r.base.core.core.label ∧
    q.2.base.core.core.bit = r.base.core.core.bit ∧
    q.2.base.core.core.path = r.base.core.core.path

/-- This is the genuinely missing R2-level theorem ... -/
def SanitizedR2NewEqualFreshAtOwnLabelNoMainMutation
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let q := R2.row hψ hw hle
      (sanitizeReadyPhys l) (sanitizeReadyPhys r)
    R2MainCarrierFrame l r q →
      (q.1.base.core.core.state = .equal →
        l.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.1) ∧
      (q.2.base.core.core.state = .equal →
        r.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.2)

/-- Smallest writer export needed ... -/
def StationaryProducerMainComparisonFrame (hψ : 0 < ψ) : Prop :=
  ∀ (l r : WCell ψ κ),
    let q := stationaryProducerRow hψ l r
    q.1.agent.core.state = l.agent.core.state ∧
      q.1.agent.core.path = l.agent.core.path ∧
      q.1.agent.core.label = l.agent.core.label ∧
      q.2.agent.core.state = r.agent.core.state ∧
      q.2.agent.core.path = r.agent.core.path ∧
      q.2.agent.core.label = r.agent.core.label

private theorem boundedPath_eq_of_erase
    (a b : BoundedAgentState ψ κ)
    (h : a.erase.path = b.erase.path) :
    a.path = b.path := by
  cases ha : a.path with
  | bot =>
      cases hb : b.path with
      | bot => rfl
      | some lab bit =>
          have hh : PathInfo.bot = .some lab.val bit.val := by
            simp only [BoundedAgentState.erase, ha, hb] at h
            exact h
          cases hh
  | some la ba =>
      cases hb : b.path with
      | bot =>
          have hh : PathInfo.some la.val ba.val = .bot := by
            simp only [BoundedAgentState.erase, ha, hb] at h
            exact h
          cases hh
      | some lb bb =>
          have hh : PathInfo.some la.val ba.val = .some lb.val bb.val := by
            simp only [BoundedAgentState.erase, ha, hb] at h
            exact h
          have hl : la = lb := Fin.ext (PathInfo.some.inj hh).1
          have hb' : ba = bb := Fin.ext (PathInfo.some.inj hh).2
          cases hl
          cases hb'
          rfl

private def boundedMainView
    (u : AuthorizedBoundedAgentState ψ κ) :
    MainState × BoundedPathInfo ψ × Fin ψ :=
  (u.core.state, u.core.path, u.core.label)

private def writerMainView (u : WCell ψ κ) :
    MainState × BoundedPathInfo ψ × Fin ψ :=
  boundedMainView u.agent

/-- Project a stationary-writer observation only after abstracting its endpoints.
This keeps large row terms out of definitional equality. -/
private theorem swView_mainFields
    (u v : AgentState ψ)
    (h : BirthStationaryWrite.swView u = BirthStationaryWrite.swView v) :
    u.state = v.state ∧ u.path = v.path ∧ u.label = v.label := by
  have hs := congrArg (fun z => z.2.2.2.state) h
  have hp := congrArg (fun z => z.2.2.2.path) h
  have hl := congrArg (fun z => z.2.1) h
  change u.state = v.state at hs
  change u.path = v.path at hp
  change u.label = v.label at hl
  exact ⟨hs, hp, hl⟩

private theorem swPair_fst_eq
    (a b c d : AgentState ψ)
    (h : BirthStationaryWrite.swPair (a, b) =
      BirthStationaryWrite.swPair (c, d)) :
    BirthStationaryWrite.swView a = BirthStationaryWrite.swView c := by
  simpa only [BirthStationaryWrite.swPair] using congrArg Prod.fst h

private theorem swPair_snd_eq
    (a b c d : AgentState ψ)
    (h : BirthStationaryWrite.swPair (a, b) =
      BirthStationaryWrite.swPair (c, d)) :
    BirthStationaryWrite.swView b = BirthStationaryWrite.swView d := by
  simpa only [BirthStationaryWrite.swPair] using congrArg Prod.snd h

private theorem boundedMainView_eq_of_swView
    (a b : AuthorizedBoundedAgentState ψ κ)
    (h : BirthStationaryWrite.swView a.core.erase =
      BirthStationaryWrite.swView b.core.erase) :
    boundedMainView a = boundedMainView b := by
  have hm := swView_mainFields a.core.erase b.core.erase h
  have hs : a.core.state = b.core.state := by
    simpa only [BoundedAgentState.erase] using hm.1
  have hp : a.core.path = b.core.path :=
    boundedPath_eq_of_erase a.core b.core hm.2.1
  have hl : a.core.label = b.core.label := by
    simpa only [BoundedAgentState.erase] using hm.2.2
  unfold boundedMainView
  exact Prod.ext hs (Prod.ext hp hl)

private theorem writerMainView_fields
    (u v : WCell ψ κ) (h : writerMainView u = writerMainView v) :
    u.agent.core.state = v.agent.core.state ∧
      u.agent.core.path = v.agent.core.path ∧
      u.agent.core.label = v.agent.core.label := by
  have hs := congrArg (fun z => z.1) h
  have hp := congrArg (fun z => z.2.1) h
  have hl := congrArg (fun z => z.2.2) h
  change u.agent.core.state = v.agent.core.state at hs
  change u.agent.core.path = v.agent.core.path at hp
  change u.agent.core.label = v.agent.core.label at hl
  exact ⟨hs, hp, hl⟩

private theorem put_mainView
    (u : WCell ψ κ) (b : BoundedAgentState ψ κ)
    (hs : b.state = u.agent.core.state)
    (hp : b.path = u.agent.core.path)
    (hl : b.label = u.agent.core.label) :
    writerMainView (put u b) = writerMainView u := by
  unfold writerMainView boundedMainView WriterProducerRepair.put
  dsimp only
  exact Prod.ext hs (Prod.ext hp hl)

private theorem idleFuel_mainView (u : WCell ψ κ) :
    writerMainView (idleFuel u) = writerMainView u := by
  unfold WriterProducerRepair.idleFuel
  split <;> rfl

private theorem tick_mainView (u : WCell ψ κ) :
    writerMainView (tick u) = writerMainView u := by
  unfold writerMainView boundedMainView WriterProducerRepair.tick
    WriterProducerRepair.put
  dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem mint_mainView (u : WCell ψ κ) (carry : Bool) :
    writerMainView (mint u carry) = writerMainView u := by
  unfold WriterProducerRepair.mint
  dsimp only
  apply put_mainView <;> rfl

/-- The first local `let l := ...` of `producerStep`. -/
private def producerStartLocal (u : WCell ψ κ) : WCell ψ κ :=
  if producerStarts u.agent.core then
    let b := u.agent.core
    let started : BoundedAgentState ψ κ :=
      { b with
        write_state := .produce
        write := .none
        b_carry := false }
    let v : WCell ψ κ := put u started
    { v with fuel := ⟨4 * ψ, Nat.lt_succ_self _⟩ }
  else u

private theorem producerStartLocal_mainView (u : WCell ψ κ) :
    writerMainView (producerStartLocal u) = writerMainView u := by
  unfold producerStartLocal
  split
  · dsimp only
    change writerMainView
      (put u { u.agent.core with
        write_state := .produce
        write := .none
        b_carry := false }) = writerMainView u
    exact put_mainView u _ rfl rfl rfl
  · rfl

/-- The conditional follower-start assignment inside the producer advance. -/
private def producerFollowerStartLocal
    (l r : WCell ψ κ) : WCell ψ κ :=
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

private theorem producerFollowerStartLocal_mainView
    (l r : WCell ψ κ) :
    writerMainView (producerFollowerStartLocal l r) = writerMainView r := by
  unfold producerFollowerStartLocal
  split
  · dsimp only
    change writerMainView
      (put r { r.agent.core with
        write_state := .produce
        write := .none
        b_carry := false }) = writerMainView r
    exact put_mainView r _ rfl rfl rfl
  · rfl

/-- The terminal component mint inside the producer advance. -/
private def producerTailMintLocal (r : WCell ψ κ) : WCell ψ κ :=
  if r.agent.core.write_state = .produce ∧
      r.agent.core.path3 = none ∧
      r.agent.core.label.val + 1 = ψ then
    mint r true
  else r

private theorem producerTailMintLocal_mainView (r : WCell ψ κ) :
    writerMainView (producerTailMintLocal r) = writerMainView r := by
  unfold producerTailMintLocal
  split
  · exact mint_mainView r true
  · rfl

/-- The ACK/release assignment inside the producer advance. -/
private def producerAckLocal
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  if ackReady r.agent.core then
    let b := r.agent.core
    let released : BoundedAgentState ψ κ :=
      { b with
        write_state := .depart
        write := .none
        b_carry := false }
    (mint l r.agent.core.b_carry, put r released)
  else (l, r)

private theorem producerAckLocal_mainView (l r : WCell ψ κ) :
    let q := producerAckLocal l r
    writerMainView q.1 = writerMainView l ∧
      writerMainView q.2 = writerMainView r := by
  unfold producerAckLocal
  split
  · dsimp only
    constructor
    · exact mint_mainView l r.agent.core.b_carry
    · change writerMainView
        (put r { r.agent.core with
          write_state := .depart
          write := .none
          b_carry := false }) = writerMainView r
      exact put_mainView r _ rfl rfl rfl
  · exact ⟨rfl, rfl⟩

/-- The middle `q` computation of `producerStep`, with its two assignments named. -/
private def producerAdvanceLocal
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  if l.agent.core.write_state = .produce ∧
      l.agent.core.path3 = none ∧
      l.agent.core.label.val + 1 = r.agent.core.label.val ∧
      r.agent.core.leader = false ∧
      (l.agent.core.leader = false ∨ l.agent.core.label.val = 0) then
    let r := producerFollowerStartLocal l r
    let r := producerTailMintLocal r
    producerAckLocal l r
  else (l, r)

private theorem producerAdvanceLocal_mainView (l r : WCell ψ κ) :
    let q := producerAdvanceLocal l r
    writerMainView q.1 = writerMainView l ∧
      writerMainView q.2 = writerMainView r := by
  unfold producerAdvanceLocal
  split
  · let r0 := producerFollowerStartLocal l r
    let r1 := producerTailMintLocal r0
    have h0 := producerFollowerStartLocal_mainView l r
    have h1 := producerTailMintLocal_mainView r0
    have h2 := producerAckLocal_mainView l r1
    change writerMainView (producerAckLocal l r1).1 = writerMainView l ∧
      writerMainView (producerAckLocal l r1).2 = writerMainView r
    exact ⟨h2.1, h2.2.trans (h1.trans h0)⟩
  · exact ⟨rfl, rfl⟩

/-- The post-advance root release assignment of `producerStep`. -/
private def producerFinishLocal (u : WCell ψ κ) : WCell ψ κ :=
  if u.agent.core.leader = true ∧ u.agent.core.label.val = 0 ∧
      ackReady u.agent.core = true then
    let b := u.agent.core
    let finished : BoundedAgentState ψ κ :=
      { b with
        write_state := .depart
        write := .none
        gen_ws := false
        b_carry := false }
    put u finished
  else u

private theorem producerFinishLocal_mainView (u : WCell ψ κ) :
    writerMainView (producerFinishLocal u) = writerMainView u := by
  unfold producerFinishLocal
  split
  · dsimp only
    change writerMainView
      (put u { u.agent.core with
        write_state := .depart
        write := .none
        gen_ws := false
        b_carry := false }) = writerMainView u
    exact put_mainView u _ rfl rfl rfl
  · rfl

/-- A definitionally exact staging of `WriterProducerRepair.producerStep`. -/
private def producerStepLocal
    (l r : WCell ψ κ) : WCell ψ κ × WCell ψ κ :=
  let l := producerStartLocal l
  let q := producerAdvanceLocal l r
  let l := producerFinishLocal q.1
  (idleFuel l, idleFuel q.2)

private theorem producerStep_eq_local (l r : WCell ψ κ) :
    producerStep l r = producerStepLocal l r := by
  rfl

private theorem producerStepLocal_mainView (l r : WCell ψ κ) :
    let q := producerStepLocal l r
    writerMainView q.1 = writerMainView l ∧
      writerMainView q.2 = writerMainView r := by
  let l0 := producerStartLocal l
  let q0 := producerAdvanceLocal l0 r
  let l1 := producerFinishLocal q0.1
  let out := producerStepLocal l r
  have hout : out = (idleFuel l1, idleFuel q0.2) := by rfl
  have hs := producerStartLocal_mainView l
  have ha := producerAdvanceLocal_mainView l0 r
  have hf := producerFinishLocal_mainView q0.1
  have hiL := idleFuel_mainView l1
  have hiR := idleFuel_mainView q0.2
  have hL : writerMainView out.1 = writerMainView l :=
    (congrArg (fun z => writerMainView z.1) hout).trans
      (hiL.trans (hf.trans (ha.1.trans hs)))
  have hR : writerMainView out.2 = writerMainView r :=
    (congrArg (fun z => writerMainView z.2) hout).trans
      (hiR.trans ha.2)
  exact ⟨hL, hR⟩

private theorem producerStep_mainView (l r : WCell ψ κ) :
    let q := producerStep l r
    writerMainView q.1 = writerMainView l ∧
      writerMainView q.2 = writerMainView r := by
  let q := producerStep l r
  let q' := producerStepLocal l r
  have he : q = q' := producerStep_eq_local l r
  have hp := producerStepLocal_mainView l r
  have hL : writerMainView q.1 = writerMainView l :=
    (congrArg (fun z => writerMainView z.1) he).trans hp.1
  have hR : writerMainView q.2 = writerMainView r :=
    (congrArg (fun z => writerMainView z.2) he).trans hp.2
  exact ⟨hL, hR⟩

private theorem persistent_mainView
    (hψ : 0 < ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := BirthStationaryWrite.stationaryPersistentBoundedRow hψ l r
    boundedMainView q.1 = boundedMainView l ∧
      boundedMainView q.2 = boundedMainView r := by
  let q := BirthStationaryWrite.stationaryPersistentBoundedRow hψ l r
  have hf :=
    BirthStationaryWrite.stationaryPersistentBoundedRow_frame hψ l r
  have hLv : BirthStationaryWrite.swView q.1.core.erase =
      BirthStationaryWrite.swView l.core.erase :=
    swPair_fst_eq q.1.core.erase q.2.core.erase
      l.core.erase r.core.erase hf
  have hRv : BirthStationaryWrite.swView q.2.core.erase =
      BirthStationaryWrite.swView r.core.erase :=
    swPair_snd_eq q.1.core.erase q.2.core.erase
      l.core.erase r.core.erase hf
  have hL : boundedMainView q.1 = boundedMainView l :=
    boundedMainView_eq_of_swView q.1 l hLv
  have hR : boundedMainView q.2 = boundedMainView r :=
    boundedMainView_eq_of_swView q.2 r hRv
  exact ⟨hL, hR⟩

/-- `stationaryProducerRow` after its two independent timer ticks. -/
private def stationaryAfterTickLocal
    (hψ : 0 < ψ) (l r : WCell ψ κ) :
    WCell ψ κ × WCell ψ κ :=
  if producerActive l.agent.core || producerActive r.agent.core ||
      producerStarts l.agent.core then
    producerStep l r
  else
    let q := BirthStationaryWrite.stationaryPersistentBoundedRow
      hψ l.agent r.agent
    (⟨q.1, 0⟩, ⟨q.2, 0⟩)

private theorem stationaryAfterTickLocal_mainView
    (hψ : 0 < ψ) (l r : WCell ψ κ) :
    let q := stationaryAfterTickLocal hψ l r
    writerMainView q.1 = writerMainView l ∧
      writerMainView q.2 = writerMainView r := by
  unfold stationaryAfterTickLocal
  split
  · exact producerStep_mainView l r
  · simpa only [writerMainView] using
      (persistent_mainView hψ l.agent r.agent)

private theorem stationaryProducerRow_eq_local
    (hψ : 0 < ψ) (l r : WCell ψ κ) :
    stationaryProducerRow hψ l r =
      stationaryAfterTickLocal hψ (tick l) (tick r) := by
  rfl

private theorem stationaryProducer_mainView
    (hψ : 0 < ψ) (l r : WCell ψ κ) :
    let q := stationaryProducerRow hψ l r
    writerMainView q.1 = writerMainView l ∧
      writerMainView q.2 = writerMainView r := by
  let q := stationaryProducerRow hψ l r
  let m := stationaryAfterTickLocal hψ (tick l) (tick r)
  have he : q = m := stationaryProducerRow_eq_local hψ l r
  have hm := stationaryAfterTickLocal_mainView hψ (tick l) (tick r)
  have htL := tick_mainView l
  have htR := tick_mainView r
  have hL : writerMainView q.1 = writerMainView l :=
    (congrArg (fun z => writerMainView z.1) he).trans
      (hm.1.trans htL)
  have hR : writerMainView q.2 = writerMainView r :=
    (congrArg (fun z => writerMainView z.2) he).trans
      (hm.2.trans htR)
  exact ⟨hL, hR⟩

/-- The producer/writer stage frames main comparison state, main path and label.
The resident bit is intentionally not in this theorem: `mint` may flip it. -/
theorem stationaryProducerMainComparisonFrame
    (hψ : 0 < ψ) :
    StationaryProducerMainComparisonFrame (κ := κ) hψ := by
  intro l r
  let q := stationaryProducerRow hψ l r
  have hm := stationaryProducer_mainView hψ l r
  have hL := writerMainView_fields q.1 l hm.1
  have hR := writerMainView_fields q.2 r hm.2
  exact ⟨hL.1, hL.2.1, hL.2.2,
    hR.1, hR.2.1, hR.2.2⟩

end R2NewEqualLocal
