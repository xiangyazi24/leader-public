import Leader.Core.Basic
import Leader.AAFJ.LeastNonDivisor
import Leader.AAFJ.SmallRings
import Leader.Wu.Protocol.FiniteState

/-!
# AAFJ journal Protocol 6, generalized to `P_k`

This module is only the local protocol and its exact finite-state carrier.
It does not state a stabilization theorem.

The 2008 journal paper gives Protocol 6 explicitly for `P_2`.  Immediately
following Theorem 9.3 it defines the general family `P_k`: an oriented edge
`(u,v)` is a barrier exactly when `label_u + 1` is not congruent to `label_v`
modulo `k`, and advancing the barrier assigns
`label_v := label_u + 1 (mod k)`.  The remaining assignments are exactly the
sequential assignments of Protocol 6.
-/

namespace AAFJPK

/-- The five local fields of generalized AAFJ `P_k`.

The four control fields are bits; the label is an element of `Fin k`.
-/
structure State (k : Nat) where
  bullet : Bool
  leader : Bool
  label : Fin k
  probe : Bool
  phase : Bool
  deriving DecidableEq, Repr

/-- Journal `+1 mod k`, packaged as a `Fin k` value.

The protocol is only instantiated when `k > 0`; Theorem 9.4 later uses
`k >= 2`.
-/
def succLabel {k : Nat} (hk : 0 < k) (a : Fin k) : Fin k :=
  ⟨(a.val + 1) % k, Nat.mod_lt _ hk⟩

@[simp] theorem succLabel_val {k : Nat} (hk : 0 < k) (a : Fin k) :
    (succLabel hk a).val = (a.val + 1) % k := rfl

/-- Generalized `P_k` barrier condition from the paragraph after Theorem 9.3. -/
def IsBarrier {k : Nat} (hk : 0 < k) (u v : State k) : Prop :=
  succLabel hk u.label ≠ v.label

instance instDecidableIsBarrier {k : Nat} (hk : 0 < k) (u v : State k) :
    Decidable (IsBarrier hk u v) := by
  unfold IsBarrier
  infer_instance

/-- The generalized barrier test specializes at `k=2` to the label-equality
test printed in Protocol 6. -/
theorem isBarrier_two_iff_label_eq (u v : State 2) :
    IsBarrier (by decide) u v ↔ u.label = v.label := by
  rcases u with ⟨ub, ul, ⟨a, ha⟩, up, uh⟩
  rcases v with ⟨vb, vl, ⟨b, hb⟩, vp, vh⟩
  have haa : a = 0 ∨ a = 1 := by omega
  have hbb : b = 0 ∨ b = 1 := by omega
  rcases haa with rfl | rfl <;>
    rcases hbb with rfl | rfl <;>
    simp [IsBarrier, succLabel]

/-- Boolean complement represented in the generalized `Fin 2` label type. -/
def complementLabelTwo (a : Fin 2) : Fin 2 :=
  ⟨1 - a.val, by omega⟩

theorem succLabel_two_eq_complement (a : Fin 2) :
    succLabel (by decide) a = complementLabelTwo a := by
  rcases a with ⟨a, ha⟩
  have haa : a = 0 ∨ a = 1 := by omega
  rcases haa with rfl | rfl <;>
    apply Fin.ext <;> simp [succLabel, complementLabelTwo]

/-- On a printed-Protocol-6 barrier, the generalized label assignment is
exactly complementing the responder label. -/
theorem barrierLabel_two_eq_responder_complement (u v : State 2)
    (h : IsBarrier (by decide) u v) :
    succLabel (by decide) u.label = complementLabelTwo v.label := by
  have huv := (isBarrier_two_iff_label_eq u v).mp h
  rw [← huv]
  exact succLabel_two_eq_complement u.label

/-- Lines 2--4: a probe arriving from behind a barrier becomes a leader. -/
def probeHitsBarrier {k : Nat} (u : State k) : State k :=
  if u.probe = true then
    { u with leader := true, probe := false }
  else
    u

@[simp] theorem probeHitsBarrier_label {k : Nat} (u : State k) :
    (probeHitsBarrier u).label = u.label := by
  unfold probeHitsBarrier
  split <;> rfl

@[simp] theorem probeHitsBarrier_phase {k : Nat} (u : State k) :
    (probeHitsBarrier u).phase = u.phase := by
  unfold probeHitsBarrier
  split <;> rfl

@[simp] theorem probeHitsBarrier_of_probe {k : Nat} (u : State k)
    (h : u.probe = true) :
    probeHitsBarrier u = { u with leader := true, probe := false } := by
  simp [probeHitsBarrier, h]

@[simp] theorem probeHitsBarrier_of_no_probe {k : Nat} (u : State k)
    (h : u.probe = false) : probeHitsBarrier u = u := by
  simp [probeHitsBarrier, h]

/-- Lines 1--15, after the generalized `P_k` barrier test has succeeded.

The lets are intentional: they make the source-order sequencing explicit.
In particular lines 2--4 execute before lines 6--14.
-/
def barrierStep {k : Nat} (hk : 0 < k) (u v : State k) : State k × State k :=
  let u₁ := probeHitsBarrier u
  if u₁.phase = false then
    -- lines 6--10: generate a probe
    let u₂ := { u₁ with phase := true }
    let v₂ :=
      if v.leader = false then
        { v with probe := true }
      else
        v
    (u₂, v₂)
  else if v.probe = false then
    -- lines 11--14: advance the barrier and absorb an incoming bullet
    let v₁ :=
      { v with
        label := succLabel hk u₁.label
        phase := false
        bullet := false }
    (u₁, v₁)
  else
    (u₁, v)

/-- Lines 16--32, after the generalized barrier test has failed.

The follower branch deliberately performs the bullet move before the probe
move, matching lines 24--30 of Protocol 6.
-/
def nonBarrierStep {k : Nat} (u v : State k) : State k × State k :=
  if v.leader = true then
    -- lines 16--22
    if v.bullet = true then
      (u, { v with leader := false })
    else
      ({ u with bullet := true, probe := false }, v)
  else
    -- lines 23--30: first advance a bullet, then advance a probe
    let p :=
      if v.bullet = true then
        ({ u with bullet := true }, { v with bullet := false })
      else
        (u, v)
    let u₁ := p.1
    let v₁ := p.2
    if u₁.probe = true then
      ({ u₁ with probe := false }, { v₁ with probe := true })
    else
      (u₁, v₁)

/-- Literal deterministic local transition of generalized journal `P_k`.

For `k = 2`, `succLabel label_u ≠ label_v` is equivalent to the displayed
Protocol-6 test `label_u = label_v`.
-/
def transition {k : Nat} (hk : 0 < k) (u v : State k) : State k × State k :=
  if IsBarrier hk u v then
    barrierStep hk u v
  else
    nonBarrierStep u v

/-- The paper's `L/N` output bit: exactly the `leader` field. -/
def output {k : Nat} (q : State k) : Bool := q.leader

/-- `P_k` packaged in the repository's directed-ring population-protocol API. -/
def protocol (k : Nat) (hk : 0 < k) : PopulationProtocol where
  Q := State k
  Y := Bool
  transition := fun u v => transition hk u v
  output := fun q => output q

@[simp] theorem output_eq_leader {k : Nat} (q : State k) :
    output q = q.leader := rfl

@[simp] theorem protocol_output_eq_leader (k : Nat) (hk : 0 < k)
    (q : State k) :
    (protocol k hk).output q = q.leader := rfl

/-! ## Branch equations

These lemmas expose the journal branch priorities without asserting any global
ring invariant or convergence fact.
-/

@[simp] theorem transition_of_barrier {k : Nat} (hk : 0 < k)
    (u v : State k) (h : IsBarrier hk u v) :
    transition hk u v = barrierStep hk u v := by
  simp [transition, h]

@[simp] theorem transition_of_nonbarrier {k : Nat} (hk : 0 < k)
    (u v : State k) (h : ¬ IsBarrier hk u v) :
    transition hk u v = nonBarrierStep u v := by
  simp [transition, h]

/-- Lines 6--10 after the possible lines-2--4 probe conversion. -/
theorem barrierStep_phase_zero {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = false) :
    barrierStep hk u v =
      ({ probeHitsBarrier u with phase := true },
        if v.leader = false then { v with probe := true } else v) := by
  simp [barrierStep, hphase]

/-- Lines 11--14: a phase-one barrier advances only when `probe_v = 0`. -/
theorem barrierStep_phase_one_probe_free {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = true) (hprobe : v.probe = false) :
    barrierStep hk u v =
      (probeHitsBarrier u,
        { v with
          label := succLabel hk u.label
          phase := false
          bullet := false }) := by
  simp [barrierStep, hphase, hprobe]

/-- A phase-one barrier does not advance past a probe already at `v`. -/
theorem barrierStep_phase_one_probe_blocked {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = true) (hprobe : v.probe = true) :
    barrierStep hk u v = (probeHitsBarrier u, v) := by
  simp [barrierStep, hphase, hprobe]

/-- Lines 16--18: on a non-barrier edge, an incoming bullet kills leader `v`. -/
theorem nonBarrierStep_leader_hit {k : Nat} (u v : State k)
    (hleader : v.leader = true) (hbullet : v.bullet = true) :
    nonBarrierStep u v = (u, { v with leader := false }) := by
  simp [nonBarrierStep, hleader, hbullet]

/-- Lines 19--21: a bullet-free leader fires toward `u` and absorbs `u`'s probe. -/
theorem nonBarrierStep_leader_fires {k : Nat} (u v : State k)
    (hleader : v.leader = true) (hbullet : v.bullet = false) :
    nonBarrierStep u v = ({ u with bullet := true, probe := false }, v) := by
  simp [nonBarrierStep, hleader, hbullet]

/-- Lines 24--30 with both a bullet at `v` and a probe at `u`.

This equation witnesses the sequential order: the bullet fields are updated first,
then the probe fields are updated on those intermediate states.
-/
theorem nonBarrierStep_follower_bullet_probe {k : Nat} (u v : State k)
    (hleader : v.leader = false) (hbullet : v.bullet = true)
    (hprobe : u.probe = true) :
    nonBarrierStep u v =
      ({ u with bullet := true, probe := false },
       { v with bullet := false, probe := true }) := by
  simp [nonBarrierStep, hleader, hbullet, hprobe]

/-- Lines 24--27 when no probe is moved afterwards. -/
theorem nonBarrierStep_follower_bullet_only {k : Nat} (u v : State k)
    (hleader : v.leader = false) (hbullet : v.bullet = true)
    (hprobe : u.probe = false) :
    nonBarrierStep u v =
      ({ u with bullet := true }, { v with bullet := false }) := by
  simp [nonBarrierStep, hleader, hbullet, hprobe]

/-- Lines 28--30 when there is no bullet at `v`. -/
theorem nonBarrierStep_follower_probe_only {k : Nat} (u v : State k)
    (hleader : v.leader = false) (hbullet : v.bullet = false)
    (hprobe : u.probe = true) :
    nonBarrierStep u v =
      ({ u with probe := false }, { v with probe := true }) := by
  simp [nonBarrierStep, hleader, hbullet, hprobe]

/-- The quiet non-barrier follower branch is the identity. -/
theorem nonBarrierStep_follower_quiet {k : Nat} (u v : State k)
    (hleader : v.leader = false) (hbullet : v.bullet = false)
    (hprobe : u.probe = false) :
    nonBarrierStep u v = (u, v) := by
  simp [nonBarrierStep, hleader, hbullet, hprobe]

/-- A representative full-transition equation for lines 16--18. -/
theorem transition_nonbarrier_leader_hit {k : Nat} (hk : 0 < k)
    (u v : State k) (hbarrier : ¬ IsBarrier hk u v)
    (hleader : v.leader = true) (hbullet : v.bullet = true) :
    transition hk u v = (u, { v with leader := false }) := by
  simp [transition, hbarrier, nonBarrierStep, hleader, hbullet]

/-- A representative full-transition equation for the sequential lines 24--30. -/
theorem transition_nonbarrier_follower_bullet_probe {k : Nat} (hk : 0 < k)
    (u v : State k) (hbarrier : ¬ IsBarrier hk u v)
    (hleader : v.leader = false) (hbullet : v.bullet = true)
    (hprobe : u.probe = true) :
    transition hk u v =
      ({ u with bullet := true, probe := false },
       { v with bullet := false, probe := true }) := by
  simp [transition, hbarrier, nonBarrierStep, hleader, hbullet, hprobe]

/-! ## Exact constructive carrier certificate

There are four Boolean control fields and one `Fin k` label, hence exactly
`2^4 * k = 16 * k` states.  We reuse the repository's constructive
`ExhaustiveList` API and prove the generated list is duplicate-free.
-/

/-- A product code ordered as `bullet, leader, probe, phase, label`.

The left-associated Boolean product is chosen so its exact length reduces to
`16` before the final multiplication by `k`.
-/
abbrev StateCode (k : Nat) := ((((Bool × Bool) × Bool) × Bool) × Fin k)

/-- Decode a product code into the named five-field state. -/
def decodeState (k : Nat) (x : StateCode k) : State k :=
  { bullet := x.1.1.1.1
    leader := x.1.1.1.2
    label := x.2
    probe := x.1.1.2
    phase := x.1.2 }

/-- The inverse coding map. -/
def encodeState (k : Nat) (q : State k) : StateCode k :=
  ((((q.bullet, q.leader), q.probe), q.phase), q.label)

@[simp] theorem decode_encode (k : Nat) (q : State k) :
    decodeState k (encodeState k q) = q := by
  cases q
  rfl

@[simp] theorem encode_decode (k : Nat) (x : StateCode k) :
    encodeState k (decodeState k x) = x := by
  rcases x with ⟨⟨⟨⟨bullet, leader⟩, probe⟩, phase⟩, label⟩
  rfl

theorem decodeState_injective (k : Nat) : Function.Injective (decodeState k) := by
  intro x y h
  have h' := congrArg (encodeState k) h
  simpa using h'

theorem decodeState_surjective (k : Nat) : Function.Surjective (decodeState k) := by
  intro q
  exact ⟨encodeState k q, decode_encode k q⟩

theorem decodeState_bijective (k : Nat) :
    Function.Injective (decodeState k) ∧ Function.Surjective (decodeState k) :=
  ⟨decodeState_injective k, decodeState_surjective k⟩

/-- Exact product source for the five fields. -/
def stateSource (k : Nat) : ExhaustiveList (StateCode k) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod
        (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool)
        ExhaustiveList.bool)
      ExhaustiveList.bool)
    (ExhaustiveList.fin k)

/-- Exact state certificate obtained by the bijective decoder. -/
def states (k : Nat) : ExhaustiveList (State k) :=
  ExhaustiveList.mapSurjective (stateSource k) (decodeState k)
    (decodeState_surjective k)

theorem stateSource_values_nodup (k : Nat) :
    (stateSource k).values.Nodup := by
  unfold stateSource
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · apply ExhaustiveList.values_nodup_prod
        · exact ExhaustiveList.values_nodup_bool
        · exact ExhaustiveList.values_nodup_bool
      · exact ExhaustiveList.values_nodup_bool
    · exact ExhaustiveList.values_nodup_bool
  · exact ExhaustiveList.values_nodup_fin k

theorem states_values_nodup (k : Nat) : (states k).values.Nodup := by
  unfold states
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact stateSource_values_nodup k
  · exact decodeState_injective k

theorem stateSource_values_length (k : Nat) :
    (stateSource k).values.length = 16 * k := by
  simp [stateSource, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool, ExhaustiveList.values_length_fin]

theorem states_values_length (k : Nat) :
    (states k).values.length = 16 * k := by
  unfold states
  rw [ExhaustiveList.values_length_mapSurjective]
  exact stateSource_values_length k

/-- Finite-index decoder induced by the duplicate-free exact state list. -/
def stateDecoder (k : Nat) : Fin (states k).values.length → State k :=
  (states k).decode

theorem stateDecoder_injective (k : Nat) :
    Function.Injective (stateDecoder k) := by
  unfold stateDecoder
  exact ExhaustiveList.decode_injective_of_values_nodup
    (states k) (states_values_nodup k)

theorem stateDecoder_surjective (k : Nat) :
    Function.Surjective (stateDecoder k) := by
  unfold stateDecoder
  exact ExhaustiveList.decode_surjective (states k)

theorem stateDecoder_bijective (k : Nat) :
    Function.Injective (stateDecoder k) ∧
      Function.Surjective (stateDecoder k) :=
  ⟨stateDecoder_injective k, stateDecoder_surjective k⟩

/-- The exact carrier size, stated directly for the protocol state type. -/
theorem exact_state_count (k : Nat) :
    (states k).values.length = 16 * k := states_values_length k

end AAFJPK

namespace AAFJExactFamily

/-- The corrected nonuniform family for a known exact positive ring size.

The small rings use their dedicated protocols.  Every ring of size at least
three uses generalized journal `P_k` at the constructive least nondivisor
`k = snd(n)`. -/
def protocolFor (n : Nat) (hn : 0 < n) : PopulationProtocol :=
  if n = 1 then
    AAFJSmallRings.oneProtocol
  else if n = 2 then
    AAFJSmallRings.twoProtocol
  else
    AAFJPK.protocol (AAFJExactN.leastNonDivisor n) (by
      have hk := AAFJExactN.leastNonDivisor_ge_two hn
      omega)

@[simp] theorem protocolFor_one (hn : 0 < 1) :
    protocolFor 1 hn = AAFJSmallRings.oneProtocol := by
  simp [protocolFor]

@[simp] theorem protocolFor_two (hn : 0 < 2) :
    protocolFor 2 hn = AAFJSmallRings.twoProtocol := by
  simp [protocolFor]

theorem protocolFor_large {n : Nat} (hn : 0 < n)
    (h1 : n ≠ 1) (h2 : n ≠ 2) :
    protocolFor n hn =
      AAFJPK.protocol (AAFJExactN.leastNonDivisor n) (by
        have hk := AAFJExactN.leastNonDivisor_ge_two hn
        omega) := by
  simp [protocolFor, h1, h2]

end AAFJExactFamily
