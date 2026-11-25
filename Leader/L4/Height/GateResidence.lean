import Leader.L4.BStarParkedPhysical
import Leader.L4.BStarGeneratedPCAncestry
import Leader.L4.BStarSeparatingProgress
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarReleaseOrigin
import Leader.L4.BStarResetHealthyService

namespace L4.Height

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarLongToken BStarLongDoor BStarLongFixedRouting BStarH6WordChart BStarH6Ordinal
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner
open BStarAdmitIncidentGeometry BStarClearanceRaceMark BStarBitParity
open BStarSteeredLikelihood BStarParkedSteering BStarSteeringSupport
open BStarClearanceSource BStarSeparatingRail BStarSeparatingProgress
open BStarResetMarkAdapter BStarResetSchedule BStarSeparatorControl

section Physical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "run" => BStarResetSchedule.run step

/-- The necessary old-file test for an actual, generated ADMIT FIRST.
Alternative admission policies can supply their own fresh-request age
or budget test and use this same physical gate observation. -/
def firstAdmission {base : X} {hh : ∃ i, oldH6 B base i = true}
    (x : X) (i : Fin n) : Prop :=
  ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat)
      (fall : Pos n) (k : Nat) (v : Payload),
    Chart hp base hh o S len fall ∧ S.getD k fall = (i, 1) ∧
    Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode false) (.out k)) ∧
    bind (longGeometry B (x i)) 1 (atSite (x i).long 1) = .forward v ∧
    v.opcode.toNat = gateOpcode false ∧ v.fault = 0 ∧ v.race = 1

/-- The first suppressed occurrence spends a real mark at the alternate
side. The next occurrence of that same candidate passes literally,
even across an arbitrary skipped candidate prefix. -/
theorem submask_redirect_two_hits
    {base : X} {hh : ∃ i, oldH6 B base i = true}
    (start : X) {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (physical : ∀ a i, fresh a i → firstAdmission hp (base := base) (hh := hh) (run start a) i)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (a skipped : Word n) (e f : Fin n) (q : Q (run start a))
    (first : redirect a e = some f)
    (avoid : ∀ j ∈ skipped, j ≠ e) :
    let a' := a ++ [f]
    chooseBy redirect (a' ++ emit (chooseBy redirect) a' skipped) e = e := by
  dsimp only
  obtain ⟨i, s, I, F, S, T⟩ := mask a e f first
  obtain ⟨o, ss, len, fall, k, v, chart, atGate, cur, read, op, fault, race⟩ := physical a i F
  have hit : BStarAcquireDoorHistory.siteOf f (opposite s) = i := by
    rw [T]
    cases s with
    | left => exact RearTrace.right_predecessor i
    | right => rfl
  have fixed : ∀ j, oldH6 B (run start a) j = oldH6 B base j :=
    fun j => (congrArg Prod.fst (fiber _ q j)).symm
  have oldGate : gate (gateOpcode false) 1 (longGeometry B (run start a i)) = true :=
    (selected_gate_iff hp hh fixed (ready _ q) i 1 false).mpr ⟨rfl, I⟩
  have eq : run start (a ++ [f]) = step (run start a) f := by
    rw [BStarResetSchedule.run_append]
    rfl
  have q' : Q (run start (a ++ [f])) := eq.symm ▸ closed _ q f
  let z := firstCode (opposite s)
  let u := {v with race := z}
  have ⟨encoded, _, current, bound⟩ := BStarGateStutter.observed_race_step hp chart Q fiber closed
    distinct i f false k q atGate cur v read op fault (ready _ q) (ready _ (closed _ q f))
    oldGate (opposite s) hit z (.inl ⟨race, rfl⟩)
  have sound (b : Word n) (j : Fin n) (F : fresh b j) :
      ∃ u, bind (longGeometry B (run start b j)) 1 (atSite (run start b j).long 1) = .forward u ∧
        u.race = 1 := by
    obtain ⟨_, _, _, _, _, u, _, _, _, R, _, _, U⟩ := physical b j F
    exact ⟨u, R, U⟩
  have H := BStarParkedPhysical.parked_after_skipped hp chart Q fiber closed ready distinct start
    (redirect := redirect) mask sound
    i k atGate I u op fault (opposite s) rfl skipped (a ++ [f]) q'
    (eq.symm ▸ current) (eq.symm ▸ bound) (eq.symm ▸ encoded)
    (by
      intro j hj
      simpa only [opposite_opposite, ← S] using avoid j hj)
  simpa only [opposite_opposite, ← S] using H.2.2.2.2

/-- The current mode is an observation on the same fixed chart.
It does not depend on a choice of generated-history proof. -/
theorem current_mode_unique {base x : X} {addr : Nat → Pos n} {len : Nat}
    (a b : Mode) (A : Current hp base addr len x a) (B' : Current hp base addr len x b) : a = b := by
  cases a with
  | idle =>
    cases b with
    | idle => rfl
    | busy op d =>
      have H := A.1.2.symm.trans B'.1.2.2.1
      omega
  | busy op z =>
    cases b with
    | idle =>
      have H := B'.1.2.symm.trans A.1.2.2.1
      omega
    | busy op' d =>
      have E := A.1.2.2.2.symm.trans B'.1.2.2.2
      subst op'
      cases z with
      | out k =>
        cases d with
        | out j =>
          have E := BStarOwnerControlHistory.pointed_unique_forward (project addr x) len j
            B'.2.1 B'.2.2 k A.2.1.1
          rw [E.mp A.2.1.2.1]
        | back j =>
          exact (BStarOwnerControlHistory.pointed_backward_no_forward (project addr x)
            len j B'.2.1 k A.2.1.1 A.2.1.2.1).elim
      | back k =>
        cases d with
        | out j =>
          exact (BStarOwnerControlHistory.pointed_backward_no_forward (project addr x)
            len k A.2.1 j B'.2.1.1 B'.2.1.2.1).elim
        | back j =>
          rcases Nat.lt_trichotomy k j with H | rfl | H
          · obtain ⟨p, hold⟩ := A.2.1.2.1
            rw [B'.2.1.2.2.1 k H] at hold
            contradiction
          · rfl
          · obtain ⟨p, hold⟩ := B'.2.1.2.1
            rw [A.2.1.2.2.1 j H] at hold
            contradiction

end Physical
end L4.Height
