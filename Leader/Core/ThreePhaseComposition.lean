import Leader.Core.PhaseComposition

/-!
# Three phases on the actual finite uniform stopping tree

The composition below consumes the project's `StopNode`, Bellman predicate,
and two-phase theorem directly.  Both terminal outcomes have zero potential;
semantic stabilization additionally requires certified success and control of
terminal failure.  No alternate stopping-tree type is introduced here.
-/

set_option autoImplicit false

namespace ThreePhaseComposition

open FiniteUniformStoppingTree PhaseComposition

/-- Name the potential returned by the existing two-phase composition. -/
def twoPhasePotential {S : Type} {n : Nat}
    {step : S → Fin n → StopNode S}
    (I : MonotonePhaseIndicator step) (Phi1 Psi : StopNode S → Nat)
    (C : Nat) : StopNode S → Nat
  | .active s => if I.phase s = .p1 then Phi1 (.active s) + C else Psi (.active s)
  | .success => 0
  | .failure => 0

inductive ProtocolPhase where | p1 | p2 | p3 deriving DecidableEq

def earlyPhase : ProtocolPhase → TwoPhase
  | .p1 => .p1 | .p2 => .p2 | .p3 => .p2

def latePhase : ProtocolPhase → TwoPhase
  | .p1 => .p1 | .p2 => .p1 | .p3 => .p2

theorem earlyPhase_eq_p1_iff (p : ProtocolPhase) :
    earlyPhase p = .p1 ↔ p = .p1 := by cases p <;> simp [earlyPhase]

theorem earlyPhase_eq_p2_iff (p : ProtocolPhase) :
    earlyPhase p = .p2 ↔ p = .p2 ∨ p = .p3 := by cases p <;> simp [earlyPhase]

theorem latePhase_eq_p1_iff (p : ProtocolPhase) :
    latePhase p = .p1 ↔ p = .p1 ∨ p = .p2 := by cases p <;> simp [latePhase]

theorem latePhase_eq_p2_iff (p : ProtocolPhase) :
    latePhase p = .p2 ↔ p = .p3 := by cases p <;> simp [latePhase]

/-- P1 versus P2-or-P3. -/
def earlyIndicator {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (phase : S → ProtocolPhase)
    (p2_no_return : ∀ s e t, phase s = .p2 → step s e = .active t →
      phase t = .p2 ∨ phase t = .p3)
    (p3_no_return : ∀ s e t, phase s = .p3 → step s e = .active t →
      phase t = .p3) : MonotonePhaseIndicator step where
  phase := fun s => earlyPhase (phase s)
  noBack := by
    intro s e t hs he
    rcases (earlyPhase_eq_p2_iff (phase s)).mp hs with hs2 | hs3
    · exact (earlyPhase_eq_p2_iff (phase t)).mpr (p2_no_return s e t hs2 he)
    · exact (earlyPhase_eq_p2_iff (phase t)).mpr
        (Or.inr (p3_no_return s e t hs3 he))

/-- Globally P1-or-P2 versus P3; after P1 is exited this is P2 versus P3. -/
def lateIndicator {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (phase : S → ProtocolPhase)
    (p3_no_return : ∀ s e t, phase s = .p3 → step s e = .active t →
      phase t = .p3) : MonotonePhaseIndicator step where
  phase := fun s => latePhase (phase s)
  noBack := by
    intro s e t hs he
    have hs3 := (latePhase_eq_p2_iff (phase s)).mp hs
    exact (latePhase_eq_p2_iff (phase t)).mpr (p3_no_return s e t hs3 he)

/-- Accepted proof-side phase map. Classical decidability is explicit. -/
noncomputable def protocolPhase {S : Type}
    (PostAudit ElimReady : S → Prop) (x : S) : ProtocolPhase :=
  @ite ProtocolPhase (¬ PostAudit x) (Classical.propDecidable _) .p1
    (@ite ProtocolPhase (¬ ElimReady x) (Classical.propDecidable _) .p2 .p3)

def Separated {S Gap : Type} (GapAt : S → Gap → Prop)
    (gapLength : S → Gap → Nat) (h : Nat) (x : S) : Prop :=
  ∀ g, GapAt x g → h ≤ gapLength x g

theorem protocolPhase_eq_p2_postAudit {S : Type}
    (PostAudit ElimReady : S → Prop) {x : S}
    (h : protocolPhase PostAudit ElimReady x = .p2) : PostAudit x := by
  by_cases hp : PostAudit x
  · exact hp
  · simp [protocolPhase, hp] at h

theorem protocolPhase_of_postAudit {S : Type}
    (PostAudit ElimReady : S → Prop) {x : S} (hp : PostAudit x) :
    protocolPhase PostAudit ElimReady x = .p2 ∨
      protocolPhase PostAudit ElimReady x = .p3 := by
  by_cases hr : ElimReady x
  · right; simp [protocolPhase, hp, hr]
  · left; simp [protocolPhase, hp, hr]

/-- Reusable restricted child term. -/
def restrictedChild {S P : Type} {n : Nat} [DecidableEq P]
    (step : S → Fin n → StopNode S) (phase : S → P) (p : P)
    (Phi : StopNode S → Nat) (s : S) (e : Fin n) : Nat :=
  match step s e with
  | .active t => if phase t = p then Phi (.active t) else 0
  | .success => 0
  | .failure => 0

/-- The P1/P2 hypotheses are instances of this transparent definition. -/
def RestrictedBellman {S P : Type} {n : Nat} [DecidableEq P]
    (step : S → Fin n → StopNode S) (phase : S → P) (p : P)
    (Phi : StopNode S → Nat) : Prop :=
  ∀ s, phase s = p →
    n + (List.ofFn (fun e : Fin n => restrictedChild step phase p Phi s e)).sum ≤
      n * Phi (.active s)

def preP3Potential {S : Type} (phase : S → ProtocolPhase)
    (Phi1 Phi2 : StopNode S → Nat) (C2 : Nat) : StopNode S → Nat
  | .active s => match phase s with
      | .p1 => Phi1 (.active s) + C2
      | .p2 => Phi2 (.active s)
      | .p3 => 0
  | .success => 0 | .failure => 0

/-- Final shape: P1=`Phi1+(C2+C3)`, P2=`Phi2+C3`, P3=`Psi3`. -/
def threePhasePotential {S : Type} (phase : S → ProtocolPhase)
    (Phi1 Phi2 Psi3 : StopNode S → Nat) (C2 C3 : Nat) : StopNode S → Nat
  | .active s => match phase s with
      | .p1 => Phi1 (.active s) + (C2 + C3)
      | .p2 => Phi2 (.active s) + C3
      | .p3 => Psi3 (.active s)
  | .success => 0 | .failure => 0

/-- Reserve ledger. `C1` bounds the starting P1 potential; `C2` bounds P2 at
P1-to-P2 entry; `C3` bounds P3 at P1/P2-to-P3 entry. The historical full-gap
estimate `C3 n h m0 ~ 16*n*n*(m0-1)` is cubic for `m0=Theta(n)`. With
separation forcing `m0 <= n/h`, the corrected C3 route is the proof-chosen
minimal-triple/harmonic `O(n^2 log n)` accounting, inside the recorded
`O(n^2 log n log log n)` target. -/
def reserveTotal (C1 C2 C3 : Nat) : Nat := C1 + C2 + C3

/-- Compose the P1 and P2 restricted inequalities into the first bucket of the
shifted pre-P3 indicator. -/
theorem preP3_restricted_bellman {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (phase : S → ProtocolPhase)
    (Phi1 Phi2 : StopNode S → Nat) (C2 : Nat) (E2 : S → Prop)
    (p2_no_return : ∀ s e t, phase s = ProtocolPhase.p2 →
      step s e = .active t → phase t = ProtocolPhase.p2 ∨ phase t = ProtocolPhase.p3)
    (h1 : RestrictedBellman step phase ProtocolPhase.p1 Phi1)
    (h2 : RestrictedBellman step phase ProtocolPhase.p2 Phi2)
    (henter2 : ∀ s e t, phase s = ProtocolPhase.p1 → step s e = .active t →
      phase t = ProtocolPhase.p2 → E2 t)
    (hC2 : ∀ t, E2 t → Phi2 (.active t) ≤ C2) :
    RestrictedBellman step (fun s => latePhase (phase s)) TwoPhase.p1
      (preP3Potential phase Phi1 Phi2 C2) := by
  intro s hsLate
  cases hs : phase s with
  | p1 =>
      have hp : ∀ e : Fin n,
          restrictedChild step (fun x => latePhase (phase x)) TwoPhase.p1
            (preP3Potential phase Phi1 Phi2 C2) s e ≤
          restrictedChild step phase ProtocolPhase.p1 Phi1 s e + C2 := by
        intro e
        cases he : step s e with
        | success =>
            simp only [restrictedChild, he]
            exact Nat.zero_le _
        | failure =>
            simp only [restrictedChild, he]
            exact Nat.zero_le _
        | active t =>
            cases ht : phase t with
            | p1 => simp [restrictedChild, latePhase, preP3Potential, he, ht]
            | p2 =>
                have hc := hC2 t (henter2 s e t hs he ht)
                simpa [restrictedChild, latePhase, preP3Potential, he, ht] using hc
            | p3 => simp [restrictedChild, latePhase, he, ht]
      have hsum := ofFn_sum_le
        (fun e : Fin n => restrictedChild step (fun x => latePhase (phase x))
          TwoPhase.p1 (preP3Potential phase Phi1 Phi2 C2) s e)
        (fun e : Fin n => restrictedChild step phase ProtocolPhase.p1 Phi1 s e + C2) hp
      rw [ofFn_sum_add, ofFn_sum_const] at hsum
      have hb := h1 s hs
      have hcalc :
          n + (List.ofFn (fun e : Fin n => restrictedChild step
            (fun x => latePhase (phase x)) TwoPhase.p1
            (preP3Potential phase Phi1 Phi2 C2) s e)).sum ≤
            n * (Phi1 (.active s) + C2) := by
        calc
          n + (List.ofFn (fun e : Fin n => restrictedChild step
              (fun x => latePhase (phase x)) TwoPhase.p1
              (preP3Potential phase Phi1 Phi2 C2) s e)).sum ≤
              n + ((List.ofFn (fun e : Fin n =>
                restrictedChild step phase ProtocolPhase.p1 Phi1 s e)).sum + n * C2) :=
            Nat.add_le_add_left hsum n
          _ = (n + (List.ofFn (fun e : Fin n =>
                restrictedChild step phase ProtocolPhase.p1 Phi1 s e)).sum) + n * C2 := by omega
          _ ≤ n * Phi1 (.active s) + n * C2 := Nat.add_le_add_right hb (n * C2)
          _ = n * (Phi1 (.active s) + C2) := by rw [Nat.mul_add]
      simpa [preP3Potential, hs] using hcalc
  | p2 =>
      have hp : ∀ e : Fin n,
          restrictedChild step (fun x => latePhase (phase x)) TwoPhase.p1
            (preP3Potential phase Phi1 Phi2 C2) s e =
          restrictedChild step phase ProtocolPhase.p2 Phi2 s e := by
        intro e
        cases he : step s e with
        | success => simp only [restrictedChild, he]
        | failure => simp only [restrictedChild, he]
        | active t =>
            rcases p2_no_return s e t hs he with ht2 | ht3
            · have hlate : latePhase (phase t) = TwoPhase.p1 := by
                simp [latePhase, ht2]
              simp only [restrictedChild, he]
              rw [if_pos hlate, if_pos ht2]
              simp [preP3Potential, ht2]
            · have hlate : ¬ latePhase (phase t) = TwoPhase.p1 := by
                simp [latePhase, ht3]
              have hnot2 : ¬ phase t = ProtocolPhase.p2 := by
                simp [ht3]
              simp only [restrictedChild, he]
              rw [if_neg hlate, if_neg hnot2]
      have hsum := ofFn_sum_eq
        (fun e : Fin n => restrictedChild step (fun x => latePhase (phase x))
          TwoPhase.p1 (preP3Potential phase Phi1 Phi2 C2) s e)
        (fun e : Fin n => restrictedChild step phase ProtocolPhase.p2 Phi2 s e) hp
      calc
        n + (List.ofFn (fun e : Fin n => restrictedChild step
            (fun x => latePhase (phase x)) TwoPhase.p1
            (preP3Potential phase Phi1 Phi2 C2) s e)).sum =
            n + (List.ofFn (fun e : Fin n =>
              restrictedChild step phase ProtocolPhase.p2 Phi2 s e)).sum :=
          congrArg (n + ·) hsum
        _ ≤ n * Phi2 (.active s) := h2 s hs
        _ = n * preP3Potential phase Phi1 Phi2 C2 (.active s) := by
          simp [preP3Potential, hs]
  | p3 => simp [latePhase, hs] at hsLate

theorem late_composedPotential_eq_three {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (phase : S → ProtocolPhase)
    (Phi1 Phi2 Psi3 : StopNode S → Nat) (C2 C3 : Nat)
    (p3_no_return : ∀ s e t, phase s = .p3 → step s e = .active t →
      phase t = .p3) :
    twoPhasePotential (lateIndicator step phase p3_no_return)
      (preP3Potential phase Phi1 Phi2 C2) Psi3 C3 =
      threePhasePotential phase Phi1 Phi2 Psi3 C2 C3 := by
  funext x
  cases x with
  | success => rfl
  | failure => rfl
  | active s =>
      cases hs : phase s <;>
        simp [twoPhasePotential, lateIndicator, latePhase, preP3Potential,
          threePhasePotential, hs, Nat.add_assoc]

theorem early_composedPotential_eq_three {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (phase : S → ProtocolPhase)
    (Phi1 Phi2 Psi3 : StopNode S → Nat) (C2 C3 : Nat)
    (p2_no_return : ∀ s e t, phase s = .p2 → step s e = .active t →
      phase t = .p2 ∨ phase t = .p3)
    (p3_no_return : ∀ s e t, phase s = .p3 → step s e = .active t →
      phase t = .p3) :
    twoPhasePotential (earlyIndicator step phase p2_no_return p3_no_return)
      Phi1 (threePhasePotential phase Phi1 Phi2 Psi3 C2 C3) (C2 + C3) =
      threePhasePotential phase Phi1 Phi2 Psi3 C2 C3 := by
  funext x
  cases x with
  | success => rfl
  | failure => rfl
  | active s =>
      cases hs : phase s <;>
        simp [twoPhasePotential, earlyIndicator, earlyPhase, threePhasePotential, hs]

/-- Pure three-phase composition. `compose_twice` is invoked twice on the same
`step`. The inner call uses the globally monotone P1-or-P2/P3 indicator and
already yields P1=`Phi1+(C2+C3)`, P2=`Phi2+C3`, P3=`Psi3`; the outer P1/post-P1
call reproduces that potential with reserve `C2+C3`. -/
theorem compose_three {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (phase : S → ProtocolPhase)
    (Phi1 Phi2 Psi3 : StopNode S → Nat) (C2 C3 : Nat) (E2 E3 : S → Prop)
    (p2_no_return : ∀ s e t, phase s = .p2 → step s e = .active t →
      phase t = .p2 ∨ phase t = .p3)
    (p3_no_return : ∀ s e t, phase s = .p3 → step s e = .active t →
      phase t = .p3)
    (h1 : RestrictedBellman step phase ProtocolPhase.p1 Phi1)
    (h2 : RestrictedBellman step phase ProtocolPhase.p2 Phi2)
    (h3 : NatBellmanSuperSolution step 1 Psi3)
    (henter2 : ∀ s e t, phase s = .p1 → step s e = .active t →
      phase t = .p2 → E2 t)
    (hC2 : ∀ t, E2 t → Phi2 (.active t) ≤ C2)
    (henter3 : ∀ s e t, (phase s = .p1 ∨ phase s = .p2) →
      step s e = .active t → phase t = .p3 → E3 t)
    (hC3 : ∀ t, E3 t → Psi3 (.active t) ≤ C3) :
    NatBellmanSuperSolution step 1
      (threePhasePotential phase Phi1 Phi2 Psi3 C2 C3) := by
  let Ilate : MonotonePhaseIndicator step := lateIndicator step phase p3_no_return
  have hpre := preP3_restricted_bellman step phase Phi1 Phi2 C2 E2
    p2_no_return h1 h2 henter2 hC2
  have hpreI : ∀ s, Ilate.phase s = .p1 →
      n + (List.ofFn (fun e : Fin n => match step s e with
        | .active t => if Ilate.phase t = .p1 then
            preP3Potential phase Phi1 Phi2 C2 (.active t) else 0
        | .success => 0 | .failure => 0)).sum ≤
        n * preP3Potential phase Phi1 Phi2 C2 (.active s) := by
    simpa [RestrictedBellman, restrictedChild, Ilate, lateIndicator] using hpre
  have henterLate : ∀ s e t, Ilate.phase s = .p1 → step s e = .active t →
      Ilate.phase t = .p2 → E3 t := by
    intro s e t hs he ht
    have hs' : phase s = .p1 ∨ phase s = .p2 :=
      (latePhase_eq_p1_iff (phase s)).mp (by simpa [Ilate, lateIndicator] using hs)
    have ht' : phase t = .p3 :=
      (latePhase_eq_p2_iff (phase t)).mp (by simpa [Ilate, lateIndicator] using ht)
    exact henter3 s e t hs' he ht'
  have hinnerRaw := compose_twice step Ilate
    (preP3Potential phase Phi1 Phi2 C2) Psi3 C3 E3 hpreI h3 henterLate hC3
  have hinner : NatBellmanSuperSolution step 1
      (threePhasePotential phase Phi1 Phi2 Psi3 C2 C3) := by
    rw [← late_composedPotential_eq_three step phase Phi1 Phi2 Psi3 C2 C3
      p3_no_return]
    exact hinnerRaw
  let Iearly : MonotonePhaseIndicator step :=
    earlyIndicator step phase p2_no_return p3_no_return
  have h1Early : ∀ s, Iearly.phase s = .p1 →
      n + (List.ofFn (fun e : Fin n => match step s e with
        | .active t => if Iearly.phase t = .p1 then Phi1 (.active t) else 0
        | .success => 0 | .failure => 0)).sum ≤ n * Phi1 (.active s) := by
    simpa [RestrictedBellman, restrictedChild, Iearly, earlyIndicator,
      earlyPhase_eq_p1_iff] using h1
  let E23 : S → Prop := fun t =>
    (phase t = ProtocolPhase.p2 ∧ Phi2 (.active t) ≤ C2) ∨
    (phase t = ProtocolPhase.p3 ∧ Psi3 (.active t) ≤ C3)
  have henterEarly : ∀ s e t, Iearly.phase s = .p1 → step s e = .active t →
      Iearly.phase t = .p2 → E23 t := by
    intro s e t hs he ht
    have hs' : phase s = .p1 :=
      (earlyPhase_eq_p1_iff (phase s)).mp (by simpa [Iearly, earlyIndicator] using hs)
    rcases (earlyPhase_eq_p2_iff (phase t)).mp
        (by simpa [Iearly, earlyIndicator] using ht) with ht2 | ht3
    · exact Or.inl ⟨ht2, hC2 t (henter2 s e t hs' he ht2)⟩
    · exact Or.inr ⟨ht3, hC3 t (henter3 s e t (Or.inl hs') he ht3)⟩
  have hC23 : ∀ t, E23 t →
      threePhasePotential phase Phi1 Phi2 Psi3 C2 C3 (.active t) ≤ C2 + C3 := by
    intro t h
    rcases h with ⟨ht, hb⟩ | ⟨ht, hb⟩
    · simp [threePhasePotential, ht]; omega
    · simp [threePhasePotential, ht]; omega
  have houterRaw := compose_twice step Iearly Phi1
    (threePhasePotential phase Phi1 Phi2 Psi3 C2 C3) (C2 + C3) E23
    h1Early hinner henterEarly hC23
  rw [← early_composedPotential_eq_three step phase Phi1 Phi2 Psi3 C2 C3
    p2_no_return p3_no_return]
  exact houterRaw

/-- Abstract protocol wrapper. `_GapAt`, `_gapLength`, and `_leaderCount` are
kept as explicit wiring parameters because the real `ElimReady` is built from
them; the pure composition only inspects `PostAudit` and `ElimReady`. -/
theorem protocol_three_phase_supersolution {S Gap : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (PostAudit ElimReady : S → Prop)
    (_GapAt : S → Gap → Prop) (_gapLength : S → Gap → Nat)
    (_leaderCount : S → Nat)
    (Phi1 Phi2 Psi3 : StopNode S → Nat) (C2 C3 : Nat) (E2 E3 : S → Prop)
    (p2_no_return : ∀ s e t, protocolPhase PostAudit ElimReady s = .p2 →
      step s e = .active t → protocolPhase PostAudit ElimReady t = .p2 ∨
        protocolPhase PostAudit ElimReady t = .p3)
    (p3_no_return : ∀ s e t, protocolPhase PostAudit ElimReady s = .p3 →
      step s e = .active t → protocolPhase PostAudit ElimReady t = .p3)
    (h1 : RestrictedBellman step (protocolPhase PostAudit ElimReady)
      ProtocolPhase.p1 Phi1)
    (h2 : RestrictedBellman step (protocolPhase PostAudit ElimReady)
      ProtocolPhase.p2 Phi2)
    (h3 : NatBellmanSuperSolution step 1 Psi3)
    (henter2 : ∀ s e t, protocolPhase PostAudit ElimReady s = .p1 →
      step s e = .active t → protocolPhase PostAudit ElimReady t = .p2 → E2 t)
    (hC2 : ∀ t, E2 t → Phi2 (.active t) ≤ C2)
    (henter3 : ∀ s e t, (protocolPhase PostAudit ElimReady s = .p1 ∨
      protocolPhase PostAudit ElimReady s = .p2) → step s e = .active t →
      protocolPhase PostAudit ElimReady t = .p3 → E3 t)
    (hC3 : ∀ t, E3 t → Psi3 (.active t) ≤ C3) :
    NatBellmanSuperSolution step 1
      (threePhasePotential (protocolPhase PostAudit ElimReady)
        Phi1 Phi2 Psi3 C2 C3) := by
  exact compose_three step (protocolPhase PostAudit ElimReady) Phi1 Phi2 Psi3
    C2 C3 E2 E3 p2_no_return p3_no_return h1 h2 h3 henter2 hC2 henter3 hC3

theorem threePhasePotential_initial_le {S : Type} (phase : S → ProtocolPhase)
    (Phi1 Phi2 Psi3 : StopNode S → Nat) (C1 C2 C3 : Nat) {s : S}
    (hs : phase s = .p1) (hC1 : Phi1 (.active s) ≤ C1) :
    threePhasePotential phase Phi1 Phi2 Psi3 C2 C3 (.active s) ≤
      reserveTotal C1 C2 C3 := by
  simp [threePhasePotential, reserveTotal, hs]
  omega

/-- Gap-level formula mirrored by the real `PostAudit`. -/
def GapPostAudit {S Gap : Type}
    (GapAt CurrentCertified DemotionOwned : S → Gap → Prop) (x : S) : Prop :=
  ∀ g, GapAt x g → CurrentCertified x g ∨ DemotionOwned x g

/-- No intermediate unowned stale gap: a topology-changing active step owns
every new gap in its target state atomically. -/
def CommitAtomic {S Gap : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (TopologyChanged : S → S → Prop)
    (NewGap : S → S → Gap → Prop) (DemotionOwned : S → Gap → Prop) : Prop :=
  ∀ s e t, step s e = .active t → TopologyChanged s t →
    ∀ g, NewGap s t g → DemotionOwned t g

theorem postAudit_preserved_of_commitAtomic {S Gap : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (PostAudit : S → Prop)
    (GapAt CurrentCertified DemotionOwned : S → Gap → Prop)
    (TopologyChanged : S → S → Prop) (NewGap : S → S → Gap → Prop)
    (hPostAudit : ∀ x, PostAudit x ↔
      GapPostAudit GapAt CurrentCertified DemotionOwned x)
    (commitAtomic : CommitAtomic step TopologyChanged NewGap DemotionOwned)
    (nonTopologyPreserved : ∀ s e t, step s e = .active t →
      ¬ TopologyChanged s t → PostAudit s → PostAudit t)
    (oldGapPreserved : ∀ s e t, step s e = .active t → TopologyChanged s t →
      PostAudit s → ∀ g, GapAt t g → ¬ NewGap s t g →
        CurrentCertified t g ∨ DemotionOwned t g)
    {s : S} {e : Fin n} {t : S}
    (he : step s e = .active t) (hs : PostAudit s) : PostAudit t := by
  by_cases htop : TopologyChanged s t
  · apply (hPostAudit t).mpr
    intro g hg
    by_cases hnew : NewGap s t g
    · exact Or.inr (commitAtomic s e t he htop g hnew)
    · exact oldGapPreserved s e t he htop hs g hg hnew
  · exact nonTopologyPreserved s e t he htop hs

/-- `CommitAtomic` plus row preservation gives P2 monotonicity. It prevents a
P2 state from falling back to P1. `p3_no_return` still additionally needs the
separate `ElimReady` closure: preserved leader vector/gaps on noncommits,
separation under `a,b >= h` merging, and no births after P1. -/
theorem p2_no_return_of_commitAtomic {S Gap : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (PostAudit ElimReady : S → Prop)
    (GapAt CurrentCertified DemotionOwned : S → Gap → Prop)
    (TopologyChanged : S → S → Prop) (NewGap : S → S → Gap → Prop)
    (hPostAudit : ∀ x, PostAudit x ↔
      GapPostAudit GapAt CurrentCertified DemotionOwned x)
    (commitAtomic : CommitAtomic step TopologyChanged NewGap DemotionOwned)
    (nonTopologyPreserved : ∀ s e t, step s e = .active t →
      ¬ TopologyChanged s t → PostAudit s → PostAudit t)
    (oldGapPreserved : ∀ s e t, step s e = .active t → TopologyChanged s t →
      PostAudit s → ∀ g, GapAt t g → ¬ NewGap s t g →
        CurrentCertified t g ∨ DemotionOwned t g) :
    ∀ s e t, protocolPhase PostAudit ElimReady s = .p2 → step s e = .active t →
      protocolPhase PostAudit ElimReady t = .p2 ∨
        protocolPhase PostAudit ElimReady t = .p3 := by
  intro s e t hs he
  have hsource := protocolPhase_eq_p2_postAudit PostAudit ElimReady hs
  have htarget := postAudit_preserved_of_commitAtomic step PostAudit GapAt
    CurrentCertified DemotionOwned TopologyChanged NewGap hPostAudit commitAtomic
    nonTopologyPreserved oldGapPreserved he hsource
  exact protocolPhase_of_postAudit PostAudit ElimReady htarget

end ThreePhaseComposition

#print axioms FiniteUniformStoppingTree.ofFn_sum_eq
#print axioms FiniteUniformStoppingTree.ofFn_sum_le
#print axioms FiniteUniformStoppingTree.ofFn_sum_add
#print axioms FiniteUniformStoppingTree.ofFn_sum_const
#print axioms PhaseComposition.compose_twice
#print axioms ThreePhaseComposition.earlyPhase_eq_p1_iff
#print axioms ThreePhaseComposition.earlyPhase_eq_p2_iff
#print axioms ThreePhaseComposition.latePhase_eq_p1_iff
#print axioms ThreePhaseComposition.latePhase_eq_p2_iff
#print axioms ThreePhaseComposition.protocolPhase_eq_p2_postAudit
#print axioms ThreePhaseComposition.protocolPhase_of_postAudit
#print axioms ThreePhaseComposition.preP3_restricted_bellman
#print axioms ThreePhaseComposition.late_composedPotential_eq_three
#print axioms ThreePhaseComposition.early_composedPotential_eq_three
#print axioms ThreePhaseComposition.compose_three
#print axioms ThreePhaseComposition.protocol_three_phase_supersolution
#print axioms ThreePhaseComposition.threePhasePotential_initial_le
#print axioms ThreePhaseComposition.postAudit_preserved_of_commitAtomic
#print axioms ThreePhaseComposition.p2_no_return_of_commitAtomic
