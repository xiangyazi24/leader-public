import Leader.AAFJ.TwoBarrier.GapWalkBoundary
set_option autoImplicit false
set_option Elab.async false
namespace AAFJPK.SignedBalanceCounterexample
open BarrierAlgebra PersistentBarrierService TwoEndpointServiceClock TwoEndpointColoredClock
instance instDecidablePreContact {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Decidable (PreContact hk ring C b) := by
  unfold PreContact; infer_instance
instance instDecidableContactAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Decidable (ContactAt hk ring C b) := by
  unfold ContactAt
  infer_instance

def ring10 : DirectedRing 10 := ⟨by omega⟩
theorem hn10 : 2 < 10 := by decide
def base (l : Fin 3) (p h : Bool) : State 3 :=
 {bullet:=false,leader:=false,label:=l,probe:=p,phase:=h}
def lab10 (i : Nat) : Fin 3 := match i with
 | 0 => 0 | 1 => 2 | 2 => 0 | 3 => 2 | 4 => 0
 | 5 => 1 | 6 => 2 | 7 => 0 | 8 => 1 | _ => 2
def C0 (i:Fin 10):State 3 := base (lab10 i.val) false (decide (i.val=2))
def C1 (i:Fin 10):State 3 := base (lab10 i.val) (decide (i.val=1)) (decide (i.val=0 ∨ i.val=2))
def C2 (i:Fin 10):State 3 := base (lab10 i.val) (decide (i.val=2)) (decide (i.val=0 ∨ i.val=2))

theorem fin10_cases (e : Fin 10) : e=0∨e=1∨e=2∨e=3∨e=4∨e=5∨e=6∨e=7∨e=8∨e=9 := by
 rcases e with ⟨e,he⟩
 simp only [Fin.ext_iff]
 omega

macro "fin10" : tactic => `(tactic|
  first | rfl | (rcases fin10_cases ‹Fin 10› with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl))

theorem step0_0 : (protocol 3 (by decide)).step ring10 C0 0 = C1 := by
 funext i
 rcases fin10_cases i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
 simp [PopulationProtocol.step,protocol,transition,barrierStep,nonBarrierStep,probeHitsBarrier,
   DirectedRing.rightNeighbor,IsBarrier,succLabel,ring10,C0,C1,base,lab10] <;> decide +kernel
theorem step1_1 : (protocol 3 (by decide)).step ring10 C1 1 = C2 := by
 funext i
 rcases fin10_cases i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
 simp [PopulationProtocol.step,protocol,transition,barrierStep,nonBarrierStep,probeHitsBarrier,
   DirectedRing.rightNeighbor,IsBarrier,succLabel,ring10,C0,C1,C2,base,lab10] <;> decide +kernel
theorem step0_quiet (e : Fin 10) (h0 : e ≠ 0) (h2 : e ≠ 2) :
    (protocol 3 (by decide)).step ring10 C0 e = C0 := by
  rcases fin10_cases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try contradiction
  all_goals funext i
  all_goals rcases fin10_cases i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [PopulationProtocol.step,protocol,transition,barrierStep,nonBarrierStep,probeHitsBarrier,
      DirectedRing.rightNeighbor,IsBarrier,succLabel,C0,base,lab10] <;> decide +kernel

theorem step1_quiet (e : Fin 10) (h1 : e ≠ 1) (h2 : e ≠ 2) :
    (protocol 3 (by decide)).step ring10 C1 e = C1 := by
  rcases fin10_cases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try contradiction
  all_goals funext i
  all_goals rcases fin10_cases i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [PopulationProtocol.step,protocol,transition,barrierStep,nonBarrierStep,probeHitsBarrier,
      DirectedRing.rightNeighbor,IsBarrier,succLabel,C1,base,lab10] <;> decide +kernel

theorem step2_quiet (e : Fin 10) (h0 : e ≠ 0) (h2 : e ≠ 2) :
    (protocol 3 (by decide)).step ring10 C2 e = C2 := by
  rcases fin10_cases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try contradiction
  all_goals funext i
  all_goals rcases fin10_cases i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [PopulationProtocol.step,protocol,transition,barrierStep,nonBarrierStep,probeHitsBarrier,
      DirectedRing.rightNeighbor,IsBarrier,succLabel,C2,base,lab10] <;> decide +kernel

theorem pre0r : PreContact (by decide) ring10 C0 0 := by decide +kernel
theorem pre0f : PreContact (by decide) ring10 C0 2 := by decide +kernel

theorem pre1r : PreContact (by decide) ring10 C1 0 := by decide +kernel
theorem pre1f : PreContact (by decide) ring10 C1 2 := by decide +kernel
theorem pre2r : PreContact (by decide) ring10 C2 0 := by decide +kernel
theorem pre2f : PreContact (by decide) ring10 C2 2 := by decide +kernel

def st0 : ActivePair (n:=10) (k:=3) (by decide) ring10 :=
 {config:=C0,rear:=0,front:=2,ne:=by decide,rearPre:=pre0r,frontPre:=pre0f}
def st1 : ActivePair (n:=10) (k:=3) (by decide) ring10 :=
 {config:=C1,rear:=0,front:=2,ne:=by decide,rearPre:=pre1r,frontPre:=pre1f}
def st2 : ActivePair (n:=10) (k:=3) (by decide) ring10 :=
 {config:=C2,rear:=0,front:=2,ne:=by decide,rearPre:=pre2r,frontPre:=pre2f}

theorem colored_step0_zero : coloredStep hn10 st0 0 = .active st1 := by
  classical
  simp only [coloredStep, st0, step0_0, pre1r, pre1f, ↓reduceDIte]
  rfl

theorem colored_step1_one : coloredStep hn10 st1 1 = .active st2 := by
  classical
  simp only [coloredStep, st1, step1_1, pre2r, pre2f, ↓reduceDIte]
  rfl


open PayloadFiniteStoppingTree

def observedKind : PayloadNode (ActivePair (n:=10) (k:=3) (by decide) ring10)
      (TerminalPayload (n:=10) (k:=3) (by decide) ring10) Empty → Option TerminalKind
  | .active _ => none
  | .success p => some p.kind
  | .failure f => nomatch f

theorem colored_step0_quiet (e : Fin 10) (h0 : e ≠ 0) (h2 : e ≠ 2) :
    coloredStep hn10 st0 e = .active st0 := by
  classical
  simp [coloredStep, st0, step0_quiet e h0 h2, pre0r, pre0f]

theorem colored_step1_quiet (e : Fin 10) (h1 : e ≠ 1) (h2 : e ≠ 2) :
    coloredStep hn10 st1 e = .active st1 := by
  classical
  simp [coloredStep, st1, step1_quiet e h1 h2, pre1r, pre1f]

theorem colored_step2_quiet (e : Fin 10) (h0 : e ≠ 0) (h2 : e ≠ 2) :
    coloredStep hn10 st2 e = .active st2 := by
  classical
  simp [coloredStep, st2, step2_quiet e h0 h2, pre2r, pre2f]

def D0F : Fin 10 → State 3 := (protocol 3 (by decide)).step ring10 C0 2
def D1F : Fin 10 → State 3 := (protocol 3 (by decide)).step ring10 C1 2
def D2F : Fin 10 → State 3 := (protocol 3 (by decide)).step ring10 C2 2
def D2C : Fin 10 → State 3 := (protocol 3 (by decide)).step ring10 C2 0

theorem D0F_rear_pre : PreContact (by decide) ring10 D0F 0 := by decide +kernel
theorem D0F_front_not_pre : ¬ PreContact (by decide) ring10 D0F 2 := by decide +kernel
theorem D0F_front_not_contact : ¬ ContactAt (by decide) ring10 D0F 2 := by decide +kernel

theorem D1F_rear_pre : PreContact (by decide) ring10 D1F 0 := by decide +kernel
theorem D1F_front_not_pre : ¬ PreContact (by decide) ring10 D1F 2 := by decide +kernel
theorem D1F_front_not_contact : ¬ ContactAt (by decide) ring10 D1F 2 := by decide +kernel

theorem D2F_rear_pre : PreContact (by decide) ring10 D2F 0 := by decide +kernel
theorem D2F_front_not_pre : ¬ PreContact (by decide) ring10 D2F 2 := by decide +kernel
theorem D2F_front_not_contact : ¬ ContactAt (by decide) ring10 D2F 2 := by decide +kernel

theorem D2C_rear_not_pre : ¬ PreContact (by decide) ring10 D2C 0 := by decide +kernel
theorem D2C_rear_not_contact : ¬ ContactAt (by decide) ring10 D2C 0 := by decide +kernel
theorem D2C_front_contact : ContactAt (by decide) ring10 D2C 2 := by decide +kernel

theorem colored0_front : observedKind (coloredStep hn10 st0 2) = some .frontAdvance := by
  classical
  have hD : (protocol 3 (by decide)).step ring10 C0 2 = D0F := rfl
  simp [observedKind, coloredStep, st0, hD, D0F_rear_pre,
    D0F_front_not_pre, D0F_front_not_contact]
theorem colored1_front : observedKind (coloredStep hn10 st1 2) = some .frontAdvance := by
  classical
  have hD : (protocol 3 (by decide)).step ring10 C1 2 = D1F := rfl
  simp [observedKind, coloredStep, st1, hD, D1F_rear_pre,
    D1F_front_not_pre, D1F_front_not_contact]
theorem colored2_front : observedKind (coloredStep hn10 st2 2) = some .frontAdvance := by
  classical
  have hD : (protocol 3 (by decide)).step ring10 C2 2 = D2F := rfl
  simp [observedKind, coloredStep, st2, hD, D2F_rear_pre,
    D2F_front_not_pre, D2F_front_not_contact]
theorem colored2_contact : observedKind (coloredStep hn10 st2 0) = some .contact := by
  classical
  have hD : (protocol 3 (by decide)).step ring10 C2 0 = D2C := rfl
  simp [observedKind, coloredStep, st2, hD, D2C_rear_not_pre,
    D2C_rear_not_contact, D2C_front_contact]


structure RaceMass where
  s0 : Nat
  s1 : Nat
  s2 : Nat
  front : Nat
  contact : Nat

def RaceMass.next (x : RaceMass) : RaceMass :=
  { s0 := 8 * x.s0
    s1 := x.s0 + 8 * x.s1
    s2 := x.s1 + 8 * x.s2
    front := 10 * x.front + x.s0 + x.s1 + x.s2
    contact := 10 * x.contact + x.s2 }

def raceMass : Nat → RaceMass
  | 0 => ⟨1, 0, 0, 0, 0⟩
  | T + 1 => (raceMass T).next

theorem race_harmonic : ∀ T,
    (raceMass T).s0 + 2 * (raceMass T).s1 + 4 * (raceMass T).s2 +
      8 * (raceMass T).contact = 10 ^ T := by
  intro T
  induction T with
  | zero => decide
  | succ T ih =>
      simp only [raceMass, RaceMass.next, Nat.pow_succ]
      omega

theorem race_front_minus_seven_contact : ∀ T,
    (raceMass T).front = 7 * (raceMass T).contact +
      (raceMass T).s1 + 3 * (raceMass T).s2 := by
  intro T
  induction T with
  | zero => decide
  | succ T ih =>
      simp only [raceMass, RaceMass.next]
      omega

theorem race_contact_mono (T : Nat) :
    (raceMass T).contact ≤ (raceMass (T + 1)).contact := by
  rw [show T + 1 = Nat.succ T by omega]
  simp only [raceMass, RaceMass.next]
  omega

theorem race_contact_pos_of_three_le {T : Nat} (hT : 3 ≤ T) :
    0 < (raceMass T).contact := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hT
  induction u with
  | zero => decide
  | succ u ih =>
      have ih' : 0 < (raceMass (3 + u)).contact := by
        simpa [Nat.add_comm] using ih
      rw [show 3 + Nat.succ u = (3 + u) + 1 by omega]
      exact Nat.lt_of_lt_of_le ih' (race_contact_mono (3 + u))

theorem race_signed_balance_fails_of_three_le {T : Nat} (hT : 3 ≤ T) :
    ¬ (((raceMass T).front : Int) * (10 - 2 * 2) ≤
      ((raceMass T).front : Int) +
        ((raceMass T).contact : Int) * TwoEndpointGapBoundary.gapPhi 10 2) := by
  have hfc := race_front_minus_seven_contact T
  have hc := race_contact_pos_of_three_le hT
  change ¬ (((raceMass T).front : Int) * 6 ≤
    ((raceMass T).front : Int) + ((raceMass T).contact : Int) * 16)
  omega

private theorem colorMass_success_formula
    (color : TerminalKind)
    (p : TerminalPayload (n:=10) (k:=3) (by decide) ring10) : ∀ T,
    colorMass hn10 color (.success p) T =
      if p.kind = color then 10 ^ T else 0 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [colorMass, ih, Nat.pow_succ]
      split <;> omega

private theorem terminal_colorMass
    (st : ActivePair (n:=10) (k:=3) (by decide) ring10)
    (e : Fin 10) (kind color : TerminalKind)
    (hknd : observedKind (coloredStep hn10 st e) = some kind) : ∀ T,
    colorMass hn10 color (coloredStep hn10 st e) T =
      if kind = color then 10 ^ T else 0 := by
  intro T
  cases h : coloredStep hn10 st e with
  | active next => simp [observedKind, h] at hknd
  | success p =>
      have hp : p.kind = kind := by simpa [observedKind, h] using hknd
      rw [colorMass_success_formula]
      simp [hp]
  | failure f => exact f.elim


private theorem terminal_step_mass
    (st : ActivePair (n:=10) (k:=3) (by decide) ring10)
    (e : Fin 10) (kind color : TerminalKind)
    (hknd : observedKind (coloredStep hn10 st e) = some kind) (T : Nat) :
    (match coloredStep hn10 st e with
      | .active next => colorMass hn10 color (.active next) T
      | .success p => colorMass hn10 color (.success p) T
      | .failure z => nomatch z) = if kind = color then 10^T else 0 := by
  cases hnode : coloredStep hn10 st e with
  | active next =>
      rw [hnode] at hknd
      simp [observedKind] at hknd
  | success p =>
      rw [hnode] at hknd
      have hp : p.kind = kind := by simpa [observedKind] using hknd
      simp only
      rw [colorMass_success_formula]
      simp [hp]
  | failure z => exact z.elim

noncomputable def frontMass0 (T : Nat) := colorMass hn10 .frontAdvance (.active st0) T
noncomputable def frontMass1 (T : Nat) := colorMass hn10 .frontAdvance (.active st1) T
noncomputable def frontMass2 (T : Nat) := colorMass hn10 .frontAdvance (.active st2) T

theorem frontMass0_succ (T : Nat) : frontMass0 (T+1) =
    8 * frontMass0 T + frontMass1 T + 10^T := by
  simp only [frontMass0, frontMass1, colorMass]
  have expand (g : Fin 10 → Nat) :
      List.ofFn g = [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9] := rfl
  rw [expand]
  dsimp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [colored_step0_zero,
      colored_step0_quiet 1 (by decide) (by decide)]
  cases hnode : coloredStep hn10 st0 2 with
  | active next =>
      have h := colored0_front
      rw [hnode] at h
      simp [observedKind] at h
  | success p =>
      have hp : p.kind = .frontAdvance := by
        have h := colored0_front
        rw [hnode] at h
        simpa [observedKind] using h
      simp only
      rw [colorMass_success_formula]
      simp [hp]
      rw [colored_step0_quiet 3 (by decide) (by decide),
          colored_step0_quiet 4 (by decide) (by decide),
          colored_step0_quiet 5 (by decide) (by decide),
          colored_step0_quiet 6 (by decide) (by decide),
          colored_step0_quiet 7 (by decide) (by decide),
          colored_step0_quiet 8 (by decide) (by decide),
          colored_step0_quiet 9 (by decide) (by decide)]
      simp
      omega
  | failure z => exact z.elim

noncomputable def cm (color : TerminalKind)
    (st : ActivePair (n:=10) (k:=3) (by decide) ring10) (T : Nat) :=
  colorMass hn10 color (.active st) T

theorem cm0_succ (color : TerminalKind) (T : Nat) : cm color st0 (T+1) =
    8 * cm color st0 T + cm color st1 T +
      (if TerminalKind.frontAdvance = color then 10^T else 0) := by
  simp only [cm, colorMass]
  have expand (g : Fin 10 → Nat) :
      List.ofFn g = [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9] := rfl
  rw [expand]
  dsimp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [colored_step0_zero, colored_step0_quiet 1 (by decide) (by decide)]
  cases hnode : coloredStep hn10 st0 2 with
  | active next =>
      have h := colored0_front
      rw [hnode] at h
      simp [observedKind] at h
  | success p =>
      have hp : p.kind = .frontAdvance := by
        have h := colored0_front
        rw [hnode] at h
        simpa [observedKind] using h
      simp only
      rw [colorMass_success_formula]
      simp [hp]
      rw [colored_step0_quiet 3 (by decide) (by decide),
          colored_step0_quiet 4 (by decide) (by decide),
          colored_step0_quiet 5 (by decide) (by decide),
          colored_step0_quiet 6 (by decide) (by decide),
          colored_step0_quiet 7 (by decide) (by decide),
          colored_step0_quiet 8 (by decide) (by decide),
          colored_step0_quiet 9 (by decide) (by decide)]
      simp
      omega
  | failure z => exact z.elim

theorem cm1_succ (color : TerminalKind) (T : Nat) : cm color st1 (T+1) =
    8 * cm color st1 T + cm color st2 T +
      (if TerminalKind.frontAdvance = color then 10^T else 0) := by
  simp only [cm, colorMass]
  have expand (g : Fin 10 → Nat) :
      List.ofFn g = [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9] := rfl
  rw [expand]
  dsimp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [colored_step1_quiet 0 (by decide) (by decide), colored_step1_one]
  cases hnode : coloredStep hn10 st1 2 with
  | active next =>
      have h := colored1_front
      rw [hnode] at h
      simp [observedKind] at h
  | success p =>
      have hp : p.kind = .frontAdvance := by
        have h := colored1_front
        rw [hnode] at h
        simpa [observedKind] using h
      simp only
      rw [colorMass_success_formula]
      simp [hp]
      rw [colored_step1_quiet 3 (by decide) (by decide),
          colored_step1_quiet 4 (by decide) (by decide),
          colored_step1_quiet 5 (by decide) (by decide),
          colored_step1_quiet 6 (by decide) (by decide),
          colored_step1_quiet 7 (by decide) (by decide),
          colored_step1_quiet 8 (by decide) (by decide),
          colored_step1_quiet 9 (by decide) (by decide)]
      simp
      omega
  | failure z => exact z.elim

theorem cm2_succ (color : TerminalKind) (T : Nat) : cm color st2 (T+1) =
    8 * cm color st2 T +
      (if TerminalKind.contact = color then 10^T else 0) +
      (if TerminalKind.frontAdvance = color then 10^T else 0) := by
  simp only [cm, colorMass]
  have expand (g : Fin 10 → Nat) :
      List.ofFn g = [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9] := rfl
  rw [expand]
  dsimp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  cases hzero : coloredStep hn10 st2 0 with
  | active next =>
      have h := colored2_contact
      rw [hzero] at h
      simp [observedKind] at h
  | success p0 =>
      have hp0 : p0.kind = .contact := by
        have h := colored2_contact
        rw [hzero] at h
        simpa [observedKind] using h
      simp only
      rw [colorMass_success_formula]
      simp [hp0]
      rw [colored_step2_quiet 1 (by decide) (by decide)]
      cases htwo : coloredStep hn10 st2 2 with
      | active next =>
          have h := colored2_front
          rw [htwo] at h
          simp [observedKind] at h
      | success p2 =>
          have hp2 : p2.kind = .frontAdvance := by
            have h := colored2_front
            rw [htwo] at h
            simpa [observedKind] using h
          simp only
          rw [colorMass_success_formula]
          simp [hp2]
          rw [colored_step2_quiet 3 (by decide) (by decide),
              colored_step2_quiet 4 (by decide) (by decide),
              colored_step2_quiet 5 (by decide) (by decide),
              colored_step2_quiet 6 (by decide) (by decide),
              colored_step2_quiet 7 (by decide) (by decide),
              colored_step2_quiet 8 (by decide) (by decide),
              colored_step2_quiet 9 (by decide) (by decide)]
          simp
          omega
      | failure z => exact z.elim
  | failure z => exact z.elim

structure BackTriple where
  m0 : Nat
  m1 : Nat
  m2 : Nat

def backTriple (color : TerminalKind) : Nat → BackTriple
  | 0 => ⟨0, 0, 0⟩
  | T + 1 =>
      let b := backTriple color T
      let frontPad := if TerminalKind.frontAdvance = color then 10^T else 0
      let contactPad := if TerminalKind.contact = color then 10^T else 0
      ⟨8*b.m0 + b.m1 + frontPad,
       8*b.m1 + b.m2 + frontPad,
       8*b.m2 + contactPad + frontPad⟩

theorem cm_eq_backTriple (color : TerminalKind) (T : Nat) :
    cm color st0 T = (backTriple color T).m0 ∧
    cm color st1 T = (backTriple color T).m1 ∧
    cm color st2 T = (backTriple color T).m2 := by
  induction T with
  | zero => simp [cm, colorMass, backTriple]
  | succ T ih =>
      rcases ih with ⟨h0, h1, h2⟩
      constructor
      · rw [cm0_succ, h0, h1]
        rfl
      constructor
      · rw [cm1_succ, h1, h2]
        rfl
      · rw [cm2_succ, h2]
        rfl

theorem actual_signed_balance_fails_at_horizon_100 :
    ¬ (((cm .frontAdvance st0 100 : Nat) : Int) * 6 ≤
      ((cm .frontAdvance st0 100 : Nat) : Int) +
        ((cm .contact st0 100 : Nat) : Int) * 16) := by
  have hf := (cm_eq_backTriple .frontAdvance 100).1
  have hc := (cm_eq_backTriple .contact 100).1
  rw [hf, hc]
  decide +kernel


theorem actual_rear_mass_zero_at_horizon_100 :
    cm .rearAdvance st0 100 = 0 := by
  have hr := (cm_eq_backTriple .rearAdvance 100).1
  rw [hr]
  decide +kernel

theorem actual_signed_balance_premise_fails_at_horizon_100 :
    ¬ ((((cm .frontAdvance st0 100 : Nat) : Int) -
          ((cm .rearAdvance st0 100 : Nat) : Int)) *
          ((10 : Int) - 2 * (2 : Int)) ≤
        ((cm .rearAdvance st0 100 + cm .frontAdvance st0 100 : Nat) : Int) +
          ((cm .contact st0 100 : Nat) : Int) *
            TwoEndpointGapBoundary.gapPhi 10 2) := by
  have hf := (cm_eq_backTriple .frontAdvance 100).1
  have hr := (cm_eq_backTriple .rearAdvance 100).1
  have hc := (cm_eq_backTriple .contact 100).1
  rw [hf, hr, hc]
  decide +kernel

end AAFJPK.SignedBalanceCounterexample
