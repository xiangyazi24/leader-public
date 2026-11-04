import Leader.Wu.ZeroDivisible.CompareTokenFrame
import Leader.Wu.ZeroDivisible.TrafficLand

namespace PPLLAstraR5CompareRank

open PPLL PPLLFableDesignR1 PPLLAstraDesign3
open PPLLAstraR5CompareB PPLLAstraR5SelectedWave
open PPLLAstraR5CompareTokenFrame

set_option autoImplicit false

/-! ## Shared pair coordinates -/

private theorem pairP_eq {ψ : Nat} (l r : AgentState ψ) :
    PPLLAstraR5TrafficMove.P l r =
      PPLLAstraR5TrafficLand.P l +
        PPLLAstraR5TrafficLand.P r := by
  have h :=
    congrArg Prod.fst
      (PPLLAstraR5TrafficLand.pair_coordinates l r)
  simpa using h

private theorem pairZ_eq {ψ : Nat} (l r : AgentState ψ) :
    PPLLAstraR5TrafficMove.Z l r =
      PPLLAstraR5TrafficLand.Z l +
        PPLLAstraR5TrafficLand.Z r := by
  have h :=
    congrArg Prod.snd
      (PPLLAstraR5TrafficLand.pair_coordinates l r)
  simpa using h

private theorem holder_coordinates_of_frame
    {ψ : Nat} {a u : AgentState ψ}
    (h : Frame a u) :
    PPLLAstraR5TrafficLand.P a =
        PPLLAstraR5TrafficLand.P u ∧
      PPLLAstraR5TrafficLand.Z a =
        PPLLAstraR5TrafficLand.Z u := by
  constructor
  · simp [PPLLAstraR5TrafficLand.P, h.label, h.token]
  · simp [PPLLAstraR5TrafficLand.Z, h.token]

private theorem pair_coordinates_of_frame
    {ψ : Nat} {a b l r : AgentState ψ}
    (hl : Frame a l) (hr : Frame b r) :
    PPLLAstraR5TrafficMove.P a b =
        PPLLAstraR5TrafficMove.P l r ∧
      PPLLAstraR5TrafficMove.Z a b =
        PPLLAstraR5TrafficMove.Z l r := by
  have hcl := holder_coordinates_of_frame hl
  have hcr := holder_coordinates_of_frame hr
  have hpa := pairP_eq a b
  have hpl := pairP_eq l r
  have hza := pairZ_eq a b
  have hzl := pairZ_eq l r
  constructor <;> omega

private theorem own_of_frame_role
    {ψ j b : Nat} {a u : AgentState ψ}
    (h : Frame a u)
    (hlab : u.label.val = j)
    (hpath : u.path = .some j b) :
    PPLLAstraR5TrafficLand.Own a := by
  refine ⟨b, ?_⟩
  calc
    a.path = u.path := h.path
    _ = .some j b := hpath
    _ = .some u.label.val b := by rw [hlab]
    _ = .some a.label.val b := by rw [h.label]

/-! ## Exact dropStray facts -/

/-- dropStray changes neither main path nor physical label. -/
theorem dropStray_frame {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).1.path = l.path ∧
    (dropStray l r).2.path = r.path ∧
    (dropStray l r).1.label = l.label ∧
    (dropStray l r).2.label = r.label := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr] <;>
    repeat (first | split) <;> simp_all

/-- On the left, dropStray removes exactly A1@0 among zero readers.
Thus every remaining zero reader is exactly a backward A2 fire. -/
theorem dropStray_left_coordinates {ψ : Nat}
    (l r : AgentState ψ) :
    PPLLAstraR5TrafficLand.P (dropStray l r).1 ≤
        PPLLAstraR5TrafficLand.P l ∧
      PPLLAstraR5TrafficLand.Z (dropStray l r).1 =
        PPLLAstraR5TrafficLand.fires 2 (dropStray l r).1 := by
  cases ht : l.path2 with
  | none =>
      simp [dropStray, ht,
        PPLLAstraR5TrafficLand.P,
        PPLLAstraR5TrafficLand.Z,
        PPLLAstraR5TrafficLand.fires]
  | some t =>
      rcases t with ⟨tl, tb, tp, ta⟩
      by_cases h1 : ta = 1
      · subst ta
        by_cases hp : tp = 0
        · subst tp
          simp [dropStray, ht,
            PPLLAstraR5TrafficLand.P,
            PPLLAstraR5TrafficLand.Z,
            PPLLAstraR5TrafficLand.fires]
        · simp [dropStray, ht, hp,
            PPLLAstraR5TrafficLand.P,
            PPLLAstraR5TrafficLand.Z,
            PPLLAstraR5TrafficLand.fires]
      · by_cases h2 : ta = 2
        · subst ta
          by_cases hp : tp = 0
          · subst tp
            simp [dropStray, ht, h1,
              PPLLAstraR5TrafficLand.P,
              PPLLAstraR5TrafficLand.Z,
              PPLLAstraR5TrafficLand.fires]
          · simp [dropStray, ht, h1, hp,
              PPLLAstraR5TrafficLand.P,
              PPLLAstraR5TrafficLand.Z,
              PPLLAstraR5TrafficLand.fires]
        · simp [dropStray, ht, h1, h2,
            PPLLAstraR5TrafficLand.P,
            PPLLAstraR5TrafficLand.Z,
            PPLLAstraR5TrafficLand.fires]

/-- Symmetrically, on the right every remaining zero reader is A1@0. -/
theorem dropStray_right_coordinates {ψ : Nat}
    (l r : AgentState ψ) :
    PPLLAstraR5TrafficLand.P (dropStray l r).2 ≤
        PPLLAstraR5TrafficLand.P r ∧
      PPLLAstraR5TrafficLand.Z (dropStray l r).2 =
        PPLLAstraR5TrafficLand.fires 1 (dropStray l r).2 := by
  cases ht : r.path2 with
  | none =>
      simp [dropStray, ht,
        PPLLAstraR5TrafficLand.P,
        PPLLAstraR5TrafficLand.Z,
        PPLLAstraR5TrafficLand.fires]
  | some t =>
      rcases t with ⟨tl, tb, tp, ta⟩
      by_cases h2 : ta = 2
      · subst ta
        by_cases hp : tp = 0
        · subst tp
          simp [dropStray, ht,
            PPLLAstraR5TrafficLand.P,
            PPLLAstraR5TrafficLand.Z,
            PPLLAstraR5TrafficLand.fires]
        · simp [dropStray, ht, hp,
            PPLLAstraR5TrafficLand.P,
            PPLLAstraR5TrafficLand.Z,
            PPLLAstraR5TrafficLand.fires]
      · by_cases h1 : ta = 1
        · subst ta
          by_cases hp : tp = 0
          · subst tp
            simp [dropStray, ht, h2,
              PPLLAstraR5TrafficLand.P,
              PPLLAstraR5TrafficLand.Z,
              PPLLAstraR5TrafficLand.fires]
          · simp [dropStray, ht, h2, hp,
              PPLLAstraR5TrafficLand.P,
              PPLLAstraR5TrafficLand.Z,
              PPLLAstraR5TrafficLand.fires]
        · simp [dropStray, ht, h1, h2,
            PPLLAstraR5TrafficLand.P,
            PPLLAstraR5TrafficLand.Z,
            PPLLAstraR5TrafficLand.fires]

theorem dropStray_pair_P_le {ψ : Nat}
    (l r : AgentState ψ) :
    PPLLAstraR5TrafficMove.P
        (dropStray l r).1 (dropStray l r).2 ≤
      PPLLAstraR5TrafficMove.P l r := by
  have hl := dropStray_left_coordinates l r
  have hr := dropStray_right_coordinates l r
  have hn := pairP_eq (dropStray l r).1 (dropStray l r).2
  have ho := pairP_eq l r
  omega

/-- Exact post-drop decomposition needed by pair_landing_coordinates. -/
theorem dropStray_pair_Z_exact {ψ : Nat}
    (l r : AgentState ψ) :
    PPLLAstraR5TrafficMove.Z
        (dropStray l r).1 (dropStray l r).2 =
      PPLLAstraR5TrafficLand.fires 2 (dropStray l r).1 +
        PPLLAstraR5TrafficLand.fires 1 (dropStray l r).2 := by
  have hl := dropStray_left_coordinates l r
  have hr := dropStray_right_coordinates l r
  have hz := pairZ_eq (dropStray l r).1 (dropStray l r).2
  omega

theorem dropStray_own {ψ : Nat}
    (l r : AgentState ψ)
    (hl : PPLLAstraR5TrafficLand.Own l)
    (hr : PPLLAstraR5TrafficLand.Own r) :
    PPLLAstraR5TrafficLand.Own (dropStray l r).1 ∧
      PPLLAstraR5TrafficLand.Own (dropStray l r).2 := by
  have hf := dropStray_frame l r
  rcases hl with ⟨bl, hpl⟩
  rcases hr with ⟨br, hpr⟩
  constructor
  · refine ⟨bl, ?_⟩
    calc
      (dropStray l r).1.path = l.path := hf.1
      _ = .some l.label.val bl := hpl
      _ = .some (dropStray l r).1.label.val bl := by
        rw [hf.2.2.1]
  · refine ⟨br, ?_⟩
    calc
      (dropStray l r).2.path = r.path := hf.2.1
      _ = .some r.label.val br := hpr
      _ = .some (dropStray l r).2.label.val br := by
        rw [hf.2.2.2]

/-! ## Literal compareLifecycle factor -/

/-- The initial pathless/non-PRODUCE reset in compareLifecycle is inert here
because the left main path is occupied. -/
private theorem compareLifecycle_factor
    {ψ j bL : Nat} (κ : Nat)
    (l r : AgentState ψ)
    (hpL : l.path = .some j bL) :
    compareLifecycle κ l r =
      let q := beforeDrop l r
      let q := dropStray q.1 q.2
      (landBackward q.1, landForward κ false true q.2) := by
  simp [PPLLAstraDesign3.compareLifecycle,
    PPLLAstraR5CompareTokenFrame.beforeDrop, hpL]

/-! ## Actual pair rank theorem -/

private theorem compareLifecycle_rank_core
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hlabL : l.label.val = j)
    (hlabR : r.label.val = k)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    PPLLAstraR5TrafficMove.P
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 ≤
      PPLLAstraR5TrafficMove.P l r ∧
    PPLLAstraR5TrafficMove.Z
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 = 0 := by
  let b := beforeDrop l r
  let d := dropStray b.1 b.2

  have hf0 :=
    beforeDrop_frame h4 l r hj hk hpL hpR hBL hBR hboundary
  have hf : Frame b.1 l ∧ Frame b.2 r := by
    change Frame b.1 l ∧ Frame b.2 r at hf0
    exact hf0

  have hframe := pair_coordinates_of_frame hf.1 hf.2

  have hobL : PPLLAstraR5TrafficLand.Own b.1 :=
    own_of_frame_role hf.1 hlabL hpL
  have hobR : PPLLAstraR5TrafficLand.Own b.2 :=
    own_of_frame_role hf.2 hlabR hpR

  have hod : PPLLAstraR5TrafficLand.Own d.1 ∧
      PPLLAstraR5TrafficLand.Own d.2 := by
    dsimp [d]
    exact dropStray_own b.1 b.2 hobL hobR

  have hdropP :
      PPLLAstraR5TrafficMove.P d.1 d.2 ≤
        PPLLAstraR5TrafficMove.P b.1 b.2 := by
    dsimp [d]
    exact dropStray_pair_P_le b.1 b.2

  have hdropZ :
      PPLLAstraR5TrafficMove.Z d.1 d.2 =
        PPLLAstraR5TrafficLand.fires 2 d.1 +
          PPLLAstraR5TrafficLand.fires 1 d.2 := by
    dsimp [d]
    exact dropStray_pair_Z_exact b.1 b.2

  have hland :=
    PPLLAstraR5TrafficLand.pair_landing_coordinates
      h4 κ d.1 d.2 hod.1 hod.2

  have heq :
      compareLifecycle κ l r =
        (landBackward d.1, landForward κ false true d.2) := by
    dsimp [d, b]
    simpa using compareLifecycle_factor κ l r hpL

  rw [heq]
  simp only [Prod.fst, Prod.snd]
  constructor
  · omega
  · omega

/-- Every position-zero reader is discharged by the complete COMPARE stage
under the B/full-own successor premises. -/
theorem compareLifecycle_zero_Z
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hlabL : l.label.val = j)
    (hlabR : r.label.val = k)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    PPLLAstraR5TrafficMove.Z
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 = 0 :=
  (compareLifecycle_rank_core h4 κ l r hj hlabL hlabR hk hpL hpR
    hBL hBR hboundary).2

/-- First requested headline: both shared coordinates are nonincreasing. -/
theorem compareLifecycle_coordinates
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hlabL : l.label.val = j)
    (hlabR : r.label.val = k)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r)) :
    PPLLAstraR5TrafficMove.P
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 ≤
      PPLLAstraR5TrafficMove.P l r ∧
    PPLLAstraR5TrafficMove.Z
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 ≤
      PPLLAstraR5TrafficMove.Z l r := by
  have h := compareLifecycle_rank_core
    h4 κ l r hj hlabL hlabR hk hpL hpR hBL hBR hboundary
  constructor
  · exact h.1
  · rw [h.2]
    omega

/-- Second requested headline. Because the output Z-coordinate is actually zero,
positive input Z gives strict lexicographic decrease with no action bound. -/
theorem compareLifecycle_strict_of_Z_pos
    {ψ j k bL bR : Nat}
    (h4 : 4 ≤ ψ) (κ : Nat)
    (l r : AgentState ψ)
    (hj : j < ψ)
    (hlabL : l.label.val = j)
    (hlabR : r.label.val = k)
    (hk : k = (j + 1) % ψ)
    (hpL : l.path = .some j bL)
    (hpR : r.path = .some k bR)
    (hBL : BState ψ j l.state)
    (hBR : BState ψ k r.state)
    (hboundary : j + 1 = ψ → HasToken (l,r))
    (hz : 0 < PPLLAstraR5TrafficMove.Z l r) :
    PPLLAstraR5TrafficMove.P
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 <
      PPLLAstraR5TrafficMove.P l r ∨
    (PPLLAstraR5TrafficMove.P
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 =
       PPLLAstraR5TrafficMove.P l r ∧
     PPLLAstraR5TrafficMove.Z
        (compareLifecycle κ l r).1
        (compareLifecycle κ l r).2 <
       PPLLAstraR5TrafficMove.Z l r) := by
  have h := compareLifecycle_rank_core
    h4 κ l r hj hlabL hlabR hk hpL hpR hBL hBR hboundary
  by_cases hp :
      PPLLAstraR5TrafficMove.P
          (compareLifecycle κ l r).1
          (compareLifecycle κ l r).2 <
        PPLLAstraR5TrafficMove.P l r
  · exact Or.inl hp
  · right
    constructor
    · omega
    · omega

/-- A bounded internal B-edge with an active backward reader inhabits the
strict theorem's premises. Its ancillary fields are chosen neutral only for
this executable witness, not for the general rank interface. -/
private def sampleCell (label : Fin 4) (state : MainState)
    (token : Option Path2Info) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := state, path := .some label.val 0,
    reset := false, carry := false, count := 0,
    label := label, h_field := false,
    path2 := token, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

private def sampleLeft : AgentState 4 :=
  sampleCell 1 .depart (some ⟨1, 0, 0, 2⟩)
private def sampleRight : AgentState 4 := sampleCell 2 .depart none

theorem sample_rank_premises :
    sampleLeft.label.val = 1 ∧ sampleRight.label.val = 2 ∧
    sampleLeft.path = .some 1 0 ∧ sampleRight.path = .some 2 0 ∧
    BState 4 1 sampleLeft.state ∧ BState 4 2 sampleRight.state ∧
    (1 + 1 = 4 → HasToken (sampleLeft,sampleRight)) ∧
    0 < PPLLAstraR5TrafficMove.Z sampleLeft sampleRight ∧
    AgentState.inProtocolDomain 2 sampleLeft ∧
    AgentState.inProtocolDomain 2 sampleRight := by
  simp [sampleLeft, sampleRight, sampleCell,
    BState, MidState, PenState, HasToken,
    PPLLAstraR5TrafficMove.Z, PPLLAstraR5TrafficMove.potential,
    AgentState.inProtocolDomain]

#print axioms dropStray_left_coordinates
#print axioms dropStray_right_coordinates
#print axioms dropStray_pair_P_le
#print axioms dropStray_pair_Z_exact
#print axioms compareLifecycle_coordinates
#print axioms compareLifecycle_strict_of_Z_pos
#check @compareLifecycle_zero_Z
#print axioms compareLifecycle_zero_Z
#check @sample_rank_premises
#print axioms sample_rank_premises

end PPLLAstraR5CompareRank
