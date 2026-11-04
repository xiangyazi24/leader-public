import Leader.Wu.ZeroDivisible.TrafficArithmetic

/-! Actual token movement decreases the literal traffic weight or is identity.
The equality classification uses only physical successor labels and actions 1–4;
all saved fields and all other agent fields are unrestricted. -/

namespace PPLLAstraR5TrafficMove
open PPLL PPLLFableDesignR1
set_option autoImplicit false

-- Literal numerical definitions from the supplied probe.
def readerRank (ψ : Nat) (t : Path2Info) : Nat :=
  (2*ψ-1)*(ψ-1-t.label) + t.position +
    (if t.action == 2 then ψ else 0) + 1

def weight (ψ j : Nat) (t : Path2Info) : Nat :=
  if t.action == 1 || t.action == 2 then (ψ+1)*readerRank ψ t
  else if t.action == 3 then (if j == ψ-1 then 0 else j+1)+1
  else if t.action == 4 then ψ-1-j+1 else 0

def potential {ψ : Nat} (ψn : Nat) (l r : AgentState ψ) : Nat × Nat :=
  let p := (match l.path2 with
    | none => 0 | some t => weight ψn l.label.val t) +
    (match r.path2 with
    | none => 0 | some t => weight ψn r.label.val t)
  let z := (match l.path2 with
    | some t =>
      if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0
    | none => 0) + (match r.path2 with
    | some t =>
      if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0
    | none => 0)
  (p,z)

abbrev P {ψ : Nat} (l r : AgentState ψ) := (potential ψ l r).1
abbrev Z {ψ : Nat} (l r : AgentState ψ) := (potential ψ l r).2

def Ok (t : Path2Info) : Prop := 1 ≤ t.action ∧ t.action ≤ 4
def OkSlot (o : Option Path2Info) : Prop := ∀ t, o = some t → Ok t
def Adj {ψ : Nat} (l r : AgentState ψ) : Prop :=
  r.label.val = (l.label.val + 1) % ψ

def Selected {ψ : Nat} (l r : AgentState ψ) : Prop :=
  (∃ t, l.path2 = some t ∧ (t.action = 1 ∨ t.action = 4)) ∨
  (∃ t, r.path2 = some t ∧ (t.action = 2 ∨ t.action = 3))

def TerminalControl {ψ : Nat} (u : AgentState ψ) : Prop :=
  ∃ t, u.path2 = some t ∧ u.label.val = ψ-1 ∧
    (t.action = 3 ∨ t.action = 4)
def ZeroReader {ψ : Nat} (u : AgentState ψ) : Prop :=
  ∃ t, u.path2 = some t ∧ (t.action = 1 ∨ t.action = 2) ∧
    t.position = 0

-- A resident token that can move in neither direction.
def Frozen {ψ : Nat} (u : AgentState ψ) : Prop :=
  ∃ t, u.path2 = some t ∧
    canMoveR u t = false ∧ canMoveL u t = false

private theorem four (t : Path2Info) (h : Ok t) :
    t.action = 1 ∨ t.action = 2 ∨ t.action = 3 ∨ t.action = 4 := by
  unfold Ok at h
  omega

private theorem as_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

theorem readerRank_eq (ψ : Nat) (t : Path2Info) :
    readerRank ψ t = PPLLAstraR5MultiReader.readerRank ψ t := by
  rfl

private theorem wpos (ψ j : Nat) (t : Path2Info) (ha : Ok t) :
    0 < weight ψ j t := by
  have hp : 0 < readerRank ψ t := by
    rw [readerRank_eq]
    exact PPLLAstraR5TrafficArithmetic.readerRank_pos ψ t
  have hm := Nat.mul_le_mul_left (ψ+1)
    (show 1 ≤ readerRank ψ t by omega)
  simp only [Nat.mul_one] at hm
  rcases four t ha with h | h | h | h
  · simpa [weight, h] using
      (show 0 < (ψ+1)*readerRank ψ t by omega)
  · simpa [weight, h] using
      (show 0 < (ψ+1)*readerRank ψ t by omega)
  · simpa [weight, h] using
      (show 0 < (if j == ψ-1 then 0 else j+1)+1 by omega)
  · simpa [weight, h] using (show 0 < ψ-1-j+1 by omega)

private theorem rdec (ψ i j : Nat) (t : Path2Info)
    (ha : t.action = 1 ∨ t.action = 2) (hp : 0 < t.position) :
    weight ψ j (dec t) + (ψ+1) = weight ψ i t := by
  have hd := PPLLAstraR5TrafficArithmetic.readerRank_dec ψ t ha hp
  change readerRank ψ (dec t) + 1 = readerRank ψ t at hd
  have hm := congrArg (fun n : Nat => (ψ+1)*n) hd
  simp only [Nat.mul_add, Nat.mul_one] at hm
  rcases ha with h | h <;> simpa [weight, dec, h] using hm

private theorem adj_cases {ψ : Nat} (l r : AgentState ψ) (he : Adj l r) :
    r.label.val = l.label.val+1 ∨
      (l.label.val = ψ-1 ∧ r.label.val = 0) := by
  unfold Adj at he
  have hl := l.label.isLt
  by_cases h : l.label.val+1 < ψ
  · exact Or.inl (he.trans (Nat.mod_eq_of_lt h))
  · have hh : l.label.val+1 = ψ := by omega
    refine Or.inr ⟨by omega, ?_⟩
    simpa [hh] using he

-- Every enabled rightward transport of an allowed token strictly pays.
private theorem wr_lt {ψ : Nat} (hψ : 4 ≤ ψ)
    (l r : AgentState ψ) (he : Adj l r) (t : Path2Info)
    (ha : Ok t) (hm : canMoveR l t = true) :
    weight ψ r.label.val (dec t) < weight ψ l.label.val t := by
  rcases four t ha with h | h | h | h
  · have hp : t.position ≠ 0 := by simpa [canMoveR, h] using hm
    have hd := rdec ψ l.label.val r.label.val t (Or.inl h) (by omega)
    omega
  · simp [canMoveR, h] at hm
  · simp [canMoveR, h] at hm
  · have hn : l.label.val ≠ ψ-1 := by simpa [canMoveR, h] using hm
    have hl := l.label.isLt
    have hr := r.label.isLt
    rcases adj_cases l r he with hs | ⟨hs, _⟩
    · simp [weight, dec, h] <;> omega
    · exact (hn hs).elim

-- A3 is treated separately at ordinary edges and at last -> zero.
private theorem wl_lt {ψ : Nat} (hψ : 4 ≤ ψ)
    (l r : AgentState ψ) (he : Adj l r) (t : Path2Info)
    (ha : Ok t) (hm : canMoveL r t = true) :
    weight ψ l.label.val (dec t) < weight ψ r.label.val t := by
  rcases four t ha with h | h | h | h
  · simp [canMoveL, h] at hm
  · have hp : t.position ≠ 0 := by simpa [canMoveL, h] using hm
    have hd := rdec ψ r.label.val l.label.val t (Or.inr h) (by omega)
    omega
  · have hn : r.label.val ≠ ψ-1 := by simpa [canMoveL, h] using hm
    have hl := l.label.isLt
    have hr := r.label.isLt
    rcases adj_cases l r he with hs | ⟨hs, hz⟩
    · have hln : l.label.val ≠ ψ-1 := by omega
      simp [weight, dec, h, hn, hln] <;> omega
    · have h0 : (0 : Nat) ≠ ψ-1 := by omega
      simp [weight, dec, h, hs, hz, h0]
  · simp [canMoveL, h] at hm

-- This is an exact local classification, not a numerical rank premise.
private theorem frozen_iff {ψ : Nat} (u : AgentState ψ)
    (hu : OkSlot u.path2) :
    Frozen u ↔ TerminalControl u ∨ ZeroReader u := by
  constructor
  · rintro ⟨t, ht, hR, hL⟩
    rcases four t (hu t ht) with h | h | h | h
    · right
      refine ⟨t, ht, Or.inl h, ?_⟩
      simpa [canMoveR, h] using hR
    · right
      refine ⟨t, ht, Or.inr h, ?_⟩
      simpa [canMoveL, h] using hL
    · left
      refine ⟨t, ht, ?_, Or.inl h⟩
      simpa [canMoveL, h] using hL
    · left
      refine ⟨t, ht, ?_, Or.inr h⟩
      simpa [canMoveR, h] using hR
  · rintro (⟨t, ht, hj, ha⟩ | ⟨t, ht, ha, hp⟩)
    · rcases ha with h | h <;>
        exact ⟨t, ht, by simp [canMoveR, h, hj],
          by simp [canMoveL, h, hj]⟩
    · rcases ha with h | h <;>
        exact ⟨t, ht, by simp [canMoveR, h, hp],
          by simp [canMoveL, h, hp]⟩

private theorem fixed_frozen {ψ : Nat} (l r : AgentState ψ)
    (hf : Frozen l ∨ Frozen r) : moveTokens l r = (l,r) := by
  rcases hf with ⟨t, ht, hR, hL⟩ | ⟨t, ht, hR, hL⟩
  · cases hr : r.path2 <;> simp [moveTokens, ht, hr, hR, hL]
  · cases hl : l.path2 <;> simp [moveTokens, ht, hl, hR, hL]

private theorem enableR {ψ : Nat} (u : AgentState ψ) (t : Path2Info)
    (ht : u.path2 = some t) (ha : t.action = 1 ∨ t.action = 4)
    (hn : ¬ Frozen u) : canMoveR u t = true := by
  have hL : canMoveL u t = false := by
    rcases ha with h | h <;> simp [canMoveL, h]
  cases hR : canMoveR u t with
  | false => exact (hn ⟨t, ht, hR, hL⟩).elim
  | true => rfl

private theorem enableL {ψ : Nat} (u : AgentState ψ) (t : Path2Info)
    (ht : u.path2 = some t) (ha : t.action = 2 ∨ t.action = 3)
    (hn : ¬ Frozen u) : canMoveL u t = true := by
  have hR : canMoveR u t = false := by
    rcases ha with h | h <;> simp [canMoveR, h]
  cases hL : canMoveL u t with
  | false => exact (hn ⟨t, ht, hR, hL⟩).elim
  | true => rfl

private theorem live_direction {ψ : Nat} (u : AgentState ψ)
    (t : Path2Info) (ht : u.path2 = some t) (ha : Ok t)
    (hn : ¬ Frozen u) :
    (canMoveR u t = true ∧ rightward t = true) ∨
    (canMoveL u t = true ∧ leftward t = true) := by
  rcases four t ha with h | h | h | h
  · exact Or.inl ⟨enableR u t ht (Or.inl h) hn, by simp [rightward, h]⟩
  · exact Or.inr ⟨enableL u t ht (Or.inl h) hn, by simp [leftward, h]⟩
  · exact Or.inr ⟨enableL u t ht (Or.inr h) hn, by simp [leftward, h]⟩
  · exact Or.inl ⟨enableR u t ht (Or.inr h) hn, by simp [rightward, h]⟩

-- All three two-token branch guards failed. Selection then forces a
-- frozen resident: a zero reader or a terminal control, possibly a blocker.
private theorem stuck {ψ : Nat} (l r : AgentState ψ) (tl tr : Path2Info)
    (hl : l.path2 = some tl) (hr : r.path2 = some tr)
    (al : Ok tl) (ar : Ok tr)
    (hs : ¬ (canMoveR l tl ∧ canMoveL r tr))
    (hR : ¬ (canMoveR l tl ∧ rightward tr ∧ canMoveR r tr))
    (hL : ¬ (canMoveL r tr ∧ leftward tl ∧ canMoveL l tl))
    (sel : Selected l r) : Frozen l ∨ Frozen r := by
  classical
  by_cases fl : Frozen l
  · exact Or.inl fl
  by_cases fr : Frozen r
  · exact Or.inr fr
  exfalso
  have hh : (tl.action = 1 ∨ tl.action = 4) ∨
      (tr.action = 2 ∨ tr.action = 3) := by
    simpa [Selected, hl, hr] using sel
  rcases hh with hh | hh
  · have a := enableR l tl hl hh fl
    rcases live_direction r tr hr ar fr with ⟨b, d⟩ | ⟨b, d⟩
    · exact hR ⟨a, d, b⟩
    · exact hs ⟨a, b⟩
  · have b := enableL r tr hr hh fr
    rcases live_direction l tl hl al fl with ⟨a, d⟩ | ⟨a, d⟩
    · exact hs ⟨a, b⟩
    · exact hL ⟨b, d, a⟩

/-- Exhaustive classification of the literal moveTokens stage.
No occupancy, leader, state, saved-label, bit, or position bound is assumed. -/
theorem moveTokens_classify {ψ : Nat} (hψ : 4 ≤ ψ)
    (l r : AgentState ψ) (he : Adj l r)
    (hla : OkSlot l.path2) (hra : OkSlot r.path2) :
    let q := moveTokens l r
    P q.1 q.2 < P l r ∨
      (q = (l,r) ∧ (Selected l r → Frozen l ∨ Frozen r)) := by
  dsimp only
  cases hl : l.path2 with
  | none =>
    cases hr : r.path2 with
    | none =>
      refine Or.inr ⟨by simp [moveTokens, hl, hr], ?_⟩
      intro sel
      simp [Selected, hl, hr] at sel
    | some tr =>
      have ar : Ok tr := by simpa [OkSlot, hr] using hra
      by_cases b : canMoveL r tr = true
      · left
        have hd := wl_lt hψ l r he tr ar b
        simpa [P, potential, moveTokens, hl, hr, b] using hd
      · refine Or.inr ⟨by simp [moveTokens, hl, hr, b], ?_⟩
        intro sel
        have ha : tr.action = 2 ∨ tr.action = 3 := by
          simpa [Selected, hl, hr] using sel
        have hR : canMoveR r tr = false := by
          rcases ha with h | h <;> simp [canMoveR, h]
        exact Or.inr ⟨tr, hr, hR, as_false b⟩
  | some tl =>
    have al : Ok tl := by simpa [OkSlot, hl] using hla
    cases hr : r.path2 with
    | none =>
      by_cases a : canMoveR l tl = true
      · left
        have hd := wr_lt hψ l r he tl al a
        simpa [P, potential, moveTokens, hl, hr, a] using hd
      · refine Or.inr ⟨by simp [moveTokens, hl, hr, a], ?_⟩
        intro sel
        have ha : tl.action = 1 ∨ tl.action = 4 := by
          simpa [Selected, hl, hr] using sel
        have hL : canMoveL l tl = false := by
          rcases ha with h | h <;> simp [canMoveL, h]
        exact Or.inl ⟨tl, hl, as_false a, hL⟩
    | some tr =>
      have ar : Ok tr := by simpa [OkSlot, hr] using hra
      by_cases hs : canMoveR l tl ∧ canMoveL r tr
      · left
        have dR := wr_lt hψ l r he tl al hs.1
        have dL := wl_lt hψ l r he tr ar hs.2
        have hd : weight ψ l.label.val (dec tr) +
            weight ψ r.label.val (dec tl) <
            weight ψ l.label.val tl + weight ψ r.label.val tr := by omega
        simpa [P, potential, moveTokens, hl, hr, hs] using hd
      · by_cases hR : canMoveR l tl ∧ rightward tr ∧ canMoveR r tr
        · left
          have hp := wpos ψ l.label.val tl al
          have hd : weight ψ r.label.val tr <
              weight ψ l.label.val tl + weight ψ r.label.val tr := by omega
          have hq : moveTokens l r = ({l with path2 := none}, r) := by
            simp only [moveTokens, hl, hr, if_neg hs, if_pos hR]
          rw [hq]
          simpa [P, potential, hl, hr] using hd
        · by_cases hL : canMoveL r tr ∧ leftward tl ∧ canMoveL l tl
          · left
            have hp := wpos ψ r.label.val tr ar
            have hd : weight ψ l.label.val tl <
                weight ψ l.label.val tl + weight ψ r.label.val tr := by omega
            have hq : moveTokens l r = (l, {r with path2 := none}) := by
              simp only [moveTokens, hl, hr, if_neg hs, if_neg hR, if_pos hL]
            rw [hq]
            simpa [P, potential, hl, hr] using hd
          · refine Or.inr ⟨by simp [moveTokens, hl, hr, hs, hR, hL], ?_⟩
            exact stuck l r tl tr hl hr al ar hs hR hL

/-- P never increases; equality of P forces equality of Z. -/
theorem moveTokens_nonincrease {ψ : Nat} (hψ : 4 ≤ ψ)
    (l r : AgentState ψ) (he : Adj l r)
    (hla : OkSlot l.path2) (hra : OkSlot r.path2) :
    let q := moveTokens l r
    P q.1 q.2 ≤ P l r ∧ (P q.1 q.2 = P l r → Z q.1 q.2 = Z l r) := by
  dsimp only
  rcases moveTokens_classify hψ l r he hla hra with hd | ⟨hq, _⟩
  · refine ⟨by omega, ?_⟩
    intro hh
    omega
  · rw [hq]
    exact ⟨Nat.le_refl _, fun _ => rfl⟩

/-- Sharp equality classification on a selected service.
The stop/zero may belong to the other token, not the selected one. -/
theorem selected_equality_iff {ψ : Nat} (hψ : 4 ≤ ψ)
    (l r : AgentState ψ) (he : Adj l r)
    (hla : OkSlot l.path2) (hra : OkSlot r.path2)
    (sel : Selected l r) :
    P (moveTokens l r).1 (moveTokens l r).2 = P l r ↔
      (TerminalControl l ∨ ZeroReader l) ∨
      (TerminalControl r ∨ ZeroReader r) := by
  rw [← frozen_iff l hla, ← frozen_iff r hra]
  constructor
  · intro hh
    rcases moveTokens_classify hψ l r he hla hra with hd | ⟨_, hf⟩
    · omega
    · exact hf sel
  · intro hf
    rw [fixed_frozen l r hf]

-- Raw payloads deliberately exceed every probe payload bound.
example : weight 4 0 ⟨99,12345,1000,1⟩ = 5005 := by decide
example : weight 4 1 (dec (⟨99,12345,1000,1⟩ : Path2Info)) = 5000 := by decide

#print axioms moveTokens_classify
#print axioms moveTokens_nonincrease
#print axioms selected_equality_iff
end PPLLAstraR5TrafficMove
