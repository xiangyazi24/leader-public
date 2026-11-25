import Leader.L4.BStarLapTransfer

/-! The first generated launch of the one-lap observer. -/
namespace L4.Height.ObserverDirty

inductive Slot where
  | empty | trail | front | negative | positive
  deriving DecidableEq

inductive Control where
  | issue | waiting | pending
  deriving DecidableEq

def Slot.Quiet (s : Slot) : Prop := s = .empty ∨ s = .negative ∨ s = .positive

/-- First matching path row in outward coordinate order. -/
def hop (p q : Slot) : Slot × Slot :=
  match p, q with
  | .front, _ => (.trail, .front)
  | _, .negative => (.negative, .empty)
  | _, .positive => (.positive, .empty)
  | .trail, .empty => (.empty, .empty)
  | p, q => (p, q)

/-- The door sees the old slot, even on a simultaneous final path hop. -/
def door (c : Control) (a : Slot) : Slot × Control :=
  match c, a with
  | .issue, _ => (.front, .waiting)
  | .waiting, .negative => (.empty, .pending)
  | .waiting, .positive | .waiting, .empty => (.empty, .issue)
  | c, a => (a, c)

def terminal (seen : Bool) (b : Slot) : Slot :=
  match b with
  | .front => if seen then .positive else .negative
  | .trail => .empty
  | b => b

def commit : Control → Control
  | .pending => .issue
  | c => c

/-- Live coordinates are zero through n inclusive. -/
structure Line where
  slot : Nat → Slot
  pc : Control

/-- Hop zero also services the terminal and pending control. Hop n-1
also services the source door. The terminal sees the actual full bit. -/
def move {n : Nat} (x : Line) (k : Fin n) (seen : Bool) : Line :=
  let p := hop (x.slot k.val) (x.slot (k.val + 1))
  let d := door x.pc (x.slot 0)
  { slot := fun i =>
      if i = k.val then p.1
      else if i = k.val + 1 then p.2
      else if k.val = 0 ∧ i = n then terminal seen (x.slot n)
      else if k.val + 1 = n ∧ i = 0 then d.1
      else x.slot i
    pc := if k.val + 1 = n then d.2
      else if k.val = 0 then commit x.pc
      else x.pc }

/-- The outgoing source service sees ISSUE before its pair update. -/
def Launches {n : Nat} (x : Line) (k : Fin n) : Prop :=
  k.val + 1 = n ∧ x.pc = .issue

instance {n : Nat} (x : Line) (k : Fin n) : Decidable (Launches x k) :=
  inferInstanceAs (Decidable (k.val + 1 = n ∧ x.pc = .issue))

theorem move_left {n : Nat} (x : Line) (k : Fin n) (seen : Bool) :
    (move x k seen).slot k.val = (hop (x.slot k.val) (x.slot (k.val + 1))).1 := by
  simp [move]

theorem move_right {n : Nat} (x : Line) (k : Fin n) (seen : Bool) :
    (move x k seen).slot (k.val + 1) = (hop (x.slot k.val) (x.slot (k.val + 1))).2 := by
  simp [move]

theorem move_terminal {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (hk : k.val = 0) :
    (move x k seen).slot n = terminal seen (x.slot n) := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [move, h0, h1, hk]

theorem move_door {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (hk : k.val + 1 = n) :
    (move x k seen).slot 0 = (door x.pc (x.slot 0)).1 := by
  have h0 : 0 ≠ k.val := by omega
  have h1 : 0 ≠ n := by omega
  have hk0 : k.val ≠ 0 := by omega
  simp [move, h0, h1, hk0, hk]

theorem move_frame {n : Nat} (x : Line) (k : Fin n) (seen : Bool) (i : Nat)
    (hleft : i ≠ k.val) (hright : i ≠ k.val + 1)
    (hterm : ¬ (k.val = 0 ∧ i = n))
    (hdoor : ¬ (k.val + 1 = n ∧ i = 0)) :
    (move x k seen).slot i = x.slot i := by
  simp [move, hleft, hright, hterm, hdoor]

theorem move_launch {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (h : Launches x k) :
    (move x k seen).slot 0 = .front ∧ (move x k seen).pc = .waiting := by
  obtain ⟨hk, hpc⟩ := h
  rw [move_door hn x k seen hk]
  simp [move, hk, hpc, door]

private theorem quiet_not_front {q : Slot} (h : q.Quiet) : q ≠ .front := by
  rcases h with rfl | rfl | rfl <;> simp

private theorem hop_left_not_front (p q : Slot) : (hop p q).1 ≠ .front := by
  cases p <;> cases q <;> simp [hop]

private theorem hop_right_not_front (p q : Slot) (hp : p ≠ .front) (hq : q ≠ .front) :
    (hop p q).2 ≠ .front := by
  cases p <;> cases q <;> simp_all [hop]

private theorem hop_left_quiet (p q : Slot) (hp : p ≠ .front) (hq : q.Quiet) :
    (hop p q).1.Quiet := by
  cases p <;> cases q <;> simp_all [hop, Slot.Quiet]

private theorem hop_right_quiet (p q : Slot) (hp : p ≠ .front) (hq : q.Quiet) :
    (hop p q).2.Quiet := by
  cases p <;> cases q <;> simp_all [hop, Slot.Quiet]

private theorem terminal_quiet (seen : Bool) (a : Slot) : (terminal seen a).Quiet := by
  cases a <;> cases seen <;> simp [terminal, Slot.Quiet]

private theorem door_not_front (c : Control) (a : Slot) (hc : c ≠ .issue)
    (ha : a ≠ .front) : (door c a).1 ≠ .front := by
  cases c <;> cases a <;> simp_all [door]

private theorem door_quiet (c : Control) (a : Slot) (hc : c ≠ .issue)
    (ha : a.Quiet) : (door c a).1.Quiet := by
  cases c <;> cases a <;> simp_all [door, Slot.Quiet]

/-- All services preserve the cleared prefix before launch. Its nominated
hop extends the prefix by one. -/
theorem outward_prefix {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (hlaunch : ¬ Launches x k) (b : Nat) (hb : b ≤ n)
    (h : ∀ i, i < b → x.slot i ≠ .front) :
    ∀ i, i < (if k.val = b then b + 1 else b) → (move x k seen).slot i ≠ .front := by
  intro i hi
  have hcut : i < b ∨ i = k.val := by
    split at hi <;> omega
  by_cases hl : i = k.val
  · subst i
    rw [move_left]
    exact hop_left_not_front _ _
  have hb' : i < b := hcut.resolve_right hl
  by_cases hr : i = k.val + 1
  · subst i
    rw [move_right]
    exact hop_right_not_front _ _ (h _ (by omega)) (h _ hb')
  by_cases ht : k.val = 0 ∧ i = n
  · obtain ⟨hk, rfl⟩ := ht
    omega
  by_cases hd : k.val + 1 = n ∧ i = 0
  · obtain ⟨hk, rfl⟩ := hd
    rw [move_door hn x k seen hk]
    exact door_not_front _ _ (fun hc => hlaunch ⟨hk, hc⟩) (h _ hb')
  rw [move_frame x k seen i hl hr ht hd]
  exact h _ hb'

/-- Without a source launch, an outward front cannot regenerate. -/
theorem no_front {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (hlaunch : ¬ Launches x k) (h : ∀ i, i ≤ n → x.slot i ≠ .front) :
    ∀ i, i ≤ n → (move x k seen).slot i ≠ .front := by
  intro i hi
  by_cases hl : i = k.val
  · subst i
    rw [move_left]
    exact hop_left_not_front _ _
  by_cases hr : i = k.val + 1
  · subst i
    rw [move_right]
    have hk := k.isLt
    exact hop_right_not_front _ _ (h _ (by omega)) (h _ (by omega))
  by_cases ht : k.val = 0 ∧ i = n
  · obtain ⟨hk, rfl⟩ := ht
    rw [move_terminal hn x k seen hk]
    exact quiet_not_front (terminal_quiet _ _)
  by_cases hd : k.val + 1 = n ∧ i = 0
  · obtain ⟨hk, rfl⟩ := hd
    rw [move_door hn x k seen hk]
    exact door_not_front _ _ (fun hc => hlaunch ⟨hk, hc⟩) (h _ hi)
  rw [move_frame x k seen i hl hr ht hd]
  exact h _ hi

/-- A silent suffix stays silent without a launch. The reverse service
of the edge just outside it extends it by one. -/
theorem reverse_suffix {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (hlaunch : ¬ Launches x k) (b : Nat)
    (hf : ∀ i, i ≤ n → x.slot i ≠ .front)
    (h : ∀ i, b ≤ i → i ≤ n → (x.slot i).Quiet) :
    ∀ i, (if k.val + 1 = b then k.val else b) ≤ i → i ≤ n →
      ((move x k seen).slot i).Quiet := by
  intro i hi hin
  have hcut : b ≤ i ∨ i = k.val := by
    split at hi <;> omega
  have hk := k.isLt
  by_cases hl : i = k.val
  · subst i
    rw [move_left]
    have hnext : b ≤ k.val + 1 := by
      split at hi <;> omega
    exact hop_left_quiet _ _ (hf _ (by omega)) (h _ hnext (by omega))
  have hb' : b ≤ i := hcut.resolve_right hl
  by_cases hr : i = k.val + 1
  · subst i
    rw [move_right]
    exact hop_right_quiet _ _ (hf _ (by omega)) (h _ hb' hin)
  by_cases ht : k.val = 0 ∧ i = n
  · obtain ⟨hk0, rfl⟩ := ht
    rw [move_terminal hn x k seen hk0]
    exact terminal_quiet _ _
  by_cases hd : k.val + 1 = n ∧ i = 0
  · obtain ⟨hkn, rfl⟩ := hd
    rw [move_door hn x k seen hkn]
    exact door_quiet _ _ (fun hc => hlaunch ⟨hkn, hc⟩) (h _ hb' hin)
  rw [move_frame x k seen i hl hr ht hd]
  exact h _ hb' hin

/-- Comparison phase. Each index is the next nominated path hop. -/
inductive Phase (n : Nat) where
  | outward (k : Fin n)
  | terminal
  | reverse (k : Fin n)
  | control
  | launched
  deriving DecidableEq

def Phase.cert {n : Nat} (x : Line) : Phase n → Prop
  | .outward k => ∀ i, i < k.val → x.slot i ≠ .front
  | .terminal => ∀ i, i < n → x.slot i ≠ .front
  | .reverse k => (∀ i, i ≤ n → x.slot i ≠ .front) ∧
      (∀ i, k.val + 1 ≤ i → i ≤ n → (x.slot i).Quiet)
  | .control => ∀ i, i ≤ n → (x.slot i).Quiet
  | .launched => True

def controlDebt : Control → Nat
  | .issue => 1
  | .waiting => 3
  | .pending => 2

def Phase.debt {n : Nat} (x : Line) : Phase n → Nat
  | .outward k => (n - k.val) + n + 4
  | .terminal => n + 4
  | .reverse k => k.val + 4
  | .control => controlDebt x.pc
  | .launched => 0

def firstHop {n : Nat} (hn : 0 < n) : Fin n := ⟨0, hn⟩
def lastHop {n : Nat} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- A generated front takes priority over the pending nomination. -/
def Phase.advance {n : Nat} (hn : 0 < n) (x : Line) (k : Fin n) (phase : Phase n) :
    Phase n :=
  if Launches x k then .launched
  else match phase with
  | .outward j =>
      if k = j then
        if h : j.val + 1 < n then .outward ⟨j.val + 1, h⟩ else .terminal
      else .outward j
  | .terminal => if k.val = 0 then .reverse (lastHop hn) else .terminal
  | .reverse j =>
      if k = j then
        if h : 0 < j.val then .reverse ⟨j.val - 1, by have := j.isLt; omega⟩
        else .control
      else .reverse j
  | .control => .control
  | .launched => .launched

def Phase.nominate {n : Nat} (hn : 0 < n) (x : Line) : Phase n → Fin n
  | .outward j | .reverse j => j
  | .terminal | .launched => firstHop hn
  | .control => if x.pc = .pending then firstHop hn else lastHop hn

theorem initial_dirty {n : Nat} (hn : 0 < n) (x : Line) :
    (Phase.outward (firstHop hn)).cert x ∧
      (Phase.outward (firstHop hn)).debt x = 2 * n + 4 := by
  constructor
  · intro i hi
    change i < 0 at hi
    omega
  · simp [Phase.debt, firstHop] <;> omega

theorem advance_launched_iff {n : Nat} (hn : 0 < n) (x : Line) (k : Fin n) (p : Phase n) :
    p.advance hn x k = .launched ↔ p = .launched ∨ Launches x k := by
  by_cases hl : Launches x k
  · simp [Phase.advance, hl]
  cases p with
  | outward j =>
    simp only [Phase.advance, hl, if_false, or_false]
    split <;> (try split) <;> simp
  | terminal =>
    simp only [Phase.advance, hl, if_false, or_false]
    split <;> simp
  | reverse j =>
    simp only [Phase.advance, hl, if_false, or_false]
    split <;> (try split) <;> simp
  | control => simp [Phase.advance, hl]
  | launched => simp [Phase.advance, hl]

private theorem control_step {n : Nat} (hn : 2 ≤ n) (x : Line) (k : Fin n) (seen : Bool)
    (hl : ¬ Launches x k) (hq : (x.slot 0).Quiet) :
    controlDebt (move x k seen).pc ≤ controlDebt x.pc ∧
      ((if x.pc = .pending then k.val = 0 else k.val + 1 = n) →
        controlDebt (move x k seen).pc + 1 ≤ controlDebt x.pc) := by
  by_cases hd : k.val + 1 = n
  · have hi : k.val ≠ 0 := by omega
    have hc : x.pc ≠ .issue := fun he => hl ⟨hd, he⟩
    rcases hq with ha | ha | ha <;> cases hpc : x.pc <;>
      simp_all [move, door, controlDebt]
  by_cases hi : k.val = 0 <;> cases hpc : x.pc <;>
    simp_all [move, commit, controlDebt]

private theorem live_debt_positive {n : Nat} (x : Line) (p : Phase n)
    (h : p ≠ .launched) : 0 < p.debt x := by
  cases p with
  | outward _ => simp [Phase.debt]
  | terminal => simp [Phase.debt]
  | reverse _ => simp [Phase.debt]
  | control => cases eq : x.pc <;> simp [Phase.debt, eq, controlDebt]
  | launched => exact False.elim (h rfl)

/-- Every selected label preserves the comparison and weakly pays down its
rank. The nominated label pays at least one, unless the launch has already
occurred. The launch itself takes priority on any selected label. -/
theorem dirty_advance {n : Nat} (hn : 2 ≤ n) (x : Line) (p : Phase n) (k : Fin n)
    (seen : Bool) (hcert : p.cert x) (hlive : p ≠ .launched) :
    let hn' : 0 < n := by omega
    let y := move x k seen
    let q := p.advance hn' x k
    q.cert y ∧ q.debt y ≤ p.debt x ∧
      (k = p.nominate hn' x → q.debt y + 1 ≤ p.debt x) := by
  dsimp only
  have hn' : 0 < n := by omega
  have hklt := k.isLt
  by_cases hl : Launches x k
  · have hpositive := live_debt_positive x p hlive
    simp only [Phase.advance, hl, if_true, Phase.cert, Phase.debt]
    exact ⟨trivial, Nat.zero_le _, fun _ => hpositive⟩
  cases p with
  | outward j =>
    have hj := j.isLt
    have hf := outward_prefix hn x k seen hl j.val (by omega) hcert
    by_cases he : k = j
    · subst k
      rw [if_pos rfl] at hf
      by_cases hmore : j.val + 1 < n
      · simp only [Phase.advance, hl, if_false, if_true, dif_pos hmore,
          Phase.cert, Phase.debt, Phase.nominate]
        exact ⟨hf, by omega, fun _ => by omega⟩
      · simp only [Phase.advance, hl, if_false, if_true, dif_neg hmore,
          Phase.cert, Phase.debt, Phase.nominate]
        exact ⟨fun i hi => hf i (by omega), by omega, fun _ => by omega⟩
    · have he' : k.val ≠ j.val := fun hv => he (Fin.ext hv)
      rw [if_neg he'] at hf
      simp only [Phase.advance, hl, if_false, if_neg he, Phase.cert, Phase.debt,
        Phase.nominate]
      exact ⟨hf, Nat.le_refl _, fun h => False.elim (he h)⟩
  | terminal =>
    have hf := outward_prefix hn x k seen hl n (Nat.le_refl _) hcert
    have hkne : k.val ≠ n := by omega
    rw [if_neg hkne] at hf
    by_cases hfirst : k.val = 0
    · have hterm : ((move x k seen).slot n).Quiet := by
        rw [move_terminal hn x k seen hfirst]
        exact terminal_quiet _ _
      have hlast : (lastHop hn').val + 1 = n := by
        simp [lastHop] <;> omega
      simp only [Phase.advance, hl, if_false, if_pos hfirst, Phase.cert, Phase.debt,
        Phase.nominate]
      refine ⟨⟨?_, ?_⟩, by omega, fun _ => by omega⟩
      · intro i hi
        by_cases hi' : i = n
        · subst i
          exact quiet_not_front hterm
        exact hf i (by omega)
      · intro i hlow hi
        have hie : i = n := by omega
        simpa only [hie] using hterm
    · have hen : k ≠ firstHop hn' := fun he =>
        hfirst (congrArg Fin.val he)
      simp only [Phase.advance, hl, if_false, if_neg hfirst, Phase.cert, Phase.debt,
        Phase.nominate]
      exact ⟨hf, Nat.le_refl _, fun he => False.elim (hen he)⟩
  | reverse j =>
    have hj := j.isLt
    have hc : (∀ i, i ≤ n → x.slot i ≠ .front) ∧
        (∀ i, j.val + 1 ≤ i → i ≤ n → (x.slot i).Quiet) := hcert
    have hf := no_front hn x k seen hl hc.1
    have hq := reverse_suffix hn x k seen hl (j.val + 1) hc.1 hc.2
    by_cases he : k = j
    · subst k
      rw [if_pos rfl] at hq
      by_cases hmore : 0 < j.val
      · simp only [Phase.advance, hl, if_false, if_true, dif_pos hmore,
          Phase.cert, Phase.debt, Phase.nominate]
        exact ⟨⟨hf, fun i hlo hi => hq i (by omega) hi⟩, by omega, fun _ => by omega⟩
      · simp only [Phase.advance, hl, if_false, if_true, dif_neg hmore,
          Phase.cert, Phase.debt, Phase.nominate]
        refine ⟨fun i hi => hq i (by omega) hi, ?_, ?_⟩
        · cases xpc : (move x j seen).pc <;> simp [controlDebt] <;> omega
        · intro _
          cases xpc : (move x j seen).pc <;> simp [controlDebt] <;> omega
    · have he' : k.val + 1 ≠ j.val + 1 := fun hv => he (Fin.ext (by omega))
      rw [if_neg he'] at hq
      simp only [Phase.advance, hl, if_false, if_neg he, Phase.cert, Phase.debt,
        Phase.nominate]
      exact ⟨⟨hf, hq⟩, Nat.le_refl _, fun h => False.elim (he h)⟩
  | control =>
    have hf : ∀ i, i ≤ n → x.slot i ≠ .front :=
      fun i hi => quiet_not_front (hcert i hi)
    have hq := reverse_suffix hn x k seen hl 0 hf (fun i _ hi => hcert i hi)
    have hnot : k.val + 1 ≠ 0 := by omega
    rw [if_neg hnot] at hq
    have hd := control_step hn x k seen hl (hcert 0 (Nat.zero_le _))
    simp only [Phase.advance, hl, if_false, Phase.cert, Phase.debt]
    refine ⟨fun i hi => hq i (Nat.zero_le _) hi, hd.1, ?_⟩
    intro he
    apply hd.2
    by_cases hp : x.pc = .pending
    · simpa only [Phase.nominate, if_pos hp, firstHop] using congrArg Fin.val he
    · have he' : k.val = n - 1 := by
        simpa only [Phase.nominate, if_neg hp, lastHop] using congrArg Fin.val he
      rw [if_neg hp]
      omega
  | launched => exact False.elim (hlive rfl)

end L4.Height.ObserverDirty
