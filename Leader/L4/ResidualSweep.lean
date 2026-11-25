import Leader.L4.FixedResidual

/-! Exact stopped rail normalization lemmas for the restart argument.
All nonnominated body/door/top services remain enabled. -/
namespace L4.ResidualSweep
open FixedResidual

/-- Upward tokens of either kind. -/
def Up (r : Rail) : Prop := r = .ui ∨ r = .uc

/-- Empty or a clockwise return. -/
def Cleared (r : Rail) : Prop := r = .e ∨ r = .di ∨ r = .dc

/-- The actual ordinary body port pair. -/
def body (a b : Rail) : Rail × Rail :=
  let w := move false (⟨Source.off, a,b,false⟩ : Patrol 1)
  (w.left,w.right)

theorem body_break_left (a b : Rail) : (body a b).1 ≠ .x := by
  cases a <;> cases b <;> decide

theorem body_break_right (a b : Rail) (ha : a ≠ .x) (hb : b ≠ .x) :
    (body a b).2 ≠ .x := by
  cases a <;> cases b <;> simp_all <;> decide

theorem body_up_right (a b : Rail) (hb : ¬ Up b) : ¬ Up (body a b).2 := by
  cases a <;> cases b <;> simp_all [Up] <;> decide

theorem body_up_progress (a b : Rail) : ¬ Up (body a b).2 := by
  cases a <;> cases b <;> unfold Up <;> decide

theorem body_up_left (a b : Rail) (ha : ¬ Up a) (hb : ¬ Up b) :
    ¬ Up (body a b).1 := by
  cases a <;> cases b <;> simp_all [Up] <;> decide

theorem body_clear_left (a b : Rail) (ha : Cleared a) (hb : ¬ Up b) :
    (body a b).1 = .e := by
  cases a <;> cases b <;> simp_all [Cleared,Up] <;> decide

theorem body_clear_right (a b : Rail) (ha : Cleared a)
    (hb : ¬ Up b) (hx : b ≠ .x) : Cleared (body a b).2 := by
  cases a <;> cases b <;> simp_all [Cleared,Up] <;> decide

theorem body_clear_pair (a b : Rail) (ha : Cleared a) (hb : Cleared b) :
    (body a b).1 = .e ∧ Cleared (body a b).2 := by
  cases a <;> cases b <;> simp_all [Cleared] <;> decide

theorem top_no_break (r : Rail) (hx : r ≠ .x) : topRail r ≠ .x := by
  cases r <;> simp_all [topRail]

theorem top_no_up (r : Rail) : ¬ Up (topRail r) := by
  cases r <;> unfold Up <;> decide

theorem top_cleared (r : Rail) (hx : r ≠ .x) : Cleared (topRail r) := by
  cases r <;> simp_all [topRail,Cleared]

/-- Literal A-group projection before L1/L2, at a pinned ghost. -/
def doorArrivals {Q : Nat} (s : Source Q) (r : Rail) : Patrol Q :=
  arrivals true true false (sourceGuard true ⟨s,r,.e,false⟩)

/-- A fresh L1/L2 launch on the selected door, not merely a resident U. -/
def launches {Q : Nat} (s : Source Q) (r : Rail) : Prop :=
  let a := doorArrivals s r
  a.source = .i0 ∨ ∃ k, a.source = .count k

private theorem arrived_left {Q : Nat} (z : Patrol Q) :
    (arrivals true true false z).left = z.left ∨ (arrivals true true false z).left = .e := by
  unfold arrivals
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · split
        · split <;> exact .inr rfl
        · split
          · exact .inr rfl
          · split <;> exact .inl rfl

private theorem guard_left {Q : Nat} (s : Source Q) (r : Rail) :
    (sourceGuard true (⟨s,r,.e,false⟩ : Patrol Q)).left = r := by
  cases s <;> rfl

private theorem arrived_left' {Q : Nat} (s : Source Q) (r : Rail) :
    (doorArrivals s r).left = r ∨ (doorArrivals s r).left = .e := by
  simpa only [doorArrivals,guard_left] using
    arrived_left (sourceGuard true (⟨s,r,.e,false⟩ : Patrol Q))

private theorem turn_left {Q : Nat} (a : Patrol Q) : (turn true a).left = a.left := by
  cases h : a.right <;> simp [turn,h]

private theorem door_left {Q : Nat} (s : Source Q) (r : Rail) :
    (serviceDoor s r).left = (launch (doorArrivals s r)).left := by
  exact turn_left _

private theorem arrived_x_left {Q : Nat} (s : Source Q) :
    (doorArrivals s .x).left = .e := by
  cases s <;> rfl

theorem door_no_break {Q : Nat} (s : Source Q) (r : Rail) :
    (serviceDoor s r).left ≠ .x := by
  rw [door_left]
  let z := doorArrivals s r
  have a : z.left ≠ .x := by
    by_cases h : r = .x
    · subst r
      simp [z,arrived_x_left]
    · rcases arrived_left' s r with hh|hh
      · exact fun h' => h (hh.symm.trans h')
      · exact fun h' => Rail.noConfusion (hh.symm.trans h')
  change (launch z).left ≠ .x
  unfold launch
  split
  · change Rail.ui ≠ .x; decide
  · change Rail.uc ≠ .x; decide
  · exact a

theorem door_no_up_unless_launch {Q : Nat} (s : Source Q) (r : Rail)
    (hL : ¬ launches s r) (hR : ¬ Up r) : ¬ Up (serviceDoor s r).left := by
  rw [door_left]
  let z := doorArrivals s r
  have a : ¬ Up z.left := by
    rcases arrived_left' s r with h|h
    · exact fun hv => hR (h ▸ hv)
    · rw [show z.left = .e from h]
      simp [Up]
  change ¬ (z.source = .i0 ∨ ∃ k, z.source = .count k) at hL
  change ¬ Up (launch z).left
  unfold launch
  split
  · rename_i h
    exact (hL (.inl h)).elim
  · rename_i k h
    exact (hL (.inr ⟨k,h⟩)).elim
  · exact a

/-- Number of interior bonds is d (h=d+1 slots). Distinct top and door
actions are the ordinary corridor. The same functions may be applied
together on a shared alias mark, after a separate physical projection. -/
inductive Port (d : Nat) where
  | body (at_ : Fin d)
  | top | door | idle
  deriving DecidableEq

structure Line (Q d : Nat) where
  rail : Fin (d+1) → Rail
  source : Source Q
  fired : Bool

def bodyLeft {d : Nat} (i : Fin d) : Fin (d+1) := i.castSucc

def bodyRight {d : Nat} (i : Fin d) : Fin (d+1) := i.succ

def topSlot (d : Nat) : Fin (d+1) := 0
def doorSlot (d : Nat) : Fin (d+1) := Fin.last d
private theorem different {d : Nat} (i : Fin d) : bodyRight i ≠ bodyLeft i := by
  intro h
  have H := congrArg Fin.val h
  change i.val+1=i.val at H
  omega

def lineStep {Q d : Nat} (s : Line Q d) : Port d → Line Q d
  | .idle => s
  | .body i =>
    let a := body (s.rail (bodyLeft i)) (s.rail (bodyRight i))
    { s with rail := fun j => if j=bodyLeft i then a.1 else if j=bodyRight i then a.2 else s.rail j }
  | .top => { s with rail := fun j => if j=topSlot d then topRail (s.rail j) else s.rail j }
  | .door =>
    let a := serviceDoor s.source (s.rail (doorSlot d))
    { rail := fun j => if j=doorSlot d then a.left else s.rail j, source := a.source, fired := a.fire }

/-- First k slots contain no X; k need not equal the first occupied slot. -/
def BreakFreePrefix {Q d : Nat} (s : Line Q d) (k : Nat) : Prop :=
  ∀ j : Fin (d+1), j.val < k → s.rail j ≠ .x

/-- Arbitrarily interleaved legal marks preserve every established
break-free prefix. The door never creates X and the ordinary left port
cannot create it; only a predecessor may send X into the right port. -/
theorem break_prefix_hold {Q d : Nat} (s : Line Q d) (k : Nat) (mark : Port d)
    (h : BreakFreePrefix s k) : BreakFreePrefix (lineStep s mark) k := by
  intro j hj
  cases mark with
  | idle => exact h j hj
  | top =>
    by_cases H : j=topSlot d
    · simpa [lineStep,H] using top_no_break _ (h j hj)
    · simpa [lineStep,H] using h j hj
  | door =>
    by_cases H : j=doorSlot d
    · simpa [lineStep,H] using door_no_break s.source (s.rail (doorSlot d))
    · simpa [lineStep,H] using h j hj
  | body i =>
    by_cases hL : j=bodyLeft i
    · simpa [lineStep,hL] using body_break_left (s.rail (bodyLeft i)) (s.rail (bodyRight i))
    · by_cases hR : j=bodyRight i
      · have hK : (bodyLeft i).val < k := by
          have H := congrArg Fin.val hR
          change j.val = i.val+1 at H
          change i.val < k
          omega
        have hr : (bodyRight i).val < k := hR ▸ hj
        simpa [lineStep,hR,different i] using body_break_right _ _ (h _ hK) (h _ hr)
      · simpa [lineStep,hL,hR] using h j hj

/-- The prescribed next clockwise mark extends the established X-free
prefix by one. No premise about dirty rails after that boundary is used. -/
theorem break_prefix_extend {Q d : Nat} (s : Line Q d) (k : Fin (d+1))
    (h : BreakFreePrefix s k.val) :
    BreakFreePrefix (lineStep s (if hk : k.val < d then .body ⟨k.val,hk⟩ else .door))
      (k.val+1) := by
  intro j hj
  by_cases hJ : j.val < k.val
  · exact break_prefix_hold _ _ _ h j hJ
  · have eq : j=k := Fin.ext (by omega)
    subst j
    split
    · rename_i hk
      have hL : k = bodyLeft ⟨k.val,hk⟩ := Fin.ext rfl
      simpa only [lineStep,if_pos hL] using body_break_left
        (s.rail (bodyLeft ⟨k.val,hk⟩)) (s.rail (bodyRight ⟨k.val,hk⟩))
    · rename_i hk
      have hs : k=doorSlot d := by apply Fin.ext; change k.val=d; omega
      simpa [lineStep,hs] using door_no_break s.source (s.rail (doorSlot d))

/-- Early phase exception: actual L1/L2 or a terminating A2 fire. -/
def PhaseExit {Q d : Nat} (s : Line Q d) (mark : Port d) : Prop :=
  match mark with
  | .door => launches s.source (s.rail (doorSlot d)) ∨ (lineStep s mark).fired = true
  | _ => False

/-- Establish clearance from the door backward. -/
def UpFreeSuffix {Q d : Nat} (s : Line Q d) (k : Nat) : Prop :=
  ∀ j : Fin (d+1), k ≤ j.val → ¬ Up (s.rail j)

/-- Already swept slots stay U-free under arbitrary marks until an
observed launch/stop. In particular a stale left U cannot return right. -/
theorem up_suffix_hold {Q d : Nat} (s : Line Q d) (k : Nat) (mark : Port d)
    (h : UpFreeSuffix s k) (hx : ¬ PhaseExit s mark) :
    UpFreeSuffix (lineStep s mark) k := by
  intro j hj
  cases mark with
  | idle => exact h j hj
  | top =>
    by_cases H : j=topSlot d
    · simpa [lineStep,H] using top_no_up (s.rail j)
    · simpa [lineStep,H] using h j hj
  | door =>
    by_cases H : j=doorSlot d
    · exact (show ¬ Up ((lineStep s .door).rail j) from by
        rw [show (lineStep s .door).rail j = (serviceDoor s.source (s.rail (doorSlot d))).left from
          if_pos H]
        exact door_no_up_unless_launch _ _ (fun hh => hx (.inl hh)) (h _ (H ▸ hj)))
    · simpa [lineStep,H] using h j hj
  | body i =>
    by_cases hL : j=bodyLeft i
    · have hK : k ≤ (bodyRight i).val := by
        have H := congrArg Fin.val hL
        change j.val = i.val at H
        change k ≤ i.val+1
        omega
      simpa [lineStep,hL] using body_up_left (s.rail (bodyLeft i)) (s.rail (bodyRight i))
        (h _ (hL ▸ hj)) (h _ hK)
    · by_cases hR : j=bodyRight i
      · simpa [lineStep,hR,different i] using body_up_progress (s.rail (bodyLeft i)) (s.rail (bodyRight i))
      · simpa [lineStep,hL,hR] using h j hj

/-- Service the right port of the next slot to be swept, or turn the
top when only offset zero remains. -/
def upNominate {d : Nat} (k : Fin (d+1)) : Port d :=
  if h : 0 < k.val then .body ⟨k.val-1,by omega⟩ else .top

/-- One selected reverse nomination extends the protected U-free
suffix across its next slot. -/
theorem up_suffix_extend {Q d : Nat} (s : Line Q d) (k : Fin (d+1))
    (h : UpFreeSuffix s (k.val+1)) :
    UpFreeSuffix (lineStep s (upNominate k)) k.val := by
  intro j hj
  by_cases hJ : k.val+1 ≤ j.val
  · apply up_suffix_hold _ _ _ h _ j hJ
    simp only [upNominate]; split <;> simp [PhaseExit]
  · have eq : j=k := Fin.ext (by omega)
    subst j
    unfold upNominate
    split
    · rename_i hk
      let i : Fin d := ⟨k.val-1,by omega⟩
      have hR : k = bodyRight i := Fin.ext (by change k.val = k.val-1+1; omega)
      have hL : k ≠ bodyLeft i := fun h => different i (hR.symm.trans h)
      change ¬ Up ((lineStep s (.body i)).rail k)
      simpa only [lineStep,if_neg hL,if_pos hR] using body_up_progress
        (s.rail (bodyLeft i)) (s.rail (bodyRight i))
    · rename_i hk
      have hT : k=topSlot d := Fin.ext (by change k.val=0; omega)
      simpa only [lineStep,if_pos hT] using top_no_up (s.rail k)

private theorem arrival_absorbs_return {Q : Nat} (z : Patrol Q) (h : returning z.left = true) :
    (arrivals true true false z).left = .e := by
  unfold arrivals
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · split <;> rfl
        · rw [h]
          rfl

private theorem door_cleared_no_launch {Q : Nat} (s : Source Q) (r : Rail)
    (hr : Cleared r) (hL : ¬ launches s r) : (serviceDoor s r).left = .e := by
  rw [door_left]
  let z := doorArrivals s r
  have H : z.left = .e := by
    rcases hr with h|h|h
    · rcases arrived_left' s r with he|he
      · exact he.trans h
      · exact he
    · apply arrival_absorbs_return
      rw [guard_left,h]
      rfl
    · apply arrival_absorbs_return
      rw [guard_left,h]
      rfl
  change ¬ (z.source = .i0 ∨ ∃ k, z.source = .count k) at hL
  change (launch z).left = .e
  unfold launch
  split
  · rename_i h
    exact (hL (.inl h)).elim
  · rename_i k h
    exact (hL (.inr ⟨k,h⟩)).elim
  · exact H

/-- The established empty prefix; at its boundary all earlier returns
have propagated to at most a single E/D slot. Outside that prefix any
X-free, U-free E/T/D bytes remain permitted. -/
def ReturnFront {Q d : Nat} (s : Line Q d) (k : Nat) : Prop :=
  (∀ j : Fin (d+1), j.val < k → s.rail j = .e) ∧
  (∀ j : Fin (d+1), j.val = k → Cleared (s.rail j))

private theorem body_e_e : body .e .e = (.e,.e) := rfl

private theorem body_clear_at_right (b : Rail) (h : Cleared b) :
    (body .e b).2 = b := by
  rcases h with e|e|e <;> subst b <;> rfl

/-- Arbitrary interleavings preserve the swept prefix and its single
E/D boundary, until a fresh launch or birth ends this cleaning phase. -/
theorem return_front_hold {Q d : Nat} (s : Line Q d) (k : Nat) (mark : Port d)
    (h : ReturnFront s k) (hB : BreakFreePrefix s (d+1))
    (hU : UpFreeSuffix s 0) (hx : ¬ PhaseExit s mark) :
    ReturnFront (lineStep s mark) k := by
  have oldClear (j : Fin (d+1)) (hj : j.val ≤ k) : Cleared (s.rail j) := by
    by_cases H : j.val < k
    · exact .inl (h.1 j H)
    · exact h.2 j (by omega)
  constructor
  · intro j hj
    cases mark with
    | idle => exact h.1 j hj
    | top =>
      by_cases H : j=topSlot d
      · rw [show (lineStep s .top).rail j = topRail (s.rail j) from if_pos H, h.1 j hj]
        rfl
      · simpa [lineStep,H] using h.1 j hj
    | door =>
      by_cases H : j=doorSlot d
      · simpa only [lineStep,if_pos H] using door_cleared_no_launch s.source
          (s.rail (doorSlot d)) (oldClear _ (H ▸ Nat.le_of_lt hj)) (fun hh => hx (.inl hh))
      · simpa [lineStep,H] using h.1 j hj
    | body i =>
      by_cases hL : j=bodyLeft i
      · simpa [lineStep,hL] using body_clear_left (s.rail (bodyLeft i))
          (s.rail (bodyRight i)) (oldClear _ (hL ▸ Nat.le_of_lt hj))
          (hU _ (Nat.zero_le _))
      · by_cases hR : j=bodyRight i
        · have hK : (bodyLeft i).val < k := by
            have H := congrArg Fin.val hR
            change j.val=i.val+1 at H
            change i.val<k; omega
          simp only [lineStep,if_neg hL,if_pos hR,h.1 _ hK,h.1 _ (hR ▸ hj),body_e_e]
        · simpa [lineStep,hL,hR] using h.1 j hj
  · intro j hj
    cases mark with
    | idle => exact h.2 j hj
    | top =>
      by_cases H : j=topSlot d
      · simpa [lineStep,H] using top_cleared (s.rail j) (hB j j.isLt)
      · simpa [lineStep,H] using h.2 j hj
    | door =>
      by_cases H : j=doorSlot d
      · apply Or.inl
        simpa only [lineStep,if_pos H] using door_cleared_no_launch s.source
          (s.rail (doorSlot d)) (oldClear _ (H ▸ Nat.le_of_eq hj)) (fun hh => hx (.inl hh))
      · simpa [lineStep,H] using h.2 j hj
    | body i =>
      by_cases hL : j=bodyLeft i
      · apply Or.inl
        simpa [lineStep,hL] using body_clear_left (s.rail (bodyLeft i))
          (s.rail (bodyRight i)) (oldClear _ (hL ▸ Nat.le_of_eq hj))
          (hU _ (Nat.zero_le _))
      · by_cases hR : j=bodyRight i
        · have hK : (bodyLeft i).val < k := by
            have H := congrArg Fin.val hR
            change j.val=i.val+1 at H
            change i.val<k; omega
          simpa only [lineStep,if_neg hL,if_pos hR,h.1 _ hK,body_clear_at_right _ (oldClear _
            (hR ▸ Nat.le_of_eq hj))] using oldClear _ (hR ▸ Nat.le_of_eq hj)
        · simpa [lineStep,hL,hR] using h.2 j hj

/-- The next forward E/D service extends the empty prefix by one and
leaves an E/D symbol at the next boundary. At the last slot this is
conditional on absence of an actual L1/L2/A2 exit. -/
theorem return_front_extend {Q d : Nat} (s : Line Q d) (k : Fin (d+1))
    (h : ReturnFront s k.val) (hB : BreakFreePrefix s (d+1))
    (hU : UpFreeSuffix s 0)
    (hx : ¬ PhaseExit s (if hk : k.val < d then .body ⟨k.val,hk⟩ else .door)) :
    ReturnFront (lineStep s (if hk : k.val < d then .body ⟨k.val,hk⟩ else .door)) (k.val+1) := by
  let m : Port d := if hk : k.val<d then .body ⟨k.val,hk⟩ else .door
  have hold := return_front_hold s k.val m h hB hU hx
  constructor
  · intro j hj
    by_cases hJ : j.val<k.val
    · exact hold.1 j hJ
    · have H : j=k := Fin.ext (by omega)
      subst j
      change (lineStep s m).rail k = .e
      by_cases hk : k.val<d
      · let i : Fin d := ⟨k.val,hk⟩
        have hL : k=bodyLeft i := Fin.ext rfl
        rw [show m = .body i from dif_pos hk]
        simpa only [lineStep,if_pos hL] using body_clear_left
          (s.rail (bodyLeft i)) (s.rail (bodyRight i)) (h.2 _ rfl) (hU _ (Nat.zero_le _))
      · have hD : k=doorSlot d := Fin.ext (by change k.val=d; omega)
        have hex : ¬ launches s.source (s.rail (doorSlot d)) :=
          fun hv => hx (by simp only [dif_neg hk,PhaseExit]; exact .inl hv)
        simpa only [m,dif_neg hk,lineStep,if_pos hD] using
          door_cleared_no_launch s.source (s.rail (doorSlot d))
            (h.2 _ (by rw [← hD])) hex
  · intro j hj
    have hk : k.val<d := by have h := j.isLt; omega
    let i : Fin d := ⟨k.val,hk⟩
    have hR : j = bodyRight i := Fin.ext hj
    have hL : j ≠ bodyLeft i := fun H => different i (hR.symm.trans H)
    change Cleared ((lineStep s m).rail j)
    rw [show m = .body i from dif_pos hk]
    simpa only [lineStep,if_neg hL,if_pos hR] using body_clear_right
      (s.rail (bodyLeft i)) (s.rail (bodyRight i)) (h.2 _ rfl)
      (hU _ (Nat.zero_le _)) (hB _ (bodyRight i).isLt)

/-- An extra selected door mark after clearing its slot sees E:
OFF/I0/waiting sources launch INIT and count-ready sources launch COUNT. -/
theorem empty_door_launch {Q : Nat} (s : Source Q) : launches s .e := by
  cases s with
  | off | i0 | i1 | await => exact .inl rfl
  | count k => exact .inr ⟨k,rfl⟩

/-- The three sweeps and their final extra door service, stopping during
phase two or three on the actual fresh launch or on a birth. -/
inductive Pass (d : Nat) where
  | breakOut (k : Fin (d+1))
  | upBack (k : Fin (d+1))
  | returnOut (k : Fin (d+1))
  | extraDoor
  | done

def clockwisePort {d : Nat} (k : Fin (d+1)) : Port d :=
  if h : k.val<d then .body ⟨k.val,h⟩ else .door

def Pass.nominate {d : Nat} : Pass d → Port d
  | .breakOut k | .returnOut k => clockwisePort k
  | .upBack k => upNominate k
  | .extraDoor => .door
  | .done => .idle

def Pass.remaining {d : Nat} : Pass d → Nat
  | .breakOut k => 3*(d+1)+1-k.val
  | .upBack k => d+3+k.val
  | .returnOut k => d+2-k.val
  | .extraDoor => 1
  | .done => 0

def Pass.afterNomination {d : Nat} : Pass d → Pass d
  | .breakOut k =>
    if h : k.val<d then .breakOut ⟨k.val+1,by omega⟩ else .upBack (Fin.last d)
  | .upBack k =>
    if h : 0<k.val then .upBack ⟨k.val-1,by omega⟩ else .returnOut 0
  | .returnOut k =>
    if h : k.val<d then .returnOut ⟨k.val+1,by omega⟩ else .extraDoor
  | .extraDoor | .done => .done

def Pass.IsExit {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d) : Prop :=
  (lineStep s m).fired = true ∨
    match p with
    | .breakOut _ | .done => False
    | _ => PhaseExit s m

def Pass.WellFormed {Q d : Nat} (s : Line Q d) : Pass d → Prop
  | .breakOut k => BreakFreePrefix s k.val
  | .upBack k => BreakFreePrefix s (d+1) ∧ UpFreeSuffix s (k.val+1)
  | .returnOut k => BreakFreePrefix s (d+1) ∧ UpFreeSuffix s 0 ∧ ReturnFront s k.val
  | .extraDoor => ∀ j, s.rail j = .e
  | .done => True

/-- A fresh isolated-pass monitor; PhaseExit is observed after each
chosen or unchosen raw service. -/
noncomputable def Pass.step {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d) : Pass d := by
  classical
  exact match p with
  | .done => .done
  | _ => if p.IsExit s m then .done else if m=p.nominate then p.afterNomination else p

/-- Number of outstanding nominated hits never increases, and at the
predictable nominated port it strictly decreases unless already done. -/
theorem Pass.step_budget {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d)
    (h : p.remaining ≠ 0) :
    (p.step s m).remaining + (if m=p.nominate then 1 else 0) ≤ p.remaining := by
  classical
  have hx : 1 ≤ p.remaining := by omega
  have z : ∀ p' : Pass d, p'.remaining ≠ 0 →
      p'.afterNomination.remaining + 1 = p'.remaining := by
    intro p' hp
    cases p' with
    | done => exact (hp rfl).elim
    | extraDoor => rfl
    | breakOut k =>
      have hk := k.isLt
      by_cases hK : k.val<d <;> simp [Pass.afterNomination,Pass.remaining,hK] <;> omega
    | upBack k =>
      by_cases hK : 0<k.val
      · simp [Pass.afterNomination,Pass.remaining,hK]; omega
      · simp only [Pass.afterNomination,dif_neg hK]
        change d+2-0+1=d+3+k.val
        omega
    | returnOut k =>
      have hk := k.isLt
      by_cases hK : k.val<d <;> simp [Pass.afterNomination,Pass.remaining,hK] <;> omega
  cases p <;> simp only [Pass.step]
  all_goals first | exact (h rfl).elim | (split <;> rename_i he)
  all_goals first
    | (change 0 + _ ≤ _; split <;> omega)
    | (split <;> first | exact Nat.le_of_eq (z _ h) | exact Nat.le_refl _)

private theorem all_empty_holds {Q d : Nat} (s : Line Q d) (m : Port d)
    (h : ∀ j, s.rail j = .e) (hx : ¬ PhaseExit s m) :
    ∀ j, (lineStep s m).rail j = .e := by
  intro j
  cases m with
  | idle => exact h j
  | door => exact (hx (.inl (by rw [h]; exact empty_door_launch s.source))).elim
  | top =>
    by_cases hj : j = topSlot d <;> simp [lineStep,hj,h,topRail]
  | body i =>
    by_cases hL : j=bodyLeft i
    · simp [lineStep,hL,h,body_e_e]
    · by_cases hR : j=bodyRight i
      · simp [lineStep,hR,h,body_e_e]
      · simp [lineStep,hL,hR,h]

/-- The monitor's certified sweep geometry holds after every selected
mark, not merely after a word made of the nominated marks. -/
theorem Pass.step_wellFormed {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d)
    (h : p.WellFormed s) :
    (p.step s m).WellFormed (lineStep s m) := by
  classical
  cases p with
  | done => trivial
  | breakOut k =>
    simp only [Pass.step]
    split
    · trivial
    · by_cases hn : m = clockwisePort k
      · subst m
        rw [if_pos (show clockwisePort k = (Pass.breakOut k).nominate from rfl)]
        simp only [Pass.afterNomination]
        have H := break_prefix_extend s k h
        by_cases hk : k.val < d
        · simp only [dif_pos hk,Pass.WellFormed]
          exact H
        · simp only [dif_neg hk,Pass.WellFormed,Fin.val_last]
          refine ⟨?_,fun j hj => (Nat.not_le_of_gt j.isLt hj).elim⟩
          have he : k.val+1=d+1 := by have hi := k.isLt; omega
          exact he ▸ H
      · rw [if_neg (show ¬m = (Pass.breakOut k).nominate from hn)]
        exact break_prefix_hold _ _ _ h
  | upBack k =>
    simp only [Pass.step]
    split
    · trivial
    · rename_i hx
      have hX : ¬ PhaseExit s m := fun hh => hx (.inr hh)
      have hb := break_prefix_hold _ _ m h.1
      by_cases hn : m = upNominate k
      · subst m
        rw [if_pos (show upNominate k = (Pass.upBack k).nominate from rfl)]
        simp only [Pass.afterNomination]
        have H := up_suffix_extend s k h.2
        by_cases hk : 0 < k.val
        · simp only [dif_pos hk,Pass.WellFormed]
          refine ⟨hb,?_⟩
          have he : (k.val-1)+1=k.val := by omega
          exact he.symm ▸ H
        · have hK : k.val = 0 := by omega
          have hTop : upNominate k = .top := dif_neg hk
          simp only [dif_neg hk,Pass.WellFormed]
          refine ⟨hb,hK ▸ H,fun j hj => (Nat.not_lt_zero _ hj).elim,?_⟩
          intro j hj
          have hj' : j=topSlot d := Fin.ext hj
          rw [hTop]
          simpa only [lineStep,if_pos hj'] using top_cleared (s.rail j) (h.1 j j.isLt)
      · rw [if_neg (show ¬m = (Pass.upBack k).nominate from hn)]
        exact ⟨hb,up_suffix_hold _ _ _ h.2 hX⟩
  | returnOut k =>
    simp only [Pass.step]
    split
    · trivial
    · rename_i hx
      have hX : ¬ PhaseExit s m := fun hh => hx (.inr hh)
      have hb := break_prefix_hold _ _ m h.1
      have hu := up_suffix_hold _ _ m h.2.1 hX
      by_cases hn : m = clockwisePort k
      · subst m
        rw [if_pos (show clockwisePort k = (Pass.returnOut k).nominate from rfl)]
        simp only [Pass.afterNomination]
        have H := return_front_extend s k h.2.2 h.1 h.2.1 hX
        by_cases hk : k.val < d
        · simp only [dif_pos hk,Pass.WellFormed]
          exact ⟨hb,hu,H⟩
        · simp only [dif_neg hk,Pass.WellFormed]
          intro j
          have hp : j.val < k.val+1 := by have hi := j.isLt; have hi' := k.isLt; omega
          exact H.1 _ hp
      · rw [if_neg (show ¬m = (Pass.returnOut k).nominate from hn)]
        exact ⟨hb,hu,return_front_hold _ _ _ h.2.2 h.1 h.2.1 hX⟩
  | extraDoor =>
    simp only [Pass.step]
    split
    · trivial
    · rename_i hx
      by_cases hn : m = .door
      · subst m; trivial
      · rw [if_neg (show ¬m = (Pass.extraDoor : Pass d).nominate from hn)]
        exact all_empty_holds _ _ h (fun hh => hx (.inr hh))

/-- The monitor never ends on a spurious nominal exhaustion: every
transition into DONE actually observes a birth or a fresh post-break
source launch. The extra door is not omitted. -/
theorem Pass.done_has_exit {Q d : Nat} (s : Line Q d) (p : Pass d) (m : Port d)
    (hW : p.WellFormed s) (hP : p ≠ .done) (hD : p.step s m = .done) :
    p.IsExit s m := by
  classical
  cases p <;> try exact (hP rfl).elim
  all_goals simp only [Pass.step] at hD
  all_goals split at hD
  all_goals first | assumption | skip
  all_goals rename_i hex
  all_goals split at hD
  all_goals try contradiction
  all_goals first
    | (simp only [Pass.afterNomination] at hD; split at hD <;> contradiction)
    | (rename_i hm
       have hM : m=.door := hm
       subst m
       exact .inr (.inl (by rw [hW (doorSlot d)]; exact empty_door_launch s.source)))

/-- A pass observer measures only cleanup to the next genuine launch
(or an earlier actual birth). It deliberately does not assert that a
COUNT launch from dirty residual state has already swept the full rail. -/
structure PassObs (Q d : Nat) where
  line : Line Q d
  phase : Pass d

def passInit {Q d : Nat} (s : Line Q d) : PassObs Q d := ⟨s,.breakOut 0⟩

noncomputable def passNext {Q d n : Nat} (port : Fin n → Port d)
    (s : PassObs Q d) (e : Fin n) : PassObs Q d :=
  match s.phase with
  | .done => s
  | _ => ⟨lineStep s.line (port e), s.phase.step s.line (port e)⟩

private theorem remaining_pos {d : Nat} (p : Pass d) (h : p ≠ .done) :
    p.remaining ≠ 0 := by
  cases p with
  | done => exact (h rfl).elim
  | extraDoor => exact Nat.one_ne_zero
  | breakOut k | upBack k | returnOut k =>
    have hk := k.isLt
    simp only [Pass.remaining]
    omega

/-- A raw-label realization of the three interleaved sweep stages
admits a genuine pathwise countdown of 3h+1, where h=d+1.
Only nominated port labels need realize a member of the raw alphabet;
all other raw marks still run their ordinary rows. -/
noncomputable def passCountdown {Q d n : Nat} (port : Fin n → Port d)
    (pick : Pass d → Fin n) (real : ∀ p : Pass d, p ≠ .done → port (pick p) = p.nominate)
    (s : Line Q d) :
    Countdown (passNext port) (fun y => y.phase = .done) (passInit s) where
  budget w := (GGTiming.runMarks (passNext port) (passInit s) w).phase.remaining
  nominate w := pick (GGTiming.runMarks (passNext port) (passInit s) w).phase
  decrease := by
    intro w hl e
    rw [GGTiming.runMarks_append]
    let o := GGTiming.runMarks (passNext port) (passInit s) w
    change (passNext port o e).phase.remaining + (if e = pick o.phase then 1 else 0) ≤ o.phase.remaining
    have hl' : o.phase ≠ .done := hl
    have rel :
        (if e = pick o.phase then 1 else 0) ≤ (if port e = o.phase.nominate then 1 else 0) := by
      by_cases he : e=pick o.phase
      · rw [if_pos he,if_pos (by rw [he,real _ hl'])]
        exact Nat.le_refl _
      · simp [he]
    have phase : (passNext port o e).phase = o.phase.step o.line (port e) := by
      cases ho : o.phase with
      | done => exact (hl' ho).elim
      | _ => simp only [passNext,ho]
    rw [phase]
    exact Nat.le_trans (Nat.add_le_add_left rel _) (Pass.step_budget _ _ _ (remaining_pos _ hl'))

/-- Exact uniform IID cost of cleanup through next launch/birth for
the rail pass. This is not yet the arbitrary-residual birth theorem. -/
theorem pass_expected {Q d n : Nat} (port : Fin n → Port d)
    (pick : Pass d → Fin n) (real : ∀ p : Pass d, p ≠ .done → port (pick p) = p.nominate)
    (s : Line Q d) :
    IIDExpectedHittingTimeAtMost (passNext port) (fun y => y.phase = .done) (passInit s)
      (n*(3*(d+1)+1)) := by
  simpa only [passCountdown,GGTiming.runMarks,passInit,Pass.remaining,Fin.val_zero,Nat.sub_zero] using
    expected_of_countdown _ _ _ (passCountdown port pick real s)

/-- A monitor that starts in a valid fixed-corridor rail image retains
its phase invariant along every finite raw word. -/
theorem pass_reachable {Q d n : Nat} (port : Fin n → Port d)
    (s : Line Q d) (w : List (Fin n)) :
    let y := GGTiming.runMarks (passNext port) (passInit s) w
    y.phase.WellFormed y.line := by
  have local_hop (o : PassObs Q d) (e : Fin n) (h : o.phase.WellFormed o.line) :
      (passNext port o e).phase.WellFormed (passNext port o e).line := by
    have h' := Pass.step_wellFormed o.line o.phase (port e) h
    cases ho : o.phase with
    | done => simp [passNext,ho,Pass.WellFormed]
    | _ => simpa only [passNext,ho] using h'
  have fold (o : PassObs Q d) (w : List (Fin n)) (h : o.phase.WellFormed o.line) :
      let y := GGTiming.runMarks (passNext port) o w
      y.phase.WellFormed y.line := by
    induction w generalizing o with
    | nil => exact h
    | cons e w ih => exact ih _ (local_hop o e h)
  exact fold _ w (fun j hj => (Nat.not_lt_zero j.val hj).elim)

/-- A waiting COUNT door has only four kinds of outcomes: restart,
terminal fire, stutter in the same count, or a strictly larger newly
launched count. The same-mark L2 behind a matching nonterminal A2
is included, not just a controller-state intention to launch. -/
theorem await_door_cases {Q : Nat} (k : Fin Q) (r : Rail) :
    let a := serviceDoor (.await k) r
    (a.source = .i1 ∧ a.left = .ui) ∨ a.fire = true ∨ a.source = .await k ∨
      ∃ k' : Fin Q, k.val < k'.val ∧ a.source = .await k' ∧ a.left = .uc := by
  cases r with
  | e | x => exact .inl ⟨rfl,rfl⟩
  | t | ui | uc | di => exact .inr (.inr (.inl rfl))
  | dc =>
    by_cases hk : k.val+1 < Q
    · refine .inr (.inr (.inr ⟨⟨k.val+1,hk⟩,Nat.lt_succ_self _,?_,?_⟩))
      · have h := door_count_accept k hk
        exact congrArg Patrol.source h
      · have h := door_count_accept k hk
        exact congrArg Patrol.left h
    · have h := door_terminal_accept k hk
      exact .inr (.inl (congrArg Patrol.fire h))

private theorem door_source {Q : Nat} (s : Source Q) (r : Rail) :
    (serviceDoor s r).source = (launch (doorArrivals s r)).source := by
  let a := launch (doorArrivals s r)
  change (turn true a).source = a.source
  cases h : a.right <;> simp [turn,h]

/-- Exactly one genuine INIT uses L1's Ui, whose post-launch source is I1.
This distinction is important if, before L1, an orphan Ui already sat
on the old door. -/
theorem init_launch_exact {Q : Nat} (s : Source Q) (r : Rail)
    (h : (doorArrivals s r).source = .i0) :
    (serviceDoor s r).source = .i1 ∧ (serviceDoor s r).left = .ui := by
  have hl : (launch (doorArrivals s r)).source = .i1 ∧
      (launch (doorArrivals s r)).left = .ui := by
    unfold launch
    split <;> simp_all
  refine ⟨?_,door_left s r ▸ hl.2⟩
  exact (door_source s r).trans hl.1

/-- A count launch records its own finite count and physical Uc port. -/
theorem count_launch_exact {Q : Nat} (s : Source Q) (r : Rail) (k : Fin Q)
    (h : (doorArrivals s r).source = .count k) :
    (serviceDoor s r).source = .await k ∧ (serviceDoor s r).left = .uc := by
  have hl : (launch (doorArrivals s r)).source = .await k ∧
      (launch (doorArrivals s r)).left = .uc := by
    unfold launch
    split <;> simp_all
  refine ⟨?_,door_left s r ▸ hl.2⟩
  exact (door_source s r).trans hl.1

#print axioms break_prefix_hold
#print axioms break_prefix_extend
#print axioms up_suffix_hold
#print axioms up_suffix_extend
#print axioms return_front_hold
#print axioms return_front_extend
#print axioms Pass.step_budget
#print axioms Pass.step_wellFormed
#print axioms Pass.done_has_exit
#print axioms passCountdown
#print axioms pass_expected
#print axioms pass_reachable
#print axioms await_door_cases
#print axioms init_launch_exact
#print axioms count_launch_exact

end L4.ResidualSweep
