-- core only
set_option autoImplicit false

namespace NonrenewableCredits

abbrev Credits (n : Nat) := Fin n → Bool

/-!
The finite configuration witness uses n = a + 4, labels in Fin 1, leaders
at 0, a, a + 3, and live bullets at a + 1, a + 2. The copied deletion row
deletes a and changes the bullet at a + 1 to a dummy. The survivor at
a + 2 gives ranks a, 5, and 2 * a + 5.

Cell and GapFrame are local model definitions. The executable deletionRow
copies only the successful deletion branch of
PPLLRepair.eliminateLeadersNoCollisionMove in Leader/Wu/Protocol/Repairs.lean.
This is not an identification with the full repository K2 transition.
The family has two nonzero bullets, so it is not a UniqueLiveShot/AActive
witness. No reachability from a stronger legitimate subspace is asserted.

Credits are proof-only history. Half-open ownership prevents double
counting at a joint, and spending never renews a site credit.
SpanChargedOnce remains the quantitative protocol obligation; local
cost and phase-decrease facts remain explicit caller inputs.
-/

structure Cell (psi : Nat) where
  leader : Bool
  shield : Bool
  signal_B : Fin 2
  bullet : Fin 3
  label : Fin psi

abbrev Config (n : Nat) := Fin n → Cell 1

structure GapFrame (n : Nat) where
  start : Nat
  d : Nat
  positive : 0 < d
  end_lt : start + d < n

def GapFrame.pos {n : Nat} (F : GapFrame n) (k : Nat) : Fin n :=
  ⟨(F.start + k) % n,
    Nat.mod_lt _
      (Nat.lt_of_le_of_lt (Nat.zero_le (F.start + F.d)) F.end_lt)⟩

def right {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n,
    Nat.mod_lt _
      (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

theorem pos_val {n : Nat} (F : GapFrame n) (k : Nat) (hk : k ≤ F.d) :
    (F.pos k).val = F.start + k := by
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left hk F.start) F.end_lt)

theorem pos_successor {n : Nat} (F : GapFrame n) (k : Nat) (hk : k < F.d) :
    F.pos (k + 1) = right (F.pos k) := by
  apply Fin.ext
  rw [pos_val F (k + 1) (Nat.succ_le_of_lt hk)]
  change F.start + (k + 1) = ((F.pos k).val + 1) % n
  rw [pos_val F k (Nat.le_of_lt hk)]
  exact (Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.succ_le_of_lt hk) F.start) F.end_lt)).symm

def beforeNat (a j : Nat) : Cell 1 where
  leader := if j = 0 ∨ j = a ∨ j = a + 3 then true else false
  shield := if j = a + 3 then true else false
  signal_B := 0
  bullet := if j = a + 1 ∨ j = a + 2 then 2 else 0
  label := 0

def afterNat (a j : Nat) : Cell 1 :=
  { beforeNat a j with
    leader := if j = 0 ∨ j = a + 3 then true else false
    bullet := if j = a + 1 then 1 else (beforeNat a j).bullet }

def before (a : Nat) : Config (a + 4) := fun i => beforeNat a i.val

def after (a : Nat) : Config (a + 4) := fun i => afterNat a i.val

def leftFrame (a : Nat) (ha : 0 < a) : GapFrame (a + 4) :=
  ⟨0, a, ha, by omega⟩

def rightFrame (a : Nat) : GapFrame (a + 4) :=
  ⟨a, 3, by decide, by omega⟩

def mergedFrame (a : Nat) : GapFrame (a + 4) :=
  ⟨0, a + 3, by omega, by omega⟩

def victim (a : Nat) : Fin (a + 4) := ⟨a, by omega⟩

theorem before_pos (a : Nat) (F : GapFrame (a + 4)) (k : Nat) (hk : k ≤ F.d) :
    before a (F.pos k) = beforeNat a (F.start + k) :=
  congrArg (beforeNat a) (pos_val F k hk)

theorem after_pos (a : Nat) (F : GapFrame (a + 4)) (k : Nat) (hk : k ≤ F.d) :
    after a (F.pos k) = afterNat a (F.start + k) :=
  congrArg (afterNat a) (pos_val F k hk)

theorem frames_join (a : Nat) (ha : 0 < a) :
    (leftFrame a ha).pos (leftFrame a ha).d = (rightFrame a).pos 0 ∧
    (mergedFrame a).d = (leftFrame a ha).d + (rightFrame a).d ∧
    (mergedFrame a).pos 0 = (leftFrame a ha).pos 0 ∧
    (mergedFrame a).pos (mergedFrame a).d = (rightFrame a).pos (rightFrame a).d := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · apply Fin.ext
    rw [pos_val (leftFrame a ha) (leftFrame a ha).d (Nat.le_refl _),
      pos_val (rightFrame a) 0 (Nat.zero_le _)]
    change 0 + a = a + 0
    exact Nat.zero_add a
  · apply Fin.ext
    rw [pos_val (mergedFrame a) (mergedFrame a).d (Nat.le_refl _),
      pos_val (rightFrame a) (rightFrame a).d (Nat.le_refl _)]
    change 0 + (a + 3) = a + 3
    exact Nat.zero_add (a + 3)

theorem fin_one_eq (x y : Fin 1) : x = y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  apply Fin.ext
  change x = y
  omega

/-- Strong zero-signal certificate, not the fresh-shot invariant. -/
structure GapCertificate {n : Nat} (F : GapFrame n) (C : Config n) : Prop where
  endpoints : (C (F.pos 0)).leader = true ∧ (C (F.pos F.d)).leader = true
  interior : ∀ k : Nat, 0 < k → k < F.d → (C (F.pos k)).leader = false
  labels : ∀ k : Nat, k < F.d → (C (F.pos (k + 1))).label =
    ⟨((C (F.pos k)).label.val + 1) % 1, Nat.mod_lt _ (by decide)⟩
  quiet : ∀ i : Fin n, (C i).signal_B = (0 : Fin 2)

theorem before_left_certificate (a : Nat) (ha : 0 < a) :
    GapCertificate (leftFrame a ha) (before a) := by
  constructor
  · constructor
    · rw [before_pos a (leftFrame a ha) 0 (Nat.zero_le _)] <;>
        simp [leftFrame, beforeNat]
    · rw [before_pos a (leftFrame a ha) (leftFrame a ha).d
        (Nat.le_refl _)] <;>
        simp [leftFrame, beforeNat]
  · intro k hk hkd
    change k < a at hkd
    rw [before_pos a (leftFrame a ha) k (Nat.le_of_lt hkd)]
    change (if 0 + k = 0 ∨ 0 + k = a ∨ 0 + k = a + 3 then true else false) = false
    rw [if_neg (by omega)]
  · intro k _hk
    exact fin_one_eq _ _
  · intro i
    rfl

theorem before_right_certificate (a : Nat) (ha : 0 < a) :
    GapCertificate (rightFrame a) (before a) := by
  constructor
  · constructor
    · rw [before_pos a (rightFrame a) 0 (Nat.zero_le _)] <;>
        simp [rightFrame, beforeNat]
    · rw [before_pos a (rightFrame a) (rightFrame a).d
        (Nat.le_refl _)] <;>
        simp [rightFrame, beforeNat]
  · intro k hk hkd
    change k < 3 at hkd
    rw [before_pos a (rightFrame a) k (Nat.le_of_lt hkd)]
    change (if a + k = 0 ∨ a + k = a ∨ a + k = a + 3 then true else false) = false
    rw [if_neg (by omega)]
  · intro k _hk
    exact fin_one_eq _ _
  · intro i
    rfl

theorem after_merged_certificate (a : Nat) :
    GapCertificate (mergedFrame a) (after a) := by
  constructor
  · constructor
    · rw [after_pos a (mergedFrame a) 0 (Nat.zero_le _)] <;>
        simp [mergedFrame, afterNat]
    · rw [after_pos a (mergedFrame a) (mergedFrame a).d
        (Nat.le_refl _)] <;>
        simp [mergedFrame, afterNat]
  · intro k hk hkd
    change k < a + 3 at hkd
    rw [after_pos a (mergedFrame a) k (Nat.le_of_lt hkd)]
    change (if 0 + k = 0 ∨ 0 + k = a + 3 then true else false) = false
    rw [if_neg (by omega)]
  · intro k _hk
    exact fin_one_eq _ _
  · intro i
    rfl

def topIdx (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => if p (m + 1) then m + 1 else topIdx p m

theorem topIdx_zero (p : Nat → Bool) : ∀ m : Nat,
    (∀ k, 0 < k → k ≤ m → p k = false) → topIdx p m = 0 := by
  intro m
  induction m with
  | zero => intro h; rfl
  | succ m ih =>
      intro h
      have hf := h (m + 1) (by omega) (Nat.le_refl _)
      rw [topIdx, hf]
      exact ih (fun k hk hkm => h k hk (by omega))

theorem topIdx_max (p : Nat → Bool) : ∀ m t : Nat,
    0 < t → t ≤ m → p t = true →
    (∀ k, t < k → k ≤ m → p k = false) → topIdx p m = t := by
  intro m
  induction m with
  | zero => intro t ht hm hp habove; omega
  | succ m ih =>
      intro t ht hm hp habove
      by_cases he : t = m + 1
      · subst t
        simp [topIdx, hp]
      · have hf := habove (m + 1) (by omega) (Nat.le_refl _)
        rw [topIdx, hf]
        exact ih t ht (by omega) hp (fun k hk hkm => habove k hk (by omega))

def bulletTop {n : Nat} (F : GapFrame n) (C : Config n) : Nat :=
  topIdx (fun k => decide (0 < (C (F.pos k)).bullet.val)) F.d

def signalTop {n : Nat} (F : GapFrame n) (C : Config n) : Nat :=
  topIdx (fun k => decide ((C (F.pos k)).signal_B.val = 1)) F.d

theorem signalTop_quiet {n : Nat} (F : GapFrame n) (C : Config n)
    (hq : ∀ i, (C i).signal_B = (0 : Fin 2)) : signalTop F C = 0 := by
  apply topIdx_zero
  intro k hk hkd
  rw [hq (F.pos k)] <;> decide

theorem before_left_top (a : Nat) (ha : 0 < a) :
    bulletTop (leftFrame a ha) (before a) = 0 := by
  apply topIdx_zero
  intro k hk hkd
  change k ≤ a at hkd
  have h1 : k ≠ a + 1 := by omega
  have h2 : k ≠ a + 2 := by omega
  rw [before_pos a (leftFrame a ha) k hkd] <;>
    simp [leftFrame, beforeNat, h1, h2]

theorem before_right_top (a : Nat) : bulletTop (rightFrame a) (before a) = 2 := by
  apply topIdx_max _ 3 2 (by decide) (by decide)
  · rw [before_pos a (rightFrame a) 2 (by change 2 ≤ 3; decide)] <;>
      simp [rightFrame, beforeNat]
  · intro k hk hkd
    have he : k = 3 := by omega
    subst k
    rw [before_pos a (rightFrame a) 3 (Nat.le_refl _)] <;>
      simp [rightFrame, beforeNat]

theorem after_merged_top (a : Nat) :
    bulletTop (mergedFrame a) (after a) = a + 2 := by
  apply topIdx_max _ (a + 3) (a + 2) (by omega) (by omega)
  · rw [after_pos a (mergedFrame a) (a + 2)
      (by change a + 2 ≤ a + 3; omega)] <;>
      simp [mergedFrame, afterNat, beforeNat]
  · intro k hk hkd
    have he : k = a + 3 := by omega
    subst k
    rw [after_pos a (mergedFrame a) (a + 3) (Nat.le_refl _)] <;>
      simp [mergedFrame, afterNat, beforeNat]

abbrev ReadyRule := (n : Nat) → GapFrame n → Config n → Prop

def ReadyCompatible (ready : ReadyRule) : Prop :=
  ∀ n F C, ready n F C → ∃ i : Fin n, (C i).signal_B = (1 : Fin 2)

def EndpointDeleted {n : Nat} (F : GapFrame n) (C : Config n) : Prop :=
  (C (F.pos 0)).leader = false ∨ (C (F.pos F.d)).leader = false

def GapDoneC (ready : ReadyRule) {n : Nat} (F : GapFrame n) (C : Config n) : Prop :=
  ready n F C ∨ EndpointDeleted F C

noncomputable def gapWC (ready : ReadyRule) {n : Nat}
    (F : GapFrame n) (C : Config n) : Nat := by
  classical
  exact if GapDoneC ready F C then 0
    else if bulletTop F C = 0 then F.d - signalTop F C
    else F.d + bulletTop F C

theorem certificate_not_done (ready : ReadyRule) (hr : ReadyCompatible ready)
    {n : Nat} (F : GapFrame n) (C : Config n) (hc : GapCertificate F C) :
    ¬ GapDoneC ready F C := by
  intro hd
  rcases hd with hd | hd
  · obtain ⟨i, hi⟩ := hr n F C hd
    have he : (0 : Fin 2) = 1 := (hc.quiet i).symm.trans hi
    have hv := congrArg Fin.val he
    change (0 : Nat) = 1 at hv
    omega
  · rcases hd with hl | hr
    · have he : true = false := hc.endpoints.1.symm.trans hl
      cases he
    · have he : true = false := hc.endpoints.2.symm.trans hr
      cases he

theorem before_left_rank (ready : ReadyRule) (hr : ReadyCompatible ready)
    (a : Nat) (ha : 0 < a) : gapWC ready (leftFrame a ha) (before a) = a := by
  classical
  have hc := before_left_certificate a ha
  have hd := certificate_not_done ready hr (leftFrame a ha) (before a) hc
  have hb := before_left_top a ha
  have hs := signalTop_quiet (leftFrame a ha) (before a) hc.quiet
  rw [gapWC, if_neg hd, if_pos hb]
  change a - signalTop (leftFrame a ha) (before a) = a
  rw [hs, Nat.sub_zero]

theorem before_right_rank (ready : ReadyRule) (hr : ReadyCompatible ready)
    (a : Nat) (ha : 0 < a) : gapWC ready (rightFrame a) (before a) = 5 := by
  classical
  have hd := certificate_not_done ready hr (rightFrame a) (before a)
    (before_right_certificate a ha)
  have hb := before_right_top a
  have hn : bulletTop (rightFrame a) (before a) ≠ 0 := by omega
  rw [gapWC, if_neg hd, if_neg hn]
  change 3 + bulletTop (rightFrame a) (before a) = 5
  rw [hb]

theorem after_merged_rank (ready : ReadyRule) (hr : ReadyCompatible ready)
    (a : Nat) : gapWC ready (mergedFrame a) (after a) = 2 * a + 5 := by
  classical
  have hd := certificate_not_done ready hr (mergedFrame a) (after a)
    (after_merged_certificate a)
  have hb := after_merged_top a
  have hn : bulletTop (mergedFrame a) (after a) ≠ 0 := by omega
  rw [gapWC, if_neg hd, if_neg hn, hb]
  change (a + 3) + (a + 2) = 2 * a + 5
  omega

/-- A consistent example; the counterfamily is independent of this choice. -/
def readyExample : ReadyRule := fun _ F C =>
  (C (F.pos F.d)).signal_B = (1 : Fin 2) ∧
    ∀ k : Nat, 0 < k → k ≤ F.d → (C (F.pos k)).bullet = (0 : Fin 3)

theorem readyExample_compatible : ReadyCompatible readyExample := by
  intro n F C h
  exact ⟨F.pos F.d, h.1⟩

/-- The successful deletion branch only, not the full K2 transition. -/
def deletionRow (l r : Cell 1) : Cell 1 × Cell 1 :=
  if l.leader = true ∧ l.shield = false ∧ r.bullet = (2 : Fin 3) then
    ({ l with leader := false }, { r with bullet := 1 })
  else (l, r)

def rowStep {n : Nat} (C : Config n) (e : Fin n) : Config n :=
  let q := deletionRow (C e) (C (right e))
  fun i => if i.val = e.val then q.1
    else if i.val = (right e).val then q.2 else C i

theorem victim_right_val (a : Nat) : (right (victim a)).val = a + 1 := by
  change (a + 1) % (a + 4) = a + 1
  exact Nat.mod_eq_of_lt (by omega)

theorem deletion_pair (a : Nat) (ha : 0 < a) :
    deletionRow (beforeNat a a) (beforeNat a (a + 1)) =
      (afterNat a a, afterNat a (a + 1)) := by
  have h0 : a ≠ 0 := by omega
  simp [deletionRow, beforeNat, afterNat, h0]

theorem rowStep_before (a : Nat) (ha : 0 < a) :
    rowStep (before a) (victim a) = after a := by
  have hl : before a (victim a) = beforeNat a a := rfl
  have hr : before a (right (victim a)) = beforeNat a (a + 1) :=
    congrArg (beforeNat a) (victim_right_val a)
  have he : (victim a).val = a := rfl
  funext i
  simp only [rowStep, hl, hr, deletion_pair a ha, he, victim_right_val]
  by_cases hi : i.val = a
  · simp [hi, after]
  · by_cases hj : i.val = a + 1
    · simp [hj, after]
    · simp [hi, hj, before, after, beforeNat, afterNat]

/-- Computed finite configurations and scans for the copied deletion row. -/
theorem configuration_counterfamily
    (ready : ReadyRule) (hr : ReadyCompatible ready) (K : Nat) :
    ∃ a : Nat, ∃ ha : 0 < a,
      GapCertificate (leftFrame a ha) (before a) ∧
      GapCertificate (rightFrame a) (before a) ∧
      GapCertificate (mergedFrame a) (after a) ∧
      rowStep (before a) (victim a) = after a ∧
      gapWC ready (leftFrame a ha) (before a) = a ∧
      gapWC ready (rightFrame a) (before a) = 5 ∧
      gapWC ready (mergedFrame a) (after a) = 2 * a + 5 ∧
      gapWC ready (leftFrame a ha) (before a) +
        gapWC ready (rightFrame a) (before a) + K <
        gapWC ready (mergedFrame a) (after a) := by
  let a := K + 1
  have ha : 0 < a := by dsimp [a]; omega
  refine ⟨a, ha, before_left_certificate a ha, before_right_certificate a ha,
    after_merged_certificate a, rowStep_before a ha,
    before_left_rank ready hr a ha, before_right_rank ready hr a ha,
    after_merged_rank ready hr a, ?_⟩
  have hL := before_left_rank ready hr a ha
  have hR := before_right_rank ready hr a ha
  have hM := after_merged_rank ready hr a
  have he : a = K + 1 := rfl
  omega

/-! Site credits are counted globally; ownership may be redistributed. -/

def bit (b : Bool) : Nat := if b then 1 else 0

def count {n : Nat} (c : Credits n) : List (Fin n) → Nat
  | [] => 0
  | i :: is => bit (c i) + count c is

theorem credit_additive {n : Nat} (c : Credits n) (L R : List (Fin n)) :
    count c (L ++ R) = count c L + count c R := by
  induction L with
  | nil => simp [count]
  | cons i is ih => simp only [List.cons_append, count, ih, Nat.add_assoc]

/-- Enumerates each member of Fin n once, by zero and the successor tail. -/
def w : {n : Nat} → Credits n → Nat
  | 0, _ => 0
  | n + 1, c => bit (c 0) + w (fun i : Fin n => c i.succ)

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by
  cases b <;> decide

theorem w_start_le {n : Nat} (c : Credits n) : w c ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      have ht := ih (fun i : Fin n => c i.succ)
      have hb := bit_le_one (c 0)
      change bit (c 0) + w (fun i : Fin n => c i.succ) ≤ n + 1
      omega

/-- No previously spent site can acquire a new credit. -/
def OnlySpends {n : Nat} (x y : Credits n) : Prop :=
  ∀ i : Fin n, y i = true → x i = true

theorem bit_monotone (a b : Bool) (h : b = true → a = true) : bit b ≤ bit a := by
  cases a <;> cases b <;> simp_all [bit]

theorem spend_monotone {n : Nat} (x y : Credits n) (h : OnlySpends x y) :
    w y ≤ w x := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      exact Nat.add_le_add (bit_monotone (x 0) (y 0) (h 0))
        (ih (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ)
          (fun i hi => h i.succ hi))

def spend {n : Nat} (c hit : Credits n) : Credits n :=
  fun i => if hit i then false else c i

theorem spend_only {n : Nat} (c hit : Credits n) : OnlySpends c (spend c hit) := by
  intro i hi
  cases hh : hit i with
  | false => simpa [spend, hh] using hi
  | true => simp [spend, hh] at hi

theorem spend_weight_le {n : Nat} (c hit : Credits n) : w (spend c hit) ≤ w c :=
  spend_monotone c (spend c hit) (spend_only c hit)

theorem revisit_spends_nothing {n : Nat} (c hit : Credits n) :
    spend (spend c hit) hit = spend c hit := by
  funext i
  cases hh : hit i <;> simp [spend, hh]

theorem spent_telescopes {n : Nat} (x y z : Credits n)
    (hxy : OnlySpends x y) (hyz : OnlySpends y z) :
    (w x - w y) + (w y - w z) = w x - w z := by
  have h1 := spend_monotone x y hxy
  have h2 := spend_monotone y z hyz
  omega

/-- Clockwise coordinates 1 through n; the cut has coordinate n. -/
def clockwiseDistance {n : Nat} (cut i : Fin n) : Nat :=
  if cut.val < i.val then i.val - cut.val else n + i.val - cut.val

theorem clockwiseDistance_bounds {n : Nat} (cut i : Fin n) :
    0 < clockwiseDistance cut i ∧ clockwiseDistance cut i ≤ n := by
  rcases cut with ⟨cv, hc⟩
  rcases i with ⟨iv, hi⟩
  change 0 < (if cv < iv then iv - cv else n + iv - cv) ∧
    (if cv < iv then iv - cv else n + iv - cv) ≤ n
  by_cases h : cv < iv
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

def Owns {n : Nat} (cut : Fin n) (lo hi : Nat) (i : Fin n) : Prop :=
  lo < clockwiseDistance cut i ∧ clockwiseDistance cut i ≤ hi

instance {n : Nat} (cut : Fin n) (lo hi : Nat) (i : Fin n) :
    Decidable (Owns cut lo hi i) := by
  unfold Owns
  infer_instance

def ownedCredits {n : Nat} (c : Credits n) (cut : Fin n) (lo hi : Nat) : Credits n :=
  fun i => if Owns cut lo hi i then c i else false

theorem halfOpen_split {n : Nat} (cut : Fin n) (lo mid hi : Nat)
    (hL : lo ≤ mid) (hR : mid ≤ hi) (i : Fin n) :
    Owns cut lo hi i ↔ Owns cut lo mid i ∨ Owns cut mid hi i := by
  unfold Owns
  omega

theorem halfOpen_disjoint {n : Nat} (cut : Fin n) (lo mid hi : Nat) (i : Fin n) :
    Owns cut lo mid i → ¬ Owns cut mid hi i := by
  unfold Owns
  omega

/-- The joint belongs to the left half-open interval and not the right. -/
theorem shared_cell_counted_once {n : Nat} (cut joint : Fin n) (lo mid hi : Nat)
    (hL : lo < mid) (hjoint : clockwiseDistance cut joint = mid) :
    Owns cut lo mid joint ∧ ¬ Owns cut mid hi joint := by
  unfold Owns
  rw [hjoint]
  constructor
  · exact ⟨hL, Nat.le_refl _⟩
  · intro h
    omega

theorem w_add_of_pointwise {n : Nat} (x y z : Credits n)
    (h : ∀ i, bit (z i) = bit (x i) + bit (y i)) : w z = w x + w y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have ht := ih (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ)
        (fun i : Fin n => z i.succ) (fun i => h i.succ)
      change bit (z 0) + w (fun i : Fin n => z i.succ) =
        (bit (x 0) + w (fun i : Fin n => x i.succ)) +
        (bit (y 0) + w (fun i : Fin n => y i.succ))
      rw [h 0, ht]
      omega

/-- Spatial additivity, not merely additivity of lists with duplicates. -/
theorem halfOpen_credit_additive {n : Nat} (c : Credits n) (cut : Fin n)
    (lo mid hi : Nat) (hL : lo ≤ mid) (hR : mid ≤ hi) :
    w (ownedCredits c cut lo hi) =
      w (ownedCredits c cut lo mid) + w (ownedCredits c cut mid hi) := by
  apply w_add_of_pointwise
  intro i
  by_cases hl : Owns cut lo mid i
  · have hr := halfOpen_disjoint cut lo mid hi i hl
    have hm := (halfOpen_split cut lo mid hi hL hR i).mpr (Or.inl hl)
    simp [ownedCredits, hl, hr, hm, bit]
  · by_cases hr : Owns cut mid hi i
    · have hm := (halfOpen_split cut lo mid hi hL hR i).mpr (Or.inr hr)
      simp [ownedCredits, hl, hr, hm, bit]
    · have hm : ¬ Owns cut lo hi i := by
        intro h
        rcases (halfOpen_split cut lo mid hi hL hR i).mp h with h | h
        · exact hl h
        · exact hr h
      simp [ownedCredits, hl, hr, hm, bit]

structure Ledger (n : Nat) where
  unspent : Credits n
  owners : List (List (Fin n))

/-- Ownership changes do not change the global site-credit map. -/
theorem merge_preserves_credits {n : Nat} (c : Credits n)
    (preOwners : List (List (Fin n))) (L R : List (Fin n))
    (postOwners : List (List (Fin n))) :
    let x : Ledger n := ⟨c, preOwners ++ (L :: R :: postOwners)⟩
    let y : Ledger n := ⟨c, preOwners ++ ((L ++ R) :: postOwners)⟩
    y.unspent = x.unspent ∧ w y.unspent = w x.unspent := by
  exact ⟨rfl, rfl⟩

/-- Long episodes must spend proportionally many distinct fresh credits. -/
def SpanChargedOnce {n : Nat} (B d : Nat) (x y : Credits n) : Prop :=
  d ≤ B * (w x - w y + 1)

theorem episode_cost_adapter {n : Nat} (c B d cost : Nat) (x y : Credits n)
    (hlocal : cost ≤ c * n * (2 * d)) (hcharge : SpanChargedOnce B d x y) :
    cost ≤ ((2 * c * B) * n) * ((w x - w y) + 1) := by
  calc
    cost ≤ c * n * (2 * d) := hlocal
    _ = (2 * c * n) * d := by ac_rfl
    _ ≤ (2 * c * n) * (B * (w x - w y + 1)) :=
      Nat.mul_le_mul_left (2 * c * n) hcharge
    _ = ((2 * c * B) * n) * ((w x - w y) + 1) := by ac_rfl

/-- The episode-step shape with C = 2 * c * B and no weight slack. -/
theorem episode_hstep {S : Type} {n : Nat}
    (next : S → S → Prop) (credits : S → Credits n) (phase : S → Nat)
    (span episodeBound : S → S → Nat) (c B : Nat)
    (hspend : ∀ x y, next x y → OnlySpends (credits x) (credits y))
    (hphase : ∀ x y, next x y → phase y < phase x)
    (hlocal : ∀ x y, next x y → episodeBound x y ≤ c * n * (2 * span x y))
    (hcharge : ∀ x y, next x y → SpanChargedOnce B (span x y) (credits x) (credits y)) :
    ∀ {x y}, next x y →
      w (credits y) ≤ w (credits x) ∧ phase y < phase x ∧
      episodeBound x y ≤ ((2 * c * B) * n) * ((w (credits x) - w (credits y)) + 1) := by
  intro x y hxy
  exact ⟨spend_monotone _ _ (hspend x y hxy), hphase x y hxy,
    episode_cost_adapter c B (span x y) (episodeBound x y)
      (credits x) (credits y) (hlocal x y hxy) (hcharge x y hxy)⟩

theorem no_spend_requires_short_span {n : Nat} (B d : Nat) (x y : Credits n)
    (he : w x = w y) (hc : SpanChargedOnce B d x y) : d ≤ B := by
  change d ≤ B * (w x - w y + 1) at hc
  simpa only [he, Nat.sub_self, Nat.zero_add, Nat.mul_one] using hc

end NonrenewableCredits

#print axioms NonrenewableCredits.pos_val
#print axioms NonrenewableCredits.pos_successor
#print axioms NonrenewableCredits.before_pos
#print axioms NonrenewableCredits.after_pos
#print axioms NonrenewableCredits.frames_join
#print axioms NonrenewableCredits.fin_one_eq
#print axioms NonrenewableCredits.before_left_certificate
#print axioms NonrenewableCredits.before_right_certificate
#print axioms NonrenewableCredits.after_merged_certificate
#print axioms NonrenewableCredits.topIdx_zero
#print axioms NonrenewableCredits.topIdx_max
#print axioms NonrenewableCredits.signalTop_quiet
#print axioms NonrenewableCredits.before_left_top
#print axioms NonrenewableCredits.before_right_top
#print axioms NonrenewableCredits.after_merged_top
#print axioms NonrenewableCredits.certificate_not_done
#print axioms NonrenewableCredits.before_left_rank
#print axioms NonrenewableCredits.before_right_rank
#print axioms NonrenewableCredits.after_merged_rank
#print axioms NonrenewableCredits.readyExample_compatible
#print axioms NonrenewableCredits.victim_right_val
#print axioms NonrenewableCredits.deletion_pair
#print axioms NonrenewableCredits.rowStep_before
#print axioms NonrenewableCredits.configuration_counterfamily
#print axioms NonrenewableCredits.credit_additive
#print axioms NonrenewableCredits.bit_le_one
#print axioms NonrenewableCredits.w_start_le
#print axioms NonrenewableCredits.bit_monotone
#print axioms NonrenewableCredits.spend_monotone
#print axioms NonrenewableCredits.spend_only
#print axioms NonrenewableCredits.spend_weight_le
#print axioms NonrenewableCredits.revisit_spends_nothing
#print axioms NonrenewableCredits.spent_telescopes
#print axioms NonrenewableCredits.clockwiseDistance_bounds
#print axioms NonrenewableCredits.halfOpen_split
#print axioms NonrenewableCredits.halfOpen_disjoint
#print axioms NonrenewableCredits.shared_cell_counted_once
#print axioms NonrenewableCredits.w_add_of_pointwise
#print axioms NonrenewableCredits.halfOpen_credit_additive
#print axioms NonrenewableCredits.merge_preserves_credits
#print axioms NonrenewableCredits.episode_cost_adapter
#print axioms NonrenewableCredits.episode_hstep
#print axioms NonrenewableCredits.no_spend_requires_short_span
