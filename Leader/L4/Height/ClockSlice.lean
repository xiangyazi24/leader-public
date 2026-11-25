import Leader.L4.Height.ClockHead
import Leader.L4.Height.LeaderBridge

/-!
# Uniform logical trials at an asynchronous clock frontier

Native decoding bounds both snapshot banks. Trial levels can overlap in
physical time with generation of the base slice. Coordinatewise flips of
the physical offers preserve that slice and permute all logical trial
assignments on words reaching the target. The resulting quarter bound
supplies the repaired-clock trial and its quadratic first-hit budget.
-/
namespace L4.Height.ClockHead

open L4.Compiler.Native

/-- Heights and proposed heights fit in the native height field. Proposals
are included because phase 5 may copy a stored proposal to the height. -/
def SnapshotHeightsBounded (B : Nat) (s : Snapshot) : Prop :=
  s.x < B ∧ s.proposal < B

/-- Both stored snapshot banks satisfy the native height-field invariant. -/
def ClockBanksBounded {m : Nat} (B : Nat) (cfg : Fin m → NativeRecord) : Prop :=
  ∀ i, SnapshotHeightsBounded B (cfg i).prior ∧
    SnapshotHeightsBounded B (cfg i).curr

/-- Every synchronous phase preserves both bounded height fields, regardless
of the neighbor records and of the offered bit. -/
theorem snapshotHeightsBounded_phase (B : Nat) (hB : 0 < B)
    (phase : Nat) (l c r : Snapshot) (b : Bool)
    (hc : SnapshotHeightsBounded B c) :
    SnapshotHeightsBounded B (phaseUpdate B phase l c r b) := by
  unfold phaseUpdate
  split
  · exact hc
  · exact hc
  · exact hc
  · exact ⟨hc.1, Nat.mod_lt _ hB⟩
  · exact hc
  · constructor
    · change (if c.approve && r.approve then c.proposal else c.x) < B
      split
      · exact hc.2
      · exact hc.1
    · exact hc.2
  · exact hc

/-- All clock actions preserve the bank invariant, including reset actions
and arbitrary input records; no clock legitimacy premise is needed. -/
theorem clockBanksBounded_finish (B : Nat) (hB : 0 < B)
    (l c r : NativeRecord) (a : ClockAction) (b : Bool)
    (hc : SnapshotHeightsBounded B c.prior ∧
      SnapshotHeightsBounded B c.curr) :
    SnapshotHeightsBounded B (finishNative B l c r a b).prior ∧
      SnapshotHeightsBounded B (finishNative B l c r a b).curr := by
  cases a with
  | reset => simpa [finishNative, SnapshotHeightsBounded] using And.intro hB hB
  | propagate t => simpa [finishNative, SnapshotHeightsBounded] using And.intro hB hB
  | clear => simpa [finishNative, SnapshotHeightsBounded] using And.intro hB hB
  | hold => exact hc
  | inc t => exact ⟨hc.2, snapshotHeightsBounded_phase B hB _ _ _ _ _ hc.2⟩

/-- Native decoding bounds both banks immediately: both heights and proposals
are reduced modulo `heightMod`, independently of the raw words. -/
theorem clockBanksBounded_decode {m : Nat} (r : Nat)
    (banks : Fin m → Bank) (sides : Fin m → Fin 3) :
    ClockBanksBounded (heightMod r) (fun i => decodeBank r (banks i) (sides i)) := by
  have hB : 0 < heightMod r := by
    unfold heightMod
    exact Nat.pow_pos (by decide)
  intro i
  exact ⟨⟨Nat.mod_lt _ hB, Nat.mod_lt _ hB⟩,
    ⟨Nat.mod_lt _ hB, Nat.mod_lt _ hB⟩⟩

/-- A literal activation preserves bounded banks at every site. -/
theorem clockBanksBounded_activate {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (s : WordState m) (hs : ClockBanksBounded B s.cfg) (i : Fin m) (b : Bool) :
    ClockBanksBounded B (activate B M hm s i b).cfg := by
  intro j
  by_cases he : j = i
  · subst j
    change SnapshotHeightsBounded B
        (setAt s.cfg i (finishNative B (s.cfg (left hm i)) (s.cfg i)
          (s.cfg (right hm i)) (clockAction M hm s i) b) i).prior ∧
      SnapshotHeightsBounded B
        (setAt s.cfg i (finishNative B (s.cfg (left hm i)) (s.cfg i)
          (s.cfg (right hm i)) (clockAction M hm s i) b) i).curr
    rw [setAt_self]
    exact clockBanksBounded_finish B hB _ _ _ _ _ (hs i)
  · simpa [activate, setAt, he] using hs j

/-- Every finite physical execution preserves the encoding invariant. -/
theorem clockBanksBounded_run {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (u : List (Fin (2 * m))) (s : WordState m) (hs : ClockBanksBounded B s.cfg) :
    ClockBanksBounded B (physicalRun B M hm s u).cfg := by
  induction u generalizing s with
  | nil => exact hs
  | cons e u ih =>
      exact ih (physicalNext B M hm s e)
        (clockBanksBounded_activate hm hB s hs (physicalSite e) (physicalBit e))

/-- A first-level observation, with the zero default when absent, retains
both field bounds. -/
theorem clockBanksBounded_levelCurr {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (h : List (Activation m)) (s : WordState m) (hs : ClockBanksBounded B s.cfg)
    (i : Fin m) (ell : Nat) :
    SnapshotHeightsBounded B
      ((levelCurr B M hm h s i ell).getD ({} : Snapshot)) := by
  induction h generalizing s with
  | nil =>
      by_cases he : s.lift i = ell
      · simpa [levelCurr, he] using (hs i).2
      · simpa [levelCurr, he, SnapshotHeightsBounded] using And.intro hB hB
  | cons a h ih =>
      by_cases he : s.lift i = ell
      · simpa [levelCurr, he] using (hs i).2
      · simpa [levelCurr, he] using ih (activate B M hm s a.1 a.2)
          (clockBanksBounded_activate hm hB s hs a.1 a.2)

/-- Every observed snapshot is bounded in the literal sense of `Bounded`,
which constrains its height alone. No generated warm-up is required. -/
theorem clockBanksBounded_observed {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (s : WordState m) (hs : ClockBanksBounded B s.cfg)
    (u : List (Fin (2 * m))) (ell : Nat) :
    Bounded B (observedSnapshot B M hm s u ell) := by
  intro i
  exact (clockBanksBounded_levelCurr hm hB (u.map physicalActivation) s hs i ell).1

end L4.Height.ClockHead
namespace L4.Height.ClockHead

open L4.Compiler.Native

/-- Eight legitimate equal clocks immediately before the aligned base 32. -/
def overlapStart : WordState 8 where
  cfg _ := { tick := 159, err := false, prior := {}, curr := {} }
  lift _ := 31

/-- A short asynchronous prefix that advances site zero twice while site
three remains below the next aligned base. -/
def overlapPrefix : List (Activation 8) :=
  [(6, false), (7, false), (0, false), (1, false),
    (2, false), (7, false), (1, false), (0, false)]

/-- The next activation reads the phase-one bit at lifted level 33. -/
def overlapHistory (b : Bool) : List (Activation 8) :=
  overlapPrefix ++ [(0, b)]

/-- The witness begins in the legitimate clock class. -/
theorem overlap_start_legit : Legit 256 (by decide) overlapStart := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i j _
  change Near 31 31
  exact ⟨by decide, by decide⟩

/-- Just before the final activation, the phase-one bit is needed at site
zero although site three has not reached base 32. -/
theorem overlap_before_bit :
    (syncRun 16 256 (by decide) overlapPrefix overlapStart).lift 0 = 33 ∧
    (syncRun 16 256 (by decide) overlapPrefix overlapStart).lift 3 = 31 ∧
    pendingNeed
      (clockAction 256 (by decide)
        (syncRun 16 256 (by decide) overlapPrefix overlapStart) 0)
      ((syncRun 16 256 (by decide) overlapPrefix overlapStart).cfg 0) = true ∧
    levelBit 16 256 (by decide) overlapPrefix overlapStart 0 33 = none := by
  decide +kernel

/-- For either offered bit, its literal first phase-one reading occurs
before all sites have reached the aligned base. A chronological cut at that
frontier therefore cannot treat this logical bit as an unread suffix bit. -/
theorem overlap_trial_bit_before_frontier (b : Bool) :
    (syncRun 16 256 (by decide) (overlapHistory b) overlapStart).lift 0 = 34 ∧
    (syncRun 16 256 (by decide) (overlapHistory b) overlapStart).lift 3 = 31 ∧
    levelBit 16 256 (by decide) (overlapHistory b) overlapStart 0 33 = some b ∧
    ((syncRun 16 256 (by decide) (overlapHistory b) overlapStart).cfg 0).curr.home = b := by
  cases b <;> decide +kernel

/-- The logical trial bit has already been read when the global base-32
frontier is still absent. -/
theorem overlap_frontier_not_reached (b : Bool) :
    ¬ (∀ i, 32 ≤
      (syncRun 16 256 (by decide) (overlapHistory b) overlapStart).lift i) := by
  intro h
  have hsite := h 3
  rw [(overlap_trial_bit_before_frontier b).2.1] at hsite
  omega

end L4.Height.ClockHead
namespace L4.Height.ClockSlice

open Classical
open L4.Height
open L4.Height.Couple

noncomputable section

private theorem list_sum_map_mono {α : Type} (f g : α → Nat)
    (h : ∀ a, f a ≤ g a) (xs : List α) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a) ih

private theorem list_indicator_sum {α : Type} (P : α → Prop) (xs : List α) :
    (xs.map (fun a => if P a then 1 else 0)).sum =
      (xs.filter (fun a => decide (P a))).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      by_cases ha : P a <;> simp [ha, ih, Nat.add_comm]

private theorem wordSum_list_sum {α : Type} {n : Nat}
    (f : α → List (Fin n) → Nat) (xs : List α) (t : Nat) :
    wordSum (fun u => (xs.map (fun a => f a u)).sum) t =
      (xs.map (fun a => wordSum (f a) t)).sum := by
  induction xs with
  | nil => simp [wordSum_zero]
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [wordSum_add_fun, ih]

private theorem wordSum_mono_length {n : Nat}
    (f g : List (Fin n) → Nat) (t : Nat)
    (h : ∀ u, u.length = t → f u ≤ g u) :
    wordSum f t ≤ wordSum g t := by
  induction t generalizing f g with
  | zero => exact h [] rfl
  | succ t ih =>
      simp only [wordSum]
      apply sum_ofFn_le
      intro e
      apply ih
      intro u hu
      apply h
      simp [hu]

/-- Flipping any fixed set of coordinates permutes all Boolean vectors. -/
theorem vector_xor_sum {J : Nat} (v : Fin J → Bool)
    (f : (Fin J → Bool) → Nat) :
    ((allVectors J).map (fun a => f (fun k => Bool.xor (v k) (a k)))).sum =
      ((allVectors J).map f).sum := by
  let flip := fun a : Fin J → Bool => fun k => Bool.xor (v k) (a k)
  have hflip (a : Fin J → Bool) : flip (flip a) = a := by
    funext k
    dsimp [flip]
    cases v k <;> cases a k <;> rfl
  let σ := fun e : Fin (2 ^ J) => encodeBits (flip (bitsOf e))
  have hσ (e : Fin (2 ^ J)) : σ (σ e) = e := by
    simp only [σ, bitsOf_encodeBits, hflip, encodeBits_bitsOf]
  have h := sum_ofFn_relabel σ σ hσ hσ (fun e => f (bitsOf e))
  simpa only [allVectors, List.map_ofFn, Function.comp_def,
    σ, bitsOf_encodeBits, flip] using h

/-- Averaging measure-preserving word transformations transfers a uniform
quarter bound even when the logical start is a function of the raw word. -/
theorem symmetrized_quarter_transfer {α : Type} {n J : Nat}
    (start : List (Fin n) → α)
    (read : List (Fin n) → Fin J → Bool)
    (transform : (Fin J → Bool) → List (Fin n) → List (Fin n))
    (E : List (Fin n) → Prop)
    (bad : α → (Fin J → Bool) → Prop) (t : Nat)
    (hpreserve : ∀ a,
      wordSum (fun u => if E (transform a u) then 1 else 0) t =
        wordSum (fun u => if E u then 1 else 0) t)
    (hcompare : ∀ a u, u.length = t → E (transform a u) →
      bad (start u) (fun k => Bool.xor (read u k) (a k)))
    (hquarter : ∀ s,
      4 * ((allVectors J).filter (fun b => decide (bad s b))).length ≤ 2 ^ J) :
    4 * wordSum (fun u => if E u then 1 else 0) t ≤ n ^ t := by
  let mass := wordSum (fun u => if E u then 1 else 0) t
  let count := fun u : List (Fin n) =>
    ((allVectors J).map (fun a => if E (transform a u) then 1 else 0)).sum
  have hcount : wordSum count t = 2 ^ J * mass := by
    dsimp [count]
    rw [wordSum_list_sum]
    simp only [hpreserve]
    change ((allVectors J).map (fun _ => mass)).sum = 2 ^ J * mass
    simp only [allVectors, List.map_ofFn]
    exact sum_ofFn_const (2 ^ J) mass
  have hpoint (u : List (Fin n)) (hu : u.length = t) :
      4 * count u ≤ 2 ^ J := by
    have hdom : count u ≤
        ((allVectors J).map (fun a =>
          if bad (start u) (fun k => Bool.xor (read u k) (a k)) then 1 else 0)).sum := by
      apply list_sum_map_mono
      intro a
      by_cases he : E (transform a u)
      · simp [he, hcompare a u hu he]
      · simp [he]
    rw [vector_xor_sum (read u) (fun b => if bad (start u) b then 1 else 0),
      list_indicator_sum (bad (start u))] at hdom
    exact Nat.le_trans (Nat.mul_le_mul_left 4 hdom) (hquarter (start u))
  have hsum := wordSum_mono_length
    (fun u => 4 * count u) (fun _ => 2 ^ J) t hpoint
  rw [wordSum_mul_left, hcount, wordSum_const] at hsum
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos J)
  calc
    (4 * mass) * 2 ^ J = 4 * (2 ^ J * mass) := by ac_rfl
    _ ≤ n ^ t * 2 ^ J := hsum

/-- Inspect successive actual prefixes, and at the first successful stop
apply the suffix event to the complete stopping history and remaining word.
If no prefix is a stop, the event is false. -/
def firstPrefixEvent {n : Nat}
    (stop : List (Fin n) → Bool)
    (F : List (Fin n) → List (Fin n) → Prop)
    (history : List (Fin n)) : List (Fin n) → Prop
  | [] => if stop history then F history [] else False
  | e :: es => if stop history then F history (e :: es)
      else firstPrefixEvent stop F (history ++ [e]) es

private theorem firstPrefixEvent_at_stop {n : Nat}
    (stop : List (Fin n) → Bool)
    (F : List (Fin n) → List (Fin n) → Prop)
    (h : List (Fin n)) (hs : stop h = true) (u : List (Fin n)) :
    firstPrefixEvent stop F h u = F h u := by
  cases u <;> simp [firstPrefixEvent, hs]

/-- Finite counting strong Markov principle at a word-dependent first-prefix
stop. Every terminal history has a uniform suffix estimate; summing the
stopping tree preserves that same fraction at its root. -/
theorem first_prefix_fraction_transfer {n : Nat}
    (stop : List (Fin n) → Bool)
    (F : List (Fin n) → List (Fin n) → Prop)
    (p q : Nat)
    (hbound : ∀ h, stop h = true → ∀ t,
      p * wordSum (fun u => if F h u then 1 else 0) t ≤ q * n ^ t)
    (history : List (Fin n)) (t : Nat) :
    p * wordSum (fun u => if firstPrefixEvent stop F history u then 1 else 0) t ≤
      q * n ^ t := by
  induction t generalizing history with
  | zero =>
      by_cases hs : stop history = true
      · simpa only [firstPrefixEvent_at_stop stop F history hs] using
          hbound history hs 0
      · simp [wordSum, firstPrefixEvent, hs]
  | succ t ih =>
      by_cases hs : stop history = true
      · simpa only [firstPrefixEvent_at_stop stop F history hs] using
          hbound history hs (t + 1)
      · simp only [wordSum, firstPrefixEvent, hs]
        rw [← sum_ofFn_mul_left]
        calc
          (List.ofFn (fun e : Fin n => p * wordSum
            (fun u => if firstPrefixEvent stop F (history ++ [e]) u then 1 else 0)
            t)).sum ≤ (List.ofFn (fun _ : Fin n => q * n ^ t)).sum := by
              apply sum_ofFn_le
              intro e
              exact ih (history ++ [e])
          _ = n * (q * n ^ t) := sum_ofFn_const n (q * n ^ t)
          _ = q * n ^ (t + 1) := by rw [Nat.pow_succ]; ac_rfl

end
end L4.Height.ClockSlice
namespace L4.Height.ClockHead

open Classical L4.Compiler.Native Couple

noncomputable section

/-- A mask indexed by round and site changes only offers at the trial levels. -/
private def trialMask {m Q : Nat} (base : Nat) (a : Fin (Q*m) → Bool)
    (s : WordState m) (i : Fin m) : Bool :=
  ((phaseRound? base Q (s.lift i)).map (fun r => a (phaseIndex r i))).getD false

private def maskLetter {m Q : Nat} (base : Nat) (a : Fin (Q*m) → Bool)
    (s : WordState m) (e : Fin (2*m)) :=
  if trialMask base a s (physicalSite e) then physicalFlip e else e

private theorem mask_site {m Q : Nat} (base : Nat) (a : Fin (Q*m) → Bool)
    (s : WordState m) (e : Fin (2*m)) :
    physicalSite (maskLetter base a s e) = physicalSite e := by
  unfold maskLetter
  split <;> simp

private theorem mask_invol {m Q : Nat} (base : Nat) (a : Fin (Q*m) → Bool)
    (s : WordState m) (e : Fin (2*m)) :
    maskLetter base a s (maskLetter base a s e) = e := by
  unfold maskLetter
  cases h : trialMask base a s (physicalSite e) <;> simp [h]

private def maskWord {m Q : Nat} (B M base : Nat) (hm : 0<m)
    (a : Fin (Q*m) → Bool) (s : WordState m) : List (Fin (2*m)) → List (Fin (2*m))
  | [] => []
  | e :: u => maskLetter base a s e :: maskWord B M base hm a (physicalNext B M hm s e) u

/-- The permutation at each node of the scheduler tree preserves its uniform mass. -/
private theorem maskWord_mass {m Q : Nat} (B M base : Nat) (hm : 0<m)
    (a : Fin (Q*m) → Bool) (d : Nat) (s : WordState m) (f : List (Fin (2*m)) → Nat) :
    wordSum (fun u => f (maskWord B M base hm a s u)) d = wordSum f d := by
  induction d generalizing s f with
  | zero => rfl
  | succ d ih =>
    change (List.ofFn (fun e => wordSum (fun u => f (maskLetter base a s e ::
      maskWord B M base hm a (physicalNext B M hm s e) u)) d)).sum = _
    calc
      _ = (List.ofFn (fun e => wordSum (fun u => f (maskLetter base a s e :: u)) d)).sum := by
        apply sum_ofFn_eq
        intro e
        exact ih _ (fun u => f (maskLetter base a s e :: u))
      _ = _ := sum_ofFn_relabel _ _ (mask_invol base a s) (mask_invol base a s)
        (fun e => wordSum (fun u => f (e :: u)) d)

private theorem clockAction_lift_eq {m M : Nat} (hm : 0<m) (hM : ClockParams M)
    {s t : WordState m} (hs : Legit M hm s) (ht : Legit M hm t)
    (hl : s.lift = t.lift) (i : Fin m) : clockAction M hm s i = clockAction M hm t i := by
  rw [nativeClock_normal hM hm s hs, nativeClock_normal hM hm t ht, hl]

/-- An advancing center below the base reads only sites at its own level
or one higher. Their complete records still agree in the two executions. -/
private theorem masked_step {m B M Q : Nat} (base : Nat) (hm : 0<m) (hM : ClockParams M)
    (a : Fin (Q*m) → Bool) (s t : WordState m)
    (hs : Legit M hm s) (ht : Legit M hm t) (hl : s.lift = t.lift)
    (hc : ∀ j, s.lift j ≤ base → s.cfg j = t.cfg j) (e : Fin (2*m)) :
    let v := physicalNext B M hm s e
    let w := physicalNext B M hm t (maskLetter base a s e)
    v.lift = w.lift ∧ ∀ j, v.lift j ≤ base → v.cfg j = w.cfg j := by
  let i := physicalSite e
  let b := physicalBit e
  let b' := physicalBit (maskLetter base a s e)
  dsimp only
  unfold physicalNext
  rw [mask_site]
  change (activate B M hm s i b).lift = (activate B M hm t i b').lift ∧ _
  have ha := clockAction_lift_eq hm hM hs ht hl i
  constructor
  · simp only [activate, hl, ha]
  · intro j hj
    change (activate B M hm s i b).lift j ≤ base at hj
    change (activate B M hm s i b).cfg j = (activate B M hm t i b').cfg j
    by_cases he : j = i
    · subst j
      have hn := nativeClock_normal hM hm s hs i
      cases hcan : canAdvanceBool hm s.lift i with
      | false =>
        have hhold : clockAction M hm s i = .hold := by simpa [hcan] using hn
        rw [activate_of_hold hm s i b hhold] at hj ⊢
        rw [activate_of_hold hm t i b' (ha.symm.trans hhold)]
        exact hc i hj
      | true =>
        have hi : clockAction M hm s i = .inc (clockOf M (s.lift i+1)) := by
          simpa [hcan] using hn
        have hfront := (canAdvanceBool_eq_true hm s.lift i).1 hcan
        have hj' : s.lift i+1 ≤ base := by simpa [activate, hi, advanceLift] using hj
        have hrec (k : Fin m) (hk : s.lift k = s.lift i ∨ s.lift k = s.lift i+1) :
            s.cfg k = t.cfg k := hc k (by rcases hk with h|h <;> omega)
        have hrnd : phaseRound? base Q (s.lift i) = none := by
          have hn' : ¬ ∃ r : Fin Q, s.lift i = base + 32*r.val+1 := by
            rintro ⟨r,hr⟩
            omega
          simp [phaseRound?, hn']
        have hb : b' = b := by
          change physicalBit (if trialMask base a s i then physicalFlip e else e) = physicalBit e
          simp [trialMask,hrnd]
        simp only [activate, setAt_self, ← ha, hrec _ hfront.1,
          hrec _ hfront.2, hc i (by omega), hb]
    · simp only [activate, setAt_other _ _ _ _ he] at hj ⊢
      exact hc j hj

private theorem phaseRound_at {base Q : Nat} (r : Fin Q) :
    phaseRound? base Q (base + 32*r.val+1) = some r := by
  have h : ∃ j : Fin Q, base + 32*r.val+1 = base + 32*j.val+1 := ⟨r,rfl⟩
  unfold phaseRound?
  rw [dif_pos h]
  congr 1
  apply Fin.ext
  have he := Classical.choose_spec h
  omega

private theorem masked_history {m B M Q : Nat} (base : Nat) (hm : 0<m) (hM : ClockParams M)
    (a : Fin (Q*m) → Bool) (u : List (Fin (2*m))) (s t : WordState m)
    (hs : Legit M hm s) (ht : Legit M hm t) (hl : s.lift = t.lift)
    (hc : ∀ j, s.lift j ≤ base → s.cfg j = t.cfg j) :
    let w := maskWord B M base hm a s u
    (∀ i, levelCurr B M hm (w.map physicalActivation) t i base =
      levelCurr B M hm (u.map physicalActivation) s i base) ∧
      (physicalRun B M hm t w).lift = (physicalRun B M hm s u).lift := by
  induction u generalizing s t with
  | nil =>
    refine ⟨?_,hl.symm⟩
    intro i
    by_cases he : s.lift i = base
    · simp [maskWord,levelCurr,← hl,he,hc i (Nat.le_of_eq he)]
    · simp [maskWord,levelCurr,← hl,he]
  | cons e u ih =>
    let e' := maskLetter base a s e
    have hn := masked_step (B:=B) base hm hM a s t hs ht hl hc e
    have htail := ih (physicalNext B M hm s e) (physicalNext B M hm t e')
      (legit_activate hM hm s hs _ _) (legit_activate hM hm t ht _ _) hn.1 hn.2
    refine ⟨?_,htail.2⟩
    intro i
    by_cases he : s.lift i = base
    · simp [maskWord,levelCurr,← hl,he,hc i (Nat.le_of_eq he)]
    · have htne : t.lift i ≠ base := by rw [← hl]; exact he
      change (if t.lift i = base then some (t.cfg i).curr else
        levelCurr B M hm
          ((maskWord B M base hm a (physicalNext B M hm s e) u).map physicalActivation)
          (physicalNext B M hm t e') i base) =
        (if s.lift i = base then some (s.cfg i).curr else
          levelCurr B M hm (u.map physicalActivation) (physicalNext B M hm s e) i base)
      rw [if_neg htne, if_neg he]
      exact htail.1 i

/-- On each orbit the clock trajectories and first observations at the
base agree, including the default for sites not yet observed. -/
private theorem masked_base {m B M Q : Nat} (base : Nat) (hm : 0<m) (hM : ClockParams M)
    (a : Fin (Q*m) → Bool) (u : List (Fin (2*m))) (s : WordState m) (hs : Legit M hm s) :
    observedSnapshot B M hm s (maskWord B M base hm a s u) base =
      observedSnapshot B M hm s u base ∧
      (physicalRun B M hm s (maskWord B M base hm a s u)).lift =
        (physicalRun B M hm s u).lift := by
  have hh := masked_history (B:=B) base hm hM a u s s hs hs rfl (fun _ _ => rfl)
  exact ⟨funext (fun i => congrArg (fun o : Option Snapshot => o.getD {}) (hh.1 i)), hh.2⟩

end
end L4.Height.ClockHead
namespace L4.Height.ClockHead

open Classical L4.Compiler.Native

noncomputable section

private theorem coverage_lift_step {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2*m)) (i : Fin m) :
    (physicalNext B M hm s e).lift i = s.lift i ∨
      (physicalNext B M hm s e).lift i = s.lift i + 1 := by
  by_cases hi : i = physicalSite e
  · subst i
    cases ha : clockAction M hm s (physicalSite e) <;>
      simp [physicalNext, activate, ha, advanceLift]
  · left
    simp [physicalNext, activate, hi]

private theorem coverage_increment_data {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2*m)) (i : Fin m)
    (hsucc : (physicalNext B M hm s e).lift i = s.lift i + 1) :
    physicalSite e = i ∧ ∃ tick, clockAction M hm s i = ClockAction.inc tick := by
  by_cases hi : i = physicalSite e
  · subst i
    refine ⟨rfl, ?_⟩
    cases ha : clockAction M hm s (physicalSite e) with
    | inc tick => exact ⟨tick, rfl⟩
    | reset => simp [physicalNext, activate, ha, advanceLift] at hsucc
    | propagate tick => simp [physicalNext, activate, ha, advanceLift] at hsucc
    | clear => simp [physicalNext, activate, ha, advanceLift] at hsucc
    | hold => simp [physicalNext, activate, ha, advanceLift] at hsucc
  · have heq : (physicalNext B M hm s e).lift i = s.lift i := by
      simp [physicalNext, activate, hi]
    omega

/-- Crossing a trial's draw level reveals its round-and-site index, even
when the starting heights are unequal and no global frontier has been hit. -/
theorem crossed_reveal {m Q : Nat} (B M base : Nat) (hm : 0 < m)
    (hp : 32 ∣ M/2) (hz : base%32 = 0) (r : Fin Q) (i : Fin m)
    (u : List (Fin (2*m))) (s : WordState m)
    (hle : s.lift i ≤ base+32*r.val+1)
    (hgt : base+32*r.val+1 < (physicalRun B M hm s u).lift i) :
    Couple.firstReveal (physSource B M base Q hm) (phaseIndex r i) s u ≠ none := by
  induction u generalizing s with
  | nil =>
      change base+32*r.val+1 < s.lift i at hgt
      omega
  | cons e u ih =>
      have hstep := coverage_lift_step B M hm s e i
      by_cases hcross : base+32*r.val+1 < (physicalNext B M hm s e).lift i
      · have hold : s.lift i = base+32*r.val+1 := by
          rcases hstep with h | h <;> omega
        have hsucc : (physicalNext B M hm s e).lift i = s.lift i+1 := by
          rcases hstep with h | h <;> omega
        obtain ⟨hsite, tick, hact⟩ := coverage_increment_data B M hm s e i hsucc
        have hphase : clockOf M (s.lift i) % 32 = 1 := by
          rw [hold]
          have hmod := clockOf_mod_phase (M := M) (ellzero := base)
            (n := 32*r.val+1) hp hz
          have hrem : (32*r.val+1)%32 = 1 := by omega
          simpa only [Nat.add_assoc, hrem] using hmod
        have hbit : (physSource B M base Q hm).bitOf s e =
            some (phaseIndex r i, physicalBit e) := by
          change physicalBitOf M base Q hm s e = _
          unfold physicalBitOf phaseRevealIndex?
          rw [hsite, hact, if_pos hphase, hold, phaseRound_at r]
          rfl
        rw [Couple.firstReveal, hbit]
        simp
      · have hnext : (physicalNext B M hm s e).lift i ≤ base+32*r.val+1 := by
          omega
        have htail := ih (physicalNext B M hm s e) hnext hgt
        rw [Couple.firstReveal]
        cases hb : (physSource B M base Q hm).bitOf s e with
        | none => exact htail
        | some p =>
            rcases p with ⟨k,b⟩
            by_cases hk : k = phaseIndex r i
            · simp [hk]
            · simpa only [if_neg hk, physSource_next] using htail

/-- Reaching a level from below supplies its actual first snapshot, without
any assumption about agreement with a generated logical computation. -/
theorem slice_observation_exists {m B M : Nat} (hm : 0 < m)
    (u : List (Fin (2*m))) (s : WordState m) (i : Fin m) (target : Nat)
    (hstart : s.lift i ≤ target)
    (hreach : target ≤ (physicalRun B M hm s u).lift i) :
    ∃ value, levelCurr B M hm (u.map physicalActivation) s i target = some value := by
  induction u generalizing s with
  | nil =>
      have he : s.lift i = target := by
        change target ≤ s.lift i at hreach
        omega
      exact ⟨(s.cfg i).curr, by simp [levelCurr, he]⟩
  | cons e u ih =>
      by_cases he : s.lift i = target
      · exact ⟨(s.cfg i).curr, by simp [levelCurr, he]⟩
      · have hstep := coverage_lift_step B M hm s e i
        have hnext : (physicalNext B M hm s e).lift i ≤ target := by
          rcases hstep with hs | hs <;> omega
        obtain ⟨value, hv⟩ := ih (physicalNext B M hm s e) hnext hreach
        refine ⟨value, ?_⟩
        simpa [levelCurr, he, physicalActivation, physicalNext] using hv

end
end L4.Height.ClockHead
namespace L4.Height.ClockHead

open Classical L4.Compiler.Native Couple

noncomputable section

/-- Equal legitimate lifts give the same reveal coordinate at each site. -/
private theorem masked_reveal_index {m M Q : Nat}
    (base : Nat) (hm : 0 < m) (hM : ClockParams M)
    (s t : WordState m) (hs : Legit M hm s) (ht : Legit M hm t)
    (hl : s.lift = t.lift) (i : Fin m) :
    phaseRevealIndex? M base Q hm t i = phaseRevealIndex? M base Q hm s i := by
  have ha := clockAction_lift_eq hm hM hs ht hl i
  unfold phaseRevealIndex?
  rw [← ha, ← hl]

/-- At a revealed coordinate, the site mask is the mask of that coordinate. -/
private theorem trialMask_of_index {m M Q : Nat}
    (base : Nat) (hm : 0 < m) (a : Fin (Q*m) → Bool)
    (s : WordState m) (i : Fin m) (k : Fin (Q*m))
    (hk : phaseRevealIndex? M base Q hm s i = some k) :
    trialMask base a s i = a k := by
  cases ha : clockAction M hm s i with
  | reset => simp [phaseRevealIndex?, ha] at hk
  | propagate tick => simp [phaseRevealIndex?, ha] at hk
  | clear => simp [phaseRevealIndex?, ha] at hk
  | hold => simp [phaseRevealIndex?, ha] at hk
  | inc tick =>
      by_cases hp : clockOf M (s.lift i) % 32 = 1
      · simp only [phaseRevealIndex?, ha, if_pos hp] at hk
        cases hr : phaseRound? base Q (s.lift i) with
        | none => simp [hr] at hk
        | some r =>
            have he : phaseIndex r i = k := by simpa [hr] using hk
            simp [trialMask, hr, he]
      · simp [phaseRevealIndex?, ha, hp] at hk

private theorem mask_bit {m Q : Nat} (base : Nat) (a : Fin (Q*m) → Bool)
    (s : WordState m) (e : Fin (2*m)) :
    physicalBit (maskLetter base a s e) =
      Bool.xor (physicalBit e) (trialMask base a s (physicalSite e)) := by
  cases hb : physicalBit e <;>
    cases ha : trialMask base a s (physicalSite e) <;>
      simp [maskLetter, ha, hb]

/-- The mask preserves each emitted index and flips exactly its assigned bit. -/
private theorem masked_bitOf {m M Q : Nat}
    (base : Nat) (hm : 0 < m) (hM : ClockParams M)
    (a : Fin (Q*m) → Bool) (s t : WordState m)
    (hs : Legit M hm s) (ht : Legit M hm t) (hl : s.lift = t.lift)
    (e : Fin (2*m)) :
    physicalBitOf M base Q hm t (maskLetter base a s e) =
      (physicalBitOf M base Q hm s e).map
        (fun p => (p.1, Bool.xor p.2 (a p.1))) := by
  unfold physicalBitOf
  rw [mask_site, masked_reveal_index base hm hM s t hs ht hl]
  cases hi : phaseRevealIndex? M base Q hm s (physicalSite e) with
  | none => rfl
  | some k =>
      simp only [Option.map_some]
      rw [mask_bit, trialMask_of_index base hm a s (physicalSite e) k hi]

/-- First reveals transform coordinatewise under the causal scheduler mask.
The two executions may differ above the base, but retain their common lift
and their complete records at all levels at or below the base. -/
private theorem masked_reveal {m B M Q : Nat}
    (base : Nat) (hm : 0 < m) (hM : ClockParams M)
    (a : Fin (Q*m) → Bool) (u : List (Fin (2*m)))
    (s t : WordState m) (hs : Legit M hm s) (ht : Legit M hm t)
    (hl : s.lift = t.lift)
    (hc : ∀ j, s.lift j ≤ base → s.cfg j = t.cfg j)
    (k : Fin (Q*m)) :
    firstReveal (physSource B M base Q hm) k t (maskWord B M base hm a s u) =
      (firstReveal (physSource B M base Q hm) k s u).map
        (fun b => Bool.xor b (a k)) := by
  let S := physSource B M base Q hm
  have hnext (z : WordState m) (e : Fin (2*m)) :
      S.next z e = physicalNext B M hm z e :=
    physSource_next B M base Q hm z e
  change firstReveal S k t (maskWord B M base hm a s u) =
    (firstReveal S k s u).map (fun b => Bool.xor b (a k))
  induction u generalizing s t with
  | nil => rfl
  | cons e u ih =>
      have hv : Legit M hm (physicalNext B M hm s e) :=
        legit_activate hM hm s hs (physicalSite e) (physicalBit e)
      have hw : Legit M hm
          (physicalNext B M hm t (maskLetter base a s e)) :=
        legit_activate hM hm t ht (physicalSite (maskLetter base a s e))
          (physicalBit (maskLetter base a s e))
      have hstep := masked_step (B := B) base hm hM a s t hs ht hl hc e
      have hrec := ih (physicalNext B M hm s e)
        (physicalNext B M hm t (maskLetter base a s e)) hv hw hstep.1 hstep.2
      have hb : S.bitOf t (maskLetter base a s e) =
          (S.bitOf s e).map (fun p => (p.1, Bool.xor p.2 (a p.1))) :=
        masked_bitOf base hm hM a s t hs ht hl e
      cases he : S.bitOf s e with
      | none =>
          have hb' : S.bitOf t (maskLetter base a s e) = none := by
            simpa only [he, Option.map_none] using hb
          simpa only [maskWord, firstReveal, he, hb', Option.map_none, hnext] using hrec
      | some p =>
          rcases p with ⟨j, b⟩
          have hb' : S.bitOf t (maskLetter base a s e) =
              some (j, Bool.xor b (a j)) := by
            simpa only [he, Option.map_some] using hb
          by_cases hj : j = k
          · subst j
            simp only [maskWord, firstReveal, he, hb', ite_true, Option.map_some]
          · simpa only [maskWord, firstReveal, he, hb', if_neg hj, hnext] using hrec

end
end L4.Height.ClockHead
namespace L4.Height.ClockHead
open Classical L4.Compiler.Native Couple
noncomputable section

/-- Masking trial offers preserves the word-dependent base snapshot while
translating the fully revealed trial vector by an arbitrary Boolean mask. -/
private theorem legitimate_uncertified_quarter {m B M base : Nat}
    (hm : 0 < m) (hmb : m < B) (hM : ClockParams M)
    (hp : 32 ∣ M/2) (hz : base%32 = 0)
    (s : WordState m) (hl : Legit M hm s)
    (hbelow : ∀ i, s.lift i < base) (hb : ClockBanksBounded B s.cfg) (d : Nat) :
    4*wordSum (fun u =>
      if uncertifiedSlice B M (base+32*(2^19*m)) hm s u then 1 else 0) d ≤
      (2*m)^d := by
  let Q := 2^19*m
  let target := base+32*Q
  let S := physSource B M base Q hm
  have hB : 0 < B := Nat.lt_trans hm hmb
  let starts := {v : Fin m → Snapshot // Bounded B v}
  let start : List (Fin (2*m)) → starts := fun u =>
    ⟨observedSnapshot B M hm s u base,
      clockBanksBounded_observed hm hB s hb u base⟩
  let bad := fun v : starts => fun a : Fin (Q*m) → Bool =>
    anchorCount hm (runRounds B hm (vecRounds Q m a) v.val) ≠ 1
  apply ClockSlice.symmetrized_quarter_transfer start
    (readVector S s) (fun a => maskWord B M base hm a s)
    (uncertifiedSlice B M target hm s) bad d
  · intro a
    exact maskWord_mass B M base hm a d s
      (fun u => if uncertifiedSlice B M target hm s u then 1 else 0)
  · intro a u _ hE
    let v := maskWord B M base hm a s u
    have hbase := masked_base (B := B) base hm hM a u s hl
    have hreach (i : Fin m) : target ≤ (physicalRun B M hm s u).lift i := by
      rw [← hbase.2]
      exact hE.1 i
    have hcovered (k : Fin (Q*m)) : firstReveal S k s u ≠ none := by
      obtain ⟨r, i, hk⟩ := phaseIndex_surjective (Q := Q) hm k
      rw [← hk]
      apply crossed_reveal B M base hm hp hz r i u s
      · have hi := hbelow i
        omega
      · have hi := hreach i
        have hr := r.isLt
        dsimp [target] at hi
        omega
    have hread : readVector S s v =
        fun k => Bool.xor (readVector S s u k) (a k) := by
      funext k
      have he := masked_reveal (B := B) base hm hM a u s s hl hl rfl
        (fun _ _ => rfl) k
      cases hv : firstReveal S k s u with
      | none => exact (hcovered k hv).elim
      | some b =>
        change (firstReveal S k s v).getD false = Bool.xor _ (a k)
        change firstReveal S k s v =
          (firstReveal S k s u).map (fun b => Bool.xor b (a k)) at he
        rw [he, hv]
        simp only [readVector, hv, Option.map_some, Option.getD_some]
    have hobs : observedSnapshot B M hm s v target =
        runRounds B hm (vecRounds Q m (readVector S s v))
          (observedSnapshot B M hm s v base) := by
      funext i
      obtain ⟨value, hv⟩ := slice_observation_exists hm v s i target
        (by have hi := hbelow i; dsimp [target]; omega) (hE.1 i)
      have hc := virtual_physical_observation hM hm hp hz Q s v hl hbelow i value hv
      rw [roundBits_readVector] at hc
      simpa only [observedSnapshot, hv, Option.getD_some] using hc
    change anchorCount hm
      (runRounds B hm (vecRounds Q m (fun k => Bool.xor (readVector S s u k) (a k)))
        (observedSnapshot B M hm s u base)) ≠ 1
    intro hone
    apply hE.2
    refine ⟨clockBanksBounded_observed hm hB s hb v target, ?_⟩
    rw [hobs, hbase.1, hread]
    exact hone
  · intro v
    have hfilter : (fun b : Fin (Q*m) → Bool => @decide (bad v b) (Classical.propDecidable _)) =
        (fun b => decide
          (anchorCount hm (runRounds B hm (vecRounds Q m b) v.val) ≠ 1)) := by
      funext b
      by_cases h : anchorCount hm (runRounds B hm (vecRounds Q m b) v.val) ≠ 1
      · simp [bad, h]
      · simp [bad, h]
    rw [hfilter]
    exact logical_quarter_vectors hm hmb v.val v.property

/-- The concrete coherent-coset trial has quarter-mass uncertified slices.
The adaptive base snapshot is handled by a uniform orbit count, without a
stopping-time assumption on the asynchronous frontier. -/
theorem clock_uncertified_quarter {m B M base : Nat}
    (hm : 0 < m) (hmb : m < B) (hM : ClockParams M)
    (hp : 32 ∣ M/2) (hz : base%32 = 0)
    (s : WordState m) (hc : LegitCoset M hm s)
    (hbelow : ∀ i, s.lift i < base) (hb : ClockBanksBounded B s.cfg) (d : Nat) :
    4*wordSum (fun u =>
      if uncertifiedSlice B M (base+32*(2^19*m)) hm s u then 1 else 0) d ≤
      (2*m)^d := by
  have hbcanon : ClockBanksBounded B (canon M s).cfg := by
    intro i
    change SnapshotHeightsBounded B ((canon M s).cfg i).prior ∧
      SnapshotHeightsBounded B ((canon M s).cfg i).curr
    simpa only [canon_prior, canon_curr] using hb i
  have hquarter := legitimate_uncertified_quarter hm hmb hM hp hz (canon M s)
    (canon_legit hc) hbelow hbcanon d
  apply Nat.le_trans (Nat.mul_le_mul_left 4 ?_) hquarter
  apply wordSum_mono
  intro u
  have he := clock_run_canon_lift (B := B) hm hM s hc none u
  simp only [clock_run_physical] at he
  have ho := clock_canon_observed (B := B) hm hM hp s hc u (base+32*(2^19*m))
  have hsame : uncertifiedSlice B M (base+32*(2^19*m)) hm s u =
      uncertifiedSlice B M (base+32*(2^19*m)) hm (canon M s) u := by
    apply propext
    simp only [uncertifiedSlice, he, ho]
  rw [hsame]
  exact Nat.le_refl _

end
end L4.Height.ClockHead
namespace L4.Height.ClockHead

open L4.Compiler.Native
open Classical

noncomputable section

/-- The original clock state together with the invariant on its two banks. -/
private abbrev BoundedClockState (m B : Nat) :=
  {x : OverrunState m // ClockBanksBounded B x.1.cfg}

private def boundedClockNext {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (x : BoundedClockState m B) (e : Fin (2*m)) : BoundedClockState m B :=
  ⟨clockNext (B := B) (M := M) hm x.val e,
    clockBanksBounded_activate hm hB x.val.1 x.property
      (physicalSite e) (physicalBit e)⟩

/-- Restricting the state space does not change a scheduler letter or its
native update. -/
private def boundedClockChain {m B M : Nat} (hm : 0 < m) (hB : 0 < B) :
    Recover.Chain.ClockChain (BoundedClockState m B) (2*m) m B M hm where
  next := boundedClockNext hm hB
  cfg := fun x => x.val.1.cfg
  act := fun x => clockAct x.val
  lastAct := fun x => x.val.2
  cfg_next := fun x e =>
    (clockChain (B := B) (M := M) hm).cfg_next x.val e
  last_next := fun x e =>
    (clockChain (B := B) (M := M) hm).last_next x.val e

private theorem bounded_clock_run {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (x : BoundedClockState m B) (u : List (Fin (2*m))) :
    (runWord (boundedClockNext (M := M) hm hB) x u).val =
      runWord (clockNext (B := B) (M := M) hm) x.val u := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (boundedClockNext hm hB x e)

private theorem head_clock_physical {m B M : Nat} (hm : 0 < m)
    (x : OverrunState m) (u : List (Fin (2*m))) :
    (runWord (clockNext (B := B) (M := M) hm) x u).1 =
      physicalRun B M hm x.1 u := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (clockNext (B := B) (M := M) hm x e)

/-- Each truncated hitting cost is unchanged by remembering the invariant. -/
private theorem bounded_clock_cost {m B M : Nat} (hm : 0 < m) (hB : 0 < B)
    (R : OverrunState m → Prop) (t : Nat) (x : BoundedClockState m B) :
    iidHitCost (boundedClockNext (M := M) hm hB) (fun y => R y.val) t x =
      iidHitCost (clockNext (B := B) (M := M) hm) R t x.val := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    simp only [iidHitCost]
    by_cases hx : R x.val
    · simp only [if_pos hx]
    · simp only [if_neg hx]
      congr 1
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext e
      exact ih (boundedClockNext hm hB x e)

/-- Starting from bounded native banks, the concrete paired clock reaches
its permanent virtual single-anchor set within the quadratic post-custody
budget. All slice counts and service moments are supplied by the clock. -/
theorem clock_layer_headline {m B M bL ringN r L : Nat}
    (hm : 0 < m) (hmb : m < B) (hM : ClockParams M)
    (hp : 32 ∣ M/2) (hmP : m < M/2)
    (hr : 0 < r) (hs : L = 2^(5*bL+34)*ringN*r) (hw : m*r ≤ ringN)
    (x : OverrunState m)
    (hx : Recover.StageTwo.WellFormed M x.1.cfg)
    (hb : ClockBanksBounded B x.1.cfg) :
    IIDExpectedHittingTimeAtMost (clockNext (B := B) (M := M) hm)
      (virtualClockR B M hm) x (2^(5*bL+66)*ringN^2) := by
  have hB : 0 < B := Nat.lt_trans hm hmb
  let C := boundedClockChain (M := M) hm hB
  let R := fun y : BoundedClockState m B => virtualClockR B M hm y.val
  let d := 2^30*L*m
  let n := 2*m
  let Event := List (Fin (2*m)) → Prop
  let mass := fun f : Event => wordSum (fun u => if f u then 1 else 0) d
  have hL := clock_service_scale hr hw hs
  have hclosed : ∀ y e, R y → R (C.next y e) := by
    intro y e hy
    exact virtualClockR_closed hm y.val e hy
  have hsel (y : BoundedClockState m B) : ∃ fs : Event × Event,
      (Recover.Chain.LgSet C y → ¬ R y →
        4*mass fs.1 ≤ n^d ∧ 4*mass fs.2 ≤ n^d) ∧
      (Recover.Chain.LgSet C y → ∀ u : List (Fin (2*m)), u.length = d →
        ¬ fs.1 u → ¬ fs.2 u → R (runWord C.next y u)) := by
    by_cases hleg : Recover.Chain.LgSet C y
    · by_cases hdone : R y
      · refine ⟨(fun _ => False, fun _ => False), fun _ hn => (hn hdone).elim, ?_⟩
        intro _ u _ _ _
        exact runWord_of_closed C.next R hclosed y u hdone
      · obtain ⟨lift, _, base, _, _, hc, hz, hbelowWarm, _, hover⟩ :=
          clock_lgSet_aligned_overrun (B := B) hm hM hmP hL y.val hleg
        let s : WordState m := ⟨y.val.1.cfg, lift⟩
        let target := base + 32*(2^19*m)
        let z : OverrunState m := (s, y.val.2)
        have hbelow (i : Fin m) : s.lift i < base := by
          have hi := hbelowWarm i
          change lift i < base
          omega
        have hlog := clock_uncertified_quarter hm hmb hM hp hz s hc hbelow
          y.property d
        let miss : Event := fun u => ∃ i, (physicalRun B M hm s u).lift i < target
        refine ⟨(uncertifiedSlice B M target hm s, miss), ?_, ?_⟩
        · intro _ _
          refine ⟨hlog, ?_⟩
          dsimp only [mass, Prod.snd]
          rw [repair_wordSum_eq_thru]
          simp only [clock_run_physical] at hover
          have hevent : (fun u => @ite Nat (miss u) (Classical.propDecidable _) 1 0) =
              (fun u => if ∃ i, (physicalRun B M hm s u).lift i < target then 1 else 0) := by
            funext u
            by_cases h : ∃ i, (physicalRun B M hm s u).lift i < target <;>
              simp [miss, h]
          rw [hevent]
          exact hover
        · intro _ u _ hgood hhit
          have hreach (i : Fin m) : target ≤ (physicalRun B M hm s u).lift i :=
            Nat.le_of_not_lt (fun hi => hhit ⟨i,hi⟩)
          have hcert : Bounded B (observedSnapshot B M hm s u target) ∧
              anchorCount hm (observedSnapshot B M hm s u target) = 1 :=
            Classical.byContradiction fun hn => hgood ⟨hreach, hn⟩
          have habove (i : Fin m) : s.lift i < target :=
            Nat.lt_of_lt_of_le (hbelow i) (Nat.le_add_right _ _)
          have hphase : target%32 = 0 := by simp [target, Nat.add_mod, hz]
          have hnative := virtualNativeR_cover_reached hm s hc habove hphase u
            hreach hcert.1 hcert.2
          change virtualNativeR B M hm (runWord (boundedClockNext hm hB) y u).val.1.cfg
          rw [bounded_clock_run, clock_run_records hm y.val z u rfl,
            head_clock_physical]
          exact hnative
    · exact ⟨(fun _ => False, fun _ => False), fun hh => (hleg hh).elim,
        fun hh => (hleg hh).elim⟩
  have hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y := by
    apply served_moment C (by omega) (k := 2)
    · intro y i
      have he := clock_service_count (B := B) (M := M) hm y.val i
      change 2 ≤ countFin (fun e : Fin (2*m) =>
        decide (((clockChain (B := B) (M := M) hm).act y.val e).map Prod.fst = some i))
      rw [he]
      exact Nat.le_refl _
    · exact service_length_ratio hm hL
  have hbound := post_custody_chain_capfree C R L bL ringN r
    (fun y => (hsel y).choose.1) (fun y => (hsel y).choose.2)
    ⟨by have := hM.1; omega, hM.2⟩ (by omega) (by omega) hm
    hMom hs hw hclosed
    (fun y hy hn => ((hsel y).choose_spec.1 hy hn).1)
    (fun y hy hn => ((hsel y).choose_spec.1 hy hn).2)
    (fun y => (hsel y).choose_spec.2) ⟨x,hb⟩ hx
  intro t
  have ht := hbound t
  change iidHitCost (boundedClockNext (M := M) hm hB)
    (fun y => virtualClockR B M hm y.val) t ⟨x,hb⟩ ≤ _ at ht
  rw [bounded_clock_cost] at ht
  exact ht

end
end L4.Height.ClockHead
namespace L4.Height.ClockHead

/-- The same budget for the uniform first-hit expectation, including almost-sure hitting. -/
theorem clock_layer_expected {m B M bL ringN r L : Nat}
    (hm : 0 < m) (hmb : m < B) (hM : ClockParams M)
    (hp : 32 ∣ M/2) (hmP : m < M/2)
    (hr : 0 < r) (hs : L = 2^(5*bL+34)*ringN*r) (hw : m*r ≤ ringN)
    (x : OverrunState m)
    (hx : Recover.StageTwo.WellFormed M x.1.cfg)
    (hb : ClockBanksBounded B x.1.cfg) :
    UniformFirstHit.ExpectedHittingTimeAtMost (clockNext (B := B) (M := M) hm)
      (virtualClockR B M hm) x ((2^(5*bL+66)*ringN^2 : Nat) : Rat) :=
  (iid_expected_iff_leader _ _ (by omega) _ _).1
    (clock_layer_headline hm hmb hM hp hmP hr hs hw x hx hb)

end L4.Height.ClockHead

