import Leader.L4.Height.SyncRound
import Leader.L4.Height.Couple

namespace L4.Height

open Classical
open L4.Compiler.Native


set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

/-! ## The paired physical alphabet -/

def physicalSite {m : Nat} (e : Fin (2 * m)) : Fin m :=
  ⟨e.val / 2, by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2
    simpa [Nat.mul_comm] using e.isLt⟩

def physicalBit {m : Nat} (e : Fin (2 * m)) : Bool :=
  decide (e.val % 2 = 1)

def physicalFlip {m : Nat} (e : Fin (2 * m)) : Fin (2 * m) :=
  ⟨2 * (e.val / 2) + (1 - e.val % 2), by
    have hq : e.val / 2 < m := (physicalSite e).isLt
    have hr : e.val % 2 < 2 := Nat.mod_lt _ (by omega)
    omega⟩

@[simp] theorem physicalSite_flip {m : Nat} (e : Fin (2 * m)) :
    physicalSite (physicalFlip e) = physicalSite e := by
  apply Fin.ext
  change
    (2 * (e.val / 2) + (1 - e.val % 2)) / 2 = e.val / 2
  have hr : e.val % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

private theorem physicalFlip_mod_two {m : Nat} (e : Fin (2 * m)) :
    (physicalFlip e).val % 2 = 1 - e.val % 2 := by
  change
    (2 * (e.val / 2) + (1 - e.val % 2)) % 2 = 1 - e.val % 2
  have hr : e.val % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

@[simp] theorem physicalBit_flip {m : Nat} (e : Fin (2 * m)) :
    physicalBit (physicalFlip e) = !physicalBit e := by
  unfold physicalBit
  rw [physicalFlip_mod_two]
  have hr : e.val % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hz : e.val % 2 = 0
  · simp [hz]
  · have ho : e.val % 2 = 1 := by omega
    simp [ho]

@[simp] theorem physicalFlip_invol {m : Nat} (e : Fin (2 * m)) :
    physicalFlip (physicalFlip e) = e := by
  apply Fin.ext
  change
    2 * ((physicalFlip e).val / 2) +
        (1 - (physicalFlip e).val % 2) = e.val
  have hd := congrArg Fin.val (physicalSite_flip e)
  change (physicalFlip e).val / 2 = e.val / 2 at hd
  have hm := physicalFlip_mod_two e
  have hr : e.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp := Nat.mod_add_div e.val 2
  omega

def physicalActivation {m : Nat} (e : Fin (2 * m)) : Activation m :=
  (physicalSite e, physicalBit e)

def physicalNext {m : Nat} (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) : WordState m :=
  activate B M hm s (physicalSite e) (physicalBit e)

/-! ## Logical indices and the reveal classifier -/

def phaseIndex {Q m : Nat} (r : Fin Q) (i : Fin m) : Fin (Q * m) :=
  ⟨r.val * m + i.val, by
    calc
      r.val * m + i.val < r.val * m + m :=
        Nat.add_lt_add_left i.isLt _
      _ = (r.val + 1) * m := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ Q * m :=
        Nat.mul_le_mul_right m (by omega)⟩

private theorem phaseIndex_injective {Q m : Nat} (hm : 0 < m) :
    Function.Injective
      (fun p : Fin Q × Fin m => phaseIndex p.1 p.2) := by
  intro p q h
  rcases p with ⟨r, i⟩
  rcases q with ⟨r', i'⟩
  have hv := congrArg Fin.val h
  change r.val * m + i.val = r'.val * m + i'.val at hv
  have hru : r.val * m + i.val < (r.val + 1) * m := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left i.isLt _
  have hqu : r'.val * m + i'.val < (r'.val + 1) * m := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left i'.isLt _
  have hr : r.val = r'.val := by
    by_cases hlt : r.val < r'.val
    · have hs : r.val + 1 ≤ r'.val := by omega
      have hb := Nat.mul_le_mul_right m hs
      have hl : r'.val * m ≤ r'.val * m + i'.val := by omega
      omega
    · by_cases hgt : r'.val < r.val
      · have hs : r'.val + 1 ≤ r.val := by omega
        have hb := Nat.mul_le_mul_right m hs
        have hl : r.val * m ≤ r.val * m + i.val := by omega
        omega
      · omega
  have hi : i.val = i'.val := by
    rw [hr] at hv
    omega
  apply Prod.ext
  · apply Fin.ext
    exact hr
  · apply Fin.ext
    exact hi

noncomputable def phaseRound? (ellzero Q ell : Nat) : Option (Fin Q) :=
  if h : ∃ r : Fin Q, ell = ellzero + 32 * r.val + 1 then
    some (Classical.choose h)
  else none

private theorem phaseRound_some_iff
    (ellzero Q ell : Nat) (r : Fin Q) :
    phaseRound? ellzero Q ell = some r ↔
      ell = ellzero + 32 * r.val + 1 := by
  unfold phaseRound?
  by_cases h : ∃ q : Fin Q, ell = ellzero + 32 * q.val + 1
  · rw [dif_pos h]
    constructor
    · intro he
      have hc : Classical.choose h = r := Option.some.inj he
      rw [← hc]
      exact Classical.choose_spec h
    · intro hr
      have hc : Classical.choose h = r := by
        apply Fin.ext
        have hs := Classical.choose_spec h
        omega
      rw [hc]
  · rw [dif_neg h]
    constructor
    · intro he
      cases he
    · intro hr
      exact False.elim (h ⟨r, hr⟩)

private theorem phaseRound_none_iff
    (ellzero Q ell : Nat) :
    phaseRound? ellzero Q ell = none ↔
      ¬ ∃ r : Fin Q, ell = ellzero + 32 * r.val + 1 := by
  unfold phaseRound?
  by_cases h : ∃ r : Fin Q, ell = ellzero + 32 * r.val + 1
  · simp [h]
  · simp [h]

noncomputable def phaseRevealIndex? {m : Nat}
    (M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (i : Fin m) : Option (Fin (Q * m)) :=
  match clockAction M hm s i with
  | .inc _ =>
      if clockOf M (s.lift i) % 32 = 1 then
        (phaseRound? ellzero Q (s.lift i)).map
          (fun r => phaseIndex r i)
      else none
  | _ => none

private theorem phaseRevealIndex_some_iff {m : Nat}
    (M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (i : Fin m) (k : Fin (Q * m)) :
    phaseRevealIndex? M ellzero Q hm s i = some k ↔
      ∃ r : Fin Q,
        k = phaseIndex r i ∧
        (∃ tick, clockAction M hm s i = ClockAction.inc tick) ∧
        clockOf M (s.lift i) % 32 = 1 ∧
        s.lift i = ellzero + 32 * r.val + 1 := by
  cases hact : clockAction M hm s i with
  | reset =>
      simp [phaseRevealIndex?, hact]
  | propagate tick =>
      simp [phaseRevealIndex?, hact]
  | clear =>
      simp [phaseRevealIndex?, hact]
  | hold =>
      simp [phaseRevealIndex?, hact]
  | inc tick =>
      by_cases hp : clockOf M (s.lift i) % 32 = 1
      · simp only [phaseRevealIndex?, hact, if_pos hp]
        cases hrnd : phaseRound? ellzero Q (s.lift i) with
        | none =>
            have hno :=
              (phaseRound_none_iff ellzero Q (s.lift i)).1 hrnd
            constructor
            · simp
            · rintro ⟨r, hk, hinc, hphase, hlift⟩
              exact False.elim (hno ⟨r, hlift⟩)
        | some r =>
            constructor
            · intro h
              change some (phaseIndex r i) = some k at h
              have hk : phaseIndex r i = k := Option.some.inj h
              exact ⟨r, hk.symm, ⟨tick, rfl⟩, hp,
                (phaseRound_some_iff ellzero Q (s.lift i) r).1 hrnd⟩
            · rintro ⟨r', hk, hinc, hphase, hlift⟩
              have hrnd' :=
                (phaseRound_some_iff ellzero Q (s.lift i) r').2 hlift
              have hrr : r = r' :=
                Option.some.inj (hrnd.symm.trans hrnd')
              subst r'
              change some (phaseIndex r i) = some k
              exact congrArg some hk.symm
      · simp [phaseRevealIndex?, hact, hp]

noncomputable def physicalBitOf {m : Nat}
    (M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) :
    Option (Fin (Q * m) × Bool) :=
  match phaseRevealIndex? M ellzero Q hm s (physicalSite e) with
  | none => none
  | some k => some (k, physicalBit e)

private theorem physicalBitOf_some_iff {m : Nat}
    (M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m))
    (k : Fin (Q * m)) (v : Bool) :
    physicalBitOf M ellzero Q hm s e = some (k, v) ↔
      ∃ r : Fin Q,
        k = phaseIndex r (physicalSite e) ∧
        physicalBit e = v ∧
        (∃ tick,
          clockAction M hm s (physicalSite e) = ClockAction.inc tick) ∧
        clockOf M (s.lift (physicalSite e)) % 32 = 1 ∧
        s.lift (physicalSite e) = ellzero + 32 * r.val + 1 := by
  unfold physicalBitOf
  cases hidx : phaseRevealIndex? M ellzero Q hm s (physicalSite e) with
  | none =>
      constructor
      · intro h
        cases h
      · rintro ⟨r, hk, hv, hinc, hphase, hlift⟩
        have hs :
            phaseRevealIndex? M ellzero Q hm s (physicalSite e) =
              some (phaseIndex r (physicalSite e)) :=
          (phaseRevealIndex_some_iff M ellzero Q hm s
            (physicalSite e) (phaseIndex r (physicalSite e))).2
            ⟨r, rfl, hinc, hphase, hlift⟩
        rw [hidx] at hs
        cases hs
  | some j =>
      constructor
      · intro h
        change some (j, physicalBit e) = some (k, v) at h
        have hp := Option.some.inj h
        have hjk : j = k := congrArg Prod.fst hp
        have hv : physicalBit e = v := congrArg Prod.snd hp
        have hs :=
          (phaseRevealIndex_some_iff M ellzero Q hm s
            (physicalSite e) j).1 hidx
        rcases hs with ⟨r, hjr, hinc, hphase, hlift⟩
        exact ⟨r, hjk.symm.trans hjr, hv, hinc, hphase, hlift⟩
      · rintro ⟨r, hk, hv, hinc, hphase, hlift⟩
        have hs :
            phaseRevealIndex? M ellzero Q hm s (physicalSite e) =
              some (phaseIndex r (physicalSite e)) :=
          (phaseRevealIndex_some_iff M ellzero Q hm s
            (physicalSite e) (phaseIndex r (physicalSite e))).2
            ⟨r, rfl, hinc, hphase, hlift⟩
        have hj : j = phaseIndex r (physicalSite e) :=
          Option.some.inj (hidx.symm.trans hs)
        have hjk : j = k := hj.trans hk.symm
        apply congrArg some
        apply Prod.ext
        · exact hjk
        · exact hv

private theorem physicalBitOf_eq_some_iff {m : Nat}
    (M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m))
    (r : Fin Q) (i : Fin m) (v : Bool) :
    physicalBitOf M ellzero Q hm s e =
        some (phaseIndex r i, v) ↔
      physicalSite e = i ∧
      physicalBit e = v ∧
      (∃ tick, clockAction M hm s i = ClockAction.inc tick) ∧
      clockOf M (s.lift i) % 32 = 1 ∧
      s.lift i = ellzero + 32 * r.val + 1 := by
  constructor
  · intro h
    have hs :=
      (physicalBitOf_some_iff M ellzero Q hm s e
        (phaseIndex r i) v).1 h
    rcases hs with ⟨r', hk, hv, hinc, hphase, hlift⟩
    have hp : (r, i) = (r', physicalSite e) :=
      phaseIndex_injective hm hk
    have hr : r = r' := congrArg Prod.fst hp
    have hi : i = physicalSite e := congrArg Prod.snd hp
    subst r'
    refine ⟨hi.symm, hv, ?_, ?_, ?_⟩
    · simpa [hi] using hinc
    · simpa [hi] using hphase
    · simpa [hi] using hlift
  · rintro ⟨hsite, hv, hinc, hphase, hlift⟩
    apply (physicalBitOf_some_iff M ellzero Q hm s e
      (phaseIndex r i) v).2
    refine ⟨r, ?_, hv, ?_, ?_, ?_⟩
    · rw [hsite]
    · simpa [hsite] using hinc
    · simpa [hsite] using hphase
    · simpa [hsite] using hlift

/-! ## The paired source -/

noncomputable def physSource {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m) :
    Couple.PairedSource (WordState m) (Fin (Q * m)) (2 * m) :=
  { next := physicalNext B M hm
    bitOf := physicalBitOf M ellzero Q hm
    flip := fun _ e => physicalFlip e
    half := m
    alphabet_even := rfl
    flip_invol := by
      intro s e
      exact physicalFlip_invol e
    flip_reveal := by
      intro s e k v h
      change physicalBitOf M ellzero Q hm s e = some (k, v) at h
      change physicalBitOf M ellzero Q hm s (physicalFlip e) =
        some (k, !v)
      unfold physicalBitOf at h ⊢
      rw [physicalSite_flip, physicalBit_flip]
      cases hx : phaseRevealIndex? M ellzero Q hm s (physicalSite e) with
      | none =>
          have hh :
              (none : Option (Fin (Q * m) × Bool)) = some (k, v) := by
            simpa only [hx] using h
          cases hh
      | some j =>
          have hh : some (j, physicalBit e) = some (k, v) := by
            simpa only [hx] using h
          have hp : (j, physicalBit e) = (k, v) := Option.some.inj hh
          cases hp
          simpa only [hx] }

@[simp] theorem physSource_next {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) :
    (physSource B M ellzero Q hm).next s e =
      physicalNext B M hm s e := rfl

@[simp] theorem physSource_bitOf {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) :
    (physSource B M ellzero Q hm).bitOf s e =
      physicalBitOf M ellzero Q hm s e := rfl

@[simp] theorem physSource_flip {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) :
    (physSource B M ellzero Q hm).flip s e = physicalFlip e := rfl

/-! ## Physical words and monotone lifts -/

def physicalRun {m : Nat} (B M : Nat) (hm : 0 < m) :
    WordState m → List (Fin (2 * m)) → WordState m
  | s, [] => s
  | s, e :: u => physicalRun B M hm (physicalNext B M hm s e) u

private theorem physicalRun_append {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u v : List (Fin (2 * m))) :
    physicalRun B M hm s (u ++ v) =
      physicalRun B M hm (physicalRun B M hm s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      exact ih (physicalNext B M hm s e)

private theorem physicalRun_eq_syncRun {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m))) :
    physicalRun B M hm s u =
      syncRun B M hm (u.map physicalActivation) s := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      change
        physicalRun B M hm (physicalNext B M hm s e) u =
          syncRun B M hm (u.map physicalActivation)
            (activate B M hm s (physicalSite e) (physicalBit e))
      simpa [physicalNext] using
        ih (physicalNext B M hm s e)

private theorem physicalNext_lift_step {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) (i : Fin m) :
    (physicalNext B M hm s e).lift i = s.lift i ∨
      (physicalNext B M hm s e).lift i = s.lift i + 1 := by
  by_cases hi : i = physicalSite e
  · subst i
    cases hact : clockAction M hm s (physicalSite e) <;>
      simp [physicalNext, activate, hact, advanceLift]
  · left
    simp [physicalNext, activate, hi]

private theorem physicalNext_lift_mono {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) (i : Fin m) :
    s.lift i ≤ (physicalNext B M hm s e).lift i := by
  rcases physicalNext_lift_step B M hm s e i with h | h
  · rw [h]
    exact Nat.le_refl _
  · rw [h]
    omega

private theorem physicalNext_lift_succ_data {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m)) (i : Fin m)
    (hsucc : (physicalNext B M hm s e).lift i = s.lift i + 1) :
    physicalSite e = i ∧
      ∃ tick, clockAction M hm s i = ClockAction.inc tick := by
  by_cases hi : i = physicalSite e
  · subst i
    refine ⟨rfl, ?_⟩
    cases hact : clockAction M hm s (physicalSite e) with
    | reset =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
    | propagate tick =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
    | clear =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
    | inc tick => exact ⟨tick, rfl⟩
    | hold =>
        simp [physicalNext, activate, hact, advanceLift] at hsucc
  · have heq : (physicalNext B M hm s e).lift i = s.lift i := by
      simp [physicalNext, activate, hi]
    omega

private theorem physicalRun_lift_mono {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m))) (i : Fin m) :
    s.lift i ≤ (physicalRun B M hm s u).lift i := by
  induction u generalizing s with
  | nil => exact Nat.le_refl _
  | cons e u ih =>
      exact Nat.le_trans
        (physicalNext_lift_mono B M hm s e i)
        (ih (physicalNext B M hm s e))

/-! ## A reveal occurs only once -/

private theorem no_reveal_above {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (r : Fin Q) (i : Fin m)
    (hgt : ellzero + 32 * r.val + 1 < s.lift i) :
    ∀ u : List (Fin (2 * m)),
      Couple.firstReveal (physSource B M ellzero Q hm)
        (phaseIndex r i) s u = none := by
  intro u
  induction u generalizing s with
  | nil => rfl
  | cons e u ih =>
      rw [Couple.firstReveal]
      cases hb : (physSource B M ellzero Q hm).bitOf s e with
      | none =>
          simp only
          apply ih ((physSource B M ellzero Q hm).next s e)
          have hmono := physicalNext_lift_mono B M hm s e i
          simpa only [physSource_next] using
            (Nat.lt_of_lt_of_le hgt hmono)
      | some p =>
          rcases p with ⟨k, b⟩
          simp only
          by_cases hk : k = phaseIndex r i
          · subst k
            rw [if_pos rfl]
            have hb' :
                physicalBitOf M ellzero Q hm s e =
                  some (phaseIndex r i, b) := by
              simpa only [physSource_bitOf] using hb
            have hs :=
              (physicalBitOf_eq_some_iff M ellzero Q hm s e r i b).1 hb'
            rcases hs with ⟨hsite, hbit, hinc, hphase, hlift⟩
            omega
          · rw [if_neg hk]
            apply ih ((physSource B M ellzero Q hm).next s e)
            have hmono := physicalNext_lift_mono B M hm s e i
            simpa only [physSource_next] using
              (Nat.lt_of_lt_of_le hgt hmono)

theorem reveal_once {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (e : Fin (2 * m))
    (r : Fin Q) (i : Fin m) (v : Bool)
    (h : (physSource B M ellzero Q hm).bitOf s e =
      some (phaseIndex r i, v)) :
    ∀ u : List (Fin (2 * m)),
      Couple.firstReveal (physSource B M ellzero Q hm)
        (phaseIndex r i)
        ((physSource B M ellzero Q hm).next s e) u = none := by
  have hb : physicalBitOf M ellzero Q hm s e =
      some (phaseIndex r i, v) := by
    simpa only [physSource_bitOf] using h
  have hs :=
    (physicalBitOf_eq_some_iff M ellzero Q hm s e r i v).1 hb
  rcases hs with ⟨hsite, hbit, ⟨tick, hact⟩, hphase, hlift⟩
  have hnext :
      ((physSource B M ellzero Q hm).next s e).lift i =
        s.lift i + 1 := by
    rw [physSource_next]
    change
      (activate B M hm s (physicalSite e) (physicalBit e)).lift i =
        s.lift i + 1
    rw [hsite]
    simp [activate, hact, advanceLift]
  apply no_reveal_above B M ellzero Q hm
  rw [hnext, hlift]
  omega

private theorem firstReveal_eq_of_reveal {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s : WordState m) (pre : List (Fin (2 * m)))
    (e : Fin (2 * m)) (post : List (Fin (2 * m)))
    (r : Fin Q) (i : Fin m) (v : Bool)
    (h : (physSource B M ellzero Q hm).bitOf
      (physicalRun B M hm s pre) e = some (phaseIndex r i, v)) :
    Couple.firstReveal (physSource B M ellzero Q hm)
      (phaseIndex r i) s (pre ++ e :: post) = some v := by
  induction pre generalizing s with
  | nil =>
      have h0 : (physSource B M ellzero Q hm).bitOf s e =
          some (phaseIndex r i, v) := by
        simpa [physicalRun] using h
      rw [List.nil_append, Couple.firstReveal]
      simp only [h0, if_pos]
  | cons a pre ih =>
      have htail := ih (s := physicalNext B M hm s a) (by
        simpa [physicalRun] using h)
      rw [List.cons_append, Couple.firstReveal]
      cases hb : (physSource B M ellzero Q hm).bitOf s a with
      | none =>
          simp only
          simpa only [physSource_next] using htail
      | some p =>
          rcases p with ⟨k, b⟩
          simp only
          by_cases hk : k = phaseIndex r i
          · subst k
            have hnone := reveal_once B M ellzero Q hm s a r i b hb
              (pre ++ e :: post)
            have htail' :
                Couple.firstReveal (physSource B M ellzero Q hm)
                  (phaseIndex r i)
                  ((physSource B M ellzero Q hm).next s a)
                  (pre ++ e :: post) = some v := by
              simpa only [physSource_next] using htail
            rw [hnone] at htail'
            cases htail'
          · rw [if_neg hk]
            simpa only [physSource_next] using htail

/-! ## The read vector honors every indexed phase-one increment -/

private theorem phase_one_has_round
    (M ellzero Q ell : Nat)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (hlower : ellzero ≤ ell)
    (hupper : ell ≤ ellzero + 32 * Q)
    (hphase : clockOf M ell % 32 = 1) :
    ∃ r : Fin Q, ell = ellzero + 32 * r.val + 1 := by
  let n := ell - ellzero
  have hell : ell = ellzero + n := by
    dsimp [n]
    omega
  have hp := clockOf_mod_phase (M := M) (ellzero := ellzero)
    (n := n) hdiv hzero
  have hp' : clockOf M (ellzero + n) % 32 = 1 := by
    rw [← hell]
    exact hphase
  have hnmod : n % 32 = 1 := by
    calc
      n % 32 = clockOf M (ellzero + n) % 32 := hp.symm
      _ = 1 := hp'
  let q := n / 32
  have hdecomp := Nat.mod_add_div n 32
  have hnform : n = 32 * q + 1 := by
    dsimp [q]
    omega
  have hnle : n ≤ 32 * Q := by
    dsimp [n]
    omega
  have hq : q < Q := by
    by_cases h : q < Q
    · exact h
    · have hge : Q ≤ q := Nat.le_of_not_gt h
      have hmul := Nat.mul_le_mul_left 32 hge
      omega
  refine ⟨⟨q, hq⟩, ?_⟩
  change ell = ellzero + 32 * q + 1
  rw [hell, hnform]
  omega

noncomputable def physicalChoices {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m))) :
    Nat → Fin m → Bool :=
  fun ell i =>
    match phaseRound? ellzero Q ell with
    | none => false
    | some r =>
        Couple.readVector (physSource B M ellzero Q hm) s0 u
          (phaseIndex r i)

@[simp] theorem physicalChoices_target {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (s0 : WordState m) (u : List (Fin (2 * m)))
    (r : Fin Q) (i : Fin m) :
    physicalChoices B M ellzero Q hm s0 u
        (ellzero + 32 * r.val + 1) i =
      Couple.readVector (physSource B M ellzero Q hm) s0 u
        (phaseIndex r i) := by
  unfold physicalChoices
  rw [(phaseRound_some_iff ellzero Q
    (ellzero + 32 * r.val + 1) r).2 rfl]

private theorem startConsistent_lift_lower {m : Nat}
    (B M ellzero : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s : WordState m)
    (hstart : StartConsistent B M ellzero hm choices start s) :
    ∀ i, ellzero ≤ s.lift i := by
  intro i
  rcases hstart i with h | h
  · rw [h.1]
    exact Nat.le_refl _
  · rw [h.1]
    omega

private theorem honors_readVector_aux {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (s0 : WordState m) (whole : List (Fin (2 * m)))
    (hlower : ∀ i, ellzero ≤ s0.lift i)
    (hcap : ∀ i,
      (physicalRun B M hm s0 whole).lift i ≤ ellzero + 32 * Q) :
    ∀ (pre rest : List (Fin (2 * m))),
      whole = pre ++ rest →
      Honors B M hm
        (physicalChoices B M ellzero Q hm s0 whole)
        (physicalRun B M hm s0 pre)
        (rest.map physicalActivation) := by
  intro pre rest hsplit
  induction rest generalizing pre with
  | nil =>
      simp [Honors]
  | cons e rest ih =>
      let cur := physicalRun B M hm s0 pre
      have hcurLower : ∀ i, ellzero ≤ cur.lift i := by
        intro i
        exact Nat.le_trans (hlower i)
          (physicalRun_lift_mono B M hm s0 pre i)
      have hfinEq :
          physicalRun B M hm s0 whole =
            physicalRun B M hm cur (e :: rest) := by
        rw [hsplit, physicalRun_append]
      have hcurUpper : ∀ i, cur.lift i ≤ ellzero + 32 * Q := by
        intro i
        have hmono := physicalRun_lift_mono B M hm cur (e :: rest) i
        have hf :
            (physicalRun B M hm cur (e :: rest)).lift i ≤
              ellzero + 32 * Q := by
          rw [← hfinEq]
          exact hcap i
        exact Nat.le_trans hmono hf
      change
        (match clockAction M hm cur (physicalSite e) with
         | .inc _ =>
             clockOf M (cur.lift (physicalSite e)) % 32 ≠ 1 ∨
               physicalBit e =
                 physicalChoices B M ellzero Q hm s0 whole
                   (cur.lift (physicalSite e)) (physicalSite e)
         | _ => True) ∧
        Honors B M hm
          (physicalChoices B M ellzero Q hm s0 whole)
          (activate B M hm cur (physicalSite e) (physicalBit e))
          (rest.map physicalActivation)
      constructor
      · cases hact : clockAction M hm cur (physicalSite e) with
        | reset => trivial
        | propagate tick => trivial
        | clear => trivial
        | hold => trivial
        | inc tick =>
            by_cases hp :
                clockOf M (cur.lift (physicalSite e)) % 32 = 1
            · right
              obtain ⟨r, hlift⟩ := phase_one_has_round M ellzero Q
                (cur.lift (physicalSite e)) hdiv hzero
                (hcurLower (physicalSite e))
                (hcurUpper (physicalSite e)) hp
              have hb0 :
                  physicalBitOf M ellzero Q hm cur e =
                    some (phaseIndex r (physicalSite e), physicalBit e) :=
                (physicalBitOf_eq_some_iff M ellzero Q hm cur e r
                  (physicalSite e) (physicalBit e)).2
                  ⟨rfl, rfl, ⟨tick, hact⟩, hp, hlift⟩
              have hb :
                  (physSource B M ellzero Q hm).bitOf cur e =
                    some (phaseIndex r (physicalSite e), physicalBit e) := by
                simpa only [physSource_bitOf] using hb0
              have hfirst0 := firstReveal_eq_of_reveal
                B M ellzero Q hm s0 pre e rest r
                (physicalSite e) (physicalBit e) hb
              have hfirst :
                  Couple.firstReveal (physSource B M ellzero Q hm)
                    (phaseIndex r (physicalSite e)) s0 whole =
                      some (physicalBit e) := by
                rw [hsplit]
                exact hfirst0
              have hread :
                  Couple.readVector (physSource B M ellzero Q hm) s0 whole
                    (phaseIndex r (physicalSite e)) = physicalBit e := by
                unfold Couple.readVector
                rw [hfirst]
                rfl
              rw [hlift, physicalChoices_target]
              exact hread.symm
            · left
              exact hp
      · have hsplitTail :
            whole = (pre ++ [e]) ++ rest := by
          rw [hsplit]
          simp [List.append_assoc]
        have htail := ih (pre ++ [e]) hsplitTail
        have hstate :
            physicalRun B M hm s0 (pre ++ [e]) =
              activate B M hm cur (physicalSite e) (physicalBit e) := by
          rw [physicalRun_append]
          simp [physicalRun, physicalNext, cur]
        rw [← hstate]
        exact htail

theorem honors_readVector {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (_hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (u : List (Fin (2 * m)))
    (_hleg : Legit M hm s0)
    (hstart : StartConsistent B M ellzero hm
      (physicalChoices B M ellzero Q hm s0 u) start s0)
    (hcap : ∀ i,
      (physicalRun B M hm s0 u).lift i ≤ ellzero + 32 * Q) :
    Honors B M hm
      (physicalChoices B M ellzero Q hm s0 u) s0
      (u.map physicalActivation) := by
  have hlower := startConsistent_lift_lower B M ellzero hm
    (physicalChoices B M ellzero Q hm s0 u) start s0 hstart
  exact honors_readVector_aux B M ellzero Q hm hdiv hzero s0 u
    hlower hcap [] u (by simp)

/-! ## Coverage and the final synchronous snapshot -/

private theorem exists_increment_split {m : Nat}
    (B M : Nat) (hm : 0 < m)
    (s : WordState m) (u : List (Fin (2 * m)))
    (i : Fin m) (ell : Nat)
    (hstart : s.lift i ≤ ell)
    (hend : ell < (physicalRun B M hm s u).lift i) :
    ∃ pre e post tick,
      u = pre ++ e :: post ∧
      physicalSite e = i ∧
      (physicalRun B M hm s pre).lift i = ell ∧
      clockAction M hm (physicalRun B M hm s pre) i =
        ClockAction.inc tick := by
  induction u generalizing s with
  | nil =>
      change ell < s.lift i at hend
      omega
  | cons e u ih =>
      let s' := physicalNext B M hm s e
      have hstep : s'.lift i = s.lift i ∨
          s'.lift i = s.lift i + 1 := by
        simpa [s'] using physicalNext_lift_step B M hm s e i
      by_cases hcross : ell < s'.lift i
      · have hold : s.lift i = ell := by
          rcases hstep with h | h <;> omega
        have hsucc : s'.lift i = s.lift i + 1 := by
          rcases hstep with h | h
          · omega
          · exact h
        have hdata := physicalNext_lift_succ_data B M hm s e i
          (by simpa [s'] using hsucc)
        rcases hdata with ⟨hsite, ⟨tick, hact⟩⟩
        refine ⟨[], e, u, tick, rfl, hsite, ?_, ?_⟩
        · simpa [physicalRun] using hold
        · simpa [physicalRun] using hact
      · have hsle : s'.lift i ≤ ell := Nat.le_of_not_gt hcross
        have hend' : ell < (physicalRun B M hm s' u).lift i := by
          simpa [physicalRun, s'] using hend
        obtain ⟨pre, a, post, tick, hu, hsite, hlift, hact⟩ :=
          ih s' hsle hend'
        refine ⟨e :: pre, a, post, tick, ?_, hsite, ?_, hact⟩
        · simp only [List.cons_append]
          rw [hu]
        · simpa [physicalRun, s'] using hlift

private theorem firstReveal_covered {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (s : WordState m) (u : List (Fin (2 * m)))
    (r : Fin Q) (i : Fin m)
    (hstart : s.lift i ≤ ellzero + 32 * r.val + 1)
    (hend : ellzero + 32 * r.val + 1 <
      (physicalRun B M hm s u).lift i) :
    ∃ v,
      Couple.firstReveal (physSource B M ellzero Q hm)
        (phaseIndex r i) s u = some v := by
  obtain ⟨pre, e, post, tick, hu, hsite, hlift, hact⟩ :=
    exists_increment_split B M hm s u i
      (ellzero + 32 * r.val + 1) hstart hend
  have hp0 := clockOf_mod_phase (M := M) (ellzero := ellzero)
    (n := 32 * r.val + 1) hdiv hzero
  have hp :
      clockOf M (ellzero + 32 * r.val + 1) % 32 = 1 := by
    calc
      clockOf M (ellzero + 32 * r.val + 1) % 32 =
          (32 * r.val + 1) % 32 := hp0
      _ = 1 := by omega
  have hb0 :
      physicalBitOf M ellzero Q hm
          (physicalRun B M hm s pre) e =
        some (phaseIndex r i, physicalBit e) :=
    (physicalBitOf_eq_some_iff M ellzero Q hm
      (physicalRun B M hm s pre) e r i (physicalBit e)).2
      ⟨hsite, rfl, ⟨tick, hact⟩, by simpa [hlift] using hp, hlift⟩
  have hb :
      (physSource B M ellzero Q hm).bitOf
          (physicalRun B M hm s pre) e =
        some (phaseIndex r i, physicalBit e) := by
    simpa only [physSource_bitOf] using hb0
  refine ⟨physicalBit e, ?_⟩
  rw [hu]
  exact firstReveal_eq_of_reveal B M ellzero Q hm s pre e post
    r i (physicalBit e) hb

private theorem all_phase_revealed {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot)
    (s0 : WordState m) (u : List (Fin (2 * m)))
    (hstart : StartConsistent B M ellzero hm choices start s0)
    (hfinish : ∀ i,
      (physicalRun B M hm s0 u).lift i = ellzero + 32 * Q) :
    ∀ r : Fin Q, ∀ i : Fin m,
      ∃ v,
        Couple.firstReveal (physSource B M ellzero Q hm)
          (phaseIndex r i) s0 u = some v := by
  intro r i
  have hinitial : s0.lift i ≤ ellzero + 32 * r.val + 1 := by
    rcases hstart i with h | h
    · rw [h.1]
      omega
    · rw [h.1]
      omega
  have hend : ellzero + 32 * r.val + 1 <
      (physicalRun B M hm s0 u).lift i := by
    rw [hfinish i]
    have hr := r.isLt
    omega
  exact firstReveal_covered B M ellzero Q hm hdiv hzero s0 u
    r i hinitial hend

private theorem levelCurr_exists_of_final_lift {m : Nat}
    (B M : Nat) (hm : 0 < m) :
    ∀ (h : List (Activation m)) (s : WordState m)
      (i : Fin m) (ell : Nat),
      (syncRun B M hm h s).lift i = ell →
      ∃ value,
        levelCurr B M hm h s i ell = some value := by
  intro h
  induction h with
  | nil =>
      intro s i ell hfinal
      refine ⟨(s.cfg i).curr, ?_⟩
      simp [syncRun] at hfinal
      simp [levelCurr, hfinal]
  | cons e h ih =>
      intro s i ell hfinal
      by_cases hnow : s.lift i = ell
      · refine ⟨(s.cfg i).curr, ?_⟩
        simp [levelCurr, hnow]
      · have htail :
            (syncRun B M hm h
              (activate B M hm s e.1 e.2)).lift i = ell := by
          simpa [syncRun] using hfinal
        obtain ⟨value, hv⟩ :=
          ih (activate B M hm s e.1 e.2) i ell htail
        refine ⟨value, ?_⟩
        simpa [levelCurr, hnow] using hv

theorem physical_snapshot_eq {m : Nat}
    (B M ellzero Q : Nat) (hm : 0 < m)
    (hM : ClockParams M)
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0)
    (start : Fin m → Snapshot) (s0 : WordState m)
    (u : List (Fin (2 * m)))
    (hleg : Legit M hm s0)
    (hstart : StartConsistent B M ellzero hm
      (physicalChoices B M ellzero Q hm s0 u) start s0)
    (hfinish : ∀ i,
      (physicalRun B M hm s0 u).lift i = ellzero + 32 * Q) :
    (∀ i,
      levelCurr B M hm (u.map physicalActivation) s0 i
          (ellzero + 32 * Q) =
        some
          (runRounds B hm
            (roundBits
              (physicalChoices B M ellzero Q hm s0 u) ellzero Q)
            start i)) ∧
    (∀ r : Fin Q, ∀ i : Fin m,
      ∃ v,
        Couple.firstReveal (physSource B M ellzero Q hm)
          (phaseIndex r i) s0 u = some v) := by
  let choices := physicalChoices B M ellzero Q hm s0 u
  change StartConsistent B M ellzero hm choices start s0 at hstart
  have hcap : ∀ i,
      (physicalRun B M hm s0 u).lift i ≤ ellzero + 32 * Q := by
    intro i
    rw [hfinish i]
    exact Nat.le_refl _
  have hhonor :
      Honors B M hm choices s0 (u.map physicalActivation) := by
    dsimp [choices]
    exact honors_readVector B M ellzero Q hm hM hdiv hzero
      start s0 u hleg hstart hcap
  have hrep : Represents B M ellzero hm choices start s0 :=
    startConsistent_represents hm choices start s0 hstart
  have hphase : ∀ n,
      clockOf M (ellzero + n) % 32 = n % 32 := by
    intro n
    exact clockOf_mod_phase hdiv hzero
  constructor
  · intro i
    have hrun := physicalRun_eq_syncRun B M hm s0 u
    have hfinalAct :
        (syncRun B M hm (u.map physicalActivation) s0).lift i =
          ellzero + 32 * Q := by
      rw [← hrun]
      exact hfinish i
    obtain ⟨value, hvalue⟩ :=
      levelCurr_exists_of_final_lift B M hm
        (u.map physicalActivation) s0 i (ellzero + 32 * Q) hfinalAct
    have hv := levelCurr_eq_sync hM hm choices start
      (u.map physicalActivation) s0 hleg hrep hhonor
      i (32 * Q) value hvalue
    have hsync := syncLevels_runRounds
      (B := B) (M := M) (ellzero := ellzero) (k := Q)
      hm choices start hphase
    have hv' : value =
        runRounds B hm (roundBits choices ellzero Q) start i := by
      calc
        value = syncLevels B M ellzero hm choices start (32 * Q) i := hv
        _ = runRounds B hm (roundBits choices ellzero Q) start i :=
          congrFun hsync i
    rw [hv'] at hvalue
    exact hvalue
  · intro r i
    exact all_phase_revealed B M ellzero Q hm hdiv hzero
      choices start s0 u hstart hfinish r i

#print axioms L4.Height.physSource
#print axioms L4.Height.reveal_once
#print axioms L4.Height.honors_readVector
#print axioms L4.Height.physical_snapshot_eq

end L4.Height

