import Leader.PPL.SPLEntry.FreshPay
import Init.Omega

/-!
# L18: the trajectory key of a window token

For the Lemma-4 window at `k` (positions `x < 2 psi`) and a token offset `c`,
`q6Key psi x c` is the trajectory time of the window point `(x, c)`: the move
count a fresh lineage born at `k` has when it sits at `x` with offset `c`
(`q6_key_of_traj`).  With `D = 2 psi - 1`:

* `c > 0`: `key = (x + c - psi) * D + (psi - c)`;
* `c < 0`: `key = (x - |c| - 1) * D + (2 psi - 1 - |c|)`.

`q6ValidPt psi x c` is the window form of local validity under `Cd`
(`q6_validPt_of_local`).  On valid points the key is injective in the
position (`q6_key_inj`), every Algorithm-3 move adds exactly one to it
(`q6_key_moveR`, `q6_key_moveL`), key `0` sits at position `0`
(`q6_key_zero`), and key `x D + psi - 1` is the `c = 1` service of target bit
`x` (`q6_key_service`).
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-- Local validity of a window point `(x, c)` under `Cd`. -/
def q6ValidPt (psi x : Nat) (c : Int) : Prop :=
  (0 < c ∧ c ≤ ((psi : Nat) : Int) ∧ ((psi : Nat) : Int) ≤ (x : Int) + c ∧
      (x : Int) + c ≤ ((2 * psi - 1 : Nat) : Int)) ∨
    (c < 0 ∧ -c ≤ ((psi - 1 : Nat) : Int) ∧ 1 ≤ (x : Int) + c ∧
      (x : Int) + c ≤ ((psi - 1 : Nat) : Int))

/-- The trajectory key of the window point `(x, c)`. -/
def q6Key (psi x : Nat) (c : Int) : Nat :=
  if 0 < c then (x + c.toNat - psi) * (2 * psi - 1) + (psi - c.toNat)
  else (x - c.natAbs - 1) * (2 * psi - 1) + (2 * psi - 1 - c.natAbs)

theorem q6_modq (q r D : Nat) (hr : r < D) : (q * D + r) % D = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hr

/-- Three-range reduction of `a mod m`. -/
theorem q6_emod (a m : Int) (h1 : -m ≤ a) (h2 : a < 2 * m) (hm : 0 < m) :
    (a % m = a + m ∧ a < 0) ∨ (a % m = a ∧ 0 ≤ a ∧ a < m) ∨
      (a % m = a - m ∧ m ≤ a) := by
  by_cases ha : a < 0
  · left
    refine ⟨?_, ha⟩
    have h := Int.add_mul_emod_self_left a m 1
    rw [Int.mul_one] at h
    rw [← h]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · by_cases hb : a < m
    · exact Or.inr (Or.inl ⟨Int.emod_eq_of_lt (by omega) hb, by omega, hb⟩)
    · right; right
      refine ⟨?_, by omega⟩
      have h := Int.add_mul_emod_self_left (a - m) m 1
      rw [Int.mul_one, show a - m + m = a by omega] at h
      rw [h]
      exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Under `Cd`, local validity of a token at window position `x` is
`q6ValidPt`. -/
theorem q6_validPt_of_local {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (C : Config n psi kappa)
    (hCd : Cd ring k kind C) (x : Nat) (hx : x < 2 * psi) (t : TokenData psi)
    (hLV : q3GLocalValid kind (C (shiftRight ring k x)) t) :
    q6ValidPt psi x (decodeOffset psi (tokenCode t)) := by
  have hd := (hCd ⟨x, hx⟩).1
  dsimp only at hd
  have hvo := decodeOffset_valid psi (by omega) (tokenCode t)
  unfold ValidOffset at hvo
  unfold q3GLocalValid tokenTargetCoordinate at hLV
  rw [hd] at hLV
  generalize hcdef : decodeOffset psi (tokenCode t) = c at hLV hvo ⊢
  -- (x + d') % 2psi + d' = x + 2psi * w
  obtain ⟨w, hw⟩ : ∃ w : Nat,
      (x + tokenD' psi kind) % (2 * psi) + tokenD' psi kind = x + 2 * psi * w := by
    cases kind with
    | black =>
        refine ⟨0, ?_⟩
        simp only [tokenD', Nat.add_zero, Nat.mul_zero]
        exact Nat.mod_eq_of_lt hx
    | white =>
        simp only [tokenD']
        by_cases hxp : x < psi
        · refine ⟨1, ?_⟩
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        · refine ⟨0, ?_⟩
          rw [show x + psi = (x - psi) + 2 * psi by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
          omega
  have hcoord : ((((x + tokenD' psi kind) % (2 * psi) : Nat) : Int) + c +
      ((tokenD' psi kind : Nat) : Int)) % (((2 * psi : Nat)) : Int) =
      ((x : Int) + c) % (((2 * psi : Nat)) : Int) := by
    have hwI : ((((x + tokenD' psi kind) % (2 * psi) : Nat) : Int) +
        ((tokenD' psi kind : Nat) : Int)) = (x : Int) + ((2 * psi : Nat) : Int) * (w : Int) := by
      exact_mod_cast hw
    rw [show ((((x + tokenD' psi kind) % (2 * psi) : Nat) : Int) + c +
        ((tokenD' psi kind : Nat) : Int)) =
        ((x : Int) + c) + ((2 * psi : Nat) : Int) * (w : Int) by omega,
      Int.add_mul_emod_self_left]
  rw [hcoord] at hLV
  have hm : (0 : Int) < ((2 * psi : Nat) : Int) := by omega
  rcases q6_emod ((x : Int) + c) (((2 * psi : Nat)) : Int) (by omega) (by omega) hm with
    ⟨he, hneg⟩ | ⟨he, h0, hlt⟩ | ⟨he, hge⟩ <;> rw [he] at hLV
  · rcases hLV with ⟨hc, h1, h2⟩ | ⟨hc, h1, h2⟩ <;> omega
  · unfold q6ValidPt
    rcases hLV with ⟨hc, h1, h2⟩ | ⟨hc, h1, h2⟩
    · left; omega
    · right; omega
  · rcases hLV with ⟨hc, h1, h2⟩ | ⟨hc, h1, h2⟩ <;> omega

/-- A trajectory point's move count is the key. -/
theorem q6_key_of_traj (psi m x : Nat) (c : Int)
    (h : Lemma4FreshTrajectoryPoint psi m x c) : m = q6Key psi x c := by
  unfold q6Key
  rcases h with ⟨q, hc, hle, hx, hm⟩ | ⟨q, hc, hle, hx, hm⟩
  · rw [if_pos hc, show x + c.toNat - psi = q by omega, hm]
  · rw [if_neg (by omega), show x - c.natAbs - 1 = q by omega, hm]

/-- Keys are `q * D + r` with `r < D`; the pieces. -/
theorem q6_key_split {psi x : Nat} {c : Int} (hpsi : 2 ≤ psi) (h : q6ValidPt psi x c) :
    (0 < c ∧ q6Key psi x c = (x + c.toNat - psi) * (2 * psi - 1) + (psi - c.toNat) ∧
        psi - c.toNat < psi ∧ psi ≤ x + c.toNat) ∨
      (c < 0 ∧ q6Key psi x c = (x - c.natAbs - 1) * (2 * psi - 1) +
          (2 * psi - 1 - c.natAbs) ∧
        psi ≤ 2 * psi - 1 - c.natAbs ∧ 2 * psi - 1 - c.natAbs < 2 * psi - 1 ∧
        c.natAbs + 1 ≤ x) := by
  unfold q6ValidPt at h
  unfold q6Key
  rcases h with ⟨hc, h1, h2, h3⟩ | ⟨hc, h1, h2, h3⟩
  · left; rw [if_pos hc]; exact ⟨hc, rfl, by omega, by omega⟩
  · right; rw [if_neg (by omega)]; exact ⟨hc, rfl, by omega, by omega, by omega⟩

/-- On valid points the key determines the position and the offset. -/
theorem q6_key_inj {psi x x' : Nat} {c c' : Int} (hpsi : 2 ≤ psi)
    (h : q6ValidPt psi x c) (h' : q6ValidPt psi x' c')
    (he : q6Key psi x c = q6Key psi x' c') : x = x' ∧ c = c' := by
  have hD : 0 < 2 * psi - 1 := by omega
  have hdiv : q6Key psi x c / (2 * psi - 1) = q6Key psi x' c' / (2 * psi - 1) := by rw [he]
  have hmod : q6Key psi x c % (2 * psi - 1) = q6Key psi x' c' % (2 * psi - 1) := by rw [he]
  rcases q6_key_split hpsi h with ⟨hc, hk, hr, hq⟩ | ⟨hc, hk, hr1, hr2, hq⟩ <;>
    rcases q6_key_split hpsi h' with ⟨hc', hk', hr', hq'⟩ | ⟨hc', hk', hr1', hr2', hq'⟩ <;>
    rw [hk, hk'] at hdiv hmod
  · rw [divq (x + c.toNat - psi) (psi - c.toNat) _ (by omega),
      divq (x' + c'.toNat - psi) (psi - c'.toNat) _ (by omega)] at hdiv
    rw [q6_modq (x + c.toNat - psi) (psi - c.toNat) _ (by omega),
      q6_modq (x' + c'.toNat - psi) (psi - c'.toNat) _ (by omega)] at hmod
    unfold q6ValidPt at h h'
    omega
  · rw [q6_modq (x + c.toNat - psi) (psi - c.toNat) _ (by omega),
      q6_modq (x' - c'.natAbs - 1) (2 * psi - 1 - c'.natAbs) _ (by omega)] at hmod
    unfold q6ValidPt at h h'
    omega
  · rw [q6_modq (x - c.natAbs - 1) (2 * psi - 1 - c.natAbs) _ (by omega),
      q6_modq (x' + c'.toNat - psi) (psi - c'.toNat) _ (by omega)] at hmod
    unfold q6ValidPt at h h'
    omega
  · rw [divq (x - c.natAbs - 1) (2 * psi - 1 - c.natAbs) _ (by omega),
      divq (x' - c'.natAbs - 1) (2 * psi - 1 - c'.natAbs) _ (by omega)] at hdiv
    rw [q6_modq (x - c.natAbs - 1) (2 * psi - 1 - c.natAbs) _ (by omega),
      q6_modq (x' - c'.natAbs - 1) (2 * psi - 1 - c'.natAbs) _ (by omega)] at hmod
    unfold q6ValidPt at h h'
    omega

/-- Key zero sits at position zero. -/
theorem q6_key_zero {psi x : Nat} {c : Int} (hpsi : 2 ≤ psi)
    (h : q6ValidPt psi x c) (h0 : q6Key psi x c = 0) : x = 0 := by
  rcases q6_key_split hpsi h with ⟨hc, hk, hr, hq⟩ | ⟨hc, hk, hr1, hr2, hq⟩
  · rw [hk] at h0
    have hmod := congrArg (· % (2 * psi - 1)) h0
    have hdiv := congrArg (· / (2 * psi - 1)) h0
    rw [q6_modq _ _ _ (by omega)] at hmod
    rw [divq _ _ _ (by omega)] at hdiv
    simp only [Nat.zero_mod, Nat.zero_div] at hmod hdiv
    omega
  · rw [hk] at h0
    have hmod := congrArg (· % (2 * psi - 1)) h0
    rw [q6_modq _ _ _ (by omega)] at hmod
    simp only [Nat.zero_mod] at hmod
    omega

/-- Key `x D + (psi - 1)` is the `c = 1` service of target bit `x`, hosted at
window position `x + psi - 1`. -/
theorem q6_key_service {psi y x : Nat} {c : Int} (hpsi : 2 ≤ psi)
    (h : q6ValidPt psi y c)
    (hk0 : q6Key psi y c = x * (2 * psi - 1) + (psi - 1)) :
    c = 1 ∧ y + 1 = x + psi := by
  have hmod := congrArg (· % (2 * psi - 1)) hk0
  have hdiv := congrArg (· / (2 * psi - 1)) hk0
  rw [q6_modq _ _ _ (by omega)] at hmod
  rw [divq _ _ _ (by omega)] at hdiv
  rcases q6_key_split hpsi h with ⟨hc, hk, hr, hq⟩ | ⟨hc, hk, hr1, hr2, hq⟩
  · rw [hk, q6_modq _ _ _ (by omega)] at hmod
    rw [hk, divq _ _ _ (by omega)] at hdiv
    omega
  · rw [hk, q6_modq _ _ _ (by omega)] at hmod
    omega

theorem q6_decode_negPsi {psi : Nat} (hpsi : 2 ≤ psi) (b c : Fin 2) :
    decodeOffset psi (tokenCode (q3GMkToken (offsetNegPsiPlusOneCode psi hpsi) b c)) =
      1 - ((psi : Nat) : Int) := by
  simp only [tokenCode, q3GMkToken]
  exact decodeOffset_negPsiPlusOne psi hpsi

theorem q6_decode_turn {psi : Nat} (hpsi : 2 ≤ psi) (s : Bool) (t : TokenData psi) :
    decodeOffset psi (tokenCode (q3GNegTurnNext hpsi s t)) = ((psi : Nat) : Int) := by
  unfold q3GNegTurnNext
  split <;> (simp only [tokenCode, q3GMkToken]; exact decodeOffset_psi psi hpsi)

/-- A right move adds one to the key. -/
theorem q6_key_moveR {psi y : Nat} (hpsi : 2 ≤ psi) (t v : TokenData psi)
    (h : q6ValidPt psi y (decodeOffset psi (tokenCode t)))
    (hmv : q3MoveR hpsi t v) :
    q6Key psi (y + 1) (decodeOffset psi (tokenCode v)) =
      q6Key psi y (decodeOffset psi (tokenCode t)) + 1 := by
  unfold q6ValidPt at h
  unfold q6Key
  rcases hmv with ⟨h1, hv⟩ | ⟨h2, hdv, _, _⟩
  · rw [hv, q6_decode_negPsi, h1]
    rw [h1] at h
    rw [if_neg (by omega), if_pos (by omega)]
    have e1 : y + 1 - (1 - ((psi : Nat) : Int)).natAbs - 1 = y + (1 : Int).toNat - psi := by
      omega
    have e2 : 2 * psi - 1 - (1 - ((psi : Nat) : Int)).natAbs = psi - (1 : Int).toNat + 1 := by
      omega
    rw [e1, e2]; omega
  · rw [hdv]
    generalize hcd : decodeOffset psi (tokenCode t) = c at h h2 ⊢
    rw [if_pos (by omega), if_pos (by omega)]
    have e1 : y + 1 + (c - 1).toNat - psi = y + c.toNat - psi := by omega
    have e2 : psi - (c - 1).toNat = psi - c.toNat + 1 := by omega
    rw [e1, e2]; omega

/-- A left move adds one to the key. -/
theorem q6_key_moveL {psi kappa y : Nat} (hpsi : 2 ≤ psi) (l : State psi kappa)
    (t v : TokenData psi)
    (h : q6ValidPt psi y (decodeOffset psi (tokenCode t)))
    (hmv : q3MoveL hpsi l t v) :
    q6Key psi (y - 1) (decodeOffset psi (tokenCode v)) =
      q6Key psi y (decodeOffset psi (tokenCode t)) + 1 := by
  unfold q6ValidPt at h
  unfold q6Key
  rcases hmv with ⟨h1, hv⟩ | ⟨h2, hdv, _, _⟩
  · rw [hv, q6_decode_turn, h1]
    rw [h1] at h
    rw [if_pos (by omega), if_neg (by omega)]
    have e1 : y - 1 + ((psi : Nat) : Int).toNat - psi = (y - (-1 : Int).natAbs - 1) + 1 := by
      omega
    have e2 : psi - ((psi : Nat) : Int).toNat = 0 := by omega
    rw [e1, e2, Nat.succ_mul]
    omega
  · rw [hdv]
    generalize hcd : decodeOffset psi (tokenCode t) = c at h h2 ⊢
    rw [if_neg (by omega), if_neg (by omega)]
    have e1 : y - 1 - (c + 1).natAbs - 1 = y - c.natAbs - 1 := by omega
    have e2 : 2 * psi - 1 - (c + 1).natAbs = 2 * psi - 1 - c.natAbs + 1 := by omega
    rw [e1, e2]; omega

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q6_validPt_of_local
#print axioms PPL.Convergence.L18.q6_key_inj
#print axioms PPL.Convergence.L18.q6_key_service
#print axioms PPL.Convergence.L18.q6_key_moveR
#print axioms PPL.Convergence.L18.q6_key_moveL
