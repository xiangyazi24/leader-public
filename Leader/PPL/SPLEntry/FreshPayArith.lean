import Leader.PPL.SPLEntry.GhostProvenance
import Leader.PPL.SPLEntry.PairColourParity
import Leader.PPL.SPLEntry.BuiltPairIds

/-!
# Fresh-lineage payload arithmetic (support for `FreshPay`)

Pure lemmas used by the fresh-lineage payload invariant:

* `firstZeroAux` / `firstZeroBit` facts (`fz_*`);
* `payloadCorrect` at a birth (`pay_birth`), under an unchanged bit/carry
  (`pay_sameBits`), after the `c = -1` turn to the next column (`pay_turn`),
  and its transport along an unchanged source segment (`pay_congr`);
* move-count division (`divq`);
* ring positions (`sr_zero`, `shiftLeft_shiftRight'`, `pred_of_rightNeighbor`);
* the prelude/black-move frame of the initiator's `id` and `dist`
  (`dm_left_id`, `prelude_left_id`, `prelude_left_dist`);
* the death of a lineage turning past the last source column
  (`turn_invalid_at_psi`).
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-! ## firstZero -/

theorem fz_bounds {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (s : Fin n) : ∀ fuel j, j ≤ firstZeroAux ring C s fuel j ∧
      firstZeroAux ring C s fuel j ≤ j + fuel := by
  intro fuel
  induction fuel with
  | zero => intro j; simp [firstZeroAux]
  | succ f ih =>
      intro j
      simp only [firstZeroAux]
      split
      · omega
      · have := ih (j + 1); omega

theorem fz_ones {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (s : Fin n) : ∀ fuel j y, j ≤ y → y < firstZeroAux ring C s fuel j →
      (C (shiftRight ring s y)).id = true := by
  intro fuel
  induction fuel with
  | zero => intro j y h1 h2; simp [firstZeroAux] at h2; omega
  | succ f ih =>
      intro j y h1 h2
      simp only [firstZeroAux] at h2
      split at h2
      · omega
      · rename_i hne
        by_cases hy : y = j
        · subst hy; simpa using hne
        · exact ih (j + 1) y (by omega) h2

theorem fz_zero {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (s : Fin n) : ∀ fuel j, firstZeroAux ring C s fuel j < j + fuel →
      (C (shiftRight ring s (firstZeroAux ring C s fuel j))).id = false := by
  intro fuel
  induction fuel with
  | zero => intro j h; simp [firstZeroAux] at h
  | succ f ih =>
      intro j h
      simp only [firstZeroAux] at h ⊢
      split
      · assumption
      · split at h
        · contradiction
        · exact ih (j + 1) (by omega)

theorem fz_first_false {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (s : Fin n) (fuel j : Nat) (hf : 0 < fuel) (h : (C (shiftRight ring s j)).id = false) :
    firstZeroAux ring C s fuel j = j := by
  cases fuel with
  | zero => omega
  | succ f => simp only [firstZeroAux]; rw [if_pos h]

theorem fz_congr {n psi kappa : Nat} (ring : DirectedRing n) (C C' : Config n psi kappa)
    (s : Fin n) (hid : ∀ y, y < psi → (C (shiftRight ring s y)).id = (C' (shiftRight ring s y)).id) :
    ∀ fuel j, j + fuel ≤ psi → firstZeroAux ring C s fuel j = firstZeroAux ring C' s fuel j := by
  intro fuel
  induction fuel with
  | zero => intro j _; rfl
  | succ f ih =>
      intro j h
      simp only [firstZeroAux]
      rw [hid j (by omega), ih (j + 1) (by omega)]

/-! ## payloadCorrect -/

theorem sr_zero {n : Nat} (ring : DirectedRing n) (k : Fin n) : shiftRight ring k 0 = k := by
  apply Fin.ext
  show (k.val + 0) % n = k.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt k.isLt]

theorem pay_sameBits {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (s : Fin n) (x : Nat) (t v : TokenData psi) (hb : v.1.2 = t.1.2) (hc : v.2 = t.2)
    (h : payloadCorrect ring C s x t) : payloadCorrect ring C s x v := by
  unfold payloadCorrect tokenBitBool tokenCarryBool at *
  rw [hb, hc]; exact h

theorem pay_congr {n psi kappa : Nat} (ring : DirectedRing n) (C C' : Config n psi kappa)
    (s : Fin n) (hid : ∀ y, y < psi → (C (shiftRight ring s y)).id = (C' (shiftRight ring s y)).id)
    (x : Nat) (hx : x < psi) (t : TokenData psi)
    (h : payloadCorrect ring C s x t) : payloadCorrect ring C' s x t := by
  unfold payloadCorrect firstZeroBit at *
  rw [← fz_congr ring C C' s hid psi 0 (by omega), ← hid x hx]
  exact h

private theorem bitVal (b : Bool) : ((if b then (1 : Fin 2) else (0 : Fin 2)).val == 1) = b := by
  cases b <;> rfl

theorem pay_birth {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa) (k : Fin n) (v : TokenData psi)
    (hb : tokenBitBool v = !(C k).id) (hc : tokenCarryBool v = (C k).id) :
    payloadCorrect ring C k 0 v := by
  unfold payloadCorrect
  have hbd := fz_bounds ring C k psi 0
  rw [sr_zero]
  refine ⟨?_, ?_⟩
  · rw [hb]; simp
  · rw [hc]
    unfold firstZeroBit
    cases hk : (C k).id
    · have : firstZeroAux ring C k psi 0 = 0 :=
        fz_first_false ring C k psi 0 (by omega) (by rw [sr_zero]; exact hk)
      rw [this]; rfl
    · have hpos : 0 < firstZeroAux ring C k psi 0 := by
        rcases Nat.eq_zero_or_pos (firstZeroAux ring C k psi 0) with h0 | h0
        · have := fz_zero ring C k psi 0 (by omega)
          rw [h0, sr_zero, hk] at this; cases this
        · exact h0
      simp [hpos]

theorem pay_turn {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (C : Config n psi kappa) (k : Fin n) (q : Nat) (hq : q + 1 < psi)
    (t : TokenData psi) (h : payloadCorrect ring C k q t) :
    payloadCorrect ring C k (q + 1)
      (q3GNegTurnNext hpsi (C (shiftRight ring k (q + 1))).id t) := by
  unfold payloadCorrect at h ⊢
  unfold firstZeroBit at h ⊢
  have hbd := fz_bounds ring C k psi 0
  generalize hj : firstZeroAux ring C k psi 0 = j at h hbd ⊢
  have hones : ∀ y, y < j → (C (shiftRight ring k y)).id = true := by
    intro y hy; rw [← hj] at hy; exact fz_ones ring C k psi 0 y (by omega) hy
  have hzero : j < psi → (C (shiftRight ring k j)).id = false := by
    intro hlt; have := fz_zero ring C k psi 0 (by omega); rw [hj] at this; exact this
  obtain ⟨hbit, hcar⟩ := h
  unfold q3GNegTurnNext
  generalize hs : (C (shiftRight ring k (q + 1))).id = s
  split
  · rename_i ht2
    have hcarT : tokenCarryBool t = true := by
      unfold tokenCarryBool; rw [ht2]; rfl
    rw [hcarT] at hcar
    have hqj : q < j := by
      by_cases hn : q < j
      · exact hn
      · rw [if_neg hn] at hcar; cases hcar
    dsimp only
    simp only [tokenBitBool, tokenCarryBool, q3GMkToken, q3GBitToFin, bitVal]
    refine ⟨?_, ?_⟩
    · rw [if_pos (show q + 1 ≤ j by omega)]
    · by_cases hlt : q + 1 < j
      · rw [if_pos hlt, ← hs]; exact hones _ hlt
      · rw [if_neg hlt, ← hs]
        have : q + 1 = j := by omega
        rw [this]; exact hzero (by omega)
  · rename_i ht2
    have hcarF : tokenCarryBool t = false := by
      unfold tokenCarryBool
      have := t.2.isLt
      cases h2 : t.2 using Fin.cases with
      | zero => rfl
      | succ m =>
          exfalso; apply ht2
          rw [h2]; apply Fin.ext; show m.val + 1 = 1
          have := m.isLt; omega
    rw [hcarF] at hcar
    have hqj : ¬ q < j := by
      intro hq'; rw [if_pos hq'] at hcar; cases hcar
    dsimp only
    simp only [tokenBitBool, tokenCarryBool, q3GMkToken, q3GBitToFin, bitVal]
    refine ⟨?_, ?_⟩
    · rw [if_neg (show ¬ (q + 1 ≤ j) by omega)]
    · rw [if_neg (show ¬ (q + 1 < j) by omega)]; rfl

/-! ## move-count division -/

theorem divq (q r D : Nat) (hr : r < D) : (q * D + r) / D = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]

/-! ## ring positions -/

theorem shiftLeft_shiftRight' {n : Nat} (ring : DirectedRing n) (i : Fin n)
    (m : Nat) (hm : m < n) : shiftLeft ring (shiftRight ring i m) m = i := by
  apply Fin.ext
  show ((i.val + m) % n + n - m % n) % n = i.val
  rw [Nat.mod_eq_of_lt hm]
  have hi := i.isLt
  by_cases h : i.val + m < n
  · rw [Nat.mod_eq_of_lt h, show i.val + m + n - m = i.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · have e : (i.val + m) % n = i.val + m - n := by
      rw [show i.val + m = (i.val + m - n) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e, show i.val + m - n + n - m = i.val by omega, Nat.mod_eq_of_lt hi]

theorem pred_of_rightNeighbor {n : Nat} (ring : DirectedRing n) (e k : Fin n) (y : Nat)
    (hn : 1 < n) (h : ring.rightNeighbor e = shiftRight ring k (y + 1)) :
    e = shiftRight ring k y := by
  have h1 : shiftRight ring e 1 = shiftRight ring (shiftRight ring k y) 1 := by
    rw [l18Gapped_shiftRight_add]; exact h
  have := congrArg (fun x => shiftLeft ring x 1) h1
  rwa [shiftLeft_shiftRight' ring e 1 hn, shiftLeft_shiftRight' ring _ 1 hn] at this

/-! ## initiator frame through the prelude and the black move -/

theorem dm_left_id {psi kappa : Nat} (l r : State psi kappa) :
    (PPL.determineMode l r).1.id = l.id ∧ (PPL.determineMode l r).1.dist = l.dist := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl⟩

theorem prelude_left_id {psi kappa : Nat} (hpsi : 2 ≤ psi) (l r : State psi kappa) :
    (q3GPrelude hpsi l r).1.id = l.id ∧ (q3GPrelude hpsi l r).1.dist = l.dist := by
  have h := dm_left_id l r
  unfold q3GPrelude
  dsimp only
  split
  · exact h
  · split
    · exact h
    · exact h

open Lean Elab Term Meta in
elab "q3ids% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairIds).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

/-- The initiator state seen by the selected colour's move. -/
def q3LState {psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) : State psi kappa :=
  match kind with
  | .black => (q3GPrelude hpsi l r).1
  | .white => (pprimeMoveToken hpsi .black (q3GPrelude hpsi l r).1 (q3GPrelude hpsi l r).2).1

theorem lstate_frame {psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) :
    (q3LState hpsi kind l r).id = l.id ∧ (q3LState hpsi kind l r).dist = l.dist := by
  have hp := prelude_left_id hpsi l r
  cases kind with
  | black => exact hp
  | white =>
      refine ⟨?_, ?_⟩
      · show (pprimeMoveToken hpsi .black _ _).1.id = l.id
        rw [(q3ids% "q20256PPrimeMoveTokenLeftId") hpsi .black]; exact hp.1
      · show (pprimeMoveToken hpsi .black _ _).1.dist = l.dist
        rw [(l18Gapped_pprimeMoveToken_dist_last hpsi .black _ _).1]; exact hp.2

/-! ## the lineage dies when it turns past the last source column -/

/-- A token with offset `psi` whose host has canonical distance
`(b+1) psi mod 2 psi` is locally invalid for the parity colour of pair `b`. -/
theorem turn_invalid_at_psi {psi kappa : Nat} (hpsi : 2 ≤ psi) (b : Nat)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (l : State psi kappa) (hd : l.dist.val = (b * psi + psi) % (2 * psi))
    (lid : Bool) (t : TokenData psi) :
    ¬ q3GLocalValid kind l (q3GNegTurnNext hpsi lid t) := by
  have hcode : decodeOffset psi (tokenCode (q3GNegTurnNext hpsi lid t)) = (psi : Int) := by
    unfold q3GNegTurnNext
    split <;> simp only [tokenCode, q3GMkToken] <;> exact decodeOffset_psi psi hpsi
  have hzero : tokenTargetCoordinate kind l (q3GNegTurnNext hpsi lid t) = 0 := by
    unfold tokenTargetCoordinate
    rw [hcode, hd]
    have key : ((b * psi + psi) % (2 * psi) + psi + tokenD' psi kind) % (2 * psi) = 0 := by
      rw [Nat.add_assoc, Nat.mod_add_mod]
      obtain ⟨q, hq⟩ : ∃ q, b = 2 * q ∨ b = 2 * q + 1 := ⟨b / 2, by omega⟩
      rcases hpar with ⟨hk, hb⟩ | ⟨hk, hb⟩ <;> subst hk
      · have hq' : b = 2 * q := by omega
        subst hq'
        rw [show 2 * q * psi + psi + (psi + tokenD' psi .black) = (2 * psi) * (q + 1) by
          simp only [tokenD']; rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm q psi,
            ← Nat.mul_assoc]; omega]
        exact Nat.mul_mod_right _ _
      · have hq' : b = 2 * q + 1 := by omega
        subst hq'
        rw [show (2 * q + 1) * psi + psi + (psi + tokenD' psi .white) = (2 * psi) * (q + 2) by
          simp only [tokenD']; rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_assoc,
            Nat.mul_comm q psi, ← Nat.mul_assoc]; omega]
        exact Nat.mul_mod_right _ _
    have : (((b * psi + psi) % (2 * psi) : Nat) : Int) + (psi : Int) + ((tokenD' psi kind : Nat) : Int)
        = (((b * psi + psi) % (2 * psi) + psi + tokenD' psi kind : Nat) : Int) := by push_cast; rfl
    rw [this, ← Int.natCast_emod, key]; rfl
  unfold q3GLocalValid
  rw [hzero, hcode]
  omega

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.pay_turn
#print axioms PPL.Convergence.L18.pay_birth
#print axioms PPL.Convergence.L18.turn_invalid_at_psi
#print axioms PPL.Convergence.L18.lstate_frame
#print axioms PPL.Convergence.L18.pred_of_rightNeighbor
