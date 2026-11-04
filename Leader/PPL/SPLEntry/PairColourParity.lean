import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.SPLEntry.BuildGappedAssembly
import Init.Omega

/-!
# L18: a valid token working for an interior pair has the pair's colour

Under rooted `CDLAt`, for a pair `b < l18BlockCount n psi`, a token that is
`ValidToken kind` and `WorkingFor … kind b` has `kind = black` when `b` is
even and `kind = white` when `b` is odd (`l18ValidWorking_parity`).

Reason: `dist` is canonical (`off mod 2 psi`), the target sits in `S_(b+1)`
(right-moving) or `S_b` (left-moving), and no ring wrap occurs because the
host lies in offsets `[b psi, (b+2) psi - 2]` with `(b+2) psi < n`.  Hence the
target coordinate is `(off_target + d'_kind) mod 2 psi`, which lands in the
validity range only for the parity colour.

Consequence (`l18WrongColourClause`): at any `CDLAt` configuration the
wrong-colour clause of the token half of pair `b` holds vacuously, so the
token half of pair `b` only needs the colour `b % 2 = 0 ↦ black`,
`b % 2 = 1 ↦ white`.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-- Interior pairs end well before the ring closes: `(b+2) psi < n`. -/
theorem wc_blockEnd {n psi : Nat} (hpsi : 2 ≤ psi) (b : Nat)
    (hb : b < l18BlockCount n psi) : (b + 2) * psi < n := by
  unfold l18BlockCount at hb
  have hz : b + 3 ≤ segmentCount n psi := by omega
  unfold segmentCount at hz
  have hmul : (b + 3) * psi ≤ n + psi - 1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < psi)).mp hz
  have e1 : (b + 3) * psi = (b + 2) * psi + psi := by
    rw [show b + 3 = (b + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

/-- Offset of a right shift without wrap. -/
theorem wc_off_shiftRight {n : Nat} (ring : DirectedRing n) (root j : Fin n)
    (m : Nat) (hm : cyclicOffset ring root j + m < n) :
    cyclicOffset ring root (shiftRight ring j m) = cyclicOffset ring root j + m := by
  have hj := l18Gapped_site_eq_shiftRight_offset ring root j
  have hs : shiftRight ring j m =
      shiftRight ring root (cyclicOffset ring root j + m) := by
    rw [show shiftRight ring j m =
        shiftRight ring (shiftRight ring root (cyclicOffset ring root j)) m from
      congrArg (fun x => shiftRight ring x m) hj]
    exact l18Gapped_shiftRight_add ring root _ m
  rw [hs]
  exact l18Gapped_cyclicOffset_shiftRight_of_lt ring root _ hm

/-- Offset of a right shift with wrap. -/
theorem wc_off_shiftRight_wrap {n : Nat} (ring : DirectedRing n) (root j : Fin n)
    (m : Nat) (hmn : m < n) (hw : n ≤ cyclicOffset ring root j + m) :
    cyclicOffset ring root (shiftRight ring j m) =
      cyclicOffset ring root j + m - n := by
  have hj := l18Gapped_site_eq_shiftRight_offset ring root j
  have hlt := l18Gapped_cyclicOffset_lt ring root j
  have hs : shiftRight ring j m =
      shiftRight ring root (cyclicOffset ring root j + m - n) := by
    rw [show shiftRight ring j m =
        shiftRight ring (shiftRight ring root (cyclicOffset ring root j)) m from
      congrArg (fun x => shiftRight ring x m) hj]
    rw [l18Gapped_shiftRight_add ring root _ m]
    apply Fin.ext
    show (root.val + (cyclicOffset ring root j + m)) % n =
      (root.val + (cyclicOffset ring root j + m - n)) % n
    rw [show root.val + (cyclicOffset ring root j + m) =
        (root.val + (cyclicOffset ring root j + m - n)) + n by omega,
      Nat.add_mod_right]
  rw [hs]
  exact l18Gapped_cyclicOffset_shiftRight_of_lt ring root _ (by omega)

/-- A left shift is undone by the right shift of the same amount. -/
theorem wc_shiftRight_shiftLeft {n : Nat} (ring : DirectedRing n) (i : Fin n)
    (m : Nat) (hm : m < n) : shiftRight ring (shiftLeft ring i m) m = i := by
  apply Fin.ext
  show ((i.val + n - m % n) % n + m) % n = i.val
  rw [Nat.mod_eq_of_lt hm, Nat.mod_add_mod,
    show i.val + n - m + m = i.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.isLt]

/-- The target coordinate in terms of the target offset. -/
theorem wc_coord {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) (hC : CDLAt ring root C) (kind : TokenKind)
    (i : Fin n) (t : TokenData psi) (offT : Nat)
    (h : ((cyclicOffset ring root i : Nat) : Int) + decodeOffset psi (tokenCode t) =
      ((offT : Nat) : Int)) :
    tokenTargetCoordinate kind (C i) t =
      (((offT + tokenD' psi kind) % (2 * psi) : Nat) : Int) := by
  unfold tokenTargetCoordinate
  rw [(hC.2.2 i).1]
  rw [Int.natCast_emod, Int.natCast_emod, Int.add_assoc, Int.emod_add_emod,
    ← Int.add_assoc, h]
  push_cast
  rfl

/-- `(D q + x) mod D = x` for `x < D`. -/
theorem wc_mod (D q x : Nat) (hx : x < D) : (D * q + x) % D = x := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hx

/-- Parity of a valid working token for an interior pair, under `CDLAt`. -/
theorem l18ValidWorking_parity {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (hC : CDLAt ring root C) (kind : TokenKind)
    (i : Fin n) (hv : ValidToken kind C i) (hw : WorkingFor ring root C i kind b) :
    (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1) := by
  have hend := wc_blockEnd hpsi b hb
  have hz : b + 3 ≤ segmentCount n psi := by unfold l18BlockCount at hb; omega
  have hb1 : (b + 1) % segmentCount n psi = b + 1 := Nat.mod_eq_of_lt (by omega)
  have hoi := l18Gapped_cyclicOffset_lt ring root i
  unfold ValidToken at hv
  unfold WorkingFor at hw
  cases ht : tokenAt kind (C i) with
  | none => rw [ht] at hv; exact hv.elim
  | some t =>
    rw [ht] at hv hw
    dsimp only at hv hw
    have hvo := decodeOffset_valid psi (by omega) (tokenCode t)
    unfold ValidOffset at hvo
    generalize hcdef : decodeOffset psi (tokenCode t) = c at hv hw hvo
    rw [hb1] at hw
    -- q-decomposition of b
    obtain ⟨q, hq⟩ : ∃ q, b = 2 * q ∨ b = 2 * q + 1 := ⟨b / 2, by omega⟩
    have hbe : ∀ q', b = 2 * q' → b * psi = (2 * psi) * q' := by
      intro q' h; subst h
      rw [Nat.mul_assoc, Nat.mul_comm q' psi, ← Nat.mul_assoc]
    have hbo : ∀ q', b = 2 * q' + 1 → b * psi = (2 * psi) * q' + psi := by
      intro q' h; subst h
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm q' psi, ← Nat.mul_assoc]
    have hb1e : (b + 1) * psi = b * psi + psi := by rw [Nat.add_mul, Nat.one_mul]
    have hb2e : (b + 2) * psi = b * psi + psi + psi := by
      rw [Nat.add_mul, show 2 * psi = psi + psi by omega, Nat.add_assoc]
    by_cases hc : 0 < c
    · -- right-moving: target in S_(b+1)
      have hseg : InSegment ring root psi (b + 1) (tokenTargetSite ring i t) := by
        rcases hw.2 with ⟨_, h⟩ | ⟨h1, _⟩
        · exact h
        · omega
      unfold InSegment at hseg
      simp only [tokenTargetSite, hcdef, hc, ↓reduceIte] at hseg
      have hm : ((c.toNat : Nat) : Int) = c := Int.toNat_of_nonneg (by omega)
      have hmle : c.toNat ≤ psi := by omega
      have hoffT : cyclicOffset ring root (shiftRight ring i c.toNat) =
          cyclicOffset ring root i + c.toNat := by
        by_cases hw2 : cyclicOffset ring root i + c.toNat < n
        · exact wc_off_shiftRight ring root i _ hw2
        · exfalso
          rw [wc_off_shiftRight_wrap ring root i _ (by omega) (by omega)] at hseg
          have : psi ≤ (b + 1) * psi := by
            rw [hb1e]; omega
          omega
      rw [hoffT] at hseg
      have hcoord := wc_coord ring root C hC kind i t
        (cyclicOffset ring root i + c.toNat) (by rw [hcdef]; push_cast; omega)
      have hvv : ((psi : Nat) : Int) ≤ tokenTargetCoordinate kind (C i) t ∧
          tokenTargetCoordinate kind (C i) t ≤ (((2 * psi - 1 : Nat)) : Int) := by
        rcases hv with ⟨_, h1, h2⟩ | ⟨h1, _⟩
        · exact ⟨h1, h2⟩
        · omega
      obtain ⟨hlo, hhi⟩ := hvv
      rw [hcoord] at hlo hhi
      have hmin : cyclicOffset ring root i + c.toNat < (b + 1 + 1) * psi := by
        have := hseg.2
        have h2 : Nat.min ((b + 1 + 1) * psi) n ≤ (b + 1 + 1) * psi := Nat.min_le_left _ _
        omega
      rw [show b + 1 + 1 = b + 2 by omega] at hmin
      generalize hO : cyclicOffset ring root i + c.toNat = O at hseg hlo hhi hmin
      rcases hq with hq | hq
      · have e := hbe q hq
        cases kind with
        | black => exact Or.inl ⟨rfl, by omega⟩
        | white =>
            exfalso
            have hx : O + tokenD' psi .white =
                (2 * psi) * (q + 1) + (O - b * psi - psi) := by
              simp only [tokenD']; rw [Nat.mul_add, Nat.mul_one]; omega
            rw [hx, wc_mod _ _ _ (by omega)] at hlo
            omega
      · have e := hbo q hq
        cases kind with
        | white => exact Or.inr ⟨rfl, by omega⟩
        | black =>
            exfalso
            have hx : O + tokenD' psi .black =
                (2 * psi) * (q + 1) + (O - b * psi - psi) := by
              simp only [tokenD']; rw [Nat.mul_add, Nat.mul_one]; omega
            rw [hx, wc_mod _ _ _ (by omega)] at hlo
            omega
    · -- left-moving: target in S_b
      have hcneg : c < 0 := by omega
      have hseg : InSegment ring root psi b (tokenTargetSite ring i t) := by
        rcases hw.2 with ⟨h1, _⟩ | ⟨_, h⟩
        · omega
        · exact h
      unfold InSegment at hseg
      simp only [tokenTargetSite, hcdef, hc, ↓reduceIte] at hseg
      have hm : ((c.natAbs : Nat) : Int) = -c := by omega
      have hmle : c.natAbs + 1 ≤ psi := by omega
      generalize hT : shiftLeft ring i c.natAbs = tgt at hseg
      have hback : shiftRight ring tgt c.natAbs = i := by
        rw [← hT]; exact wc_shiftRight_shiftLeft ring i _ (by omega)
      have hmin : cyclicOffset ring root tgt < (b + 1) * psi := by
        have := hseg.2
        have h2 : Nat.min ((b + 1) * psi) n ≤ (b + 1) * psi := Nat.min_le_left _ _
        omega
      have hoi' : cyclicOffset ring root i = cyclicOffset ring root tgt + c.natAbs := by
        rw [← hback]
        exact wc_off_shiftRight ring root tgt _ (by omega)
      have hcoord := wc_coord ring root C hC kind i t
        (cyclicOffset ring root tgt) (by rw [hcdef, hoi']; push_cast; omega)
      have hvv : 1 ≤ tokenTargetCoordinate kind (C i) t ∧
          tokenTargetCoordinate kind (C i) t ≤ (((psi - 1 : Nat)) : Int) := by
        rcases hv with ⟨h1, _⟩ | ⟨_, h1, h2⟩
        · omega
        · exact ⟨h1, h2⟩
      obtain ⟨hlo, hhi⟩ := hvv
      rw [hcoord] at hlo hhi
      have hlow := hseg.1
      generalize hO : cyclicOffset ring root tgt = O at hlo hhi hmin hlow
      rcases hq with hq | hq
      · have e := hbe q hq
        cases kind with
        | black => exact Or.inl ⟨rfl, by omega⟩
        | white =>
            exfalso
            have hx : O + tokenD' psi .white =
                (2 * psi) * q + (O - b * psi + psi) := by
              simp only [tokenD']; omega
            rw [hx, wc_mod _ _ _ (by omega)] at hhi
            omega
      · have e := hbo q hq
        cases kind with
        | white => exact Or.inr ⟨rfl, by omega⟩
        | black =>
            exfalso
            have hx : O + tokenD' psi .black =
                (2 * psi) * q + (O - b * psi + psi) := by
              simp only [tokenD']; omega
            rw [hx, wc_mod _ _ _ (by omega)] at hhi
            omega

/-- The wrong-colour clause of the token half of pair `b` holds vacuously at
every `CDLAt` configuration. -/
theorem l18WrongColourClause {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (hC : CDLAt ring root C) (i : Fin n) :
    (b % 2 = 0 →
      (ValidToken .white C i ∧ WorkingFor ring root C i .white b) →
        CorrectToken ring root C i .white b) ∧
    (b % 2 = 1 →
      (ValidToken .black C i ∧ WorkingFor ring root C i .black b) →
        CorrectToken ring root C i .black b) := by
  refine ⟨fun he hVW => ?_, fun ho hVW => ?_⟩
  · rcases l18ValidWorking_parity hpsi ring root b hb C hC .white i hVW.1 hVW.2
      with ⟨h, _⟩ | ⟨_, h⟩
    · cases h
    · omega
  · rcases l18ValidWorking_parity hpsi ring root b hb C hC .black i hVW.1 hVW.2
      with ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · cases h

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18ValidWorking_parity
#print axioms PPL.Convergence.L18.l18WrongColourClause
