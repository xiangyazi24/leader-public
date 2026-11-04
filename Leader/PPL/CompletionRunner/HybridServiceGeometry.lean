import Leader.PPL.CompletionRunner.Hybrid
import Leader.PPL.TokenCompletion.ServiceGeometry
import Init.Omega

/-!
# Step-parametric Lemma 4: service geometry for the hybrid runner

`ServiceGeometry hybridRunner`, by re-running the ordinary proof of
`lemma4TwoSweepServiceGeometry_proved`
(`TokenCorrectnessLemma4ServiceGeometry.lean`) on the hybrid runner.

* Sections 3-6 of the ordinary file (ring arithmetic, the indexed H-block
  word, the phase-invariant arithmetic, window coordinates of sound owners
  under `C_d`) are protocol-free and are copied verbatim (lines 633-1103).
* Sections 7-10 (lines 1104-1947) are copied with `ghostStep`, `ghostRun`,
  `CdTrace` replaced by the hybrid runner's `gstep`, `run`, `cdTrace`, the five
  ordinary step Props replaced by the generic ones at `hybridRunner`, and the
  run facts replaced by `hybrid_runSound` and `idsUnique_run hybridRunner`.
* The two ghost-lineage facts of the ordinary proof, `sgOrigin` (every
  post-step owner descends from a pre-step owner with the same ID and birth
  site, or is born now) and `sgLeftNone` (an interaction with both endpoints
  unowned leaves the initiator unowned), are ghost-only.  For the hybrid step
  they follow from the ordinary private lemmas: in the ordinary branch
  directly, in the prime branch through `ghostStepPrime_eq_withPhys` (the
  prime ghost maps are the ordinary ones under the prelude agreement that
  `PrimeGood` supplies).
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 0. The two lineage facts for the hybrid step -/

/-- The hybrid step's ghost maps are the ordinary step's. -/
theorem hybrid_ghostTokenAt_eq {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) (j : Fin n) :
    ghostTokenAt kind (hybridRunner.gstep hpsi ring t G e) j =
      ghostTokenAt kind (ghostStep hpsi ring t G e) j := by
  rw [hybridRunner_gstep]
  by_cases hg : PrimeGood ring G.phys
  · rw [hybridGStep_good hpsi ring t G e hg,
      ghostStepPrime_eq_withPhys hpsi ring t G e (preludeAgree_of_good hpsi ring G.phys e hg)]
    cases kind <;> rfl
  · rw [hybridGStep_bad hpsi ring t G e hg]

private theorem sgOrigin
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) (j : Fin n) (z : GhostToken n psi)
    (h : ghostTokenAt kind (hybridRunner.gstep hpsi ring step G e) j = some z) :
    (∃ j0 : Fin n, ∃ z0 : GhostToken n psi,
        ghostTokenAt kind G j0 = some z0 ∧
          z.lmeta.id = z0.lmeta.id ∧
          z.lmeta.birthSite = z0.lmeta.birthSite) ∨
      z.lmeta.id = LineageId.born kind step := by
  rw [hybrid_ghostTokenAt_eq] at h
  exact (privc% Leader.PPL.TokenCompletion.ServiceGeometry PPL.sgOrigin)
    hpsi ring step G e kind j z h

private theorem sgLeftNone
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind)
    (hl : ghostTokenAt kind G e = none)
    (hr : ghostTokenAt kind G (ring.rightNeighbor e) = none) :
    ghostTokenAt kind (hybridRunner.gstep hpsi ring step G e) e = none := by
  rw [hybrid_ghostTokenAt_eq]
  exact (privc% Leader.PPL.TokenCompletion.ServiceGeometry PPL.sgLeftNone)
    hpsi ring step G e kind hl hr

/-! ## 3. Ring arithmetic -/


private theorem sgModEq (a b n q1 q2 : Nat)
    (h : a + n * q1 = b + n * q2) :
    a % n = b % n := by
  have h1 : (a + n * q1) % n = a % n :=
    Nat.add_mul_mod_self_left a n q1
  have h2 : (b + n * q2) % n = b % n :=
    Nat.add_mul_mod_self_left b n q2
  rw [← h1, ← h2, h]


private theorem sgModSub (A B n : Nat) (hn : 0 < n) (hBA : B ≤ A) :
    (A % n + n - B % n) % n = (A - B) % n := by
  have hA := Nat.mod_add_div A n
  have hB := Nat.mod_add_div B n
  have hBlt : B % n < n := Nat.mod_lt B hn
  apply sgModEq _ _ n (A / n) (B / n + 1)
  rw [Nat.mul_add, Nat.mul_one]
  omega


private theorem sgShiftZero {n : Nat}
    (ring : DirectedRing n) (k : Fin n) :
    shiftRight ring k 0 = k := by
  apply Fin.ext
  show (k.val + 0) % n = k.val
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt k.isLt


private theorem sgRightShift {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (x : Nat) :
    ring.rightNeighbor (shiftRight ring k x) =
      shiftRight ring k (x + 1) := by
  apply Fin.ext
  show ((k.val + x) % n + 1) % n = (k.val + (x + 1)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem sgLeftShift {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (x : Nat)
    (hx : 1 ≤ x) (hn2 : 2 ≤ n) :
    ring.leftNeighbor (shiftRight ring k x) =
      shiftRight ring k (x - 1) := by
  apply Fin.ext
  show ((k.val + x) % n + n - 1) % n = (k.val + (x - 1)) % n
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have h := sgModSub (k.val + x) 1 n (by omega) (by omega)
  rw [h1] at h
  rw [h]
  congr 1
  omega


private def sgL {n : Nat} (ring : DirectedRing n) (k : Fin n)
    (psi m : Nat) : Fin n :=
  shiftLeft ring (shiftRight ring k (2 * psi - 1)) (m + 1)


private theorem sgL_eq {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (psi m : Nat)
    (hm : m + 1 ≤ 2 * psi - 1) :
    sgL ring k psi m = shiftRight ring k (2 * psi - 2 - m) := by
  apply Fin.ext
  show ((k.val + (2 * psi - 1)) % n + n - (m + 1) % n) % n =
    (k.val + (2 * psi - 2 - m)) % n
  rw [sgModSub _ _ n ring.hn (by omega)]
  congr 1
  omega


/-! ## 4. The H block as an indexed letter list -/


private def sgIdx {n : Nat} (f : Nat → Fin n) : Nat → Nat → List (Fin n)
  | _, 0 => []
  | s, len + 1 => f s :: sgIdx f (s + 1) len


private theorem sgIdx_length {n : Nat} (f : Nat → Fin n) :
    ∀ (len s : Nat), (sgIdx f s len).length = len := by
  intro len
  induction len with
  | zero =>
      intro s
      rfl
  | succ len ih =>
      intro s
      simp only [sgIdx, List.length_cons]
      rw [ih (s + 1)]


private theorem sgIdx_ofFn {n : Nat} (f : Nat → Fin n) :
    ∀ (len s : Nat),
      List.ofFn (fun x : Fin len => f (s + x.val)) = sgIdx f s len := by
  intro len
  induction len with
  | zero =>
      intro s
      rfl
  | succ len ih =>
      intro s
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
      rw [sgIdx]
      congr 1
      have hfun :
          (fun i : Fin len => f (s + (i.val + 1))) =
            (fun i : Fin len => f (s + 1 + i.val)) := by
        funext i
        congr 1
        omega
      rw [hfun]
      exact ih (s + 1)


private theorem sgIdx_ofFn0 {n : Nat} (f : Nat → Fin n) (len : Nat) :
    List.ofFn (fun x : Fin len => f x.val) = sgIdx f 0 len := by
  have h := sgIdx_ofFn f len 0
  simp only [Nat.zero_add] at h
  exact h


private def sgWord {n : Nat} (ring : DirectedRing n) (k : Fin n)
    (psi s : Nat) : DetSchedule n :=
  sgIdx (fun m => shiftRight ring k m) s (2 * psi - 1 - s) ++
    sgIdx (sgL ring k psi) (s - (2 * psi - 1))
      (2 * psi - 1 - (s - (2 * psi - 1)))


private def sgE {n : Nat} (ring : DirectedRing n) (k : Fin n)
    (psi s : Nat) : Fin n :=
  if s < 2 * psi - 1 then
    shiftRight ring k s
  else
    sgL ring k psi (s - (2 * psi - 1))


private theorem sgWord_zero {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (psi : Nat) :
    lemma4Block ring k psi = sgWord ring k psi 0 := by
  unfold lemma4Block seqR seqL sgWord
  rw [sgIdx_ofFn0 (fun m => shiftRight ring k m) (2 * psi - 1)]
  rw [show (List.ofFn fun x : Fin (2 * psi - 1) =>
        shiftLeft ring (shiftRight ring k (2 * psi - 1)) (x.val + 1)) =
      sgIdx (sgL ring k psi) 0 (2 * psi - 1) from
    sgIdx_ofFn0 (sgL ring k psi) (2 * psi - 1)]
  simp only [Nat.zero_sub, Nat.sub_zero]


private theorem sgWord_length {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (psi s : Nat)
    (hs : s ≤ 4 * psi - 2) (hpsi : 2 ≤ psi) :
    (sgWord ring k psi s).length = 4 * psi - 2 - s := by
  unfold sgWord
  rw [List.length_append, sgIdx_length, sgIdx_length]
  omega


private theorem sgWord_cons {n : Nat}
    (ring : DirectedRing n) (k : Fin n) (psi s : Nat)
    (hpsi : 2 ≤ psi) (hs : s < 4 * psi - 2) :
    sgWord ring k psi s =
      sgE ring k psi s :: sgWord ring k psi (s + 1) := by
  by_cases hR : s < 2 * psi - 1
  · have h1 : 2 * psi - 1 - s = (2 * psi - 1 - (s + 1)) + 1 := by
      omega
    have h2 : s - (2 * psi - 1) = 0 := by
      omega
    have h3 : s + 1 - (2 * psi - 1) = 0 := by
      omega
    unfold sgWord sgE
    rw [h1, h2, h3, if_pos hR]
    simp only [sgIdx, List.cons_append]
  · obtain ⟨m, hm⟩ : ∃ m, s = 2 * psi - 1 + m := ⟨s - (2 * psi - 1), by omega⟩
    subst hm
    have h1 : 2 * psi - 1 - (2 * psi - 1 + m) = 0 := by
      omega
    have h1' : 2 * psi - 1 - (2 * psi - 1 + m + 1) = 0 := by
      omega
    have h2 : 2 * psi - 1 + m - (2 * psi - 1) = m := by
      omega
    have h3 : 2 * psi - 1 + m + 1 - (2 * psi - 1) = m + 1 := by
      omega
    have h4 : 2 * psi - 1 - m = (2 * psi - 1 - (m + 1)) + 1 := by
      omega
    unfold sgWord sgE
    rw [h1, h1', h2, h3, h4, if_neg hR]
    simp only [sgIdx, List.nil_append]


/-! ## 5. Arithmetic of the phase invariant -/


private theorem sgMono (B a1 q1 a2 q2 : Nat)
    (hq1 : q1 < B) (hq2 : q2 < B)
    (h : a1 * B + q1 ≤ a2 * B + q2) :
    a1 < a2 ∨ (a1 = a2 ∧ q1 ≤ q2) := by
  rcases Nat.lt_or_ge a1 a2 with hlt | hge
  · exact Or.inl hlt
  · rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · subst heq
      exact Or.inr ⟨rfl, by omega⟩
    · have hmul : (a2 + 1) * B ≤ a1 * B :=
        Nat.mul_le_mul_right B hlt
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega


/--
Phase invariant.  `s < 2 psi - 1`: seqR pointer `s`.
`s >= 2 psi - 1`: seqL pointer `m = s - (2 psi - 1)`, i.e. the next seqL
letter is the edge at coordinate `2 psi - 2 - m`.
-/
private def SgPC (psi a0 s a q x : Nat) : Prop :=
  a0 < a ∨
    (a = a0 ∧
      ((s < 2 * psi - 1 ∧ (psi ≤ q ∨ s ≤ x)) ∨
        (2 * psi - 1 ≤ s ∧ psi ≤ q ∧ x + s ≤ 4 * psi - 2)))


private theorem sgPC_step (psi a0 s s' a1 q1 x1 a2 q2 x2 : Nat)
    (hpsi : 2 ≤ psi)
    (hq1 : q1 < 2 * psi - 1) (hq2 : q2 < 2 * psi - 1)
    (ha1 : a1 < psi) (ha2 : a2 < psi)
    (hx1 : (q1 < psi ∧ x1 = a1 + q1) ∨ (psi ≤ q1 ∧ x1 + q1 = a1 + 2 * psi))
    (hx2 : (q2 < psi ∧ x2 = a2 + q2) ∨ (psi ≤ q2 ∧ x2 + q2 = a2 + 2 * psi))
    (hx2lt : x2 < 2 * psi)
    (hmono : a1 * (2 * psi - 1) + q1 ≤ a2 * (2 * psi - 1) + q2)
    (hpc : SgPC psi a0 s a1 q1 x1)
    (hmode :
      s' = s ∨
        (s' = s + 1 ∧ s < 4 * psi - 2 ∧
          (((s < 2 * psi - 1 ∧ q1 < psi ∧ x1 = s) ∨
              (2 * psi - 1 ≤ s ∧ psi ≤ q1 ∧ x1 + s = 4 * psi - 2)) →
            a2 * (2 * psi - 1) + q2 = a1 * (2 * psi - 1) + q1 + 1))) :
    SgPC psi a0 s' a2 q2 x2 := by
  have hm := sgMono (2 * psi - 1) a1 q1 a2 q2 hq1 hq2 hmono
  unfold SgPC at hpc ⊢
  rcases hm with hlt | ⟨heq, hqle⟩
  · left
    omega
  · subst heq
    rcases hpc with hlt0 | ⟨ha0, hph⟩
    · exact Or.inl hlt0
    · right
      refine ⟨ha0, ?_⟩
      rcases hmode with hs' | ⟨hs', hslt, hsvc⟩
      · subst hs'
        omega
      · subst hs'
        by_cases hc :
            (s < 2 * psi - 1 ∧ q1 < psi ∧ x1 = s) ∨
              (2 * psi - 1 ≤ s ∧ psi ≤ q1 ∧ x1 + s = 4 * psi - 2)
        · have hp := hsvc hc
          omega
        · omega


private theorem sgPC_end (psi a0 a q x : Nat)
    (hpsi : 2 ≤ psi)
    (hq : q < 2 * psi - 1)
    (hx : (q < psi ∧ x = a + q) ∨ (psi ≤ q ∧ x + q = a + 2 * psi))
    (hpc : SgPC psi a0 (4 * psi - 2) a q x) :
    a0 < a := by
  unfold SgPC at hpc
  omega


/-! ## 6. Coordinates of a sound window owner under C_d -/


private theorem sgIntZero (M W : Int) (hM : 0 < M)
    (h1 : -M < M * W) (h2 : M * W < M) : W = 0 := by
  rcases Int.lt_trichotomy W 0 with h | h | h
  · have hw : W ≤ -1 := by
      omega
    have hmul : M * W ≤ M * (-1) :=
      Int.mul_le_mul_of_nonneg_left hw (by omega)
    omega
  · exact h
  · have hw : 1 ≤ W := by
      omega
    have hmul : M * 1 ≤ M * W :=
      Int.mul_le_mul_of_nonneg_left hw (by omega)
    omega


private theorem sgCoord {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (hCd : Cd ring k kind C)
    (x : Nat) (hx : x < 2 * psi) (v : TokenData psi)
    (hval :
      (0 < decodeOffset psi (tokenCode v) ∧
          ((psi : Nat) : Int) ≤
            tokenTargetCoordinate kind (C (shiftRight ring k x)) v ∧
          tokenTargetCoordinate kind (C (shiftRight ring k x)) v ≤
            (((2 * psi - 1 : Nat)) : Int)) ∨
        (decodeOffset psi (tokenCode v) < 0 ∧
          1 ≤ tokenTargetCoordinate kind (C (shiftRight ring k x)) v ∧
          tokenTargetCoordinate kind (C (shiftRight ring k x)) v ≤
            (((psi - 1 : Nat)) : Int))) :
    (x : Int) + decodeOffset psi (tokenCode v) =
      tokenTargetCoordinate kind (C (shiftRight ring k x)) v := by
  have hdist :
      (C (shiftRight ring k x)).dist.val =
        (x + tokenD' psi kind) % (2 * psi) :=
    (hCd ⟨x, hx⟩).1
  have hcv := decodeOffset_valid psi (by omega) (tokenCode v)
  unfold ValidOffset at hcv
  have hdcase : tokenD' psi kind = 0 ∨ tokenD' psi kind = psi := by
    cases kind
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hT :
      tokenTargetCoordinate kind (C (shiftRight ring k x)) v =
        ((((C (shiftRight ring k x)).dist.val : Nat) : Int) +
            decodeOffset psi (tokenCode v) +
            (((tokenD' psi kind : Nat)) : Int)) %
          (((2 * psi : Nat)) : Int) := by
    rfl
  have hdiv :=
    Int.emod_add_ediv_mul
      ((((C (shiftRight ring k x)).dist.val : Nat) : Int) +
        decodeOffset psi (tokenCode v) +
        (((tokenD' psi kind : Nat)) : Int))
      (((2 * psi : Nat)) : Int)
  rw [← hT] at hdiv
  have hnat := Nat.mod_add_div (x + tokenD' psi kind) (2 * psi)
  rw [← hdist] at hnat
  have hnatI :
      ((((C (shiftRight ring k x)).dist.val : Nat) : Int)) +
          (((2 * psi : Nat)) : Int) *
            ((((x + tokenD' psi kind) / (2 * psi) : Nat)) : Int) =
        ((x : Nat) : Int) + (((tokenD' psi kind : Nat)) : Int) := by
    exact_mod_cast hnat
  have hMv : (((2 * psi : Nat)) : Int) = 2 * ((psi : Nat) : Int) := by
    omega
  generalize hQ :
      ((((C (shiftRight ring k x)).dist.val : Nat) : Int) +
          decodeOffset psi (tokenCode v) +
          (((tokenD' psi kind : Nat)) : Int)) /
        (((2 * psi : Nat)) : Int) = Q at hdiv
  rw [Int.mul_comm Q] at hdiv
  generalize hq1 :
      ((((x + tokenD' psi kind) / (2 * psi) : Nat)) : Int) = q1 at hnatI
  generalize hTT :
      tokenTargetCoordinate kind (C (shiftRight ring k x)) v = T
    at hdiv hval ⊢
  generalize hcc : decodeOffset psi (tokenCode v) = c at hdiv hval hcv ⊢
  generalize hDD :
      ((((C (shiftRight ring k x)).dist.val : Nat) : Int)) = D
    at hdiv hnatI
  generalize hdd : tokenD' psi kind = dd at hdiv hnatI hdcase
  generalize hM : (((2 * psi : Nat)) : Int) = M at hdiv hnatI hMv
  have hMpos : 0 < M := by
    omega
  have hmul : M * (Q + q1) = M * Q + M * q1 := Int.mul_add M Q q1
  have hmul2 : M * (Q + q1 - 1) = M * Q + M * q1 - M := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_one]
  rcases hdcase with h0 | hp
  · subst h0
    have hW : Q + q1 = 0 :=
      sgIntZero M (Q + q1) hMpos (by omega) (by omega)
    rw [hW, Int.mul_zero] at hmul
    omega
  · subst hp
    have hW : Q + q1 - 1 = 0 :=
      sgIntZero M (Q + q1 - 1) hMpos (by omega) (by omega)
    rw [hW, Int.mul_zero] at hmul2
    omega


/-- Stage/progress/coordinate summary of one window owner. -/
private def SgGeom {psi kappa : Nat} (kind : TokenKind)
    (st : State psi kappa) (v : TokenData psi) (x a q : Nat) : Prop :=
  lemma4TokenStage kind st v = psi + a ∧
    lemma4TokenProgress kind st v = a * (2 * psi - 1) + q ∧
    q < 2 * psi - 1 ∧
    a < psi ∧
    (0 < decodeOffset psi (tokenCode v) ↔ q < psi) ∧
    ((q < psi ∧ x = a + q) ∨ (psi ≤ q ∧ x + q = a + 2 * psi)) ∧
    x < 2 * psi


private theorem sgGeomCore {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind)
    (st : State psi kappa) (v : TokenData psi)
    (x : Nat) (hx : x < 2 * psi)
    (hxc :
      (x : Int) + decodeOffset psi (tokenCode v) =
        tokenTargetCoordinate kind st v)
    (hval :
      (0 < decodeOffset psi (tokenCode v) ∧
          ((psi : Nat) : Int) ≤ tokenTargetCoordinate kind st v ∧
          tokenTargetCoordinate kind st v ≤
            (((2 * psi - 1 : Nat)) : Int)) ∨
        (decodeOffset psi (tokenCode v) < 0 ∧
          1 ≤ tokenTargetCoordinate kind st v ∧
          tokenTargetCoordinate kind st v ≤
            (((psi - 1 : Nat)) : Int))) :
    ∃ a q, SgGeom kind st v x a q := by
  have hcv := decodeOffset_valid psi (by omega) (tokenCode v)
  unfold ValidOffset at hcv
  have hTn :
      (((tokenTargetCoordinate kind st v).toNat : Nat) : Int) =
        tokenTargetCoordinate kind st v :=
    Int.toNat_of_nonneg (by omega)
  rcases hval with ⟨hc, hT1, hT2⟩ | ⟨hc, hT1, hT2⟩
  · have hcn :
        (((decodeOffset psi (tokenCode v)).toNat : Nat) : Int) =
          decodeOffset psi (tokenCode v) :=
      Int.toNat_of_nonneg (by omega)
    have hstage :
        lemma4TokenStage kind st v =
          psi + ((tokenTargetCoordinate kind st v).toNat - psi) := by
      unfold lemma4TokenStage
      dsimp only
      rw [if_pos hc]
      omega
    refine
      ⟨(tokenTargetCoordinate kind st v).toNat - psi,
        psi - (decodeOffset psi (tokenCode v)).toNat,
        hstage, ?_, ?_, ?_, ?_, ?_, hx⟩
    · unfold lemma4TokenProgress
      dsimp only
      rw [hstage, if_pos hc, Nat.add_sub_cancel_left]
    · omega
    · omega
    · constructor
      · intro _
        omega
      · intro _
        exact hc
    · left
      omega
  · have hneg :
        (((-decodeOffset psi (tokenCode v)).natAbs : Nat) : Int) =
          -decodeOffset psi (tokenCode v) :=
      Int.natAbs_of_nonneg (by omega)
    rw [Int.natAbs_neg] at hneg
    have hnc : ¬ (0 < decodeOffset psi (tokenCode v)) := by
      omega
    have hstage :
        lemma4TokenStage kind st v =
          psi + ((tokenTargetCoordinate kind st v).toNat - 1) := by
      unfold lemma4TokenStage
      dsimp only
      rw [if_neg hnc]
      omega
    refine
      ⟨(tokenTargetCoordinate kind st v).toNat - 1,
        2 * psi - (decodeOffset psi (tokenCode v)).natAbs - 1,
        hstage, ?_, ?_, ?_, ?_, ?_, hx⟩
    · unfold lemma4TokenProgress
      dsimp only
      rw [hstage, if_neg hnc, Nat.add_sub_cancel_left]
    · omega
    · omega
    · constructor
      · intro h
        exact absurd h hnc
      · intro h
        omega
    · right
      omega



/-! ## 7. Reachable-state plumbing -/


private def SgReach {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C0 : Config n psi kappa)
    (t : Nat) (G : GhostConfig n psi kappa) : Prop :=
  ∃ p : DetSchedule n,
    G = hybridRunner.run hpsi ring 0 (initialGhost C0) p ∧ t = p.length


private theorem sgReach_step {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C0 : Config n psi kappa)
    (t : Nat) (G : GhostConfig n psi kappa)
    (hr : SgReach hpsi ring C0 t G) (e : Fin n) :
    SgReach hpsi ring C0 (t + 1) (hybridRunner.gstep hpsi ring t G e) := by
  obtain ⟨p, rfl, rfl⟩ := hr
  refine ⟨p ++ [e], ?_, by simp⟩
  rw [hybridRunner.run_append, Nat.zero_add, hybridRunner.run_single]


private theorem sgSound {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C0 : Config n psi kappa)
    (t : Nat) (G : GhostConfig n psi kappa)
    (hr : SgReach hpsi ring C0 t G) :
    GhostSound G := by
  obtain ⟨p, rfl, _⟩ := hr
  exact hybrid_runSound hpsi ring C0 p

private theorem sgTwoLeN
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 <= n := by
  by_cases hn2 : 2 <= n
  case pos =>
    exact hn2
  case neg =>
    have hn0 : 0 < n := ring.hn
    have hn1 : n = 1 := by
      omega
    subst n
    let x0 : Fin (2 * psi) := ⟨0, by omega⟩
    let x1 : Fin (2 * psi) := ⟨1, by omega⟩
    have h0 := (hCd x0).1
    have h1 := (hCd x1).1
    dsimp only [x0, x1] at h0 h1
    have hs :
        shiftRight ring k 0 =
          shiftRight ring k 1 := by
      apply Fin.ext
      simp [shiftRight]
    have hsame :
        (C (shiftRight ring k 0)).dist.val =
          (C (shiftRight ring k 1)).dist.val :=
      congrArg (fun i : Fin 1 => (C i).dist.val) hs
    have hcanon :
        (0 + tokenD' psi kind) % (2 * psi) =
          (1 + tokenD' psi kind) % (2 * psi) :=
      h0.symm.trans (hsame.trans h1)
    cases kind with
    | black =>
        have hm1 :
            1 % (2 * psi) = 1 :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm1] at hcanon
    | white =>
        have hm0 :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        have hm1 :
            (1 + psi) % (2 * psi) =
              1 + psi :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm0, hm1] at hcanon



private theorem sgUnique {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (C0 : Config n psi kappa)
    (t : Nat) (G : GhostConfig n psi kappa)
    (hr : SgReach hpsi ring C0 t G) (hn2 : 2 ≤ n) :
    GhostIdsUniqueAt t G := by
  obtain ⟨p, rfl, rfl⟩ := hr
  exact idsUnique_run hybridRunner hybrid_idsUniqueStep hpsi hn2 ring C0 p


private theorem sgOwnerTok {n psi kappa : Nat}
    (kind : TokenKind) (G : GhostConfig n psi kappa)
    (i : Fin n) (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value ∧ ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      refine ⟨hs.1, ?_⟩
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      refine ⟨hs.1, ?_⟩
      unfold ValidToken
      rw [hs.1]
      exact hs.2


private theorem sgGeomOwner {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (hCd : Cd ring k kind G.phys) (hsound : GhostSound G)
    (y : Nat) (hy : y < 2 * psi) (z : GhostToken n psi)
    (howner : ghostTokenAt kind G (shiftRight ring k y) = some z) :
    ∃ a q, SgGeom kind (G.phys (shiftRight ring k y)) z.value y a q := by
  have ht := sgOwnerTok kind G _ z hsound howner
  have hv := ht.2
  unfold ValidToken at hv
  rw [ht.1] at hv
  dsimp only at hv
  exact
    sgGeomCore hpsi kind _ z.value y hy
      (sgCoord hpsi ring k kind G.phys hCd y hy z.value hv) hv


private theorem sgRmOwner {n psi kappa : Nat}
    {ring : DirectedRing n} {k : Fin n} {kind : TokenKind}
    {G : GhostConfig n psi kappa} {x : Fin (2 * psi)}
    {z : GhostToken n psi}
    (h : Lemma4RightmostAt ring k kind G x z) :
    ghostTokenAt kind G (shiftRight ring k x.val) = some z :=
  h.1


private theorem sgRightmostExists {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (G : GhostConfig n psi kappa) (hsound : GhostSound G)
    (h : ∃ i : Fin n, ∃ z : GhostToken n psi,
      Lemma4InWindow ring k psi i ∧ ghostTokenAt kind G i = some z) :
    ∃ x : Fin (2 * psi), ∃ z : GhostToken n psi,
      Lemma4RightmostAt ring k kind G x z := by
  have key :
      ∀ d y : Nat, y < 2 * psi → 2 * psi - y ≤ d →
        (∃ z : GhostToken n psi,
          ghostTokenAt kind G (shiftRight ring k y) = some z) →
        ∃ x : Fin (2 * psi), ∃ z : GhostToken n psi,
          ghostTokenAt kind G (shiftRight ring k x.val) = some z ∧
            ∀ w : Fin (2 * psi), x.val < w.val →
              ghostTokenAt kind G (shiftRight ring k w.val) = none := by
    intro d
    induction d with
    | zero =>
        intro y hy hd _
        exfalso
        omega
    | succ d ih =>
        intro y hy hd hz
        obtain ⟨z, hz⟩ := hz
        rcases Classical.em
            (∃ w : Fin (2 * psi), y < w.val ∧
              ∃ z' : GhostToken n psi,
                ghostTokenAt kind G (shiftRight ring k w.val) = some z')
          with hmore | hmore
        · obtain ⟨w, hw, hz'⟩ := hmore
          exact ih w.val w.isLt (by omega) hz'
        · refine ⟨⟨y, hy⟩, z, hz, ?_⟩
          intro w hw
          cases hc : ghostTokenAt kind G (shiftRight ring k w.val) with
          | none => rfl
          | some z' =>
              exact absurd ⟨w, hw, z', hc⟩ hmore
  obtain ⟨i, z, ⟨x, rfl⟩, hz⟩ := h
  obtain ⟨x', z', hz', hmax⟩ :=
    key (2 * psi) x.val x.isLt (by omega) ⟨z, hz⟩
  refine ⟨x', z', ?_⟩
  exact ⟨hz', (sgOwnerTok kind G _ z' hsound hz').2, hmax⟩


/-! ## 8. Letter-by-letter walk through a scheduled block -/


private theorem sgWalk {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (Inv : DetSchedule n → Nat → GhostConfig n psi kappa → Prop)
    (hskip :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
        (word : DetSchedule n),
        SgReach hpsi ring C0 t G →
        Cd ring k kind G.phys →
        Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys →
        Inv word t G →
        Inv word (t + 1) (hybridRunner.gstep hpsi ring t G e))
    (htake :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
        (word : DetSchedule n),
        SgReach hpsi ring C0 t G →
        Cd ring k kind G.phys →
        Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys →
        Inv (e :: word) t G →
        Inv word (t + 1) (hybridRunner.gstep hpsi ring t G e))
    {word schedule : DetSchedule n}
    (hsub : word.Sublist schedule) :
    ∀ (t : Nat) (G : GhostConfig n psi kappa),
      SgReach hpsi ring C0 t G →
      hybridRunner.cdTrace hpsi ring k kind G.phys schedule →
      Inv word t G →
      ∃ t', Inv [] t' (hybridRunner.run hpsi ring t G schedule) := by
  induction hsub with
  | slnil =>
      intro t G _ _ hinv
      exact ⟨t, hinv⟩
  | @cons l1 l2 e h ih =>
      intro t G hr hc hinv
      have hc' := (hybridRunner.cdTrace_cons hpsi ring k kind G.phys e l2).mp hc
      have hpost :
          hybridRunner.cdTrace hpsi ring k kind (hybridRunner.gstep hpsi ring t G e).phys l2 := by
        rw [hybridRunner.gstep_phys]
        exact hc'.2
      have hCd1 := hybridRunner.cdTrace_start hpsi ring k kind _ l2 hpost
      rw [hybridRunner.run_cons]
      exact
        ih (t + 1) (hybridRunner.gstep hpsi ring t G e)
          (sgReach_step hpsi ring C0 t G hr e) hpost
          (hskip t G e l1 hr hc'.1 hCd1 hinv)
  | @cons_cons l1 l2 e h ih =>
      intro t G hr hc hinv
      have hc' := (hybridRunner.cdTrace_cons hpsi ring k kind G.phys e l2).mp hc
      have hpost :
          hybridRunner.cdTrace hpsi ring k kind (hybridRunner.gstep hpsi ring t G e).phys l2 := by
        rw [hybridRunner.gstep_phys]
        exact hc'.2
      have hCd1 := hybridRunner.cdTrace_start hpsi ring k kind _ l2 hpost
      rw [hybridRunner.run_cons]
      exact
        ih (t + 1) (hybridRunner.gstep hpsi ring t G e)
          (sgReach_step hpsi ring C0 t G hr e) hpost
          (htake t G e l1 hr hc'.1 hCd1 hinv)


private def SgInvBlock {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n)
    (C0 : Config n psi kappa)
    (Q : Nat → GhostConfig n psi kappa → Prop)
    (P : Nat → GhostConfig n psi kappa → Prop)
    (word : DetSchedule n) (t : Nat) (G : GhostConfig n psi kappa) : Prop :=
  SgReach hpsi ring C0 t G ∧ Q t G ∧
    ∃ s, s ≤ 4 * psi - 2 ∧ word = sgWord ring k psi s ∧ P s G


/--
Generic one-block driver: a per-letter frame invariant `Q` and a
pointer-indexed status `P` (skip letters keep the pointer, the prescribed
letter `sgE s` advances it) survive the whole scheduled block.
-/
private theorem sgBlock {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (Q : Nat → GhostConfig n psi kappa → Prop)
    (P : Nat → GhostConfig n psi kappa → Prop)
    (hQ :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n),
        SgReach hpsi ring C0 t G →
        Cd ring k kind G.phys →
        Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys →
        Q t G → Q (t + 1) (hybridRunner.gstep hpsi ring t G e))
    (hP :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) (s s' : Nat),
        SgReach hpsi ring C0 t G →
        Cd ring k kind G.phys →
        Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys →
        Q t G → s ≤ 4 * psi - 2 → P s G →
        (s' = s ∨ (s' = s + 1 ∧ s < 4 * psi - 2 ∧ e = sgE ring k psi s)) →
        P s' (hybridRunner.gstep hpsi ring t G e))
    (t : Nat) (G : GhostConfig n psi kappa) (schedule : DetSchedule n)
    (hr : SgReach hpsi ring C0 t G)
    (hc : hybridRunner.cdTrace hpsi ring k kind G.phys schedule)
    (hsub : (lemma4Block ring k psi).Sublist schedule)
    (hq : Q t G) (hp : P 0 G) :
    ∃ t', SgReach hpsi ring C0 t' (hybridRunner.run hpsi ring t G schedule) ∧
      Q t' (hybridRunner.run hpsi ring t G schedule) ∧
      P (4 * psi - 2) (hybridRunner.run hpsi ring t G schedule) := by
  have hskip :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
        (word : DetSchedule n),
        SgReach hpsi ring C0 t G →
        Cd ring k kind G.phys →
        Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys →
        SgInvBlock hpsi ring k C0 Q P word t G →
        SgInvBlock hpsi ring k C0 Q P word (t + 1)
          (hybridRunner.gstep hpsi ring t G e) := by
    intro t G e word hr hCd hCd' hinv
    obtain ⟨_, hq, s, hs, hw, hp⟩ := hinv
    exact
      ⟨sgReach_step hpsi ring C0 t G hr e,
        hQ t G e hr hCd hCd' hq, s, hs, hw,
        hP t G e s s hr hCd hCd' hq hs hp (Or.inl rfl)⟩
  have htake :
      ∀ (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
        (word : DetSchedule n),
        SgReach hpsi ring C0 t G →
        Cd ring k kind G.phys →
        Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys →
        SgInvBlock hpsi ring k C0 Q P (e :: word) t G →
        SgInvBlock hpsi ring k C0 Q P word (t + 1)
          (hybridRunner.gstep hpsi ring t G e) := by
    intro t G e word hr hCd hCd' hinv
    obtain ⟨_, hq, s, hs, hw, hp⟩ := hinv
    have hslt : s < 4 * psi - 2 := by
      rcases Nat.lt_or_ge s (4 * psi - 2) with h | h
      · exact h
      · exfalso
        have hl := sgWord_length ring k psi s hs hpsi
        rw [← hw, List.length_cons] at hl
        omega
    rw [sgWord_cons ring k psi s hpsi hslt] at hw
    obtain ⟨he, hw'⟩ := List.cons.inj hw
    exact
      ⟨sgReach_step hpsi ring C0 t G hr e,
        hQ t G e hr hCd hCd' hq, s + 1, hslt, hw',
        hP t G e s (s + 1) hr hCd hCd' hq hs hp
          (Or.inr ⟨rfl, hslt, he⟩)⟩
  have hinit : SgInvBlock hpsi ring k C0 Q P (lemma4Block ring k psi) t G :=
    ⟨hr, hq, 0, Nat.zero_le _, sgWord_zero ring k psi, hp⟩
  obtain ⟨t', hr', hq', s, hs, hw, hp'⟩ :=
    sgWalk hpsi ring k kind C0 (SgInvBlock hpsi ring k C0 Q P)
      hskip htake hsub t G hr hc hinit
  have hl := sgWord_length ring k psi s hs hpsi
  rw [← hw, List.length_nil] at hl
  have hs4 : s = 4 * psi - 2 := by
    omega
  subst hs4
  exact ⟨t', hr', hq', hp'⟩


/-! ## 9. Per-letter status steps -/


private theorem sgCovStep (hcov : CoverageStep hybridRunner)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa) (t : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hr : SgReach hpsi ring C0 t G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys)
    (hcovd : Lemma4GhostCoveredWindow ring k kind G) :
    Lemma4GhostCoveredWindow ring k kind (hybridRunner.gstep hpsi ring t G e) := by
  obtain ⟨p, rfl, rfl⟩ := hr
  have h := (hcov hpsi ring k kind).2 C0 p _ e rfl hCd hCd' hcovd
  exact h.1


private theorem sgCFStep (hcov : CoverageStep hybridRunner)
    (hpersist : FreshLineagePersistenceStep hybridRunner)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa) (t : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hr : SgReach hpsi ring C0 t G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys)
    (hcf : Lemma4CoveredFreshWindow ring k kind G) :
    Lemma4CoveredFreshWindow ring k kind (hybridRunner.gstep hpsi ring t G e) := by
  have hn2 := sgTwoLeN hpsi ring k kind G.phys hCd
  have huniq := sgUnique hpsi ring C0 t G hr hn2
  obtain ⟨p, rfl, rfl⟩ := hr
  have h := (hcov hpsi ring k kind).2 C0 p _ e rfl hCd hCd' hcf.2
  dsimp only at h
  refine ⟨?_, h.1⟩
  intro i z hwin howner
  rcases h.2 i z hwin howner with hf | ⟨j, z0, hwin0, howner0, hid⟩
  · exact hf
  · exact
      hpersist hpsi ring k kind p.length _ e j i z0 z huniq
        hwin0 howner0 (hcf.1 j z0 hwin0 howner0) hwin howner hid


private theorem sgHFCStep {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) (k : Fin n)
    (h : HasFreshCompletion kind k G) :
    HasFreshCompletion kind k (hybridRunner.gstep hpsi ring t G e) := by
  unfold HasFreshCompletion at h ⊢
  rcases h with ⟨m, hm, hf⟩
  refine ⟨m, ?_, hf⟩
  rcases hybridRunner.gstep_completed hpsi ring t G e with ⟨l, hl⟩
  rw [hl]
  exact List.mem_append_left l hm


private theorem sgTakeSvc {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (G : GhostConfig n psi kappa) (hn2 : 2 ≤ n)
    (s y a q : Nat) (z : GhostToken n psi)
    (hg : SgGeom kind (G.phys (shiftRight ring k y)) z.value y a q)
    (hs : s < 4 * psi - 2)
    (hc :
      (s < 2 * psi - 1 ∧ q < psi ∧ y = s) ∨
        (2 * psi - 1 ≤ s ∧ psi ≤ q ∧ y + s = 4 * psi - 2)) :
    sgE ring k psi s =
      lemma4ServiceEdge ring kind G (shiftRight ring k y) z := by
  have hiff := hg.2.2.2.2.1
  have hxy := hg.2.2.2.2.2.1
  have hq := hg.2.2.1
  rcases hc with ⟨hsR, hqp, hy⟩ | ⟨hsL, hqn, hy⟩
  · unfold lemma4ServiceEdge sgE
    rw [if_pos (hiff.mpr hqp), if_pos hsR, hy]
  · have hnc : ¬ (0 < decodeOffset psi (tokenCode z.value)) := by
      intro h
      have := hiff.mp h
      omega
    have hy1 : 1 ≤ y := by
      omega
    have hnR : ¬ (s < 2 * psi - 1) := by
      omega
    unfold lemma4ServiceEdge sgE
    rw [if_neg hnc, if_neg hnR,
      sgL_eq ring k psi (s - (2 * psi - 1)) (by omega),
      sgLeftShift ring k y hy1 hn2]
    congr 1
    omega


/-- Status of a tracked non-fresh owner: gone for good, or alive in phase. -/
private def SgOld1 {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (I : LineageId n) (b : Fin n) (a0 s : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  (∀ (j : Fin n) (z' : GhostToken n psi),
      ghostTokenAt kind G j = some z' → z'.lmeta.id ≠ I) ∨
    ∃ (y : Nat) (z' : GhostToken n psi) (a q : Nat),
      y < 2 * psi ∧
        ghostTokenAt kind G (shiftRight ring k y) = some z' ∧
        z'.lmeta.id = I ∧ z'.lmeta.birthSite = b ∧
        SgGeom kind (G.phys (shiftRight ring k y)) z'.value y a q ∧
        SgPC psi a0 s a q y


private theorem sgOld1Step
    (hold : OldOwnerProgressStep hybridRunner)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (I : LineageId n) (b : Fin n) (a0 : Nat)
    (hIb : ¬ ∃ t0 : Nat, I = LineageId.born kind t0 ∧ b = k)
    (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) (s s' : Nat)
    (hr : SgReach hpsi ring C0 t G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys)
    (hcovd : Lemma4GhostCoveredWindow ring k kind G)
    (htime : ∀ (bk : TokenKind) (s0 : Nat), I = LineageId.born bk s0 → s0 < t)
    (hst : SgOld1 ring k kind I b a0 s G)
    (hmode :
      s' = s ∨ (s' = s + 1 ∧ s < 4 * psi - 2 ∧ e = sgE ring k psi s)) :
    SgOld1 ring k kind I b a0 s' (hybridRunner.gstep hpsi ring t G e) := by
  have hn2 := sgTwoLeN hpsi ring k kind G.phys hCd
  have hsound' :=
    sgSound hpsi ring C0 (t + 1) _ (sgReach_step hpsi ring C0 t G hr e)
  have huniq := sgUnique hpsi ring C0 t G hr hn2
  have hnewid :
      ∀ (j : Fin n) (z' : GhostToken n psi),
        ghostTokenAt kind (hybridRunner.gstep hpsi ring t G e) j = some z' →
        z'.lmeta.id = I →
        ∃ j0 : Fin n, ∃ z0 : GhostToken n psi,
          ghostTokenAt kind G j0 = some z0 ∧ z0.lmeta.id = I ∧
            z'.lmeta.birthSite = z0.lmeta.birthSite := by
    intro j z' h hid
    rcases sgOrigin hpsi ring t G e kind j z' h with
      ⟨j0, z0, h0, h1, h2⟩ | hb
    · exact ⟨j0, z0, h0, h1.symm.trans hid, h2⟩
    · exfalso
      have := htime kind t (hid.symm.trans hb)
      omega
  rcases hst with hgone | ⟨y1, z1, a1, q1, hy1, how1, hid1, hbs1, hg1, hpc1⟩
  · left
    intro j z' h hid
    obtain ⟨j0, z0, h0, hid0, _⟩ := hnewid j z' h hid
    exact hgone j0 z0 h0 hid0
  · have hnf : ¬ FreshAt kind k z1.lmeta := by
      intro hf
      obtain ⟨t0, h1, h2⟩ := hf
      rw [hid1] at h1
      rw [hbs1] at h2
      exact hIb ⟨t0, h1, h2⟩
    obtain ⟨p, rfl, rfl⟩ := hr
    have hh :=
      hold hpsi ring k kind C0 p _ e rfl hCd hCd' hcovd
        (shiftRight ring k y1) z1 ⟨⟨y1, hy1⟩, rfl⟩ how1 hnf
    dsimp only at hh
    rcases hh with hgone' |
        ⟨j2, z2, hwin2, how2, hid2, _hval2, hmono, hsvc⟩
    · left
      intro j z' h hid
      exact hgone' j z' h (hid.trans hid1.symm)
    · obtain ⟨⟨y2, hy2⟩, rfl⟩ := hwin2
      have how2' :
          ghostTokenAt kind (hybridRunner.gstep hpsi ring p.length
              (hybridRunner.run hpsi ring 0 (initialGhost C0) p) e)
            (shiftRight ring k y2) = some z2 := how2
      obtain ⟨a2, q2, hg2⟩ :=
        sgGeomOwner hpsi ring k kind _ hCd' hsound' y2 hy2 z2 how2'
      have hbs2 : z2.lmeta.birthSite = b := by
        obtain ⟨j0, z0, h0, hid0, hbs0⟩ :=
          hnewid _ z2 how2' (hid2.trans hid1)
        have hj : j0 = shiftRight ring k y1 :=
          huniq.1 kind j0 _ z0 z1 h0 how1 (hid0.trans hid1.symm)
        subst hj
        have hz : z1 = z0 := Option.some.inj (how1.symm.trans h0)
        rw [hbs0, ← hz, hbs1]
      right
      refine ⟨y2, z2, a2, q2, hy2, how2', hid2.trans hid1, hbs2, hg2, ?_⟩
      have hmono' := hmono
      rw [hg1.2.1, hg2.2.1] at hmono'
      apply
        sgPC_step psi a0 s s' a1 q1 y1 a2 q2 y2 hpsi
          hg1.2.2.1 hg2.2.2.1 hg1.2.2.2.1 hg2.2.2.2.1
          hg1.2.2.2.2.2.1 hg2.2.2.2.2.2.1 hg2.2.2.2.2.2.2 hmono' hpc1
      rcases hmode with h | ⟨h1, h2, he⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, h2, ?_⟩
        intro hc
        have hsv :=
          sgTakeSvc hpsi ring k kind _ hn2 s y1 a1 q1 z1 hg1 h2 hc
        have hp := hsvc (he.trans hsv)
        rw [hg1.2.1, hg2.2.1] at hp
        exact hp


/-- Status of a tracked fresh rightmost owner. -/
private def SgFresh2 {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (I : LineageId n) (a0 s : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  HasFreshCompletion kind k G ∨
    ∃ (x : Fin (2 * psi)) (z' : GhostToken n psi) (a q : Nat),
      Lemma4RightmostAt ring k kind G x z' ∧
        z'.lmeta.id = I ∧ FreshAt kind k z'.lmeta ∧
        SgGeom kind (G.phys (shiftRight ring k x.val)) z'.value x.val a q ∧
        SgPC psi a0 s a q x.val


private theorem sgFresh2Step
    (hright : RightmostProgressStep hybridRunner)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (I : LineageId n) (a0 : Nat)
    (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) (s s' : Nat)
    (hr : SgReach hpsi ring C0 t G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys)
    (hcovd : Lemma4GhostCoveredWindow ring k kind G)
    (hst : SgFresh2 ring k kind I a0 s G)
    (hmode :
      s' = s ∨ (s' = s + 1 ∧ s < 4 * psi - 2 ∧ e = sgE ring k psi s)) :
    SgFresh2 ring k kind I a0 s' (hybridRunner.gstep hpsi ring t G e) := by
  have hn2 := sgTwoLeN hpsi ring k kind G.phys hCd
  have hsound' :=
    sgSound hpsi ring C0 (t + 1) _ (sgReach_step hpsi ring C0 t G hr e)
  rcases hst with hdone | ⟨x1, z1, a1, q1, hR1, hid1, hfr1, hg1, hpc1⟩
  · exact Or.inl (sgHFCStep hpsi ring t G e kind k hdone)
  · obtain ⟨p, rfl, rfl⟩ := hr
    have hh :=
      hright hpsi ring k kind C0 p _ e x1 z1 rfl hCd hCd' hcovd hR1
    dsimp only at hh
    rcases hh with ⟨hnf, _⟩ | hdone |
        ⟨x2, z2, hR2, hid2, hfr, hmono, hsvc⟩
    · exact absurd hfr1 hnf
    · exact Or.inl hdone
    · obtain ⟨a2, q2, hg2⟩ :=
        sgGeomOwner hpsi ring k kind _ hCd' hsound' x2.val x2.isLt z2
          (sgRmOwner hR2)
      right
      refine ⟨x2, z2, a2, q2, hR2, hid2.trans hid1, hfr hfr1, hg2, ?_⟩
      have hmono' := hmono
      rw [hg1.2.1, hg2.2.1] at hmono'
      apply
        sgPC_step psi a0 s s' a1 q1 x1.val a2 q2 x2.val hpsi
          hg1.2.2.1 hg2.2.2.1 hg1.2.2.2.1 hg2.2.2.2.1
          hg1.2.2.2.2.2.1 hg2.2.2.2.2.2.1 hg2.2.2.2.2.2.2 hmono' hpc1
      rcases hmode with h | ⟨h1, h2, he⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, h2, ?_⟩
        intro hc
        have hsv :=
          sgTakeSvc hpsi ring k kind _ hn2 s x1.val a1 q1 z1 hg1 h2 hc
        have hp := hsvc (he.trans hsv)
        rw [hg1.2.1, hg2.2.1] at hp
        exact hp


/-- Empty-window source step (the only place the source birth is used). -/
private theorem sgEmptyStep
    (hcov : CoverageStep hybridRunner)
    (hrows : SweepMissingRows hybridRunner)
    (hpersist : FreshLineagePersistenceStep hybridRunner)
    {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n) (s' : Nat)
    (hr : SgReach hpsi ring C0 t G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (hybridRunner.gstep hpsi ring t G e).phys)
    (hcf : Lemma4CoveredFreshWindow ring k kind G)
    (hemp : Lemma4WindowEmpty ring k kind G)
    (hmode :
      s' = 0 ∨ (s' = 0 + 1 ∧ 0 < 4 * psi - 2 ∧ e = sgE ring k psi 0)) :
    (s' = 0 ∧ Lemma4WindowEmpty ring k kind (hybridRunner.gstep hpsi ring t G e)) ∨
      ∃ I : LineageId n,
        SgFresh2 ring k kind I 0 s' (hybridRunner.gstep hpsi ring t G e) := by
  have hsound' :=
    sgSound hpsi ring C0 (t + 1) _ (sgReach_step hpsi ring C0 t G hr e)
  have hcf' := sgCFStep hcov hpersist hpsi ring k kind C0 t G e hr hCd hCd' hcf
  rcases hmode with rfl | ⟨rfl, _, he⟩
  · rcases Classical.em
        (∃ i : Fin n, ∃ z : GhostToken n psi,
          Lemma4InWindow ring k psi i ∧
            ghostTokenAt kind (hybridRunner.gstep hpsi ring t G e) i = some z)
      with hne | hne
    · obtain ⟨x, z', hR⟩ := sgRightmostExists ring k kind _ hsound' hne
      obtain ⟨a, q, hg⟩ :=
        sgGeomOwner hpsi ring k kind _ hCd' hsound' x.val x.isLt z'
          (sgRmOwner hR)
      right
      refine ⟨z'.lmeta.id, Or.inr ⟨x, z', a, q, hR, rfl,
        hcf'.1 _ z' ⟨x, rfl⟩ (sgRmOwner hR), hg, ?_⟩⟩
      unfold SgPC
      rcases Nat.eq_zero_or_pos a with h | h
      · right
        exact ⟨h, Or.inl ⟨by omega, Or.inr (Nat.zero_le _)⟩⟩
      · left
        exact h
    · left
      exact ⟨rfl, fun i z hwin how => hne ⟨i, z, hwin, how⟩⟩
  · have hek : e = k := by
      have h0 : 0 < 2 * psi - 1 := by
        omega
      rw [he]
      unfold sgE
      rw [if_pos h0]
      exact sgShiftZero ring k
    have hnone :
        ¬ ∃ i : Fin n, ∃ z : GhostToken n psi,
          Lemma4InWindow ring k psi i ∧ ghostTokenAt kind G i = some z := by
      intro h
      obtain ⟨i, z, hw, hz⟩ := h
      exact hemp i z hw hz
    have hl : ghostTokenAt kind G e = none := by
      cases hc : ghostTokenAt kind G e with
      | none => rfl
      | some w =>
          exact absurd hc
            (hemp e w ⟨⟨0, by omega⟩, hek.trans (sgShiftZero ring k).symm⟩)
    have hrr : ghostTokenAt kind G (ring.rightNeighbor e) = none := by
      cases hc : ghostTokenAt kind G (ring.rightNeighbor e) with
      | none => rfl
      | some w =>
          have hwin : Lemma4InWindow ring k psi (ring.rightNeighbor e) := by
            refine ⟨⟨1, by omega⟩, ?_⟩
            rw [hek]
            rfl
          exact absurd hc (hemp _ w hwin)
    have hleft := sgLeftNone hpsi ring t G e kind hl hrr
    obtain ⟨p, rfl, rfl⟩ := hr
    have hrw :=
      (hrows hpsi ring k kind C0 p _ e rfl hCd hCd' hcf.2).2 hnone hek
    rcases hrw with hdone | ⟨x, z', hR, hfr⟩
    · right
      exact ⟨LineageId.born kind 0, Or.inl hdone⟩
    · have hx1 : 1 ≤ x.val := by
        rcases Nat.eq_zero_or_pos x.val with h0 | h0
        · exfalso
          have hown := sgRmOwner hR
          rw [h0, sgShiftZero, ← hek, hleft] at hown
          cases hown
        · exact h0
      obtain ⟨a, q, hg⟩ :=
        sgGeomOwner hpsi ring k kind _ hCd' hsound' x.val x.isLt z'
          (sgRmOwner hR)
      right
      refine ⟨z'.lmeta.id, Or.inr ⟨x, z', a, q, hR, rfl, hfr, hg, ?_⟩⟩
      unfold SgPC
      rcases Nat.eq_zero_or_pos a with h | h
      · right
        exact ⟨h, Or.inl ⟨by omega, Or.inr (by omega)⟩⟩
      · left
        exact h


/-! ## 10. The service geometry -/


/-- The one-block service geometry for the hybrid runner. -/
theorem hybrid_serviceGeometry : ServiceGeometry hybridRunner := by
  unfold ServiceGeometry
  intro hcov hrows hright hold hpersist n psi kappa hpsi ring k kind
  refine ⟨?_, ?_, ?_⟩
  · -- old owners: deleted, or one strict macro-stage per block
    intro C0 pre G schedule i z hG hCdT hsub hcovd hwin howner _hvalid hnf
    dsimp only
    obtain ⟨⟨x0, hx0⟩, rfl⟩ := hwin
    have hr0 : SgReach hpsi ring C0 pre.length G := ⟨pre, hG, rfl⟩
    have hCd0 : Cd ring k kind G.phys :=
      hybridRunner.cdTrace_start hpsi ring k kind G.phys schedule hCdT
    have hsound0 := sgSound hpsi ring C0 _ G hr0
    obtain ⟨a0, q0, hg0⟩ :=
      sgGeomOwner hpsi ring k kind G hCd0 hsound0 x0 hx0 z howner
    have hn2 := sgTwoLeN hpsi ring k kind G.phys hCd0
    have huniq := sgUnique hpsi ring C0 _ G hr0 hn2
    have htime0 :
        ∀ (bk : TokenKind) (s0 : Nat),
          z.lmeta.id = LineageId.born bk s0 → s0 < pre.length := by
      intro bk s0 hb
      exact huniq.2 kind _ z bk s0 howner hb
    have hIb :
        ¬ ∃ t0 : Nat,
          z.lmeta.id = LineageId.born kind t0 ∧ z.lmeta.birthSite = k :=
      hnf
    obtain ⟨t', hrE, hqE, hpE⟩ :=
      sgBlock hpsi ring k kind C0
        (fun t G =>
          Lemma4GhostCoveredWindow ring k kind G ∧
            ∀ (bk : TokenKind) (s0 : Nat),
              z.lmeta.id = LineageId.born bk s0 → s0 < t)
        (fun s G =>
          SgOld1 ring k kind z.lmeta.id z.lmeta.birthSite a0 s G)
        (by
          intro t G e hr hCd hCd' hq
          exact
            ⟨sgCovStep hcov hpsi ring k kind C0 t G e hr hCd hCd' hq.1,
              fun bk s0 hb => Nat.lt_succ_of_lt (hq.2 bk s0 hb)⟩)
        (by
          intro t G e s s' hr hCd hCd' hq _ hp hmode
          exact
            sgOld1Step hold hpsi ring k kind C0 z.lmeta.id z.lmeta.birthSite
              a0 hIb t G e s s' hr hCd hCd' hq.1 hq.2 hp hmode)
        pre.length G schedule hr0 hCdT hsub ⟨hcovd, htime0⟩
        (Or.inr ⟨x0, z, a0, q0, hx0, howner, rfl, rfl, hg0,
          Or.inr ⟨rfl, Or.inl ⟨by omega, Or.inr (Nat.zero_le _)⟩⟩⟩)
    rcases hpE with hgone | ⟨y, z', a, q, hy, how, hid, hbs, hg, hpc⟩
    · exact Or.inl hgone
    · right
      have hlt :=
        sgPC_end psi a0 a q y hpsi hg.2.2.1 hg.2.2.2.2.2.1 hpc
      have hsoundE := sgSound hpsi ring C0 _ _ hrE
      refine ⟨shiftRight ring k y, z', ⟨⟨y, hy⟩, rfl⟩, how, hid, ?_,
        (sgOwnerTok kind _ _ z' hsoundE how).2, ?_⟩
      · intro hf
        obtain ⟨t0, h1, h2⟩ := hf
        rw [hid] at h1
        rw [hbs] at h2
        exact hIb ⟨t0, h1, h2⟩
      · rw [hg0.1, hg.1]
        omega
  · -- fresh rightmost owner: completion, or one strict macro-stage per block
    intro C0 pre G schedule x z hG hcf hCdT hsub hR hfresh
    dsimp only
    have hr0 : SgReach hpsi ring C0 pre.length G := ⟨pre, hG, rfl⟩
    have hCd0 : Cd ring k kind G.phys :=
      hybridRunner.cdTrace_start hpsi ring k kind G.phys schedule hCdT
    have hsound0 := sgSound hpsi ring C0 _ G hr0
    obtain ⟨a0, q0, hg0⟩ :=
      sgGeomOwner hpsi ring k kind G hCd0 hsound0 x.val x.isLt z
        (sgRmOwner hR)
    obtain ⟨t', hrE, hqE, hpE⟩ :=
      sgBlock hpsi ring k kind C0
        (fun _ G => Lemma4CoveredFreshWindow ring k kind G)
        (fun s G => SgFresh2 ring k kind z.lmeta.id a0 s G)
        (by
          intro t G e hr hCd hCd' hq
          exact sgCFStep hcov hpersist hpsi ring k kind C0 t G e hr hCd hCd' hq)
        (by
          intro t G e s s' hr hCd hCd' hq _ hp hmode
          exact
            sgFresh2Step hright hpsi ring k kind C0 z.lmeta.id a0
              t G e s s' hr hCd hCd' hq.2 hp hmode)
        pre.length G schedule hr0 hCdT hsub hcf
        (Or.inr ⟨x, z, a0, q0, hR, rfl, hfresh, hg0,
          Or.inr ⟨rfl, Or.inl ⟨by omega, Or.inr (Nat.zero_le _)⟩⟩⟩)
    rcases hpE with hdone | ⟨y, z', a, q, hRy, hid, hfr, hg, hpc⟩
    · exact Or.inl hdone
    · right
      have hlt :=
        sgPC_end psi a0 a q y.val hpsi hg.2.2.1 hg.2.2.2.2.2.1 hpc
      refine ⟨hqE, y, z', hRy, hid, hfr, ?_⟩
      rw [hg0.1, hg.1]
      omega
  · -- empty window: the source birth reaches stage psi + 1 in one block
    intro C0 pre G schedule hG hcf hempty hCdT hsub
    dsimp only
    have hr0 : SgReach hpsi ring C0 pre.length G := ⟨pre, hG, rfl⟩
    obtain ⟨t', hrE, hqE, hpE⟩ :=
      sgBlock hpsi ring k kind C0
        (fun _ G => Lemma4CoveredFreshWindow ring k kind G)
        (fun s G =>
          (s = 0 ∧ Lemma4WindowEmpty ring k kind G) ∨
            ∃ I : LineageId n, SgFresh2 ring k kind I 0 s G)
        (by
          intro t G e hr hCd hCd' hq
          exact sgCFStep hcov hpersist hpsi ring k kind C0 t G e hr hCd hCd' hq)
        (by
          intro t G e s s' hr hCd hCd' hq _ hp hmode
          rcases hp with ⟨hs0, hemp⟩ | ⟨I, hst⟩
          · subst hs0
            exact
              sgEmptyStep hcov hrows hpersist hpsi ring k kind C0 t G e s'
                hr hCd hCd' hq hemp hmode
          · exact
              Or.inr ⟨I, sgFresh2Step hright hpsi ring k kind C0 I 0
                t G e s s' hr hCd hCd' hq.2 hst hmode⟩)
        pre.length G schedule hr0 hCdT hsub hcf
        (Or.inl ⟨rfl, hempty⟩)
    rcases hpE with ⟨h0, _⟩ | ⟨I, hdone | ⟨y, z', a, q, hRy, _, hfr, hg, hpc⟩⟩
    · exfalso
      omega
    · exact Or.inl hdone
    · right
      have hlt :=
        sgPC_end psi 0 a q y.val hpsi hg.2.2.1 hg.2.2.2.2.2.1 hpc
      refine ⟨hqE, y, z', hRy, hfr, ?_⟩
      rw [hg.1]
      omega

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.hybrid_serviceGeometry
