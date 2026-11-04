import Leader.PPL.SPLEntry.FreshPay
import Leader.PPL.SPLEntry.WhiteFrame
import Leader.PPL.SPLEntry.WhiteTokenHalf
import Leader.PPL.CompletionRunner.HybridCore
import Leader.PPL.CompletionRunner.HybridServiceGeometry
import Leader.PPL.CompletionRunner.Backstep
import Init.Omega

/-!
# L18: the half-word token row, unconditionally

`l18PrimeHalfWordTokenHalfRow_proved : L18PrimeHalfWordTokenHalfRow`.

From `L18BuildPrefixAt ring root b C` and a prime schedule `pre` containing
block `b`'s half word `H^psi` (based at `k = root + b psi`), the prime run ends
with the token half of pair `b` (`L18TokenHalfAt`); the SPL disjunct is never
used.

Route (ghost level, no physical old-image linking):

1. Along the prime ghost run from `initialGhost C`, carry
   `Prefix b ∧ HybridInv ∧ FreshPay` (`q4_run_freshPay`): the prefix frame is
   `l18PrimeStepPreservesBuildPrefix_of_white` with the proved white frame,
   `HybridInv` is `hybridInv_step` rewritten by `hybridGStep_good`, and
   `FreshPay` is `freshPay_step`.
2. The generic first-power purge (`halfPowerFirstPowerInduction_proved` on
   `hybridRunner`) gives a covered-fresh window at the end of `pre`; the hybrid
   run equals the prime run from a `PrimeGood` start.
3. A token working for pair `b` is hosted in the `2 psi` window at `k`
   (`q4_host_window`).
4. Its ghost owner is fresh; kinematics puts its target at `k + (q + psi)`
   (right-moving) or `k + (q + 1)` (left-moving) with `q = moves / (2 psi - 1)`,
   and `FreshPay` supplies `q < psi` and the payload (`q4_correct`).
5. The other colour is vacuous (`l18WrongColourClause`).
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-- A token working for interior pair `b` is hosted in the `2 psi` window
based at `root + b psi`. -/
theorem q4_host_window {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (kind : TokenKind) (i : Fin n)
    (hw : WorkingFor ring root C i kind b) :
    ∃ x : Nat, x < 2 * psi ∧ i = shiftRight ring (shiftRight ring root (b * psi)) x := by
  have hend := wc_blockEnd hpsi b hb
  have hz : b + 3 ≤ segmentCount n psi := by unfold l18BlockCount at hb; omega
  have hb1 : (b + 1) % segmentCount n psi = b + 1 := Nat.mod_eq_of_lt (by omega)
  have hoi := l18Gapped_cyclicOffset_lt ring root i
  have hb1e : (b + 1) * psi = b * psi + psi := by rw [Nat.add_mul, Nat.one_mul]
  have hb2e : (b + 2) * psi = b * psi + psi + psi := by
    rw [Nat.add_mul, show 2 * psi = psi + psi by omega, Nat.add_assoc]
  suffices hO : b * psi ≤ cyclicOffset ring root i ∧
      cyclicOffset ring root i < b * psi + 2 * psi by
    refine ⟨cyclicOffset ring root i - b * psi, by omega, ?_⟩
    rw [l18Gapped_shiftRight_add,
      show b * psi + (cyclicOffset ring root i - b * psi) = cyclicOffset ring root i by omega]
    exact l18Gapped_site_eq_shiftRight_offset ring root i
  unfold WorkingFor at hw
  cases ht : tokenAt kind (C i) with
  | none => rw [ht] at hw; exact hw.elim
  | some t =>
    rw [ht] at hw
    dsimp only at hw
    have hvo := decodeOffset_valid psi (by omega) (tokenCode t)
    unfold ValidOffset at hvo
    generalize hcdef : decodeOffset psi (tokenCode t) = c at hw hvo
    rw [hb1] at hw
    by_cases hc : 0 < c
    · have hseg : InSegment ring root psi (b + 1) (tokenTargetSite ring i t) := by
        rcases hw.2 with ⟨_, h⟩ | ⟨h1, _⟩
        · exact h
        · omega
      unfold InSegment at hseg
      simp only [tokenTargetSite, hcdef, hc, ↓reduceIte] at hseg
      have hmle : c.toNat ≤ psi := by omega
      have hm1 : 1 ≤ c.toNat := by omega
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
      have hmin : cyclicOffset ring root i + c.toNat < (b + 1 + 1) * psi := by
        have := hseg.2
        have h2 : Nat.min ((b + 1 + 1) * psi) n ≤ (b + 1 + 1) * psi := Nat.min_le_left _ _
        omega
      rw [show b + 1 + 1 = b + 2 by omega] at hmin
      have hlow := hseg.1
      omega
    · have hcneg : c < 0 := by omega
      have hseg : InSegment ring root psi b (tokenTargetSite ring i t) := by
        rcases hw.2 with ⟨h1, _⟩ | ⟨_, h⟩
        · omega
        · exact h
      unfold InSegment at hseg
      simp only [tokenTargetSite, hcdef, hc, ↓reduceIte] at hseg
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
      have hlow := hseg.1
      omega

/-- The parity colour of block `b` satisfies the parity condition. -/
theorem q4_blockKind_par (b : Nat) :
    (PPL.Lemma4Generic.l18BlockKind b = .black ∧ b % 2 = 0) ∨
      (PPL.Lemma4Generic.l18BlockKind b = .white ∧ b % 2 = 1) := by
  unfold PPL.Lemma4Generic.l18BlockKind
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · left; rw [if_pos h]; exact ⟨rfl, h⟩
  · right; rw [if_neg (by omega)]; exact ⟨rfl, h⟩

/-- `FreshPay` holds at an initial ghost: no initial owner is a birth. -/
theorem q4_freshPay_initial {n psi kappa : Nat} (ring : DirectedRing n)
    (kind : TokenKind) (k : Fin n) (C : Config n psi kappa) :
    FreshPay ring kind k (PPL.initialGhost C) := by
  intro i z howner hfresh
  rcases hfresh with ⟨t, hborn, _hsite⟩
  have hU := (ghostIdsUnique_initial C).2 kind i z kind t howner hborn
  omega

/-- `FreshPay` along every prime ghost run that starts inside `Prefix b` with
the hybrid invariant. -/
theorem q4_run_freshPay {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1)) :
    ∀ (pre : DetSchedule n) (t : Nat) (G : GhostConfig n psi kappa),
      L18BuildPrefixAt ring root b G.phys →
      PPL.Lemma4Generic.HybridInv ring t G →
      FreshPay ring kind (shiftRight ring root (b * psi)) G →
      FreshPay ring kind (shiftRight ring root (b * psi))
        (ghostRunPrime hpsi ring t G pre) := by
  intro pre
  induction pre with
  | nil => intro t G _ _ hF; exact hF
  | cons e es ih =>
    intro t G hP hI hF
    have hg := PPL.Lemma4Generic.primeGood_of_buildPrefix hn3 hpsi ring root b G.phys hb hP
    have hI' := PPL.Lemma4Generic.hybridInv_step hpsi ring t G e hI
    rw [PPL.Lemma4Generic.hybridGStep_good hpsi ring t G e hg] at hI'
    show FreshPay ring kind (shiftRight ring root (b * psi))
      (ghostRunPrime hpsi ring (t + 1) (ghostStepPrime hpsi ring t G e) es)
    exact ih (t + 1) (ghostStepPrime hpsi ring t G e)
      (l18PrimeStepPreservesBuildPrefix_of_white l18PrimeSelectedWhiteFrame_proved
        hn3 hpsi ring root b G.phys e hb hP)
      hI'
      (freshPay_step hn3 hpsi ring root b hb kind hpar G t e (hI.2.2.1 _) hP hF)

/-- The parity-colour clause: a valid token of the block colour working for
pair `b` is correct, given soundness, kinematics, `FreshPay` and a
covered-fresh window at `k = root + b psi`. -/
theorem q4_correct {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (G : GhostConfig n psi kappa) (hsound : GhostSound G)
    (hkin : Lemma4FreshKinematics ring (shiftRight ring root (b * psi)) G)
    (hF : FreshPay ring kind (shiftRight ring root (b * psi)) G)
    (hW : Lemma4CoveredFreshWindow ring (shiftRight ring root (b * psi)) kind G)
    (i : Fin n)
    (hVW : ValidToken kind G.phys i ∧ WorkingFor ring root G.phys i kind b) :
    CorrectToken ring root G.phys i kind b := by
  have hend := wc_blockEnd hpsi b hb
  have h2n : 2 * psi ≤ (b + 2) * psi := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨x, hx, hix⟩ := q4_host_window hpsi ring root b hb G.phys kind i hVW.2
  have hwin : Lemma4InWindow ring (shiftRight ring root (b * psi)) psi i := ⟨⟨x, hx⟩, hix⟩
  obtain ⟨z, hz⟩ := hW.2 i hwin hVW.1
  have hfr := hW.1 i z hwin hz
  have hs : tokenAt kind (G.phys i) = some z.value := by
    cases kind
    · exact (hsound.1 i z hz).1
    · exact (hsound.2 i z hz).1
  obtain ⟨x', hix', htraj⟩ := hkin kind i z hz hfr
  obtain ⟨hqlt, hpay⟩ := hF i z hz hfr
  unfold CorrectToken
  rw [hs]
  dsimp only
  refine ⟨?_, ?_⟩
  · rcases hpar with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
  generalize hcdef : decodeOffset psi (tokenCode z.value) = c at htraj ⊢
  rcases htraj with ⟨q, hc, hcle, hxq, hmv⟩ | ⟨q, hc, hcle, hxq, hmv⟩
  · -- right-moving: target `k + (q + psi)`
    have hqd : z.lmeta.moves / (2 * psi - 1) = q := by
      rw [hmv]; exact divq _ _ _ (by omega)
    rw [hqd] at hqlt hpay
    have htgt : tokenTargetSite ring i z.value =
        shiftRight ring (shiftRight ring root (b * psi)) (q + psi) := by
      unfold tokenTargetSite
      simp only [hcdef, hc, ↓reduceIte]
      rw [hix', l18Gapped_shiftRight_add]
      congr 1
      omega
    rw [htgt, l18Gapped_cyclicOffset_shiftRight_of_lt ring _ _ (by omega), if_pos hc]
    refine ⟨by omega, ?_⟩
    rw [show q + psi - psi = q by omega]
    exact ⟨hqlt, hpay⟩
  · -- left-moving: target `k + (q + 1)`
    have hqd : z.lmeta.moves / (2 * psi - 1) = q := by
      rw [hmv]; exact divq _ _ _ (by omega)
    rw [hqd] at hqlt hpay
    have hc' : ¬ (0 < c) := by omega
    have htgt : tokenTargetSite ring i z.value =
        shiftRight ring (shiftRight ring root (b * psi)) (q + 1) := by
      unfold tokenTargetSite
      simp only [hcdef, hc', ↓reduceIte]
      rw [hix', hxq, show q + c.natAbs + 1 = (q + 1) + c.natAbs by omega,
        ← l18Gapped_shiftRight_add]
      exact shiftLeft_shiftRight' ring _ _ (by omega)
    rw [htgt, l18Gapped_cyclicOffset_shiftRight_of_lt ring _ _ (by omega), if_neg hc']
    refine ⟨hc, by omega, ?_⟩
    rw [show q + 1 - 1 = q by omega]
    exact ⟨hqlt, hpay⟩

/-- The token half of pair `b` at a ghost state with the four ghost facts at
`k = root + b psi` for the parity colour, and `CDLAt` for the other colour. -/
theorem q4_tokenHalf_of_ghost {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (G : GhostConfig n psi kappa) (hsound : GhostSound G)
    (hkin : Lemma4FreshKinematics ring (shiftRight ring root (b * psi)) G)
    (hF : FreshPay ring kind (shiftRight ring root (b * psi)) G)
    (hW : Lemma4CoveredFreshWindow ring (shiftRight ring root (b * psi)) kind G)
    (hCDL : CDLAt ring root G.phys) :
    L18TokenHalfAt ring root G.phys b := by
  intro i
  have hwc := l18WrongColourClause hpsi ring root b hb G.phys hCDL i
  have hmain := q4_correct hpsi ring root b hb kind hpar G hsound hkin hF hW i
  rcases hpar with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨hmain, hwc.1 h⟩
  · exact ⟨hwc.2 h, hmain⟩

/-- **The half-word token row, unconditionally.**  From `Prefix b`, a prime
schedule containing block `b`'s half word leaves the token half of pair `b`
established (always the right disjunct). -/
theorem l18PrimeHalfWordTokenHalfRow_proved : L18PrimeHalfWordTokenHalfRow := by
  intro n psi kappa hn3 hpsi ring root b C pre hb hPrefix hsub
  right
  have hpar := q4_blockKind_par b
  have hgood := PPL.Lemma4Generic.primeGood_of_buildPrefix hn3 hpsi ring root b C hb hPrefix
  have hlt : psi < n := hgood.2.1
  have hhyb : PPL.Lemma4Generic.hybridRunner.run hpsi ring 0 (PPL.initialGhost C) pre =
      ghostRunPrime hpsi ring 0 (PPL.initialGhost C) pre :=
    PPL.Lemma4Generic.hybrid_run_eq_prime hpsi ring 0 (PPL.initialGhost C) pre hgood
  have hI : PPL.Lemma4Generic.HybridInv ring pre.length
      (ghostRunPrime hpsi ring 0 (PPL.initialGhost C) pre) := by
    rw [← hhyb]; exact PPL.Lemma4Generic.hybridInv_run hpsi ring C pre
  have hF := q4_run_freshPay hn3 hpsi ring root b hb _ hpar pre 0 (PPL.initialGhost C)
    hPrefix (PPL.Lemma4Generic.hybridInv_initial hpsi ring C)
    (q4_freshPay_initial ring _ _ C)
  have hPE : L18BuildPrefixAt ring root b (runPPrime ring C pre) :=
    l18PrimeRunPreservesBuildPrefix_of_white l18PrimeSelectedWhiteFrame_proved
      hn3 hpsi ring root b C pre hb hPrefix
  have hcdP : PPL.Lemma4Generic.primeRunner.cdTrace hpsi ring (shiftRight ring root (b * psi))
      (PPL.Lemma4Generic.l18BlockKind b) C pre :=
    PPL.Lemma4Generic.prime_cdTrace_of_prefix hn3 hpsi hlt ring root _ _ C pre
      ⟨hPrefix.1, fun i _ => hPrefix.2.1 i⟩
      (PPL.Lemma4Generic.cd_block_of_CDLAt hpsi ring root b C hb hPrefix.1)
  have hcdH := (PPL.Lemma4Generic.hybrid_cdTrace_iff_prime hpsi ring _ _ C pre hgood).2 hcdP
  have hW : Lemma4CoveredFreshWindow ring (shiftRight ring root (b * psi))
      (PPL.Lemma4Generic.l18BlockKind b)
      (ghostRunPrime hpsi ring 0 (PPL.initialGhost C) pre) := by
    rw [← hhyb]
    exact PPL.Lemma4Generic.halfPowerFirstPowerInduction_proved
      PPL.Lemma4Generic.hybridRunner
      PPL.Lemma4Generic.hybrid_runSound PPL.Lemma4Generic.hybrid_idsUniqueStep
      (PPL.Lemma4Generic.rankGeometryCorrected_of_serviceGeometry _
        PPL.Lemma4Generic.hybrid_serviceGeometry)
      PPL.Lemma4Generic.hybrid_coverageStep PPL.Lemma4Generic.hybrid_sweepMissingRows
      PPL.Lemma4Generic.hybrid_rightmostProgressStep
      PPL.Lemma4Generic.hybrid_oldOwnerProgressStep
      PPL.Lemma4Generic.hybrid_freshLineagePersistenceStep
      hpsi ring _ _ C pre hcdH hsub
  have hphys : (ghostRunPrime hpsi ring 0 (PPL.initialGhost C) pre).phys =
      runPPrime ring C pre :=
    ghostRunPrime_phys hpsi ring 0 (PPL.initialGhost C) pre
  have h := q4_tokenHalf_of_ghost hpsi ring root b hb _ hpar
    (ghostRunPrime hpsi ring 0 (PPL.initialGhost C) pre) hI.1 (hI.2.2.1 _) hF hW
    (by rw [hphys]; exact hPE.1)
  rw [hphys] at h
  exact h

/-- Establishment cut, token half, unconditionally. -/
theorem l18PrimeLemma4EstablishmentTokensAtCut_proved
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hsub :
      (PPL.lemma4Word ring
        (shiftRight ring root (b * psi)) psi).Sublist cut) :
    let E := runPPrime ring C cut
    l18HitsSPL ring root C cut = true ∨
      ∀ i : Fin n,
        ((ValidToken .black E i ∧ WorkingFor ring root E i .black b) →
            CorrectToken ring root E i .black b) ∧
          ((ValidToken .white E i ∧ WorkingFor ring root E i .white b) →
            CorrectToken ring root E i .white b) :=
  l18PrimeLemma4EstablishmentTokensAtCut_of_halfRow
    l18PrimeHalfWordTokenHalfRow_proved
    hn3 hpsi ring root b C cut hb hPrefix hsub

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q4_host_window
#print axioms PPL.Convergence.L18.q4_correct
#print axioms PPL.Convergence.L18.l18PrimeHalfWordTokenHalfRow_proved
#print axioms PPL.Convergence.L18.l18PrimeLemma4EstablishmentTokensAtCut_proved
