import Leader.PPL.CompletionRunner.HybridRightmost
import Leader.PPL.CompletionRunner.Core
import Leader.PPL.SPLEntry.BuildGappedAssembly
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.SPLEntry.RiskyFlushScoped

/-!
# Step-parametric Lemma 4: the P_PL-prime deterministic core

1. `hybrid_deterministicCore : DeterministicCore hybridRunner`, from the
   generic headline `deterministicCore_of_steps` and the eight hybrid
   producers.
2. `prime_deterministicCore_of_good`: for every `PrimeGood` start, the prime
   ghost run `ghostRunPrime` along a prime `C_d` trace containing
   `H^(2 psi)` as a subsequence logs a fresh completion born at `k`.
3. `C_d` along CDLAt runs: `Cd` reads only `dist`/`last`, which `CDLAt` pins
   to canonical values, so `Cd` transfers between any two configurations that
   are `CDLAt` at the same root (`cd_transfer_of_CDLAt`); along a prime run
   from `L18RiskySweepPrefix2 … psi`, CDLAt is preserved at every letter, so a
   single `Cd` at the start gives the whole prime `C_d` trace
   (`prime_cdTrace_of_prefix`).  Hence `prime_deterministicCore_of_prefix`
   needs `Cd` only at the start.
4. The L18 block window: under `CDLAt`, block `b < l18BlockCount n psi` based
   at `root + b psi` satisfies `Cd` for the parity colour `l18BlockKind b`
   (`cd_block_of_CDLAt`).  With `L18BuildPrefixAt ring root b C`
   (`primeGood_of_buildPrefix`) this gives
   `prime_blockCompletion_of_buildPrefix`: the prime ghost run through any
   schedule containing that block's `lemma4Word` logs a fresh completion born
   at the block border.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 1. The hybrid and prime cores -/

theorem hybrid_deterministicCore : DeterministicCore hybridRunner :=
  deterministicCore_of_steps hybridRunner
    hybrid_runSound hybrid_idsUniqueStep hybrid_coverageStep
    hybrid_sweepMissingRows hybrid_rightmostProgressStep
    hybrid_oldOwnerProgressStep hybrid_freshLineagePersistenceStep
    hybrid_serviceGeometry

/-- Prime Lemma-4 deterministic core from a `PrimeGood` start. -/
theorem prime_deterministicCore_of_good {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (schedule : DetSchedule n)
    (hgood : PrimeGood ring C)
    (hCd : primeRunner.cdTrace hpsi ring k kind C schedule)
    (hsub : (lemma4Word ring k psi).Sublist schedule) :
    HasFreshCompletion kind k (ghostRunPrime hpsi ring 0 (initialGhost C) schedule) := by
  have hCdH : hybridRunner.cdTrace hpsi ring k kind C schedule :=
    (hybrid_cdTrace_iff_prime hpsi ring k kind C schedule hgood).2 hCd
  have h := hybrid_deterministicCore hpsi ring k kind C schedule hCdH hsub
  rw [hybrid_run_eq_prime hpsi ring 0 (initialGhost C) schedule hgood] at h
  exact h

/-! ## 2. `C_d` along CDLAt runs -/

/-- `Cd` transfers between two configurations that are `CDLAt` at the same
root. -/
theorem cd_transfer_of_CDLAt {n psi kappa : Nat} (ring : DirectedRing n)
    (root k : Fin n) (kind : TokenKind) (C C' : Config n psi kappa)
    (hC : CDLAt ring root C) (hC' : CDLAt ring root C') (hCd : Cd ring k kind C) :
    Cd ring k kind C' := by
  intro x
  have h := hCd x
  dsimp only at h ⊢
  have ha := hC.2.2 (shiftRight ring k x.val)
  have ha' := hC'.2.2 (shiftRight ring k x.val)
  dsimp only at ha ha'
  refine ⟨?_, ?_⟩
  · rw [ha'.1, ← ha.1]
    exact h.1
  · cases hl : (C' (shiftRight ring k x.val)).last with
    | false => rfl
    | true =>
        have hcond := ha'.2.1 hl
        have := ha.2.2 hcond
        rw [h.2] at this
        cases this

/-- Along a prime run from `L18RiskySweepPrefix2 … psi`, one `Cd` at the start
gives the whole prime `C_d` trace. -/
theorem prime_cdTrace_of_prefix {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (hlt : psi < n) (ring : DirectedRing n) (root k : Fin n) (kind : TokenKind) :
    ∀ (C : Config n psi kappa) (schedule : DetSchedule n),
      L18RiskySweepPrefix2 ring root psi C →
      Cd ring k kind C →
      primeRunner.cdTrace hpsi ring k kind C schedule := by
  intro C schedule
  induction schedule generalizing C with
  | nil =>
      intro _ hCd
      exact hCd
  | cons e es ih =>
      intro hpref hCd
      have hpref' := l18GappedRiskyInsertedStepRow_proved hn3 hpsi hlt ring root psi
        C e (Nat.le_refl psi) hpref
      exact ⟨hCd, ih (pprimeStep ring C e) hpref'
        (cd_transfer_of_CDLAt ring root k kind C _ hpref.1 hpref'.1 hCd)⟩

/-- Prime core needing `Cd` only at the start. -/
theorem prime_deterministicCore_of_prefix {n psi kappa : Nat} (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) (hlt : psi < n) (ring : DirectedRing n) (root k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) (schedule : DetSchedule n)
    (hpref : L18RiskySweepPrefix2 ring root psi C)
    (hCd : Cd ring k kind C)
    (hsub : (lemma4Word ring k psi).Sublist schedule) :
    HasFreshCompletion kind k (ghostRunPrime hpsi ring 0 (initialGhost C) schedule) :=
  prime_deterministicCore_of_good hpsi ring k kind C schedule ⟨hn3, hlt, root, hpref⟩
    (prime_cdTrace_of_prefix hn3 hpsi hlt ring root k kind C schedule hpref hCd) hsub

/-! ## 3. The L18 block window -/

/-- The parity colour of block `b` (black on even blocks). -/
def l18BlockKind (b : Nat) : TokenKind :=
  if b % 2 = 0 then .black else .white

theorem shiftRight_shiftRight {n : Nat} (ring : DirectedRing n) (i : Fin n)
    (a c : Nat) :
    shiftRight ring (shiftRight ring i a) c = shiftRight ring i (a + c) := by
  apply Fin.ext
  show ((i.val + a) % n + c) % n = (i.val + (a + c)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Under `CDLAt`, block `b` based at `root + b psi` satisfies `Cd` for its
parity colour. -/
theorem cd_block_of_CDLAt {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (C : Config n psi kappa)
    (hb : b < l18BlockCount n psi) (hC : CDLAt ring root C) :
    Cd ring (shiftRight ring root (b * psi)) (l18BlockKind b) C := by
  intro x
  have hx := x.isLt
  dsimp only
  rw [shiftRight_shiftRight]
  -- arithmetic of the block position
  have hzeta : b + 3 ≤ segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  have hdiv : segmentCount n psi * psi ≤ n + psi - 1 := by
    unfold segmentCount
    exact Nat.div_mul_le_self _ _
  have hmono : (b + 3) * psi ≤ segmentCount n psi * psi :=
    Nat.mul_le_mul_right psi hzeta
  have hexp : (b + 3) * psi = b * psi + 3 * psi := Nat.add_mul b 3 psi
  have hlast_eq : psi * (segmentCount n psi - 1) = segmentCount n psi * psi - psi := by
    rw [Nat.mul_sub_one, Nat.mul_comm]
  have hoff_lt : b * psi + x.val < n := by
    omega
  have hoff : cyclicOffset ring root (shiftRight ring root (b * psi + x.val)) =
      b * psi + x.val :=
    l18Gapped_cyclicOffset_shiftRight_of_lt ring root _ hoff_lt
  have ha := hC.2.2 (shiftRight ring root (b * psi + x.val))
  dsimp only at ha
  rw [hoff] at ha
  refine ⟨?_, ?_⟩
  · rw [ha.1]
    have hbm : b * psi % (2 * psi) = (if b % 2 = 0 then 0 else psi) := by
      rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
      · rw [if_pos h0]
        obtain ⟨m, hm⟩ : ∃ m, b = 2 * m := ⟨b / 2, by omega⟩
        rw [hm, show 2 * m * psi = (2 * psi) * m by
          rw [Nat.mul_assoc, Nat.mul_comm m psi, ← Nat.mul_assoc]]
        exact Nat.mul_mod_right _ _
      · rw [if_neg (by omega)]
        obtain ⟨m, hm⟩ : ∃ m, b = 2 * m + 1 := ⟨b / 2, by omega⟩
        rw [hm, Nat.add_mul, Nat.one_mul, show 2 * m * psi = (2 * psi) * m by
          rw [Nat.mul_assoc, Nat.mul_comm m psi, ← Nat.mul_assoc],
          Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
    unfold l18BlockKind
    rw [Nat.add_mod, hbm]
    rcases Nat.mod_two_eq_zero_or_one b with h0 | h1
    · rw [if_pos h0, if_pos h0]
      simp [tokenD']
    · rw [if_neg (by omega), if_neg (by omega)]
      show (psi + x.val % (2 * psi)) % (2 * psi) = (x.val + psi) % (2 * psi)
      rw [Nat.mod_eq_of_lt hx, Nat.add_comm]
  · cases hl : (C (shiftRight ring root (b * psi + x.val))).last with
    | false => rfl
    | true =>
        have hcond := ha.2.1 hl
        exfalso
        omega

/-- `L18BuildPrefixAt` at block `b` gives `PrimeGood`. -/
theorem primeGood_of_buildPrefix {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (C : Config n psi kappa)
    (hb : b < l18BlockCount n psi) (hP : L18BuildPrefixAt ring root b C) :
    PrimeGood ring C := by
  have hseg : 2 ≤ segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  have hlt : psi < n := (two_le_segmentCount_iff_psi_lt_n hpsi).1 hseg
  exact ⟨hn3, hlt, root, hP.1, fun i _ => hP.2.1 i⟩

/-- The Lemma-4 input of the L18 pair row: from `L18BuildPrefixAt ring root b C`,
any schedule containing block `b`'s `lemma4Word` makes the prime ghost run log
a fresh completion of colour `l18BlockKind b` born at the block border. -/
theorem prime_blockCompletion_of_buildPrefix {n psi kappa : Nat} (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (schedule : DetSchedule n)
    (hb : b < l18BlockCount n psi) (hP : L18BuildPrefixAt ring root b C)
    (hsub : (lemma4Word ring (shiftRight ring root (b * psi)) psi).Sublist schedule) :
    HasFreshCompletion (l18BlockKind b) (shiftRight ring root (b * psi))
      (ghostRunPrime hpsi ring 0 (initialGhost C) schedule) := by
  obtain ⟨_, hlt, root', hpref⟩ := primeGood_of_buildPrefix hn3 hpsi ring root b C hb hP
  have hpref0 : L18RiskySweepPrefix2 ring root psi C := ⟨hP.1, fun i _ => hP.2.1 i⟩
  exact prime_deterministicCore_of_prefix hn3 hpsi hlt ring root _ _ C schedule hpref0
    (cd_block_of_CDLAt hpsi ring root b C hb hP.1) hsub

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.hybrid_deterministicCore
#print axioms PPL.Lemma4Generic.prime_deterministicCore_of_good
#print axioms PPL.Lemma4Generic.prime_deterministicCore_of_prefix
#print axioms PPL.Lemma4Generic.cd_block_of_CDLAt
#print axioms PPL.Lemma4Generic.prime_blockCompletion_of_buildPrefix
