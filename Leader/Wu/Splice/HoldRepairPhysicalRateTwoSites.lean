import Leader.Wu.Splice.HoldRepairPhysicalRate

set_option autoImplicit false
set_option Elab.async false

/-! # V10j physical-service rate on every ring with `n ≥ 2`

`psiJ_drop_two`: on the two-site ring the amortized potential still drops at every non-physical change (the two edge
terms are the served edge and its reverse, and `row_amortized` keeps the reverse bonus); `psiJ_drop_ge_two` joins it
with `B9SpliceV10jAmortizedChain.psiJ_drop`.  `block_escape_of_mass` is the weighted escape of one block from any
progress mass `n^L ≤ Q * wordSum n L progressBitG`, with factor `(2Q-1)/2Q`.  On two sites the three-letter word
`e e e` realizes the three-service global progress, so `n^3 ≤ 8 * wordSum n 3 progressBitG` (`progress_mass_two`),
the block factor is `15/16`, and at most half of the words of length `3 * 165` avoid physical services
(`noPhysical_two_half`).  With `B9SpliceV10jPhysicalRate.noPhysical_one_over_n` for `n ≥ 3`, a physical V10j service
follows within `O(n^2)` letters with failure at most `1/n` on every ring with `n ≥ 2`. -/

namespace B9SpliceV10jPhysicalRateAll

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10g B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency
  B9SpliceV10ePairWeight B9SpliceLocalStepMass B9SpliceV10jGlobalProgress B9SpliceV10jProgressMass
  B9SpliceV10jAmortizedPotential B9SpliceV10jAmortizedChain BirthLeaderlessBirthMassRenewal
  B9SpliceV10jPhysicalRate FixedSpanRenewalPayload

variable {n psi width kappa tau : Nat}

/-! ## The potential on two sites -/

theorem fin_two_cases (hn : n = 2) (ring : DirectedRing n) (e i : Fin n) : i = e ∨ i = ring.rightNeighbor e := by
  subst hn
  have he := e.isLt
  have hi := i.isLt
  by_cases h : i = e
  · exact Or.inl h
  · right
    apply Fin.ext
    simp only [DirectedRing.rightNeighbor]
    have hne : i.val ≠ e.val := fun hv => h (Fin.ext hv)
    by_cases h0 : e.val = 0
    · rw [h0]; omega
    · have h1 : e.val = 1 := by omega
      rw [h1]; omega

theorem rn_rn_two (hn : n = 2) (ring : DirectedRing n) (e : Fin n) : ring.rightNeighbor (ring.rightNeighbor e) = e := by
  subst hn
  apply Fin.ext
  simp only [DirectedRing.rightNeighbor]
  have he := e.isLt
  by_cases h0 : e.val = 0
  · rw [h0]
  · have h1 : e.val = 1 := by omega
    rw [h1]

theorem psiJ_drop_two (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : n = 2) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C)
    (e : Fin n)
    (hnp : ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e)
    (hch : stepV10j hpsi hwidth hle ring C e ≠ C) :
    PsiJ hpsi ring (stepV10j hpsi hwidth hle ring C e) < PsiJ hpsi ring C := by
  classical
  have hself := rightNeighbor_ne_of_two_le ring (by omega) e
  have hstep := stepV10j_eq_writeAt hpsi hwidth hle ring C e hself
  have hout := row_amortized hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) (hS.2.1 e) (hS.2.1 _)
  generalize rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = w at hstep hout
  rcases hout with hp | hsame | ⟨hlt, hf1, hf2⟩
  · exfalso
    apply hnp
    rw [hstep]
    have hw := physical_of_row hpsi hwidth hle ring C e hself (C e, C (ring.rightNeighbor e)) w hp
    rwa [B9SpliceV10hWholeStepSafe.writeAt_self] at hw
  · exfalso
    apply hch
    rw [hstep, hsame]
    exact B9SpliceV10hWholeStepSafe.writeAt_self ring C e
  · rw [hstep]
    unfold PsiJ
    apply ofFn_sum_two_lt _ _ e (ring.rightNeighbor e) (Ne.symm hself)
    · intro i hie hij
      rcases fin_two_cases hn ring e i with h | h
      · exact absurd h hie
      · exact absurd h hij
    · unfold edgeTermJ
      have hrr := rn_rn_two hn ring e
      rw [hrr, writeAt_e, writeAt_j ring C e w hself]
      have hb : bonusJ hpsi (C (ring.rightNeighbor e)) (C e) ≤ bonusJ hpsi w.2 w.1 := by
        rcases hf1 with h1 | h1
        · rcases hf2 with h2 | h2
          · rw [h1, h2]; exact Nat.le_refl _
          · rw [bonusJ_left_zero hpsi _ _ h2]; exact Nat.zero_le _
        · rw [bonusJ_right_zero hpsi _ _ h1]; exact Nat.zero_le _
      unfold LocalJ at hlt
      have := bonusJ_le hpsi (C (ring.rightNeighbor e)) (C e)
      have := bonusJ_le hpsi w.2 w.1
      omega

theorem psiJ_drop_ge_two (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C)
    (e : Fin n)
    (hnp : ¬ PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e)
    (hch : stepV10j hpsi hwidth hle ring C e ≠ C) :
    PsiJ hpsi ring (stepV10j hpsi hwidth hle ring C e) < PsiJ hpsi ring C := by
  by_cases h2 : n = 2
  · exact psiJ_drop_two hpsi hwidth hle ring h2 C hS e hnp hch
  · exact psiJ_drop hpsi hwidth hle ring (by omega) C hS e hnp hch

/-! ## Alive words, for `n ≥ 2` -/

theorem psi_along_alive2 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n) :
    ∀ (u : List (Fin n)) (x : R1ConfigV6 n psi kappa tau × Bool),
      AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u →
        serveWordG (stepV10j hpsi hwidth hle ring) u x.1 = x.1 ∨
          PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) < PsiJ hpsi ring x.1
  | [], _, _ => Or.inl rfl
  | e :: u, x, h => by
      classical
      have hx := aliveAlong_good (step := stepF hpsi hwidth hle ring) (Good := GoodF hpsi ring) h
      have hg := aliveAlong_good (step := stepF hpsi hwidth hle ring) (Good := GoodF hpsi ring) h.2
      have hnp := not_physical_of_good_step hpsi hwidth hle ring x e hg
      have ih := psi_along_alive2 hpsi hwidth hle ring hn u _ h.2
      show serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring x.1 e) = x.1 ∨
        PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u (stepV10j hpsi hwidth hle ring x.1 e)) <
          PsiJ hpsi ring x.1
      by_cases hch : stepV10j hpsi hwidth hle ring x.1 e = x.1
      · have ih' := ih
        simp only [stepF, hch] at ih'
        rw [hch]
        exact ih'
      · right
        have hd := psiJ_drop_ge_two hpsi hwidth hle ring hn x.1 hx.2 e hnp hch
        rcases ih with h1 | h1
        · simp only [stepF] at h1
          rw [h1]; exact hd
        · simp only [stepF] at h1
          omega

theorem psi_le_along_alive2 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n) (u : List (Fin n)) (x : R1ConfigV6 n psi kappa tau × Bool)
    (h : AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u) :
    PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) ≤ PsiJ hpsi ring x.1 := by
  rcases psi_along_alive2 hpsi hwidth hle ring hn u x h with h1 | h1
  · rw [h1]; exact Nat.le_refl _
  · exact Nat.le_of_lt h1

/-! ## One block from any progress mass -/

theorem block_escape_of_mass (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n) (L Q : Nat)
    (hmass : ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7g hpsi ring C →
      ∃ e : Fin n, n ^ L ≤ Q * wordSum n L (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e)) :
    WeightedEscape (stepF (kappa := kappa) (tau := tau) hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring)
      L (2 * Q - 1) (2 * Q) := by
  classical
  intro x hx
  obtain ⟨e, hm⟩ := hmass x.1 hx.2
  have hpoint : ∀ u : List (Fin n), u.length = L →
      2 * (aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u *
          2 ^ PsiJ hpsi ring (u.foldl (stepF hpsi hwidth hle ring) x).1) +
        2 ^ PsiJ hpsi ring x.1 * progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u ≤
      2 * 2 ^ PsiJ hpsi ring x.1 := by
    intro u _
    have hpb : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u ≤ 1 := by
      unfold progressBitG; split <;> omega
    by_cases hal : AliveAlong (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u
    · have hab : aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u = 1 := by
        unfold aliveBit; rw [if_pos hal]
      rw [hab, Nat.one_mul, stepF_fst]
      have hle1 := psi_le_along_alive2 hpsi hwidth hle ring hn u x hal
      by_cases hprog : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u = 1
      · rw [hprog, Nat.mul_one]
        have hdrop : PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) < PsiJ hpsi ring x.1 := by
          unfold progressBitG at hprog
          split at hprog
          · rename_i hc
            rcases hc with hc | ⟨w', ⟨t, ht⟩, hw⟩
            · have := physCount_zero_of_alive hpsi hwidth hle ring u x hal
              omega
            · subst ht
              have hal' := (aliveAlong_append (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x w' t).1 hal
              have hne : serveWordG (stepV10j hpsi hwidth hle ring) w' x.1 ≠ x.1 := by
                intro heq; rw [heq] at hw; exact Nat.lt_irrefl _ hw
              have h1 : PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) w' x.1) < PsiJ hpsi ring x.1 := by
                rcases psi_along_alive2 hpsi hwidth hle ring hn w' x hal'.1 with h | h
                · exact absurd h hne
                · exact h
              have h2 := psi_le_along_alive2 hpsi hwidth hle ring hn t _ hal'.2
              rw [stepF_fst] at h2
              rw [serveWordG_append]
              omega
          · omega
        have hp2 : 2 * 2 ^ PsiJ hpsi ring (serveWordG (stepV10j hpsi hwidth hle ring) u x.1) ≤
            2 ^ PsiJ hpsi ring x.1 := by
          have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hdrop)
          rw [Nat.pow_succ] at this
          omega
        omega
      · have hp0 : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u = 0 := by omega
        rw [hp0, Nat.mul_zero, Nat.add_zero]
        exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hle1)
    · have hab : aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u = 0 := by
        unfold aliveBit; rw [if_neg hal]
      rw [hab, Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
      calc 2 ^ PsiJ hpsi ring x.1 * progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e u
          ≤ 2 ^ PsiJ hpsi ring x.1 * 1 := Nat.mul_le_mul_left _ hpb
        _ ≤ 2 * 2 ^ PsiJ hpsi ring x.1 := by omega
  have hsum := wordSum_mono_len _ _ hpoint
  rw [wordSum_add', wordSum_mul_l, wordSum_mul_l, wordSum_const'] at hsum
  -- hsum : 2 * A + 2^p * prog ≤ 2 * 2^p * n^L ;  hm : n^L ≤ Q * prog
  unfold weightedAlive WF
  generalize hA : wordSum n L (fun u => aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) x u *
    2 ^ PsiJ hpsi ring (u.foldl (stepF hpsi hwidth hle ring) x).1) = A at hsum ⊢
  generalize hPr : wordSum n L (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) x.1 e) = Pr at hsum hm
  generalize hZ : 2 ^ PsiJ hpsi ring x.1 = Z at hsum ⊢
  generalize hN : n ^ L = N at hsum hm ⊢
  -- from here: 2A + Z Pr ≤ 2 Z N and N ≤ Q Pr give 2 Q A ≤ (2Q - 1) Z N
  have h1 : Q * (2 * A + Z * Pr) ≤ Q * (2 * Z * N) := Nat.mul_le_mul_left Q hsum
  have h2 : Z * N ≤ Z * (Q * Pr) := Nat.mul_le_mul_left Z hm
  have e1 : Q * (2 * A + Z * Pr) = 2 * (Q * A) + Z * (Q * Pr) := by
    rw [Nat.mul_add]; congr 1 <;> ac_rfl
  have e2 : Q * (2 * Z * N) = 2 * (Q * (Z * N)) := by ac_rfl
  rw [e1, e2] at h1
  have e3 : (2 * Q - 1) * (Z * N) = 2 * (Q * (Z * N)) - Z * N := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_assoc]
  have e4 : 2 * Q * A = 2 * (Q * A) := Nat.mul_assoc 2 Q A
  rw [e3, e4]
  omega

/-! ## Two sites: three letters of one edge -/

theorem single_le_wordSum (f : List (Fin n) → Nat) : ∀ (u : List (Fin n)), f u ≤ wordSum n u.length f
  | [] => by simp [wordSum, allSchedules]
  | e :: u => by
      show f (e :: u) ≤ wordSum n (u.length + 1) f
      rw [wordSum_succ]
      have h1 := single_le_wordSum (fun v => f (e :: v)) u
      have h2 := B9SpliceTableV10d.ofFn_sum_split (fun _ : Fin n => 0)
        (fun e' : Fin n => wordSum n u.length (fun v => f (e' :: v))) e (fun _ _ => Nat.zero_le _)
      rw [FiniteUniformStoppingTree.ofFn_sum_const] at h2
      omega

theorem serveWordG_replicate (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (e : Fin n) : ∀ (k : Nat) (C : R1ConfigV6 n psi kappa tau),
      serveWordG (stepV10j hpsi hwidth hle ring) (List.replicate k e) C =
        serveIterG (stepV10j hpsi hwidth hle ring) e k C
  | 0, _ => rfl
  | k + 1, C => by
      show serveWordG (stepV10j hpsi hwidth hle ring) (List.replicate k e) (stepV10j hpsi hwidth hle ring C e) =
        serveIterG (stepV10j hpsi hwidth hle ring) e (k + 1) C
      rw [serveWordG_replicate hpsi hwidth hle ring e k, serveIterG_succ_comm]

theorem progress_mass_two (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : n = 2) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) :
    ∃ e : Fin n, n ^ 3 ≤ 8 * wordSum n 3 (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e) := by
  classical
  obtain ⟨e, m, hm, hp⟩ := progressWithin3_V10j hpsi hwidth hle ring (by omega) C hS
  refine ⟨e, ?_⟩
  have hbit : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e [e, e, e] = 1 := by
    unfold progressBitG
    rw [if_pos]
    rcases hp with hphys | hdrop
    · left
      have hsplit : [e, e, e] = List.replicate m e ++ ([e] ++ List.replicate (2 - m) e) := by
        rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h | h | h <;> subst h <;> rfl
      rw [hsplit, physCountG_append, physCountG_append]
      have h1 : physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) [e]
          (serveWordG (stepV10j hpsi hwidth hle ring) (List.replicate m e) C) = 1 := by
        rw [serveWordG_replicate, physCountG, physCountG,
          if_pos (show PhysicalServiceAt hpsi hwidth hle ring (serveIterG (stepV10j hpsi hwidth hle ring) e m C)
            (stepV10j hpsi hwidth hle ring (serveIterG (stepV10j hpsi hwidth hle ring) e m C) e) e from hphys)]
      rw [h1]
      omega
    · right
      refine ⟨List.replicate (m + 1) e, ⟨List.replicate (2 - m) e, ?_⟩, ?_⟩
      · rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h | h | h <;> subst h <;> rfl
      · rw [serveWordG_replicate]; exact hdrop
  have hle1 : progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e [e, e, e] ≤
      wordSum n 3 (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e) :=
    single_le_wordSum (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e) [e, e, e]
  rw [hbit] at hle1
  subst hn
  have h8 : (2 : Nat) ^ 3 = 8 := rfl
  rw [h8]
  omega

/-- On two sites at most half of the words of length `3 * 165` avoid physical services. -/
theorem noPhysical_two_half (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (hn : n = 2) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) :
    n * wordSum n (165 * 3) (noPhysBit hpsi hwidth hle ring C) ≤ n ^ (165 * 3) := by
  classical
  have hesc := block_escape_of_mass (kappa := kappa) (tau := tau) hpsi hwidth hle ring (by omega) 3 8
    (fun C' hS' => progress_mass_two hpsi hwidth hle ring hn C' hS')
  have ht := weighted_tail (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring) 3 15 16 hesc 165 (C, false)
    ⟨rfl, hS⟩
  have hmono : wordSum n (165 * 3) (noPhysBit hpsi hwidth hle ring C) ≤
      weightedAlive (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring) (C, false) (165 * 3) := by
    unfold weightedAlive
    apply wordSum_mono_len
    intro u _
    unfold noPhysBit
    split
    · rename_i h0
      have hal := alive_of_noPhys hpsi hwidth hle ring u C hS h0
      have hab : aliveBit (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (C, false) u = 1 := by
        unfold aliveBit; rw [if_pos hal]
      rw [hab, Nat.one_mul]
      exact Nat.one_le_two_pow
    · exact Nat.zero_le _
  have hW : WF hpsi ring (C, false) ≤ 2 ^ 14 := by
    have := PsiJ_le hpsi ring C
    subst hn
    exact Nat.pow_le_pow_right (by decide) this
  have hbase : 2 ^ 15 * 15 ^ 165 ≤ 16 ^ 165 := by decide
  subst hn
  have hpos : 0 < 16 ^ 165 := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc 16 ^ 165 * (2 * wordSum 2 (165 * 3) (noPhysBit hpsi hwidth hle ring C))
      = 2 * (16 ^ 165 * wordSum 2 (165 * 3) (noPhysBit hpsi hwidth hle ring C)) := Nat.mul_left_comm _ _ _
    _ ≤ 2 * (16 ^ 165 * weightedAlive (stepF hpsi hwidth hle ring) (GoodF hpsi ring) (WF hpsi ring) (C, false)
          (165 * 3)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hmono)
    _ ≤ 2 * (15 ^ 165 * (WF hpsi ring (C, false) * 2 ^ (165 * 3))) := Nat.mul_le_mul_left 2 ht
    _ ≤ 2 * (15 ^ 165 * (2 ^ 14 * 2 ^ (165 * 3))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hW))
    _ = (2 ^ 15 * 15 ^ 165) * 2 ^ (165 * 3) := by
        rw [show (2 : Nat) ^ 15 = 2 * 2 ^ 14 from rfl, Nat.mul_left_comm (15 ^ 165) (2 ^ 14),
          ← Nat.mul_assoc 2 (2 ^ 14), ← Nat.mul_assoc (2 * 2 ^ 14)]
    _ ≤ 16 ^ 165 * 2 ^ (165 * 3) := Nat.mul_le_mul_right _ hbase

end B9SpliceV10jPhysicalRateAll
