import Leader.PPL.Safety.SPLBlackOldImageSeams
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.TokenCorrectness.PersistenceClosed
import Init.Omega

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Convergence.L18

private theorem splBlackSemanticSourceClear_some
    {psi kappa : Nat}
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt .black (sourceClear .black q) = some t) :
    tokenAt .black q = some t ∧ l18Risk2LocalValid .black q t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : tokenAt .black q with
  | none =>
      simp only [hq] at h
      cases h
  | some u =>
      by_cases hv : l18Risk2LocalValid .black q u
      · simp only [hq, if_pos hv] at h
        have hut : u = t := Option.some.inj h
        subst u
        exact ⟨rfl, hv⟩
      · simp only [hq, if_neg hv] at h
        have hf : (none : Option (TokenData psi)) = some t := by
          simpa [l18Risk2SetToken, tokenAt] using h
        cases hf

private theorem splBlackSemanticSourceClear_id
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (sourceClear kind q).id = q.id := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem splBlackSemanticValid_of_clear
    {n psi kappa : Nat}
    (q : State psi kappa)
    (C : Config n psi kappa)
    (i : Fin n)
    (t : TokenData psi)
    (hdist : q.dist = (C i).dist)
    (hCtok : tokenAt .black (C i) = some t)
    (hclear :
      tokenAt .black (sourceClear .black q) = some t) :
    ValidToken .black C i := by
  have hs :=
    splBlackSemanticSourceClear_some q t hclear
  have hv := hs.2
  unfold l18Risk2LocalValid at hv
  unfold ValidToken
  rw [hCtok]
  dsimp only
  simpa [tokenTargetCoordinate, hdist] using hv

private theorem splBlackSemanticShiftLeft_shiftRight_sub
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d k : Nat)
    (hk : k <= d)
    (hd : d < n) :
    shiftLeft ring (shiftRight ring i d) k =
      shiftRight ring i (d - k) := by
  apply Fin.ext
  unfold shiftLeft shiftRight
  change
    (((i.val + d) % n + n - k % n) % n) =
      (i.val + (d - k)) % n
  have hklt : k < n :=
    Nat.lt_of_le_of_lt hk hd
  rw [Nat.mod_eq_of_lt hklt]
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - k =
          n + (i.val + (d - k)) := by
      omega
    rw [heq, Nat.add_mod_left]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - k =
          i.val + (d - k) := by
      omega
    rw [heq]

private theorem splBlackSemanticShiftLeft_shiftRight_cancel
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d : Nat)
    (hd : d < n) :
    shiftLeft ring (shiftRight ring i d) d = i := by
  rw [splBlackSemanticShiftLeft_shiftRight_sub
    ring i d d (Nat.le_refl _) hd]
  simp only [Nat.sub_self]
  exact l18Risk2ShiftRight_zero ring i

private theorem splBlackSemanticShiftLeftRightNeighborSucc
    {n : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (d : Nat) :
    shiftLeft ring e d =
      shiftLeft ring (ring.rightNeighbor e) (d + 1) := by
  apply Fin.ext
  simp only [shiftLeft, DirectedRing.rightNeighbor]
  have hn : 0 < n := ring.hn
  by_cases hn1 : n = 1
  · subst n
    simp
  have h1n : 1 < n := by
    omega
  have hd : d % n < n :=
    Nat.mod_lt _ hn
  have he : e.val < n :=
    e.isLt
  have hdSucc :
      (d + 1) % n =
        (d % n + 1) % n := by
    rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt h1n]
  rw [hdSucc]
  by_cases hd1 : d % n + 1 < n
  · rw [Nat.mod_eq_of_lt hd1]
    by_cases he1 : e.val + 1 < n
    · rw [Nat.mod_eq_of_lt he1]
      congr 1
      omega
    · have heq : e.val + 1 = n := by
        omega
      rw [heq, Nat.mod_self]
      have hA :
          e.val + n - d % n =
            n + (n - d % n - 1) := by
        omega
      have hB :
          n - (d % n + 1) =
            n - d % n - 1 := by
        omega
      have hk :
          n - d % n - 1 < n := by
        omega
      rw [hA]
      simp only [Nat.zero_add]
      rw [hB]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
  · have hdEq : d % n + 1 = n := by
      omega
    rw [hdEq, Nat.mod_self]
    have hdVal : d % n = n - 1 := by
      omega
    rw [hdVal]
    have hA :
        e.val + n - (n - 1) =
          e.val + 1 := by
      omega
    rw [hA]
    simp [Nat.add_mod]

private theorem splBlackSemanticInterior_two_end_lt
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (seg : Fin (segmentCount n psi - 2)) :
    (seg.val + 2) * psi < n := by
  have hz :
      seg.val + 3 <= segmentCount n psi := by
    have hs := seg.isLt
    omega
  unfold segmentCount at hz
  have hmul :
      (seg.val + 3) * psi <= n + psi - 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).mp hz
  simp [Nat.add_mul] at hmul ⊢
  omega

private theorem splBlackSemanticAddOneValid
    {psi : Nat}
    {c : Int}
    (hc : ValidOffset psi c)
    (hm2 : c <= -2) :
    ValidOffset psi (c + 1) := by
  rcases hc with hn | hp
  · left
    omega
  · exfalso
    omega

private def splBlackSemanticNegNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hc : ValidOffset psi c :=
    decodeOffset_valid psi (by omega) (tokenCode t)
  have hc' : ValidOffset psi (c + 1) :=
    splBlackSemanticAddOneValid hc hm2
  l18Risk2MkToken
    (encodeOffset psi (c + 1) hc')
    t.1.2 t.2

private theorem splBlackSemanticNegNext_decode
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    decodeOffset psi
        (tokenCode
          (splBlackSemanticNegNext hpsi t hm2)) =
      decodeOffset psi (tokenCode t) + 1 := by
  unfold splBlackSemanticNegNext
  dsimp only
  simp only [l18Risk2MkToken, tokenCode]
  rw [decode_encode]

private theorem splBlackSemanticNegNext_bit
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    tokenBitBool (splBlackSemanticNegNext hpsi t hm2) =
      tokenBitBool t := by
  unfold splBlackSemanticNegNext l18Risk2MkToken tokenBitBool
  rfl

private theorem splBlackSemanticNegNext_carry
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    tokenCarryBool (splBlackSemanticNegNext hpsi t hm2) =
      tokenCarryBool t := by
  unfold splBlackSemanticNegNext l18Risk2MkToken tokenCarryBool
  rfl

private theorem splBlackSemanticNatAbsAddOne
    (c : Int)
    (hc : c <= -2) :
    (c + 1).natAbs + 1 = c.natAbs := by
  cases c with
  | ofNat m =>
      omega
  | negSucc m =>
      cases m with
      | zero =>
          omega
      | succ m =>
          rfl

private theorem splBlackSemanticNegNext_target
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    tokenTargetSite ring e
        (splBlackSemanticNegNext hpsi t hm2) =
      tokenTargetSite ring (ring.rightNeighbor e) t := by
  let c : Int := decodeOffset psi (tokenCode t)
  have hc : c <= -2 := by
    simpa [c] using hm2
  have hnew :
      decodeOffset psi
          (tokenCode
            (splBlackSemanticNegNext hpsi t hm2)) =
        c + 1 := by
    simpa [c] using
      splBlackSemanticNegNext_decode hpsi t hm2
  have hneg : Not (0 < c) := by
    omega
  have hneg1 : Not (0 < c + 1) := by
    omega
  have habs :
      (c + 1).natAbs + 1 = c.natAbs :=
    splBlackSemanticNatAbsAddOne c hc
  unfold tokenTargetSite
  rw [hnew]
  have hold :
      decodeOffset psi (tokenCode t) = c := by
    rfl
  rw [hold]
  rw [if_neg hneg1, if_neg hneg]
  have hs :=
    splBlackSemanticShiftLeftRightNeighborSucc
      ring e (c + 1).natAbs
  rw [habs] at hs
  exact hs

private theorem splBlackSemanticNegTurn_eq_value
    {psi : Nat}
    (hpsi : 2 <= psi)
    (b : Bool)
    (t : TokenData psi) :
    l18Risk2NegTurnNext hpsi b t =
      remark2NegTurnValue hpsi b t := by
  rw [PPL.remark2NegTurnValue_eq_next]
  rfl

private theorem splBlackSemanticNegTurn_decode
    {psi : Nat}
    (hpsi : 2 <= psi)
    (b : Bool)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (remark2NegTurnValue hpsi b t)) =
      ((psi : Nat) : Int) := by
  rw [← splBlackSemanticNegTurn_eq_value hpsi b t]
  exact l18Risk2NegTurnNext_decode hpsi b t

private theorem splBlackSemanticNegTurn_target
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (b : Bool)
    (t : TokenData psi) :
    tokenTargetSite ring e
        (remark2NegTurnValue hpsi b t) =
      shiftRight ring e psi := by
  unfold tokenTargetSite
  rw [splBlackSemanticNegTurn_decode hpsi b t]
  rw [if_pos (by omega)]
  simp

private theorem splBlackSemanticTarget_neg_one
    {n psi : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hc :
      decodeOffset psi (tokenCode t) = (-1 : Int)) :
    tokenTargetSite ring (ring.rightNeighbor e) t = e := by
  unfold tokenTargetSite
  rw [hc]
  rw [if_neg (by omega)]
  change shiftLeft ring (ring.rightNeighbor e) 1 = e
  have hs :=
    splBlackSemanticShiftLeftRightNeighborSucc ring e 0
  rw [l18Gapped_shiftLeft_zero] at hs
  exact hs.symm

private theorem splBlackSemanticWorking_same_backward
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (i : Fin n)
    (kind : TokenKind)
    (seg : Nat)
    (t : TokenData psi)
    (ht : tokenAt kind (C i) = some t)
    (ht' : tokenAt kind (C' i) = some t)
    (hwork : WorkingFor ring root C' i kind seg) :
    WorkingFor ring root C i kind seg := by
  unfold WorkingFor at hwork ⊢
  rw [ht'] at hwork
  rw [ht]
  dsimp only at hwork ⊢
  exact hwork

private theorem splBlackSemanticWorkingNegative_backward
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (i j : Fin n)
    (kind : TokenKind)
    (seg : Nat)
    (t t' : TokenData psi)
    (ht : tokenAt kind (C i) = some t)
    (ht' : tokenAt kind (C' j) = some t')
    (hold : decodeOffset psi (tokenCode t) < 0)
    (hnew : decodeOffset psi (tokenCode t') < 0)
    (htarget :
      tokenTargetSite ring j t' =
        tokenTargetSite ring i t)
    (hwork : WorkingFor ring root C' j kind seg) :
    WorkingFor ring root C i kind seg := by
  unfold WorkingFor at hwork ⊢
  rw [ht'] at hwork
  rw [ht]
  dsimp only at hwork ⊢
  rcases hwork with ⟨hz, hp | hn⟩
  · have hf : False := by
      omega
    exact False.elim hf
  · have hin := hn.2
    rw [htarget] at hin
    exact ⟨hz, Or.inr ⟨hold, hin⟩⟩

private def splBlackSemanticResponderLeftValue
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    Option (TokenData psi) :=
  let c := decodeOffset psi (tokenCode t)
  if hm1 : c = -1 then
    some (l18Risk2NegTurnNext hpsi sourceBit t)
  else if hm2 : c <= -2 then
    some (splBlackSemanticNegNext hpsi t hm2)
  else
    none

private theorem splBlackSemanticResponderLeftValue_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate :
      (sourceClear .black l).last = false ∧
        (sourceClear .black r).last = false)
    (hsource :
      tokenAt .black (sourceClear .black r) = some t) :
    tokenAt .black
        (moveToken hpsi .black l r).1 =
      splBlackSemanticResponderLeftValue
        hpsi (sourceClear .black l).id t := by
  rw [← l18Risk2MoveTokenMirror_eq hpsi .black l r]
  unfold l18Risk2MoveTokenMirror
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte]
  cases hl :
      tokenAt .black (sourceClear .black l) with
  | none =>
      by_cases hdist :
          (sourceClear .black l).dist.val =
            tokenD' psi .black
      · by_cases h1 : decodeOffset psi (tokenCode t) = -1
        · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1]
        · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
          · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
          · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
      · by_cases h1 : decodeOffset psi (tokenCode t) = -1
        · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1]
        · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
          · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
          · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
  | some u =>
      by_cases h1 : decodeOffset psi (tokenCode t) = -1
      · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hsource, l18Risk2SourceSet_tokenAt, h1]
      · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
        · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
        · simp [splBlackSemanticResponderLeftValue, splBlackSemanticNegNext, hl, hsource, l18Risk2SourceSet_tokenAt, h1, h2]

private theorem splBlackSemanticResponderMoved_shape
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear .black l).last = false ∧
        (sourceClear .black r).last = false)
    (hsource :
      tokenAt .black (sourceClear .black r) = some t)
    (hq :
      tokenAt .black
          (moveToken hpsi .black l r).1 = some t') :
    (decodeOffset psi (tokenCode t) < 0 ∧
        decodeOffset psi (tokenCode t') < 0 ∧
        tokenTargetSite ring e t' =
          tokenTargetSite ring (ring.rightNeighbor e) t ∧
        tokenBitBool t' = tokenBitBool t ∧
        tokenCarryBool t' = tokenCarryBool t) ∨
      (decodeOffset psi (tokenCode t) = -1 ∧
        t' =
          remark2NegTurnValue
            hpsi (sourceClear .black l).id t) := by
  have hframe :=
    splBlackSemanticResponderLeftValue_eq
      hpsi l r t hgate hsource
  have hcanon :
      splBlackSemanticResponderLeftValue
          hpsi (sourceClear .black l).id t =
        some t' :=
    hframe.symm.trans hq
  by_cases hm1 :
      decodeOffset psi (tokenCode t) = -1
  · have heq :
        l18Risk2NegTurnNext
            hpsi (sourceClear .black l).id t =
          t' := by
      simpa
        [splBlackSemanticResponderLeftValue, hm1]
        using hcanon
    have hval :
        t' =
          remark2NegTurnValue
            hpsi (sourceClear .black l).id t := by
      calc
        t' =
            l18Risk2NegTurnNext
              hpsi (sourceClear .black l).id t :=
          heq.symm
        _ =
            remark2NegTurnValue
              hpsi (sourceClear .black l).id t :=
          splBlackSemanticNegTurn_eq_value
            hpsi (sourceClear .black l).id t
    exact Or.inr ⟨hm1, hval⟩
  · by_cases hm2 :
        decodeOffset psi (tokenCode t) <= -2
    · have heq :
          splBlackSemanticNegNext hpsi t hm2 = t' := by
        simpa
          [splBlackSemanticResponderLeftValue,
            hm1, hm2]
          using hcanon
      have hnew :
          decodeOffset psi (tokenCode t') < 0 := by
        calc
          decodeOffset psi (tokenCode t') =
              decodeOffset psi
                (tokenCode
                  (splBlackSemanticNegNext hpsi t hm2)) := by
            rw [heq]
          _ =
              decodeOffset psi (tokenCode t) + 1 :=
            splBlackSemanticNegNext_decode
              hpsi t hm2
          _ < 0 := by
            omega
      have htarget :
          tokenTargetSite ring e t' =
            tokenTargetSite ring (ring.rightNeighbor e) t := by
        calc
          tokenTargetSite ring e t' =
              tokenTargetSite ring e
                (splBlackSemanticNegNext hpsi t hm2) := by
            rw [heq]
          _ =
              tokenTargetSite ring (ring.rightNeighbor e) t :=
            splBlackSemanticNegNext_target
              hpsi ring e t hm2
      have hbit :
          tokenBitBool t' = tokenBitBool t := by
        calc
          tokenBitBool t' =
              tokenBitBool
                (splBlackSemanticNegNext hpsi t hm2) := by
            rw [heq]
          _ = tokenBitBool t :=
            splBlackSemanticNegNext_bit
              hpsi t hm2
      have hcarry :
          tokenCarryBool t' = tokenCarryBool t := by
        calc
          tokenCarryBool t' =
              tokenCarryBool
                (splBlackSemanticNegNext hpsi t hm2) := by
            rw [heq]
          _ = tokenCarryBool t :=
            splBlackSemanticNegNext_carry
              hpsi t hm2
      exact
        Or.inl
          ⟨by omega, hnew, htarget,
            hbit, hcarry⟩
    · have hf : False := by
        simpa
          [splBlackSemanticResponderLeftValue,
            hm1, hm2]
          using hcanon
      exact False.elim hf

private theorem splBlackSemanticClosedRight_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hsource :
      tokenAt .black (sourceClear .black r) = some t)
    (hgate :
      Not
        ((sourceClear .black l).last = false ∧
          (sourceClear .black r).last = false))
    (hq :
      tokenAt .black
          (moveToken hpsi .black l r).2 = some t') :
    t' = t := by
  have hframe :
      tokenAt .black
          (moveToken hpsi .black l r).2 =
        tokenAt .black (sourceClear .black r) := by
    rw [← l18Risk2MoveTokenMirror_eq hpsi .black l r]
    simp [l18Risk2MoveTokenMirror, hgate]
  have hs : some t' = some t := by
    calc
      some t' =
          tokenAt .black
            (moveToken hpsi .black l r).2 :=
        hq.symm
      _ =
          tokenAt .black (sourceClear .black r) :=
        hframe
      _ = some t := hsource
  exact Option.some.inj hs

private theorem splBlackSemanticOpenRight_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear .black l).last = false ∧
        (sourceClear .black r).last = false)
    (hsource :
      tokenAt .black (sourceClear .black r) = some t)
    (hq :
      tokenAt .black
          (moveToken hpsi .black l r).2 = some t') :
    t' = t := by
  rw [← l18Risk2MoveTokenMirror_eq hpsi .black l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq
  cases hl :
      tokenAt .black (sourceClear .black l) with
  | none =>
      by_cases hdist :
          (sourceClear .black l).dist.val =
            tokenD' psi .black
      · by_cases hm1 :
            decodeOffset psi (tokenCode t) = -1
        · have hf : False := by
            simpa
              [hl, hdist, hsource, hm1,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · by_cases hm2 :
              decodeOffset psi (tokenCode t) <= -2
          · have hf : False := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact heq.symm
      · by_cases hm1 :
            decodeOffset psi (tokenCode t) = -1
        · have hf : False := by
            simpa
              [hl, hdist, hsource, hm1,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · by_cases hm2 :
              decodeOffset psi (tokenCode t) <= -2
          · have hf : False := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact heq.symm
  | some u =>
      by_cases hm1 :
          decodeOffset psi (tokenCode t) = -1
      · have hf : False := by
          simpa
            [hl, hsource, hm1,
              l18Risk2SourceSet_tokenAt]
            using hq
        exact False.elim hf
      · by_cases hm2 :
            decodeOffset psi (tokenCode t) <= -2
        · have hf : False := by
            simpa
              [hl, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · have heq : t = t' := by
            simpa
              [hl, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact heq.symm

private theorem splBlackSemanticNegTurn_working_backward
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t : TokenData psi)
    (ht :
      tokenAt .black (C (ring.rightNeighbor e)) =
        some t)
    (hc :
      decodeOffset psi (tokenCode t) = (-1 : Int))
    (hpost :
      tokenAt .black (C' e) =
        some (remark2NegTurnValue hpsi (C e).id t))
    (hworkPost :
      WorkingFor ring root C' e .black seg.val) :
    WorkingFor ring root C
      (ring.rightNeighbor e) .black seg.val := by
  let u := remark2NegTurnValue hpsi (C e).id t
  let target := tokenTargetSite ring e u
  let off := cyclicOffset ring root target

  have hfit :=
    splBlackSemanticInterior_two_end_lt hpsi seg
  have hpsiN : psi < n := by
    have hle : 1 * psi ≤ (seg.val + 2) * psi :=
      Nat.mul_le_mul_right psi (by omega)
    rw [Nat.one_mul] at hle
    omega
  have hdec :
      decodeOffset psi (tokenCode u) =
        ((psi : Nat) : Int) := by
    simpa [u] using
      splBlackSemanticNegTurn_decode
        hpsi (C e).id t
  have htarget :
      target = shiftRight ring e psi := by
    simpa [target, u] using
      splBlackSemanticNegTurn_target
        hpsi ring e (C e).id t

  have hidxlt :
      seg.val + 1 < segmentCount n psi := by
    have hs := seg.isLt
    omega
  have hidx :
      (seg.val + 1) % segmentCount n psi =
        seg.val + 1 :=
    Nat.mod_eq_of_lt hidxlt

  have hw := hworkPost
  unfold WorkingFor at hw
  rw [hpost] at hw
  dsimp only at hw
  have hin :
      InSegment ring root psi
        (seg.val + 1) target := by
    rcases hw.2 with hp | hn
    · have hin0 := hp.2
      simpa [target, u, hidx] using hin0
    · have hf : False := by
        rw [hdec] at hn
        omega
      exact False.elim hf

  have hin0 := hin
  unfold InSegment at hin0
  dsimp only at hin0
  have hlo :
      (seg.val + 1) * psi <= off := by
    simpa [off] using hin0.1
  have hupp :
      off < (seg.val + 1 + 1) * psi := by
    exact
      Nat.lt_of_lt_of_le hin0.2
        (Nat.min_le_left _ _)
  have hoffN : off < n := by
    exact
      Nat.lt_of_lt_of_le hin0.2
        (Nat.min_le_right _ _)

  have hrootTarget :
      shiftRight ring root off = target := by
    dsimp only [off]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root target

  have heBack :
      shiftLeft ring target psi = e := by
    rw [htarget]
    exact
      splBlackSemanticShiftLeft_shiftRight_cancel
        ring e psi hpsiN

  have hpsiOff : psi <= off := by
    have hl := hlo
    simp only [Nat.add_mul, Nat.one_mul] at hl
    omega

  have heSite :
      e = shiftRight ring root (off - psi) := by
    calc
      e = shiftLeft ring target psi :=
        heBack.symm
      _ =
          shiftLeft ring
            (shiftRight ring root off) psi := by
        rw [hrootTarget]
      _ =
          shiftRight ring root (off - psi) :=
        splBlackSemanticShiftLeft_shiftRight_sub
          ring root off psi hpsiOff hoffN

  have hoffE :
      cyclicOffset ring root e = off - psi := by
    rw [heSite]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root (off - psi) (by omega)

  have hinE :
      InSegment ring root psi seg.val e := by
    unfold InSegment
    dsimp only
    rw [hoffE]
    constructor
    · have hl := hlo
      simp only [Nat.add_mul, Nat.one_mul] at hl
      omega
    · apply Nat.lt_min.mpr
      constructor
      · have hu := hupp
        simp only [Nat.add_mul, Nat.one_mul] at hu ⊢
        omega
      · omega

  unfold WorkingFor
  rw [ht]
  dsimp only
  rw [hc]
  refine ⟨hw.1, Or.inr ⟨by omega, ?_⟩⟩
  have hold :
      tokenTargetSite ring (ring.rightNeighbor e) t = e :=
    splBlackSemanticTarget_neg_one ring e t hc
  rw [hold]
  exact hinE

theorem splBlackOldImageResponderSemanticRow_proved :
    SPLBlackOldImageResponderSemanticRow := by
  unfold SPLBlackOldImageResponderSemanticRow
  intro _hMirror
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t t'
  dsimp only
  intro hCtok hr0tok hshape hpost hVW

  let rsite := ring.rightNeighbor e
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C rsite)

  have hrow :=
    splAlgorithm2DistWriteIdempotent
      hn3 hpsi ring root C e hSPL
  dsimp only at hrow
  have hpRDist :
      p.2.dist = (C rsite).dist := by
    simpa [p, rsite] using hrow.2.2.2.2.1
  have hpLId :
      p.1.id = (C e).id := by
    simpa [p, rsite] using hrow.2.2.2.2.2.1

  have hr0 :
      tokenAt .black
          (sourceClear .black p.2) = some t := by
    simpa [p, rsite] using hr0tok

  have hvalidPre :
      ValidToken .black C rsite :=
    splBlackSemanticValid_of_clear
      p.2 C rsite t hpRDist hCtok hr0

  have hclearId :
      (sourceClear .black p.1).id = (C e).id := by
    calc
      (sourceClear .black p.1).id = p.1.id :=
        splBlackSemanticSourceClear_id .black p.1
      _ = (C e).id := hpLId

  rcases hshape with hclosed | hopen
  · rcases hclosed with
      ⟨hgate, hir, hq⟩
    subst i

    have hgate' :
        Not
          ((sourceClear .black p.1).last = false ∧
            (sourceClear .black p.2).last = false) := by
      simpa [p, rsite] using hgate
    have hq' :
        tokenAt .black
            (moveToken hpsi .black p.1 p.2).2 =
          some t' := by
      simpa [p, rsite] using hq
    have htt :
        t' = t :=
      splBlackSemanticClosedRight_same
        hpsi p.1 p.2 t t' hr0 hgate' hq'
    have hpostT :
        tokenAt .black
            ((nextConfig ring C e) rsite) =
          some t := by
      rw [← htt]
      exact hpost
    have hworkPre :
        WorkingFor ring root C rsite .black seg.val :=
      splBlackSemanticWorking_same_backward
        ring root
        C (nextConfig ring C e)
        rsite .black seg.val t
        hCtok hpostT hVW.2
    exact
      ⟨hvalidPre, hworkPre,
        Or.inl ⟨rfl, htt⟩⟩

  · rcases hopen with ⟨hgate, hwhere⟩
    have hgate' :
        (sourceClear .black p.1).last = false ∧
          (sourceClear .black p.2).last = false := by
      simpa [p, rsite] using hgate

    rcases hwhere with hleft | hright
    · rcases hleft with ⟨hie, hq⟩
      subst i
      have hq' :
          tokenAt .black
              (moveToken hpsi .black p.1 p.2).1 =
            some t' := by
        simpa [p, rsite] using hq
      have hcases :=
        splBlackSemanticResponderMoved_shape
          hpsi ring e p.1 p.2 t t'
          hgate' hr0 hq'
      rcases hcases with hord | hturn
      · rcases hord with
          ⟨holdNeg, hnewNeg, htarget,
            hbit, hcarry⟩
        have hworkPre :
            WorkingFor ring root C rsite
              .black seg.val :=
          splBlackSemanticWorkingNegative_backward
            ring root
            C (nextConfig ring C e)
            rsite e .black seg.val t t'
            hCtok hpost
            holdNeg hnewNeg htarget
            hVW.2
        exact
          ⟨hvalidPre, hworkPre,
            Or.inr
              (Or.inl
                ⟨rfl, holdNeg, hnewNeg,
                  htarget, hbit, hcarry⟩)⟩
      · rcases hturn with ⟨hcneg, hval0⟩
        have hval :
            t' =
              remark2NegTurnValue
                hpsi (C e).id t := by
          rw [← hclearId]
          exact hval0
        have hpostTurn :
            tokenAt .black
                ((nextConfig ring C e) e) =
              some
                (remark2NegTurnValue
                  hpsi (C e).id t) := by
          rw [← hval]
          exact hpost
        have hworkPre :
            WorkingFor ring root C rsite
              .black seg.val :=
          splBlackSemanticNegTurn_working_backward
            hpsi ring root
            C (nextConfig ring C e)
            e seg t hCtok hcneg
            hpostTurn hVW.2
        exact
          ⟨hvalidPre, hworkPre,
            Or.inr
              (Or.inr
                ⟨rfl, hcneg, hval⟩)⟩

    · rcases hright with ⟨hir, hq⟩
      subst i
      have hq' :
          tokenAt .black
              (moveToken hpsi .black p.1 p.2).2 =
            some t' := by
        simpa [p, rsite] using hq
      have htt :
          t' = t :=
        splBlackSemanticOpenRight_same
          hpsi p.1 p.2 t t'
          hgate' hr0 hq'
      have hpostT :
          tokenAt .black
              ((nextConfig ring C e) rsite) =
            some t := by
        rw [← htt]
        exact hpost
      have hworkPre :
          WorkingFor ring root C rsite
            .black seg.val :=
        splBlackSemanticWorking_same_backward
          ring root
          C (nextConfig ring C e)
          rsite .black seg.val t
          hCtok hpostT hVW.2
      exact
        ⟨hvalidPre, hworkPre,
          Or.inl ⟨rfl, htt⟩⟩


end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splBlackOldImageResponderSemanticRow_proved
