import Leader.PPL.Safety.SPLWhiteCorrectnessRoute
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.TokenCorrectness.PersistenceClosed
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Convergence.L18

private theorem splWhiteSemanticBlackPassLeftId
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    (moveToken hpsi .black l r).1.id = l.id := by
  have h :=
    congrArg
      (fun q : State psi kappa => q.id)
      (PPL.moveToken_initiator_fields
        hpsi .black l r)
  simpa [PPL.eraseKindToken] using h

private theorem splWhiteSemanticBlackPassRightDist
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    (moveToken hpsi .black l r).2.dist = r.dist := by
  rcases
      PPL.moveToken_responder_fields
        hpsi .black l r with h | h
  · have hd :=
      congrArg
        (fun q : State psi kappa => q.dist) h
    simpa
      [PPL.eraseKindTokenId, PPL.eraseKindToken]
      using hd
  · have hd :=
      congrArg
        (fun q : State psi kappa => q.dist) h
    simpa
      [PPL.eraseKindTokenId, PPL.eraseKindToken,
        PPL.birthFields]
      using hd

private theorem splWhiteSemanticSourceClear_some
    {psi kappa : Nat}
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt .white (sourceClear .white q) = some t) :
    tokenAt .white q = some t ∧ l18Risk2LocalValid .white q t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : tokenAt .white q with
  | none =>
      simp only [hq] at h
      cases h
  | some u =>
      by_cases hv : l18Risk2LocalValid .white q u
      · simp only [hq, if_pos hv] at h
        have hut : u = t := Option.some.inj h
        subst u
        exact ⟨rfl, hv⟩
      · simp only [hq, if_neg hv] at h
        have hf : (none : Option (TokenData psi)) = some t := by
          simpa [l18Risk2SetToken, tokenAt] using h
        cases hf

private theorem splWhiteSemanticSourceClear_id
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

private theorem splWhiteSemanticValid_of_clear
    {n psi kappa : Nat}
    (q : State psi kappa)
    (C : Config n psi kappa)
    (i : Fin n)
    (t : TokenData psi)
    (hdist : q.dist = (C i).dist)
    (hCtok : tokenAt .white (C i) = some t)
    (hclear :
      tokenAt .white (sourceClear .white q) = some t) :
    ValidToken .white C i := by
  have hs :=
    splWhiteSemanticSourceClear_some q t hclear
  have hv := hs.2
  unfold l18Risk2LocalValid at hv
  unfold ValidToken
  rw [hCtok]
  dsimp only
  simpa [tokenTargetCoordinate, hdist] using hv

private theorem splWhiteSemanticShiftLeft_shiftRight_sub
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

private theorem splWhiteSemanticShiftLeft_shiftRight_cancel
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d : Nat)
    (hd : d < n) :
    shiftLeft ring (shiftRight ring i d) d = i := by
  rw [splWhiteSemanticShiftLeft_shiftRight_sub
    ring i d d (Nat.le_refl _) hd]
  simp only [Nat.sub_self]
  exact l18Risk2ShiftRight_zero ring i

private theorem splWhiteSemanticShiftLeftRightNeighborSucc
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

private theorem splWhiteSemanticInterior_two_end_lt
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

private theorem splWhiteSemanticAddOneValid
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

private def splWhiteSemanticNegNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    TokenData psi :=
  let c := decodeOffset psi (tokenCode t)
  have hc : ValidOffset psi c :=
    decodeOffset_valid psi (by omega) (tokenCode t)
  have hc' : ValidOffset psi (c + 1) :=
    splWhiteSemanticAddOneValid hc hm2
  l18Risk2MkToken
    (encodeOffset psi (c + 1) hc')
    t.1.2 t.2

private theorem splWhiteSemanticNegNext_decode
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    decodeOffset psi
        (tokenCode
          (splWhiteSemanticNegNext hpsi t hm2)) =
      decodeOffset psi (tokenCode t) + 1 := by
  unfold splWhiteSemanticNegNext
  dsimp only
  simp only [l18Risk2MkToken, tokenCode]
  rw [decode_encode]

private theorem splWhiteSemanticNegNext_bit
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    tokenBitBool (splWhiteSemanticNegNext hpsi t hm2) =
      tokenBitBool t := by
  unfold splWhiteSemanticNegNext l18Risk2MkToken tokenBitBool
  rfl

private theorem splWhiteSemanticNegNext_carry
    {psi : Nat}
    (hpsi : 2 <= psi)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    tokenCarryBool (splWhiteSemanticNegNext hpsi t hm2) =
      tokenCarryBool t := by
  unfold splWhiteSemanticNegNext l18Risk2MkToken tokenCarryBool
  rfl

private theorem splWhiteSemanticNatAbsAddOne
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

private theorem splWhiteSemanticNegNext_target
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hm2 : decodeOffset psi (tokenCode t) <= -2) :
    tokenTargetSite ring e
        (splWhiteSemanticNegNext hpsi t hm2) =
      tokenTargetSite ring (ring.rightNeighbor e) t := by
  let c : Int := decodeOffset psi (tokenCode t)
  have hc : c <= -2 := by
    simpa [c] using hm2
  have hnew :
      decodeOffset psi
          (tokenCode
            (splWhiteSemanticNegNext hpsi t hm2)) =
        c + 1 := by
    simpa [c] using
      splWhiteSemanticNegNext_decode hpsi t hm2
  have hneg : Not (0 < c) := by
    omega
  have hneg1 : Not (0 < c + 1) := by
    omega
  have habs :
      (c + 1).natAbs + 1 = c.natAbs :=
    splWhiteSemanticNatAbsAddOne c hc
  unfold tokenTargetSite
  rw [hnew]
  have hold :
      decodeOffset psi (tokenCode t) = c := by
    rfl
  rw [hold]
  rw [if_neg hneg1, if_neg hneg]
  have hs :=
    splWhiteSemanticShiftLeftRightNeighborSucc
      ring e (c + 1).natAbs
  rw [habs] at hs
  exact hs

private theorem splWhiteSemanticNegTurn_eq_value
    {psi : Nat}
    (hpsi : 2 <= psi)
    (b : Bool)
    (t : TokenData psi) :
    l18Risk2NegTurnNext hpsi b t =
      remark2NegTurnValue hpsi b t := by
  rw [PPL.remark2NegTurnValue_eq_next]
  rfl

private theorem splWhiteSemanticNegTurn_decode
    {psi : Nat}
    (hpsi : 2 <= psi)
    (b : Bool)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (remark2NegTurnValue hpsi b t)) =
      ((psi : Nat) : Int) := by
  rw [← splWhiteSemanticNegTurn_eq_value hpsi b t]
  exact l18Risk2NegTurnNext_decode hpsi b t

private theorem splWhiteSemanticNegTurn_target
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
  rw [splWhiteSemanticNegTurn_decode hpsi b t]
  rw [if_pos (by omega)]
  simp

private theorem splWhiteSemanticTarget_neg_one
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
    splWhiteSemanticShiftLeftRightNeighborSucc ring e 0
  rw [l18Gapped_shiftLeft_zero] at hs
  exact hs.symm

private theorem splWhiteSemanticWorking_same_backward
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

private theorem splWhiteSemanticWorkingNegative_backward
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

private def splWhiteSemanticResponderLeftValue
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    Option (TokenData psi) :=
  let c := decodeOffset psi (tokenCode t)
  if hm1 : c = -1 then
    some (l18Risk2NegTurnNext hpsi sourceBit t)
  else if hm2 : c <= -2 then
    some (splWhiteSemanticNegNext hpsi t hm2)
  else
    none

private theorem splWhiteSemanticResponderLeftValue_eq
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hgate :
      (sourceClear .white l).last = false ∧
        (sourceClear .white r).last = false)
    (hsource :
      tokenAt .white (sourceClear .white r) = some t) :
    tokenAt .white
        (moveToken hpsi .white l r).1 =
      splWhiteSemanticResponderLeftValue
        hpsi (sourceClear .white l).id t := by
  rw [← l18Risk2MoveTokenMirror_eq hpsi .white l r]
  unfold l18Risk2MoveTokenMirror
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte]
  cases hl :
      tokenAt .white (sourceClear .white l) with
  | none =>
      by_cases hdist :
          (sourceClear .white l).dist.val =
            tokenD' psi .white
      · by_cases h1 : decodeOffset psi (tokenCode t) = -1
        · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1]
        · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
          · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
          · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
      · by_cases h1 : decodeOffset psi (tokenCode t) = -1
        · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1]
        · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
          · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
          · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hdist, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
  | some u =>
      by_cases h1 : decodeOffset psi (tokenCode t) = -1
      · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hsource, l18Risk2SourceSet_tokenAt, h1]
      · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
        · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hsource, l18Risk2SourceSet_tokenAt, h1, h2]
        · simp [splWhiteSemanticResponderLeftValue, splWhiteSemanticNegNext, hl, hsource, l18Risk2SourceSet_tokenAt, h1, h2]

private theorem splWhiteSemanticResponderMoved_shape
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear .white l).last = false ∧
        (sourceClear .white r).last = false)
    (hsource :
      tokenAt .white (sourceClear .white r) = some t)
    (hq :
      tokenAt .white
          (moveToken hpsi .white l r).1 = some t') :
    (decodeOffset psi (tokenCode t) < 0 ∧
        decodeOffset psi (tokenCode t') < 0 ∧
        tokenTargetSite ring e t' =
          tokenTargetSite ring (ring.rightNeighbor e) t ∧
        tokenBitBool t' = tokenBitBool t ∧
        tokenCarryBool t' = tokenCarryBool t) ∨
      (decodeOffset psi (tokenCode t) = -1 ∧
        t' =
          remark2NegTurnValue
            hpsi (sourceClear .white l).id t) := by
  have hframe :=
    splWhiteSemanticResponderLeftValue_eq
      hpsi l r t hgate hsource
  have hcanon :
      splWhiteSemanticResponderLeftValue
          hpsi (sourceClear .white l).id t =
        some t' :=
    hframe.symm.trans hq
  by_cases hm1 :
      decodeOffset psi (tokenCode t) = -1
  · have heq :
        l18Risk2NegTurnNext
            hpsi (sourceClear .white l).id t =
          t' := by
      simpa
        [splWhiteSemanticResponderLeftValue, hm1]
        using hcanon
    have hval :
        t' =
          remark2NegTurnValue
            hpsi (sourceClear .white l).id t := by
      calc
        t' =
            l18Risk2NegTurnNext
              hpsi (sourceClear .white l).id t :=
          heq.symm
        _ =
            remark2NegTurnValue
              hpsi (sourceClear .white l).id t :=
          splWhiteSemanticNegTurn_eq_value
            hpsi (sourceClear .white l).id t
    exact Or.inr ⟨hm1, hval⟩
  · by_cases hm2 :
        decodeOffset psi (tokenCode t) <= -2
    · have heq :
          splWhiteSemanticNegNext hpsi t hm2 = t' := by
        simpa
          [splWhiteSemanticResponderLeftValue,
            hm1, hm2]
          using hcanon
      have hnew :
          decodeOffset psi (tokenCode t') < 0 := by
        calc
          decodeOffset psi (tokenCode t') =
              decodeOffset psi
                (tokenCode
                  (splWhiteSemanticNegNext hpsi t hm2)) := by
            rw [heq]
          _ =
              decodeOffset psi (tokenCode t) + 1 :=
            splWhiteSemanticNegNext_decode
              hpsi t hm2
          _ < 0 := by
            omega
      have htarget :
          tokenTargetSite ring e t' =
            tokenTargetSite ring (ring.rightNeighbor e) t := by
        calc
          tokenTargetSite ring e t' =
              tokenTargetSite ring e
                (splWhiteSemanticNegNext hpsi t hm2) := by
            rw [heq]
          _ =
              tokenTargetSite ring (ring.rightNeighbor e) t :=
            splWhiteSemanticNegNext_target
              hpsi ring e t hm2
      have hbit :
          tokenBitBool t' = tokenBitBool t := by
        calc
          tokenBitBool t' =
              tokenBitBool
                (splWhiteSemanticNegNext hpsi t hm2) := by
            rw [heq]
          _ = tokenBitBool t :=
            splWhiteSemanticNegNext_bit
              hpsi t hm2
      have hcarry :
          tokenCarryBool t' = tokenCarryBool t := by
        calc
          tokenCarryBool t' =
              tokenCarryBool
                (splWhiteSemanticNegNext hpsi t hm2) := by
            rw [heq]
          _ = tokenCarryBool t :=
            splWhiteSemanticNegNext_carry
              hpsi t hm2
      exact
        Or.inl
          ⟨by omega, hnew, htarget,
            hbit, hcarry⟩
    · have hf : False := by
        simpa
          [splWhiteSemanticResponderLeftValue,
            hm1, hm2]
          using hcanon
      exact False.elim hf

private theorem splWhiteSemanticClosedRight_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hsource :
      tokenAt .white (sourceClear .white r) = some t)
    (hgate :
      Not
        ((sourceClear .white l).last = false ∧
          (sourceClear .white r).last = false))
    (hq :
      tokenAt .white
          (moveToken hpsi .white l r).2 = some t') :
    t' = t := by
  have hframe :
      tokenAt .white
          (moveToken hpsi .white l r).2 =
        tokenAt .white (sourceClear .white r) := by
    rw [← l18Risk2MoveTokenMirror_eq hpsi .white l r]
    simp [l18Risk2MoveTokenMirror, hgate]
  have hs : some t' = some t := by
    calc
      some t' =
          tokenAt .white
            (moveToken hpsi .white l r).2 :=
        hq.symm
      _ =
          tokenAt .white (sourceClear .white r) :=
        hframe
      _ = some t := hsource
  exact Option.some.inj hs

private theorem splWhiteSemanticOpenRight_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear .white l).last = false ∧
        (sourceClear .white r).last = false)
    (hsource :
      tokenAt .white (sourceClear .white r) = some t)
    (hq :
      tokenAt .white
          (moveToken hpsi .white l r).2 = some t') :
    t' = t := by
  rw [← l18Risk2MoveTokenMirror_eq hpsi .white l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq
  cases hl :
      tokenAt .white (sourceClear .white l) with
  | none =>
      by_cases hdist :
          (sourceClear .white l).dist.val =
            tokenD' psi .white
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

private theorem splWhiteSemanticNegTurn_working_backward
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C C' : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t : TokenData psi)
    (ht :
      tokenAt .white (C (ring.rightNeighbor e)) =
        some t)
    (hc :
      decodeOffset psi (tokenCode t) = (-1 : Int))
    (hpost :
      tokenAt .white (C' e) =
        some (remark2NegTurnValue hpsi (C e).id t))
    (hworkPost :
      WorkingFor ring root C' e .white seg.val) :
    WorkingFor ring root C
      (ring.rightNeighbor e) .white seg.val := by
  let u := remark2NegTurnValue hpsi (C e).id t
  let target := tokenTargetSite ring e u
  let off := cyclicOffset ring root target

  have hfit :=
    splWhiteSemanticInterior_two_end_lt hpsi seg
  have hpsiN : psi < n := by
    have hle : 1 * psi ≤ (seg.val + 2) * psi :=
      Nat.mul_le_mul_right psi (by omega)
    rw [Nat.one_mul] at hle
    omega
  have hdec :
      decodeOffset psi (tokenCode u) =
        ((psi : Nat) : Int) := by
    simpa [u] using
      splWhiteSemanticNegTurn_decode
        hpsi (C e).id t
  have htarget :
      target = shiftRight ring e psi := by
    simpa [target, u] using
      splWhiteSemanticNegTurn_target
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
      splWhiteSemanticShiftLeft_shiftRight_cancel
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
        splWhiteSemanticShiftLeft_shiftRight_sub
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
    splWhiteSemanticTarget_neg_one ring e t hc
  rw [hold]
  exact hinE

theorem splWhiteOldImageResponderSemanticRow_proved :
    SPLWhiteOldImageResponderSemanticRow := by
  unfold SPLWhiteOldImageResponderSemanticRow
  intro _hMirror
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t t'
  dsimp only
  intro hCtok hr0tok hshape hpost hVW

  let rsite := ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C rsite)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2

  change
    tokenAt .white (C rsite) = some t
    at hCtok
  change
    tokenAt .white
        (sourceClear .white p.2) = some t
    at hr0tok
  change
    ((¬ ((sourceClear .white p.1).last = false ∧
          (sourceClear .white p.2).last = false) ∧
        i = rsite ∧
        tokenAt .white
            (moveToken hpsi .white p.1 p.2).2 =
          some t') ∨
      (((sourceClear .white p.1).last = false ∧
          (sourceClear .white p.2).last = false) ∧
        ((i = e ∧
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).1 =
              some t') ∨
          (i = rsite ∧
            tokenAt .white
                (moveToken hpsi .white p.1 p.2).2 =
              some t'))))
    at hshape

  have hrow :=
    splAlgorithm2DistWriteIdempotent
      hn3 hpsi ring root C e hSPL
  dsimp only at hrow

  have hpreRDist :
      pre.2.dist = (C rsite).dist := by
    simpa [pre, rsite] using
      hrow.2.2.2.2.1

  have hpreLId :
      pre.1.id = (C e).id := by
    simpa [pre, rsite] using
      hrow.2.2.2.2.2.1

  have hpRDist :
      p.2.dist = (C rsite).dist := by
    calc
      p.2.dist = pre.2.dist := by
        simpa [p] using
          splWhiteSemanticBlackPassRightDist
            hpsi pre.1 pre.2
      _ = (C rsite).dist := hpreRDist

  have hpLId :
      p.1.id = (C e).id := by
    calc
      p.1.id = pre.1.id := by
        simpa [p] using
          splWhiteSemanticBlackPassLeftId
            hpsi pre.1 pre.2
      _ = (C e).id := hpreLId

  have hr0 :
      tokenAt .white
          (sourceClear .white p.2) = some t :=
    hr0tok

  have hvalidPre :
      ValidToken .white C rsite :=
    splWhiteSemanticValid_of_clear
      p.2 C rsite t hpRDist hCtok hr0

  have hclearId :
      (sourceClear .white p.1).id = (C e).id := by
    calc
      (sourceClear .white p.1).id = p.1.id :=
        splWhiteSemanticSourceClear_id .white p.1
      _ = (C e).id := hpLId

  rcases hshape with hclosed | hopen
  · rcases hclosed with
      ⟨hgate, hir, hq⟩
    subst i

    have hgate' :
        ¬ ((sourceClear .white p.1).last = false ∧
            (sourceClear .white p.2).last = false) :=
      hgate
    have hq' :
        tokenAt .white
            (moveToken hpsi .white p.1 p.2).2 =
          some t' :=
      hq
    have htt :
        t' = t :=
      splWhiteSemanticClosedRight_same
        hpsi p.1 p.2 t t' hr0 hgate' hq'
    have hpostT :
        tokenAt .white
            ((nextConfig ring C e) rsite) =
          some t := by
      rw [← htt]
      exact hpost
    have hworkPre :
        WorkingFor ring root C rsite .white seg.val :=
      splWhiteSemanticWorking_same_backward
        ring root
        C (nextConfig ring C e)
        rsite .white seg.val t
        hCtok hpostT hVW.2
    exact
      ⟨hvalidPre, hworkPre,
        Or.inl ⟨rfl, htt⟩⟩

  · rcases hopen with ⟨hgate, hwhere⟩
    have hgate' :
        (sourceClear .white p.1).last = false ∧
          (sourceClear .white p.2).last = false :=
      hgate

    rcases hwhere with hleft | hright
    · rcases hleft with ⟨hie, hq⟩
      subst i
      have hq' :
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).1 =
            some t' :=
        hq
      have hcases :=
        splWhiteSemanticResponderMoved_shape
          hpsi ring e p.1 p.2 t t'
          hgate' hr0 hq'
      rcases hcases with hord | hturn
      · rcases hord with
          ⟨holdNeg, hnewNeg, htarget,
            hbit, hcarry⟩
        have hworkPre :
            WorkingFor ring root C rsite
              .white seg.val :=
          splWhiteSemanticWorkingNegative_backward
            ring root
            C (nextConfig ring C e)
            rsite e .white seg.val t t'
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
            tokenAt .white
                ((nextConfig ring C e) e) =
              some
                (remark2NegTurnValue
                  hpsi (C e).id t) := by
          rw [← hval]
          exact hpost
        have hworkPre :
            WorkingFor ring root C rsite
              .white seg.val :=
          splWhiteSemanticNegTurn_working_backward
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
          tokenAt .white
              (moveToken hpsi .white p.1 p.2).2 =
            some t' :=
        hq
      have htt :
          t' = t :=
        splWhiteSemanticOpenRight_same
          hpsi p.1 p.2 t t'
          hgate' hr0 hq'
      have hpostT :
          tokenAt .white
              ((nextConfig ring C e) rsite) =
            some t := by
        rw [← htt]
        exact hpost
      have hworkPre :
          WorkingFor ring root C rsite
            .white seg.val :=
        splWhiteSemanticWorking_same_backward
          ring root
          C (nextConfig ring C e)
          rsite .white seg.val t
          hCtok hpostT hVW.2
      exact
        ⟨hvalidPre, hworkPre,
          Or.inl ⟨rfl, htt⟩⟩


end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splWhiteOldImageResponderSemanticRow_proved

