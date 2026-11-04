import Leader.PPL.Safety.SPLWhiteCorrectnessRoute
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.TransitionFacts
import Init.Omega

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Convergence.L18

private theorem q20276SourceClearSomeValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt kind
          (sourceClear kind q) =
        some t) :
    tokenAt kind q = some t ∧
      l18Risk2LocalValid kind q t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : tokenAt kind q with
  | none =>
      try simp [hq] at h
  | some u =>
      by_cases hv :
          l18Risk2LocalValid kind q u
      · simp only [hq, if_pos hv] at h
        have hut : u = t :=
          Option.some.inj h
        subst u
        exact ⟨rfl, hv⟩
      · simp only [hq, if_neg hv] at h
        unfold l18Risk2SetToken at h
        cases kind <;>
          try simp [tokenAt] at h

private theorem q20276ValidOfCleared
    {n psi kappa : Nat}
    (kind : TokenKind)
    (C : Config n psi kappa)
    (i : Fin n)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist : q.dist = (C i).dist)
    (hCtok : tokenAt kind (C i) = some t)
    (hclear :
      tokenAt kind (sourceClear kind q) =
        some t) :
    ValidToken kind C i := by
  have hs :=
    q20276SourceClearSomeValid
      kind q t hclear
  have hv := hs.2
  unfold l18Risk2LocalValid at hv
  dsimp only at hv
  unfold ValidToken
  rw [hCtok]
  dsimp only
  unfold tokenTargetCoordinate at hv ⊢
  rw [hdist] at hv
  exact hv

private theorem q20276PositiveMoveTarget
    {n psi : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (t t' : TokenData psi)
    (hc2 :
      2 ≤ decodeOffset psi (tokenCode t))
    (hc' :
      decodeOffset psi (tokenCode t') =
        decodeOffset psi (tokenCode t) - 1) :
    tokenTargetSite ring
        (ring.rightNeighbor e) t' =
      tokenTargetSite ring e t := by
  cases hcode :
      decodeOffset psi (tokenCode t) with
  | negSucc m =>
      rw [hcode] at hc2
      omega
  | ofNat m =>
      have hm2 : 2 ≤ m := by
        rw [hcode] at hc2
        simp only [Int.ofNat_eq_coe] at hc2
        omega
      have hcode' :
          decodeOffset psi (tokenCode t') =
            ((m - 1 : Nat) : Int) := by
        rw [hc', hcode]
        simp only [Int.ofNat_eq_coe]
        omega
      have hp :
          0 < decodeOffset psi (tokenCode t) := by
        rw [hcode]
        omega
      have hp' :
          0 < decodeOffset psi (tokenCode t') := by
        rw [hcode']
        omega
      unfold tokenTargetSite
      rw [if_pos hp', if_pos hp]
      rw [hcode, hcode']
      change
        shiftRight ring
            (ring.rightNeighbor e) (m - 1) =
          shiftRight ring e m
      change
        shiftRight ring
            (shiftRight ring e 1) (m - 1) =
          shiftRight ring e m
      rw [l18Risk2ShiftRight_add]
      congr 2
      omega

private theorem q20276LiteralMotion
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (e : Fin n)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (sourceClear .white l).last = false ∧
        (sourceClear .white r).last = false)
    (hleft :
      tokenAt .white
          (sourceClear .white l) =
        some t)
    (hrnone :
      tokenAt .white
          (sourceClear .white r) =
        none)
    (hq :
      tokenAt .white
          (moveToken hpsi .white l r).2 =
        some t') :
    PPL.Remark2RightLiteralMotionData
      hpsi ring e (ring.rightNeighbor e)
      t t' := by
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi TokenKind.white l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq

  by_cases hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int)
  · have heq :
        l18Risk2MkToken
            (offsetNegPsiPlusOneCode
              psi hpsi)
            t.1.2 t.2 =
          t' := by
      simpa
        [hleft, hrnone, hc1,
          l18Risk2SourceSet_tokenAt]
        using hq

    have hbit :
        tokenBitBool t' =
          tokenBitBool t := by
      rw [← heq]
      rfl
    have hcarry :
        tokenCarryBool t' =
          tokenCarryBool t := by
      rw [← heq]
      rfl
    have hturn :
        t' =
          PPL.remark2RightTurnValue
            hpsi t := by
      calc
        t' =
            l18Risk2MkToken
              (offsetNegPsiPlusOneCode
                psi hpsi)
              t.1.2 t.2 := heq.symm
        _ =
            PPL.remark2RightTurnValue
              hpsi t := by
          rfl

    unfold PPL.Remark2RightLiteralMotionData
    exact
      ⟨hbit, hcarry,
        Or.inr ⟨hc1, hturn⟩⟩

  · by_cases hc2 :
      2 ≤ decodeOffset psi (tokenCode t)
    · have heq :
          l18Risk2MkToken
              (encodeOffset psi
                (decodeOffset psi
                    (tokenCode t) - 1)
                (by
                  have hv :=
                    decodeOffset_valid
                      psi (by omega)
                      (tokenCode t)
                  rcases hv with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
              t.1.2 t.2 =
            t' := by
        simpa
          [hleft, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq

      have hdec0 :=
        congrArg
          (fun u : TokenData psi =>
            decodeOffset psi (tokenCode u))
          heq.symm
      have hdec :
          decodeOffset psi (tokenCode t') =
            decodeOffset psi (tokenCode t) - 1 := by
        simpa
          [l18Risk2MkToken, tokenCode,
            decode_encode]
          using hdec0

      have hbit :
          tokenBitBool t' =
            tokenBitBool t := by
        rw [← heq]
        rfl
      have hcarry :
          tokenCarryBool t' =
            tokenCarryBool t := by
        rw [← heq]
        rfl
      have hnewPos :
          0 < decodeOffset psi
            (tokenCode t') := by
        omega
      have htarget :=
        q20276PositiveMoveTarget
          ring e t t' hc2 hdec

      unfold PPL.Remark2RightLiteralMotionData
      exact
        ⟨hbit, hcarry,
          Or.inl
            ⟨hc2, hnewPos, htarget⟩⟩

    · have hf : False := by
        simpa
          [hleft, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq
      exact False.elim hf

private theorem q20276TurnDecode
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) :
    decodeOffset psi
        (tokenCode
          (PPL.remark2RightTurnValue
            hpsi t)) =
      1 - ((psi : Nat) : Int) := by
  unfold PPL.remark2RightTurnValue
  change
    decodeOffset psi
        (offsetNegPsiPlusOneCode
          psi hpsi) =
      1 - ((psi : Nat) : Int)
  exact decodeOffset_negPsiPlusOne psi hpsi

private theorem q20276TurnTarget
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (j : Fin n)
    (t : TokenData psi) :
    tokenTargetSite ring j
        (PPL.remark2RightTurnValue
          hpsi t) =
      shiftLeft ring j (psi - 1) := by
  unfold tokenTargetSite
  rw [q20276TurnDecode hpsi t]
  have hnpos :
      ¬
        (0 <
          (1 - ((psi : Nat) : Int))) := by
    omega
  rw [if_neg hnpos]
  have hz :
      1 - ((psi : Nat) : Int) =
        -(((psi - 1 : Nat) : Int)) := by
    omega
  rw [hz]
  try simp

private theorem q20276ShiftRightN
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    shiftRight ring i n = i := by
  apply Fin.ext
  simp only [shiftRight]
  rw [Nat.add_mod]
  try simp [Nat.mod_eq_of_lt i.isLt]

private theorem q20276ShiftLeftEqShiftRightSub
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d : Nat)
    (hd : d < n) :
    shiftLeft ring i d =
      shiftRight ring i (n - d) := by
  apply Fin.ext
  simp only [shiftLeft, shiftRight]
  rw [Nat.mod_eq_of_lt hd]
  have hs :
      i.val + n - d =
        i.val + (n - d) := by
    omega
  rw [hs]

private theorem q20276ShiftRightShiftLeftCancel
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (d : Nat)
    (hd : d < n) :
    shiftRight ring
        (shiftLeft ring i d) d =
      i := by
  rw [q20276ShiftLeftEqShiftRightSub
    ring i d hd]
  rw [l18Risk2ShiftRight_add]
  have hs : n - d + d = n := by
    omega
  rw [hs, q20276ShiftRightN]

private theorem q20276OldTargetOne
    {n psi : Nat}
    (ring : DirectedRing n)
    (e : Fin n)
    (t : TokenData psi)
    (hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int)) :
    tokenTargetSite ring e t =
      ring.rightNeighbor e := by
  unfold tokenTargetSite
  rw [hc1]
  try simp
  rfl

private theorem q20276OrdinaryWorkingBackward
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t t' : TokenData psi)
    (hCtok :
      tokenAt .white (C e) = some t)
    (hDtok :
      tokenAt .white
          (D (ring.rightNeighbor e)) =
        some t')
    (hc2 :
      2 ≤ decodeOffset psi (tokenCode t))
    (hnewPos :
      0 < decodeOffset psi (tokenCode t'))
    (htarget :
      tokenTargetSite ring
          (ring.rightNeighbor e) t' =
        tokenTargetSite ring e t)
    (hwork :
      WorkingFor ring root D
        (ring.rightNeighbor e)
        .white seg.val) :
    WorkingFor ring root C e .white seg.val := by
  have hw := hwork
  unfold WorkingFor at hw ⊢
  rw [hDtok] at hw
  rw [hCtok]
  dsimp only at hw ⊢

  have hz := hw.1
  rcases hw.2 with hp | hn
  · refine
      ⟨hz,
        Or.inl
          ⟨by omega, ?_⟩⟩
    rw [← htarget]
    exact hp.2
  · have hf : False := by
      omega
    exact False.elim hf

private theorem q20276TurnWorkingBackward
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (t t' : TokenData psi)
    (hSPL : SPLAt ring root C)
    (hCtok :
      tokenAt .white (C e) = some t)
    (hc1 :
      decodeOffset psi (tokenCode t) =
        (1 : Int))
    (hpost :
      tokenAt .white
          ((nextConfig ring C e)
            (ring.rightNeighbor e)) =
        some t')
    (hturn :
      t' =
        PPL.remark2RightTurnValue hpsi t)
    (hvalidPost :
      ValidToken .white
        (nextConfig ring C e)
        (ring.rightNeighbor e))
    (hworkPost :
      WorkingFor ring root
        (nextConfig ring C e)
        (ring.rightNeighbor e)
        .white seg.val) :
    WorkingFor ring root C e .white seg.val := by
  let r := ring.rightNeighbor e
  let D := nextConfig ring C e
  let newTarget :=
    tokenTargetSite ring r t'
  let u :=
    cyclicOffset ring root newTarget
  let y :=
    cyclicOffset ring root r
  let zeta := segmentCount n psi

  have hpost' :
      tokenAt .white (D r) = some t' := by
    simpa [D, r] using hpost

  have hvalid' :
      ValidToken .white D r := by
    simpa [D, r] using hvalidPost

  have hwork' :
      WorkingFor ring root D r
        .white seg.val := by
    simpa [D, r] using hworkPost

  have hz :
      seg.val + 3 ≤ zeta := by
    dsimp only [zeta]
    have hs := seg.isLt
    omega

  have hz0 := hz
  dsimp only [zeta] at hz0
  unfold segmentCount at hz0
  have hmul :
      (seg.val + 3) * psi ≤
        n + psi - 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < psi)).mp hz0

  have hfit :
      (seg.val + 2) * psi < n := by
    try simp [Nat.add_mul] at hmul ⊢
    omega

  have htwo :
      2 * psi ≤
        (seg.val + 2) * psi :=
    Nat.mul_le_mul_right psi (by omega)

  have h2psi : 2 * psi < n :=
    Nat.lt_of_le_of_lt htwo hfit

  have hdlt : psi - 1 < n := by
    omega

  have hcNew :
      decodeOffset psi (tokenCode t') =
        1 - ((psi : Nat) : Int) := by
    rw [hturn]
    exact q20276TurnDecode hpsi t

  have hnewNeg :
      decodeOffset psi (tokenCode t') < 0 := by
    rw [hcNew]
    omega

  have hnewTargetEq :
      newTarget =
        shiftLeft ring r (psi - 1) := by
    dsimp only [newTarget]
    rw [hturn]
    exact q20276TurnTarget hpsi ring r t

  have hw := hwork'
  unfold WorkingFor at hw
  rw [hpost'] at hw
  dsimp only at hw
  have hzPos := hw.1

  have hinNew :
      InSegment ring root psi seg.val
        newTarget := by
    rcases hw.2 with hp | hn
    · have hf : False := by
        omega
      exact False.elim hf
    · simpa [newTarget] using hn.2

  unfold InSegment at hinNew
  dsimp only at hinNew

  have huLower :
      seg.val * psi ≤ u := by
    simpa [u] using hinNew.1

  have huUpper :
      u < (seg.val + 1) * psi := by
    have hmin :
        u <
          Nat.min
            ((seg.val + 1) * psi) n := by
      simpa [u] using hinNew.2
    exact
      Nat.lt_of_lt_of_le
        hmin
        (Nat.min_le_left _ _)

  have hnewRep :
      shiftRight ring root u =
        newTarget := by
    dsimp only [u]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root newTarget

  have hrFromNew :
      r =
        shiftRight ring
          newTarget (psi - 1) := by
    calc
      r =
          shiftRight ring
            (shiftLeft ring r (psi - 1))
            (psi - 1) :=
        (q20276ShiftRightShiftLeftCancel
          ring r (psi - 1) hdlt).symm
      _ =
          shiftRight ring
            newTarget (psi - 1) := by
        rw [← hnewTargetEq]

  have hsegGap :
      (seg.val + 1) * psi +
          (psi - 1) <
        (seg.val + 2) * psi := by
    try simp [Nat.add_mul]
    omega

  have husum :
      u + (psi - 1) < n := by
    have h1 :
        u + (psi - 1) <
          (seg.val + 1) * psi +
            (psi - 1) :=
      Nat.add_lt_add_right
        huUpper (psi - 1)
    exact
      Nat.lt_trans
        (Nat.lt_trans h1 hsegGap)
        hfit

  have hrRep :
      r =
        shiftRight ring root
          (u + (psi - 1)) := by
    calc
      r =
          shiftRight ring
            newTarget (psi - 1) :=
        hrFromNew
      _ =
          shiftRight ring
            (shiftRight ring root u)
            (psi - 1) := by
        rw [hnewRep]
      _ =
          shiftRight ring root
            (u + (psi - 1)) :=
        l18Risk2ShiftRight_add
          ring root u (psi - 1)

  have hy :
      y = u + (psi - 1) := by
    dsimp only [y]
    rw [hrRep]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root
        (u + (psi - 1)) husum

  have hf :=
    splAlgorithm23FieldFrameResidual_proved
      hn3 hpsi ring root C e hSPL
  dsimp only at hf

  have hgeomR := hSPL.1.2.2 r
  dsimp only at hgeomR

  have hdistPost :
      (D r).dist.val =
        y % (2 * psi) := by
    calc
      (D r).dist.val =
          (C r).dist.val := by
        have hd := hf.2.1 r
        simpa [D] using congrArg Fin.val hd
      _ =
          cyclicOffset ring root r %
            (2 * psi) :=
        hgeomR.1
      _ =
          y % (2 * psi) := by
        rfl

  have hv := hvalid'
  unfold ValidToken at hv
  rw [hpost'] at hv
  dsimp only at hv

  have hvNeg :
      decodeOffset psi (tokenCode t') < 0 ∧
        1 ≤
          tokenTargetCoordinate
            .white (D r) t' ∧
        tokenTargetCoordinate
            .white (D r) t' ≤
          (((psi - 1 : Nat)) : Int) := by
    rcases hv with hp | hn
    · have hfalse : False := by
        omega
      exact False.elim hfalse
    · exact hn

  have hcoordLo := hvNeg.2.1
  have hcoordHi := hvNeg.2.2

  have huNe :
      ¬ (u = seg.val * psi) := by
    intro huEq

    have hb0 :=
      l18Gapped_psiMultiple_border
        psi seg.val (by omega)

    have huMul :
        u = psi * seg.val := by
      calc
        u = seg.val * psi := huEq
        _ = psi * seg.val :=
          Nat.mul_comm _ _

    have hb :
        u % (2 * psi) = 0 ∨
          u % (2 * psi) = psi := by
      rw [huMul]
      exact hb0

    rcases hb with hzero | hpsiMod

    · have hymod :
          y % (2 * psi) =
            psi - 1 := by
        rw [hy, Nat.add_mod, hzero]
        have hdmod :
            (psi - 1) % (2 * psi) =
              psi - 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hdmod, Nat.zero_add]
        exact hdmod

      have hcoord :
          tokenTargetCoordinate
              .white (D r) t' =
            ((psi : Nat) : Int) := by
        unfold tokenTargetCoordinate
        simp only [tokenD']
        rw [hdistPost, hcNew, hymod]
        have hs :
            (((psi - 1 : Nat) : Int) +
                  (1 - ((psi : Nat) : Int)) +
                  ((psi : Nat) : Int)) =
              ((psi : Nat) : Int) := by
          omega
        rw [hs]
        rw [Int.emod_eq_of_lt
          (by omega) (by omega)]

      rw [hcoord] at hcoordHi
      omega

    · have hymod :
          y % (2 * psi) =
            2 * psi - 1 := by
        rw [hy, Nat.add_mod, hpsiMod]
        have hdmod :
            (psi - 1) % (2 * psi) =
              psi - 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hdmod]
        have hlt :
            psi + (psi - 1) <
              2 * psi := by
          omega
        rw [Nat.mod_eq_of_lt hlt]
        omega

      have hcoord :
          tokenTargetCoordinate
              .white (D r) t' =
            (0 : Int) := by
        unfold tokenTargetCoordinate
        simp only [tokenD']
        rw [hdistPost, hcNew, hymod]
        have hs :
            (((2 * psi - 1 : Nat) : Int) +
                  (1 - ((psi : Nat) : Int)) +
                  ((psi : Nat) : Int)) =
              (((2 * psi : Nat)) : Int) := by
          omega
        rw [hs]
        try simp

      rw [hcoord] at hcoordLo
      omega

  have huStrict :
      seg.val * psi < u := by
    omega

  have hyLower :
      (seg.val + 1) * psi ≤ y := by
    rw [hy]
    try simp [Nat.add_mul]
    omega

  have hyUpper :
      y < (seg.val + 2) * psi := by
    rw [hy]
    have h1 :
        u + (psi - 1) <
          (seg.val + 1) * psi +
            (psi - 1) :=
      Nat.add_lt_add_right
        huUpper (psi - 1)
    exact Nat.lt_trans h1 hsegGap

  have hinOld :
      InSegment ring root psi
        (seg.val + 1) r := by
    unfold InSegment
    dsimp only
    rw [show
      cyclicOffset ring root r = y by rfl]
    constructor
    · exact hyLower
    · exact
        Nat.lt_min.mpr
          ⟨hyUpper,
            Nat.lt_trans hyUpper hfit⟩

  have hidxLt :
      seg.val + 1 < zeta := by
    omega

  have hidx :
      (seg.val + 1) % zeta =
        seg.val + 1 :=
    Nat.mod_eq_of_lt hidxLt

  have holdTarget :
      tokenTargetSite ring e t = r := by
    dsimp only [r]
    exact q20276OldTargetOne
      ring e t hc1

  unfold WorkingFor
  rw [hCtok]
  dsimp only
  rw [hc1]

  exact
    ⟨hzPos,
      Or.inl
        ⟨by omega,
          by
            rw [hidx, holdTarget]
            exact hinOld⟩⟩

theorem splWhiteOldImageInitiatorMovedRightSemanticRow_proved :
    SPLWhiteOldImageInitiatorMovedRightSemanticRow := by
  unfold SPLWhiteOldImageInitiatorMovedRightSemanticRow

  intro _hMirror
  intro n psi kappa
  intro hn3 hpsi ring root C e
  intro hSPL
  intro seg t t'
  dsimp only
  intro hCtok hl0tok hgate hrnone
  intro hq hpost hVW

  let r := ring.rightNeighbor e
  let pre :=
    PPL.Safety.PeacefulProps.preTokenPair
      hpsi (C e) (C r)
  let p :=
    PPL.moveToken hpsi .black pre.1 pre.2

  have hl0 := hl0tok
  change
    tokenAt .white
        (sourceClear .white p.1) =
      some t at hl0

  have hr0 := hrnone
  change
    tokenAt .white
        (sourceClear .white p.2) =
      none at hr0

  have hgate' := hgate
  change
    (sourceClear .white p.1).last = false ∧
      (sourceClear .white p.2).last = false
      at hgate'

  have hq' := hq
  change
    tokenAt .white
        (moveToken hpsi .white p.1 p.2).2 =
      some t' at hq'

  have hpost' :
      tokenAt .white
          ((nextConfig ring C e) r) =
        some t' := by
    simpa [r] using hpost

  have hVW' :
      ValidToken .white
          (nextConfig ring C e) r ∧
        WorkingFor ring root
          (nextConfig ring C e)
          r .white seg.val := by
    simpa [r] using hVW

  have hrow0 :=
    splAlgorithm2DistWriteIdempotent
      hn3 hpsi ring root C e hSPL
  dsimp only at hrow0

  have hpreDist :
      pre.1.dist = (C e).dist := by
    simpa [pre, r] using
      hrow0.2.2.2.1

  have hblack :=
    PPL.moveToken_initiator_fields
      hpsi TokenKind.black pre.1 pre.2

  have hpDist0 :=
    congrArg
      (fun q : State psi kappa => q.dist)
      hblack

  have hpDistPre :
      p.1.dist = pre.1.dist := by
    simpa [p, PPL.eraseKindToken]
      using hpDist0

  have hpDist :
      p.1.dist = (C e).dist :=
    hpDistPre.trans hpreDist

  have hvalidPre :
      ValidToken .white C e :=
    q20276ValidOfCleared
      TokenKind.white C e p.1 t
      hpDist hCtok hl0

  have hliteral :
      PPL.Remark2RightLiteralMotionData
        hpsi ring e r t t' := by
    simpa [r] using
      q20276LiteralMotion
        hpsi ring e p.1 p.2
        t t' hgate' hl0 hr0 hq'

  have hworkPre :
      WorkingFor ring root C e
        .white seg.val := by
    have hm := hliteral
    unfold
      PPL.Remark2RightLiteralMotionData
      at hm

    rcases hm.2.2 with hord | hturn

    · exact
        q20276OrdinaryWorkingBackward
          ring root C
          (nextConfig ring C e)
          e seg t t'
          hCtok
          (by simpa [r] using hpost')
          hord.1 hord.2.1
          (by simpa [r] using hord.2.2)
          (by simpa [r] using hVW'.2)

    · exact
        q20276TurnWorkingBackward
          hn3 hpsi ring root C e
          seg t t' hSPL
          hCtok hturn.1
          (by simpa [r] using hpost')
          hturn.2
          (by simpa [r] using hVW'.1)
          (by simpa [r] using hVW'.2)

  exact
    ⟨hvalidPre, hworkPre, hliteral⟩

end PPL.Safety.SPL

#print axioms
  PPL.Safety.SPL.splWhiteOldImageInitiatorMovedRightSemanticRow_proved
