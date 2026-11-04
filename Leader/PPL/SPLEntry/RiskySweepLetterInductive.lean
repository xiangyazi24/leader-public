import Leader.PPL.SPLEntry.RiskySweepLetterPrefix
import Leader.PPL.SPLEntry.LastSweepPhase
import Leader.PPL.SPLEntry.CPBUniqueStepRow
import Leader.PPL.TransitionFacts
import Init.Data.List.OfFn
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/--
The exact inductive letter row needed by the risky-flush sweep.

Unlike the earlier L18RiskySweepLetterRow, there is no claim about
unprocessed offsets.  A risky positive token may legitimately move from j
to j+1 and remain risky; the prefix induction does not need j+1 clean yet.
-/
def L18RiskySweepLetterRow2 : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat),
    j < psi →
    CDLAt ring root C →
    (∀ i : Fin n,
      cyclicOffset ring root i < j →
      ¬ Risky ring root C i) →
    let D :=
      pprimeStep ring C
        (PPL.shiftRight ring root j)
    CDLAt ring root D ∧
      ∀ i : Fin n,
        cyclicOffset ring root i < j + 1 →
        ¬ Risky ring root D i

/-! -------------------------------------------------------------------------
    Ring geometry
------------------------------------------------------------------------- -/

theorem l18Risk2ShiftRight_add
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (a b : Nat) :
    PPL.shiftRight ring
        (PPL.shiftRight ring i a) b =
      PPL.shiftRight ring i (a + b) := by
  apply Fin.ext
  change
    (((i.val + a) % n + b) % n) =
      (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem l18Risk2RightNeighbor_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n)
    (a : Nat) :
    ring.rightNeighbor
        (PPL.shiftRight ring i a) =
      PPL.shiftRight ring i (a + 1) := by
  change
    PPL.shiftRight ring
        (PPL.shiftRight ring i a) 1 =
      PPL.shiftRight ring i (a + 1)
  exact l18Risk2ShiftRight_add ring i a 1

theorem l18Risk2CyclicOffset_self
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    PPL.cyclicOffset ring root root = 0 := by
  unfold PPL.cyclicOffset
  have h :
      root.val + n - root.val = n := by
    omega
  rw [h, Nat.mod_self]

theorem l18Risk2CyclicOffset_shiftRight_of_lt
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (d : Nat)
    (hd : d < n) :
    PPL.cyclicOffset ring root
        (PPL.shiftRight ring root d) =
      d := by
  exact
    l18LastCyclicOffsetShiftRight
      ring root d hd

theorem l18Risk2ShiftRight_cyclicOffset
    {n : Nat}
    (ring : DirectedRing n)
    (root i : Fin n) :
    PPL.shiftRight ring root
        (PPL.cyclicOffset ring root i) =
      i := by
  exact
    l18LastShiftRightCyclicOffset
      ring root i

theorem l18Risk2CyclicOffset_injective
    {n : Nat}
    (ring : DirectedRing n)
    (root i j : Fin n)
    (h :
      PPL.cyclicOffset ring root i =
        PPL.cyclicOffset ring root j) :
    i = j := by
  have hs :=
    congrArg
      (fun d : Nat =>
        PPL.shiftRight ring root d) h
  rw [l18Risk2ShiftRight_cyclicOffset,
      l18Risk2ShiftRight_cyclicOffset] at hs
  exact hs

theorem l18Risk2ShiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight,
    Nat.mod_eq_of_lt i.isLt]

theorem l18Risk2OutsideS0AtPsi
    {n psi : Nat}
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n) :
    ¬ InSegment ring root psi 0
        (PPL.shiftRight ring root psi) := by
  unfold InSegment
  dsimp only
  rw [l18Risk2CyclicOffset_shiftRight_of_lt
    ring root psi hlt]
  have hmin :
      Nat.min psi n = psi :=
    Nat.min_eq_left (Nat.le_of_lt hlt)
  simp [hmin]

theorem l18Risk2Threshold_ge_psi
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (hlt : psi < n) :
    psi ≤
      psi * (PPL.segmentCount n psi - 1) := by
  have hz :
      2 ≤ PPL.segmentCount n psi :=
    (two_le_segmentCount_iff_psi_lt_n hpsi).2 hlt
  have hz1 :
      1 ≤ PPL.segmentCount n psi - 1 := by
    omega
  calc
    psi = psi * 1 := by simp
    _ ≤ psi * (PPL.segmentCount n psi - 1) :=
      Nat.mul_le_mul_left psi hz1

/-! -------------------------------------------------------------------------
    Token geometry: +psi is never risky inside a proper S0
------------------------------------------------------------------------- -/

theorem l18Risk2SafeCode_not_tokenRisky
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (D : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (kind : TokenKind)
    (hsafe :
      ∀ t : TokenData psi,
        PPL.tokenAt kind
            (D (PPL.shiftRight ring root j)) =
          some t →
        PPL.decodeOffset psi (PPL.tokenCode t) < 0 ∨
          PPL.decodeOffset psi (PPL.tokenCode t) =
            ((psi : Nat) : Int)) :
    ¬ PPL.tokenRisky ring root D
        (PPL.shiftRight ring root j) kind := by
  intro hrisk
  unfold PPL.tokenRisky at hrisk
  cases ht :
      PPL.tokenAt kind
        (D (PPL.shiftRight ring root j)) with
  | none =>
      simp [ht] at hrisk
  | some t =>
      rw [ht] at hrisk
      dsimp only at hrisk
      have hs := hsafe t ht
      rcases hs with hneg | hpsiCode
      · omega
      · rw [hpsiCode] at hrisk
        have hidx :
            psi - j <
              (((psi : Nat) : Int).natAbs + 1) := by
          simp
          omega
        have hin :=
          hrisk.2
            ⟨psi - j, hidx⟩
        have hsite :
            PPL.shiftRight ring
                (PPL.shiftRight ring root j)
                (psi - j) =
              PPL.shiftRight ring root psi := by
          calc
            PPL.shiftRight ring
                (PPL.shiftRight ring root j)
                (psi - j) =
              PPL.shiftRight ring root
                (j + (psi - j)) :=
              l18Risk2ShiftRight_add
                ring root j (psi - j)
            _ =
              PPL.shiftRight ring root psi := by
              congr 2
              omega
        rw [hsite] at hin
        exact
          (l18Risk2OutsideS0AtPsi
            hlt ring root) hin

theorem l18Risk2BoundaryToken_not_risky
    {n psi kappa : Nat}
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (D : Config n psi kappa)
    (j : Nat)
    (hboundary : j + 1 = psi)
    (kind : TokenKind) :
    ¬ PPL.tokenRisky ring root D
        (PPL.shiftRight ring root j) kind := by
  intro hrisk
  unfold PPL.tokenRisky at hrisk
  cases ht :
      PPL.tokenAt kind
        (D (PPL.shiftRight ring root j)) with
  | none =>
      simp [ht] at hrisk
  | some t =>
      rw [ht] at hrisk
      dsimp only at hrisk
      cases hc :
          PPL.decodeOffset psi (PPL.tokenCode t) with
      | ofNat m =>
          rw [hc] at hrisk
          cases m with
          | zero =>
              have hp : (0 : Int) < 0 := by
                simpa using hrisk.1
              omega
          | succ m =>
              have hin :=
                hrisk.2
                  (⟨1, by
                      change 1 < Nat.succ m + 1
                      omega⟩ :
                    Fin
                      ((Int.ofNat (Nat.succ m)).natAbs +
                        1))
              have hsite :
                  PPL.shiftRight ring
                      (PPL.shiftRight ring root j) 1 =
                    PPL.shiftRight ring root psi := by
                calc
                  PPL.shiftRight ring
                      (PPL.shiftRight ring root j) 1 =
                    PPL.shiftRight ring root (j + 1) :=
                    l18Risk2ShiftRight_add
                      ring root j 1
                  _ =
                    PPL.shiftRight ring root psi := by
                    rw [hboundary]
              rw [hsite] at hin
              exact
                (l18Risk2OutsideS0AtPsi
                  hlt ring root) hin
      | negSucc m =>
          rw [hc] at hrisk
          omega

theorem l18Risk2Boundary_not_risky
    {n psi kappa : Nat}
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (D : Config n psi kappa)
    (j : Nat)
    (hboundary : j + 1 = psi) :
    ¬ Risky ring root D
        (PPL.shiftRight ring root j) := by
  intro h
  rcases h with hb | hw
  · exact
      l18Risk2BoundaryToken_not_risky
        hlt ring root D j hboundary
        TokenKind.black hb
  · exact
      l18Risk2BoundaryToken_not_risky
        hlt ring root D j hboundary
        TokenKind.white hw

/-! -------------------------------------------------------------------------
    Literal Algorithm-3 mirror, using only public aliases
------------------------------------------------------------------------- -/

def l18Risk2BitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

def l18Risk2MkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) :
    TokenData psi :=
  ((offset, bit), carry)

def l18Risk2LocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c :=
    PPL.decodeOffset psi (PPL.tokenCode t)
  let target :=
    PPL.tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
      target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
      target ≤ (((psi - 1 : Nat)) : Int))

instance l18Risk2LocalValidDecidable
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (l18Risk2LocalValid kind q t) := by
  unfold l18Risk2LocalValid
  infer_instance

def l18Risk2SetToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

def l18Risk2ClearInvalid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    State psi kappa :=
  match PPL.tokenAt kind q with
  | none => q
  | some t =>
      if l18Risk2LocalValid kind q t then
        q
      else
        l18Risk2SetToken kind q none

def l18Risk2LeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) :
    State psi kappa :=
  { q with
      leader := true
      bullet := (2 : Fin 3)
      shield := true
      signalB := false }

theorem l18Risk2SourceSet_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) :
    PPL.sourceSet kind q t =
      l18Risk2SetToken kind q t := by
  cases kind <;> rfl

theorem l18Risk2SourceClear_eq
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    PPL.sourceClear kind q =
      l18Risk2ClearInvalid kind q := by
  cases kind <;> rfl

theorem l18Risk2SourceBirth_eq
    {psi kappa : Nat}
    (q : State psi kappa) :
    PPL.sourceBirth q =
      l18Risk2LeaderBirth q := by
  rfl

def l18Risk2NegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    l18Risk2MkToken
      (PPL.offsetPsiCode psi hpsi)
      (l18Risk2BitToFin (!sourceBit))
      (l18Risk2BitToFin sourceBit)
  else
    l18Risk2MkToken
      (PPL.offsetPsiCode psi hpsi)
      (l18Risk2BitToFin sourceBit)
      (0 : Fin 2)

def l18Risk2MoveTokenMirror
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let l := PPL.sourceClear kind l
  let r := PPL.sourceClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = PPL.tokenD' psi kind ∧
          PPL.tokenAt kind l = none then
        PPL.sourceSet kind l
          (some
            (l18Risk2MkToken
              (PPL.offsetPsiCode psi hpsi)
              (l18Risk2BitToFin (!l.id))
              (l18Risk2BitToFin l.id)))
      else
        l
    let l :=
      if PPL.tokenAt kind l ≠ none ∧
          PPL.tokenAt kind r ≠ none then
        PPL.sourceSet kind l none
      else
        l
    let moveLeft :=
      fun (l r : State psi kappa) =>
        match PPL.tokenAt kind r with
        | none =>
            (l, r)
        | some t =>
            let c :=
              PPL.decodeOffset psi
                (PPL.tokenCode t)
            if hm1 : c = -1 then
              let next :=
                l18Risk2NegTurnNext
                  hpsi l.id t
              (PPL.sourceSet kind l (some next),
                PPL.sourceSet kind r none)
            else if hm2 : c ≤ -2 then
              have hc :
                  PPL.ValidOffset psi c :=
                PPL.decodeOffset_valid
                  psi (by omega)
                  (PPL.tokenCode t)
              have hc' :
                  PPL.ValidOffset psi (c + 1) := by
                rcases hc with hn | hp
                · left
                  exact ⟨by omega, by omega⟩
                · have hf : False := by
                    omega
                  exact False.elim hf
              let next :=
                l18Risk2MkToken
                  (PPL.encodeOffset psi (c + 1) hc')
                  t.1.2 t.2
              (PPL.sourceSet kind l (some next),
                PPL.sourceSet kind r none)
            else
              (l, r)
    match PPL.tokenAt kind l with
    | none =>
        moveLeft l r
    | some t =>
        let c :=
          PPL.decodeOffset psi (PPL.tokenCode t)
        if hc1 : c = 1 then
          let bit := PPL.tokenBitBool t
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              PPL.sourceBirth r
            else if r.mode = false then
              { r with id := bit }
            else
              r
          let r :=
            PPL.sourceSet kind r
              (some
                (l18Risk2MkToken
                  (PPL.offsetNegPsiPlusOneCode
                    psi hpsi)
                  t.1.2 t.2))
          (PPL.sourceSet kind l none, r)
        else if hc2 : 2 ≤ c then
          have hc :
              PPL.ValidOffset psi c :=
            PPL.decodeOffset_valid
              psi (by omega)
              (PPL.tokenCode t)
          have hc' :
              PPL.ValidOffset psi (c - 1) := by
            rcases hc with hn | hp
            · have hf : False := by
                omega
              exact False.elim hf
            · right
              exact ⟨by omega, by omega⟩
          let next :=
            l18Risk2MkToken
              (PPL.encodeOffset psi (c - 1) hc')
              t.1.2 t.2
          (PPL.sourceSet kind l none,
            PPL.sourceSet kind r (some next))
        else
          moveLeft l r
  else
    (l, r)

theorem l18Risk2MoveTokenMirror_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    l18Risk2MoveTokenMirror
        hpsi kind l r =
      PPL.moveToken hpsi kind l r := by
  cases kind <;> rfl

/--
With an open line-13 gate, anything left at the initiator after one
selected-color MoveToken call is either negative or the +psi value created
by the c=-1 return.  Births and positive initiators either collide away or
move right.
-/
theorem l18Risk2NegTurnNext_decode
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    PPL.decodeOffset psi
        (PPL.tokenCode
          (l18Risk2NegTurnNext
            hpsi sourceBit t)) =
      ((psi : Nat) : Int) := by
  unfold
    l18Risk2NegTurnNext
    l18Risk2MkToken
    PPL.tokenCode
  split <;>
    exact PPL.decodeOffset_psi psi hpsi

theorem l18Risk2SourceSet_tokenAt
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (x : Option (TokenData psi)) :
    PPL.tokenAt kind (PPL.sourceSet kind q x) = x := by
  rw [l18Risk2SourceSet_eq]
  unfold l18Risk2SetToken
  cases kind <;> rfl

theorem l18Risk2SourceClear_last
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).last = q.last := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none =>
      rfl
  | some u =>
      by_cases hv : l18Risk2LocalValid kind q u
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

theorem l18Risk2MoveToken_left_code
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hlast : l.last = false)
    (hrlast : r.last = false) :
    ∀ t : TokenData psi,
      PPL.tokenAt kind
          (PPL.moveToken hpsi kind l r).1 =
        some t →
      PPL.decodeOffset psi (PPL.tokenCode t) < 0 ∨
        PPL.decodeOffset psi (PPL.tokenCode t) =
          ((psi : Nat) : Int) := by
  intro t htok

  have hgate :
      (PPL.sourceClear kind l).last = false ∧
        (PPL.sourceClear kind r).last = false := by
    exact
      ⟨(l18Risk2SourceClear_last kind l).trans hlast,
        (l18Risk2SourceClear_last kind r).trans hrlast⟩

  have hpsiNeOne :
      ((psi : Nat) : Int) ≠ 1 := by
    try (have hm2' := hm2; simp only [PPL.tokenCode] at hm2')
    omega

  have hpsiGeTwo :
      (2 : Int) ≤ ((psi : Nat) : Int) := by
    try (have hm2' := hm2; simp only [PPL.tokenCode] at hm2')
    omega

  rw [← l18Risk2MoveTokenMirror_eq hpsi kind l r] at htok
  unfold l18Risk2MoveTokenMirror at htok
  simp only
    [dif_pos hgate, hgate, and_self, dite_true, ↓reduceDIte] at htok

  cases hl :
      PPL.tokenAt kind (PPL.sourceClear kind l) with
  | none =>
      cases hr :
          PPL.tokenAt kind (PPL.sourceClear kind r) with
      | none =>
          by_cases hdist :
              (PPL.sourceClear kind l).dist.val =
                PPL.tokenD' psi kind
          · have hnone :
                (none : Option (TokenData psi)) = some t := by
              simpa only
                [hl, and_true, if_pos hdist,
                  l18Risk2SourceSet_tokenAt, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  l18Risk2MkToken, PPL.tokenCode,
                  PPL.decodeOffset_psi,
                  hpsiNeOne, hpsiGeTwo]
                using htok
            cases hnone

          · have hnone :
                (none : Option (TokenData psi)) = some t := by
              simpa only
                [hl, and_true, if_neg hdist, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  l18Risk2SourceSet_tokenAt]
                using htok
            cases hnone

      | some u =>
          by_cases hdist :
              (PPL.sourceClear kind l).dist.val =
                PPL.tokenD' psi kind
          · by_cases hm1 :
                PPL.decodeOffset psi (PPL.tokenCode u) = -1
            · simp only
                [hl, and_true, if_pos hdist,
                  l18Risk2SourceSet_tokenAt, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  dif_pos hm1, Option.some.injEq] at htok
              rw [← htok]
              exact
                Or.inr
                  (l18Risk2NegTurnNext_decode hpsi _ u)

            · by_cases hm2 :
                  PPL.decodeOffset psi (PPL.tokenCode u) ≤ -2
              · simp only
                  [hl, and_true, if_pos hdist,
                    l18Risk2SourceSet_tokenAt, hr,
                    ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                    and_false, false_and, and_true, true_and,
                    ite_true, ite_false, ↓reduceIte,
                    dite_true, dite_false, ↓reduceDIte,
                    dif_neg hm1, dif_pos hm2,
                    Option.some.injEq] at htok
                rw [← htok]
                apply Or.inl
                simp only
                  [l18Risk2MkToken,
                    PPL.tokenCode,
                    PPL.decode_encode]
                try (have hm2' := hm2; simp only [PPL.tokenCode] at hm2')
                omega

              · have hnone :
                    (none : Option (TokenData psi)) =
                      some t := by
                  simpa only
                    [hl, and_true, if_pos hdist,
                      l18Risk2SourceSet_tokenAt, hr,
                      ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                      and_false, false_and, and_true, true_and,
                      ite_true, ite_false, ↓reduceIte,
                      dite_true, dite_false, ↓reduceDIte,
                      dif_neg hm1, dif_neg hm2]
                    using htok
                cases hnone

          · by_cases hm1 :
                PPL.decodeOffset psi (PPL.tokenCode u) = -1
            · simp only
                [hl, and_true, if_neg hdist,
                  l18Risk2SourceSet_tokenAt, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  dif_pos hm1, Option.some.injEq] at htok
              rw [← htok]
              exact
                Or.inr
                  (l18Risk2NegTurnNext_decode hpsi _ u)

            · by_cases hm2 :
                  PPL.decodeOffset psi (PPL.tokenCode u) ≤ -2
              · simp only
                  [hl, and_true, if_neg hdist,
                    l18Risk2SourceSet_tokenAt, hr,
                    ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                    and_false, false_and, and_true, true_and,
                    ite_true, ite_false, ↓reduceIte,
                    dite_true, dite_false, ↓reduceDIte,
                    dif_neg hm1, dif_pos hm2,
                    Option.some.injEq] at htok
                rw [← htok]
                apply Or.inl
                simp only
                  [l18Risk2MkToken,
                    PPL.tokenCode,
                    PPL.decode_encode]
                try (have hm2' := hm2; simp only [PPL.tokenCode] at hm2')
                omega

              · have hnone :
                    (none : Option (TokenData psi)) =
                      some t := by
                  simpa only
                    [hl, and_true, if_neg hdist,
                      l18Risk2SourceSet_tokenAt, hr,
                      ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                      and_false, false_and, and_true, true_and,
                      ite_true, ite_false, ↓reduceIte,
                      dite_true, dite_false, ↓reduceDIte,
                      dif_neg hm1, dif_neg hm2]
                    using htok
                cases hnone

  | some u =>
      cases hr :
          PPL.tokenAt kind (PPL.sourceClear kind r) with
      | none =>
          by_cases hc1 :
              PPL.decodeOffset psi (PPL.tokenCode u) = 1
          · have hnone :
                (none : Option (TokenData psi)) = some t := by
              simpa only
                [hl, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  dif_pos hc1,
                  l18Risk2SourceSet_tokenAt]
                using htok
            cases hnone

          · by_cases hc2 :
                2 ≤ PPL.decodeOffset psi (PPL.tokenCode u)
            · have hnone :
                  (none : Option (TokenData psi)) =
                    some t := by
                simpa only
                  [hl, hr,
                    ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                    and_false, false_and, and_true, true_and,
                    ite_true, ite_false, ↓reduceIte,
                    dite_true, dite_false, ↓reduceDIte,
                    dif_neg hc1, dif_pos hc2,
                    l18Risk2SourceSet_tokenAt]
                  using htok
              cases hnone

            · simp only
                [hl, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  dif_neg hc1, dif_neg hc2,
                  l18Risk2SourceSet_tokenAt,
                  Option.some.injEq] at htok
              rw [← htok]
              have hv :
                  PPL.ValidOffset psi
                    (PPL.decodeOffset psi (PPL.tokenCode u)) :=
                PPL.decodeOffset_valid psi (by omega : 0 < psi) (PPL.tokenCode u)
              rcases hv with hn | hp
              · exact Or.inl (by omega)
              · omega

      | some v =>
          by_cases hm1 :
              PPL.decodeOffset psi (PPL.tokenCode v) = -1
          · simp only
              [hl, hr,
                ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                and_false, false_and, and_true, true_and,
                ite_true, ite_false, ↓reduceIte,
                dite_true, dite_false, ↓reduceDIte,
                l18Risk2SourceSet_tokenAt,
                dif_pos hm1, Option.some.injEq] at htok
            rw [← htok]
            exact
              Or.inr
                (l18Risk2NegTurnNext_decode hpsi _ v)

          · by_cases hm2 :
                PPL.decodeOffset psi (PPL.tokenCode v) ≤ -2
            · simp only
                [hl, hr,
                  ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                  and_false, false_and, and_true, true_and,
                  ite_true, ite_false, ↓reduceIte,
                  dite_true, dite_false, ↓reduceDIte,
                  l18Risk2SourceSet_tokenAt,
                  dif_neg hm1, dif_pos hm2,
                  Option.some.injEq] at htok
              rw [← htok]
              apply Or.inl
              simp only
                [l18Risk2MkToken,
                  PPL.tokenCode,
                  PPL.decode_encode]
              try (have hm2' := hm2; simp only [PPL.tokenCode] at hm2')
              omega

            · have hnone :
                  (none : Option (TokenData psi)) =
                    some t := by
                simpa only
                  [hl, hr,
                    ne_eq, reduceCtorEq, not_true_eq_false, not_false_eq_true,
                    and_false, false_and, and_true, true_and,
                    ite_true, ite_false, ↓reduceIte,
                    dite_true, dite_false, ↓reduceDIte,
                    l18Risk2SourceSet_tokenAt,
                    dif_neg hm1, dif_neg hm2]
                  using htok
              cases hnone

/-! -------------------------------------------------------------------------
    Dist/last frame of the prime letter
------------------------------------------------------------------------- -/

def l18Risk2Line4Value
    {psi kappa : Nat}
    (l r : State psi kappa) : Nat :=
  if r.leader = true then
    0
  else
    (l.dist.val + 1) % (2 * psi)

def l18Risk2PreTokenPair
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let d := PPL.determineMode l r
  let tmp : Fin (2 * psi) :=
    if d.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(d.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩
  let r1 : State psi kappa :=
    { d.2 with dist := tmp }
  let l1 : State psi kappa :=
    if r1.leader = true then
      { d.1 with last := true }
    else if
        r1.dist.val = 0 ∨
          r1.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r1.last }
  (l1, r1)

theorem l18Risk2DetermineModeFields
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.dist = l.dist ∧
      d.1.last = l.last ∧
      d.1.leader = l.leader ∧
      d.2.dist = r.dist ∧
      d.2.last = r.last ∧
      d.2.leader = r.leader := by
  simp only [PPL.determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals
    exact
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem l18Risk2PreTokenPairFields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    let p := l18Risk2PreTokenPair hpsi l r
    p.1.dist = l.dist ∧
      p.2.dist.val =
        l18Risk2Line4Value l r ∧
      p.2.last = r.last ∧
      p.1.last =
        if r.leader = true then
          true
        else if
            l18Risk2Line4Value l r = 0 ∨
              l18Risk2Line4Value l r = psi then
          false
        else
          r.last := by
  change
    let p := l18LastPreTokenPair hpsi l r
    p.1.dist = l.dist ∧
      p.2.dist.val =
        l18LastLine4Value l r ∧
      p.2.last = r.last ∧
      p.1.last =
        if r.leader = true then
          true
        else if
            l18LastLine4Value l r = 0 ∨
              l18LastLine4Value l r = psi then
          false
        else
          r.last
  exact
    l18LastPreTokenPairFields
      hpsi l r

theorem l18Risk2MoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := PPL.moveToken hpsi kind l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
  exact
    l18LastMoveTokenDistLast
      hpsi kind l r

theorem l18Risk2PPrimeMoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let q := pprimeMoveToken hpsi kind l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
  exact
    l18LastPPrimeMoveTokenDistLast
      hpsi kind l r

theorem l18Risk2EliminateDistLast
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let q := PPL.eliminateLeaders l r
    q.1.dist = l.dist ∧
      q.1.last = l.last ∧
      q.2.dist = r.dist ∧
      q.2.last = r.last := by
  exact
    l18LastEliminateDistLast l r

theorem l18Risk2PPrimeCreateLeaderFields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    let q := pprimeCreateLeader hpsi l r
    q.1.dist = l.dist ∧
      q.2.dist.val =
        l18Risk2Line4Value l r ∧
      q.2.last = r.last ∧
      q.1.last =
        if r.leader = true then
          true
        else if
            l18Risk2Line4Value l r = 0 ∨
              l18Risk2Line4Value l r = psi then
          false
        else
          r.last := by
  change
    let q := pprimeCreateLeader hpsi l r
    q.1.dist = l.dist ∧
      q.2.dist.val =
        l18LastLine4Value l r ∧
      q.2.last = r.last ∧
      q.1.last =
        if r.leader = true then
          true
        else if
            l18LastLine4Value l r = 0 ∨
              l18LastLine4Value l r = psi then
          false
        else
          r.last
  exact
    l18LastPPrimeCreateLeaderFields
      hpsi l r
theorem l18Risk2PPrimePplFields
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    let q := pprimePpl hpsi l r
    q.1.dist = l.dist ∧
      q.2.dist.val =
        l18Risk2Line4Value l r ∧
      q.2.last = r.last ∧
      q.1.last =
        if r.leader = true then
          true
        else if
            l18Risk2Line4Value l r = 0 ∨
              l18Risk2Line4Value l r = psi then
          false
        else
          r.last := by
  change
    let q := pprimePpl hpsi l r
    q.1.dist = l.dist ∧
      q.2.dist.val =
        l18LastLine4Value l r ∧
      q.2.last = r.last ∧
      q.1.last =
        if r.leader = true then
          true
        else if
            l18LastLine4Value l r = 0 ∨
              l18LastLine4Value l r = psi then
          false
        else
          r.last
  exact
    l18LastPPrimePplFields
      hpsi l r
theorem l18Risk2UntouchedFrame
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    pprimeStep ring C e i = C i := by
  exact
    l18LastUntouchedFrame
      ring C e i hie hir

theorem l18Risk2PPrimeStepLeft
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    pprimeStep ring C e e =
      (pprimePpl hpsi
        (C e)
        (C (ring.rightNeighbor e))).1 := by
  exact
    l18LastPPrimeStepLeft
      hpsi ring C e

theorem l18Risk2PPrimeStepRight
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    pprimeStep ring C e
        (ring.rightNeighbor e) =
      (pprimePpl hpsi
        (C e)
        (C (ring.rightNeighbor e))).2 := by
  exact
    l18LastPPrimeStepRight
      hn3 hpsi ring C e

/-! -------------------------------------------------------------------------
    Canonical selected pair inside S0
------------------------------------------------------------------------- -/

theorem l18Risk2CanonicalPairFacts
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (hC : CDLAt ring root C) :
    let e := PPL.shiftRight ring root j
    let r := ring.rightNeighbor e
    PPL.cyclicOffset ring root e = j ∧
      r = PPL.shiftRight ring root (j + 1) ∧
      PPL.cyclicOffset ring root r = j + 1 ∧
      (C e).dist.val = j ∧
      (C e).last = false ∧
      (C r).dist.val = j + 1 ∧
      (C r).leader = false ∧
      l18Risk2Line4Value (C e) (C r) =
        j + 1 := by
  let e := PPL.shiftRight ring root j
  let r := ring.rightNeighbor e
  have heoff :
      PPL.cyclicOffset ring root e = j := by
    dsimp only [e]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root j (by omega)
  have hrsite :
      r = PPL.shiftRight ring root (j + 1) := by
    dsimp only [r, e]
    exact l18Risk2RightNeighbor_shiftRight
      ring root j
  have hroff :
      PPL.cyclicOffset ring root r =
        j + 1 := by
    rw [hrsite]
    exact
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root (j + 1) (by omega)

  have hthr :=
    l18Risk2Threshold_ge_psi hpsi hlt

  have heGeom := hC.2.2 e
  dsimp only at heGeom
  have hedist :
      (C e).dist.val = j := by
    have h := heGeom.1
    rw [heoff,
      Nat.mod_eq_of_lt (by omega : j < 2 * psi)] at h
    exact h
  have helast :
      (C e).last = false := by
    cases hlast : (C e).last with
    | false =>
        rfl
    | true =>
        have ht := heGeom.2.mp hlast
        rw [heoff] at ht
        omega

  have hrGeom := hC.2.2 r
  dsimp only at hrGeom
  have hrdist :
      (C r).dist.val = j + 1 := by
    have h := hrGeom.1
    rw [hroff,
      Nat.mod_eq_of_lt
        (by omega : j + 1 < 2 * psi)] at h
    exact h

  have hrne : r ≠ root := by
    intro hre
    have h0 :
        PPL.cyclicOffset ring root r = 0 := by
      rw [hre, l18Risk2CyclicOffset_self]
    rw [hroff] at h0
    omega
  have hrleader :
      (C r).leader = false := by
    cases hl : (C r).leader with
    | false =>
        rfl
    | true =>
        have hre : r = root :=
          (hC.2.1 r).mp hl
        exact False.elim (hrne hre)

  have hline :
      l18Risk2Line4Value (C e) (C r) =
        j + 1 := by
    unfold l18Risk2Line4Value
    have hnotLeader :
        (C r).leader ≠ true := by
      rw [hrleader]
      decide
    rw [if_neg hnotLeader, hedist,
      Nat.mod_eq_of_lt
        (by omega : j + 1 < 2 * psi)]

  exact
    ⟨heoff, hrsite, hroff,
      hedist, helast, hrdist,
      hrleader, hline⟩

theorem l18Risk2SelectedPplDistLast
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (hC : CDLAt ring root C) :
    let e := PPL.shiftRight ring root j
    let r := ring.rightNeighbor e
    let q := pprimePpl hpsi (C e) (C r)
    q.1.dist = (C e).dist ∧
      q.1.last = (C e).last ∧
      q.2.dist = (C r).dist ∧
      q.2.last = (C r).last := by
  let e := PPL.shiftRight ring root j
  let r := ring.rightNeighbor e
  let q := pprimePpl hpsi (C e) (C r)
  have hf :=
    l18Risk2CanonicalPairFacts
      hpsi hlt ring root C j hj hC
  dsimp only at hf
  rcases hf with
    ⟨heoff, hrsite, hroff,
      hedist, helast, hrdist,
      hrleader, hline⟩

  have hp :=
    l18Risk2PPrimePplFields
      hpsi (C e) (C r)
  dsimp only at hp

  have hrightDist :
      q.2.dist = (C r).dist := by
    apply Fin.ext
    calc
      q.2.dist.val =
          l18Risk2Line4Value (C e) (C r) :=
        hp.2.1
      _ = j + 1 := hline
      _ = (C r).dist.val := hrdist.symm

  have hleftLast :
      q.1.last = (C e).last := by
    rw [hp.2.2.2, helast]
    have hnotLeader :
        (C r).leader ≠ true := by
      rw [hrleader]
      decide
    rw [if_neg hnotLeader, hline]
    by_cases hb : j + 1 = psi
    · have hborder :
          j + 1 = 0 ∨ j + 1 = psi :=
        Or.inr hb
      rw [if_pos hborder]
    · have hinner : j + 1 < psi := by
        omega
      have hrGeom := hC.2.2 r
      dsimp only at hrGeom
      have hthr :=
        l18Risk2Threshold_ge_psi hpsi hlt
      have hrlast :
          (C r).last = false := by
        cases hlast : (C r).last with
        | false =>
            rfl
        | true =>
            have ht := hrGeom.2.mp hlast
            rw [hroff] at ht
            omega
      have hne0 : j + 1 ≠ 0 := by
        omega
      have hborder :
          ¬ (j + 1 = 0 ∨ j + 1 = psi) := by
        intro h
        rcases h with h0 | hp
        · exact hne0 h0
        · exact hb hp
      rw [if_neg hborder, hrlast]

  exact
    ⟨hp.1, hleftLast,
      hrightDist, hp.2.2.1⟩

theorem l18Risk2StepDistLastFrame
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (hC : CDLAt ring root C) :
    ∀ i : Fin n,
      let D :=
        pprimeStep ring C
          (PPL.shiftRight ring root j)
      (D i).dist = (C i).dist ∧
        (D i).last = (C i).last := by
  let e := PPL.shiftRight ring root j
  let r := ring.rightNeighbor e
  let D := pprimeStep ring C e
  have hp :=
    l18Risk2SelectedPplDistLast
      hpsi hlt ring root C j hj hC
  dsimp only at hp

  intro i
  dsimp only
  by_cases hie : i = e
  · subst i
    have hs :=
      l18Risk2PPrimeStepLeft
        hpsi ring C e
    rw [hs]
    exact ⟨hp.1, hp.2.1⟩
  · by_cases hir : i = r
    · subst i
      have hs :=
        l18Risk2PPrimeStepRight
          hn3 hpsi ring C e
      rw [hs]
      exact ⟨hp.2.2.1, hp.2.2.2⟩
    · have hs :
          pprimeStep ring C e i = C i := by
        exact
          l18Risk2UntouchedFrame
            ring C e i hie hir
      constructor
      · exact
          congrArg
            (fun q : State psi kappa => q.dist) hs
      · exact
          congrArg
            (fun q : State psi kappa => q.last) hs

theorem l18Risk2StepCDL
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (hC : CDLAt ring root C) :
    CDLAt ring root
      (pprimeStep ring C
        (PPL.shiftRight ring root j)) := by
  let e := PPL.shiftRight ring root j
  let D := pprimeStep ring C e
  have hstruct :=
    PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
      hn3 hpsi ring root C e
      hC.1 hC.2.1
  have hframe :=
    l18Risk2StepDistLastFrame
      hn3 hpsi hlt ring root C j hj hC

  unfold CDLAt
  refine
    ⟨hstruct.1, hstruct.2, ?_⟩
  intro i
  dsimp only
  have hc := hC.2.2 i
  dsimp only at hc
  have hf := hframe i
  dsimp only at hf
  constructor
  · rw [hf.1]
    exact hc.1
  · rw [hf.2]
    exact hc.2

/-! -------------------------------------------------------------------------
    Token at the just-processed initiator
------------------------------------------------------------------------- -/

theorem l18Risk2PreTokenPair_open
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (hinner : j + 1 < psi)
    (hC : CDLAt ring root C) :
    let e := PPL.shiftRight ring root j
    let r := ring.rightNeighbor e
    let p := l18Risk2PreTokenPair
      hpsi (C e) (C r)
    p.1.last = false ∧
      p.2.last = false := by
  let e := PPL.shiftRight ring root j
  let r := ring.rightNeighbor e
  let p := l18Risk2PreTokenPair
    hpsi (C e) (C r)
  have hf :=
    l18Risk2CanonicalPairFacts
      hpsi hlt ring root C j hj hC
  dsimp only at hf
  rcases hf with
    ⟨heoff, hrsite, hroff,
      hedist, helast, hrdist,
      hrleader, hline⟩

  have hrGeom := hC.2.2 r
  dsimp only at hrGeom
  have hthr :=
    l18Risk2Threshold_ge_psi hpsi hlt
  have hrlast :
      (C r).last = false := by
    cases hlast : (C r).last with
    | false =>
        rfl
    | true =>
        have ht := hrGeom.2.mp hlast
        rw [hroff] at ht
        omega

  have hp :=
    l18Risk2PreTokenPairFields
      hpsi (C e) (C r)
  dsimp only at hp
  have hne0 : j + 1 ≠ 0 := by
    omega
  have hnepsi : j + 1 ≠ psi := by
    omega
  constructor
  · rw [hp.2.2.2]
    have hnotLeader :
        (C r).leader ≠ true := by
      rw [hrleader]
      decide
    rw [if_neg hnotLeader, hline]
    have hborder :
        ¬ (j + 1 = 0 ∨ j + 1 = psi) := by
      intro h
      rcases h with h0 | hp
      · exact hne0 h0
      · exact hnepsi hp
    rw [if_neg hborder, hrlast]
  · exact hp.2.2.1.trans hrlast

theorem l18Risk2PPrimeMoveToken_left_code
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hlast : l.last = false)
    (hrlast : r.last = false) :
    ∀ t : TokenData psi,
      PPL.tokenAt kind
          (pprimeMoveToken hpsi kind l r).1 =
        some t →
      PPL.decodeOffset psi (PPL.tokenCode t) < 0 ∨
        PPL.decodeOffset psi (PPL.tokenCode t) =
          ((psi : Nat) : Int) := by
  intro t ht
  unfold pprimeMoveToken at ht
  dsimp only at ht
  have h :
      ∀ u : TokenData psi,
        PPL.tokenAt kind
            (PPL.moveToken hpsi kind
              l { r with mode := false }).1 =
          some u →
        PPL.decodeOffset psi
              (PPL.tokenCode u) < 0 ∨
          PPL.decodeOffset psi
              (PPL.tokenCode u) =
            ((psi : Nat) : Int) :=
    l18Risk2MoveToken_left_code
      hpsi kind l { r with mode := false }
      hlast (by simpa using hrlast)
  apply h t
  cases kind <;>
    simpa [PPL.tokenAt] using ht

theorem l18Risk2WhitePreservesBlackLeft
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    PPL.tokenAt TokenKind.black
        (pprimeMoveToken
          hpsi TokenKind.white l r).1 =
      PPL.tokenAt TokenKind.black l := by
  unfold pprimeMoveToken
  dsimp only
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi TokenKind.white
      l { r with mode := false }
  have htb :=
    congrArg
      (fun q : State psi kappa => q.tokenB) hi
  simpa
    [PPL.eraseKindToken, PPL.tokenAt]
    using htb

theorem l18Risk2EliminateLeftToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    PPL.tokenAt kind
        (PPL.eliminateLeaders l r).1 =
      PPL.tokenAt kind l := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_left
      l r
  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB) h
      simpa [PPL.Elim.otherView, PPL.tokenAt]
        using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW) h
      simpa [PPL.Elim.otherView, PPL.tokenAt]
        using ht

theorem l18Risk2PPrimeStepLeftToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    PPL.tokenAt kind
        (pprimeStep ring C e e) =
      PPL.tokenAt kind
        (pprimeCreateLeader
          hpsi (C e)
          (C (ring.rightNeighbor e))).1 := by
  rw [l18Risk2PPrimeStepLeft
    hpsi ring C e]
  change
    PPL.tokenAt kind
        (PPL.eliminateLeaders
          (pprimeCreateLeader
            hpsi (C e)
            (C (ring.rightNeighbor e))).1
          (pprimeCreateLeader
            hpsi (C e)
            (C (ring.rightNeighbor e))).2).1 =
      PPL.tokenAt kind
        (pprimeCreateLeader
          hpsi (C e)
          (C (ring.rightNeighbor e))).1
  exact
    l18Risk2EliminateLeftToken
      kind
      (pprimeCreateLeader
        hpsi (C e)
        (C (ring.rightNeighbor e))).1
      (pprimeCreateLeader
        hpsi (C e)
        (C (ring.rightNeighbor e))).2

theorem l18Risk2Current_not_risky
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat)
    (hj : j < psi)
    (hC : CDLAt ring root C) :
    ¬ Risky ring root
        (pprimeStep ring C
          (PPL.shiftRight ring root j))
        (PPL.shiftRight ring root j) := by
  by_cases hinner : j + 1 < psi
  · let e := PPL.shiftRight ring root j
    let r := ring.rightNeighbor e
    let p :=
      l18Risk2PreTokenPair
        hpsi (C e) (C r)
    let b :=
      pprimeMoveToken
        hpsi TokenKind.black p.1 p.2
    let w :=
      pprimeMoveToken
        hpsi TokenKind.white b.1 b.2
    let D := pprimeStep ring C e

    have hopen :=
      l18Risk2PreTokenPair_open
        hpsi hlt ring root C j hj
        hinner hC
    dsimp only at hopen

    have hbsafe :=
      l18Risk2PPrimeMoveToken_left_code
        hpsi TokenKind.black
        p.1 p.2 hopen.1 hopen.2

    have hbfields :=
      l18Risk2PPrimeMoveTokenDistLast
        hpsi TokenKind.black p.1 p.2
    dsimp only at hbfields
    have hbopen :
        b.1.last = false ∧
          b.2.last = false := by
      dsimp only [b]
      constructor
      · rw [hbfields.2.1, hopen.1]
      · rw [hbfields.2.2.2, hopen.2]

    have hwsafe :=
      l18Risk2PPrimeMoveToken_left_code
        hpsi TokenKind.white
        b.1 b.2 hbopen.1 hbopen.2

    have hwhiteFrame :=
      l18Risk2WhitePreservesBlackLeft
        hpsi b.1 b.2

    have hcreate :
        pprimeCreateLeader
            hpsi (C e) (C r) =
          w := by
      dsimp only [w, b, p]
      unfold
        pprimeCreateLeader
        l18Risk2PreTokenPair
      rfl

    have hstepBlack :
        PPL.tokenAt TokenKind.black
            (D e) =
          PPL.tokenAt TokenKind.black w.1 := by
      dsimp only [D]
      calc
        PPL.tokenAt TokenKind.black
            (pprimeStep ring C e e) =
          PPL.tokenAt TokenKind.black
            (pprimeCreateLeader
              hpsi (C e) (C r)).1 :=
          l18Risk2PPrimeStepLeftToken
            hpsi ring C e TokenKind.black
        _ =
          PPL.tokenAt TokenKind.black w.1 := by
            rw [hcreate]

    have hstepWhite :
        PPL.tokenAt TokenKind.white
            (D e) =
          PPL.tokenAt TokenKind.white w.1 := by
      dsimp only [D]
      calc
        PPL.tokenAt TokenKind.white
            (pprimeStep ring C e e) =
          PPL.tokenAt TokenKind.white
            (pprimeCreateLeader
              hpsi (C e) (C r)).1 :=
          l18Risk2PPrimeStepLeftToken
            hpsi ring C e TokenKind.white
        _ =
          PPL.tokenAt TokenKind.white w.1 := by
            rw [hcreate]

    have hblackSafe :
        ∀ t : TokenData psi,
          PPL.tokenAt TokenKind.black (D e) =
              some t →
            PPL.decodeOffset psi
                (PPL.tokenCode t) < 0 ∨
              PPL.decodeOffset psi
                  (PPL.tokenCode t) =
                ((psi : Nat) : Int) := by
      intro t ht
      apply hbsafe t
      have htw :
          PPL.tokenAt TokenKind.black w.1 =
            some t := by
        rw [← hstepBlack]
        exact ht
      rw [hwhiteFrame] at htw
      exact htw

    have hwhiteSafe :
        ∀ t : TokenData psi,
          PPL.tokenAt TokenKind.white (D e) =
              some t →
            PPL.decodeOffset psi
                (PPL.tokenCode t) < 0 ∨
              PPL.decodeOffset psi
                  (PPL.tokenCode t) =
                ((psi : Nat) : Int) := by
      intro t ht
      apply hwsafe t
      rw [← hstepWhite]
      exact ht

    have hnb :
        ¬ PPL.tokenRisky
            ring root D e TokenKind.black := by
      dsimp only [e, D] at hblackSafe ⊢
      exact
        l18Risk2SafeCode_not_tokenRisky
          hpsi hlt ring root
          (pprimeStep ring C
            (PPL.shiftRight ring root j))
          j hj TokenKind.black
          hblackSafe

    have hnw :
        ¬ PPL.tokenRisky
            ring root D e TokenKind.white := by
      dsimp only [e, D] at hwhiteSafe ⊢
      exact
        l18Risk2SafeCode_not_tokenRisky
          hpsi hlt ring root
          (pprimeStep ring C
            (PPL.shiftRight ring root j))
          j hj TokenKind.white
          hwhiteSafe

    intro hR
    rcases hR with hb | hw
    · exact hnb hb
    · exact hnw hw

  · have hboundary :
        j + 1 = psi := by
      omega
    exact
      l18Risk2Boundary_not_risky
        hlt ring root
        (pprimeStep ring C
          (PPL.shiftRight ring root j))
        j hboundary

/-! -------------------------------------------------------------------------
    The two-clause letter theorem
------------------------------------------------------------------------- -/

theorem l18RiskySweepLetterRow2_proved :
    L18RiskySweepLetterRow2 := by
  unfold L18RiskySweepLetterRow2
  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root C j
  intro hj hC hprefix
  dsimp only

  have hCDL :
      CDLAt ring root
        (pprimeStep ring C
          (PPL.shiftRight ring root j)) :=
    l18Risk2StepCDL
      hn3 hpsi hlt ring root C
      j hj hC

  refine ⟨hCDL, ?_⟩
  intro i hi

  by_cases hold :
      PPL.cyclicOffset ring root i < j
  · let e := PPL.shiftRight ring root j
    let r := ring.rightNeighbor e
    have heoff :
        PPL.cyclicOffset ring root e = j := by
      dsimp only [e]
      exact
        l18Risk2CyclicOffset_shiftRight_of_lt
          ring root j (by omega)
    have hrsite :
        r =
          PPL.shiftRight ring root (j + 1) := by
      dsimp only [r, e]
      exact
        l18Risk2RightNeighbor_shiftRight
          ring root j
    have hroff :
        PPL.cyclicOffset ring root r =
          j + 1 := by
      rw [hrsite]
      exact
        l18Risk2CyclicOffset_shiftRight_of_lt
          ring root (j + 1) (by omega)

    have hie : i ≠ e := by
      intro hieq
      have hoff :
          PPL.cyclicOffset ring root i = j := by
        rw [hieq, heoff]
      omega
    have hir : i ≠ r := by
      intro hireq
      have hoff :
          PPL.cyclicOffset ring root i =
            j + 1 := by
        rw [hireq, hroff]
      omega

    have hframe :
        pprimeStep ring C e i = C i :=
      l18Risk2UntouchedFrame
        ring C e i hie hir

    have holdSafe := hprefix i hold
    intro hR
    apply holdSafe
    unfold Risky PPL.tokenRisky at hR ⊢
    rw [hframe] at hR
    exact hR

  · have hioff :
        PPL.cyclicOffset ring root i = j := by
      omega
    have heoff :
        PPL.cyclicOffset ring root
            (PPL.shiftRight ring root j) =
          j :=
      l18Risk2CyclicOffset_shiftRight_of_lt
        ring root j (by omega)
    have hie :
        i = PPL.shiftRight ring root j :=
      l18Risk2CyclicOffset_injective
        ring root i
        (PPL.shiftRight ring root j)
        (hioff.trans heoff.symm)
    subst i
    exact
      l18Risk2Current_not_risky
        hn3 hpsi hlt ring root C
        j hj hC

/-! -------------------------------------------------------------------------
    Prefix induction and the one-sweep theorem
------------------------------------------------------------------------- -/

theorem l18Risk2SeqR_succ
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat) :
    PPL.seqR ring root (j + 1) =
      PPL.seqR ring root j ++
        [PPL.shiftRight ring root j] := by
  unfold PPL.seqR
  rw [List.ofFn_succ_last]
  rfl

theorem l18Risk2Run_seqR_succ
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat) :
    runPPrime ring C
        (PPL.seqR ring root (j + 1)) =
      pprimeStep ring
        (runPPrime ring C
          (PPL.seqR ring root j))
        (PPL.shiftRight ring root j) := by
  rw [l18Risk2SeqR_succ,
    runPPrime_append]
  rfl

def L18RiskySweepPrefix2
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat)
    (C : Config n psi kappa) : Prop :=
  CDLAt ring root C ∧
    ∀ i : Fin n,
      PPL.cyclicOffset ring root i < j →
      ¬ Risky ring root C i

theorem l18Risk2Prefix_run
    (hrow : L18RiskySweepLetterRow2)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hC : CDLAt ring root C) :
    ∀ j : Nat,
      j ≤ psi →
      L18RiskySweepPrefix2
        ring root j
        (runPPrime ring C
          (PPL.seqR ring root j)) := by
  intro j
  induction j with
  | zero =>
      intro _
      unfold L18RiskySweepPrefix2
      constructor
      · simpa [PPL.seqR, runPPrime]
          using hC
      · intro i hi
        omega
  | succ j ih =>
      intro hjle
      have hjlt : j < psi := by
        omega
      have hprev :=
        ih (by omega : j ≤ psi)
      have hstep :=
        hrow hn3 hpsi hlt
          ring root
          (runPPrime ring C
            (PPL.seqR ring root j))
          j hjlt
          hprev.1 hprev.2
      dsimp only at hstep
      rw [l18Risk2Run_seqR_succ]
      exact hstep

theorem l18Risk2RiskyHostOffset_lt_psi
    {n psi kappa : Nat}
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (i : Fin n)
    (hR : Risky ring root C i) :
    PPL.cyclicOffset ring root i < psi := by
  rcases hR with hB | hW
  · unfold PPL.tokenRisky at hB
    cases ht : PPL.tokenAt TokenKind.black (C i) with
    | none =>
        simp [ht] at hB
    | some t =>
        rw [ht] at hB
        dsimp only at hB
        have hin :=
          hB.2 ⟨0, by omega⟩
        have hs :
            PPL.shiftRight ring i 0 = i :=
          l18Risk2ShiftRight_zero ring i
        rw [hs] at hin
        unfold InSegment at hin
        dsimp only at hin
        have hmin :
            Nat.min psi n = psi :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        simpa [hmin] using hin.2
  · unfold PPL.tokenRisky at hW
    cases ht : PPL.tokenAt TokenKind.white (C i) with
    | none =>
        simp [ht] at hW
    | some t =>
        rw [ht] at hW
        dsimp only at hW
        have hin :=
          hW.2 ⟨0, by omega⟩
        have hs :
            PPL.shiftRight ring i 0 = i :=
          l18Risk2ShiftRight_zero ring i
        rw [hs] at hin
        unfold InSegment at hin
        dsimp only at hin
        have hmin :
            Nat.min psi n = psi :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        simpa [hmin] using hin.2

theorem l18RiskySingleSweepScopedRow_of_letterRow2
    (hrow : L18RiskySweepLetterRow2) :
    L18RiskySingleSweepScopedRow := by
  unfold L18RiskySingleSweepScopedRow
  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root C
  intro hC
  dsimp only

  have hfinal :=
    l18Risk2Prefix_run
      hrow hn3 hpsi hlt
      ring root C hC
      psi (Nat.le_refl psi)

  constructor
  · exact hfinal.1
  · intro i hR
    have hoff :
        PPL.cyclicOffset ring root i < psi :=
      l18Risk2RiskyHostOffset_lt_psi
        hlt ring root
        (runPPrime ring C
          (PPL.seqR ring root psi))
        i hR
    exact hfinal.2 i hoff hR

theorem l18RiskySingleSweepScopedRow_proved :
    L18RiskySingleSweepScopedRow := by
  exact
    l18RiskySingleSweepScopedRow_of_letterRow2
      l18RiskySweepLetterRow2_proved

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18Risk2ShiftRight_add
#print axioms PPL.Convergence.L18.l18Risk2RightNeighbor_shiftRight
#print axioms PPL.Convergence.L18.l18Risk2CyclicOffset_self
#print axioms PPL.Convergence.L18.l18Risk2CyclicOffset_shiftRight_of_lt
#print axioms PPL.Convergence.L18.l18Risk2ShiftRight_cyclicOffset
#print axioms PPL.Convergence.L18.l18Risk2CyclicOffset_injective
#print axioms PPL.Convergence.L18.l18Risk2ShiftRight_zero
#print axioms PPL.Convergence.L18.l18Risk2OutsideS0AtPsi
#print axioms PPL.Convergence.L18.l18Risk2Threshold_ge_psi
#print axioms PPL.Convergence.L18.l18Risk2SafeCode_not_tokenRisky
#print axioms PPL.Convergence.L18.l18Risk2BoundaryToken_not_risky
#print axioms PPL.Convergence.L18.l18Risk2Boundary_not_risky
#print axioms PPL.Convergence.L18.l18Risk2SourceSet_eq
#print axioms PPL.Convergence.L18.l18Risk2SourceClear_eq
#print axioms PPL.Convergence.L18.l18Risk2SourceBirth_eq
#print axioms PPL.Convergence.L18.l18Risk2MoveTokenMirror_eq
#print axioms PPL.Convergence.L18.l18Risk2NegTurnNext_decode
#print axioms PPL.Convergence.L18.l18Risk2MoveToken_left_code
#print axioms PPL.Convergence.L18.l18Risk2DetermineModeFields
#print axioms PPL.Convergence.L18.l18Risk2PreTokenPairFields
#print axioms PPL.Convergence.L18.l18Risk2MoveTokenDistLast
#print axioms PPL.Convergence.L18.l18Risk2PPrimeMoveTokenDistLast
#print axioms PPL.Convergence.L18.l18Risk2EliminateDistLast
#print axioms PPL.Convergence.L18.l18Risk2PPrimeCreateLeaderFields
#print axioms PPL.Convergence.L18.l18Risk2PPrimePplFields
#print axioms PPL.Convergence.L18.l18Risk2UntouchedFrame
#print axioms PPL.Convergence.L18.l18Risk2PPrimeStepLeft
#print axioms PPL.Convergence.L18.l18Risk2PPrimeStepRight
#print axioms PPL.Convergence.L18.l18Risk2CanonicalPairFacts
#print axioms PPL.Convergence.L18.l18Risk2SelectedPplDistLast
#print axioms PPL.Convergence.L18.l18Risk2StepDistLastFrame
#print axioms PPL.Convergence.L18.l18Risk2StepCDL
#print axioms PPL.Convergence.L18.l18Risk2PreTokenPair_open
#print axioms PPL.Convergence.L18.l18Risk2PPrimeMoveToken_left_code
#print axioms PPL.Convergence.L18.l18Risk2WhitePreservesBlackLeft
#print axioms PPL.Convergence.L18.l18Risk2EliminateLeftToken
#print axioms PPL.Convergence.L18.l18Risk2PPrimeStepLeftToken
#print axioms PPL.Convergence.L18.l18Risk2Current_not_risky
#print axioms PPL.Convergence.L18.l18RiskySweepLetterRow2_proved
#print axioms PPL.Convergence.L18.l18Risk2SeqR_succ
#print axioms PPL.Convergence.L18.l18Risk2Run_seqR_succ
#print axioms PPL.Convergence.L18.l18Risk2Prefix_run
#print axioms PPL.Convergence.L18.l18Risk2RiskyHostOffset_lt_psi
#print axioms PPL.Convergence.L18.l18RiskySingleSweepScopedRow_of_letterRow2
#print axioms PPL.Convergence.L18.l18RiskySingleSweepScopedRow_proved
