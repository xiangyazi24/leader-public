import Leader.PPL.SPLEntry.NoOvertake
import Leader.PPL.SPLEntry.EstablishmentIdAtCutPersist
import Leader.PPL.SPLEntry.HalfWordTokenHalf

/-!
# L18: target-bit writes of one prime step, with local hypotheses only

* `q9StepTargetBitStable`: the persistence step `l18PrimeStepTargetBitStable`
 needs the token half only at the firing initiator, and only for
  its `c = 1` tokens; this is the same proof with that local hypothesis.
* `q9_fire`: when the parity-colour move of a step fires its `c = 1` branch
  (open gate, live `c = 1` initiator value `t`, empty live responder slot),
  the target bit after the whole step is `tokenBitBool t`.
* `q9_fresh_correct`: a live fresh owner (of the parity colour, under
  `GhostSound`, kinematics and `FreshPay`) is `CorrectToken` for pair `b`.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-- Local `c = 1` correctness at an initiator site. -/
def L18C1CorrectAt {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n)
    (A : Config n psi kappa) (e : Fin n) (b : Nat) : Prop :=
  ∀ (kind : TokenKind) (t : TokenData psi),
    PPL.tokenAt kind (A e) = some t →
    PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int) →
    PPL.ValidToken kind A e → PPL.WorkingFor ring root A e kind b →
    PPL.CorrectToken ring root A e kind b

/-- The selected `c = 1` initiator token into a target bit of `S_(b+1)` is a
valid token of `A e` working for `b`. -/
theorem q9C1Origin
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : b < l18BlockCount n psi) (A : Config n psi kappa) (e : Fin n)
    (kind : TokenKind) (l r : State psi kappa) (t : TokenData psi) (x : Nat) (hx : x < psi)
    (hsite : ring.rightNeighbor e = PPL.shiftRight ring root ((b + 1) * psi + x))
    (hlDist : l.dist = (A e).dist)
    (hlTok : PPL.tokenAt kind l = PPL.tokenAt kind (A e))
    (hsel : PPL.tokenAt kind ((q3ids% "q20256SelectedLeft") hpsi kind l r) = some t)
    (hc1 : PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int)) :
    PPL.tokenAt kind (A e) = some t ∧ PPL.ValidToken kind A e ∧
      PPL.WorkingFor ring root A e kind b := by
  have horigin :
      PPL.tokenAt kind l = some t ∧ l18Risk2LocalValid kind l t :=
    (q3ids% "q20256SelectedC1Origin") hpsi kind l r t hsel hc1
  have htC : PPL.tokenAt kind (A e) = some t := by
    rw [← hlTok]
    exact horigin.1
  have hvalid : PPL.ValidToken kind A e :=
    (q3ids% "q20256ValidOfLocal") kind A e l t hlDist horigin.1 htC horigin.2
  have htarget : PPL.tokenTargetSite ring e t = ring.rightNeighbor e := by
    unfold PPL.tokenTargetSite
    rw [hc1]
    try simp
    rfl
  have hend := l18TargetEndLt hpsi b hb
  have hdN : (b + 1) * psi + x < n := by
    simp only [Nat.add_mul, Nat.one_mul] at hend ⊢
    omega
  have hoff : PPL.cyclicOffset ring root (ring.rightNeighbor e) = (b + 1) * psi + x := by
    rw [hsite]
    exact l18Risk2CyclicOffset_shiftRight_of_lt ring root _ hdN
  have hzeta : b + 1 < PPL.segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  have hzpos : 0 < PPL.segmentCount n psi := by omega
  have hidx : (b + 1) % PPL.segmentCount n psi = b + 1 := Nat.mod_eq_of_lt hzeta
  have hle : (b + 1 + 1) * psi ≤ n := by
    simp only [Nat.add_mul, Nat.one_mul] at hend ⊢
    omega
  have hInJ : PPL.InSegment ring root psi (b + 1) (ring.rightNeighbor e) := by
    unfold PPL.InSegment
    show (b + 1) * psi ≤ PPL.cyclicOffset ring root (ring.rightNeighbor e) ∧
        PPL.cyclicOffset ring root (ring.rightNeighbor e) < Nat.min ((b + 1 + 1) * psi) n
    rw [hoff, show Nat.min _ n = _ from Nat.min_eq_left hle]
    constructor
    · omega
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
  have hwork : PPL.WorkingFor ring root A e kind b := by
    unfold PPL.WorkingFor
    rw [htC]
    dsimp only
    rw [hc1]
    refine ⟨hzpos, Or.inl ⟨by omega, ?_⟩⟩
    rw [hidx, htarget]
    exact hInJ
  exact ⟨htC, hvalid, hwork⟩

/-- Copy of the private `q2031HalfC1Bit` with the local hypothesis. -/
theorem q9HalfC1Bit
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : b < l18BlockCount n psi) (A : Config n psi kappa) (e : Fin n)
    (hC1 : L18C1CorrectAt ring root A e b)
    (kind : TokenKind) (l r : State psi kappa) (t : TokenData psi) (x : Nat) (hx : x < psi)
    (hsite : ring.rightNeighbor e = PPL.shiftRight ring root ((b + 1) * psi + x))
    (hbit :
      (A (ring.rightNeighbor e)).id =
        (if x ≤ PPL.firstZeroBit ring A (PPL.shiftRight ring root (b * psi))
          then !(A (PPL.shiftRight ring (PPL.shiftRight ring root (b * psi)) x)).id
          else (A (PPL.shiftRight ring (PPL.shiftRight ring root (b * psi)) x)).id))
    (hlDist : l.dist = (A e).dist)
    (hlTok : PPL.tokenAt kind l = PPL.tokenAt kind (A e))
    (hrId : r.id = (A (ring.rightNeighbor e)).id)
    (hsel : PPL.tokenAt kind ((q3ids% "q20256SelectedLeft") hpsi kind l r) = some t)
    (hc1 : PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int)) :
    PPL.tokenBitBool t = (PPL.sourceClear kind r).id := by
  obtain ⟨htC, hvalid, hwork⟩ :=
    q9C1Origin hpsi ring root b hb A e kind l r t x hx hsite hlDist hlTok hsel hc1
  have hend := l18TargetEndLt hpsi b hb
  have hdN : (b + 1) * psi + x < n := by
    simp only [Nat.add_mul, Nat.one_mul] at hend ⊢
    omega
  have hcorr : PPL.CorrectToken ring root A e kind b := hC1 kind t htC hc1 hvalid hwork
  have hdes := l18PrimeCorrectC1DesiredBit hpsi ring root A e b kind t htC hc1 hcorr
  dsimp only at hdes
  generalize hX :
      PPL.cyclicOffset ring (PPL.shiftRight ring root (b * psi)) (ring.rightNeighbor e) - psi
        = x' at hdes
  obtain ⟨hx', hsite', hbitT⟩ := hdes
  have hxx : x' = x := by
    have h1 : PPL.shiftRight ring root ((b + 1) * psi + x') =
        PPL.shiftRight ring root ((b + 1) * psi + x) := by
      rw [← PPL.Lemma4Generic.shiftRight_shiftRight, ← hsite', hsite]
    have h2 := congrArg (PPL.cyclicOffset ring root) h1
    have hdN' : (b + 1) * psi + x' < n := by
      simp only [Nat.add_mul, Nat.one_mul] at hend ⊢
      omega
    rw [l18Risk2CyclicOffset_shiftRight_of_lt ring root _ hdN',
      l18Risk2CyclicOffset_shiftRight_of_lt ring root _ hdN] at h2
    omega
  subst hxx
  have hclear : (PPL.sourceClear kind r).id = r.id := (q3ids% "q20256SourceClearId") kind r
  rw [hbitT, ← hbit, ← hrId, hclear]

/-- Copy of the private `q2031PPrimePplTargetRightId` with the local
hypothesis. -/
theorem q9PPrimePplTargetRightId
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n)
    (bidx : Nat) (hb : bidx < l18BlockCount n psi) (C : Config n psi kappa) (e : Fin n)
    (hC1 : L18C1CorrectAt ring root C e bidx)
    (x : Nat) (hx : x < psi)
    (hsite : ring.rightNeighbor e = PPL.shiftRight ring root ((bidx + 1) * psi + x))
    (hbit :
      (C (ring.rightNeighbor e)).id =
        (if x ≤ PPL.firstZeroBit ring C (PPL.shiftRight ring root (bidx * psi))
          then !(C (PPL.shiftRight ring (PPL.shiftRight ring root (bidx * psi)) x)).id
          else (C (PPL.shiftRight ring (PPL.shiftRight ring root (bidx * psi)) x)).id)) :
    (pprimePpl hpsi (C e) (C (ring.rightNeighbor e))).2.id = (C (ring.rightNeighbor e)).id := by
  let rsite := ring.rightNeighbor e
  let p := l18Risk2PreTokenPair hpsi (C e) (C rsite)
  have hpB0 := (q3ids% "q20256PreTokenFrame") hpsi .black (C e) (C rsite)
  have hpB :
      p.1.dist = (C e).dist ∧ p.1.id = (C e).id ∧
        PPL.tokenAt .black p.1 = PPL.tokenAt .black (C e) ∧
        p.2.last = (C rsite).last ∧ p.2.id = (C rsite).id ∧
        PPL.tokenAt .black p.2 = PPL.tokenAt .black (C rsite) ∧
        ((C rsite).leader = true → p.1.last = true) := by
    simpa [p, rsite] using hpB0
  have hpW0 := (q3ids% "q20256PreTokenFrame") hpsi .white (C e) (C rsite)
  have hpW :
      p.1.dist = (C e).dist ∧ p.1.id = (C e).id ∧
        PPL.tokenAt .white p.1 = PPL.tokenAt .white (C e) ∧
        p.2.last = (C rsite).last ∧ p.2.id = (C rsite).id ∧
        PPL.tokenAt .white p.2 = PPL.tokenAt .white (C rsite) ∧
        ((C rsite).leader = true → p.1.last = true) := by
    simpa [p, rsite] using hpW0
  have hblackSafe :
      ∀ (t : TokenData psi),
        (PPL.sourceClear .black p.1).last = false →
        (PPL.sourceClear .black { p.2 with mode := false }).last = false →
        PPL.tokenAt .black
            ((q3ids% "q20256SelectedLeft") hpsi .black p.1 { p.2 with mode := false }) =
          some t →
        PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int) →
        PPL.tokenBitBool t = (PPL.sourceClear .black { p.2 with mode := false }).id := by
    intro t _hl _hr hsel hc1
    exact q9HalfC1Bit hpsi ring root bidx hb C e hC1 .black p.1 { p.2 with mode := false } t x hx
      hsite hbit hpB.1 hpB.2.2.1 (by simpa using hpB.2.2.2.2.1) hsel hc1
  let black := pprimeMoveToken hpsi .black p.1 p.2
  have hblack0 := (q3ids% "q20256PPrimeMoveTokenIds") hpsi .black p.1 p.2 hblackSafe
  have hblack : black.1.id = p.1.id ∧ black.2.id = p.2.id := by
    simpa [black] using hblack0
  have hblackGeom0 := l18Risk2PPrimeMoveTokenDistLast hpsi .black p.1 p.2
  have hblackGeom :
      black.1.dist = p.1.dist ∧ black.1.last = p.1.last ∧
        black.2.dist = p.2.dist ∧ black.2.last = p.2.last := by
    simpa [black] using hblackGeom0
  have hwhiteTok : PPL.tokenAt .white black.1 = PPL.tokenAt .white (C e) := by
    have h0 : PPL.tokenAt .white (pprimeMoveToken hpsi .black p.1 p.2).1 =
        PPL.tokenAt .white p.1 :=
      (q3ids% "q20256PPrimeBlackPreservesWhiteLeft") hpsi p.1 p.2
    calc
      PPL.tokenAt .white black.1 = PPL.tokenAt .white p.1 := h0
      _ = PPL.tokenAt .white (C e) := hpW.2.2.1
  have hwhiteSafe :
      ∀ (t : TokenData psi),
        (PPL.sourceClear .white black.1).last = false →
        (PPL.sourceClear .white { black.2 with mode := false }).last = false →
        PPL.tokenAt .white
            ((q3ids% "q20256SelectedLeft") hpsi .white black.1 { black.2 with mode := false }) =
          some t →
        PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int) →
        PPL.tokenBitBool t = (PPL.sourceClear .white { black.2 with mode := false }).id := by
    intro t _hl _hr hsel hc1
    exact q9HalfC1Bit hpsi ring root bidx hb C e hC1 .white black.1
      { black.2 with mode := false } t x hx hsite hbit (hblackGeom.1.trans hpW.1) hwhiteTok
      (by
        calc
          ({ black.2 with mode := false } : State psi kappa).id = black.2.id := rfl
          _ = p.2.id := hblack.2
          _ = (C rsite).id := hpW.2.2.2.2.1)
      hsel hc1
  let white := pprimeMoveToken hpsi .white black.1 black.2
  have hwhite0 := (q3ids% "q20256PPrimeMoveTokenIds") hpsi .white black.1 black.2 hwhiteSafe
  have hwhite : white.1.id = black.1.id ∧ white.2.id = black.2.id := by
    simpa [white] using hwhite0
  have hcreate : pprimeCreateLeader hpsi (C e) (C rsite) = white := by rfl
  unfold pprimePpl
  rw [hcreate]
  have helim : (PPL.eliminateLeaders white.1 white.2).2.id = white.2.id :=
    (q3ids% "q20256EliminateRightId") white.1 white.2
  calc
    (PPL.eliminateLeaders white.1 white.2).2.id = white.2.id := helim
    _ = black.2.id := hwhite.2
    _ = p.2.id := hblack.2
    _ = (C rsite).id := hpB.2.2.2.2.1

/-- Local form of `l18PrimeStepTargetBitStable`. -/
theorem q9StepTargetBitStable
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : b < l18BlockCount n psi) (A : Config n psi kappa) (e : Fin n)
    (x : Nat) (hx : x < psi)
    (hC1 : ring.rightNeighbor e = PPL.shiftRight ring root ((b + 1) * psi + x) →
      L18C1CorrectAt ring root A e b)
    (hbit :
      (A (PPL.shiftRight ring root ((b + 1) * psi + x))).id =
        (if x ≤ PPL.firstZeroBit ring A (PPL.shiftRight ring root (b * psi))
          then !(A (PPL.shiftRight ring (PPL.shiftRight ring root (b * psi)) x)).id
          else (A (PPL.shiftRight ring (PPL.shiftRight ring root (b * psi)) x)).id)) :
    (pprimeStep ring A e (PPL.shiftRight ring root ((b + 1) * psi + x))).id =
      (A (PPL.shiftRight ring root ((b + 1) * psi + x))).id := by
  let i := PPL.shiftRight ring root ((b + 1) * psi + x)
  let rsite := ring.rightNeighbor e
  by_cases hie : i = e
  · have hleft : (pprimePpl hpsi (A e) (A rsite)).1.id = (A e).id :=
      (q3ids% "q20256PPrimePplLeftId") hpsi (A e) (A rsite)
    calc
      (pprimeStep ring A e i).id = (pprimeStep ring A e e).id := by rw [hie]
      _ = (pprimePpl hpsi (A e) (A rsite)).1.id := by rw [l18Risk2PPrimeStepLeft hpsi ring A e]
      _ = (A e).id := hleft
      _ = (A i).id := by rw [hie]
  · by_cases hir : i = rsite
    · have hr := q9PPrimePplTargetRightId hpsi ring root b hb A e (hC1 hir.symm) x hx
        (by exact hir.symm)
        (by
          have h : (A rsite).id = (A i).id := by rw [hir]
          exact h.trans hbit)
      calc
        (pprimeStep ring A e i).id = (pprimeStep ring A e rsite).id := by rw [hir]
        _ = (pprimePpl hpsi (A e) (A rsite)).2.id := by
          dsimp only [rsite]
          rw [l18Risk2PPrimeStepRight hn3 hpsi ring A e]
        _ = (A rsite).id := hr
        _ = (A i).id := by rw [hir]
    · have hsame : pprimeStep ring A e i = A i :=
        l18Risk2UntouchedFrame ring A e i hie (by simpa [rsite] using hir)
      exact congrArg (fun q : State psi kappa => q.id) hsame

/-! ## The firing write -/

theorem q9_sc_tok {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    PPL.tokenAt kind (PPL.sourceClear kind q) = q3GLiveValue kind q := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid q3GLiveValue
  cases hq : PPL.tokenAt kind q with
  | none => simp only [hq]
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · have hv' : q3GLocalValid kind q t := hv
        simp only [hv, hv', if_true, hq]
      · have hv' : ¬ q3GLocalValid kind q t := hv
        simp only [hv, hv', if_false]
        unfold l18Risk2SetToken
        cases kind <;> rfl

theorem q9_sc_last {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    (PPL.sourceClear kind q).last = q.last := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none => rfl
  | some t =>
      by_cases hv : l18Risk2LocalValid kind q t
      · simp only [hv, if_true]
      · simp only [hv, if_false]
        unfold l18Risk2SetToken
        cases kind <;> rfl

theorem q9_mode_live {psi kappa : Nat} (kind : TokenKind) (q : State psi kappa) :
    q3GLiveValue kind { q with mode := false } = q3GLiveValue kind q := by
  cases kind <;> rfl

/-- The parity-colour `c = 1` branch writes its bit into the target site,
and the rest of the step keeps it. -/
theorem q9_fire
    {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : b < l18BlockCount n psi) (A : Config n psi kappa) (e : Fin n)
    (hCDL : CDLAt ring root A)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (x : Nat) (hx : x < psi)
    (hsite : ring.rightNeighbor e = PPL.shiftRight ring root ((b + 1) * psi + x))
    (t : TokenData psi)
    (hLV : q3GLiveValue kind (q3LState hpsi kind (A e) (A (ring.rightNeighbor e))) = some t)
    (hc1 : PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int))
    (hgate : (q3LState hpsi kind (A e) (A (ring.rightNeighbor e))).last = false ∧
      (q3RState hpsi kind (A e) (A (ring.rightNeighbor e))).last = false)
    (hRV : q3GLiveValue kind (q3RState hpsi kind (A e) (A (ring.rightNeighbor e))) = none) :
    (pprimeStep ring A e (ring.rightNeighbor e)).id = PPL.tokenBitBool t := by
  let rsite := ring.rightNeighbor e
  let p := l18Risk2PreTokenPair hpsi (A e) (A rsite)
  have hpre : q3GPrelude hpsi (A e) (A rsite) = p := rfl
  let black := pprimeMoveToken hpsi .black p.1 p.2
  let white := pprimeMoveToken hpsi .white black.1 black.2
  have hcreate : pprimeCreateLeader hpsi (A e) (A rsite) = white := by rfl
  have hstep : (pprimeStep ring A e rsite).id = white.2.id := by
    dsimp only [rsite]
    rw [l18Risk2PPrimeStepRight hn3 hpsi ring A e]
    unfold pprimePpl
    rw [hcreate]
    exact (q3ids% "q20256EliminateRightId") white.1 white.2
  rw [hstep]
  cases kind with
  | black =>
      have hb0 : b % 2 = 0 := by
        rcases hpar with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · cases h
      have hL : q3LState hpsi .black (A e) (A rsite) = p.1 := by
        show (q3GPrelude hpsi (A e) (A rsite)).1 = p.1; rw [hpre]
      have hR : q3RState hpsi .black (A e) (A rsite) = p.2 := by
        show (q3GPrelude hpsi (A e) (A rsite)).2 = p.2; rw [hpre]
      rw [hL] at hLV hgate
      rw [hR] at hgate hRV
      have hwrite : black.2.id = PPL.tokenBitBool t :=
        l18PrimePPrimeMoveTokenC1Write hpsi .black p.1 p.2 t
          ⟨by rw [q9_sc_last]; exact hgate.1, by rw [q9_sc_last]; exact hgate.2⟩
          (by rw [q9_sc_tok]; exact hLV)
          (by rw [q9_sc_tok, q9_mode_live]; exact hRV) hc1
      -- the white move cannot write: a white c=1 writer would be working for b
      have hpW0 := (q3ids% "q20256PreTokenFrame") hpsi .white (A e) (A rsite)
      have hpW : p.1.dist = (A e).dist ∧ p.1.id = (A e).id ∧
          PPL.tokenAt .white p.1 = PPL.tokenAt .white (A e) ∧
          p.2.last = (A rsite).last ∧ p.2.id = (A rsite).id ∧
          PPL.tokenAt .white p.2 = PPL.tokenAt .white (A rsite) ∧
          ((A rsite).leader = true → p.1.last = true) := by
        simpa [p, rsite] using hpW0
      have hblackGeom0 := l18Risk2PPrimeMoveTokenDistLast hpsi .black p.1 p.2
      have hblackGeom : black.1.dist = p.1.dist ∧ black.1.last = p.1.last ∧
          black.2.dist = p.2.dist ∧ black.2.last = p.2.last := by
        simpa [black] using hblackGeom0
      have hwhiteTok : PPL.tokenAt .white black.1 = PPL.tokenAt .white (A e) := by
        have h0 : PPL.tokenAt .white (pprimeMoveToken hpsi .black p.1 p.2).1 =
            PPL.tokenAt .white p.1 :=
          (q3ids% "q20256PPrimeBlackPreservesWhiteLeft") hpsi p.1 p.2
        exact h0.trans hpW.2.2.1
      have hwhiteSafe :
          ∀ (t' : TokenData psi),
            (PPL.sourceClear .white black.1).last = false →
            (PPL.sourceClear .white { black.2 with mode := false }).last = false →
            PPL.tokenAt .white
                ((q3ids% "q20256SelectedLeft") hpsi .white black.1
                  { black.2 with mode := false }) = some t' →
            PPL.decodeOffset psi (PPL.tokenCode t') = (1 : Int) →
            PPL.tokenBitBool t' =
              (PPL.sourceClear .white { black.2 with mode := false }).id := by
        intro t' _hl _hr hsel hc1'
        exfalso
        obtain ⟨_, hvalid, hwork⟩ := q9C1Origin hpsi ring root b hb A e .white black.1
          { black.2 with mode := false } t' x hx hsite (hblackGeom.1.trans hpW.1) hwhiteTok
          hsel hc1'
        rcases l18ValidWorking_parity hpsi ring root b hb A hCDL .white e hvalid hwork with
          ⟨h, _⟩ | ⟨_, h⟩
        · cases h
        · omega
      have hwhite0 := (q3ids% "q20256PPrimeMoveTokenIds") hpsi .white black.1 black.2 hwhiteSafe
      have hwhite : white.1.id = black.1.id ∧ white.2.id = black.2.id := by
        simpa [white] using hwhite0
      rw [hwhite.2, hwrite]
  | white =>
      have hL : q3LState hpsi .white (A e) (A rsite) = black.1 := by
        show (pprimeMoveToken hpsi .black (q3GPrelude hpsi (A e) (A rsite)).1
          (q3GPrelude hpsi (A e) (A rsite)).2).1 = black.1
        rw [hpre]
      have hR : q3RState hpsi .white (A e) (A rsite) = black.2 := by
        show (pprimeMoveToken hpsi .black (q3GPrelude hpsi (A e) (A rsite)).1
          (q3GPrelude hpsi (A e) (A rsite)).2).2 = black.2
        rw [hpre]
      rw [hL] at hLV hgate
      rw [hR] at hgate hRV
      exact l18PrimePPrimeMoveTokenC1Write hpsi .white black.1 black.2 t
        ⟨by rw [q9_sc_last]; exact hgate.1, by rw [q9_sc_last]; exact hgate.2⟩
        (by rw [q9_sc_tok]; exact hLV)
        (by rw [q9_sc_tok, q9_mode_live]; exact hRV) hc1

/-! ## Fresh owners are correct -/

/-- A live fresh owner of the parity colour is `CorrectToken` for pair `b`. -/
theorem q9_fresh_correct {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (G : GhostConfig n psi kappa) (hsound : GhostSound G)
    (hkin : Lemma4FreshKinematics ring (shiftRight ring root (b * psi)) G)
    (hF : FreshPay ring kind (shiftRight ring root (b * psi)) G)
    (i : Fin n) (z : GhostToken n psi)
    (hz : ghostTokenAt kind G i = some z)
    (hfr : FreshAt kind (shiftRight ring root (b * psi)) z.lmeta) :
    CorrectToken ring root G.phys i kind b := by
  have hend := wc_blockEnd hpsi b hb
  have h2n : 2 * psi ≤ (b + 2) * psi := Nat.mul_le_mul_right _ (by omega)
  have hs : tokenAt kind (G.phys i) = some z.value := (q8_sound G hsound kind i z hz).1
  obtain ⟨x', hix', htraj⟩ := hkin kind i z hz hfr
  obtain ⟨hqlt, hpay⟩ := hF i z hz hfr
  unfold CorrectToken
  rw [hs]
  dsimp only
  refine ⟨?_, ?_⟩
  · rcases hpar with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h
  generalize hcdef : decodeOffset psi (tokenCode z.value) = c at htraj ⊢
  rcases htraj with ⟨q, hc, hcle, hxq, hmv⟩ | ⟨q, hc, hcle, hxq, hmv⟩
  · have hqd : z.lmeta.moves / (2 * psi - 1) = q := by
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
  · have hqd : z.lmeta.moves / (2 * psi - 1) = q := by
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

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q9StepTargetBitStable
#print axioms PPL.Convergence.L18.q9_fire
#print axioms PPL.Convergence.L18.q9_fresh_correct
