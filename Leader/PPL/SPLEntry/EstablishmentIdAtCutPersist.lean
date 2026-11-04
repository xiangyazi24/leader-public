import Leader.PPL.SPLEntry.EstablishmentIdAtCutAssembly

/-!
# (P2) Persistence of correct target bits once the token half holds

Once the pair-`b` token half `L18TokenHalfAt ring root P b` holds (with
`Prefix b`), every prime step leaves a target bit of `S_(b+1)` that already
equals the add-one payload bit unchanged: a firing c=1 writer into that
bit is working for `b`, hence correct by the token half, hence writes the
same payload bit (`l18PrimeCorrectC1DesiredBit`).  Token half and
`Prefix b` propagate along any prime run (`l18PrimeRunTokenHalf`,
white frames proved), and `S_b` is frozen (`q20256SourceIotaProtected`).

Consequently the ID half of the establishment cut reduces to the single
trace proposition `L18PrimeLemma4LateTargetBitsRow`: unless the cut hits
SPL, each target bit is correct at some cut prefix where the token half
already holds (`l18PrimeEstablishmentIdAtCut_of_late`).
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

open Lean Elab Term Meta in
elab "q2031ids% " s:str : term => do
  let n : Name := ((((((`_private.Leader.PPL.SPLEntry.BuiltPairIds).num 0).str "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

theorem l18TargetEndLt
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (b : Nat)
    (hb : b < l18BlockCount n psi) :
    (b + 2) * psi < n := by
  have hz : b + 3 ≤ PPL.segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  unfold PPL.segmentCount at hz
  have hmul : (b + 3) * psi ≤ n + psi - 1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < psi)).mp hz
  simp [Nat.add_mul] at hmul ⊢
  omega

/-- Add-one payload bit is determined by the source bits. -/
theorem l18AddOneBit_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (A C : Config n psi kappa)
    (hsrc :
      PPL.sourceIota ring root A b = PPL.sourceIota ring root C b)
    (x : Nat)
    (hx : x < psi) :
    (if x ≤ PPL.firstZeroBit ring A (PPL.shiftRight ring root (b * psi))
      then !(A (PPL.shiftRight ring
        (PPL.shiftRight ring root (b * psi)) x)).id
      else (A (PPL.shiftRight ring
        (PPL.shiftRight ring root (b * psi)) x)).id) =
    (if x ≤ PPL.firstZeroBit ring C (PPL.shiftRight ring root (b * psi))
      then !(C (PPL.shiftRight ring
        (PPL.shiftRight ring root (b * psi)) x)).id
      else (C (PPL.shiftRight ring
        (PPL.shiftRight ring root (b * psi)) x)).id) := by
  have hsrcBit :
      ∀ y : Nat, y < psi →
        (A (PPL.shiftRight ring
          (PPL.shiftRight ring root (b * psi)) y)).id =
          (C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) y)).id := by
    intro y hy
    exact congrFun hsrc ⟨y, hy⟩
  have hfz :
      PPL.firstZeroBit ring A (PPL.shiftRight ring root (b * psi)) =
        PPL.firstZeroBit ring C (PPL.shiftRight ring root (b * psi)) := by
    unfold PPL.firstZeroBit
    apply l18FirstZeroAux_congr
    intro y _ hy2
    exact hsrcBit y (by omega)
  rw [hfz, hsrcBit x hx]

/-- A firing c=1 selected token into a target bit that already carries the
payload bit writes that same bit, under the token half. -/
private theorem q2031HalfC1Bit
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi)
    (A : Config n psi kappa)
    (e : Fin n)
    (hTok : L18TokenHalfAt ring root A b)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (x : Nat)
    (hx : x < psi)
    (hsite :
      ring.rightNeighbor e =
        PPL.shiftRight ring root ((b + 1) * psi + x))
    (hbit :
      (A (ring.rightNeighbor e)).id =
        (if x ≤ PPL.firstZeroBit ring A (PPL.shiftRight ring root (b * psi))
          then !(A (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id
          else (A (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id))
    (hlDist : l.dist = (A e).dist)
    (hlTok : PPL.tokenAt kind l = PPL.tokenAt kind (A e))
    (hrId : r.id = (A (ring.rightNeighbor e)).id)
    (hsel :
      PPL.tokenAt kind
          ((q2031ids% "q20256SelectedLeft") hpsi kind l r) =
        some t)
    (hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int)) :
    PPL.tokenBitBool t = (PPL.sourceClear kind r).id := by
  have horigin :
      PPL.tokenAt kind l = some t ∧ l18Risk2LocalValid kind l t :=
    (q2031ids% "q20256SelectedC1Origin") hpsi kind l r t hsel hc1
  have htC : PPL.tokenAt kind (A e) = some t := by
    rw [← hlTok]
    exact horigin.1
  have hvalid : PPL.ValidToken kind A e :=
    (q2031ids% "q20256ValidOfLocal")
      kind A e l t hlDist horigin.1 htC horigin.2
  have htarget :
      PPL.tokenTargetSite ring e t = ring.rightNeighbor e := by
    unfold PPL.tokenTargetSite
    rw [hc1]
    try simp
    rfl
  have hend := l18TargetEndLt hpsi b hb
  have hdN : (b + 1) * psi + x < n := by
    simp only [Nat.add_mul, Nat.one_mul] at hend ⊢
    omega
  have hoff :
      PPL.cyclicOffset ring root (ring.rightNeighbor e) =
        (b + 1) * psi + x := by
    rw [hsite]
    exact l18Risk2CyclicOffset_shiftRight_of_lt ring root _ hdN
  have hzeta : b + 1 < PPL.segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  have hzpos : 0 < PPL.segmentCount n psi := by
    omega
  have hidx : (b + 1) % PPL.segmentCount n psi = b + 1 :=
    Nat.mod_eq_of_lt hzeta
  have hle : (b + 1 + 1) * psi ≤ n := by
    simp only [Nat.add_mul, Nat.one_mul] at hend ⊢
    omega
  have hInJ :
      PPL.InSegment ring root psi (b + 1) (ring.rightNeighbor e) := by
    unfold PPL.InSegment
    show
      (b + 1) * psi ≤ PPL.cyclicOffset ring root (ring.rightNeighbor e) ∧
        PPL.cyclicOffset ring root (ring.rightNeighbor e) <
          Nat.min ((b + 1 + 1) * psi) n
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
  have hcorr : PPL.CorrectToken ring root A e kind b := by
    cases kind with
    | black => exact (hTok e).1 ⟨hvalid, hwork⟩
    | white => exact (hTok e).2 ⟨hvalid, hwork⟩
  have hdes :=
    l18PrimeCorrectC1DesiredBit hpsi ring root A e b kind t htC hc1 hcorr
  dsimp only at hdes
  generalize hX :
      PPL.cyclicOffset ring (PPL.shiftRight ring root (b * psi))
          (ring.rightNeighbor e) - psi = x' at hdes
  obtain ⟨hx', hsite', hbitT⟩ := hdes
  have hxx : x' = x := by
    have h1 :
        PPL.shiftRight ring root ((b + 1) * psi + x') =
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
  have hclear : (PPL.sourceClear kind r).id = r.id :=
    (q2031ids% "q20256SourceClearId") kind r
  rw [hbitT, ← hbit, ← hrId, hclear]

/-- The prime responder keeps a target bit that already carries the
payload bit, under the token half. -/
private theorem q2031PPrimePplTargetRightId
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (bidx : Nat)
    (hb : bidx < l18BlockCount n psi)
    (C : Config n psi kappa)
    (e : Fin n)
    (hTok : L18TokenHalfAt ring root C bidx)
    (x : Nat)
    (hx : x < psi)
    (hsite :
      ring.rightNeighbor e =
        PPL.shiftRight ring root ((bidx + 1) * psi + x))
    (hbit :
      (C (ring.rightNeighbor e)).id =
        (if x ≤ PPL.firstZeroBit ring C
              (PPL.shiftRight ring root (bidx * psi))
          then !(C (PPL.shiftRight ring
            (PPL.shiftRight ring root (bidx * psi)) x)).id
          else (C (PPL.shiftRight ring
            (PPL.shiftRight ring root (bidx * psi)) x)).id)) :
    (pprimePpl hpsi
        (C e) (C (ring.rightNeighbor e))).2.id =
      (C (ring.rightNeighbor e)).id := by
  let rsite := ring.rightNeighbor e
  let p := l18Risk2PreTokenPair hpsi (C e) (C rsite)

  have hpB0 :=
    (q2031ids% "q20256PreTokenFrame") hpsi .black (C e) (C rsite)
  have hpB :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        PPL.tokenAt .black p.1 = PPL.tokenAt .black (C e) ∧
        p.2.last = (C rsite).last ∧
        p.2.id = (C rsite).id ∧
        PPL.tokenAt .black p.2 = PPL.tokenAt .black (C rsite) ∧
        ((C rsite).leader = true → p.1.last = true) := by
    simpa [p, rsite] using hpB0

  have hpW0 :=
    (q2031ids% "q20256PreTokenFrame") hpsi .white (C e) (C rsite)
  have hpW :
      p.1.dist = (C e).dist ∧
        p.1.id = (C e).id ∧
        PPL.tokenAt .white p.1 = PPL.tokenAt .white (C e) ∧
        p.2.last = (C rsite).last ∧
        p.2.id = (C rsite).id ∧
        PPL.tokenAt .white p.2 = PPL.tokenAt .white (C rsite) ∧
        ((C rsite).leader = true → p.1.last = true) := by
    simpa [p, rsite] using hpW0

  have hblackSafe :
      ∀ (t : TokenData psi),
        (PPL.sourceClear .black p.1).last = false →
        (PPL.sourceClear .black { p.2 with mode := false }).last = false →
        PPL.tokenAt .black
            ((q2031ids% "q20256SelectedLeft") hpsi .black p.1
              { p.2 with mode := false }) =
          some t →
        PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int) →
        PPL.tokenBitBool t =
          (PPL.sourceClear .black { p.2 with mode := false }).id := by
    intro t _hl _hr hsel hc1
    exact
      q2031HalfC1Bit hpsi ring root bidx hb C e hTok
        .black p.1 { p.2 with mode := false } t x hx hsite hbit
        hpB.1 hpB.2.2.1
        (by simpa using hpB.2.2.2.2.1)
        hsel hc1

  let black := pprimeMoveToken hpsi .black p.1 p.2

  have hblack0 :=
    (q2031ids% "q20256PPrimeMoveTokenIds") hpsi .black p.1 p.2 hblackSafe
  have hblack : black.1.id = p.1.id ∧ black.2.id = p.2.id := by
    simpa [black] using hblack0

  have hblackGeom0 := l18Risk2PPrimeMoveTokenDistLast hpsi .black p.1 p.2
  have hblackGeom :
      black.1.dist = p.1.dist ∧
        black.1.last = p.1.last ∧
        black.2.dist = p.2.dist ∧
        black.2.last = p.2.last := by
    simpa [black] using hblackGeom0

  have hwhiteTok :
      PPL.tokenAt .white black.1 = PPL.tokenAt .white (C e) := by
    have h0 :
        PPL.tokenAt .white (pprimeMoveToken hpsi .black p.1 p.2).1 =
          PPL.tokenAt .white p.1 :=
      (q2031ids% "q20256PPrimeBlackPreservesWhiteLeft") hpsi p.1 p.2
    calc
      PPL.tokenAt .white black.1 = PPL.tokenAt .white p.1 := h0
      _ = PPL.tokenAt .white (C e) := hpW.2.2.1

  have hwhiteSafe :
      ∀ (t : TokenData psi),
        (PPL.sourceClear .white black.1).last = false →
        (PPL.sourceClear .white { black.2 with mode := false }).last =
          false →
        PPL.tokenAt .white
            ((q2031ids% "q20256SelectedLeft") hpsi .white black.1
              { black.2 with mode := false }) =
          some t →
        PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int) →
        PPL.tokenBitBool t =
          (PPL.sourceClear .white { black.2 with mode := false }).id := by
    intro t _hl _hr hsel hc1
    exact
      q2031HalfC1Bit hpsi ring root bidx hb C e hTok
        .white black.1 { black.2 with mode := false } t x hx hsite hbit
        (hblackGeom.1.trans hpW.1)
        hwhiteTok
        (by
          calc
            ({ black.2 with mode := false } : State psi kappa).id =
                black.2.id := rfl
            _ = p.2.id := hblack.2
            _ = (C rsite).id := hpW.2.2.2.2.1)
        hsel hc1

  let white := pprimeMoveToken hpsi .white black.1 black.2

  have hwhite0 :=
    (q2031ids% "q20256PPrimeMoveTokenIds") hpsi .white black.1 black.2
      hwhiteSafe
  have hwhite : white.1.id = black.1.id ∧ white.2.id = black.2.id := by
    simpa [white] using hwhite0

  have hcreate : pprimeCreateLeader hpsi (C e) (C rsite) = white := by
    rfl

  unfold pprimePpl
  rw [hcreate]
  have helim : (PPL.eliminateLeaders white.1 white.2).2.id = white.2.id :=
    (q2031ids% "q20256EliminateRightId") white.1 white.2
  calc
    (PPL.eliminateLeaders white.1 white.2).2.id = white.2.id := helim
    _ = black.2.id := hwhite.2
    _ = p.2.id := hblack.2
    _ = (C rsite).id := hpB.2.2.2.2.1

/-- (P2) One prime step keeps a target bit of `S_(b+1)` that already
carries the add-one payload bit, under the token half. -/
theorem l18PrimeStepTargetBitStable
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi)
    (A : Config n psi kappa)
    (e : Fin n)
    (hTok : L18TokenHalfAt ring root A b)
    (x : Nat)
    (hx : x < psi)
    (hbit :
      (A (PPL.shiftRight ring root ((b + 1) * psi + x))).id =
        (if x ≤ PPL.firstZeroBit ring A (PPL.shiftRight ring root (b * psi))
          then !(A (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id
          else (A (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id)) :
    (pprimeStep ring A e
        (PPL.shiftRight ring root ((b + 1) * psi + x))).id =
      (A (PPL.shiftRight ring root ((b + 1) * psi + x))).id := by
  let i := PPL.shiftRight ring root ((b + 1) * psi + x)
  let rsite := ring.rightNeighbor e
  by_cases hie : i = e
  · have hleft :
        (pprimePpl hpsi (A e) (A rsite)).1.id = (A e).id :=
      (q2031ids% "q20256PPrimePplLeftId") hpsi (A e) (A rsite)
    calc
      (pprimeStep ring A e i).id = (pprimeStep ring A e e).id := by
        rw [hie]
      _ = (pprimePpl hpsi (A e) (A rsite)).1.id := by
        rw [l18Risk2PPrimeStepLeft hpsi ring A e]
      _ = (A e).id := hleft
      _ = (A i).id := by
        rw [hie]
  · by_cases hir : i = rsite
    · have hr :=
        q2031PPrimePplTargetRightId hpsi ring root b hb A e hTok x hx
          (by exact hir.symm) (by
            have h : (A rsite).id = (A i).id := by rw [hir]
            exact h.trans hbit)
      calc
        (pprimeStep ring A e i).id = (pprimeStep ring A e rsite).id := by
          rw [hir]
        _ = (pprimePpl hpsi (A e) (A rsite)).2.id := by
          dsimp only [rsite]
          rw [l18Risk2PPrimeStepRight hn3 hpsi ring A e]
        _ = (A rsite).id := hr
        _ = (A i).id := by
          rw [hir]
    · have hsame : pprimeStep ring A e i = A i :=
        l18Risk2UntouchedFrame ring A e i hie (by simpa [rsite] using hir)
      exact congrArg (fun q : State psi kappa => q.id) hsame

/-- `S_b` is frozen along any prime run from `Prefix b`. -/
theorem l18PrimeRunSourceIotaFrozen
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi) :
    ∀ (w : DetSchedule n) (P : Config n psi kappa),
      L18BuildPrefixAt ring root b P →
      PPL.sourceIota ring root (runPPrime ring P w) b =
        PPL.sourceIota ring root P b := by
  intro w
  induction w with
  | nil =>
      intro P _
      rfl
  | cons e rest ih =>
      intro P hPrefix
      have hPrefix' :=
        l18PrimeStepPreservesBuildPrefix_of_white
          l18PrimeSelectedWhiteFrame_proved
          hn3 hpsi ring root b P e hb hPrefix
      have hstep :
          PPL.sourceIota ring root P b =
            PPL.sourceIota ring root (pprimeStep ring P e) b :=
        (q2031ids% "q20256SourceIotaProtected")
          hn3 hpsi ring root b P e hb hPrefix b (Nat.le_refl b)
      exact (ih (pprimeStep ring P e) hPrefix').trans hstep.symm

/-- (P2, run form) From `Prefix b` and the token half, a target bit that
carries `C`'s add-one payload bit (with `S_b` equal to `C`'s) keeps it along
any prime run. -/
theorem l18PrimeRunTargetBitPersists
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa)
    (x : Nat)
    (hx : x < psi) :
    ∀ (w : DetSchedule n) (P : Config n psi kappa),
      L18BuildPrefixAt ring root b P →
      L18TokenHalfAt ring root P b →
      PPL.sourceIota ring root P b = PPL.sourceIota ring root C b →
      (P (PPL.shiftRight ring root ((b + 1) * psi + x))).id =
        (if x ≤ PPL.firstZeroBit ring C (PPL.shiftRight ring root (b * psi))
          then !(C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id
          else (C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id) →
      (runPPrime ring P w
          (PPL.shiftRight ring root ((b + 1) * psi + x))).id =
        (if x ≤ PPL.firstZeroBit ring C (PPL.shiftRight ring root (b * psi))
          then !(C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id
          else (C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x)).id) := by
  intro w
  induction w with
  | nil =>
      intro P _ _ _ hbit
      exact hbit
  | cons e rest ih =>
      intro P hPrefix hTok hsrc hbit
      have hPrefix' :=
        l18PrimeStepPreservesBuildPrefix_of_white
          l18PrimeSelectedWhiteFrame_proved
          hn3 hpsi ring root b P e hb hPrefix
      have hTok' :=
        l18PrimeStepTokenHalf l18PrimeSelectedWhiteTokenHalfFrame_proved
          hn3 hpsi ring root b P e hb hPrefix hTok
      have hstepSrc :
          PPL.sourceIota ring root P b =
            PPL.sourceIota ring root (pprimeStep ring P e) b :=
        (q2031ids% "q20256SourceIotaProtected")
          hn3 hpsi ring root b P e hb hPrefix b (Nat.le_refl b)
      have hbitP := hbit
      rw [← l18AddOneBit_congr ring root b P C hsrc x hx] at hbitP
      have hstable :=
        l18PrimeStepTargetBitStable hn3 hpsi ring root b hb P e hTok x hx
          hbitP
      exact
        ih (pprimeStep ring P e) hPrefix' hTok'
          (hstepSrc.symm.trans hsrc) (hstable.trans hbit)

/-- Remaining trace input: unless the cut hits SPL, every target bit of
`S_(b+1)` carries `C`'s add-one payload bit at some cut prefix where the
pair-`b` token half already holds.  Open. -/
def L18PrimeLemma4LateTargetBitsRow : Prop :=
  ∀ {n psi kappa : Nat}
    (_hn3 : 3 ≤ n)
    (_hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (_hb : b < l18BlockCount n psi)
    (_hPrefix : L18BuildPrefixAt ring root b C)
    (_hsub :
      (PPL.lemma4Word ring
        (shiftRight ring root (b * psi)) psi).Sublist cut)
    (_hminimal :
      ∀ (cut0 tail : DetSchedule n),
        cut = cut0 ++ tail →
        tail ≠ [] →
        Not
          ((PPL.lemma4Word ring
            (shiftRight ring root (b * psi)) psi).Sublist cut0)),
    Or
      (l18HitsSPL ring root C cut = true)
      (∀ x : Fin psi,
        ∃ pre post : DetSchedule n,
          And (cut = pre ++ post)
          (And (L18TokenHalfAt ring root (runPPrime ring C pre) b)
            ((runPPrime ring C pre
                (PPL.shiftRight ring root ((b + 1) * psi + x.val))).id =
              (if x.val ≤
                  PPL.firstZeroBit ring C
                    (PPL.shiftRight ring root (b * psi))
                then
                  !(C (PPL.shiftRight ring
                    (PPL.shiftRight ring root (b * psi)) x.val)).id
                else
                  (C (PPL.shiftRight ring
                    (PPL.shiftRight ring root (b * psi)) x.val)).id))))

/-- The bit-level conclusion at the end of the cut from late target bits. -/
theorem l18PrimeLemma4EndBits_of_late
    (hLate : L18PrimeLemma4LateTargetBitsRow)
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
        (shiftRight ring root (b * psi)) psi).Sublist cut)
    (hminimal :
      ∀ (cut0 tail : DetSchedule n),
        cut = cut0 ++ tail →
        tail ≠ [] →
        Not
          ((PPL.lemma4Word ring
            (shiftRight ring root (b * psi)) psi).Sublist cut0)) :
    Or
      (l18HitsSPL ring root C cut = true)
      (And
        (PPL.sourceIota ring root (runPPrime ring C cut) b =
          PPL.sourceIota ring root C b)
        (∀ x : Fin psi,
          (runPPrime ring C cut
              (PPL.shiftRight ring root ((b + 1) * psi + x.val))).id =
            (if x.val ≤
                PPL.firstZeroBit ring C
                  (PPL.shiftRight ring root (b * psi))
              then
                !(C (PPL.shiftRight ring
                  (PPL.shiftRight ring root (b * psi)) x.val)).id
              else
                (C (PPL.shiftRight ring
                  (PPL.shiftRight ring root (b * psi)) x.val)).id))) := by
  rcases hLate hn3 hpsi ring root b C cut hb hPrefix hsub hminimal with
    hhit | hlate
  · exact Or.inl hhit
  · refine Or.inr ⟨?_, ?_⟩
    · exact l18PrimeRunSourceIotaFrozen hn3 hpsi ring root b hb cut C hPrefix
    · intro x
      obtain ⟨pre, post, hcut, hTok, hbit⟩ := hlate x
      have hPrefixP :=
        l18PrimeRunPreservesBuildPrefix_of_white
          l18PrimeSelectedWhiteFrame_proved
          hn3 hpsi ring root b C pre hb hPrefix
      have hsrcP :=
        l18PrimeRunSourceIotaFrozen hn3 hpsi ring root b hb pre C hPrefix
      have h :=
        l18PrimeRunTargetBitPersists hn3 hpsi ring root b hb C x.val x.isLt
          post (runPPrime ring C pre) hPrefixP hTok hsrcP hbit
      rw [hcut, runPPrime_append]
      exact h

/-- The bit-level persistence row from late target bits. -/
theorem l18PrimeLemma4ServicedBitsPersistBitsRow_of_late
    (hLate : L18PrimeLemma4LateTargetBitsRow) :
    L18PrimeLemma4ServicedBitsPersistBitsRow := by
  intro n psi kappa hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
    _hservices
  exact l18PrimeLemma4EndBits_of_late hLate hn3 hpsi ring root b C cut hb
    hPrefix hsub hminimal

/-- The ID half of the establishment cut from late target bits alone. -/
theorem l18PrimeEstablishmentIdAtCut_of_late
    (hLate : L18PrimeLemma4LateTargetBitsRow) :
    L18PrimeLemma4EstablishmentIdAtCutRow := by
  intro n psi kappa hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
  rcases l18PrimeLemma4EndBits_of_late hLate
      hn3 hpsi ring root b C cut hb hPrefix hsub hminimal with
    hhit | ⟨hsrc, hbits⟩
  · exact Or.inl hhit
  · exact Or.inr
      (l18PrimeSuccessorIdOfAddOneBits hpsi ring root b hb C
        (runPPrime ring C cut) hsrc hbits)

/-- A service event whose firing config already has the token half gives a
late witness for that target bit. -/
theorem l18PrimeLateWitness_of_service
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (cut pre post : DetSchedule n)
    (e : Fin n)
    (x : Fin psi)
    (hcut : cut = pre ++ e :: post)
    (hTok : L18TokenHalfAt ring root (runPPrime ring C pre) b)
    (hwrite :
      (pprimeStep ring (runPPrime ring C pre) e
          (PPL.shiftRight ring root ((b + 1) * psi + x.val))).id =
        (if x.val ≤
            PPL.firstZeroBit ring C (PPL.shiftRight ring root (b * psi))
          then !(C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x.val)).id
          else (C (PPL.shiftRight ring
            (PPL.shiftRight ring root (b * psi)) x.val)).id)) :
    ∃ pre' post' : DetSchedule n,
      And (cut = pre' ++ post')
      (And (L18TokenHalfAt ring root (runPPrime ring C pre') b)
        ((runPPrime ring C pre'
            (PPL.shiftRight ring root ((b + 1) * psi + x.val))).id =
          (if x.val ≤
              PPL.firstZeroBit ring C (PPL.shiftRight ring root (b * psi))
            then !(C (PPL.shiftRight ring
              (PPL.shiftRight ring root (b * psi)) x.val)).id
            else (C (PPL.shiftRight ring
              (PPL.shiftRight ring root (b * psi)) x.val)).id))) := by
  have hrun :
      runPPrime ring C (pre ++ [e]) =
        pprimeStep ring (runPPrime ring C pre) e := by
    rw [runPPrime_append]
    rfl
  have hPrefixP :=
    l18PrimeRunPreservesBuildPrefix_of_white
      l18PrimeSelectedWhiteFrame_proved
      hn3 hpsi ring root b C pre hb hPrefix
  refine ⟨pre ++ [e], post, ?_, ?_, ?_⟩
  · rw [hcut, List.append_assoc]
    rfl
  · rw [hrun]
    exact
      l18PrimeStepTokenHalf l18PrimeSelectedWhiteTokenHalfFrame_proved
        hn3 hpsi ring root b _ e hb hPrefixP hTok
  · rw [hrun]
    exact hwrite

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeStepTargetBitStable
#print axioms PPL.Convergence.L18.l18PrimeRunSourceIotaFrozen
#print axioms PPL.Convergence.L18.l18PrimeRunTargetBitPersists
#print axioms PPL.Convergence.L18.l18PrimeLemma4ServicedBitsPersistBitsRow_of_late
#print axioms PPL.Convergence.L18.l18PrimeEstablishmentIdAtCut_of_late
#print axioms PPL.Convergence.L18.l18PrimeLateWitness_of_service
