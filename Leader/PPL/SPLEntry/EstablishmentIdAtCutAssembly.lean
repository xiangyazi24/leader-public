import Leader.PPL.SPLEntry.EstablishmentIdAtCut
import Leader.PPL.CompletionRunner.HybridCore
import Leader.PPL.SPLEntry.EstablishmentCutHalves
import Init.Omega

/-!
# The ID half of the establishment cut, reduced to service and persistence

`L18PrimeLemma4EstablishmentIdAtCutRow` is reduced to two named
trace propositions (the (ii)/(iii) split):

* `L18PrimeLemma4EveryTargetBitServicedRow`: unless the cut hits SPL, every
  target bit `x < psi` of `S_(b+1)` receives a correct c=1 service of the
  pair-`b` colour inside the cut;
* `L18PrimeLemma4ServicedBitsPersistBitsRow`: given the services, unless the
  cut hits SPL, at the end of the cut the source bits `S_b` equal those of
  `C` and every target bit equals the add-one payload bit of `C`'s source
  (bit-level form of (iii)).

The arithmetic that turns the bit-level conclusion into the ID equation
(converse of `q20256WordAddOneBit`) is proved here
(`l18PrimeSuccessorIdOfAddOneBits`), and it also turns the bit-level
persistence row into the earlier verbatim (iii)
(`l18PrimeLemma4ServicedBitsPersistToCutRow_of_bits`).

The one-step write effect (P1) is `L18PrimeEstablishmentIdAtCut.lean`
, imported, not reproved.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/-! ## (P3) converse add-one arithmetic -/

/-- Little-endian word read from `start + j`, `len` bits. -/
def l18IdWord
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    Nat → Nat → Nat
  | 0, _ => 0
  | len + 1, j =>
      (if (C (PPL.shiftRight ring start j)).id = true then 1 else 0) +
        2 * l18IdWord ring C start len (j + 1)

theorem l18IdWord_factor
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ len j : Nat,
      PPL.segmentIdAux ring C start len j =
        2 ^ j * l18IdWord ring C start len j := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [PPL.segmentIdAux, l18IdWord]
  | succ len ih =>
      intro j
      simp only [PPL.segmentIdAux, l18IdWord]
      rw [ih (j + 1)]
      cases hb : (C (PPL.shiftRight ring start j)).id <;>
        simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc]

theorem l18SegmentIdFrom_eq_word
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n)
    (len : Nat) :
    PPL.segmentIdFrom ring C start len =
      l18IdWord ring C start len 0 := by
  unfold PPL.segmentIdFrom
  rw [l18IdWord_factor]
  simp

theorem l18IdWord_lt_pow
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ len j : Nat, l18IdWord ring C start len j < 2 ^ len := by
  intro len
  induction len with
  | zero =>
      intro j
      simp [l18IdWord]
  | succ len ih =>
      intro j
      have ht := ih (j + 1)
      cases hb : (C (PPL.shiftRight ring start j)).id <;>
        simp [l18IdWord, hb, Nat.pow_succ] <;>
        omega

/-- Words agree when the bits agree on the read range. -/
theorem l18IdWord_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (a c : Fin n) :
    ∀ fuel j : Nat,
      (∀ x : Nat, j ≤ x → x < j + fuel →
        (C (PPL.shiftRight ring a x)).id =
          (D (PPL.shiftRight ring c x)).id) →
      l18IdWord ring C a fuel j = l18IdWord ring D c fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j _
      rfl
  | succ fuel ih =>
      intro j h
      have h0 := h j (by omega) (by omega)
      have htail :=
        ih (j + 1) (fun x hx1 hx2 => h x (by omega) (by omega))
      simp only [l18IdWord]
      rw [h0, htail]

/-- `firstZeroAux` agrees when the source bits agree on the read range. -/
theorem l18FirstZeroAux_congr
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C D : Config n psi kappa)
    (a : Fin n) :
    ∀ fuel j : Nat,
      (∀ x : Nat, j ≤ x → x < j + fuel →
        (C (PPL.shiftRight ring a x)).id =
          (D (PPL.shiftRight ring a x)).id) →
      PPL.firstZeroAux ring C a fuel j =
        PPL.firstZeroAux ring D a fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j _
      rfl
  | succ fuel ih =>
      intro j h
      have h0 := h j (by omega) (by omega)
      have htail :=
        ih (j + 1) (fun x hx1 hx2 => h x (by omega) (by omega))
      simp only [PPL.firstZeroAux]
      rw [h0, htail]

theorem l18FirstZeroAux_ge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (start : Fin n) :
    ∀ fuel j : Nat, j ≤ PPL.firstZeroAux ring C start fuel j := by
  intro fuel
  induction fuel with
  | zero =>
      intro j
      simp [PPL.firstZeroAux]
  | succ fuel ih =>
      intro j
      cases hb : (C (PPL.shiftRight ring start j)).id with
      | false =>
          simp [PPL.firstZeroAux, hb]
      | true =>
          have ht := ih (j + 1)
          simp [PPL.firstZeroAux, hb]
          omega

/--
Converse of `q20256WordAddOneBit`: if every target bit is the add-one
payload bit of the source, the target word is the source word plus one.
-/
theorem l18IdWord_addOne_of_bits
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (source target : Fin n) :
    ∀ fuel j : Nat,
      (∀ x : Nat, j ≤ x → x < j + fuel →
        (C (PPL.shiftRight ring target x)).id =
          (if x ≤ PPL.firstZeroAux ring C source fuel j
            then !(C (PPL.shiftRight ring source x)).id
            else (C (PPL.shiftRight ring source x)).id)) →
      l18IdWord ring C target fuel j =
        (l18IdWord ring C source fuel j + 1) % (2 ^ fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro j _
      simp [l18IdWord]
  | succ fuel ih =>
      intro j h
      have hsLt := l18IdWord_lt_pow ring C source fuel (j + 1)
      have h0 := h j (by omega) (by omega)
      cases hs : (C (PPL.shiftRight ring source j)).id with
      | false =>
          have hfirst :
              PPL.firstZeroAux ring C source (fuel + 1) j = j := by
            simp [PPL.firstZeroAux, hs]
          have ht : (C (PPL.shiftRight ring target j)).id = true := by
            rw [h0, hfirst, hs]
            simp
          have htail :
              l18IdWord ring C target fuel (j + 1) =
                l18IdWord ring C source fuel (j + 1) := by
            apply l18IdWord_congr
            intro x hx1 hx2
            have hx := h x (by omega) (by omega)
            rw [hfirst] at hx
            have hnot : Not (x ≤ j) := by omega
            rw [if_neg hnot] at hx
            exact hx
          simp only [l18IdWord, hs, ht, htail]
          simp only [Bool.false_eq_true, if_true, if_false, Nat.pow_succ]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
      | true =>
          have hfirst :
              PPL.firstZeroAux ring C source (fuel + 1) j =
                PPL.firstZeroAux ring C source fuel (j + 1) := by
            simp [PPL.firstZeroAux, hs]
          have hge := l18FirstZeroAux_ge ring C source fuel (j + 1)
          have ht : (C (PPL.shiftRight ring target j)).id = false := by
            rw [h0, hfirst, hs, if_pos (by omega)]
            rfl
          have htail :
              l18IdWord ring C target fuel (j + 1) =
                (l18IdWord ring C source fuel (j + 1) + 1) % (2 ^ fuel) := by
            apply ih (j + 1)
            intro x hx1 hx2
            have hx := h x (by omega) (by omega)
            rw [hfirst] at hx
            exact hx
          simp only [l18IdWord, hs, ht, htail]
          simp only [Bool.false_eq_true, if_true, if_false, Nat.pow_succ]
          by_cases hsmall :
              l18IdWord ring C source fuel (j + 1) + 1 < 2 ^ fuel
          · rw [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt (by omega)]
            omega
          · have hover :
                l18IdWord ring C source fuel (j + 1) + 1 = 2 ^ fuel := by
              omega
            rw [hover, Nat.mod_self]
            have hsum :
                1 + 2 * l18IdWord ring C source fuel (j + 1) + 1 =
                  2 ^ fuel * 2 := by
              omega
            rw [hsum, Nat.mod_self]

theorem l18InteriorLengths
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (b : Nat)
    (hb : b < l18BlockCount n psi) :
    PPL.segmentLength n psi b = psi ∧
      PPL.segmentLength n psi (b + 1) = psi := by
  have hz : b + 3 ≤ PPL.segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  unfold PPL.segmentCount at hz
  have hmul : (b + 3) * psi ≤ n + psi - 1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < psi)).mp hz
  have h2 : (b + 2) * psi < n := by
    simp [Nat.add_mul] at hmul ⊢
    omega
  constructor
  · unfold PPL.segmentLength
    have hle : (b + 1) * psi ≤ n := by
      simp only [Nat.add_mul, Nat.one_mul] at h2 ⊢
      omega
    rw [show Nat.min _ n = _ from Nat.min_eq_left hle]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  · unfold PPL.segmentLength
    have hle : (b + 1 + 1) * psi ≤ n := by
      simp only [Nat.add_mul, Nat.one_mul] at h2 ⊢
      omega
    rw [show Nat.min _ n = _ from Nat.min_eq_left hle]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/--
(P3) Bits to ID equation.  If the source bits of `E` equal those of `C` and
every target bit of `E` is the add-one payload bit of `C`'s source, then the
interior successor-ID equation holds in `E`.
-/
theorem l18PrimeSuccessorIdOfAddOneBits
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (hb : b < l18BlockCount n psi)
    (C E : Config n psi kappa)
    (hsrc :
      PPL.sourceIota ring root E b = PPL.sourceIota ring root C b)
    (hbits :
      ∀ x : Fin psi,
        (E (PPL.shiftRight ring root ((b + 1) * psi + x.val))).id =
          (if x.val ≤
              PPL.firstZeroBit ring C
                (PPL.shiftRight ring root (b * psi))
            then
              !(C (PPL.shiftRight ring
                (PPL.shiftRight ring root (b * psi)) x.val)).id
            else
              (C (PPL.shiftRight ring
                (PPL.shiftRight ring root (b * psi)) x.val)).id)) :
    PPL.rootedSegmentId ring root E (b + 1) =
      (PPL.rootedSegmentId ring root E b + 1) % (2 ^ psi) := by
  let source := PPL.shiftRight ring root (b * psi)
  let target := PPL.shiftRight ring root ((b + 1) * psi)
  have hsrcBit :
      ∀ x : Nat, x < psi →
        (E (PPL.shiftRight ring source x)).id =
          (C (PPL.shiftRight ring source x)).id := by
    intro x hx
    exact congrFun hsrc ⟨x, hx⟩
  have hfz :
      PPL.firstZeroBit ring C source =
        PPL.firstZeroBit ring E source := by
    unfold PPL.firstZeroBit
    apply l18FirstZeroAux_congr
    intro x _ hx2
    exact (hsrcBit x (by omega)).symm
  have hbitsE :
      ∀ x : Nat, 0 ≤ x → x < 0 + psi →
        (E (PPL.shiftRight ring target x)).id =
          (if x ≤ PPL.firstZeroAux ring E source psi 0
            then !(E (PPL.shiftRight ring source x)).id
            else (E (PPL.shiftRight ring source x)).id) := by
    intro x _ hx2
    have hx : x < psi := by omega
    have h := hbits ⟨x, hx⟩
    have hsite :
        PPL.shiftRight ring root ((b + 1) * psi + x) =
          PPL.shiftRight ring target x :=
      (PPL.Lemma4Generic.shiftRight_shiftRight ring root _ _).symm
    rw [hsite] at h
    rw [h, hsrcBit x hx]
    have hfz' := hfz
    unfold PPL.firstZeroBit at hfz'
    exact congrArg
      (fun m => if x ≤ m
        then !(C (PPL.shiftRight ring source x)).id
        else (C (PPL.shiftRight ring source x)).id) hfz'
  have hword :=
    l18IdWord_addOne_of_bits ring E source target psi 0 hbitsE
  have hlens := l18InteriorLengths hpsi b hb
  unfold PPL.rootedSegmentId
  rw [hlens.1, hlens.2, l18SegmentIdFrom_eq_word, l18SegmentIdFrom_eq_word]
  exact hword

/-! ## (P4) the two trace propositions, and the assembly -/

/-- (ii) service event for target bit `x` of pair `b` inside `cut`
(verbatim body of `l18PrimeLemma4EveryTargetBitServiced`). -/
def L18PrimeLemma4TargetBitService
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (x : Fin psi) : Prop :=
  ∃ pre : DetSchedule n,
  ∃ e : Fin n,
  ∃ post : DetSchedule n,
  ∃ kind : TokenKind,
  ∃ t : TokenData psi,
    let A := runPPrime ring C pre
    let source := PPL.shiftRight ring root (b * psi)
    let target := PPL.shiftRight ring root ((b + 1) * psi + x.val)
    And (cut = pre ++ e :: post)
    (And (PPL.sourceIota ring root A b = PPL.sourceIota ring root C b)
    (And (kind = PPL.Lemma4Generic.l18BlockKind b)
    (And (ring.rightNeighbor e = target)
    (And (PPL.tokenAt kind (A e) = some t)
    (And (PPL.ValidToken kind A e)
    (And (PPL.WorkingFor ring root A e kind b)
    (And (PPL.CorrectToken ring root A e kind b)
    (And (PPL.decodeOffset psi (PPL.tokenCode t) = (1 : Int))
      ((pprimeStep ring A e target).id =
        (if x.val ≤ PPL.firstZeroBit ring C source
          then !(C (PPL.shiftRight ring source x.val)).id
          else (C (PPL.shiftRight ring source x.val)).id))))))))))

/-- (ii) `l18PrimeLemma4EveryTargetBitServiced`, universally
quantified.  Open. -/
def L18PrimeLemma4EveryTargetBitServicedRow : Prop :=
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
      (∀ x : Fin psi, L18PrimeLemma4TargetBitService ring root b C cut x)

/-- (iii) `l18PrimeLemma4ServicedBitsPersistToCut`, universally
quantified, verbatim conclusion (the successor-ID equation).  Open. -/
def L18PrimeLemma4ServicedBitsPersistToCutRow : Prop :=
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
            (shiftRight ring root (b * psi)) psi).Sublist cut0))
    (_hservices :
      ∀ x : Fin psi, L18PrimeLemma4TargetBitService ring root b C cut x),
    let E := runPPrime ring C cut
    Or
      (l18HitsSPL ring root C cut = true)
      (rootedSegmentId ring root E (b + 1) =
        (rootedSegmentId ring root E b + 1) % (2 ^ psi))

/-- Bit-level form of (iii): at the end of the cut, `S_b` is `C`'s
and each target bit is the add-one payload bit of `C`'s source.  Open. -/
def L18PrimeLemma4ServicedBitsPersistBitsRow : Prop :=
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
            (shiftRight ring root (b * psi)) psi).Sublist cut0))
    (_hservices :
      ∀ x : Fin psi, L18PrimeLemma4TargetBitService ring root b C cut x),
    let E := runPPrime ring C cut
    Or
      (l18HitsSPL ring root C cut = true)
      (And
        (PPL.sourceIota ring root E b = PPL.sourceIota ring root C b)
        (∀ x : Fin psi,
          (E (PPL.shiftRight ring root ((b + 1) * psi + x.val))).id =
            (if x.val ≤
                PPL.firstZeroBit ring C
                  (PPL.shiftRight ring root (b * psi))
              then
                !(C (PPL.shiftRight ring
                  (PPL.shiftRight ring root (b * psi)) x.val)).id
              else
                (C (PPL.shiftRight ring
                  (PPL.shiftRight ring root (b * psi)) x.val)).id)))

/-- The bit-level persistence row gives the earlier verbatim (iii). -/
theorem l18PrimeLemma4ServicedBitsPersistToCutRow_of_bits
    (hBits : L18PrimeLemma4ServicedBitsPersistBitsRow) :
    L18PrimeLemma4ServicedBitsPersistToCutRow := by
  intro n psi kappa hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
    hservices
  rcases hBits hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
      hservices with hhit | ⟨hsrc, hbits⟩
  · exact Or.inl hhit
  · exact Or.inr
      (l18PrimeSuccessorIdOfAddOneBits hpsi ring root b hb C
        (runPPrime ring C cut) hsrc hbits)

/-- The ID half of the establishment cut from service (ii) and
persistence (iii). -/
theorem l18PrimeEstablishmentIdAtCut_of_coverage
    (hServ : L18PrimeLemma4EveryTargetBitServicedRow)
    (hPersist : L18PrimeLemma4ServicedBitsPersistToCutRow) :
    L18PrimeLemma4EstablishmentIdAtCutRow := by
  intro n psi kappa hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
  rcases hServ hn3 hpsi ring root b C cut hb hPrefix hsub hminimal with
    hhit | hservices
  · exact Or.inl hhit
  · exact hPersist hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
      hservices

/-- Same, with the bit-level persistence row. -/
theorem l18PrimeEstablishmentIdAtCut_of_coverageBits
    (hServ : L18PrimeLemma4EveryTargetBitServicedRow)
    (hBits : L18PrimeLemma4ServicedBitsPersistBitsRow) :
    L18PrimeLemma4EstablishmentIdAtCutRow :=
  l18PrimeEstablishmentIdAtCut_of_coverage hServ
    (l18PrimeLemma4ServicedBitsPersistToCutRow_of_bits hBits)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18IdWord_addOne_of_bits
#print axioms PPL.Convergence.L18.l18PrimeSuccessorIdOfAddOneBits
#print axioms PPL.Convergence.L18.l18PrimeLemma4ServicedBitsPersistToCutRow_of_bits
#print axioms PPL.Convergence.L18.l18PrimeEstablishmentIdAtCut_of_coverage
#print axioms PPL.Convergence.L18.l18PrimeEstablishmentIdAtCut_of_coverageBits
