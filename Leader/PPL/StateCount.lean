import Leader.Wu.Protocol.FiniteState

/-!
# Literal local state of Yokota--Sudo--Ooshita--Masuzawa P_PL v2

This file transcribes only the simultaneous fields listed in Algorithm 1 of
arXiv:2305.08375v2.  It does not transcribe the transition or assert the
paper's convergence theorem.  The purpose is to pin down the exact literal
state count independently of asymptotic prose.
-/

namespace PPLv2

/-- A non-bottom token carries one of `2 * psi - 1` nonzero signed offsets,
one payload bit, and one carry bit. -/
abbrev Token (psi : Nat) :=
  Option ((Fin (2 * psi - 1) × Fin 2) × Fin 2)

/-- The six Boolean fields, grouped only to keep the enumeration balanced. -/
abbrev SixBits := ((Bool × Bool) × (Bool × Bool)) × (Bool × Bool)

/-- The literal Cartesian carrier displayed in Algorithm 1.  `kappa` is the
maximum value of both the clock and reset-signal TTL fields. -/
structure State (psi kappa : Nat) where
  leader : Bool
  id : Bool
  dist : Fin (2 * psi)
  last : Bool
  tokenB : Token psi
  tokenW : Token psi
  mode : Bool
  clock : Fin (kappa + 1)
  signalR : Fin (kappa + 1)
  hits : Fin (psi + 1)
  bullet : Fin 3
  shield : Bool
  signalB : Bool
  deriving DecidableEq

private abbrev Code (psi kappa : Nat) :=
  ((((SixBits × Fin 3) × Fin (2 * psi)) × (Token psi × Token psi)) ×
    (Fin (kappa + 1) × Fin (kappa + 1))) × Fin (psi + 1)

private def tokenSource (psi : Nat) : ExhaustiveList (Token psi) :=
  (ExhaustiveList.prod
    (ExhaustiveList.prod (ExhaustiveList.fin (2 * psi - 1))
      (ExhaustiveList.fin 2))
    (ExhaustiveList.fin 2)).option

private def sixBitsSource : ExhaustiveList SixBits :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool)
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))
    (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool)

private def codeSource (psi kappa : Nat) :
    ExhaustiveList (Code psi kappa) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod
        (ExhaustiveList.prod
          (ExhaustiveList.prod sixBitsSource (ExhaustiveList.fin 3))
          (ExhaustiveList.fin (2 * psi)))
        (ExhaustiveList.prod (tokenSource psi) (tokenSource psi)))
      (ExhaustiveList.prod (ExhaustiveList.fin (kappa + 1))
        (ExhaustiveList.fin (kappa + 1))))
    (ExhaustiveList.fin (psi + 1))

private theorem tokenSource_nodup (psi : Nat) :
    (tokenSource psi).values.Nodup := by
  apply ExhaustiveList.values_nodup_option
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_fin _
    · exact ExhaustiveList.values_nodup_fin _
  · exact ExhaustiveList.values_nodup_fin _

private theorem sixBitsSource_nodup : sixBitsSource.values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_prod _ _
        ExhaustiveList.values_nodup_bool ExhaustiveList.values_nodup_bool
    · exact ExhaustiveList.values_nodup_prod _ _
        ExhaustiveList.values_nodup_bool ExhaustiveList.values_nodup_bool
  · exact ExhaustiveList.values_nodup_prod _ _
      ExhaustiveList.values_nodup_bool ExhaustiveList.values_nodup_bool

private theorem codeSource_nodup (psi kappa : Nat) :
    (codeSource psi kappa).values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    (ExhaustiveList.values_nodup_prod _ _
      (ExhaustiveList.values_nodup_prod _ _
        (ExhaustiveList.values_nodup_prod _ _
          (ExhaustiveList.values_nodup_prod _ _
            sixBitsSource_nodup (ExhaustiveList.values_nodup_fin _))
          (ExhaustiveList.values_nodup_fin _))
        (ExhaustiveList.values_nodup_prod _ _
          (tokenSource_nodup psi) (tokenSource_nodup psi)))
      (ExhaustiveList.values_nodup_prod _ _
        (ExhaustiveList.values_nodup_fin _)
        (ExhaustiveList.values_nodup_fin _)))
    (ExhaustiveList.values_nodup_fin _)

private def ofCode {psi kappa : Nat} (x : Code psi kappa) : State psi kappa :=
  let bits := x.1.1.1.1.1
  {
    leader := bits.1.1.1
    id := bits.1.1.2
    dist := x.1.1.1.2
    last := bits.1.2.1
    tokenB := x.1.1.2.1
    tokenW := x.1.1.2.2
    mode := bits.1.2.2
    clock := x.1.2.1
    signalR := x.1.2.2
    hits := x.2
    bullet := x.1.1.1.1.2
    shield := bits.2.1
    signalB := bits.2.2
  }

private def toCode {psi kappa : Nat} (q : State psi kappa) : Code psi kappa :=
  ((((((((q.leader, q.id), (q.last, q.mode)), (q.shield, q.signalB)), q.bullet),
      q.dist), (q.tokenB, q.tokenW)), (q.clock, q.signalR)), q.hits)

private theorem ofCode_toCode {psi kappa : Nat} (q : State psi kappa) :
    ofCode (toCode q) = q := by
  cases q
  rfl

private theorem toCode_ofCode {psi kappa : Nat} (x : Code psi kappa) :
    toCode (ofCode x) = x := by
  rcases x with ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩, g⟩, h⟩,
    ⟨i, j⟩⟩, ⟨k, l⟩⟩, m⟩
  rfl

private theorem ofCode_surjective (psi kappa : Nat) :
    Function.Surjective (@ofCode psi kappa) := by
  intro q
  exact ⟨toCode q, ofCode_toCode q⟩

private theorem ofCode_injective (psi kappa : Nat) :
    Function.Injective (@ofCode psi kappa) := by
  intro x y h
  simpa [toCode_ofCode] using congrArg toCode h

/-- Duplicate-free exhaustive enumeration of the literal Algorithm-1 carrier. -/
def states (psi kappa : Nat) : ExhaustiveList (State psi kappa) :=
  ExhaustiveList.mapSurjective (codeSource psi kappa) ofCode
    (ofCode_surjective psi kappa)

/-- The enumeration has no duplicates, so its length is the semantic carrier
cardinality rather than merely an upper bound. -/
theorem states_nodup (psi kappa : Nat) :
    (states psi kappa).values.Nodup := by
  exact ExhaustiveList.values_nodup_mapSurjective
    (codeSource psi kappa) ofCode (ofCode_surjective psi kappa)
    (codeSource_nodup psi kappa) (ofCode_injective psi kappa)

/-- The finite-index decoder is a bijection onto the literal carrier. -/
theorem states_decode_bijective (psi kappa : Nat) :
    Function.Injective (states psi kappa).decode ∧
      Function.Surjective (states psi kappa).decode := by
  exact ⟨
    ExhaustiveList.decode_injective_of_values_nodup
      (states psi kappa) (states_nodup psi kappa),
    ExhaustiveList.decode_surjective (states psi kappa)⟩

/-- Number of values in one token field before simplifying the arithmetic. -/
def tokenCount (psi : Nat) : Nat := 1 + (2 * psi - 1) * 2 * 2

theorem tokenCount_eq (psi : Nat) (hpsi : 0 < psi) :
    tokenCount psi = 8 * psi - 3 := by
  simp [tokenCount]
  omega

private theorem tokenSource_length (psi : Nat) :
    (tokenSource psi).values.length = tokenCount psi := by
  simp [tokenSource, tokenCount, ExhaustiveList.option,
    ExhaustiveList.values_length_prod, ExhaustiveList.values_length_fin,
    Nat.add_comm]

private theorem sixBitsSource_length : sixBitsSource.values.length = 64 := by
  simp [sixBitsSource, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool]

/-- Exact literal-product count, before replacing `tokenCount psi` by
`8 * psi - 3`. -/
theorem states_length (psi kappa : Nat) :
    (states psi kappa).values.length =
      384 * psi * (tokenCount psi) ^ 2 * (kappa + 1) ^ 2 * (psi + 1) := by
  simp [states, codeSource, ExhaustiveList.values_length_mapSurjective,
    ExhaustiveList.values_length_prod, ExhaustiveList.values_length_fin,
    tokenSource_length, sixBitsSource_length, Nat.pow_two, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm]

/-- The paper-regime formula: each token has `8 * psi - 3` values. -/
theorem states_length_eq_paper_formula (psi kappa : Nat) (hpsi : 0 < psi) :
    (states psi kappa).values.length =
      384 * psi * (8 * psi - 3) ^ 2 * (kappa + 1) ^ 2 * (psi + 1) := by
  rw [states_length, tokenCount_eq psi hpsi]

end PPLv2
