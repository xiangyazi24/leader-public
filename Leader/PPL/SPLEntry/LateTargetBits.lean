import Leader.PPL.SPLEntry.TargetBitWrite
import Leader.PPL.CompletionRunner.ForcedConstructTransfer

/-!
# L18: the late target-bits row, unconditionally

`l18PrimeLemma4LateTargetBitsRow_proved : L18PrimeLemma4LateTargetBitsRow`, and
with it `l18PrimeEstablishmentIdAtCut_proved`.

Route (plan (b), historical no-crossing write frame, without a tagged
second power).  Pair `b`, parity colour `kind = l18BlockKind b`, border
`k = root + b psi`, `D = 2 psi - 1`.  The service key of target bit `x` is
`K_x = x D + (psi - 1)`: the `c = 1` point at window position `x + psi - 1`
(`q6_key_service`).  Along the prime ghost run from `initialGhost C` carry
(`q10Inv`):

* `Prefix b`, `HybridInv`, `FreshPay`, ghost coverage of the window, the frozen
  source segment, colour-tagged lineage ids (`q10IdsColoured`), `NoOvertake`;
* `q10Q`: for every `x < psi`, once a fresh owner has passed key `K_x` or a
  fresh completion is logged (`q10Trig`), target bit `x` carries `C`'s add-one
  bit and every old in-window owner has key `> K_x`.

Step (`q10_inv_step`).  If the trigger held before, the bit is stable
(`q10_stable`): a valid `c = 1` token of the parity colour at the service site
has key `K_x`, so it is fresh by `OldAbove K_x` and hence correct
(`q9_fresh_correct`); the other colour is vacuous.  If the trigger fires in
this step (`q10_new`), the step moves a fresh pre-owner of key exactly `K_x`
out of the service site through the `c = 1` branch (left moves and births are
excluded by the key algebra, other-colour completions by colour tags); the
write lands its payload bit, which `FreshPay` makes `C`'s add-one bit
(`q10_establish`), and `NoOvertake` gives `OldAbove K_x`.

At the end of the cut `prime_blockCompletion_of_buildPrefix` logs a fresh
completion, so every trigger holds; the late row is taken with
`pre = cut, post = []`, the token half coming from
`l18PrimeLemma4EstablishmentTokensAtCut_proved`.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-! ## Definitions -/

/-- Every live owner in the `kind` map carries a lineage id of colour `kind`
(when it is a birth id). -/
def q10IdsColoured {n psi kappa : Nat} (G : GhostConfig n psi kappa) : Prop :=
  ∀ (kind kind' : TokenKind) (i : Fin n) (z : GhostToken n psi) (s : Nat),
    ghostTokenAt kind G i = some z → z.lmeta.id = .born kind' s → kind' = kind

/-- Trigger for target bit `x`: a fresh owner has passed its service key, or a
fresh completion is logged. -/
def q10Trig {n psi kappa : Nat} (kind : TokenKind) (k : Fin n) (x : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  (∃ (j : Fin n) (zF : GhostToken n psi), ghostTokenAt kind G j = some zF ∧
      FreshAt kind k zF.lmeta ∧ x * (2 * psi - 1) + (psi - 1) < zF.lmeta.moves) ∨
    HasFreshCompletion (psi := psi) kind k G

/-- Target bit `x` of `S_(b+1)` carries `C`'s add-one payload bit. -/
def q10Bit {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C A : Config n psi kappa) (x : Nat) : Prop :=
  (A (shiftRight ring root ((b + 1) * psi + x))).id =
    (if x ≤ firstZeroBit ring C (shiftRight ring root (b * psi))
      then !(C (shiftRight ring (shiftRight ring root (b * psi)) x)).id
      else (C (shiftRight ring (shiftRight ring root (b * psi)) x)).id)

/-- The historical write frame. -/
def q10Q {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  ∀ x : Nat, x < psi → q10Trig kind (shiftRight ring root (b * psi)) x G →
    q10Bit ring root b C G.phys x ∧
      OldAbove ring kind (shiftRight ring root (b * psi)) (x * (2 * psi - 1) + (psi - 1)) G

/-- The run invariant. -/
def q10Inv {n psi kappa : Nat} (ring : DirectedRing n) (root : Fin n) (b : Nat)
    (C : Config n psi kappa) (t : Nat) (G : GhostConfig n psi kappa) : Prop :=
  L18BuildPrefixAt ring root b G.phys ∧
    PPL.Lemma4Generic.HybridInv ring t G ∧
    FreshPay ring (PPL.Lemma4Generic.l18BlockKind b) (shiftRight ring root (b * psi)) G ∧
    Lemma4GhostCoveredWindow ring (shiftRight ring root (b * psi))
      (PPL.Lemma4Generic.l18BlockKind b) G ∧
    PPL.sourceIota ring root G.phys b = PPL.sourceIota ring root C b ∧
    q10IdsColoured G ∧
    NoOvertake ring (PPL.Lemma4Generic.l18BlockKind b) (shiftRight ring root (b * psi)) G ∧
    q10Q ring root b C (PPL.Lemma4Generic.l18BlockKind b) G

/-! ## Arithmetic -/

theorem q10_T {psi : Nat} (hpsi : 1 ≤ psi) :
    tokenTrajectoryMoves psi = (psi - 1) * (2 * psi - 1) + psi := by
  unfold tokenTrajectoryMoves
  obtain ⟨p, rfl⟩ : ∃ p, psi = p + 1 := ⟨psi - 1, by omega⟩
  have h1 : 2 * (p + 1) * (p + 1) = 2 * (p * p) + 4 * p + 2 := by
    rw [Nat.mul_assoc, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_add,
      Nat.mul_add]
    omega
  have h2 : (p + 1 - 1) * (2 * (p + 1) - 1) = 2 * (p * p) + p := by
    rw [show p + 1 - 1 = p by omega, show 2 * (p + 1) - 1 = 2 * p + 1 by omega, Nat.mul_add,
      Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm p 2, Nat.mul_assoc]
  rw [h1, h2]
  omega

theorem q10_key_service_pt {psi : Nat} (hpsi : 2 ≤ psi) (x : Nat) (hx : x < psi) :
    q6Key psi (x + psi - 1) 1 = x * (2 * psi - 1) + (psi - 1) := by
  unfold q6Key
  rw [if_pos Int.one_pos]
  show (x + psi - 1 + 1 - psi) * (2 * psi - 1) + (psi - 1) = _
  rw [show x + psi - 1 + 1 - psi = x by omega]

theorem q10_site {n : Nat} (ring : DirectedRing n) (root : Fin n) (b x y : Nat) {psi : Nat}
    (h : y + 1 = x + psi) :
    shiftRight ring root ((b + 1) * psi + x) =
      shiftRight ring (shiftRight ring root (b * psi)) (y + 1) := by
  rw [l18Gapped_shiftRight_add, h]
  congr 1
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ## Fresh owners at a service key -/

/-- A fresh owner whose move count is the service key of bit `x` holds a
`c = 1` token at window position `x + psi - 1`. -/
theorem q10_fresh_service {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (G : GhostConfig n psi kappa) (hs : GhostSound G)
    (hCd : Cd ring k kind G.phys)
    (hkin : Lemma4FreshKinematics ring k G) (hF : FreshPay ring kind k G)
    (j : Fin n) (zF : GhostToken n psi)
    (hj : ghostTokenAt kind G j = some zF) (hfr : FreshAt kind k zF.lmeta)
    (x : Nat) (hmv : zF.lmeta.moves = x * (2 * psi - 1) + (psi - 1)) :
    decodeOffset psi (tokenCode zF.value) = 1 ∧ j = shiftRight ring k (x + psi - 1) := by
  obtain ⟨y, hy, hjy, hk⟩ := q8_fresh_point hpsi ring k kind G hkin hF j zF hj hfr
  have hV := q8_valid hpsi ring k kind G hs hCd j zF y hj hy hjy
  rw [hmv] at hk
  obtain ⟨hc, hy1⟩ := q6_key_service hpsi hV hk.symm
  exact ⟨hc, by rw [hjy, show y = x + psi - 1 by omega]⟩

/-- Such an owner never moves left. -/
theorem q10_noMoveL {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (G : GhostConfig n psi kappa) (hs : GhostSound G)
    (hCd : Cd ring k kind G.phys)
    (hkin : Lemma4FreshKinematics ring k G) (hF : FreshPay ring kind k G)
    (j : Fin n) (zF : GhostToken n psi)
    (hj : ghostTokenAt kind G j = some zF) (hfr : FreshAt kind k zF.lmeta)
    (x : Nat) (hmv : zF.lmeta.moves = x * (2 * psi - 1) + (psi - 1))
    (l : State psi kappa) (v : TokenData psi) :
    ¬ q3MoveL hpsi l zF.value v := by
  intro hmvL
  obtain ⟨hc, _⟩ := q10_fresh_service hpsi ring k kind G hs hCd hkin hF j zF hj hfr x hmv
  rcases hmvL with ⟨h1, _⟩ | ⟨h2, _⟩ <;> omega

/-! ## Colour tags -/

theorem q10_ids_initial {n psi kappa : Nat} (C : Config n psi kappa) :
    q10IdsColoured (initialGhost C) := by
  intro kind kind' i z s hz hid
  have := (ghostIdsUnique_initial C).2 kind i z kind' s hz hid
  omega

theorem q10_ids_step {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (st : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (h : q10IdsColoured G) : q10IdsColoured (ghostStepPrime hpsi ring st G e) := by
  intro kind kind' i z s hz hid
  rcases q8_post hpsi ring hn2 st G e kind _ _ rfl rfl i z hz with hk |
      ⟨_, z0, v, hsrc, _, hzz, _⟩ | ⟨_, z0, v, hgr, _, hzz⟩
  · exact h kind kind' i z s hk hid
  · subst hzz
    rcases hsrc with ⟨hgl, _⟩ | ⟨hbirth, _, _⟩
    · exact h kind kind' e z0 s hgl hid
    · subst hbirth
      have h2 : (LineageId.born kind st : LineageId n) = .born kind' s := hid
      injection h2 with h3 h4
      exact h3.symm
  · subst hzz
    exact h kind kind' _ z0 s hgr hid

/-! ## Establishment by the service write -/

theorem q10_establish {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (st : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hP : L18BuildPrefixAt ring root b G.phys)
    (hsrc : PPL.sourceIota ring root G.phys b = PPL.sourceIota ring root C b)
    (hs : GhostSound G) (hs' : GhostSound (ghostStepPrime hpsi ring st G e))
    (hCd : Cd ring (shiftRight ring root (b * psi)) kind G.phys)
    (hCd' : Cd ring (shiftRight ring root (b * psi)) kind (ghostStepPrime hpsi ring st G e).phys)
    (hkin : Lemma4FreshKinematics ring (shiftRight ring root (b * psi)) G)
    (hF : FreshPay ring kind (shiftRight ring root (b * psi)) G)
    (hNO : NoOvertake ring kind (shiftRight ring root (b * psi)) G)
    (x : Nat) (hx : x < psi) (z0 : GhostToken n psi)
    (hz0 : ghostTokenAt kind G e = some z0)
    (hfr : FreshAt kind (shiftRight ring root (b * psi)) z0.lmeta)
    (hmv : z0.lmeta.moves = x * (2 * psi - 1) + (psi - 1))
    (hLV : q3GLiveValue kind (q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))) =
      some z0.value)
    (hgate : (q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).last = false ∧
      (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).last = false)
    (hRV : q3GLiveValue kind (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))) =
      none) :
    q10Bit ring root b C (ghostStepPrime hpsi ring st G e).phys x ∧
      OldAbove ring kind (shiftRight ring root (b * psi)) (x * (2 * psi - 1) + (psi - 1))
        (ghostStepPrime hpsi ring st G e) := by
  have hend := l18TargetEndLt hpsi b hb
  have h2n : 2 * psi < n := by
    have : 2 * psi ≤ (b + 2) * psi := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨hc1, hey⟩ := q10_fresh_service hpsi ring _ kind G hs hCd hkin hF e z0 hz0 hfr x hmv
  have hsite : ring.rightNeighbor e = shiftRight ring root ((b + 1) * psi + x) := by
    rw [hey, q8_rn, q10_site ring root b x (x + psi - 1) (by omega)]
  have hfire := q9_fire hn3 hpsi ring root b hb G.phys e hP.1 kind hpar x hx hsite z0.value
    hLV hc1 hgate hRV
  have hpay := (hF e z0 hz0 hfr).2
  rw [hmv, divq _ _ _ (by omega)] at hpay
  have hbitA : tokenBitBool z0.value =
      (if x ≤ firstZeroBit ring G.phys (shiftRight ring root (b * psi))
        then !(G.phys (shiftRight ring (shiftRight ring root (b * psi)) x)).id
        else (G.phys (shiftRight ring (shiftRight ring root (b * psi)) x)).id) := hpay.1
  refine ⟨?_, ?_⟩
  · unfold q10Bit
    rw [ghostStepPrime_phys, ← hsite, hfire, hbitA]
    exact l18AddOneBit_congr ring root b G.phys C hsrc x hx
  · apply q8_oldAbove_step hpsi ring h2n _ kind st G e hCd hCd' hs hs'
    intro i zO x' hO hx' hi hold
    have := hNO i zO x' e z0 hO hx' hi hold hz0 hfr
    omega

/-! ## Stability once triggered -/

theorem q10_stable {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (st : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hP : L18BuildPrefixAt ring root b G.phys)
    (hsrc : PPL.sourceIota ring root G.phys b = PPL.sourceIota ring root C b)
    (hs : GhostSound G) (hs' : GhostSound (ghostStepPrime hpsi ring st G e))
    (hCd : Cd ring (shiftRight ring root (b * psi)) kind G.phys)
    (hCd' : Cd ring (shiftRight ring root (b * psi)) kind (ghostStepPrime hpsi ring st G e).phys)
    (hkin : Lemma4FreshKinematics ring (shiftRight ring root (b * psi)) G)
    (hF : FreshPay ring kind (shiftRight ring root (b * psi)) G)
    (hCov : Lemma4GhostCoveredWindow ring (shiftRight ring root (b * psi)) kind G)
    (x : Nat) (hx : x < psi)
    (hPx : q10Bit ring root b C G.phys x ∧
      OldAbove ring kind (shiftRight ring root (b * psi)) (x * (2 * psi - 1) + (psi - 1)) G) :
    q10Bit ring root b C (ghostStepPrime hpsi ring st G e).phys x ∧
      OldAbove ring kind (shiftRight ring root (b * psi)) (x * (2 * psi - 1) + (psi - 1))
        (ghostStepPrime hpsi ring st G e) := by
  have hend := l18TargetEndLt hpsi b hb
  have h2n : 2 * psi < n := by
    have : 2 * psi ≤ (b + 2) * psi := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨?_, q8_oldAbove_step hpsi ring h2n _ kind st G e hCd hCd' hs hs' _ hPx.2⟩
  have hbitA : (G.phys (shiftRight ring root ((b + 1) * psi + x))).id =
      (if x ≤ firstZeroBit ring G.phys (shiftRight ring root (b * psi))
        then !(G.phys (shiftRight ring (shiftRight ring root (b * psi)) x)).id
        else (G.phys (shiftRight ring (shiftRight ring root (b * psi)) x)).id) := by
    rw [l18AddOneBit_congr ring root b G.phys C hsrc x hx]
    exact hPx.1
  have hC1 : ring.rightNeighbor e = shiftRight ring root ((b + 1) * psi + x) →
      L18C1CorrectAt ring root G.phys e b := by
    intro hsite kind' t htok hc1 hV hW
    have he : e = shiftRight ring (shiftRight ring root (b * psi)) (x + psi - 1) := by
      apply pred_of_rightNeighbor ring e _ (x + psi - 1) (by omega)
      rw [hsite]
      exact q10_site ring root b x (x + psi - 1) (by omega)
    by_cases hk : kind' = kind
    · rw [hk] at htok hV hW ⊢
      obtain ⟨z, hz⟩ := hCov e ⟨⟨x + psi - 1, by omega⟩, he⟩ hV
      by_cases hfr : FreshAt kind (shiftRight ring root (b * psi)) z.lmeta
      · exact q9_fresh_correct hpsi ring root b hb kind hpar G hs hkin hF e z hz hfr
      · exfalso
        have hzt : z.value = t := by
          have h1 := (q8_sound G hs kind e z hz).1
          rw [htok] at h1
          exact (Option.some.inj h1).symm
        have hlt := hPx.2 e z (x + psi - 1) hz (by omega) he hfr
        rw [hzt, hc1, q10_key_service_pt hpsi x hx] at hlt
        omega
    · have hwc := l18WrongColourClause hpsi ring root b hb G.phys hP.1 e
      rcases hpar with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · cases kind' with
        | black => exact absurd rfl hk
        | white => exact hwc.1 h ⟨hV, hW⟩
      · cases kind' with
        | black => exact hwc.2 h ⟨hV, hW⟩
        | white => exact absurd rfl hk
  have hst := q9StepTargetBitStable hn3 hpsi ring root b hb G.phys e x hx hC1 hbitA
  unfold q10Bit
  rw [ghostStepPrime_phys, hst]
  exact hPx.1

/-! ## A new trigger is a service write -/

theorem q10_noTrig {n psi kappa : Nat} (kind : TokenKind) (k : Fin n) (x : Nat)
    (G : GhostConfig n psi kappa) (hnot : ¬ q10Trig kind k x G)
    (j : Fin n) (zF : GhostToken n psi)
    (hj : ghostTokenAt kind G j = some zF) (hfr : FreshAt kind k zF.lmeta) :
    zF.lmeta.moves ≤ x * (2 * psi - 1) + (psi - 1) :=
  Nat.le_of_not_lt (fun hlt => hnot (Or.inl ⟨j, zF, hj, hfr, hlt⟩))

/-- A fresh completion logged by the move of colour `kind''`. -/
theorem q10_done {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (st : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hs : GhostSound G) (hCd : Cd ring k kind G.phys)
    (hkin : Lemma4FreshKinematics ring k G) (hF : FreshPay ring kind k G)
    (hIC : q10IdsColoured G)
    (x : Nat) (hx : x < psi) (hnot : ¬ q10Trig kind k x G)
    (kind'' : TokenKind) (m : LineageMeta n)
    (hm : m ∈ (ghostStepSelectedPair_prime hpsi ring st G e kind'').done)
    (hfc : FreshCompletion (psi := psi) kind k m) :
    ∃ z0 : GhostToken n psi, ghostTokenAt kind G e = some z0 ∧ FreshAt kind k z0.lmeta ∧
      z0.lmeta.moves = x * (2 * psi - 1) + (psi - 1) ∧
      q3GLiveValue kind (q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))) =
        some z0.value ∧
      ((q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).last = false ∧
        (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).last = false) ∧
      q3GLiveValue kind (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))) =
        none := by
  rw [q3_selected_eq'] at hm
  obtain ⟨z0, v, hcase, hmeq, hT⟩ := q7_done_cases hpsi kind'' st e _ _ _ _ m hm
  obtain ⟨⟨t, hid, hsite⟩, hmT⟩ := hfc
  subst hmeq
  have hid0 : z0.lmeta.id = .born kind t := hid
  have hfr0 : FreshAt kind k z0.lmeta := ⟨t, hid0, hsite⟩
  have hTf := q10_T (psi := psi) (by omega)
  have hxD : x * (2 * psi - 1) ≤ (psi - 1) * (2 * psi - 1) := Nat.mul_le_mul_right _ (by omega)
  rcases hcase with ⟨src, hmvR, hgate, hrn⟩ | ⟨hgr, hmvL⟩
  · rcases src with ⟨hgl, hlv⟩ | ⟨hbirth, _, _⟩
    · have hkk := hIC kind'' kind e z0 t hgl hid0
      subst hkk
      have hle := q10_noTrig kind k x G hnot e z0 hgl hfr0
      exact ⟨z0, hgl, hfr0, by omega, hlv, hgate, hrn⟩
    · subst hbirth
      change 0 + 1 = _ at hT
      omega
  · have hkk := hIC kind'' kind _ z0 t hgr hid0
    subst hkk
    have hle := q10_noTrig kind k x G hnot _ z0 hgr hfr0
    exact absurd hmvL (q10_noMoveL hpsi ring k kind G hs hCd hkin hF _ z0 hgr hfr0 x
      (by omega) _ v)

theorem q10_new {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (hn2 : 2 ≤ n) (k : Fin n) (kind : TokenKind) (st : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (hs : GhostSound G) (hCd : Cd ring k kind G.phys)
    (hkin : Lemma4FreshKinematics ring k G) (hF : FreshPay ring kind k G)
    (hIC : q10IdsColoured G)
    (x : Nat) (hx : x < psi) (hnot : ¬ q10Trig kind k x G)
    (hT' : q10Trig kind k x (ghostStepPrime hpsi ring st G e)) :
    ∃ z0 : GhostToken n psi, ghostTokenAt kind G e = some z0 ∧ FreshAt kind k z0.lmeta ∧
      z0.lmeta.moves = x * (2 * psi - 1) + (psi - 1) ∧
      q3GLiveValue kind (q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))) =
        some z0.value ∧
      ((q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).last = false ∧
        (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))).last = false) ∧
      q3GLiveValue kind (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))) =
        none := by
  rcases hT' with ⟨j, zF', hj, hfr', hlt'⟩ | ⟨m, hm, hfc⟩
  · rcases q8_post hpsi ring hn2 st G e kind _ _ rfl rfl j zF' hj with hk |
        ⟨_, z0, v, hsrc, _, hzz, hgate, hrn⟩ | ⟨_, z0, v, hgr, hmvL, hzz⟩
    · exact absurd (Or.inl ⟨j, zF', hk, hfr', hlt'⟩) hnot
    · subst hzz
      rcases hsrc with ⟨hgl, hlv⟩ | ⟨hbirth, _, _⟩
      · have hfr0 : FreshAt kind k z0.lmeta := hfr'
        have hle := q10_noTrig kind k x G hnot e z0 hgl hfr0
        change _ < z0.lmeta.moves + 1 at hlt'
        exact ⟨z0, hgl, hfr0, by omega, hlv, hgate, hrn⟩
      · subst hbirth
        change _ < 0 + 1 at hlt'
        omega
    · subst hzz
      have hfr0 : FreshAt kind k z0.lmeta := hfr'
      have hle := q10_noTrig kind k x G hnot _ z0 hgr hfr0
      change _ < z0.lmeta.moves + 1 at hlt'
      exact absurd hmvL (q10_noMoveL hpsi ring k kind G hs hCd hkin hF _ z0 hgr hfr0 x
        (by omega) _ v)
  · rw [q7_completed_step, List.mem_append, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact absurd (Or.inr ⟨m, hm, hfc⟩) hnot
    · exact q10_done hpsi ring k kind st G e hs hCd hkin hF hIC x hx hnot .black m hm hfc
    · exact q10_done hpsi ring k kind st G e hs hCd hkin hF hIC x hx hnot .white m hm hfc

/-! ## The run invariant -/

theorem q10_inv_initial {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (hPrefix : L18BuildPrefixAt ring root b C) :
    q10Inv ring root b C 0 (initialGhost C) := by
  have hCd := PPL.Lemma4Generic.cd_block_of_CDLAt hpsi ring root b C hb hPrefix.1
  refine ⟨hPrefix, PPL.Lemma4Generic.hybridInv_initial hpsi ring C,
    q4_freshPay_initial ring _ _ C,
    (PPL.lemma4StepProps_proved.1 hpsi ring _ _).1 C hCd, rfl, q10_ids_initial C, ?_, ?_⟩
  · intro i zO x j zF hO hx hi hold hFj hfr
    obtain ⟨t, hid, _⟩ := hfr
    have := (ghostIdsUnique_initial C).2 _ j zF _ t hFj hid
    omega
  · intro x hx hT
    exfalso
    rcases hT with ⟨j, zF, hj, ⟨t, hid, _⟩, _⟩ | ⟨m, hm, _⟩
    · have := (ghostIdsUnique_initial C).2 _ j zF _ t hj hid
      omega
    · change m ∈ ([] : List (LineageMeta n)) at hm
      cases hm

theorem q10_inv_step {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (h : q10Inv ring root b C t G) :
    q10Inv ring root b C (t + 1) (ghostStepPrime hpsi ring t G e) := by
  obtain ⟨hP, hI, hF, hCov, hsrc, hIC, hNO, hQ⟩ := h
  have hpar := q4_blockKind_par b
  have hend := l18TargetEndLt hpsi b hb
  have h2n : 2 * psi < n := by
    have : 2 * psi ≤ (b + 2) * psi := Nat.mul_le_mul_right _ (by omega)
    omega
  have hg := PPL.Lemma4Generic.primeGood_of_buildPrefix hn3 hpsi ring root b G.phys hb hP
  have hI' := PPL.Lemma4Generic.hybridInv_step hpsi ring t G e hI
  rw [PPL.Lemma4Generic.hybridGStep_good hpsi ring t G e hg] at hI'
  have hP' : L18BuildPrefixAt ring root b (ghostStepPrime hpsi ring t G e).phys :=
    l18PrimeStepPreservesBuildPrefix_of_white l18PrimeSelectedWhiteFrame_proved
      hn3 hpsi ring root b G.phys e hb hP
  have hF' := freshPay_step hn3 hpsi ring root b hb _ hpar G t e (hI.2.2.1 _) hP hF
  have hCd := PPL.Lemma4Generic.cd_block_of_CDLAt hpsi ring root b G.phys hb hP.1
  have hCd' : Cd ring (shiftRight ring root (b * psi)) (PPL.Lemma4Generic.l18BlockKind b)
      (ghostStepPrime hpsi ring t G e).phys :=
    PPL.Lemma4Generic.cd_block_of_CDLAt hpsi ring root b _ hb hP'.1
  have hCov' := (PPL.Lemma4Generic.primeCoverage_ofSound hpsi ring _ _ t G e hI.1
    (PPL.Lemma4Generic.preludeAgree_of_good hpsi ring G.phys e hg) hCd hCd' hCov).1
  have hsrc' : PPL.sourceIota ring root (ghostStepPrime hpsi ring t G e).phys b =
      PPL.sourceIota ring root C b :=
    ((q3fp% "q20256SourceIotaProtected") hn3 hpsi ring root b G.phys e hb hP b
      (Nat.le_refl b)).symm.trans hsrc
  have hIC' := q10_ids_step hpsi ring (by omega) t G e hIC
  have hNO' := q8_noOvertake_step hpsi ring h2n _ _ t G e hCd hCd' hI.1 hI'.1
    (hI'.2.2.1 _) hF' hNO
  refine ⟨hP', hI', hF', hCov', hsrc', hIC', hNO', ?_⟩
  intro x hx hT'
  by_cases hT : q10Trig (PPL.Lemma4Generic.l18BlockKind b) (shiftRight ring root (b * psi)) x G
  · exact q10_stable hn3 hpsi ring root b hb C _ hpar t G e hP hsrc hI.1 hI'.1 hCd hCd'
      (hI.2.2.1 _) hF hCov x hx (hQ x hx hT)
  · obtain ⟨z0, hz0, hfr, hmv, hLV, hgate, hRV⟩ :=
      q10_new hpsi ring (by omega) _ _ t G e hI.1 hCd (hI.2.2.1 _) hF hIC x hx hT hT'
    exact q10_establish hn3 hpsi ring root b hb C _ hpar t G e hP hsrc hI.1 hI'.1 hCd hCd'
      (hI.2.2.1 _) hF hNO x hx z0 hz0 hfr hmv hLV hgate hRV

theorem q10_inv_run {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (C : Config n psi kappa) :
    ∀ (p : DetSchedule n) (t : Nat) (G : GhostConfig n psi kappa),
      q10Inv ring root b C t G →
      ∃ t', q10Inv ring root b C t' (ghostRunPrime hpsi ring t G p) := by
  intro p
  induction p with
  | nil => intro t G h; exact ⟨t, h⟩
  | cons e es ih =>
      intro t G h
      exact ih (t + 1) (ghostStepPrime hpsi ring t G e)
        (q10_inv_step hn3 hpsi ring root b hb C t G e h)

/-! ## The rows -/

/-- **The late target-bits row, unconditionally** (pre = the whole cut). -/
theorem l18PrimeLemma4LateTargetBitsRow_proved : L18PrimeLemma4LateTargetBitsRow := by
  intro n psi kappa hn3 hpsi ring root b C cut hb hPrefix hsub _hmin
  rcases l18PrimeLemma4EstablishmentTokensAtCut_proved hn3 hpsi ring root b C cut hb hPrefix
      hsub with hhit | htok
  · exact Or.inl hhit
  · right
    intro x
    obtain ⟨t', hInv⟩ := q10_inv_run hn3 hpsi ring root b hb C cut 0 (initialGhost C)
      (q10_inv_initial hn3 hpsi ring root b hb C hPrefix)
    have hcomp := PPL.Lemma4Generic.prime_blockCompletion_of_buildPrefix hn3 hpsi ring root b
      C cut hb hPrefix hsub
    have hbit := (hInv.2.2.2.2.2.2.2 x.val x.isLt (Or.inr hcomp)).1
    unfold q10Bit at hbit
    rw [ghostRunPrime_phys] at hbit
    exact ⟨cut, [], (List.append_nil cut).symm, htok, hbit⟩

/-- The ID half of the establishment cut, unconditionally. -/
theorem l18PrimeEstablishmentIdAtCut_proved : L18PrimeLemma4EstablishmentIdAtCutRow :=
  l18PrimeEstablishmentIdAtCut_of_late l18PrimeLemma4LateTargetBitsRow_proved

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.q10_inv_step
#print axioms PPL.Convergence.L18.l18PrimeLemma4LateTargetBitsRow_proved
#print axioms PPL.Convergence.L18.l18PrimeEstablishmentIdAtCut_proved
