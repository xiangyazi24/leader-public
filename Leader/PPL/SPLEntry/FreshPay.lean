import Leader.PPL.SPLEntry.FreshPayArith
import Leader.PPL.TokenCompletion.RunFacts

/-!
# The fresh-lineage payload invariant `FreshPay` along prime ghost runs

For pair `b` with parity colour `kind` and border `k = root + b psi`, every
live fresh owner (`FreshAt kind k`) has column `q = moves / (2 psi - 1)`
below `psi` and a correct payload for column `q` of the source segment `S_b`:

`FreshPay ring kind k G := ∀ i z, owner … → FreshAt … →
   q < psi ∧ payloadCorrect ring G.phys k q z.value`.

`freshPay_step`: one prime ghost step preserves `FreshPay`, from
`L18BuildPrefixAt ring root b G.phys` (source frame, CDLAt) and the fresh
kinematics of the pre-state.  The proof is by the ghost provenance of
`L18PrimeGhostProvenance` (no physical old-image witness):

* stay (initiator or responder): value and moves unchanged;
* right bump from the initiator owner (`c = 1`, `c ≥ 2`) and left bump
  `c ≤ -2`: bits and column unchanged;
* right bump of a birth: the birth site is `k`, column `0`, payload
  `(!id k, id k)` (`pay_birth`);
* left bump `c = -1`: column `q + 1`, payload `pay_turn`; at `q + 1 = psi`
  the new value is locally invalid at the turn site (`turn_invalid_at_psi`),
  so no live owner results.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false

open PPL

/-- The fresh-lineage payload invariant. -/
def FreshPay {n psi kappa : Nat} (ring : DirectedRing n) (kind : TokenKind) (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n) (z : GhostToken n psi),
    ghostTokenAt kind G i = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves / (2 * psi - 1) < psi ∧
      payloadCorrect ring G.phys k (z.lmeta.moves / (2 * psi - 1)) z.value

/-- The responder state seen by the selected colour's move. -/
def q3RState {psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) : State psi kappa :=
  match kind with
  | .black => (q3GPrelude hpsi l r).2
  | .white => (pprimeMoveToken hpsi .black (q3GPrelude hpsi l r).1 (q3GPrelude hpsi l r).2).2

theorem q3_selected_eq' {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (step : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) :
    ghostStepSelectedPair_prime hpsi ring step G e kind =
      q3GMoveToken hpsi kind step e
        (q3LState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e)))
        (q3RState hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e)))
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G (ring.rightNeighbor e)) := by
  cases kind <;> rfl

open Lean Elab Term Meta in
elab "q3fp% " s:str : term => do
  let n : Name :=
    ((((((`_private.Leader.PPL.SPLEntry.BuiltPairIds).num 0).str
      "PPL").str "Convergence").str "L18").str s.getString)
  mkConstWithFreshMVarLevels n

theorem birth_bits {n psi : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind) (st : Nat)
    (site : Fin n) (lid : Bool) :
    ((q3GBirth hpsi kind st site lid).value.1.2.val == 1) = !lid ∧
      ((q3GBirth hpsi kind st site lid).value.2.val == 1) = lid := by
  cases lid <;> exact ⟨rfl, rfl⟩

theorem rightNeighbor_ne {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · rw [show e.val + 1 = 0 + n by omega, Nat.add_mod_right, Nat.zero_mod] at hv; omega

/-- One prime ghost step preserves `FreshPay`. -/
theorem freshPay_step {n psi kappa : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (root : Fin n) (b : Nat) (hb : b < l18BlockCount n psi)
    (kind : TokenKind)
    (hpar : (kind = .black ∧ b % 2 = 0) ∨ (kind = .white ∧ b % 2 = 1))
    (G : GhostConfig n psi kappa) (st : Nat) (e : Fin n)
    (hkin : Lemma4FreshKinematics ring (shiftRight ring root (b * psi)) G)
    (hP : L18BuildPrefixAt ring root b G.phys)
    (hF : FreshPay ring kind (shiftRight ring root (b * psi)) G) :
    FreshPay ring kind (shiftRight ring root (b * psi)) (ghostStepPrime hpsi ring st G e) := by
  generalize hk : shiftRight ring root (b * psi) = k at hkin hF ⊢
  have hend := wc_blockEnd hpsi b hb
  have hD : 3 ≤ 2 * psi - 1 := by omega
  -- source frame
  have hsrc := (q3fp% "q20256SourceIotaProtected") hn3 hpsi ring root b G.phys e hb hP b
    (Nat.le_refl b)
  have hid : ∀ y, y < psi → (G.phys (shiftRight ring k y)).id =
      (pprimeStep ring G.phys e (shiftRight ring k y)).id := by
    intro y hy
    have := congrFun hsrc ⟨y, hy⟩
    rw [← hk]; exact this
  have hphys : (ghostStepPrime hpsi ring st G e).phys = pprimeStep ring G.phys e := rfl
  -- transport of a pre fact to the post configuration
  have transport : ∀ (q : Nat) (v : TokenData psi), q < psi →
      payloadCorrect ring G.phys k q v →
      payloadCorrect ring (ghostStepPrime hpsi ring st G e).phys k q v := by
    intro q v hq h
    rw [hphys]; exact pay_congr ring _ _ k hid q hq v h
  intro i z hz hfresh
  have hne := rightNeighbor_ne ring (by omega) e
  have hlf := lstate_frame hpsi kind (G.phys e) (G.phys (ring.rightNeighbor e))
  by_cases hie : i = e
  · subst hie
    rw [ghostTokenAt_ghostStep_initiator_prime, q3_selected_eq'] at hz
    rcases q3_left_cases hpsi kind st i _ _ _ _ z hz with hst | ⟨z0, v, hgr, hmv, hzeq, hLV⟩
    · obtain ⟨hq, hpay⟩ := hF i z hst hfresh
      exact ⟨hq, transport _ _ hq hpay⟩
    · subst hzeq
      have hfr0 : FreshAt kind k z0.lmeta := hfresh
      obtain ⟨hq0, hpay0⟩ := hF _ z0 hgr hfr0
      obtain ⟨x, hx, htraj⟩ := hkin kind _ z0 hgr hfr0
      rcases htraj with ⟨q', hc, _, _, _⟩ | ⟨q', hc, habs, hxq, hm⟩
      · exfalso
        rcases hmv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · have hmq : z0.lmeta.moves / (2 * psi - 1) = q' := by
          rw [hm]; exact divq _ _ _ (by omega)
        rw [hmq] at hq0 hpay0
        show (z0.lmeta.moves + 1) / (2 * psi - 1) < psi ∧
          payloadCorrect ring _ k ((z0.lmeta.moves + 1) / (2 * psi - 1)) v
        rcases hmv with ⟨h1, hv⟩ | ⟨h2, _, hb1, hb2⟩
        · -- c = -1: turn to column q' + 1
          have habs1 : (decodeOffset psi (tokenCode z0.value)).natAbs = 1 := by omega
          have hm1 : z0.lmeta.moves + 1 = (q' + 1) * (2 * psi - 1) + 0 := by
            rw [hm, habs1, Nat.add_mul, Nat.one_mul]; omega
          rw [hm1, divq _ _ _ (by omega)]
          have hxe : ring.rightNeighbor i = shiftRight ring k (q' + 1 + 1) := by
            rw [hx, hxq, habs1]
          have hei := pred_of_rightNeighbor ring i k (q' + 1) (by omega) hxe
          by_cases hlt : q' + 1 < psi
          · refine ⟨hlt, ?_⟩
            have heid : (G.phys i).id = (G.phys (shiftRight ring k (q' + 1))).id :=
              congrArg (fun x => (G.phys x).id) hei
            rw [hv, hlf.1, heid]
            exact transport _ _ hlt (pay_turn hpsi ring G.phys k q' hlt z0.value hpay0)
          · exfalso
            have hq1 : q' + 1 = psi := by omega
            apply turn_invalid_at_psi hpsi b kind hpar
              (q3LState hpsi kind (G.phys i) (G.phys (ring.rightNeighbor i)))
              ?_ (G.phys i).id z0.value
            · rw [← hlf.1, ← hv]; exact hLV
            · rw [hlf.2, (hP.1.2.2 i).1, hei, hq1, ← hk, l18Gapped_shiftRight_add,
                l18Gapped_cyclicOffset_shiftRight_of_lt ring root _ (by
                  have : (b + 2) * psi = b * psi + psi + psi := by
                    rw [Nat.add_mul, show 2 * psi = psi + psi by omega, Nat.add_assoc]
                  omega)]
        · -- c ≤ -2: same column, same bits
          have hm1 : z0.lmeta.moves + 1 = q' * (2 * psi - 1) +
              (2 * psi - 1 - (decodeOffset psi (tokenCode z0.value)).natAbs + 1) := by
            rw [hm]; omega
          rw [hm1, divq _ _ _ (by omega)]
          exact ⟨hq0, transport _ _ hq0 (pay_sameBits ring _ k q' _ v hb1 hb2 hpay0)⟩
  · by_cases hir : i = ring.rightNeighbor e
    · subst hir
      rw [ghostTokenAt_ghostStep_responder_of_ne_prime hpsi ring st G e kind hne,
        q3_selected_eq'] at hz
      rcases q3_right_cases hpsi kind st e _ _ _ _ z hz with hst |
          ⟨z0, v, hsrcz, hmv, hzeq, hLV⟩
      · obtain ⟨hq, hpay⟩ := hF _ z hst hfresh
        exact ⟨hq, transport _ _ hq hpay⟩
      · subst hzeq
        have hfr0 : FreshAt kind k z0.lmeta := hfresh
        have hbits : v.1.2 = z0.value.1.2 ∧ v.2 = z0.value.2 := by
          rcases hmv with ⟨_, hv⟩ | ⟨_, _, h1, h2⟩
          · rw [hv]; exact ⟨rfl, rfl⟩
          · exact ⟨h1, h2⟩
        have hcpos : 1 ≤ decodeOffset psi (tokenCode z0.value) := by
          rcases hmv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
        show (z0.lmeta.moves + 1) / (2 * psi - 1) < psi ∧
          payloadCorrect ring _ k ((z0.lmeta.moves + 1) / (2 * psi - 1)) v
        rcases hsrcz with hgl | ⟨hbirth, _, _⟩
        · obtain ⟨hq0, hpay0⟩ := hF _ z0 hgl hfr0
          obtain ⟨x, hx, htraj⟩ := hkin kind _ z0 hgl hfr0
          rcases htraj with ⟨q', hc, hcle, _, hm⟩ | ⟨q', hc, _, _, _⟩
          · have hmq : z0.lmeta.moves / (2 * psi - 1) = q' := by
              rw [hm]; exact divq _ _ _ (by omega)
            rw [hmq] at hq0 hpay0
            have hm1 : z0.lmeta.moves + 1 = q' * (2 * psi - 1) +
                (psi - (decodeOffset psi (tokenCode z0.value)).toNat + 1) := by
              rw [hm]; omega
            rw [hm1, divq _ _ _ (by omega)]
            exact ⟨hq0, transport _ _ hq0 (pay_sameBits ring _ k q' _ v hbits.1 hbits.2 hpay0)⟩
          · exfalso; omega
        · -- birth at the border
          subst hbirth
          obtain ⟨tb, _, hsite⟩ := hfresh
          have hek : e = k := hsite
          have hm0 : (0 + 1) / (2 * psi - 1) = 0 := Nat.div_eq_of_lt (by omega)
          refine ⟨by simp only [q3GBirth]; rw [hm0]; omega, ?_⟩
          simp only [q3GBirth]
          rw [hm0]
          apply transport _ _ (by omega)
          apply pay_birth hpsi ring G.phys k v
          · unfold tokenBitBool; rw [hbits.1, (birth_bits hpsi kind st e _).1, hlf.1, hek]
          · unfold tokenCarryBool; rw [hbits.2, (birth_bits hpsi kind st e _).2, hlf.1, hek]
    · rw [ghostTokenAt_ghostStep_frame_prime hpsi ring st G e i kind hie hir] at hz
      obtain ⟨hq, hpay⟩ := hF i z hz hfresh
      exact ⟨hq, transport _ _ hq hpay⟩

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.freshPay_step
