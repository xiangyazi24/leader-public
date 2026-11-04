import Leader.PPL.TokenCompletion.Sweep
import Leader.PPL.TokenCompletion.GhostStepMirror
import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TransitionFacts


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/--
Verbatim residual statement, renamed only so this file does not depend
on the not-yet-landed SweepResponderSameId file.
-/
def Lemma4SweepResponderNegTurnProgressRowStmt : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z z' : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    GhostSound G →
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) →
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z →
    (ghostStepSelectedPair
        hpsi ring step G e kind).left =
      some z' →
    z'.lmeta.id = z.lmeta.id →
    z'.lmeta = ghostStepLineageAdvance z.lmeta →
    decodeOffset psi (tokenCode z.value) = -1 →
    tokenAt kind
        ((ghostStep hpsi ring step G e).phys e) =
      some z'.value →
    decodeOffset psi (tokenCode z'.value) =
      ((psi : Nat) : Int) →
    Lemma4InWindow ring k psi e ∧
      (FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta) ∧
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e ∧
      lemma4TokenProgress
          kind
          (G.phys (ring.rightNeighbor e))
          z.value ≤
        lemma4TokenProgress
          kind
          ((ghostStep hpsi ring step G e).phys e)
          z'.value ∧
      (e =
          lemma4ServiceEdge
            ring kind G (ring.rightNeighbor e) z →
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys e)
            z'.value =
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value +
            1)


private theorem q19947_leftNeighbor_rightNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only
    [DirectedRing.leftNeighbor,
      DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq :
        i.val + 1 + n - 1 = n + i.val := by
      omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by
      omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by
      omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem q19947_rightNeighbor_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (d : Nat) :
    ring.rightNeighbor (shiftRight ring k d) =
      shiftRight ring k (d + 1) := by
  apply Fin.ext
  simp only
    [DirectedRing.rightNeighbor, shiftRight]
  rw [Nat.mod_add_mod, Nat.add_assoc]


private theorem q19947_ghostSound_token
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    tokenAt kind (G.phys i) = some z.value := by
  cases kind with
  | black =>
      exact (hsound.1 i z howner).1
  | white =>
      exact (hsound.2 i z howner).1


private theorem q19947_owner_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner :
      ghostTokenAt kind G i = some z) :
    ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2


/--
At window coordinate zero the C_d distance is the selected-color source
distance. A locally valid negative selected-color token would then target
strictly to the right of psi, contradicting negative-token validity.
-/
private theorem q19947_firstNegativeTarget
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (hdist :
      q.dist.val = tokenD' psi kind)
    (hneg :
      decodeOffset psi (tokenCode t) < 0) :
    ((psi : Nat) : Int) <
      tokenTargetCoordinate kind q t := by
  let c :=
    decodeOffset psi (tokenCode t)
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  have hb :
      1 - ((psi : Nat) : Int) ≤ c ∧
        c ≤ -1 := by
    rcases hv with hn | hp
    · exact hn
    · exfalso
      try dsimp only [c] at hneg
      omega
  cases kind with
  | black =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist]
      simp only
        [Int.natCast_zero, Int.zero_add, Int.add_zero]
      change
        ((psi : Nat) : Int) <
          c % (((2 * psi : Nat)) : Int)
      have hperiod :
          c % (((2 * psi : Nat)) : Int) =
            (c + (((2 * psi : Nat)) : Int)) %
              (((2 * psi : Nat)) : Int) := by
        rw [Int.add_emod_right]
      rw [hperiod]
      rw [Int.emod_eq_of_lt
        (by omega) (by omega)]
      omega
  | white =>
      simp only [tokenD'] at hdist
      unfold tokenTargetCoordinate
      simp only [tokenD']
      rw [hdist]
      have hsum :
          ((psi : Nat) : Int) +
                c +
                ((psi : Nat) : Int) =
            c + (((2 * psi : Nat)) : Int) := by
        omega
      change
        ((psi : Nat) : Int) <
          (((psi : Nat) : Int) +
              c +
              ((psi : Nat) : Int)) %
            (((2 * psi : Nat)) : Int)
      rw [hsum]
      rw [Int.emod_eq_of_lt
        (by omega) (by omega)]
      omega


private theorem q19947_negative_not_first
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hsound : GhostSound G)
    (hx :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    x.val ≠ 0 := by
  intro hx0
  have htok :=
    q19947_ghostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner
  have hvalid :=
    q19947_owner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner
  unfold ValidToken at hvalid
  rw [htok] at hvalid
  dsimp only at hvalid
  rcases hvalid with hp | hn
  · omega
  · have hrow := (hCd x).1
    try dsimp only at hrow
    rw [← hx] at hrow
    have hdist :
        (G.phys (ring.rightNeighbor e)).dist.val =
          tokenD' psi kind := by
      cases kind with
      | black =>
          simp only [tokenD'] at hrow ⊢
          rw [hx0, Nat.zero_add] at hrow
          simpa using hrow
      | white =>
          simp only [tokenD'] at hrow ⊢
          rw [hx0, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega)] at hrow
          exact hrow
    have ht :=
      q19947_firstNegativeTarget
        hpsi kind
        (G.phys (ring.rightNeighbor e))
        z.value hdist hneg
    omega


/--
A negative responder in the C_d window cannot be at coordinate zero, hence
its selected initiator is the immediately preceding window coordinate.
-/
private theorem q19947_predecessorData
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hsound : GhostSound G)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (howner :
      ghostTokenAt kind G
          (ring.rightNeighbor e) =
        some z)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    ∃ x : Fin (2 * psi), ∃ y : Fin (2 * psi),
      ring.rightNeighbor e =
          shiftRight ring k x.val ∧
        e = shiftRight ring k y.val ∧
        y.val + 1 = x.val := by
  rcases hwin with ⟨x, hx⟩
  have hx0 :=
    q19947_negative_not_first
      hpsi ring k kind G e x z
      hCd hsound hx howner hneg
  let y : Fin (2 * psi) :=
    ⟨x.val - 1, by omega⟩
  have hstep :
      ring.rightNeighbor
          (shiftRight ring k y.val) =
        shiftRight ring k x.val := by
    calc
      ring.rightNeighbor
            (shiftRight ring k y.val) =
          shiftRight ring k (y.val + 1) :=
        q19947_rightNeighbor_shiftRight
          ring k y.val
      _ = shiftRight ring k x.val := by
        congr 1
        dsimp [y]
        omega
  have hrn :
      ring.rightNeighbor e =
        ring.rightNeighbor
          (shiftRight ring k y.val) :=
    hx.trans hstep.symm
  have he :=
    congrArg ring.leftNeighbor hrn
  rw [q19947_leftNeighbor_rightNeighbor,
    q19947_leftNeighbor_rightNeighbor] at he
  exact
    ⟨x, y, hx, he,
      by dsimp [y]; omega⟩


private theorem q19947_fresh_advance
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (z z' : GhostToken n psi)
    (hmeta :
      z'.lmeta = ghostStepLineageAdvance z.lmeta) :
    FreshAt kind k z.lmeta →
      FreshAt kind k z'.lmeta := by
  intro hfresh
  rcases hfresh with ⟨t, hid, hsite⟩
  refine ⟨t, ?_, ?_⟩
  · rw [hmeta]
    simpa [ghostStepLineageAdvance] using hid
  · rw [hmeta]
    simpa [ghostStepLineageAdvance] using hsite


/--
C_d geometry for the exceptional responder turn.

For c=-1 the old negative target is exactly the predecessor window coordinate
y. Local validity therefore gives 1 <= y < psi. After moving left and turning
to c=+psi, the new positive target is y+psi.
-/
private theorem q19947_negTurnGeometry
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (e : Fin n)
    (x y : Fin (2 * psi))
    (t t' : TokenData psi)
    (hCd : Cd ring k kind C)
    (hCd' : Cd ring k kind C')
    (hxr :
      ring.rightNeighbor e =
        shiftRight ring k x.val)
    (hye :
      e = shiftRight ring k y.val)
    (hyx :
      y.val + 1 = x.val)
    (htok :
      tokenAt kind (C (ring.rightNeighbor e)) =
        some t)
    (hvalid :
      ValidToken kind C (ring.rightNeighbor e))
    (hc :
      decodeOffset psi (tokenCode t) = -1)
    (hc' :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int)) :
    1 ≤ y.val ∧
      y.val < psi ∧
      tokenTargetCoordinate
          kind (C (ring.rightNeighbor e)) t =
        (y.val : Int) ∧
      tokenTargetCoordinate kind (C' e) t' =
        ((y.val + psi : Nat) : Int) := by
  have hvalid' := hvalid
  unfold ValidToken at hvalid'
  rw [htok] at hvalid'
  dsimp only at hvalid'
  rcases hvalid' with hp | hn
  · rw [hc] at hp
    omega
  · have hpre := (hCd x).1
    have hpost := (hCd' y).1
    try dsimp only at hpre hpost
    rw [← hxr] at hpre
    rw [← hye] at hpost

    cases kind with
    | black =>
        simp only [tokenD'] at hpre hpost

        rw [Nat.add_zero,
          Nat.mod_eq_of_lt x.isLt] at hpre
        rw [Nat.add_zero,
          Nat.mod_eq_of_lt y.isLt] at hpost

        have hold :
            tokenTargetCoordinate
                .black
                (C (ring.rightNeighbor e)) t =
              (y.val : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpre, hc]
          have heq :
              (x.val : Int) + (-1 : Int) + ((0 : Nat) : Int) =
                (y.val : Int) := by
            omega
          rw [heq]
          rw [Int.emod_eq_of_lt
            (by omega) (by
              have hy := y.isLt
              omega)]

        have hylo : 1 ≤ y.val := by
          rw [hold] at hn
          omega
        have hylt : y.val < psi := by
          rw [hold] at hn
          omega

        have hnew :
            tokenTargetCoordinate
                .black (C' e) t' =
              ((y.val + psi : Nat) : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpost, hc']
          have heq :
              (y.val : Int) +
                    ((psi : Nat) : Int) + ((0 : Nat) : Int) =
                ((y.val + psi : Nat) : Int) := by
            omega
          rw [heq]
          rw [Int.emod_eq_of_lt
            (by omega) (by omega)]

        exact
          ⟨hylo, hylt, hold, hnew⟩

    | white =>
        simp only [tokenD'] at hpre hpost

        have hold :
            tokenTargetCoordinate
                .white
                (C (ring.rightNeighbor e)) t =
              (y.val : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hc]

          by_cases hxlt : x.val < psi
          · have hsumlt :
                x.val + psi < 2 * psi := by
              omega
            rw [Nat.mod_eq_of_lt hsumlt] at hpre
            rw [hpre]
            have heq :
                ((x.val + psi : Nat) : Int) +
                      (-1 : Int) +
                      ((psi : Nat) : Int) =
                  (y.val : Int) +
                    (((2 * psi : Nat)) : Int) := by
              omega
            rw [heq, Int.add_emod_right]
            rw [Int.emod_eq_of_lt
              (by omega) (by
                have hy := y.isLt
                omega)]

          · by_cases hxeq : x.val = psi
            · have hsum :
                  x.val + psi = 2 * psi := by
                omega
              rw [hsum, Nat.mod_self] at hpre
              rw [hpre]
              have heq :
                  ((0 : Nat) : Int) + (-1 : Int) +
                        ((psi : Nat) : Int) =
                    (y.val : Int) := by
                omega
              rw [heq]
              rw [Int.emod_eq_of_lt
                (by omega) (by
                  have hy := y.isLt
                  omega)]

            · have hxge :
                  2 * psi ≤ x.val + psi := by
                omega
              have hrem :
                  x.val + psi - 2 * psi <
                    2 * psi := by
                omega
              rw [Nat.mod_eq_sub_mod hxge,
                Nat.mod_eq_of_lt hrem] at hpre
              rw [hpre]
              have heq :
                  ((x.val + psi - 2 * psi : Nat) : Int) +
                        (-1 : Int) +
                        ((psi : Nat) : Int) =
                    (y.val : Int) := by
                omega
              rw [heq]
              rw [Int.emod_eq_of_lt
                (by omega) (by
                  have hy := y.isLt
                  omega)]

        have hylo : 1 ≤ y.val := by
          rw [hold] at hn
          omega
        have hylt : y.val < psi := by
          rw [hold] at hn
          omega

        have hpostlt :
            y.val + psi < 2 * psi := by
          omega
        rw [Nat.mod_eq_of_lt hpostlt] at hpost

        have hnew :
            tokenTargetCoordinate
                .white (C' e) t' =
              ((y.val + psi : Nat) : Int) := by
          unfold tokenTargetCoordinate
          simp only [tokenD']
          rw [hpost, hc']
          have hsum :
              ((y.val + psi : Nat) : Int) +
                    ((psi : Nat) : Int) +
                    ((psi : Nat) : Int) =
                ((y.val + psi : Nat) : Int) +
                  (((2 * psi : Nat)) : Int) := by
            omega
          rw [hsum, Int.add_emod_right]
          rw [Int.emod_eq_of_lt
            (by omega) (by omega)]

        exact
          ⟨hylo, hylt, hold, hnew⟩


private theorem q19947_negTurn_valid
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (C' : Config n psi kappa)
    (e : Fin n)
    (t' : TokenData psi)
    (htok' :
      tokenAt kind (C' e) = some t')
    (hc' :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int))
    (y : Nat)
    (hylt : y < psi)
    (htarget :
      tokenTargetCoordinate kind (C' e) t' =
        ((y + psi : Nat) : Int)) :
    ValidToken kind C' e := by
  unfold ValidToken
  rw [htok']
  dsimp only
  left
  refine And.intro ?_ (And.intro ?_ ?_)
  · rw [hc']
    omega
  · rw [htarget]
    omega
  · rw [htarget]
    omega


/--
The public rank increases by exactly one across the c=-1 -> +psi turn.
The calculation uses only the two target coordinates supplied by C_d.
-/
private theorem q19947_negTurn_progress
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (q q' : State psi kappa)
    (t t' : TokenData psi)
    (y : Nat)
    (hypos : 0 < y)
    (hc :
      decodeOffset psi (tokenCode t) = -1)
    (hc' :
      decodeOffset psi (tokenCode t') =
        ((psi : Nat) : Int))
    (hold :
      tokenTargetCoordinate kind q t =
        (y : Int))
    (hnew :
      tokenTargetCoordinate kind q' t' =
        ((y + psi : Nat) : Int)) :
    lemma4TokenProgress kind q' t' =
      lemma4TokenProgress kind q t + 1 := by
  have hneg :
      ¬ 0 < decodeOffset psi (tokenCode t) := by
    rw [hc]
    omega
  have hpos :
      0 < decodeOffset psi (tokenCode t') := by
    rw [hc']
    omega
  have habs :
      (decodeOffset psi (tokenCode t)).natAbs = 1 := by
    rw [hc]
    rfl
  have hto :
      (decodeOffset psi (tokenCode t')).toNat = psi := by
    rw [hc']
    simp
  have holdNat :
      (tokenTargetCoordinate kind q t).toNat = y := by
    rw [hold]
    simp
  have hnewNat :
      (tokenTargetCoordinate kind q' t').toNat =
        y + psi := by
    rw [hnew]
    omega

  unfold lemma4TokenProgress lemma4TokenStage
  simp only [hneg, hpos, if_false, if_true]
  rw [holdNat, hnewNat, habs, hto]

  have hstageOld :
      y + psi - 1 - psi = y - 1 := by
    omega
  have hstageNew :
      y + psi - psi = y := by
    omega
  rw [hstageOld, hstageNew]
  simp only [Nat.sub_self, Nat.add_zero]

  let D : Nat := 2 * psi - 1
  have hDpos : 0 < D := by
    dsimp [D]
    omega
  have hydec :
      y = (y - 1) + 1 := by
    omega
  change
    y * D =
      (y - 1) * D + (D - 1) + 1
  calc
    y * D =
        ((y - 1) + 1) * D := by
      rw [← hydec]
    _ = (y - 1) * D + D := by
      rw [Nat.add_mul, Nat.one_mul]
    _ = (y - 1) * D + (D - 1) + 1 := by
      omega


theorem lemma4SweepResponderNegTurnProgressRow_proved :
    Lemma4SweepResponderNegTurnProgressRowStmt := by
  unfold Lemma4SweepResponderNegTurnProgressRowStmt
  intro n psi kappa hpsi
  intro ring k kind step G e z z'
  intro hCd hCd' hsound hwin howner
  intro _hleft _hid hmeta hc htokPost hc'

  have hneg :
      decodeOffset psi (tokenCode z.value) < 0 := by
    rw [hc]
    omega

  rcases
      q19947_predecessorData
        hpsi ring k kind G e z
        hCd hsound hwin howner hneg with
    ⟨x, y, hxr, hye, hyx⟩

  have hwinE :
      Lemma4InWindow ring k psi e :=
    ⟨y, hye⟩

  have htokPre :
      tokenAt kind
          (G.phys (ring.rightNeighbor e)) =
        some z.value :=
    q19947_ghostSound_token
      kind G (ring.rightNeighbor e)
      z hsound howner

  have hvalidPre :
      ValidToken kind G.phys
        (ring.rightNeighbor e) :=
    q19947_owner_valid
      kind G (ring.rightNeighbor e)
      z hsound howner

  have hgeom :=
    q19947_negTurnGeometry
      hpsi ring k kind
      G.phys
      (ghostStep hpsi ring step G e).phys
      e x y z.value z'.value
      hCd hCd' hxr hye hyx
      htokPre hvalidPre hc hc'

  rcases hgeom with
    ⟨hylo, hylt, htargetOld, htargetNew⟩

  have hfresh :
      FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta :=
    q19947_fresh_advance
      kind k z z' hmeta

  have hvalidPost :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys e :=
    q19947_negTurn_valid
      hpsi kind
      (ghostStep hpsi ring step G e).phys
      e z'.value htokPost hc'
      y.val hylt htargetNew

  have hprog :
      lemma4TokenProgress
          kind
          ((ghostStep hpsi ring step G e).phys e)
          z'.value =
        lemma4TokenProgress
            kind
            (G.phys (ring.rightNeighbor e))
            z.value +
          1 :=
    q19947_negTurn_progress
      hpsi kind
      (G.phys (ring.rightNeighbor e))
      ((ghostStep hpsi ring step G e).phys e)
      z.value z'.value
      y.val (by omega)
      hc hc' htargetOld htargetNew

  have hmono :
      lemma4TokenProgress
          kind
          (G.phys (ring.rightNeighbor e))
          z.value ≤
        lemma4TokenProgress
          kind
          ((ghostStep hpsi ring step G e).phys e)
          z'.value := by
    rw [hprog]
    omega

  refine
    And.intro hwinE
      (And.intro hfresh
        (And.intro hvalidPost
          (And.intro hmono ?_)))
  intro _hs
  exact hprog


end PPL


#print axioms PPL.lemma4SweepResponderNegTurnProgressRow_proved

