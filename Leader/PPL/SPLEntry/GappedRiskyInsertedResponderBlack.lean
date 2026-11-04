import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderCases
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Leader.PPL.SPLEntry.GappedPhases
import Init.Omega


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-
Bounded responder reduction.


The two residual Props below contain only the literal responder-token algebra:
* wrap: closed-gate responder token frame;
* nonwrap: the four possible black responder token shapes.


Everything geometric/risky is discharged here.  The exact public L18 interfaces
are pinned below; in particular no private SPL helper is unfolded.
-/


private theorem q20230_black_left_code
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (hlast : l.last = false)
    (hrlast : r.last = false) :
    forall t : TokenData psi,
      PPL.tokenAt .black
          (PPL.moveToken hpsi .black l r).1 = some t ->
      (PPL.decodeOffset psi (PPL.tokenCode t) < 0) \/
        (PPL.decodeOffset psi (PPL.tokenCode t) =
          ((psi : Nat) : Int)) := by
  exact
    l18Risk2MoveToken_left_code
      hpsi .black l r hlast hrlast


private theorem q20230_untouched_frame
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : i != e)
    (hir : i != ring.rightNeighbor e) :
    pprimeStep ring C e i = C i := by
  exact
    l18Risk2UntouchedFrame
      ring C e i (bne_iff_ne.mp hie) (bne_iff_ne.mp hir)


private theorem q20230_wrap_last_true
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : CDLAt ring root C)
    (hroot : ring.rightNeighbor e = root) :
    (C e).last = true := by
  have hoff :=
    l18Gapped_predecessor_offset_of_right_root
      ring root e hroot
  have hth :=
    l18Gapped_lastThreshold_lt
      (n := n) (psi := psi) hn3 hpsi
  unfold l18GappedLastThreshold at hth
  have hgeom := hC.2.2 e
  dsimp only at hgeom
  apply hgeom.2.mpr
  rw [hoff]
  omega


private theorem q20230_same_black_risky_pre
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (i : Fin n)
    (t : TokenData psi)
    (hCtok : PPL.tokenAt .black (C i) = some t)
    (hDtok : PPL.tokenAt .black (D i) = some t)
    (hRisk : PPL.tokenRisky ring root D i .black) :
    PPL.tokenRisky ring root C i .black := by
  unfold PPL.tokenRisky at hRisk ⊢
  rw [hDtok] at hRisk
  rw [hCtok]
  exact hRisk


private theorem q20230_predecessor_in_s0
    {n psi : Nat}
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root e : Fin n)
    (hroot : Not (ring.rightNeighbor e = root))
    (hroff :
      PPL.cyclicOffset ring root
          (ring.rightNeighbor e) < psi) :
    InSegment ring root psi 0 e := by
  unfold InSegment
  dsimp only
  have hoff :=
    l18Gapped_rightNeighbor_offset_of_ne_root
      ring root e hroot
  have hmin : Nat.min psi n = psi :=
    Nat.min_eq_left (Nat.le_of_lt hlt)
  simp only
    [Nat.zero_mul, Nat.zero_add, Nat.one_mul, hmin]
  rw [hoff] at hroff
  omega


private theorem q20230_moved_black_risky_pre
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C D : Config n psi kappa)
    (e : Fin n)
    (t t' : TokenData psi)
    (hCtok : PPL.tokenAt .black (C e) = some t)
    (hDtok :
      PPL.tokenAt .black
        (D (ring.rightNeighbor e)) = some t')
    (hc2 :
      2 <=
        PPL.decodeOffset psi (PPL.tokenCode t))
    (hc' :
      PPL.decodeOffset psi (PPL.tokenCode t') =
        PPL.decodeOffset psi (PPL.tokenCode t) - 1)
    (he0 : InSegment ring root psi 0 e)
    (hRisk :
      PPL.tokenRisky ring root D
        (ring.rightNeighbor e) .black) :
    PPL.tokenRisky ring root C e .black := by
  cases hcode :
      PPL.decodeOffset psi (PPL.tokenCode t) with
  | negSucc m =>
      rw [hcode] at hc2
      omega
  | ofNat m =>
      have hm2 : 2 <= m := by
        rw [hcode] at hc2
        simp only [Int.ofNat_eq_coe] at hc2
        omega
      have hcode' :
          PPL.decodeOffset psi (PPL.tokenCode t') =
            ((m - 1 : Nat) : Int) := by
        rw [hc', hcode]
        simp only [Int.ofNat_eq_coe]
        omega
      unfold PPL.tokenRisky at hRisk ⊢
      rw [hDtok] at hRisk
      rw [hCtok]
      dsimp only at hRisk ⊢
      rw [hcode'] at hRisk
      rw [hcode]
      try dsimp only at hRisk ⊢
      constructor
      · omega
      · intro h
        by_cases hz : h.val = 0
        · rw [hz, l18Risk2ShiftRight_zero ring e]
          exact he0
        · have hval : h.val < m + 1 := h.isLt
          let hp : Fin ((m - 1) + 1) :=
            ⟨h.val - 1, by omega⟩
          have hs := hRisk.2 hp
          have hsite :
              PPL.shiftRight ring
                  (ring.rightNeighbor e) hp.val =
                PPL.shiftRight ring e h.val := by
            change
              PPL.shiftRight ring
                  (PPL.shiftRight ring e 1) hp.val =
                PPL.shiftRight ring e h.val
            calc
              PPL.shiftRight ring
                  (PPL.shiftRight ring e 1) hp.val =
                  PPL.shiftRight ring e (1 + hp.val) :=
                l18Risk2ShiftRight_add
                  ring e 1 hp.val
              _ = PPL.shiftRight ring e h.val := by
                congr 2
                dsimp only [hp]
                omega
          rw [hsite] at hs
          exact hs


private theorem q20230_safe_black_code_not_risky
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (D : Config n psi kappa)
    (i : Fin n)
    (hi : PPL.cyclicOffset ring root i < psi)
    (t : TokenData psi)
    (ht : PPL.tokenAt .black (D i) = some t)
    (hcode :
      (PPL.decodeOffset psi (PPL.tokenCode t) < 0) \/
        (PPL.decodeOffset psi (PPL.tokenCode t) =
          ((psi : Nat) : Int))) :
    Not (PPL.tokenRisky ring root D i .black) := by
  let j := PPL.cyclicOffset ring root i
  have hj : j < psi := by
    dsimp only [j]
    exact hi
  have hsite :
      PPL.shiftRight ring root j = i := by
    dsimp only [j]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root i
  have hsafe :
      forall u : TokenData psi,
        PPL.tokenAt .black
            (D (PPL.shiftRight ring root j)) = some u ->
        (PPL.decodeOffset psi (PPL.tokenCode u) < 0) \/
          (PPL.decodeOffset psi (PPL.tokenCode u) =
            ((psi : Nat) : Int)) := by
    intro u hu
    rw [hsite] at hu
    have hut : u = t :=
      Option.some.inj (hu.symm.trans ht)
    subst u
    exact hcode
  have hnr :=
    l18Risk2SafeCode_not_tokenRisky
      hpsi hlt ring root D j hj .black hsafe
  rw [hsite] at hnr
  exact hnr


private theorem q20230_fresh_black_not_risky
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : CDLAt ring root C)
    (hroot : Not (ring.rightNeighbor e = root))
    (hroff :
      PPL.cyclicOffset ring root
          (ring.rightNeighbor e) < psi)
    (t' : TokenData psi)
    (hDtok :
      PPL.tokenAt .black
          ((pprimeStep ring C e)
            (ring.rightNeighbor e)) = some t')
    (hborder : PPL.IsBorder C e)
    (hcode :
      PPL.decodeOffset psi (PPL.tokenCode t') =
        ((psi - 1 : Nat) : Int)) :
    Not
      (PPL.tokenRisky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e) .black) := by
  have hoff :=
    l18Gapped_rightNeighbor_offset_of_ne_root
      ring root e hroot
  let j := PPL.cyclicOffset ring root e
  have hj : j < psi := by
    dsimp only [j]
    have hr := hroff
    rw [hoff] at hr
    omega


  have hgeom := hC.2.2 e
  dsimp only at hgeom
  have hj2 : j < 2 * psi := by
    omega
  have hdistC : (C e).dist.val = j := by
    calc
      (C e).dist.val =
          PPL.cyclicOffset ring root e % (2 * psi) :=
        hgeom.1
      _ = j % (2 * psi) := by
        rfl
      _ = j := Nat.mod_eq_of_lt hj2


  have hborder0 := hborder
  unfold PPL.IsBorder at hborder0
  have hj0 : j = 0 := by
    rcases hborder0 with hb0 | hbpsi
    · rw [hdistC] at hb0
      exact hb0
    · rw [hdistC] at hbpsi
      omega


  have hoff0 :
      PPL.cyclicOffset ring root e = 0 := by
    simpa [j] using hj0
  have hshift :=
    l18Risk2ShiftRight_cyclicOffset
      ring root e
  rw [hoff0, l18Risk2ShiftRight_zero ring root] at hshift
  have heroot : e = root := hshift.symm


  intro hRisk
  unfold PPL.tokenRisky at hRisk
  rw [hDtok] at hRisk
  dsimp only at hRisk
  rw [hcode] at hRisk
  try dsimp only at hRisk
  have hout :=
    hRisk.2
      (⟨psi - 1, by omega⟩ :
        Fin ((psi - 1) + 1))
  have hsite :
      PPL.shiftRight ring
          (ring.rightNeighbor e) (psi - 1) =
        PPL.shiftRight ring root psi := by
    change
      PPL.shiftRight ring
          (PPL.shiftRight ring e 1) (psi - 1) =
        PPL.shiftRight ring root psi
    calc
      PPL.shiftRight ring
          (PPL.shiftRight ring e 1) (psi - 1) =
          PPL.shiftRight ring e (1 + (psi - 1)) :=
        l18Risk2ShiftRight_add
          ring e 1 (psi - 1)
      _ = PPL.shiftRight ring e psi := by
        congr 2
        omega
      _ = PPL.shiftRight ring root psi := by
        rw [heroot]
  rw [hsite] at hout
  exact
    (l18Risk2OutsideS0AtPsi
      hlt ring root) hout


/--
Literal residual for the wrap case.  Once canonical last=true at the
predecessor has closed line 13, any surviving black responder token is the
same old responder token.  The remaining proof is only the pprimeCreateLeader
black/right projection (sourceClear may delete, never invent, on this branch).
-/
def L18GappedRiskyInsertedResponderWrapBlackTokenFrame : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    ring.rightNeighbor e = root ->
    (C e).last = true ->
    forall t : TokenData psi,
      PPL.tokenAt .black
          ((pprimeStep ring C e)
            (ring.rightNeighbor e)) = some t ->
      PPL.tokenAt .black
          (C (ring.rightNeighbor e)) = some t


/--
Literal residual for the nonwrap case.  A black token surviving on the
responder is either the same old responder token, a positive old initiator
token shifted by one, a code already covered by l18Risk2SafeCode_not_tokenRisky,
or the fresh border birth after its immediate right move.
-/
def L18GappedRiskyInsertedResponderNonwrapBlackTokenShapes : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    Not (ring.rightNeighbor e = root) ->
    PPL.cyclicOffset ring root
        (ring.rightNeighbor e) < psi ->
    forall t' : TokenData psi,
      PPL.tokenAt .black
          ((pprimeStep ring C e)
            (ring.rightNeighbor e)) = some t' ->
      (PPL.tokenAt .black
          (C (ring.rightNeighbor e)) = some t') \/
      (Exists fun t : TokenData psi =>
        (PPL.tokenAt .black (C e) = some t) /\
        (2 <= PPL.decodeOffset psi (PPL.tokenCode t)) /\
        (PPL.decodeOffset psi (PPL.tokenCode t') =
          PPL.decodeOffset psi (PPL.tokenCode t) - 1)) \/
      ((PPL.decodeOffset psi (PPL.tokenCode t') < 0) \/
        (PPL.decodeOffset psi (PPL.tokenCode t') =
          ((psi : Nat) : Int))) \/
      ((PPL.IsBorder C e) /\
        (PPL.decodeOffset psi (PPL.tokenCode t') =
          ((psi - 1 : Nat) : Int)))


theorem l18GappedRiskyInsertedResponderWrapBlackCase_of_tokenFrame
    (hFrame :
      L18GappedRiskyInsertedResponderWrapBlackTokenFrame) :
    L18GappedRiskyInsertedResponderWrapBlackCase := by
  unfold
    L18GappedRiskyInsertedResponderWrapBlackTokenFrame
    at hFrame
  unfold L18GappedRiskyInsertedResponderWrapBlackCase
  intro n psi kappa
  intro hn3 hpsi hlt ring root C e
  intro hC hroot hpre
  have hlast :=
    q20230_wrap_last_true
      hn3 hpsi ring root C e hC hroot
  intro hRisk
  cases ht :
      PPL.tokenAt .black
        ((pprimeStep ring C e)
          (ring.rightNeighbor e)) with
  | none =>
      unfold PPL.tokenRisky at hRisk
      simp [ht] at hRisk
  | some t =>
      have hsame :=
        hFrame
          hn3 hpsi hlt ring root C e
          hC hroot hlast t ht
      have hpreRisk :=
        q20230_same_black_risky_pre
          ring root C (pprimeStep ring C e)
          (ring.rightNeighbor e) t
          hsame ht hRisk
      exact hpre hpreRisk


theorem l18GappedRiskyInsertedResponderNonwrapBlackCase_of_tokenShapes
    (hShapes :
      L18GappedRiskyInsertedResponderNonwrapBlackTokenShapes) :
    L18GappedRiskyInsertedResponderNonwrapBlackCase := by
  unfold
    L18GappedRiskyInsertedResponderNonwrapBlackTokenShapes
    at hShapes
  unfold L18GappedRiskyInsertedResponderNonwrapBlackCase
  intro n psi kappa
  intro hn3 hpsi hlt ring root C e
  intro hC hroot hroff hpreE hpreR
  intro hRisk


  cases ht :
      PPL.tokenAt .black
        ((pprimeStep ring C e)
          (ring.rightNeighbor e)) with
  | none =>
      unfold PPL.tokenRisky at hRisk
      simp [ht] at hRisk
  | some t' =>
      have hs :=
        hShapes
          hn3 hpsi hlt ring root C e
          hC hroot hroff t' ht
      rcases hs with hsame | hs
      · have hpreRisk :=
          q20230_same_black_risky_pre
            ring root C (pprimeStep ring C e)
            (ring.rightNeighbor e) t'
            hsame ht hRisk
        exact hpreR hpreRisk
      · rcases hs with hmoved | hs
        · rcases hmoved with
            ⟨t, hCtok, hc2, hc'⟩
          have he0 :=
            q20230_predecessor_in_s0
              hlt ring root e hroot hroff
          have hpreRisk :=
            q20230_moved_black_risky_pre
              ring root C (pprimeStep ring C e)
              e t t' hCtok ht hc2 hc' he0 hRisk
          exact hpreE hpreRisk
        · rcases hs with hsafe | hfresh
          · exact
              (q20230_safe_black_code_not_risky
                hpsi hlt ring root
                (pprimeStep ring C e)
                (ring.rightNeighbor e)
                hroff t' ht hsafe) hRisk
          · rcases hfresh with
              ⟨hborder, hcode⟩
            exact
              (q20230_fresh_black_not_risky
                hpsi hlt ring root C e
                hC hroot hroff t'
                ht hborder hcode) hRisk


end PPL.Convergence.L18


#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapBlackCase_of_tokenFrame
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapBlackCase_of_tokenShapes
