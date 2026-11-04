import Leader.PPL.ReachCPB.MismatchHistFreshBranchRow
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

private theorem q19927_shiftRight_zero
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt i.isLt]

private theorem q19927_shiftRight_n
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftRight ring i n = i := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.add_mod,
    Nat.mod_eq_of_lt i.isLt]

private theorem q19927_shiftLeft_n
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    PPL.shiftLeft ring i n = i := by
  apply Fin.ext
  simp [PPL.shiftLeft, Nat.mod_eq_of_lt i.isLt]

private theorem q19927_shiftRight_add
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (a d : Nat) :
    PPL.shiftRight ring
        (PPL.shiftRight ring i a) d =
      PPL.shiftRight ring i (a + d) := by
  apply Fin.ext
  change
    (((i.val + a) % n + d) % n) =
      (i.val + (a + d)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem q19927_shiftLeft_eq_shiftRight_sub
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) :
    PPL.shiftLeft ring i d =
      PPL.shiftRight ring i (n - d) := by
  apply Fin.ext
  simp only [PPL.shiftLeft, PPL.shiftRight]
  rw [Nat.mod_eq_of_lt hd]
  have hs :
      i.val + n - d =
        i.val + (n - d) := by
    omega
  rw [hs]

private theorem q19927_shiftRight_shiftLeft_cancel
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d : Nat)
    (hd : d < n) :
    PPL.shiftRight ring
        (PPL.shiftLeft ring i d) d = i := by
  rw [q19927_shiftLeft_eq_shiftRight_sub
    ring i d hd]
  rw [q19927_shiftRight_add]
  have hs : n - d + d = n := by
    omega
  rw [hs, q19927_shiftRight_n]

private theorem q19927_shiftLeft_shiftRight_sub
    {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (d k : Nat)
    (hk : k <= d) (hd : d < n) :
    PPL.shiftLeft ring
        (PPL.shiftRight ring i d) k =
      PPL.shiftRight ring i (d - k) := by
  apply Fin.ext
  unfold PPL.shiftLeft PPL.shiftRight
  change
    (((i.val + d) % n + n - k % n) % n) =
      (i.val + (d - k)) % n
  have hklt : k < n :=
    Nat.lt_of_le_of_lt hk hd
  rw [Nat.mod_eq_of_lt hklt]
  by_cases hs : i.val + d < n
  · rw [Nat.mod_eq_of_lt hs]
    have heq :
        i.val + d + n - k =
          n + (i.val + (d - k)) := by
      omega
    rw [heq, Nat.add_mod_left]
  · have hge : n <= i.val + d := by
      omega
    have hlt : i.val + d - n < n := by
      omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hlt]
    have heq :
        i.val + d - n + n - k =
          i.val + (d - k) := by
      omega
    rw [heq]

private theorem q19927_scanDistance_some_bounds
    {n : Nat}
    (site : Nat -> Fin n)
    (hit : Fin n -> Bool) :
    forall fuel start r,
      PPL.scanDistance site hit fuel start =
        some r ->
      And
        (start <= r)
        (r < start + fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start r h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start r h
      cases hh : hit (site start) with
      | false =>
          have ht :
              PPL.scanDistance site hit fuel
                  (start + 1) =
                some r := by
            simpa [PPL.scanDistance, hh] using h
          have hb := ih (start + 1) r ht
          exact
            And.intro
              (by omega)
              (by omega)
      | true =>
          have hr : r = start := by
            have h' := h
            simp [PPL.scanDistance, hh] at h'
            exact h'.symm
          subst r
          exact
            And.intro
              (Nat.le_refl _)
              (by omega)

private theorem q19927_scanDistance_some_false_before
    {n : Nat}
    (site : Nat -> Fin n)
    (hit : Fin n -> Bool) :
    forall fuel start r,
      PPL.scanDistance site hit fuel start =
        some r ->
      forall d,
        start <= d ->
        d < r ->
        hit (site d) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start r h
      simp [PPL.scanDistance] at h
  | succ fuel ih =>
      intro start r h d hstart hd
      cases hh : hit (site start) with
      | false =>
          by_cases heq : d = start
          · subst d
            exact hh
          · have ht :
                PPL.scanDistance site hit fuel
                    (start + 1) =
                  some r := by
              simpa [PPL.scanDistance, hh] using h
            exact
              ih (start + 1) r ht d
                (by omega) hd
      | true =>
          have hr : r = start := by
            have h' := h
            simp [PPL.scanDistance, hh] at h'
            exact h'.symm
          omega

private theorem q19927_scanDistance_none_false_in_range
    {n : Nat}
    (site : Nat -> Fin n)
    (hit : Fin n -> Bool) :
    forall fuel start,
      PPL.scanDistance site hit fuel start = none ->
      forall d,
        start <= d ->
        d < start + fuel ->
        hit (site d) = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro start _h d _hstart hd
      omega
  | succ fuel ih =>
      intro start h d hstart hd
      cases hh : hit (site start) with
      | false =>
          by_cases heq : d = start
          · subst d
            exact hh
          · have ht :
                PPL.scanDistance site hit fuel
                    (start + 1) =
                  none := by
              simpa [PPL.scanDistance, hh] using h
            exact
              ih (start + 1) ht d
                (by omega) (by omega)
      | true =>
          simp [PPL.scanDistance, hh] at h

private theorem q19927_isBorderBool_true_of_border
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (i : Fin n)
    (h : PPL.IsBorder C i) :
    PPL.isBorderBool C i = true := by
  unfold PPL.IsBorder at h
  rcases h with h0 | hpsi
  · simp [PPL.isBorderBool, h0]
  · simp [PPL.isBorderBool, hpsi]

private theorem q19927_cd_twoPsi_le_n
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (k : Fin n)
    (kind : PPL.TokenKind)
    (hCd : PPL.Cd ring k kind C) :
    2 * psi <= n := by
  have hnpos : 0 < n := ring.hn
  by_cases hlt : n < 2 * psi
  · let x0 : Fin (2 * psi) :=
      ⟨0, by omega⟩
    let xn : Fin (2 * psi) :=
      ⟨n, hlt⟩
    have h0 := hCd x0
    have hn := hCd xn
    dsimp only [x0] at h0
    dsimp only [xn] at hn
    rw [q19927_shiftRight_zero ring k] at h0
    rw [q19927_shiftRight_n ring k] at hn
    have heq :
        (0 + PPL.tokenD' psi kind) %
              (2 * psi) =
          (n + PPL.tokenD' psi kind) %
              (2 * psi) :=
      h0.1.symm.trans hn.1
    cases kind with
    | black =>
        have hz : 0 = n := by
          simpa
            [PPL.tokenD',
              Nat.mod_eq_of_lt hlt] using heq
        omega
    | white =>
        have hpsiLt : psi < 2 * psi := by
          omega
        have heq' :
            psi =
              (n + psi) % (2 * psi) := by
          simpa
            [PPL.tokenD',
              Nat.mod_eq_of_lt hpsiLt] using heq
        by_cases hnpsi : n < psi
        · have hsumlt :
              n + psi < 2 * psi := by
            omega
          rw [Nat.mod_eq_of_lt hsumlt] at heq'
          omega
        · have hsum :
              n + psi =
                2 * psi + (n - psi) := by
            omega
          have htail :
              n - psi < 2 * psi := by
            omega
          rw [hsum, Nat.add_mod_left,
            Nat.mod_eq_of_lt htail] at heq'
          omega
  · omega

private theorem q19927_cd_border_at_psi
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (k : Fin n)
    (kind : PPL.TokenKind)
    (hCd : PPL.Cd ring k kind C) :
    PPL.IsBorder C
      (PPL.shiftRight ring k psi) := by
  have hx :=
    hCd (⟨psi, by omega⟩ :
      Fin (2 * psi))
  dsimp only at hx
  unfold PPL.IsBorder
  cases kind with
  | black =>
      exact
        Or.inr (by
          simpa
            [PPL.tokenD',
              Nat.mod_eq_of_lt
                (by omega : psi < 2 * psi)]
            using hx.1)
  | white =>
      have hs : psi + psi = 2 * psi := by
        omega
      exact
        Or.inl (by
          simpa [PPL.tokenD', hs] using hx.1)

private theorem q19927_cd_not_border_before_psi
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (k : Fin n)
    (kind : PPL.TokenKind)
    (hCd : PPL.Cd ring k kind C)
    (x : Nat)
    (hx0 : 0 < x)
    (hxpsi : x < psi) :
    Not
      (PPL.IsBorder C
        (PPL.shiftRight ring k x)) := by
  intro hb
  unfold PPL.IsBorder at hb
  have hx :=
    hCd (⟨x, by omega⟩ :
      Fin (2 * psi))
  dsimp only at hx
  cases kind with
  | black =>
      have hv :
          (C (PPL.shiftRight ring k x)).dist.val =
            x := by
        simpa
          [PPL.tokenD',
            Nat.mod_eq_of_lt
              (by omega : x < 2 * psi)]
          using hx.1
      rcases hb with h0 | hp
      · omega
      · omega
  | white =>
      have hsumlt :
          x + psi < 2 * psi := by
        omega
      have hv :
          (C (PPL.shiftRight ring k x)).dist.val =
            x + psi := by
        simpa
          [PPL.tokenD',
            Nat.mod_eq_of_lt hsumlt]
          using hx.1
      rcases hb with h0 | hp
      · omega
      · omega

/--
A bad-border witness already contains the geometry missing from the earlier row.

No LastReady, history, or frozen-state premise is needed.  The conclusion is
purely static in ring, b, k, and psi.
-/
theorem lemma16PostEpochFreshBorderGeometry_of_badBorderWitness
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (hbad :
      Lemma16BadBorderWitness
        ring C b k kind) :
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi := by
  unfold Lemma16BadBorderWitness at hbad
  rcases hbad with
    ⟨hborder, hprev, hCd, _hmismatch⟩

  have h2psi :
      2 * psi <= n :=
    q19927_cd_twoPsi_le_n
      hpsi ring C k kind hCd
  have hpsiN : psi < n := by
    omega

  unfold Lemma16PostEpochFreshBorderGeometry

  let site : Nat -> Fin n :=
    fun d => PPL.shiftLeft ring b d

  cases hs :
      PPL.scanDistance site
        (PPL.isBorderBool C) n 1 with
  | none =>
      have hfalse :=
        q19927_scanDistance_none_false_in_range
          site (PPL.isBorderBool C)
          n 1 hs n
          (by omega) (by omega)
      have hsiteN : site n = b := by
        dsimp only [site]
        exact q19927_shiftLeft_n ring b
      rw [hsiteN] at hfalse
      have htrue :=
        q19927_isBorderBool_true_of_border
          C b hborder
      rw [htrue] at hfalse
      cases hfalse

  | some dp =>
      have hdpDef :
          PPL.prevBorderDistance ring C b =
            dp := by
        simp [PPL.prevBorderDistance, site, hs]
      rw [hdpDef] at hprev

      have hbounds :=
        q19927_scanDistance_some_bounds
          site (PPL.isBorderBool C)
          n 1 dp hs
      have hdpPos : 1 <= dp :=
        hbounds.1
      have hdpLeN : dp <= n := by
        omega

      have hmin :=
        q19927_scanDistance_some_false_before
          site (PPL.isBorderBool C)
          n 1 dp hs

      have hnotLt :
          Not (dp < psi) := by
        intro hdpLt
        have hdpN : dp < n := by
          omega
        have hcancel :=
          q19927_shiftRight_shiftLeft_cancel
            ring b dp hdpN
        have hbEq :
            b =
              PPL.shiftRight ring k dp := by
          calc
            b =
                PPL.shiftRight ring
                  (PPL.shiftLeft ring b dp) dp :=
              hcancel.symm
            _ =
                PPL.shiftRight ring k dp := by
              rw [← hprev]
        have hbAt :
            PPL.IsBorder C
              (PPL.shiftRight ring k dp) := by
          rw [← hbEq]
          exact hborder
        exact
          (q19927_cd_not_border_before_psi
            hpsi ring C k kind hCd
            dp (by omega) hdpLt) hbAt

      have hnotGt :
          Not (psi < dp) := by
        intro hpsiDp
        let d0 := dp - psi
        have hd0Pos : 1 <= d0 := by
          dsimp only [d0]
          omega
        have hd0Lt : d0 < dp := by
          dsimp only [d0]
          omega

        have hsiteEq :
            site d0 =
              PPL.shiftRight ring k psi := by
          by_cases hdpN : dp < n
          · have hcancel :=
              q19927_shiftRight_shiftLeft_cancel
                ring b dp hdpN
            have hbEq :
                b =
                  PPL.shiftRight ring k dp := by
              calc
                b =
                    PPL.shiftRight ring
                      (PPL.shiftLeft ring b dp) dp :=
                  hcancel.symm
                _ =
                    PPL.shiftRight ring k dp := by
                  rw [← hprev]
            dsimp only [site, d0]
            rw [hbEq]
            rw [
              q19927_shiftLeft_shiftRight_sub
                ring k dp (dp - psi)
                (by omega) hdpN]
            have hsub :
                dp - (dp - psi) = psi := by
              omega
            rw [hsub]
          · have hdpEqN : dp = n := by
              omega
            have hkEq : k = b := by
              calc
                k =
                    PPL.shiftLeft ring b dp :=
                  hprev
                _ =
                    PPL.shiftLeft ring b n := by
                  rw [hdpEqN]
                _ = b :=
                  q19927_shiftLeft_n ring b
            dsimp only [site, d0]
            rw [hdpEqN, hkEq]
            have hd :
                n - psi < n := by
              omega
            calc
              PPL.shiftLeft ring b (n - psi) =
                  PPL.shiftRight ring b
                    (n - (n - psi)) :=
                q19927_shiftLeft_eq_shiftRight_sub
                  ring b (n - psi) hd
              _ =
                  PPL.shiftRight ring b psi := by
                congr 2
                omega

        have hborderSite :
            PPL.IsBorder C (site d0) := by
          rw [hsiteEq]
          exact
            q19927_cd_border_at_psi
              hpsi ring C k kind hCd

        have hfalse :=
          hmin d0 hd0Pos hd0Lt
        have htrue :=
          q19927_isBorderBool_true_of_border
            C (site d0) hborderSite
        rw [htrue] at hfalse
        cases hfalse

      have hdpEq : dp = psi := by
        omega
      have hprevPsi :
          k =
            PPL.shiftLeft ring b psi := by
        simpa [hdpEq] using hprev
      have hcancel :=
        q19927_shiftRight_shiftLeft_cancel
          ring b psi hpsiN
      calc
        b =
            PPL.shiftRight ring
              (PPL.shiftLeft ring b psi) psi :=
          hcancel.symm
        _ =
            PPL.shiftRight ring k psi := by
          rw [← hprevPsi]

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshBorderGeometry_of_badBorderWitness
