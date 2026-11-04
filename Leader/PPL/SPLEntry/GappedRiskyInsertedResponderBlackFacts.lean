import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderBlack

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

private theorem q20237_sourceClear_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      tokenAt kind (PPL.sourceClear kind q) = some t) :
    tokenAt kind q = some t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      rw [hq] at h
      dsimp only at h
      by_cases hv : l18Risk2LocalValid kind q u
      · rw [if_pos hv] at h
        rw [hq] at h
        exact h
      · rw [if_neg hv] at h
        unfold l18Risk2SetToken at h
        cases kind <;> simp [tokenAt] at h

private theorem q20237_sourceClear_dist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).dist = q.dist := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : tokenAt kind q with
  | none =>
      rfl
  | some u =>
      by_cases hv : l18Risk2LocalValid kind q u
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem q20237_determineMode_frame
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    d.1.dist = l.dist
      /\ tokenAt kind d.1 = tokenAt kind l
      /\ tokenAt kind d.2 = tokenAt kind r := by
  cases kind <;>
    simp only [PPL.determineMode, tokenAt]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl, rfl⟩

private theorem q20237_preToken_frame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    let p := l18Risk2PreTokenPair hpsi l r
    p.1.dist = l.dist
      /\ tokenAt kind p.1 = tokenAt kind l
      /\ tokenAt kind p.2 = tokenAt kind r := by
  let d := PPL.determineMode l r
  have hd0 := q20237_determineMode_frame kind l r
  have hd :
      d.1.dist = l.dist
        /\ tokenAt kind d.1 = tokenAt kind l
        /\ tokenAt kind d.2 = tokenAt kind r := by
    simpa [d] using hd0

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
        r1.dist.val = 0 \/
          r1.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r1.last }

  have hrTok :
      tokenAt kind r1 = tokenAt kind r := by
    simpa [r1, tokenAt] using hd.2.2
  have hlDist :
      l1.dist = l.dist := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead] using hd.1
    · by_cases hb :
          r1.dist.val = 0 \/
            r1.dist.val = psi
      · simpa [l1, hlead, hb] using hd.1
      · simpa [l1, hlead, hb] using hd.1
  have hlTok :
      tokenAt kind l1 = tokenAt kind l := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead, tokenAt] using hd.2.1
    · by_cases hb :
          r1.dist.val = 0 \/
            r1.dist.val = psi
      · simpa [l1, hlead, hb, tokenAt] using hd.2.1
      · simpa [l1, hlead, hb, tokenAt] using hd.2.1

  let p := l18Risk2PreTokenPair hpsi l r
  have hp : p = (l1, r1) := by
    rfl
  change
    p.1.dist = l.dist
      /\ tokenAt kind p.1 = tokenAt kind l
      /\ tokenAt kind p.2 = tokenAt kind r
  rw [hp]
  exact ⟨hlDist, hlTok, hrTok⟩

private theorem q20237_eliminate_right_black
    {psi kappa : Nat}
    (l r : State psi kappa) :
    tokenAt .black (PPL.eliminateLeaders l r).2 =
      tokenAt .black r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right l r
  have ht :=
    congrArg
      (fun q : PPL.Elim.OtherFields psi kappa =>
        q.tokenB) h
  simpa [PPL.Elim.otherView, tokenAt] using ht

private theorem q20237_white_preserves_black_right
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    tokenAt .black
        (pprimeMoveToken hpsi .white l r).2 =
      tokenAt .black r := by
  unfold pprimeMoveToken
  dsimp only
  rcases
      PPL.moveToken_responder_fields
        hpsi TokenKind.white
        l { r with mode := false } with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenB) hr
    simpa
      [PPL.eraseKindTokenId, PPL.eraseKindToken,
        PPL.tokenAt]
      using hrr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenB) hr
    simpa
      [PPL.eraseKindTokenId, PPL.eraseKindToken,
        PPL.birthFields, PPL.tokenAt]
      using hrr

private theorem q20237_step_right_black_move
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n)
    (t : TokenData psi)
    (hpost :
      tokenAt .black
          ((pprimeStep ring C e)
            (ring.rightNeighbor e)) = some t) :
    tokenAt .black
        (pprimeMoveToken hpsi .black
          (l18Risk2PreTokenPair hpsi
            (C e) (C (ring.rightNeighbor e))).1
          (l18Risk2PreTokenPair hpsi
            (C e) (C (ring.rightNeighbor e))).2).2 =
      some t := by
  let rsite := ring.rightNeighbor e
  let p :=
    l18Risk2PreTokenPair hpsi (C e) (C rsite)
  let b :=
    pprimeMoveToken hpsi .black p.1 p.2
  let w :=
    pprimeMoveToken hpsi .white b.1 b.2

  have h := hpost
  rw [l18Risk2PPrimeStepRight
    hn3 hpsi ring C e] at h

  have hcreate :
      pprimeCreateLeader hpsi
          (C e) (C rsite) = w := by
    rfl

  change
    tokenAt .black
        (PPL.eliminateLeaders
          (pprimeCreateLeader
            hpsi (C e) (C rsite)).1
          (pprimeCreateLeader
            hpsi (C e) (C rsite)).2).2 =
      some t at h
  rw [hcreate] at h

  have helim :=
    q20237_eliminate_right_black w.1 w.2
  rw [helim] at h

  have hwhite :
      tokenAt .black w.2 =
        tokenAt .black b.2 := by
    dsimp only [w]
    exact
      q20237_white_preserves_black_right
        hpsi b.1 b.2
  rw [hwhite] at h

  simpa [b, p, rsite] using h

private theorem q20237_open_right_same
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (PPL.sourceClear kind l).last = false
        /\ (PPL.sourceClear kind r).last = false)
    (hsource :
      tokenAt kind
          (PPL.sourceClear kind r) = some t)
    (hq :
      tokenAt kind
          (PPL.moveToken hpsi kind l r).2 = some t') :
    t' = t := by
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi kind l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq
  cases hl :
      tokenAt kind (PPL.sourceClear kind l) with
  | none =>
      by_cases hdist :
          (PPL.sourceClear kind l).dist.val =
            PPL.tokenD' psi kind
      · by_cases hm1 :
            PPL.decodeOffset psi
              (PPL.tokenCode t) = -1
        · have hf : False := by
            simpa
              [hl, hdist, hsource, hm1,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · by_cases hm2 :
              PPL.decodeOffset psi
                (PPL.tokenCode t) <= -2
          · have hf : False := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact heq.symm
      · by_cases hm1 :
            PPL.decodeOffset psi
              (PPL.tokenCode t) = -1
        · have hf : False := by
            simpa
              [hl, hdist, hsource, hm1,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · by_cases hm2 :
              PPL.decodeOffset psi
                (PPL.tokenCode t) <= -2
          · have hf : False := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa
                [hl, hdist, hsource, hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact heq.symm
  | some u =>
      by_cases hm1 :
          PPL.decodeOffset psi
            (PPL.tokenCode t) = -1
      · have hf : False := by
          simpa
            [hl, hsource, hm1,
              l18Risk2SourceSet_tokenAt]
            using hq
        exact False.elim hf
      · by_cases hm2 :
            PPL.decodeOffset psi
              (PPL.tokenCode t) <= -2
        · have hf : False := by
            simpa
              [hl, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · have heq : t = t' := by
            simpa
              [hl, hsource, hm1, hm2,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact heq.symm

private theorem q20237_open_left_shape
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (PPL.sourceClear kind l).last = false
        /\ (PPL.sourceClear kind r).last = false)
    (hleft :
      tokenAt kind
          (PPL.sourceClear kind l) = some t)
    (hrnone :
      tokenAt kind
          (PPL.sourceClear kind r) = none)
    (hq :
      tokenAt kind
          (PPL.moveToken hpsi kind l r).2 = some t') :
    (PPL.decodeOffset psi (PPL.tokenCode t') < 0)
      \/ ((2 <=
            PPL.decodeOffset psi (PPL.tokenCode t))
        /\ PPL.decodeOffset psi (PPL.tokenCode t') =
          PPL.decodeOffset psi (PPL.tokenCode t) - 1) := by
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi kind l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq

  by_cases hc1 :
      PPL.decodeOffset psi (PPL.tokenCode t) = 1
  · have heq :
        l18Risk2MkToken
            (PPL.offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2 =
          t' := by
      simpa
        [hleft, hrnone, hc1,
          l18Risk2SourceSet_tokenAt]
        using hq
    have hdec :=
      congrArg
        (fun u : TokenData psi =>
          PPL.decodeOffset psi (PPL.tokenCode u))
        heq.symm
    left
    have hturn :
        PPL.decodeOffset psi (PPL.tokenCode t') =
          1 - ((psi : Nat) : Int) := by
      simpa
        [l18Risk2MkToken, PPL.tokenCode,
          PPL.decodeOffset_negPsiPlusOne]
        using hdec
    omega
  · by_cases hc2 :
        2 <=
          PPL.decodeOffset psi (PPL.tokenCode t)
    · have heq :
          l18Risk2MkToken
              (PPL.encodeOffset psi
                (PPL.decodeOffset psi
                    (PPL.tokenCode t) - 1)
                (by
                  have hv :=
                    PPL.decodeOffset_valid
                      psi (by omega) (PPL.tokenCode t)
                  rcases hv with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
              t.1.2 t.2 =
            t' := by
        simpa
          [hleft, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq
      have hdec :=
        congrArg
          (fun u : TokenData psi =>
            PPL.decodeOffset psi (PPL.tokenCode u))
          heq.symm
      right
      refine ⟨hc2, ?_⟩
      simpa
        [l18Risk2MkToken, PPL.tokenCode,
          PPL.decode_encode]
        using hdec
    · have hf : False := by
        simpa
          [hleft, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq
      exact False.elim hf

private theorem q20237_fresh_right_code
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t' : TokenData psi)
    (hgate :
      (PPL.sourceClear .black l).last = false
        /\ (PPL.sourceClear .black r).last = false)
    (hlnone :
      tokenAt .black
          (PPL.sourceClear .black l) = none)
    (hrnone :
      tokenAt .black
          (PPL.sourceClear .black r) = none)
    (hdist :
      (PPL.sourceClear .black l).dist.val =
        PPL.tokenD' psi .black)
    (hq :
      tokenAt .black
          (PPL.moveToken hpsi .black l r).2 = some t') :
    PPL.decodeOffset psi (PPL.tokenCode t') =
      ((psi : Nat) : Int) - 1 := by
  have hpsiNeOne :
      ((psi : Nat) : Int) ≠ 1 := by
    omega
  have hpsiGeTwo :
      (2 : Int) <= ((psi : Nat) : Int) := by
    omega
  rw [← l18Risk2MoveTokenMirror_eq
    hpsi TokenKind.black l r] at hq
  unfold l18Risk2MoveTokenMirror at hq
  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq
  simp
    [hlnone, hrnone, hdist,
      PPL.tokenD', l18Risk2SourceSet_tokenAt,
      l18Risk2MkToken, PPL.tokenCode,
      PPL.decodeOffset_psi psi hpsi,
      hpsiNeOne, hpsiGeTwo]
    at hq
  have hdec :=
    congrArg
      (fun u : TokenData psi =>
        PPL.decodeOffset psi (PPL.tokenCode u))
      hq.symm
  simpa
    [l18Risk2MkToken, PPL.tokenCode,
      PPL.decode_encode]
    using hdec

theorem
    l18GappedRiskyInsertedResponderWrapBlackTokenFrame_proved :
    L18GappedRiskyInsertedResponderWrapBlackTokenFrame := by
  unfold L18GappedRiskyInsertedResponderWrapBlackTokenFrame
  intro n psi kappa
  intro hn3 hpsi _hlt ring root C e
  intro hC hroot _hlast
  intro t hpost

  let rsite := ring.rightNeighbor e
  let p :=
    l18Risk2PreTokenPair hpsi (C e) (C rsite)

  have hpre0 :=
    q20237_preToken_frame
      hpsi TokenKind.black (C e) (C rsite)
  have hpre :
      p.1.dist = (C e).dist
        /\ tokenAt .black p.1 = tokenAt .black (C e)
        /\ tokenAt .black p.2 =
          tokenAt .black (C rsite) := by
    simpa [p, rsite] using hpre0

  have hrleader :
      (C rsite).leader = true := by
    exact (hC.2.1 rsite).2 hroot

  have hpf0 :=
    l18Risk2PreTokenPairFields
      hpsi (C e) (C rsite)
  have hplast :
      p.1.last = true := by
    have hx := hpf0.2.2.2
    simpa [p, rsite, hrleader] using hx

  have hq0 :=
    q20237_step_right_black_move
      hn3 hpsi ring C e t hpost
  have hq :
      tokenAt .black
          (pprimeMoveToken
            hpsi .black p.1 p.2).2 = some t := by
    simpa [p, rsite] using hq0

  let rr : State psi kappa :=
    { p.2 with mode := false }
  have hqMove :
      tokenAt .black
          (PPL.moveToken hpsi .black p.1 rr).2 =
        some t := by
    unfold pprimeMoveToken at hq
    dsimp only at hq
    simpa [rr, PPL.tokenAt] using hq

  have hclearL :
      (PPL.sourceClear .black p.1).last = true :=
    (l18Risk2SourceClear_last .black p.1).trans hplast
  have hngate :
      Not
        ((PPL.sourceClear .black p.1).last = false
          /\ (PPL.sourceClear .black rr).last = false) := by
    intro hg
    have hbad : true = false :=
      hclearL.symm.trans hg.1
    cases hbad

  have hframe :
      tokenAt .black
          (PPL.moveToken hpsi .black p.1 rr).2 =
        tokenAt .black (PPL.sourceClear .black rr) := by
    rw [← l18Risk2MoveTokenMirror_eq
      hpsi TokenKind.black p.1 rr]
    simp [l18Risk2MoveTokenMirror, hngate]
  rw [hframe] at hqMove

  have hrr :=
    q20237_sourceClear_some
      TokenKind.black rr t hqMove
  have hp2 :
      tokenAt .black p.2 = some t := by
    simpa [rr, PPL.tokenAt] using hrr
  rw [hpre.2.2] at hp2
  exact hp2

theorem
    l18GappedRiskyInsertedResponderNonwrapBlackTokenShapes_proved :
    L18GappedRiskyInsertedResponderNonwrapBlackTokenShapes := by
  unfold L18GappedRiskyInsertedResponderNonwrapBlackTokenShapes
  intro n psi kappa
  intro hn3 hpsi hlt ring root C e
  intro hC hroot hroff
  intro t' hpost

  let rsite := ring.rightNeighbor e
  let p :=
    l18Risk2PreTokenPair hpsi (C e) (C rsite)

  have hpre0 :=
    q20237_preToken_frame
      hpsi TokenKind.black (C e) (C rsite)
  have hpre :
      p.1.dist = (C e).dist
        /\ tokenAt .black p.1 = tokenAt .black (C e)
        /\ tokenAt .black p.2 =
          tokenAt .black (C rsite) := by
    simpa [p, rsite] using hpre0

  have hoff :=
    l18Gapped_rightNeighbor_offset_of_ne_root
      ring root e hroot
  let j := PPL.cyclicOffset ring root e
  have hj : j < psi := by
    dsimp only [j]
    rw [hoff] at hroff
    omega
  have hinner : j + 1 < psi := by
    dsimp only [j]
    rw [hoff] at hroff
    omega
  have he :
      PPL.shiftRight ring root j = e := by
    dsimp only [j]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root e

  have hopen0 :=
    l18Risk2PreTokenPair_open
      hpsi hlt ring root C j hj hinner hC
  dsimp only at hopen0
  rw [he] at hopen0
  have hopen :
      p.1.last = false
        /\ p.2.last = false := by
    simpa [p, rsite] using hopen0

  have hq0 :=
    q20237_step_right_black_move
      hn3 hpsi ring C e t' hpost
  have hq :
      tokenAt .black
          (pprimeMoveToken
            hpsi .black p.1 p.2).2 = some t' := by
    simpa [p, rsite] using hq0

  let rr : State psi kappa :=
    { p.2 with mode := false }
  have hqMove :
      tokenAt .black
          (PPL.moveToken hpsi .black p.1 rr).2 =
        some t' := by
    unfold pprimeMoveToken at hq
    dsimp only at hq
    simpa [rr, PPL.tokenAt] using hq

  have hrrlast :
      rr.last = false := by
    simpa [rr] using hopen.2
  have hgate :
      (PPL.sourceClear .black p.1).last = false
        /\ (PPL.sourceClear .black rr).last = false := by
    exact
      ⟨(l18Risk2SourceClear_last
          .black p.1).trans hopen.1,
        (l18Risk2SourceClear_last
          .black rr).trans hrrlast⟩

  cases hr :
      tokenAt .black
        (PPL.sourceClear .black rr) with
  | some v =>
      have htt :=
        q20237_open_right_same
          hpsi TokenKind.black
          p.1 rr v t'
          hgate hr hqMove
      subst t'
      have hrr0 :=
        q20237_sourceClear_some
          TokenKind.black rr v hr
      have hp2 :
          tokenAt .black p.2 = some v := by
        simpa [rr, PPL.tokenAt] using hrr0
      rw [hpre.2.2] at hp2
      exact Or.inl hp2

  | none =>
      cases hl :
          tokenAt .black
            (PPL.sourceClear .black p.1) with
      | some u =>
          have hs :=
            q20237_open_left_shape
              hpsi TokenKind.black
              p.1 rr u t'
              hgate hl hr hqMove
          have hcu :=
            q20237_sourceClear_some
              TokenKind.black p.1 u hl
          rw [hpre.2.1] at hcu
          rcases hs with hneg | hmove
          · exact
              Or.inr
                (Or.inr
                  (Or.inl (Or.inl hneg)))
          · rcases hmove with ⟨hc2, hc'⟩
            exact
              Or.inr
                (Or.inl
                  ⟨u, hcu, hc2, hc'⟩)

      | none =>
          by_cases hdist :
              (PPL.sourceClear .black p.1).dist.val =
                PPL.tokenD' psi .black
          · have hcode0 :=
              q20237_fresh_right_code
                hpsi p.1 rr t'
                hgate hl hr hdist hqMove
            have hcode :
                PPL.decodeOffset psi
                    (PPL.tokenCode t') =
                  ((psi - 1 : Nat) : Int) := by
              calc
                PPL.decodeOffset psi
                    (PPL.tokenCode t') =
                    ((psi : Nat) : Int) - 1 :=
                  hcode0
                _ = ((psi - 1 : Nat) : Int) := by
                  omega

            have hdistC :
                (C e).dist.val = 0 := by
              calc
                (C e).dist.val = p.1.dist.val := by
                  exact congrArg Fin.val hpre.1.symm
                _ =
                    (PPL.sourceClear
                      .black p.1).dist.val := by
                  exact
                    congrArg Fin.val
                      (q20237_sourceClear_dist
                        TokenKind.black p.1).symm
                _ = PPL.tokenD' psi .black := hdist
                _ = 0 := by
                  rfl
            have hborder : PPL.IsBorder C e := by
              unfold PPL.IsBorder
              exact Or.inl hdistC
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    ⟨hborder, hcode⟩))

          · have hf : False := by
              have hqBad := hqMove
              rw [← l18Risk2MoveTokenMirror_eq
                hpsi TokenKind.black p.1 rr] at hqBad
              simp
                [l18Risk2MoveTokenMirror,
                  hgate, hl, hr, hdist]
                at hqBad
            exact False.elim hf

theorem
    l18GappedRiskyInsertedResponderWrapBlackCase_proved :
    L18GappedRiskyInsertedResponderWrapBlackCase :=
  l18GappedRiskyInsertedResponderWrapBlackCase_of_tokenFrame
    l18GappedRiskyInsertedResponderWrapBlackTokenFrame_proved

theorem
    l18GappedRiskyInsertedResponderNonwrapBlackCase_proved :
    L18GappedRiskyInsertedResponderNonwrapBlackCase :=
  l18GappedRiskyInsertedResponderNonwrapBlackCase_of_tokenShapes
    l18GappedRiskyInsertedResponderNonwrapBlackTokenShapes_proved

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapBlackTokenFrame_proved
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapBlackTokenShapes_proved
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapBlackCase_proved
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapBlackCase_proved
