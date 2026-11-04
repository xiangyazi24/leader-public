import Leader.PPL.SPLEntry.GappedRiskyInsertedResponderWhite
import Leader.PPL.TransitionFacts
import Leader.PPL.Elim.RowE
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

private theorem q20238SourceClearSome
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (h :
      PPL.tokenAt kind
          (PPL.sourceClear kind q) =
        some t) :
    PPL.tokenAt kind q = some t := by
  rw [l18Risk2SourceClear_eq] at h
  unfold l18Risk2ClearInvalid at h
  cases hq : PPL.tokenAt kind q with
  | none =>
      simp [hq] at h
  | some u =>
      rw [hq] at h
      dsimp only at h
      by_cases hv :
          l18Risk2LocalValid kind q u
      · rw [if_pos hv] at h
        rw [hq] at h
        exact h
      · rw [if_neg hv] at h
        unfold l18Risk2SetToken at h
        cases kind <;>
          simp [PPL.tokenAt] at h

private theorem q20238SourceClearDist
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (PPL.sourceClear kind q).dist =
      q.dist := by
  rw [l18Risk2SourceClear_eq]
  unfold l18Risk2ClearInvalid
  cases hq : PPL.tokenAt kind q with
  | none =>
      rfl
  | some t =>
      by_cases hv :
          l18Risk2LocalValid kind q t
      · simp only [hq, if_pos hv]
      · simp only [hq, if_neg hv]
        unfold l18Risk2SetToken
        cases kind <;> rfl

private theorem q20238DetermineModeWhiteFrame
    {psi kappa : Nat}
    (l r : State psi kappa) :
    let d := PPL.determineMode l r
    PPL.tokenAt .white d.1 =
        PPL.tokenAt .white l
      /\ PPL.tokenAt .white d.2 =
        PPL.tokenAt .white r := by
  simp only [PPL.determineMode, PPL.tokenAt]
  all_goals try
    (split <;> try dsimp only)
  all_goals try
    (split <;> try dsimp only)
  all_goals try
    (split <;> try dsimp only)
  all_goals try
    (split <;> try dsimp only)
  all_goals exact ⟨rfl, rfl⟩

private theorem q20238PreTokenWhiteFrame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    let p :=
      l18Risk2PreTokenPair hpsi l r
    PPL.tokenAt .white p.1 =
        PPL.tokenAt .white l
      /\ PPL.tokenAt .white p.2 =
        PPL.tokenAt .white r := by
  let d := PPL.determineMode l r

  have hd0 :=
    q20238DetermineModeWhiteFrame l r

  have hd :
      PPL.tokenAt .white d.1 =
          PPL.tokenAt .white l
        /\ PPL.tokenAt .white d.2 =
          PPL.tokenAt .white r := by
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
        r1.dist.val = 0
          \/ r1.dist.val = psi then
      { d.1 with last := false }
    else
      { d.1 with last := r1.last }

  have hr :
      PPL.tokenAt .white r1 =
        PPL.tokenAt .white r := by
    simpa [r1, PPL.tokenAt] using hd.2

  have hl :
      PPL.tokenAt .white l1 =
        PPL.tokenAt .white l := by
    by_cases hlead : r1.leader = true
    · simpa [l1, hlead, PPL.tokenAt]
        using hd.1
    · by_cases hb :
        r1.dist.val = 0
          \/ r1.dist.val = psi
      · simpa [l1, hlead, hb, PPL.tokenAt]
          using hd.1
      · simpa [l1, hlead, hb, PPL.tokenAt]
          using hd.1

  let p :=
    l18Risk2PreTokenPair hpsi l r

  have hp : p = (l1, r1) := by
    rfl

  change
    PPL.tokenAt .white p.1 =
        PPL.tokenAt .white l
      /\ PPL.tokenAt .white p.2 =
        PPL.tokenAt .white r

  rw [hp]
  exact ⟨hl, hr⟩

private theorem q20238BlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    PPL.tokenAt .white
        (PPL.moveToken hpsi .black l r).1 =
        PPL.tokenAt .white l
      /\ PPL.tokenAt .white
        (PPL.moveToken hpsi .black l r).2 =
        PPL.tokenAt .white r := by
  have hi :=
    PPL.moveToken_initiator_fields
      hpsi .black l r

  have hil :=
    congrArg
      (fun q : State psi kappa => q.tokenW)
      hi

  have hleft :
      PPL.tokenAt .white
          (PPL.moveToken hpsi .black l r).1 =
        PPL.tokenAt .white l := by
    simpa [PPL.eraseKindToken, PPL.tokenAt]
      using hil

  rcases
      PPL.moveToken_responder_fields
        hpsi .black l r with hr | hr
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenW)
        hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken,
              PPL.tokenAt]
            using hrr⟩
  · have hrr :=
      congrArg
        (fun q : State psi kappa => q.tokenW)
        hr
    exact
      ⟨hleft,
        by
          simpa
            [PPL.eraseKindTokenId,
              PPL.eraseKindToken,
              PPL.birthFields,
              PPL.tokenAt]
            using hrr⟩

private theorem q20238PPrimeBlackPreservesWhite
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa) :
    PPL.tokenAt .white
        (pprimeMoveToken hpsi .black l r).1 =
        PPL.tokenAt .white l
      /\ PPL.tokenAt .white
        (pprimeMoveToken hpsi .black l r).2 =
        PPL.tokenAt .white r := by
  unfold pprimeMoveToken
  dsimp only

  have h :=
    q20238BlackPreservesWhite
      hpsi l { r with mode := false }

  constructor
  · exact h.1
  · simpa [PPL.tokenAt] using h.2

private theorem q20238EliminateRightToken
    {psi kappa : Nat}
    (kind : TokenKind)
    (l r : State psi kappa) :
    PPL.tokenAt kind
        (PPL.eliminateLeaders l r).2 =
      PPL.tokenAt kind r := by
  have h :=
    PPL.Elim.otherView_eliminateLeaders_right
      l r

  cases kind with
  | black =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenB)
          h
      simpa [PPL.Elim.otherView, PPL.tokenAt]
        using ht
  | white =>
      have ht :=
        congrArg
          (fun q : PPL.Elim.OtherFields
            psi kappa => q.tokenW)
          h
      simpa [PPL.Elim.otherView, PPL.tokenAt]
        using ht

private theorem q20238PPrimeStepRightWhite
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e : Fin n) :
    PPL.tokenAt .white
        (pprimeStep ring C e
          (ring.rightNeighbor e)) =
      PPL.tokenAt .white
        (pprimeCreateLeader
          hpsi (C e)
          (C (ring.rightNeighbor e))).2 := by
  rw [
    l18Risk2PPrimeStepRight
      hn3 hpsi ring C e
  ]
  unfold pprimePpl
  dsimp only
  exact
    q20238EliminateRightToken
      .white
      (pprimeCreateLeader
        hpsi (C e)
        (C (ring.rightNeighbor e))).1
      (pprimeCreateLeader
        hpsi (C e)
        (C (ring.rightNeighbor e))).2

private theorem q20238ClosedRightSame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hsource :
      PPL.tokenAt kind
          (PPL.sourceClear kind r) =
        some t)
    (hgate :
      Not
        ((PPL.sourceClear kind l).last = false
          /\ (PPL.sourceClear kind r).last = false))
    (hq :
      PPL.tokenAt kind
          (PPL.moveToken hpsi kind l r).2 =
        some t') :
    t' = t := by
  have hframe :
      PPL.tokenAt kind
          (PPL.moveToken hpsi kind l r).2 =
        PPL.tokenAt kind
          (PPL.sourceClear kind r) := by
    rw [
      ← l18Risk2MoveTokenMirror_eq
        hpsi kind l r
    ]
    simp [l18Risk2MoveTokenMirror, hgate]

  have hs : some t' = some t := by
    calc
      some t' =
          PPL.tokenAt kind
            (PPL.moveToken hpsi kind l r).2 :=
        hq.symm
      _ =
          PPL.tokenAt kind
            (PPL.sourceClear kind r) :=
        hframe
      _ = some t := hsource

  exact Option.some.inj hs

private theorem q20238OpenRightSame
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (PPL.sourceClear kind l).last = false
        /\ (PPL.sourceClear kind r).last = false)
    (hsource :
      PPL.tokenAt kind
          (PPL.sourceClear kind r) =
        some t)
    (hq :
      PPL.tokenAt kind
          (PPL.moveToken hpsi kind l r).2 =
        some t') :
    t' = t := by
  rw [
    ← l18Risk2MoveTokenMirror_eq
      hpsi kind l r
  ] at hq

  unfold l18Risk2MoveTokenMirror at hq

  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq

  cases hl :
      PPL.tokenAt kind
        (PPL.sourceClear kind l) with
  | none =>
      by_cases hdist :
          (PPL.sourceClear kind l).dist.val =
            PPL.tokenD' psi kind
      · by_cases hm1 :
          PPL.decodeOffset psi
              (PPL.tokenCode t) =
            -1
        · have hf : False := by
            simpa
              [hl, hdist, hsource, hm1,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · by_cases hm2 :
            PPL.decodeOffset psi
                (PPL.tokenCode t) <=
              -2
          · have hf : False := by
              simpa
                [hl, hdist, hsource,
                  hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa
                [hl, hdist, hsource,
                  hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact heq.symm
      · by_cases hm1 :
          PPL.decodeOffset psi
              (PPL.tokenCode t) =
            -1
        · have hf : False := by
            simpa
              [hl, hdist, hsource, hm1,
                l18Risk2SourceSet_tokenAt]
              using hq
          exact False.elim hf
        · by_cases hm2 :
            PPL.decodeOffset psi
                (PPL.tokenCode t) <=
              -2
          · have hf : False := by
              simpa
                [hl, hdist, hsource,
                  hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact False.elim hf
          · have heq : t = t' := by
              simpa
                [hl, hdist, hsource,
                  hm1, hm2,
                  l18Risk2SourceSet_tokenAt]
                using hq
            exact heq.symm

  | some u =>
      by_cases hm1 :
          PPL.decodeOffset psi
              (PPL.tokenCode t) =
            -1
      · have hf : False := by
          simpa
            [hl, hsource, hm1,
              l18Risk2SourceSet_tokenAt]
            using hq
        exact False.elim hf
      · by_cases hm2 :
          PPL.decodeOffset psi
              (PPL.tokenCode t) <=
            -2
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

private theorem q20238OpenLeftRightShape
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t t' : TokenData psi)
    (hgate :
      (PPL.sourceClear kind l).last = false
        /\ (PPL.sourceClear kind r).last = false)
    (hleft :
      PPL.tokenAt kind
          (PPL.sourceClear kind l) =
        some t)
    (hrnone :
      PPL.tokenAt kind
          (PPL.sourceClear kind r) =
        none)
    (hq :
      PPL.tokenAt kind
          (PPL.moveToken hpsi kind l r).2 =
        some t') :
    PPL.decodeOffset psi
        (PPL.tokenCode t') < 0
      \/ ((2 <=
          PPL.decodeOffset psi
            (PPL.tokenCode t))
        /\ (PPL.decodeOffset psi
              (PPL.tokenCode t') =
            PPL.decodeOffset psi
              (PPL.tokenCode t) - 1)) := by
  rw [
    ← l18Risk2MoveTokenMirror_eq
      hpsi kind l r
  ] at hq

  unfold l18Risk2MoveTokenMirror at hq

  simp only
    [dif_pos hgate, hgate, and_self,
      dite_true, ↓reduceDIte] at hq

  by_cases hc1 :
      PPL.decodeOffset psi
          (PPL.tokenCode t) =
        1
  · have heq :
        l18Risk2MkToken
            (PPL.offsetNegPsiPlusOneCode
              psi hpsi)
            t.1.2 t.2 =
          t' := by
      simpa
        [hleft, hrnone, hc1,
          l18Risk2SourceSet_tokenAt]
        using hq

    have hdec :=
      congrArg
        (fun u : TokenData psi =>
          PPL.decodeOffset psi
            (PPL.tokenCode u))
        heq.symm

    left

    have hturn :
        PPL.decodeOffset psi
            (PPL.tokenCode t') =
          1 - ((psi : Nat) : Int) := by
      simpa
        [l18Risk2MkToken,
          PPL.tokenCode,
          PPL.decodeOffset_negPsiPlusOne]
        using hdec

    omega

  · by_cases hc2 :
      2 <=
        PPL.decodeOffset psi
          (PPL.tokenCode t)
    · have heq :
          l18Risk2MkToken
              (PPL.encodeOffset psi
                (PPL.decodeOffset psi
                    (PPL.tokenCode t) - 1)
                (by
                  have hv :=
                    PPL.decodeOffset_valid
                      psi
                      (by omega)
                      (PPL.tokenCode t)
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
            PPL.decodeOffset psi
              (PPL.tokenCode u))
          heq.symm

      right
      constructor
      · exact hc2
      · simpa
          [l18Risk2MkToken,
            PPL.tokenCode,
            PPL.decode_encode]
          using hdec

    · have hf : False := by
        simpa
          [hleft, hrnone, hc1, hc2,
            l18Risk2SourceSet_tokenAt]
          using hq

      exact False.elim hf

private theorem q20238MoveTokenWhiteRightShape
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (hnoFresh :
      Not (l.dist.val = psi))
    (t' : TokenData psi)
    (hq :
      PPL.tokenAt .white
          (PPL.moveToken hpsi .white l r).2 =
        some t') :
    (exists t : TokenData psi,
        PPL.tokenAt .white r = some t
          /\ t' = t)
      \/ ((exists t : TokenData psi,
          PPL.tokenAt .white l = some t
            /\ 2 <=
              PPL.decodeOffset psi
                (PPL.tokenCode t)
            /\ PPL.decodeOffset psi
                (PPL.tokenCode t') =
              PPL.decodeOffset psi
                (PPL.tokenCode t) - 1)
        \/ PPL.decodeOffset psi
            (PPL.tokenCode t') < 0) := by
  by_cases hgate :
      (PPL.sourceClear .white l).last = false
        /\ (PPL.sourceClear .white r).last = false

  · cases hr :
      PPL.tokenAt .white
        (PPL.sourceClear .white r) with

    | some t =>
        have heq :=
          q20238OpenRightSame
            hpsi .white l r
            t t' hgate hr hq

        have hpre :=
          q20238SourceClearSome
            .white r t hr

        exact
          Or.inl
            ⟨t, hpre, heq⟩

    | none =>
        cases hl :
            PPL.tokenAt .white
              (PPL.sourceClear .white l) with

        | some t =>
            have hs :=
              q20238OpenLeftRightShape
                hpsi .white l r
                t t' hgate hl hr hq

            have hpre :=
              q20238SourceClearSome
                .white l t hl

            rcases hs with hneg | hmove
            · exact
                Or.inr
                  (Or.inr hneg)
            · exact
                Or.inr
                  (Or.inl
                    ⟨t, hpre,
                      hmove.1,
                      hmove.2⟩)

        | none =>
            have hd :=
              congrArg Fin.val
                (q20238SourceClearDist
                  TokenKind.white l)

            have hdist :
                Not
                  ((PPL.sourceClear
                      .white l).dist.val =
                    PPL.tokenD' psi .white) := by
              intro h
              apply hnoFresh
              calc
                l.dist.val =
                    (PPL.sourceClear
                      .white l).dist.val :=
                  hd.symm
                _ =
                    PPL.tokenD' psi .white :=
                  h
                _ = psi := by
                  rfl

            have hq0 := hq

            rw [
              ← l18Risk2MoveTokenMirror_eq
                hpsi TokenKind.white l r
            ] at hq0

            unfold
              l18Risk2MoveTokenMirror at hq0

            simp only
              [dif_pos hgate, hgate,
                and_self, dite_true,
                ↓reduceDIte] at hq0

            have hf : False := by
              simpa
                [hl, hr, hdist,
                  l18Risk2SourceSet_tokenAt]
                using hq0

            exact False.elim hf

  · cases hr :
      PPL.tokenAt .white
        (PPL.sourceClear .white r) with

    | none =>
        have hframe :
            PPL.tokenAt .white
                (PPL.moveToken
                  hpsi .white l r).2 =
              PPL.tokenAt .white
                (PPL.sourceClear
                  .white r) := by
          rw [
            ← l18Risk2MoveTokenMirror_eq
              hpsi TokenKind.white l r
          ]
          simp
            [l18Risk2MoveTokenMirror,
              hgate]

        have hnone :
            (none :
              Option (TokenData psi)) =
              some t' := by
          calc
            none =
                PPL.tokenAt .white
                  (PPL.sourceClear
                    .white r) :=
              hr.symm
            _ =
                PPL.tokenAt .white
                  (PPL.moveToken
                    hpsi .white l r).2 :=
              hframe.symm
            _ = some t' :=
              hq

        cases hnone

    | some t =>
        have heq :=
          q20238ClosedRightSame
            hpsi .white l r
            t t' hr hgate hq

        have hpre :=
          q20238SourceClearSome
            .white r t hr

        exact
          Or.inl
            ⟨t, hpre, heq⟩

private theorem q20238PPrimeWhiteRightShape
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (hnoFresh :
      Not (l.dist.val = psi))
    (t' : TokenData psi)
    (hpost :
      PPL.tokenAt .white
          (pprimeMoveToken
            hpsi .white l r).2 =
        some t') :
    (exists t : TokenData psi,
        PPL.tokenAt .white r = some t
          /\ t' = t)
      \/ ((exists t : TokenData psi,
          PPL.tokenAt .white l = some t
            /\ 2 <=
              PPL.decodeOffset psi
                (PPL.tokenCode t)
            /\ PPL.decodeOffset psi
                (PPL.tokenCode t') =
              PPL.decodeOffset psi
                (PPL.tokenCode t) - 1)
        \/ PPL.decodeOffset psi
            (PPL.tokenCode t') < 0) := by
  unfold pprimeMoveToken at hpost
  dsimp only at hpost

  let r0 : State psi kappa :=
    { r with mode := false }

  have hq :
      PPL.tokenAt .white
          (PPL.moveToken
            hpsi .white l r0).2 =
        some t' := by
    simpa [r0, PPL.tokenAt]
      using hpost

  have hs :=
    q20238MoveTokenWhiteRightShape
      hpsi l r0 hnoFresh t' hq

  rcases hs with hstay | hrest
  · rcases hstay with
      ⟨t, ht, heq⟩

    have ht' :
        PPL.tokenAt .white r =
          some t := by
      simpa [r0, PPL.tokenAt]
        using ht

    exact
      Or.inl ⟨t, ht', heq⟩

  · rcases hrest with hmoved | hneg
    · rcases hmoved with
        ⟨t, ht, hc2, hc'⟩
      exact
        Or.inr
          (Or.inl
            ⟨t, ht, hc2, hc'⟩)
    · exact
        Or.inr
          (Or.inr hneg)

private theorem q20238PPrimeWhiteRightClosed
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hlast : l.last = true)
    (hpost :
      PPL.tokenAt .white
          (pprimeMoveToken
            hpsi .white l r).2 =
        some t) :
    PPL.tokenAt .white r = some t := by
  unfold pprimeMoveToken at hpost
  dsimp only at hpost

  let r0 : State psi kappa :=
    { r with mode := false }

  have hq :
      PPL.tokenAt .white
          (PPL.moveToken
            hpsi .white l r0).2 =
        some t := by
    simpa [r0, PPL.tokenAt]
      using hpost

  have hleft :
      (PPL.sourceClear .white l).last =
        true := by
    exact
      (l18Risk2SourceClear_last
        TokenKind.white l).trans hlast

  have hgate :
      Not
        ((PPL.sourceClear .white l).last =
            false
          /\ (PPL.sourceClear .white r0).last =
            false) := by
    intro h
    have hf : true = false :=
      hleft.symm.trans h.1
    cases hf

  have hframe :
      PPL.tokenAt .white
          (PPL.moveToken
            hpsi .white l r0).2 =
        PPL.tokenAt .white
          (PPL.sourceClear .white r0) := by
    rw [
      ← l18Risk2MoveTokenMirror_eq
        hpsi TokenKind.white l r0
    ]
    simp
      [l18Risk2MoveTokenMirror,
        hgate]

  have hsc :
      PPL.tokenAt .white
          (PPL.sourceClear .white r0) =
        some t := by
    rw [← hframe]
    exact hq

  have horig :=
    q20238SourceClearSome
      TokenKind.white r0 t hsc

  simpa [r0, PPL.tokenAt]
    using horig

theorem l18GappedRiskyInsertedResponderWrapWhiteTokenFrame_proved :
    L18GappedRiskyInsertedResponderWrapWhiteTokenFrame := by
  unfold
    L18GappedRiskyInsertedResponderWrapWhiteTokenFrame

  intro n psi kappa
  intro hn3 hpsi _hlt
  intro ring root C e
  intro hC hroot
  intro t hpost

  let r := ring.rightNeighbor e

  have hrroot : r = root := by
    simpa [r] using hroot

  have heoff :=
    l18Gapped_predecessor_offset_of_right_root
      ring root e hroot

  have hthr :=
    l18Gapped_lastThreshold_lt
      (n := n) (psi := psi)
      hn3 hpsi

  unfold l18GappedLastThreshold at hthr

  have hgeom := hC.2.2 e
  dsimp only at hgeom

  have hElast :
      (C e).last = true := by
    apply hgeom.2.mpr
    rw [heoff]
    omega

  have hleader :
      (C r).leader = true := by
    exact
      (hC.2.1 r).mpr hrroot

  let p :=
    l18Risk2PreTokenPair
      hpsi (C e) (C r)

  let b :=
    pprimeMoveToken
      hpsi TokenKind.black
      p.1 p.2

  let w :=
    pprimeMoveToken
      hpsi TokenKind.white
      b.1 b.2

  have hcreate :
      pprimeCreateLeader
          hpsi (C e) (C r) =
        w := by
    dsimp only [w, b, p]
    unfold
      pprimeCreateLeader
      l18Risk2PreTokenPair
    rfl

  have hpostCreate :
      PPL.tokenAt .white
          (pprimeCreateLeader
            hpsi (C e) (C r)).2 =
        some t := by
    rw [
      ← q20238PPrimeStepRightWhite
        hn3 hpsi ring C e
    ]
    exact hpost

  have hpostW :
      PPL.tokenAt .white w.2 =
        some t := by
    rw [← hcreate]
    exact hpostCreate

  have hpfields :=
    l18Risk2PreTokenPairFields
      hpsi (C e) (C r)

  dsimp only at hpfields

  have hpLast :
      p.1.last = (C e).last := by
    calc
      p.1.last = true := by
        have h :=
          hpfields.2.2.2
        rw [hleader] at h
        simpa [p] using h
      _ = (C e).last :=
        hElast.symm

  have hbfields :=
    l18Risk2PPrimeMoveTokenDistLast
      hpsi TokenKind.black
      p.1 p.2

  dsimp only at hbfields

  have hbLast :
      b.1.last = p.1.last := by
    simpa [b]
      using hbfields.2.1

  have hbLastTrue :
      b.1.last = true :=
    hbLast.trans
      (hpLast.trans hElast)

  have hfromB :
      PPL.tokenAt .white b.2 =
        some t := by
    exact
      q20238PPrimeWhiteRightClosed
        hpsi b.1 b.2 t
        hbLastTrue hpostW

  have hbTok0 :=
    q20238PPrimeBlackPreservesWhite
      hpsi p.1 p.2

  have hbTok :
      PPL.tokenAt .white b.2 =
        PPL.tokenAt .white p.2 := by
    simpa [b] using hbTok0.2

  have hpTok0 :=
    q20238PreTokenWhiteFrame
      hpsi (C e) (C r)

  dsimp only at hpTok0

  have hpTok :
      PPL.tokenAt .white p.2 =
        PPL.tokenAt .white (C r) := by
    simpa [p] using hpTok0.2

  have hCr :
      PPL.tokenAt .white (C r) =
        some t := by
    calc
      PPL.tokenAt .white (C r) =
          PPL.tokenAt .white p.2 :=
        hpTok.symm
      _ =
          PPL.tokenAt .white b.2 :=
        hbTok.symm
      _ = some t :=
        hfromB

  simpa [r] using hCr

theorem l18GappedRiskyInsertedResponderNonwrapWhiteOutputRow_proved :
    L18GappedRiskyInsertedResponderNonwrapWhiteOutputRow := by
  unfold
    L18GappedRiskyInsertedResponderNonwrapWhiteOutputRow

  intro n psi kappa
  intro hn3 hpsi _hlt
  intro ring root C e
  intro hC hroot hroff
  intro t' hpost

  let r := ring.rightNeighbor e

  have hroot' :
      Not (r = root) := by
    simpa [r] using hroot

  have hoff :=
    l18Gapped_rightNeighbor_offset_of_ne_root
      ring root e hroot

  have heoff :
      cyclicOffset ring root e < psi := by
    have h := hroff
    rw [hoff] at h
    omega

  have hgeom := hC.2.2 e
  dsimp only at hgeom

  have he2 :
      cyclicOffset ring root e <
        2 * psi := by
    omega

  have hdistC :
      (C e).dist.val =
        cyclicOffset ring root e := by
    have h := hgeom.1
    rw [Nat.mod_eq_of_lt he2] at h
    exact h

  let p :=
    l18Risk2PreTokenPair
      hpsi (C e) (C r)

  let b :=
    pprimeMoveToken
      hpsi TokenKind.black
      p.1 p.2

  let w :=
    pprimeMoveToken
      hpsi TokenKind.white
      b.1 b.2

  have hcreate :
      pprimeCreateLeader
          hpsi (C e) (C r) =
        w := by
    dsimp only [w, b, p]
    unfold
      pprimeCreateLeader
      l18Risk2PreTokenPair
    rfl

  have hpostCreate :
      PPL.tokenAt .white
          (pprimeCreateLeader
            hpsi (C e) (C r)).2 =
        some t' := by
    rw [
      ← q20238PPrimeStepRightWhite
        hn3 hpsi ring C e
    ]
    exact hpost

  have hpostW :
      PPL.tokenAt .white w.2 =
        some t' := by
    rw [← hcreate]
    exact hpostCreate

  have hpfields :=
    l18Risk2PreTokenPairFields
      hpsi (C e) (C r)

  dsimp only at hpfields

  have hpDist :
      p.1.dist = (C e).dist := by
    simpa [p] using hpfields.1

  have hbfields :=
    l18Risk2PPrimeMoveTokenDistLast
      hpsi TokenKind.black
      p.1 p.2

  dsimp only at hbfields

  have hbDist :
      b.1.dist = p.1.dist := by
    simpa [b] using hbfields.1

  have hbVal :
      b.1.dist.val =
        (C e).dist.val := by
    exact
      congrArg Fin.val
        (hbDist.trans hpDist)

  have hnoFresh :
      Not (b.1.dist.val = psi) := by
    intro h
    have heq :
        cyclicOffset ring root e = psi := by
      calc
        cyclicOffset ring root e =
            (C e).dist.val :=
          hdistC.symm
        _ = b.1.dist.val :=
          hbVal.symm
        _ = psi := h
    omega

  have hs :=
    q20238PPrimeWhiteRightShape
      hpsi b.1 b.2
      hnoFresh t' hpostW

  have hpTok0 :=
    q20238PreTokenWhiteFrame
      hpsi (C e) (C r)

  dsimp only at hpTok0

  have hpLeft :
      PPL.tokenAt .white p.1 =
        PPL.tokenAt .white (C e) := by
    simpa [p] using hpTok0.1

  have hpRight :
      PPL.tokenAt .white p.2 =
        PPL.tokenAt .white (C r) := by
    simpa [p] using hpTok0.2

  have hbTok0 :=
    q20238PPrimeBlackPreservesWhite
      hpsi p.1 p.2

  have hbLeft :
      PPL.tokenAt .white b.1 =
        PPL.tokenAt .white p.1 := by
    simpa [b] using hbTok0.1

  have hbRight :
      PPL.tokenAt .white b.2 =
        PPL.tokenAt .white p.2 := by
    simpa [b] using hbTok0.2

  rcases hs with hstay | hrest

  · rcases hstay with
      ⟨t, ht, heq⟩

    have hpre :
        PPL.tokenAt .white (C r) =
          some t := by
      calc
        PPL.tokenAt .white (C r) =
            PPL.tokenAt .white p.2 :=
          hpRight.symm
        _ =
            PPL.tokenAt .white b.2 :=
          hbRight.symm
        _ = some t := ht

    exact
      Or.inl
        ⟨t,
          by
            simpa [r] using hpre,
          heq⟩

  · rcases hrest with hmoved | hneg

    · rcases hmoved with
        ⟨t, ht, hc2, hc'⟩

      have hpre :
          PPL.tokenAt .white (C e) =
            some t := by
        calc
          PPL.tokenAt .white (C e) =
              PPL.tokenAt .white p.1 :=
            hpLeft.symm
          _ =
              PPL.tokenAt .white b.1 :=
            hbLeft.symm
          _ = some t := ht

      exact
        Or.inr
          (Or.inl
            ⟨t, hpre, hc2, hc'⟩)

    · exact
        Or.inr
          (Or.inr hneg)

theorem l18GappedRiskyInsertedResponderWrapWhiteCase_proved :
    L18GappedRiskyInsertedResponderWrapWhiteCase :=
  l18GappedRiskyInsertedResponderWrapWhiteCase_of_tokenFrame
    l18GappedRiskyInsertedResponderWrapWhiteTokenFrame_proved

theorem l18GappedRiskyInsertedResponderNonwrapWhiteCase_proved :
    L18GappedRiskyInsertedResponderNonwrapWhiteCase :=
  l18GappedRiskyInsertedResponderNonwrapWhiteCase_of_outputRow
    l18GappedRiskyInsertedResponderNonwrapWhiteOutputRow_proved

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapWhiteTokenFrame_proved
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapWhiteOutputRow_proved
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapWhiteCase_proved
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapWhiteCase_proved
