import Leader.PPL.ReachCPB.MismatchHistFreshGeomLiteralCounterexample
import Leader.PPL.TokenCompletion.GhostStepMirror
import Leader.PPL.TokenCorrectness.Persistence

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
The public ghost-step export exposes only the final selected-pair result.
Its birth/bump implementation is private, so this file uses a definitionally
identical proof-local mirror under the coh prefix, then bridges back to
PPL.ghostStepSelectedPair by rfl.
-/

private def cohBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def cohMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : PPL.TokenData psi :=
  ((offset, bit), carry)

private def cohLocalValid
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : PPL.TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And
      (0 < c)
      (And
        (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And
      (c < 0)
      (And
        (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))

private instance instDecidableCohLocalValid
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : PPL.TokenData psi) :
    Decidable (cohLocalValid kind q t) := by
  unfold cohLocalValid
  infer_instance

private def cohTokenPrelude
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    PPL.State psi kappa × PPL.State psi kappa :=
  let s := PPL.createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 :=
    if r0.mode = false then
      { r0 with dist := tmp }
    else
      r0
  let l1 :=
    if r1.leader = true then
      { l0 with last := true }
    else if Or (r1.dist.val = 0)
        (r1.dist.val = psi) then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def cohLiveShadow
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (g : Option (PPL.GhostToken n psi)) :
    Option (PPL.GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match PPL.tokenAt kind q with
      | none => none
      | some t =>
          if And (z.value = t)
              (cohLocalValid kind q t) then
            some z
          else
            none

private def cohLiveValue
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa) :
    Option (PPL.TokenData psi) :=
  match PPL.tokenAt kind q with
  | none => none
  | some t =>
      if cohLocalValid kind q t then
        some t
      else
        none

private def cohBirthGhost
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    PPL.GhostToken n psi :=
  { value :=
      cohMkToken
        (PPL.offsetPsiCode psi hpsi)
        (cohBitToFin (!idBit))
        (cohBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def cohBumpTo
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (qDest : PPL.State psi kappa)
    (newValue : PPL.TokenData psi)
    (g : Option (PPL.GhostToken n psi)) :
    PPL.Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' : PPL.LineageMeta n :=
        PPL.ghostStepLineageAdvance z.lmeta
      let z' : PPL.GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = PPL.tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if cohLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def cohNegTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : PPL.TokenData psi) :
    PPL.TokenData psi :=
  if t.2 = (1 : Fin 2) then
    cohMkToken
      (PPL.offsetPsiCode psi hpsi)
      (cohBitToFin (!sourceBit))
      (cohBitToFin sourceBit)
  else
    cohMkToken
      (PPL.offsetPsiCode psi hpsi)
      (cohBitToFin sourceBit)
      (0 : Fin 2)

private def cohFinishMove
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa)
    (lv2 rv0 : Option (PPL.TokenData psi))
    (gl2 gr0 : Option (PPL.GhostToken n psi)) :
    PPL.GhostMoveResult n psi :=
  match lv2 with
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let next :=
          cohMkToken
            (PPL.offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          cohBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : PPL.ValidOffset psi c :=
          PPL.decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          cohMkToken
            (PPL.encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          cohBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                cohNegTurnNext hpsi l.id t
              let b :=
                cohBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : PPL.ValidOffset psi c :=
                PPL.decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                cohMkToken
                  (PPL.encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                cohBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  | none =>
      match rv0 with
      | none =>
          ⟨gl2, gr0, []⟩
      | some t =>
          let c := decodeOffset psi (tokenCode t)
          if hm1 : c = -1 then
            let next :=
              cohNegTurnNext hpsi l.id t
            let b :=
              cohBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c <= -2 then
            have hc : PPL.ValidOffset psi c :=
              PPL.decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              cohMkToken
                (PPL.encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              cohBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def cohGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : PPL.State psi kappa)
    (gl gr : Option (PPL.GhostToken n psi)) :
    PPL.GhostMoveResult n psi :=
  let lv0 := cohLiveValue kind l
  let rv0 := cohLiveValue kind r
  let gl0 := cohLiveShadow kind l gl
  let gr0 := cohLiveShadow kind r gr
  if And (l.last = false) (r.last = false) then
    let born :=
      if And (l.dist.val = PPL.tokenD' psi kind)
          (lv0 = none) then
        some
          (cohBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if And (l.dist.val = PPL.tokenD' psi kind)
          (lv0 = none) then
        some
          (cohBirthGhost
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide :=
      And (lv1 ≠ none) (rv0 ≠ none)
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    cohFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def cohSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (kind : PPL.TokenKind) :
    PPL.GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let pre :=
    cohTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      cohGhostMoveToken
        hpsi .black step e
        pre.1 pre.2
        (PPL.ghostTokenAt .black G e)
        (PPL.ghostTokenAt .black G rsite)
  | .white =>
      let qb :=
        PPL.moveToken hpsi .black pre.1 pre.2
      cohGhostMoveToken
        hpsi .white step e
        qb.1 qb.2
        (PPL.ghostTokenAt .white G e)
        (PPL.ghostTokenAt .white G rsite)

private theorem cohSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (kind : PPL.TokenKind) :
    cohSelectedPair hpsi ring step G e kind =
      PPL.ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

/-! -------------------------------------------------------------------------
    Metadata coherence for one option and one selected-colour local move
------------------------------------------------------------------------- -/

private def CohOpt
    {n psi : Nat}
    (slotKind : PPL.TokenKind)
    (g : Option (PPL.GhostToken n psi)) : Prop :=
  forall
    (bornKind : PPL.TokenKind)
    (z : PPL.GhostToken n psi)
    (t : Nat),
    g = some z ->
    z.lmeta.id = .born bornKind t ->
    And
      (slotKind = bornKind)
      (z.lmeta.birthStep = t)

private theorem cohOpt_none
    {n psi : Nat}
    (kind : PPL.TokenKind) :
    CohOpt (n := n) (psi := psi) kind none := by
  intro bornKind z t howner hid
  simp at howner

private theorem cohLiveShadow_coherent
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (g : Option (PPL.GhostToken n psi))
    (hg : CohOpt kind g) :
    CohOpt kind (cohLiveShadow kind q g) := by
  intro bornKind z t howner hid
  cases hopt : g with
  | none =>
      simp [cohLiveShadow, hopt] at howner
  | some z0 =>
      cases ht : PPL.tokenAt kind q with
      | none =>
          simp [cohLiveShadow, hopt, ht] at howner
      | some u =>
          by_cases hv :
              And (z0.value = u)
                (cohLocalValid kind q u)
          · have hzz : z0 = z := by
              simpa [cohLiveShadow, hopt, ht, hv]
                using howner
            subst z
            exact hg bornKind z0 t hopt hid
          · simp [cohLiveShadow, hopt, ht, hv] at howner

private theorem cohBirthGhost_coherent
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    CohOpt kind
      (some
        (cohBirthGhost
          hpsi kind step site idBit)) := by
  intro bornKind z t howner hid
  have hzz :
      cohBirthGhost hpsi kind step site idBit = z := by
    simpa using howner
  subst z
  change
    PPL.LineageId.born kind step =
      PPL.LineageId.born bornKind t at hid
  cases hid
  exact And.intro rfl rfl

private theorem cohBumpTo_coherent
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (qDest : PPL.State psi kappa)
    (newValue : PPL.TokenData psi)
    (g : Option (PPL.GhostToken n psi))
    (hg : CohOpt kind g) :
    CohOpt kind
      (cohBumpTo kind qDest newValue g).live := by
  intro bornKind z t howner hid
  cases hopt : g with
  | none =>
      simp [cohBumpTo, hopt] at howner
  | some z0 =>
      by_cases hv :
          cohLocalValid kind qDest newValue
      · let z1 : PPL.GhostToken n psi :=
          { value := newValue
            lmeta :=
              PPL.ghostStepLineageAdvance z0.lmeta }
        have hzz : z1 = z := by
          simpa [cohBumpTo, hopt, hv, z1]
            using howner
        subst z
        have hid0 :
            z0.lmeta.id = .born bornKind t := by
          simpa [z1, PPL.ghostStepLineageAdvance]
            using hid
        have hc :=
          hg bornKind z0 t hopt hid0
        exact
          And.intro hc.1
            (by
              simpa
                [z1, PPL.ghostStepLineageAdvance]
                using hc.2)
      · simp [cohBumpTo, hopt, hv] at howner

private theorem cohFinishMove_coherent
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (l r : PPL.State psi kappa)
    (lv2 rv0 : Option (PPL.TokenData psi))
    (gl2 gr0 : Option (PPL.GhostToken n psi))
    (hgl : CohOpt kind gl2)
    (hgr : CohOpt kind gr0) :
    let out :=
      cohFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0
    And
      (CohOpt kind out.left)
      (CohOpt kind out.right) := by
  cases lv2 with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [cohFinishMove, dif_pos h1]
        constructor
        · exact cohOpt_none kind
        · apply cohBumpTo_coherent
          exact hgl
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [cohFinishMove,
              dif_neg h1, dif_pos h2]
          constructor
          · exact cohOpt_none kind
          · apply cohBumpTo_coherent
            exact hgl
        · cases rv0 with
          | none =>
              simp only
                [cohFinishMove,
                  dif_neg h1, dif_neg h2]
              exact And.intro hgl hgr
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [cohFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1]
                constructor
                · apply cohBumpTo_coherent
                  exact hgr
                · exact cohOpt_none kind
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) <= -2
                · simp only
                    [cohFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2]
                  constructor
                  · apply cohBumpTo_coherent
                    exact hgr
                  · exact cohOpt_none kind
                · simp only
                    [cohFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]
                  exact And.intro hgl hgr
  | none =>
      cases rv0 with
      | none =>
          simp only [cohFinishMove]
          exact And.intro hgl hgr
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [cohFinishMove, dif_pos hm1]
            constructor
            · apply cohBumpTo_coherent
              exact hgr
            · exact cohOpt_none kind
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [cohFinishMove,
                  dif_neg hm1, dif_pos hm2]
              constructor
              · apply cohBumpTo_coherent
                exact hgr
              · exact cohOpt_none kind
            · simp only
                [cohFinishMove,
                  dif_neg hm1, dif_neg hm2]
              exact And.intro hgl hgr

private theorem cohGhostMoveToken_coherent
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : PPL.TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : PPL.State psi kappa)
    (gl gr : Option (PPL.GhostToken n psi))
    (hgl : CohOpt kind gl)
    (hgr : CohOpt kind gr) :
    let out :=
      cohGhostMoveToken
        hpsi kind step site l r gl gr
    And
      (CohOpt kind out.left)
      (CohOpt kind out.right) := by
  let lv0 := cohLiveValue kind l
  let rv0 := cohLiveValue kind r
  let gl0 := cohLiveShadow kind l gl
  let gr0 := cohLiveShadow kind r gr

  have hgl0 :
      CohOpt kind gl0 := by
    exact
      cohLiveShadow_coherent
        kind l gl hgl

  have hgr0 :
      CohOpt kind gr0 := by
    exact
      cohLiveShadow_coherent
        kind r gr hgr

  by_cases hlast :
      And (l.last = false) (r.last = false)
  · let hb :=
      And
        (l.dist.val = PPL.tokenD' psi kind)
        (lv0 = none)
    let birth :=
      cohBirthGhost
        hpsi kind step site l.id
    let lv1 : Option (PPL.TokenData psi) :=
      if hb then some birth.value else lv0
    let gl1 : Option (PPL.GhostToken n psi) :=
      if hb then some birth else gl0

    have hgl1 :
        CohOpt kind gl1 := by
      by_cases hbirth : hb
      · have hborn :
            CohOpt kind (some birth) := by
          simpa [birth] using
            cohBirthGhost_coherent
              hpsi kind step site l.id
        simpa [gl1, hbirth] using hborn
      · simpa [gl1, hbirth] using hgl0

    let collide :=
      And (lv1 ≠ none) (rv0 ≠ none)
    let lv2 : Option (PPL.TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (PPL.GhostToken n psi) :=
      if collide then none else gl1

    have hgl2 :
        CohOpt kind gl2 := by
      by_cases hcol : collide
      · simp [gl2, hcol]
        exact cohOpt_none kind
      · simpa [gl2, hcol] using hgl1

    have hfinish :=
      cohFinishMove_coherent
        hpsi kind l r
        lv2 rv0 gl2 gr0 hgl2 hgr0

    simp only
      [cohGhostMoveToken,
        if_pos hlast]
    exact hfinish
  · simp only
      [cohGhostMoveToken,
        if_neg hlast]
    exact And.intro hgl0 hgr0

private theorem cohSelectedPair_coherent
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (kind : PPL.TokenKind)
    (hcoh : Lemma16GhostLineageCoherent G) :
    let out :=
      cohSelectedPair hpsi ring step G e kind
    And
      (CohOpt kind out.left)
      (CohOpt kind out.right) := by
  have hleft :
      CohOpt kind
        (PPL.ghostTokenAt kind G e) := by
    intro bornKind z t howner hid
    exact
      hcoh kind bornKind e z t
        howner hid

  have hright :
      CohOpt kind
        (PPL.ghostTokenAt kind G
          (ring.rightNeighbor e)) := by
    intro bornKind z t howner hid
    exact
      hcoh kind bornKind
        (ring.rightNeighbor e) z t
        howner hid

  cases kind with
  | black =>
      dsimp [cohSelectedPair]
      exact
        cohGhostMoveToken_coherent
          hpsi .black step e
          (cohTokenPrelude hpsi
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).1
          (cohTokenPrelude hpsi
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).2
          (PPL.ghostTokenAt .black G e)
          (PPL.ghostTokenAt .black G
            (ring.rightNeighbor e))
          hleft hright
  | white =>
      dsimp [cohSelectedPair]
      let pre :=
        cohTokenPrelude hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))
      let qb :=
        PPL.moveToken hpsi .black pre.1 pre.2
      exact
        cohGhostMoveToken_coherent
          hpsi .white step e
          qb.1 qb.2
          (PPL.ghostTokenAt .white G e)
          (PPL.ghostTokenAt .white G
            (ring.rightNeighbor e))
          hleft hright

private theorem ghostStepSelectedPair_coherent
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (kind : PPL.TokenKind)
    (hcoh : Lemma16GhostLineageCoherent G) :
    let out :=
      PPL.ghostStepSelectedPair
        hpsi ring step G e kind
    And
      (CohOpt kind out.left)
      (CohOpt kind out.right) := by
  have h :=
    cohSelectedPair_coherent
      hpsi ring step G e kind hcoh
  rw [cohSelectedPair_eq_export
    hpsi ring step G e kind] at h
  exact h

/-! -------------------------------------------------------------------------
    Coherence preservation by ghostStep and ghostRun
------------------------------------------------------------------------- -/

private theorem lemma16GhostLineageCoherent_initial
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    Lemma16GhostLineageCoherent
      (PPL.initialGhost C) := by
  unfold Lemma16GhostLineageCoherent
  intro slotKind bornKind i z t howner hid
  have hlt :=
    (PPL.ghostIdsUnique_initial C).2
      slotKind i z bornKind t howner hid
  omega

private theorem lemma16GhostLineageCoherent_step
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n)
    (hcoh : Lemma16GhostLineageCoherent G) :
    Lemma16GhostLineageCoherent
      (PPL.ghostStep hpsi ring step G e) := by
  unfold Lemma16GhostLineageCoherent
  intro slotKind bornKind i z t howner hid

  have hpair :=
    ghostStepSelectedPair_coherent
      hpsi ring step G e slotKind hcoh

  by_cases hie : i = e
  · subst i
    rw [PPL.ghostTokenAt_ghostStep_initiator
      hpsi ring step G e slotKind] at howner
    exact
      hpair.1 bornKind z t howner hid

  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hne :
          ring.rightNeighbor e ≠ e := by
        exact hie
      rw [PPL.ghostTokenAt_ghostStep_responder_of_ne
        hpsi ring step G e slotKind hne] at howner
      exact
        hpair.2 bornKind z t howner hid

    · have howner0 :
          PPL.ghostTokenAt slotKind G i = some z := by
        exact
          (PPL.ghostTokenAt_ghostStep_frame
            hpsi ring step G e i slotKind
            hie hir).symm.trans howner
      exact
        hcoh slotKind bornKind i z t
          howner0 hid

private theorem lemma16GhostLineageCoherent_run_from
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) :
    forall
      (t : Nat)
      (G : PPL.GhostConfig n psi kappa)
      (pre : DetSchedule n),
      Lemma16GhostLineageCoherent G ->
      Lemma16GhostLineageCoherent
        (PPL.ghostRun hpsi ring t G pre) := by
  intro t G pre hcoh
  induction pre generalizing t G with
  | nil =>
      exact hcoh
  | cons e es ih =>
      simp only [PPL.ghostRun]
      exact
        ih
          (t := t + 1)
          (G := PPL.ghostStep hpsi ring t G e)
          (lemma16GhostLineageCoherent_step
            hpsi ring t G e hcoh)

/--
Canonical ghost runs preserve the two immutable born-lineage fields used by
the repaired Lemma-16 history interface: slot colour agrees with the born-ID
colour, and the born-ID timestamp equals birthStep.
-/
theorem lemma16GhostLineageCoherentRunProducer_proved :
    Lemma16GhostLineageCoherentRunProducer := by
  unfold Lemma16GhostLineageCoherentRunProducer
  intro n psi kappa hpsi ring C0 pre
  exact
    lemma16GhostLineageCoherent_run_from
      hpsi ring
      0 (PPL.initialGhost C0) pre
      (lemma16GhostLineageCoherent_initial C0)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16GhostLineageCoherentRunProducer_proved

