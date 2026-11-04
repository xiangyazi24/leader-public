import Leader.PPL.ReachCPB.MismatchHistFreshTerminalCompareUnique
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

private def doneProvBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def doneProvMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def doneProvLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
        target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
        target ≤ (((psi - 1 : Nat)) : Int))

private instance instDecidableDoneProvLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (doneProvLocalValid kind q t) := by
  unfold doneProvLocalValid
  infer_instance

private def doneProvTokenPrelude
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let s := createLeaderThroughLine6 hpsi l r
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
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def doneProvLiveShadow
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if z.value = t ∧ doneProvLocalValid kind q t then
            some z
          else
            none

private def doneProvLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if doneProvLocalValid kind q t then
        some t
      else
        none

private def doneProvBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      doneProvMkToken
        (offsetPsiCode psi hpsi)
        (doneProvBitToFin (!idBit))
        (doneProvBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def doneProvBumpTo
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none =>
      ⟨none, []⟩
  | some z =>
      let m' : LineageMeta n :=
        ghostStepLineageAdvance z.lmeta
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if doneProvLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def doneProvNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    doneProvMkToken
      (offsetPsiCode psi hpsi)
      (doneProvBitToFin (!sourceBit))
      (doneProvBitToFin sourceBit)
  else
    doneProvMkToken
      (offsetPsiCode psi hpsi)
      (doneProvBitToFin sourceBit)
      (0 : Fin 2)

private def doneProvFinishMove
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  match lv2 with
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let next :=
          doneProvMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := doneProvBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          doneProvMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := doneProvBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                doneProvNegTurnNext hpsi l.id tr
              let b := doneProvBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid psi (by omega) (tokenCode tr)
              let next :=
                doneProvMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := doneProvBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  | none =>
      match rv0 with
      | none =>
          ⟨gl2, gr0, []⟩
      | some tr =>
          let cr := decodeOffset psi (tokenCode tr)
          if hm1 : cr = -1 then
            let next :=
              doneProvNegTurnNext hpsi l.id tr
            let b := doneProvBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid psi (by omega) (tokenCode tr)
            let next :=
              doneProvMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := doneProvBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def doneProvGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := doneProvLiveValue kind l
  let rv0 := doneProvLiveValue kind r
  let gl0 := doneProvLiveShadow kind l gl
  let gr0 := doneProvLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (doneProvBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (doneProvBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    doneProvFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def doneProvSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := doneProvTokenPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2

private def doneProvSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    doneProvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  doneProvGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem doneProvSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    doneProvSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

private theorem doneProvTrajectoryMoves_gt_one
    (psi : Nat)
    (hpsi : 2 ≤ psi) :
    1 < tokenTrajectoryMoves psi := by
  have hmul :
      2 * psi < (2 * psi) * psi := by
    calc
      2 * psi = (2 * psi) * 1 := by omega
      _ < (2 * psi) * psi :=
        (Nat.mul_lt_mul_left
          (by omega : 0 < 2 * psi)).2
          (by omega)
  have hpos :
      0 < (2 * psi) * psi - 2 * psi :=
    Nat.sub_pos_of_lt hmul
  unfold tokenTrajectoryMoves
  omega

private theorem doneProvLiveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      doneProvLiveShadow kind q g = some z) :
    g = some z := by
  cases hg : g with
  | none =>
      simp [doneProvLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [doneProvLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                doneProvLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [doneProvLiveShadow, hg, ht, hv]
                using hz
            subst z
            rfl
          · simp
              [doneProvLiveShadow, hg, ht, hv]
              at hz

private theorem doneProvLiveShadow_value
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      doneProvLiveShadow kind q g = some z) :
    doneProvLiveValue kind q = some z.value := by
  cases hg : g with
  | none =>
      simp [doneProvLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [doneProvLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                doneProvLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [doneProvLiveShadow, hg, ht, hv]
                using hz
            subst z
            rcases hv with ⟨hvalue, hvalid⟩
            simp
              [doneProvLiveValue, ht, hvalid, hvalue]
          · simp
              [doneProvLiveShadow, hg, ht, hv]
              at hz

private theorem bump_done_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈
        (doneProvBumpTo
          kind qDest newValue g).done) :
    ∃ z : GhostToken n psi,
      g = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi := by
  cases hg : g with
  | none =>
      simp [doneProvBumpTo, hg] at hm
  | some z =>
      by_cases hdone :
          (ghostStepLineageAdvance z.lmeta).moves =
            tokenTrajectoryMoves psi
      · have hmm :
            m = ghostStepLineageAdvance z.lmeta := by
          simpa [doneProvBumpTo, hg, hdone]
            using hm
        exact ⟨z, rfl, hmm, hdone⟩
      · simp [doneProvBumpTo, hg, hdone] at hm

private theorem doneProvFinish_done_source_class
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈
        (doneProvFinishMove
          hpsi kind l r lv2 rv0 gl2 gr0).done) :
    (∃ z : GhostToken n psi,
      gl2 = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi) ∨
    (∃ (tr : TokenData psi) (z : GhostToken n psi),
      rv0 = some tr ∧
      gr0 = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi ∧
      decodeOffset psi (tokenCode tr) < 0) := by
  cases hlv : lv2 with
  | none =>
      cases hrv : rv0 with
      | none =>
          simp [doneProvFinishMove, hlv, hrv] at hm
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [doneProvFinishMove, hlv, hrv,
                dif_pos hm1] at hm
            let next :=
              doneProvNegTurnNext hpsi l.id tr
            rcases
                bump_done_source
                  kind l next gr0 m hm with
              ⟨z, hgr, hmadv, hterm⟩
            exact
              .inr
                ⟨tr, z, rfl, hgr, hmadv,
                  hterm, by omega⟩
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · simp only
                [doneProvFinishMove, hlv, hrv,
                  dif_neg hm1, dif_pos hm2] at hm
              have hc :
                  ValidOffset psi
                    (decodeOffset psi
                      (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                doneProvMkToken
                  (encodeOffset psi
                    (decodeOffset psi
                      (tokenCode tr) + 1)
                    (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                  tr.1.2 tr.2
              rcases
                  bump_done_source
                    kind l next gr0 m hm with
                ⟨z, hgr, hmadv, hterm⟩
              exact
                .inr
                  ⟨tr, z, rfl, hgr, hmadv,
                    hterm, by omega⟩
            · simp
                [doneProvFinishMove, hlv, hrv,
                  hm1, hm2] at hm
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [doneProvFinishMove, hlv, dif_pos h1] at hm
        let next :=
          doneProvMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        exact
          .inl
            (bump_done_source
              kind r next gl2 m hm)
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · simp only
            [doneProvFinishMove, hlv,
              dif_neg h1, dif_pos h2] at hm
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            doneProvMkToken
              (encodeOffset psi
                (decodeOffset psi (tokenCode t) - 1)
                (by
                  rcases hc with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
              t.1.2 t.2
          exact
            .inl
              (bump_done_source
                kind r next gl2 m hm)
        · cases hrv : rv0 with
          | none =>
              simp
                [doneProvFinishMove, hlv, hrv,
                  h1, h2] at hm
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [doneProvFinishMove, hlv, hrv,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1] at hm
                let next :=
                  doneProvNegTurnNext hpsi l.id tr
                rcases
                    bump_done_source
                      kind l next gr0 m hm with
                  ⟨z, hgr, hmadv, hterm⟩
                exact
                  .inr
                    ⟨tr, z, rfl, hgr, hmadv,
                      hterm, by omega⟩
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · simp only
                    [doneProvFinishMove, hlv, hrv,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2] at hm
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    doneProvMkToken
                      (encodeOffset psi
                        (decodeOffset psi
                          (tokenCode tr) + 1)
                        (by
                          rcases hc with hn | hp
                          · left
                            omega
                          · exfalso
                            omega))
                      tr.1.2 tr.2
                  rcases
                      bump_done_source
                        kind l next gr0 m hm with
                    ⟨z, hgr, hmadv, hterm⟩
                  exact
                    .inr
                      ⟨tr, z, rfl, hgr, hmadv,
                        hterm, by omega⟩
                · simp
                    [doneProvFinishMove, hlv, hrv,
                      h1, h2, hm1, hm2] at hm

private theorem doneProvGhostMove_done_source_class
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈
        (doneProvGhostMoveToken
          hpsi kind step site l r gl gr).done) :
    (∃ z : GhostToken n psi,
      gl = some z ∧
      m = ghostStepLineageAdvance z.lmeta) ∨
    (∃ z : GhostToken n psi,
      gr = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      decodeOffset psi (tokenCode z.value) < 0) := by
  let lv0 := doneProvLiveValue kind l
  let rv0 := doneProvLiveValue kind r
  let gl0 := doneProvLiveShadow kind l gl
  let gr0 := doneProvLiveShadow kind r gr

  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      doneProvBirthGhost
        hpsi kind step site l.id
    let lv1 : Option (TokenData psi) :=
      if hb then some birth.value else lv0
    let gl1 : Option (GhostToken n psi) :=
      if hb then some birth else gl0
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 : Option (TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (GhostToken n psi) :=
      if collide then none else gl1

    have hmFinish :
        m ∈
          (doneProvFinishMove
            hpsi kind l r
            lv2 rv0 gl2 gr0).done := by
      simpa only
        [doneProvGhostMoveToken,
          if_pos hlast]
        using hm

    rcases
        doneProvFinish_done_source_class
          hpsi kind l r
          lv2 rv0 gl2 gr0
          m hmFinish with hleft | hright
    · rcases hleft with
        ⟨z, hgl2, hmadv, hterm⟩
      by_cases hcol : collide
      · simp [gl2, hcol] at hgl2
      · have hgl1 :
            gl1 = some z := by
          simpa [gl2, hcol] using hgl2
        by_cases hbirth : hb
        · have hz : birth = z := by
            simpa [gl1, hbirth] using hgl1
          subst z
          have hterm1 :
              1 = tokenTrajectoryMoves psi := by
            simpa
              [birth, doneProvBirthGhost,
                ghostStepLineageAdvance]
              using hterm
          have hgt :=
            doneProvTrajectoryMoves_gt_one
              psi hpsi
          omega
        · have hgl0 :
              gl0 = some z := by
            simpa [gl1, hbirth] using hgl1
          have hsource :
              gl = some z :=
            doneProvLiveShadow_source
              kind l gl z hgl0
          exact .inl ⟨z, hsource, hmadv⟩

    · rcases hright with
        ⟨tr, z, hrv, hgr0, hmadv,
          _hterm, hneg⟩
      have hsource :
          gr = some z :=
        doneProvLiveShadow_source
          kind r gr z hgr0
      have hvalue :
          rv0 = some z.value :=
        doneProvLiveShadow_value
          kind r gr z hgr0
      have htz : tr = z.value :=
        Option.some.inj (hrv.symm.trans hvalue)
      rw [htz] at hneg
      exact .inr ⟨z, hsource, hmadv, hneg⟩

  · simp
      [doneProvGhostMoveToken,
        if_neg hlast] at hm

private theorem doneProvSelectedPair_done_source_class
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (m : LineageMeta n)
    (hm :
      m ∈
        (doneProvSelectedPair
          hpsi ring step G e kind).done) :
    (∃ z : GhostToken n psi,
      ghostTokenAt kind G e = some z ∧
      m = ghostStepLineageAdvance z.lmeta) ∨
    (∃ z : GhostToken n psi,
      ghostTokenAt kind G
          (ring.rightNeighbor e) = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      decodeOffset psi (tokenCode z.value) < 0) := by
  unfold doneProvSelectedPair at hm
  rcases
      doneProvGhostMove_done_source_class
        hpsi kind step e
        (doneProvSelectedInput
          hpsi kind
          (G.phys e)
          (G.phys
            (ring.rightNeighbor e))).1
        (doneProvSelectedInput
          hpsi kind
          (G.phys e)
          (G.phys
            (ring.rightNeighbor e))).2
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G
          (ring.rightNeighbor e))
        m hm with hleft | hright
  · rcases hleft with ⟨z, howner, hmadv⟩
    exact .inl ⟨z, howner, hmadv⟩
  · rcases hright with
      ⟨z, howner, hmadv, hneg⟩
    exact .inr ⟨z, howner, hmadv, hneg⟩

private theorem terminalMoves_split
    (psi : Nat)
    (hpsi : 2 ≤ psi) :
    tokenTrajectoryMoves psi =
      (psi - 1) * (2 * psi - 1) + psi := by
  have hpoint :
      Lemma4FreshTrajectoryPoint
        psi
        ((psi - 1) * (2 * psi - 1) +
          (psi - 1))
        (2 * psi - 2)
        (1 : Int) := by
    left
    refine ⟨psi - 1, ?_, ?_, ?_, ?_⟩
    · omega
    · change 1 ≤ psi
      omega
    · change
        2 * psi - 2 =
          (psi - 1) + (psi - 1)
      omega
    · change
        (psi - 1) * (2 * psi - 1) +
            (psi - 1) =
          (psi - 1) * (2 * psi - 1) +
            (psi - 1)
      rfl
  have hfinal :=
    lemma4FreshTrajectoryPoint_finalPositive
      hpsi hpoint
  omega

private theorem terminalMacroSourceClass
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k i : Fin n)
    (z : GhostToken n psi)
    (q : Nat)
    (hterminal :
      z.lmeta.moves + 1 =
        tokenTrajectoryMoves psi)
    (hq : q < psi)
    (hstage :
      Lemma16FreshMacroStageAt
        ring k i z q) :
    q + 1 = psi ∧
      decodeOffset psi
        (tokenCode z.value) = 1 := by
  have hsplit :=
    terminalMoves_split psi hpsi
  unfold Lemma16FreshMacroStageAt at hstage
  dsimp only at hstage
  rcases hstage with
    ⟨_x, _hsite, hpos | hneg⟩
  · rcases hpos with
      ⟨hcpos, hcbound, _hx, hmoves⟩
    cases hc :
        decodeOffset psi (tokenCode z.value) with
    | ofNat v =>
        rw [hc] at hcpos hcbound hmoves
        change 0 < (v : Int) at hcpos
        change v ≤ psi at hcbound
        change
          z.lmeta.moves =
            q * (2 * psi - 1) +
              (psi - v)
          at hmoves
        have hvpos : 0 < v := by
          omega
        have heq :
            q * (2 * psi - 1) +
                  (psi - v) + 1 =
              (psi - 1) * (2 * psi - 1) +
                psi := by
          calc
            q * (2 * psi - 1) +
                  (psi - v) + 1 =
                z.lmeta.moves + 1 := by
              rw [hmoves]
            _ = tokenTrajectoryMoves psi :=
              hterminal
            _ =
                (psi - 1) * (2 * psi - 1) +
                  psi :=
              hsplit
        have hqlast : q + 1 = psi := by
          refine (Nat.lt_or_ge (q + 1) psi).elim
            (fun hqearly => ?_) (fun hge => by omega)
          exfalso
          have hqbound :
              q + 1 ≤ psi - 1 := by
            omega
          have hmul :
              (q + 1) * (2 * psi - 1) ≤
                (psi - 1) * (2 * psi - 1) :=
            Nat.mul_le_mul_right
              (2 * psi - 1) hqbound
          have hqmul :
              (q + 1) * (2 * psi - 1) =
                q * (2 * psi - 1) +
                  (2 * psi - 1) := by
            rw [Nat.add_mul, Nat.one_mul]
          have hrem :
              psi - v + 1 <
                2 * psi - 1 := by
            omega
          have hlt :
              q * (2 * psi - 1) +
                    (psi - v) + 1 <
                (q + 1) * (2 * psi - 1) := by
            omega
          omega
        have hqeq : q = psi - 1 := by
          omega
        rw [hqeq] at heq
        have hv : v = 1 := by
          omega
        constructor
        · exact hqlast
        · subst hv
          rfl
    | negSucc v =>
        rw [hc] at hcpos
        omega

  · rcases hneg with
      ⟨hcneg, hcbound, _hx, hmoves⟩
    cases hc :
        decodeOffset psi (tokenCode z.value) with
    | ofNat v =>
        rw [hc] at hcneg
        change (v : Int) < 0 at hcneg
        omega
    | negSucc v =>
        rw [hc] at hcbound hmoves
        change Nat.succ v < psi at hcbound
        change
          z.lmeta.moves =
            q * (2 * psi - 1) +
              (2 * psi - 1 - Nat.succ v)
          at hmoves
        have heq :
            q * (2 * psi - 1) +
                  (2 * psi - 1 - Nat.succ v) + 1 =
              (psi - 1) * (2 * psi - 1) +
                psi := by
          calc
            q * (2 * psi - 1) +
                  (2 * psi - 1 - Nat.succ v) + 1 =
                z.lmeta.moves + 1 := by
              rw [hmoves]
            _ = tokenTrajectoryMoves psi :=
              hterminal
            _ =
                (psi - 1) * (2 * psi - 1) +
                  psi :=
              hsplit
        by_cases hlast : q + 1 = psi
        · have hqeq : q = psi - 1 := by
            omega
          rw [hqeq] at heq
          omega
        · have hqearly : q + 1 < psi := by
            omega
          have hqbound :
              q + 1 ≤ psi - 1 := by
            omega
          have hmul :
              (q + 1) * (2 * psi - 1) ≤
                (psi - 1) * (2 * psi - 1) :=
            Nat.mul_le_mul_right
              (2 * psi - 1) hqbound
          have hqmul :
              (q + 1) * (2 * psi - 1) =
                q * (2 * psi - 1) +
                  (2 * psi - 1) := by
            rw [Nat.add_mul, Nat.one_mul]
          have hrem :
              (2 * psi - 1 - Nat.succ v) + 1 ≤
                2 * psi - 1 := by
            omega
          have hle :
              q * (2 * psi - 1) +
                    (2 * psi - 1 - Nat.succ v) + 1 ≤
                (q + 1) * (2 * psi - 1) := by
            omega
          omega

theorem lemma16TerminalDoneSourceClassUnique_proved :
    Lemma16TerminalDoneSourceClassUnique := by
  unfold Lemma16TerminalDoneSourceClassUnique
  intro n psi kappa
  intro hpsi ring k kind step G e i z m q
  intro hunique _hpair howner _hzfresh
  intro hadv hmDone hfresh hq hstage

  have hterminal :
      z.lmeta.moves + 1 =
        tokenTrajectoryMoves psi := by
    calc
      z.lmeta.moves + 1 =
          (ghostStepLineageAdvance z.lmeta).moves := by
        rfl
      _ = m.moves := by
        rw [hadv]
      _ = tokenTrajectoryMoves psi :=
        hfresh.2

  rcases
      terminalMacroSourceClass
        hpsi ring k i z q
        hterminal hq hstage with
    ⟨hqlast, hcfinal⟩

  have hmMirror :
      m ∈
        (doneProvSelectedPair
          hpsi ring step G e kind).done := by
    rw [doneProvSelectedPair_eq_export]
    exact hmDone

  rcases
      doneProvSelectedPair_done_source_class
        hpsi ring step G e kind m hmMirror with
    hleft | hright
  · rcases hleft with
      ⟨z0, howner0, hadv0⟩
    have hadvEq :
        ghostStepLineageAdvance z0.lmeta =
          ghostStepLineageAdvance z.lmeta :=
      hadv0.symm.trans hadv
    have hid :
        z0.lmeta.id = z.lmeta.id := by
      have hid' :=
        congrArg
          (fun mm : LineageMeta n => mm.id)
          hadvEq
      simpa [ghostStepLineageAdvance] using hid'
    have hei : e = i :=
      hunique
        kind e i z0 z
        howner0 howner hid
    exact ⟨hei.symm, hqlast, hcfinal⟩

  · rcases hright with
      ⟨z0, howner0, hadv0, hneg0⟩
    have hadvEq :
        ghostStepLineageAdvance z0.lmeta =
          ghostStepLineageAdvance z.lmeta :=
      hadv0.symm.trans hadv
    have hid :
        z0.lmeta.id = z.lmeta.id := by
      have hid' :=
        congrArg
          (fun mm : LineageMeta n => mm.id)
          hadvEq
      simpa [ghostStepLineageAdvance] using hid'
    have hri :
        ring.rightNeighbor e = i :=
      hunique
        kind (ring.rightNeighbor e) i
        z0 z howner0 howner hid
    have hz0z : z0 = z := by
      have hsome :
          some z0 = some z := by
        calc
          some z0 =
              ghostTokenAt kind G
                (ring.rightNeighbor e) :=
            howner0.symm
          _ = ghostTokenAt kind G i := by
            rw [hri]
          _ = some z :=
            howner
      exact Option.some.inj hsome
    rw [hz0z, hcfinal] at hneg0
    omega

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16TerminalDoneSourceClassUnique_proved
