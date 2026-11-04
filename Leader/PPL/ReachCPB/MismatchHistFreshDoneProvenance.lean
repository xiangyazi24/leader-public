import Leader.PPL.ReachCPB.MismatchHistFreshDistCanonLocal
import Leader.PPL.TokenCompletion.GhostStepMirror
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
A proof-local mirror of the selected ghost row.  The implementation names in
TokenCorrectness are private, so, as in ReachCPBMismatchHistFreshCoherent,
ReachCPBMismatchHistFreshAge, and TokenCorrectnessLemma4FreshTerminalRun, we
copy the definitions definitionally and bridge back to the public export.
-/

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

private def doneProvSetTwo
    {n : Nat} {A : Type}
    (f : Fin n → A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n → A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def doneProvGhostStep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let pre :=
    doneProvTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  let gb :=
    doneProvGhostMoveToken hpsi .black step e
      pre.1 pre.2
      (G.black e) (G.black rsite)
  let qb :=
    moveToken hpsi .black pre.1 pre.2
  let gw :=
    doneProvGhostMoveToken hpsi .white step e
      qb.1 qb.2
      (G.white e) (G.white rsite)
  { phys :=
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e
    black :=
      doneProvSetTwo
        G.black e rsite gb.left gb.right
    white :=
      doneProvSetTwo
        G.white e rsite gw.left gw.right
    completed :=
      G.completed ++ gb.done ++ gw.done }

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

private theorem doneProvGhostStep_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    doneProvGhostStep hpsi ring step G e =
      ghostStep hpsi ring step G e := by
  unfold doneProvGhostStep ghostStep
  unfoldGhostStepCore
  rfl

private theorem doneProvGhostStep_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (doneProvGhostStep
      hpsi ring step G e).completed =
      G.completed ++
        (doneProvSelectedPair
          hpsi ring step G e .black).done ++
        (doneProvSelectedPair
          hpsi ring step G e .white).done := by
  rfl

/-! ## Done provenance through the mirrored row -/

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

private theorem doneProvFinish_done_source
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
    (∃ z : GhostToken n psi,
      gr0 = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi) := by
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
            exact
              .inr
                (bump_done_source
                  kind l next gr0 m hm)
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
              exact
                .inr
                  (bump_done_source
                    kind l next gr0 m hm)
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
                exact
                  .inr
                    (bump_done_source
                      kind l next gr0 m hm)
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
                  exact
                    .inr
                      (bump_done_source
                        kind l next gr0 m hm)
                · simp
                    [doneProvFinishMove, hlv, hrv,
                      h1, h2, hm1, hm2] at hm

private theorem doneProvGhostMove_done_source
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
      m = ghostStepLineageAdvance z.lmeta) := by
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
        doneProvFinish_done_source
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
        ⟨z, hgr0, hmadv, _hterm⟩
      have hsource :
          gr = some z :=
        doneProvLiveShadow_source
          kind r gr z hgr0
      exact .inr ⟨z, hsource, hmadv⟩

  · simp
      [doneProvGhostMoveToken,
        if_neg hlast] at hm

private theorem doneProvSelectedPair_done_source
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
    ∃ (i : Fin n)
      (z : GhostToken n psi),
      (i = e ∨
        i = ring.rightNeighbor e) ∧
      ghostTokenAt kind G i = some z ∧
      m = ghostStepLineageAdvance z.lmeta := by
  unfold doneProvSelectedPair at hm
  rcases
      doneProvGhostMove_done_source
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
    exact
      ⟨e, z, .inl rfl, howner, hmadv⟩
  · rcases hright with ⟨z, howner, hmadv⟩
    exact
      ⟨ring.rightNeighbor e, z,
        .inr rfl, howner, hmadv⟩

private theorem doneProvFreshAt_advance_iff
    {n : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n) :
    FreshAt kind k
        (ghostStepLineageAdvance m) ↔
      FreshAt kind k m := by
  unfold FreshAt ghostStepLineageAdvance
  rfl

private theorem doneProvWrongKind_done_impossible
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (slotKind targetKind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n)
    (hne : slotKind ≠ targetKind)
    (hcoh : Lemma16GhostLineageCoherent G)
    (hm :
      m ∈
        (doneProvSelectedPair
          hpsi ring step G e slotKind).done)
    (hfresh :
      FreshCompletion
        (psi := psi) targetKind k m) :
    False := by
  rcases
      doneProvSelectedPair_done_source
        hpsi ring step G e slotKind m hm with
    ⟨i, z, _hpair, howner, hmadv⟩
  have hfreshAdv :
      FreshAt targetKind k
        (ghostStepLineageAdvance z.lmeta) := by
    rw [← hmadv]
    exact hfresh.1
  have hfreshZ :
      FreshAt targetKind k z.lmeta :=
    (doneProvFreshAt_advance_iff
      targetKind k z.lmeta).1 hfreshAdv
  rcases hfreshZ with ⟨t, hid, _hsite⟩
  have hkinds :=
    hcoh
      slotKind targetKind
      i z t howner hid
  exact hne hkinds.1

/-!
The only fresh lineage that can be introduced by this interaction has
moves = 0.  If it is immediately bumped, its advanced metadata has moves = 1.
The hpsi premise gives tokenTrajectoryMoves psi > 1, so such a birth cannot
appear in done.  Hence a done entry is the advance of an old endpoint owner.
The completed-list split then removes G.completed with hnew, while lineage
coherence removes the other colour's done list.
-/
theorem lemma16PostEpochFreshNewCompletionDoneProvenanceRow_proved :
    Lemma16PostEpochFreshNewCompletionDoneProvenanceRow := by
  unfold Lemma16PostEpochFreshNewCompletionDoneProvenanceRow
  intro n psi kappa
  intro hpsi ring step G e kind k
  intro hcoh m hm hfresh hnew

  rw [← doneProvGhostStep_eq
    hpsi ring step G e] at hm
  rw [doneProvGhostStep_completed
    hpsi ring step G e] at hm
  simp only [List.mem_append] at hm

  rcases hm with holdOrBlack | hwhite
  · rcases holdOrBlack with hold | hblack
    · exact False.elim (hnew hold)

    · cases kind with
      | black =>
          have hdone :
              m ∈
                (ghostStepSelectedPair
                  hpsi ring step G e .black).done := by
            rw [← doneProvSelectedPair_eq_export
              hpsi ring step G e .black]
            exact hblack

          rcases
              doneProvSelectedPair_done_source
                hpsi ring step G e .black m hblack with
            ⟨i, z, hpair, howner, hmadv⟩

          have hfreshAdv :
              FreshAt .black k
                (ghostStepLineageAdvance z.lmeta) := by
            rw [← hmadv]
            exact hfresh.1
          have hfreshZ :
              FreshAt .black k z.lmeta :=
            (doneProvFreshAt_advance_iff
              .black k z.lmeta).1 hfreshAdv

          exact
            ⟨hdone, i, z,
              hpair, howner, hfreshZ, hmadv⟩

      | white =>
          have hfalse : False :=
            doneProvWrongKind_done_impossible
              hpsi ring step G e
              .black .white k m
              (by decide) hcoh hblack hfresh
          exact hfalse.elim

  · cases kind with
    | black =>
        have hfalse : False :=
          doneProvWrongKind_done_impossible
            hpsi ring step G e
            .white .black k m
            (by decide) hcoh hwhite hfresh
        exact hfalse.elim

    | white =>
        have hdone :
            m ∈
              (ghostStepSelectedPair
                hpsi ring step G e .white).done := by
          rw [← doneProvSelectedPair_eq_export
            hpsi ring step G e .white]
          exact hwhite

        rcases
            doneProvSelectedPair_done_source
              hpsi ring step G e .white m hwhite with
          ⟨i, z, hpair, howner, hmadv⟩

        have hfreshAdv :
            FreshAt .white k
              (ghostStepLineageAdvance z.lmeta) := by
          rw [← hmadv]
          exact hfresh.1
        have hfreshZ :
            FreshAt .white k z.lmeta :=
          (doneProvFreshAt_advance_iff
            .white k z.lmeta).1 hfreshAdv

        exact
          ⟨hdone, i, z,
            hpair, howner, hfreshZ, hmadv⟩

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshNewCompletionDoneProvenanceRow_proved
