import Leader.PPL.TokenCompletion.GhostStepMirror
import Leader.PPL.TokenCompletion.RightmostInitiatorAged
import Leader.PPL.TokenCompletion.CoverageLeaves
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false

private def Lemma4FreshTerminalHistory
    {n psi kappa : Nat}
    (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ kind i z,
    ghostTokenAt kind G i = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi ∨
      HasFreshCompletion kind k G

private def terminalBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def terminalMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def terminalLocalValid
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

private instance instDecidableTerminalLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (terminalLocalValid kind q t) := by
  unfold terminalLocalValid
  infer_instance

private def terminalTokenPrelude
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

private def terminalLiveShadow
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
          if z.value = t ∧ terminalLocalValid kind q t then
            some z
          else
            none

private def terminalLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if terminalLocalValid kind q t then some t else none

private def terminalBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      terminalMkToken
        (offsetPsiCode psi hpsi)
        (terminalBitToFin (!idBit))
        (terminalBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def terminalBumpTo
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
        if m'.moves = tokenTrajectoryMoves psi then [m'] else []
      let live :=
        if terminalLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def terminalNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    terminalMkToken
      (offsetPsiCode psi hpsi)
      (terminalBitToFin (!sourceBit))
      (terminalBitToFin sourceBit)
  else
    terminalMkToken
      (offsetPsiCode psi hpsi)
      (terminalBitToFin sourceBit)
      (0 : Fin 2)

private def terminalFinishMove
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
          terminalMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := terminalBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          terminalMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := terminalBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                terminalNegTurnNext hpsi l.id tr
              let b := terminalBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid psi (by omega) (tokenCode tr)
              let next :=
                terminalMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := terminalBumpTo kind l next gr0
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
              terminalNegTurnNext hpsi l.id tr
            let b := terminalBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid psi (by omega) (tokenCode tr)
            let next :=
              terminalMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := terminalBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def terminalGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := terminalLiveValue kind l
  let rv0 := terminalLiveValue kind r
  let gl0 := terminalLiveShadow kind l gl
  let gr0 := terminalLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (terminalBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (terminalBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    terminalFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def terminalSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := terminalTokenPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2

private def terminalSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let p :=
    terminalSelectedInput hpsi kind
      (G.phys e) (G.phys rsite)
  terminalGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G rsite)

private def terminalSetTwo
    {n : Nat} {A : Type}
    (f : Fin n → A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n → A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def terminalGhostStep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let pre :=
    terminalTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  let gb :=
    terminalGhostMoveToken hpsi .black step e
      pre.1 pre.2 (G.black e) (G.black rsite)
  let qb := moveToken hpsi .black pre.1 pre.2
  let gw :=
    terminalGhostMoveToken hpsi .white step e
      qb.1 qb.2 (G.white e) (G.white rsite)
  { phys :=
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e
    black :=
      terminalSetTwo G.black e rsite gb.left gb.right
    white :=
      terminalSetTwo G.white e rsite gw.left gw.right
    completed := G.completed ++ gb.done ++ gw.done }

private theorem terminalSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    terminalSelectedPair hpsi ring step G e kind =
      ghostStepSelectedPair hpsi ring step G e kind := by
  cases kind <;> rfl

private theorem terminalGhostStep_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    terminalGhostStep hpsi ring step G e =
      ghostStep hpsi ring step G e := by
  unfold terminalGhostStep ghostStep
  unfoldGhostStepCore
  rfl

private theorem terminalGhostStep_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (terminalGhostStep hpsi ring step G e).completed =
      G.completed ++
        (terminalSelectedPair
          hpsi ring step G e .black).done ++
        (terminalSelectedPair
          hpsi ring step G e .white).done := by
  rfl

private def TerminalYoung
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (g : Option (GhostToken n psi)) : Prop :=
  ∀ z,
    g = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi

private def TerminalStepGood
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (g : Option (GhostToken n psi))
    (done : List (LineageMeta n)) : Prop :=
  ∀ z,
    g = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi ∨
      ∃ m,
        m ∈ done ∧
          FreshCompletion (psi := psi) kind k m

private theorem terminalTrajectoryMoves_pos
    (psi : Nat) :
    0 < tokenTrajectoryMoves psi := by
  unfold tokenTrajectoryMoves
  exact Nat.zero_lt_succ _

private theorem terminalFreshAt_advance_iff
    {n : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n) :
    FreshAt kind k (ghostStepLineageAdvance m) ↔
      FreshAt kind k m := by
  unfold FreshAt ghostStepLineageAdvance
  rfl

private theorem terminalYoung_none
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n) :
    TerminalYoung
      (psi := psi) kind k none := by
  intro z hz _hfresh
  cases hz

private theorem terminalStep_none
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (done : List (LineageMeta n)) :
    TerminalStepGood
      (psi := psi) kind k none done := by
  intro z hz _hfresh
  cases hz

private theorem terminalStep_of_young
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (g : Option (GhostToken n psi))
    (done : List (LineageMeta n))
    (hyoung : TerminalYoung kind k g) :
    TerminalStepGood kind k g done := by
  intro z hz hfresh
  exact .inl (hyoung z hz hfresh)

private theorem terminalLiveShadow_young
    {n psi kappa : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hyoung : TerminalYoung kind k g) :
    TerminalYoung kind k
      (terminalLiveShadow kind q g) := by
  intro z hz hfresh
  cases hg : g with
  | none =>
      simp [terminalLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [terminalLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧ terminalLocalValid kind q t
          · have hzz : z0 = z := by
              simpa [terminalLiveShadow, hg, ht, hv]
                using hz
            subst z
            exact hyoung z0 hg hfresh
          · simp [terminalLiveShadow, hg, ht, hv] at hz

private theorem terminalBirth_young
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (k : Fin n)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    TerminalYoung kind k
      (some
        (terminalBirthGhost
          hpsi kind step site idBit)) := by
  intro z hz _hfresh
  cases hz
  change 0 < tokenTrajectoryMoves psi
  exact terminalTrajectoryMoves_pos psi

private theorem terminalBump_status
    {n psi kappa : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (hyoung : TerminalYoung kind k g) :
    TerminalStepGood kind k
      (terminalBumpTo kind qDest newValue g).live
      (terminalBumpTo kind qDest newValue g).done := by
  intro z' hz hfresh
  cases hg : g with
  | none =>
      simp [terminalBumpTo, hg] at hz
  | some z =>
      by_cases hv :
          terminalLocalValid kind qDest newValue
      · simp [terminalBumpTo, hg, hv] at hz
        cases hz
        have hfresh0 :
            FreshAt kind k z.lmeta :=
          (terminalFreshAt_advance_iff
            kind k z.lmeta).1 hfresh
        have hold :
            z.lmeta.moves <
              tokenTrajectoryMoves psi :=
          hyoung z hg hfresh0
        by_cases hdone :
            (ghostStepLineageAdvance z.lmeta).moves =
              tokenTrajectoryMoves psi
        · exact
            .inr
              ⟨ghostStepLineageAdvance z.lmeta,
                by
                  simp [terminalBumpTo, hg, hdone],
                ⟨hfresh, hdone⟩⟩
        · left
          change
            z.lmeta.moves + 1 <
              tokenTrajectoryMoves psi
          have hne :
              z.lmeta.moves + 1 ≠
                tokenTrajectoryMoves psi := by
            simpa [ghostStepLineageAdvance]
              using hdone
          omega
      · simp [terminalBumpTo, hg, hv] at hz

private theorem terminalFinish_status
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (k : Fin n)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (hleft : TerminalYoung kind k gl2)
    (hright : TerminalYoung kind k gr0) :
    let out :=
      terminalFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0
    TerminalStepGood kind k out.left out.done ∧
      TerminalStepGood kind k out.right out.done := by
  cases lv2 with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [terminalFinishMove, dif_pos h1]
        let next :=
          terminalMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        exact
          ⟨terminalStep_none kind k _,
            terminalBump_status
              kind k r next gl2 hleft⟩
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · simp only
            [terminalFinishMove,
              dif_neg h1, dif_pos h2]
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            terminalMkToken
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
            ⟨terminalStep_none kind k _,
              terminalBump_status
                kind k r next gl2 hleft⟩
        · cases rv0 with
          | none =>
              simp only
                [terminalFinishMove,
                  dif_neg h1, dif_neg h2]
              exact
                ⟨terminalStep_of_young
                    kind k gl2 [] hleft,
                  terminalStep_of_young
                    kind k gr0 [] hright⟩
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [terminalFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1]
                let next :=
                  terminalNegTurnNext hpsi l.id tr
                exact
                  ⟨terminalBump_status
                      kind k l next gr0 hright,
                    terminalStep_none kind k _⟩
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · simp only
                    [terminalFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2]
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    terminalMkToken
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
                    ⟨terminalBump_status
                        kind k l next gr0 hright,
                      terminalStep_none kind k _⟩
                · simp only
                    [terminalFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]
                  exact
                    ⟨terminalStep_of_young
                        kind k gl2 [] hleft,
                      terminalStep_of_young
                        kind k gr0 [] hright⟩
  | none =>
      cases rv0 with
      | none =>
          simp only [terminalFinishMove]
          exact
            ⟨terminalStep_of_young
                kind k gl2 [] hleft,
              terminalStep_of_young
                kind k gr0 [] hright⟩
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [terminalFinishMove, dif_pos hm1]
            let next :=
              terminalNegTurnNext hpsi l.id tr
            exact
              ⟨terminalBump_status
                  kind k l next gr0 hright,
                terminalStep_none kind k _⟩
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · simp only
                [terminalFinishMove,
                  dif_neg hm1, dif_pos hm2]
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                terminalMkToken
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
                ⟨terminalBump_status
                    kind k l next gr0 hright,
                  terminalStep_none kind k _⟩
            · simp only
                [terminalFinishMove,
                  dif_neg hm1, dif_neg hm2]
              exact
                ⟨terminalStep_of_young
                    kind k gl2 [] hleft,
                  terminalStep_of_young
                    kind k gr0 [] hright⟩

private theorem terminalGhostMove_status
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (k : Fin n)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgl : TerminalYoung kind k gl)
    (hgr : TerminalYoung kind k gr) :
    let out :=
      terminalGhostMoveToken
        hpsi kind step site l r gl gr
    TerminalStepGood kind k out.left out.done ∧
      TerminalStepGood kind k out.right out.done := by
  let lv0 := terminalLiveValue kind l
  let rv0 := terminalLiveValue kind r
  let gl0 := terminalLiveShadow kind l gl
  let gr0 := terminalLiveShadow kind r gr
  have hgl0 :
      TerminalYoung kind k gl0 := by
    exact
      terminalLiveShadow_young
        kind k l gl hgl
  have hgr0 :
      TerminalYoung kind k gr0 := by
    exact
      terminalLiveShadow_young
        kind k r gr hgr

  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      terminalBirthGhost
        hpsi kind step site l.id
    let lv1 : Option (TokenData psi) :=
      if hb then some birth.value else lv0
    let gl1 : Option (GhostToken n psi) :=
      if hb then some birth else gl0

    have hgl1 :
        TerminalYoung kind k gl1 := by
      by_cases hbirth : hb
      · simp only [gl1, if_pos hbirth]
        exact
          terminalBirth_young
            hpsi kind k step site l.id
      · simpa [gl1, hbirth] using hgl0

    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 : Option (TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (GhostToken n psi) :=
      if collide then none else gl1

    have hgl2 :
        TerminalYoung kind k gl2 := by
      by_cases hcol : collide
      · simp only [gl2, if_pos hcol]
        exact terminalYoung_none kind k
      · simpa [gl2, hcol] using hgl1

    have hfinish :=
      terminalFinish_status
        hpsi kind k l r
        lv2 rv0 gl2 gr0 hgl2 hgr0

    simp only
      [terminalGhostMoveToken,
        if_pos hlast]
    exact hfinish
  · simp only
      [terminalGhostMoveToken,
        if_neg hlast]
    exact
      ⟨terminalStep_of_young
          kind k gl0 [] hgl0,
        terminalStep_of_young
          kind k gr0 [] hgr0⟩

private theorem terminalSelectedPair_status
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hleft :
      TerminalYoung kind k
        (ghostTokenAt kind G e))
    (hright :
      TerminalYoung kind k
        (ghostTokenAt kind G
          (ring.rightNeighbor e))) :
    let out :=
      terminalSelectedPair
        hpsi ring step G e kind
    TerminalStepGood kind k out.left out.done ∧
      TerminalStepGood kind k out.right out.done := by
  unfold terminalSelectedPair
  cases kind with
  | black =>
      dsimp only
      exact
        terminalGhostMove_status
          hpsi .black k step e
          (terminalTokenPrelude hpsi
            (G.phys e)
            (G.phys
              (ring.rightNeighbor e))).1
          (terminalTokenPrelude hpsi
            (G.phys e)
            (G.phys
              (ring.rightNeighbor e))).2
          (G.black e)
          (G.black (ring.rightNeighbor e))
          hleft hright
  | white =>
      dsimp only
      let pre :=
        terminalTokenPrelude hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))
      let qb :=
        moveToken hpsi .black pre.1 pre.2
      exact
        terminalGhostMove_status
          hpsi .white k step e
          qb.1 qb.2
          (G.white e)
          (G.white (ring.rightNeighbor e))
          hleft hright

private theorem terminalHasFreshCompletion_step
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (k : Fin n)
    (h : HasFreshCompletion kind k G) :
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e) := by
  unfold HasFreshCompletion at h ⊢
  rcases h with ⟨m, hm, hfresh⟩
  refine ⟨m, ?_, hfresh⟩
  simp only [ghostStep, List.mem_append]
  exact .inl (.inl hm)

private theorem terminalSelectedDone_mem_completed
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
        (terminalSelectedPair
          hpsi ring step G e kind).done) :
    m ∈
      (ghostStep hpsi ring step G e).completed := by
  rw [← terminalGhostStep_eq
    hpsi ring step G e]
  rw [terminalGhostStep_completed
    hpsi ring step G e]
  simp only [List.mem_append]
  cases kind with
  | black =>
      exact .inl (.inr hm)
  | white =>
      exact .inr hm

private theorem terminalHasFreshCompletion_of_selectedDone
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n)
    (hm :
      m ∈
        (terminalSelectedPair
          hpsi ring step G e kind).done)
    (hfresh :
      FreshCompletion (psi := psi) kind k m) :
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e) := by
  exact
    ⟨m,
      terminalSelectedDone_mem_completed
        hpsi ring step G e kind m hm,
      hfresh⟩

private theorem terminalHistory_step
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hhist : Lemma4FreshTerminalHistory k G) :
    Lemma4FreshTerminalHistory k
      (ghostStep hpsi ring step G e) := by
  intro kind i z howner hfresh
  by_cases hdone :
      HasFreshCompletion kind k G
  · exact
      .inr
        (terminalHasFreshCompletion_step
          hpsi ring step G e kind k hdone)
  · have hleft :
        TerminalYoung kind k
          (ghostTokenAt kind G e) := by
      intro z0 hz0 hfresh0
      rcases
          hhist kind e z0 hz0 hfresh0 with
        hyoung | hcomplete
      · exact hyoung
      · exact False.elim (hdone hcomplete)

    have hright :
        TerminalYoung kind k
          (ghostTokenAt kind G
            (ring.rightNeighbor e)) := by
      intro z0 hz0 hfresh0
      rcases
          hhist kind (ring.rightNeighbor e)
            z0 hz0 hfresh0 with
        hyoung | hcomplete
      · exact hyoung
      · exact False.elim (hdone hcomplete)

    have hpair :=
      terminalSelectedPair_status
        hpsi ring k step G e kind
        hleft hright

    by_cases hie : i = e
    · subst i
      have hlocal :
          (terminalSelectedPair
            hpsi ring step G e kind).left =
            some z := by
        rw [terminalSelectedPair_eq_export]
        exact
          (ghostTokenAt_ghostStep_initiator
            hpsi ring step G e kind).symm.trans
              howner
      rcases hpair.1 z hlocal hfresh with
        hyoung | hlogged
      · exact .inl hyoung
      · rcases hlogged with
          ⟨m, hm, hcompletion⟩
        exact
          .inr
            (terminalHasFreshCompletion_of_selectedDone
              hpsi ring step G e kind k
              m hm hcompletion)

    · by_cases hir :
          i = ring.rightNeighbor e
      · subst i
        have hne :
            ring.rightNeighbor e ≠ e := hie
        have hlocal :
            (terminalSelectedPair
              hpsi ring step G e kind).right =
              some z := by
          rw [terminalSelectedPair_eq_export]
          exact
            (ghostTokenAt_ghostStep_responder_of_ne
              hpsi ring step G e kind hne).symm.trans
                howner
        rcases hpair.2 z hlocal hfresh with
          hyoung | hlogged
        · exact .inl hyoung
        · rcases hlogged with
            ⟨m, hm, hcompletion⟩
          exact
            .inr
              (terminalHasFreshCompletion_of_selectedDone
                hpsi ring step G e kind k
                m hm hcompletion)

      · have howner0 :
            ghostTokenAt kind G i = some z := by
          exact
            (ghostTokenAt_ghostStep_frame
              hpsi ring step G e i kind
              hie hir).symm.trans howner
        rcases
            hhist kind i z howner0 hfresh with
          hyoung | hcomplete
        · exact .inl hyoung
        · exact False.elim (hdone hcomplete)

private theorem terminalHistory_initial
    {n psi kappa : Nat}
    (k : Fin n)
    (C0 : Config n psi kappa) :
    Lemma4FreshTerminalHistory k
      (initialGhost C0) := by
  intro kind i z howner hfresh
  rcases hfresh with ⟨t, hborn, _hsite⟩
  have hbefore :=
    (ghostIdsUnique_initial C0).2
      kind i z kind t howner hborn
  have hfalse : False := by
    omega
  exact hfalse.elim

private theorem terminalHistory_run_from
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n) :
    ∀ (t : Nat)
      (G : GhostConfig n psi kappa)
      (pre : DetSchedule n),
      Lemma4FreshTerminalHistory k G →
      Lemma4FreshTerminalHistory k
        (ghostRun hpsi ring t G pre) := by
  intro t G pre hhist
  induction pre generalizing t G with
  | nil =>
      exact hhist
  | cons e es ih =>
      simp only [ghostRun]
      exact
        ih (t := t + 1)
          (G := ghostStep hpsi ring t G e)
          (terminalHistory_step
            hpsi ring k t G e hhist)

theorem lemma4FreshTerminalProvenance_run
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (k : Fin n) :
    Lemma4FreshTerminalProvenance k
      (ghostRun hpsi ring 0
        (initialGhost C0) pre) := by
  have hhist :
      Lemma4FreshTerminalHistory k
        (ghostRun hpsi ring 0
          (initialGhost C0) pre) :=
    terminalHistory_run_from
      hpsi ring k 0 (initialGhost C0) pre
      (terminalHistory_initial k C0)
  intro kind i z howner hnoCompletion hfresh
  rcases
      hhist kind i z howner hfresh with
    hyoung | hcomplete
  · exact hyoung
  · exact False.elim (hnoCompletion hcomplete)

/-- The rightmost-initiator branch now reduces to the aged no-prior-row leaf. -/
theorem lemma4RightmostInitiatorBranch_of_noPriorRow
    (hNoPrior :
      Lemma4RightmostInitiatorAgedNoPriorCompletionRow) :
    Lemma4RightmostInitiatorBranch :=
  lemma4RightmostInitiatorBranch_of_literalCasesAged
    lemma4CoverageGhostRunSound_proved
    (by
      intro n psi kappa hpsi ring k C0 pre
      exact lemma4FreshTerminalProvenance_run hpsi ring C0 pre k)
    (lemma4RightmostInitiatorLiteralCasesAged_of_noPriorRow hNoPrior)

end PPL

#print axioms PPL.lemma4FreshTerminalProvenance_run
#print axioms PPL.lemma4RightmostInitiatorBranch_of_noPriorRow
