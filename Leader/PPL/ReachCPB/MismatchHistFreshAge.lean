import Leader.PPL.ReachCPB.MismatchHistFreshLiveRow
import Leader.PPL.TokenCompletion.FreshTerminalRun
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

private def ageBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def ageMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def ageLocalValid
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
    Decidable (ageLocalValid kind q t) := by
  unfold ageLocalValid
  infer_instance

private def ageTokenPrelude
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

private def ageLiveShadow
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
          if z.value = t ∧ ageLocalValid kind q t then
            some z
          else
            none

private def ageLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if ageLocalValid kind q t then some t else none

private def ageBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      ageMkToken
        (offsetPsiCode psi hpsi)
        (ageBitToFin (!idBit))
        (ageBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def ageBumpTo
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
        if ageLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def ageNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    ageMkToken
      (offsetPsiCode psi hpsi)
      (ageBitToFin (!sourceBit))
      (ageBitToFin sourceBit)
  else
    ageMkToken
      (offsetPsiCode psi hpsi)
      (ageBitToFin sourceBit)
      (0 : Fin 2)

private def ageFinishMove
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
          ageMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := ageBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          ageMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := ageBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                ageNegTurnNext hpsi l.id tr
              let b := ageBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid psi (by omega) (tokenCode tr)
              let next :=
                ageMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := ageBumpTo kind l next gr0
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
              ageNegTurnNext hpsi l.id tr
            let b := ageBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid psi (by omega) (tokenCode tr)
            let next :=
              ageMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := ageBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def ageGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := ageLiveValue kind l
  let rv0 := ageLiveValue kind r
  let gl0 := ageLiveShadow kind l gl
  let gr0 := ageLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (ageBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (ageBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    ageFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def ageSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := ageTokenPrelude hpsi l r
  match kind with
  | .black => pre
  | .white => moveToken hpsi .black pre.1 pre.2

private def ageSelectedPair
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
    ageSelectedInput hpsi kind
      (G.phys e) (G.phys rsite)
  ageGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G rsite)

private def ageSetTwo
    {n : Nat} {A : Type}
    (f : Fin n → A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n → A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def ageGhostStep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let pre :=
    ageTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  let gb :=
    ageGhostMoveToken hpsi .black step e
      pre.1 pre.2 (G.black e) (G.black rsite)
  let qb := moveToken hpsi .black pre.1 pre.2
  let gw :=
    ageGhostMoveToken hpsi .white step e
      qb.1 qb.2 (G.white e) (G.white rsite)
  { phys :=
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e
    black :=
      ageSetTwo G.black e rsite gb.left gb.right
    white :=
      ageSetTwo G.white e rsite gw.left gw.right
    completed := G.completed ++ gb.done ++ gw.done }

private theorem ageSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ageSelectedPair hpsi ring step G e kind =
      ghostStepSelectedPair hpsi ring step G e kind := by
  cases kind <;> rfl

private theorem ageGhostStep_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    ageGhostStep hpsi ring step G e =
      ghostStep hpsi ring step G e := by
  unfold ageGhostStep ghostStep
  unfoldGhostStepCore
  rfl

private theorem ageGhostStep_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (ageGhostStep hpsi ring step G e).completed =
      G.completed ++
        (ageSelectedPair
          hpsi ring step G e .black).done ++
        (ageSelectedPair
          hpsi ring step G e .white).done := by
  rfl

private def AgeOpt
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (g : Option (GhostToken n psi)) : Prop :=
  ∀ z,
    g = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi ∨
      ∃ m : LineageMeta n,
        m ∈ completed ∧
          m.id = z.lmeta.id

private def AgeStepGood
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (g : Option (GhostToken n psi))
    (done : List (LineageMeta n)) : Prop :=
  ∀ z,
    g = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi ∨
      (∃ m : LineageMeta n,
        m ∈ completed ∧
          m.id = z.lmeta.id) ∨
      ∃ m : LineageMeta n,
        m ∈ done ∧
          m.id = z.lmeta.id

private theorem ageTrajectoryMoves_pos
    (psi : Nat) :
    0 < tokenTrajectoryMoves psi := by
  unfold tokenTrajectoryMoves
  exact Nat.zero_lt_succ _

private theorem ageFreshAt_advance_iff
    {n : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (m : LineageMeta n) :
    FreshAt kind k (ghostStepLineageAdvance m) ↔
      FreshAt kind k m := by
  unfold FreshAt ghostStepLineageAdvance
  rfl

private theorem ageOpt_none
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n)) :
    AgeOpt (psi := psi) kind k completed none := by
  intro z hz _hfresh
  cases hz

private theorem ageStep_none
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed done : List (LineageMeta n)) :
    AgeStepGood
      (psi := psi) kind k completed none done := by
  intro z hz _hfresh
  cases hz

private theorem ageStep_of_age
    {n psi : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (g : Option (GhostToken n psi))
    (done : List (LineageMeta n))
    (hage : AgeOpt kind k completed g) :
    AgeStepGood kind k completed g done := by
  intro z hz hfresh
  rcases hage z hz hfresh with hyoung | hold
  · exact .inl hyoung
  · exact .inr (.inl hold)

private theorem ageLiveShadow_age
    {n psi kappa : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hage : AgeOpt kind k completed g) :
    AgeOpt kind k completed
      (ageLiveShadow kind q g) := by
  intro z hz hfresh
  cases hg : g with
  | none =>
      simp [ageLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [ageLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧ ageLocalValid kind q t
          · have hzz : z0 = z := by
              simpa [ageLiveShadow, hg, ht, hv]
                using hz
            subst z
            exact hage z0 hg hfresh
          · simp [ageLiveShadow, hg, ht, hv] at hz

private theorem ageBirth_age
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    AgeOpt kind k completed
      (some
        (ageBirthGhost
          hpsi kind step site idBit)) := by
  intro z hz _hfresh
  cases hz
  left
  change 0 < tokenTrajectoryMoves psi
  exact ageTrajectoryMoves_pos psi

private theorem ageBump_status
    {n psi kappa : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (hage : AgeOpt kind k completed g) :
    AgeStepGood kind k completed
      (ageBumpTo kind qDest newValue g).live
      (ageBumpTo kind qDest newValue g).done := by
  intro z' hz hfresh
  cases hg : g with
  | none =>
      simp [ageBumpTo, hg] at hz
  | some z =>
      by_cases hv :
          ageLocalValid kind qDest newValue
      · simp [ageBumpTo, hg, hv] at hz
        cases hz
        have hfresh0 :
            FreshAt kind k z.lmeta :=
          (ageFreshAt_advance_iff
            kind k z.lmeta).1 hfresh
        rcases hage z hg hfresh0 with hyoung | hold
        · by_cases hdone :
              (ghostStepLineageAdvance z.lmeta).moves =
                tokenTrajectoryMoves psi
          · exact
              .inr (.inr
                ⟨ghostStepLineageAdvance z.lmeta,
                  by
                    simp [ageBumpTo, hg, hdone],
                  rfl⟩)
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
        · right
          left
          rcases hold with ⟨m, hm, hid⟩
          exact
            ⟨m, hm, by
              simpa [ghostStepLineageAdvance]
                using hid⟩
      · simp [ageBumpTo, hg, hv] at hz

private theorem ageFinish_status
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (hleft : AgeOpt kind k completed gl2)
    (hright : AgeOpt kind k completed gr0) :
    let out :=
      ageFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0
    AgeStepGood kind k completed out.left out.done ∧
      AgeStepGood kind k completed out.right out.done := by
  cases lv2 with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [ageFinishMove, dif_pos h1]
        let next :=
          ageMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        exact
          ⟨ageStep_none kind k completed _,
            ageBump_status
              kind k completed r next gl2 hleft⟩
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · simp only
            [ageFinishMove,
              dif_neg h1, dif_pos h2]
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            ageMkToken
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
            ⟨ageStep_none kind k completed _,
              ageBump_status
                kind k completed r next gl2 hleft⟩
        · cases rv0 with
          | none =>
              simp only
                [ageFinishMove,
                  dif_neg h1, dif_neg h2]
              exact
                ⟨ageStep_of_age
                    kind k completed gl2 [] hleft,
                  ageStep_of_age
                    kind k completed gr0 [] hright⟩
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [ageFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1]
                let next :=
                  ageNegTurnNext hpsi l.id tr
                exact
                  ⟨ageBump_status
                      kind k completed l next gr0 hright,
                    ageStep_none kind k completed _⟩
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · simp only
                    [ageFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2]
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    ageMkToken
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
                    ⟨ageBump_status
                        kind k completed l next gr0 hright,
                      ageStep_none kind k completed _⟩
                · simp only
                    [ageFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]
                  exact
                    ⟨ageStep_of_age
                        kind k completed gl2 [] hleft,
                      ageStep_of_age
                        kind k completed gr0 [] hright⟩
  | none =>
      cases rv0 with
      | none =>
          simp only [ageFinishMove]
          exact
            ⟨ageStep_of_age
                kind k completed gl2 [] hleft,
              ageStep_of_age
                kind k completed gr0 [] hright⟩
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [ageFinishMove, dif_pos hm1]
            let next :=
              ageNegTurnNext hpsi l.id tr
            exact
              ⟨ageBump_status
                  kind k completed l next gr0 hright,
                ageStep_none kind k completed _⟩
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · simp only
                [ageFinishMove,
                  dif_neg hm1, dif_pos hm2]
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                ageMkToken
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
                ⟨ageBump_status
                    kind k completed l next gr0 hright,
                  ageStep_none kind k completed _⟩
            · simp only
                [ageFinishMove,
                  dif_neg hm1, dif_neg hm2]
              exact
                ⟨ageStep_of_age
                    kind k completed gl2 [] hleft,
                  ageStep_of_age
                    kind k completed gr0 [] hright⟩

private theorem ageGhostMove_status
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgl : AgeOpt kind k completed gl)
    (hgr : AgeOpt kind k completed gr) :
    let out :=
      ageGhostMoveToken
        hpsi kind step site l r gl gr
    AgeStepGood kind k completed out.left out.done ∧
      AgeStepGood kind k completed out.right out.done := by
  let lv0 := ageLiveValue kind l
  let rv0 := ageLiveValue kind r
  let gl0 := ageLiveShadow kind l gl
  let gr0 := ageLiveShadow kind r gr
  have hgl0 :
      AgeOpt kind k completed gl0 := by
    exact
      ageLiveShadow_age
        kind k completed l gl hgl
  have hgr0 :
      AgeOpt kind k completed gr0 := by
    exact
      ageLiveShadow_age
        kind k completed r gr hgr

  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      ageBirthGhost
        hpsi kind step site l.id
    let lv1 : Option (TokenData psi) :=
      if hb then some birth.value else lv0
    let gl1 : Option (GhostToken n psi) :=
      if hb then some birth else gl0

    have hgl1 :
        AgeOpt kind k completed gl1 := by
      by_cases hbirth : hb
      · simp only [gl1, if_pos hbirth]
        exact
          ageBirth_age
            hpsi kind k completed step site l.id
      · simpa [gl1, hbirth] using hgl0

    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 : Option (TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (GhostToken n psi) :=
      if collide then none else gl1

    have hgl2 :
        AgeOpt kind k completed gl2 := by
      by_cases hcol : collide
      · simp only [gl2, if_pos hcol]
        exact ageOpt_none kind k completed
      · simpa [gl2, hcol] using hgl1

    have hfinish :=
      ageFinish_status
        hpsi kind k completed l r
        lv2 rv0 gl2 gr0 hgl2 hgr0

    simp only
      [ageGhostMoveToken,
        if_pos hlast]
    exact hfinish
  · simp only
      [ageGhostMoveToken,
        if_neg hlast]
    exact
      ⟨ageStep_of_age
          kind k completed gl0 [] hgl0,
        ageStep_of_age
          kind k completed gr0 [] hgr0⟩

private theorem ageSelectedPair_status
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (completed : List (LineageMeta n))
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hleft :
      AgeOpt kind k completed
        (ghostTokenAt kind G e))
    (hright :
      AgeOpt kind k completed
        (ghostTokenAt kind G
          (ring.rightNeighbor e))) :
    let out :=
      ageSelectedPair
        hpsi ring step G e kind
    AgeStepGood kind k completed out.left out.done ∧
      AgeStepGood kind k completed out.right out.done := by
  unfold ageSelectedPair
  cases kind with
  | black =>
      dsimp only
      exact
        ageGhostMove_status
          hpsi .black k completed step e
          (ageTokenPrelude hpsi
            (G.phys e)
            (G.phys
              (ring.rightNeighbor e))).1
          (ageTokenPrelude hpsi
            (G.phys e)
            (G.phys
              (ring.rightNeighbor e))).2
          (G.black e)
          (G.black (ring.rightNeighbor e))
          hleft hright
  | white =>
      dsimp only
      let pre :=
        ageTokenPrelude hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))
      let qb :=
        moveToken hpsi .black pre.1 pre.2
      exact
        ageGhostMove_status
          hpsi .white k completed step e
          qb.1 qb.2
          (G.white e)
          (G.white (ring.rightNeighbor e))
          hleft hright

private theorem ageOld_mem_completed_step
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (m : LineageMeta n)
    (hm : m ∈ G.completed) :
    m ∈ (ghostStep hpsi ring step G e).completed := by
  simp only [ghostStep, List.mem_append]
  exact .inl (.inl hm)

private theorem ageSelectedDone_mem_completed
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
        (ageSelectedPair
          hpsi ring step G e kind).done) :
    m ∈
      (ghostStep hpsi ring step G e).completed := by
  rw [← ageGhostStep_eq
    hpsi ring step G e]
  rw [ageGhostStep_completed
    hpsi ring step G e]
  simp only [List.mem_append]
  cases kind with
  | black =>
      exact .inl (.inr hm)
  | white =>
      exact .inr hm

private def AgeHistory
    {n psi kappa : Nat}
    (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (kind : TokenKind) (i : Fin n)
      (z : GhostToken n psi),
    ghostTokenAt kind G i = some z →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi ∨
      ∃ m : LineageMeta n,
        m ∈ G.completed ∧
          m.id = z.lmeta.id

private theorem ageHistory_step
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hhist : AgeHistory k G) :
    AgeHistory k
      (ghostStep hpsi ring step G e) := by
  intro kind i z howner hfresh
  have hleft :
      AgeOpt kind k G.completed
        (ghostTokenAt kind G e) := by
    intro z0 hz0 hfresh0
    exact hhist kind e z0 hz0 hfresh0
  have hright :
      AgeOpt kind k G.completed
        (ghostTokenAt kind G
          (ring.rightNeighbor e)) := by
    intro z0 hz0 hfresh0
    exact
      hhist kind (ring.rightNeighbor e)
        z0 hz0 hfresh0
  have hpair :=
    ageSelectedPair_status
      hpsi ring k G.completed step G e kind
      hleft hright

  by_cases hie : i = e
  · subst i
    have hlocal :
        (ageSelectedPair
          hpsi ring step G e kind).left =
          some z := by
      rw [ageSelectedPair_eq_export]
      exact
        (ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind).symm.trans
            howner
    rcases hpair.1 z hlocal hfresh with
      hyoung | hold | hnew
    · exact .inl hyoung
    · rcases hold with ⟨m, hm, hid⟩
      exact
        .inr
          ⟨m,
            ageOld_mem_completed_step
              hpsi ring step G e m hm,
            hid⟩
    · rcases hnew with ⟨m, hm, hid⟩
      exact
        .inr
          ⟨m,
            ageSelectedDone_mem_completed
              hpsi ring step G e kind m hm,
            hid⟩

  · by_cases hir :
        i = ring.rightNeighbor e
    · subst i
      have hne :
          ring.rightNeighbor e ≠ e := hie
      have hlocal :
          (ageSelectedPair
            hpsi ring step G e kind).right =
            some z := by
        rw [ageSelectedPair_eq_export]
        exact
          (ghostTokenAt_ghostStep_responder_of_ne
            hpsi ring step G e kind hne).symm.trans
              howner
      rcases hpair.2 z hlocal hfresh with
        hyoung | hold | hnew
      · exact .inl hyoung
      · rcases hold with ⟨m, hm, hid⟩
        exact
          .inr
            ⟨m,
              ageOld_mem_completed_step
                hpsi ring step G e m hm,
              hid⟩
      · rcases hnew with ⟨m, hm, hid⟩
        exact
          .inr
            ⟨m,
              ageSelectedDone_mem_completed
                hpsi ring step G e kind m hm,
              hid⟩

    · have howner0 :
          ghostTokenAt kind G i = some z := by
        exact
          (ghostTokenAt_ghostStep_frame
            hpsi ring step G e i kind
            hie hir).symm.trans howner
      rcases
          hhist kind i z howner0 hfresh with
        hyoung | hold
      · exact .inl hyoung
      · rcases hold with ⟨m, hm, hid⟩
        exact
          .inr
            ⟨m,
              ageOld_mem_completed_step
                hpsi ring step G e m hm,
              hid⟩

private theorem ageHistory_initial
    {n psi kappa : Nat}
    (k : Fin n)
    (C0 : Config n psi kappa) :
    AgeHistory k
      (initialGhost C0) := by
  intro kind i z howner hfresh
  rcases hfresh with ⟨t, hborn, _hsite⟩
  have hbefore :=
    (ghostIdsUnique_initial C0).2
      kind i z kind t howner hborn
  have hfalse : False := by
    omega
  exact hfalse.elim

private theorem ageHistory_run_from
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n) :
    ∀ (t : Nat)
      (G : GhostConfig n psi kappa)
      (pre : DetSchedule n),
      AgeHistory k G →
      AgeHistory k
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
          (ageHistory_step
            hpsi ring k t G e hhist)

theorem lemma16FreshNoPriorTerminalAgeCanon_proved :
    Lemma16FreshNoPriorTerminalAgeCanon := by
  unfold Lemma16FreshNoPriorTerminalAgeCanon
  intro n psi kappa hpsi ring C0 pre k kind
  unfold Lemma16FreshNoPriorTerminalAge
  intro i z howner hfresh hnoPrior
  have hhist :
      AgeHistory k
        (ghostRun hpsi ring 0
          (initialGhost C0) pre) :=
    ageHistory_run_from
      hpsi ring k 0 (initialGhost C0) pre
      (ageHistory_initial k C0)
  rcases hhist kind i z howner hfresh with
    hyoung | hold
  · exact hyoung
  · rcases hold with ⟨m, hm, hid⟩
    have hne := hnoPrior m hm
    exact False.elim (hne hid)

#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoPriorTerminalAgeCanon_proved

end PPL.Convergence.ReachCPB

