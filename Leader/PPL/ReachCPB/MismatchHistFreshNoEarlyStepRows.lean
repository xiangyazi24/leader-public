import Leader.PPL.ReachCPB.MismatchHistFreshNoEarlyStep
import Leader.PPL.TokenCompletion.GhostStepMirror
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
Proof-local mirror of the ghost step (copied definition-for-definition from
ReachCPBMismatchHistFreshDoneProvenance, renamed with the `nes` prefix), then
the three local rows of the L16 no-early one-step history row.
-/

private def nesBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def nesMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def nesLocalValid
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
    Decidable (nesLocalValid kind q t) := by
  unfold nesLocalValid
  infer_instance

private def nesTokenPrelude
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

private def nesLiveShadow
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
          if z.value = t ∧ nesLocalValid kind q t then
            some z
          else
            none

private def nesLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if nesLocalValid kind q t then
        some t
      else
        none

private def nesBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      nesMkToken
        (offsetPsiCode psi hpsi)
        (nesBitToFin (!idBit))
        (nesBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def nesBumpTo
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
        if nesLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def nesNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    nesMkToken
      (offsetPsiCode psi hpsi)
      (nesBitToFin (!sourceBit))
      (nesBitToFin sourceBit)
  else
    nesMkToken
      (offsetPsiCode psi hpsi)
      (nesBitToFin sourceBit)
      (0 : Fin 2)

private def nesFinishMove
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
          nesMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := nesBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          nesMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := nesBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                nesNegTurnNext hpsi l.id tr
              let b := nesBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid psi (by omega) (tokenCode tr)
              let next :=
                nesMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := nesBumpTo kind l next gr0
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
              nesNegTurnNext hpsi l.id tr
            let b := nesBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid psi (by omega) (tokenCode tr)
            let next :=
              nesMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := nesBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def nesGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := nesLiveValue kind l
  let rv0 := nesLiveValue kind r
  let gl0 := nesLiveShadow kind l gl
  let gr0 := nesLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (nesBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (nesBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    nesFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def nesSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := nesTokenPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2

private def nesSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    nesSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  nesGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private def nesSetTwo
    {n : Nat} {A : Type}
    (f : Fin n → A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n → A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def nesGhostStep
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let pre :=
    nesTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  let gb :=
    nesGhostMoveToken hpsi .black step e
      pre.1 pre.2
      (G.black e) (G.black rsite)
  let qb :=
    moveToken hpsi .black pre.1 pre.2
  let gw :=
    nesGhostMoveToken hpsi .white step e
      qb.1 qb.2
      (G.white e) (G.white rsite)
  { phys :=
      PopulationProtocol.step
        (protocol psi kappa) ring G.phys e
    black :=
      nesSetTwo
        G.black e rsite gb.left gb.right
    white :=
      nesSetTwo
        G.white e rsite gw.left gw.right
    completed :=
      G.completed ++ gb.done ++ gw.done }

private theorem nesSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    nesSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

private theorem nesGhostStep_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    nesGhostStep hpsi ring step G e =
      ghostStep hpsi ring step G e := by
  unfold nesGhostStep ghostStep
  unfoldGhostStepCore
  rfl

private theorem nesGhostStep_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (nesGhostStep
      hpsi ring step G e).completed =
      G.completed ++
        (nesSelectedPair
          hpsi ring step G e .black).done ++
        (nesSelectedPair
          hpsi ring step G e .white).done := by
  rfl

/-! ## Done provenance through the mirrored row -/

private theorem nesTrajectoryMoves_gt_one
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

private theorem nesLiveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      nesLiveShadow kind q g = some z) :
    g = some z := by
  cases hg : g with
  | none =>
      simp [nesLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [nesLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                nesLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [nesLiveShadow, hg, ht, hv]
                using hz
            subst z
            rfl
          · simp
              [nesLiveShadow, hg, ht, hv]
              at hz

private theorem nesBump_done_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈
        (nesBumpTo
          kind qDest newValue g).done) :
    ∃ z : GhostToken n psi,
      g = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi := by
  cases hg : g with
  | none =>
      simp [nesBumpTo, hg] at hm
  | some z =>
      by_cases hdone :
          (ghostStepLineageAdvance z.lmeta).moves =
            tokenTrajectoryMoves psi
      · have hmm :
            m = ghostStepLineageAdvance z.lmeta := by
          simpa [nesBumpTo, hg, hdone]
            using hm
        exact ⟨z, rfl, hmm, hdone⟩
      · simp [nesBumpTo, hg, hdone] at hm


/-! ## Lineage bookkeeping for the mirrored row -/

/-- `z` is the same lineage as an old source token, with no fewer moves. -/
private def NesFrom
    {n psi : Nat}
    (src : Option (GhostToken n psi))
    (z : GhostToken n psi) : Prop :=
  ∃ z0 : GhostToken n psi,
    src = some z0 ∧
    z.lmeta.id = z0.lmeta.id ∧
    z.lmeta.birthSite = z0.lmeta.birthSite ∧
    z0.lmeta.moves ≤ z.lmeta.moves

/-- `z` carries the ID of the birth made by this interaction. -/
private def NesBirth
    {n psi : Nat}
    (kind : TokenKind)
    (step : Nat)
    (z : GhostToken n psi) : Prop :=
  z.lmeta.id = .born kind step

private theorem nesFrom_self
    {n psi : Nat}
    (src : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (h : src = some z) :
    NesFrom src z :=
  ⟨z, h, rfl, rfl, Nat.le_refl _⟩

private theorem nesFrom_adv
    {n psi : Nat}
    (src : Option (GhostToken n psi))
    (z z0 : GhostToken n psi)
    (h : src = some z0)
    (hadv : z.lmeta = ghostStepLineageAdvance z0.lmeta) :
    NesFrom src z := by
  refine ⟨z0, h, ?_, ?_, ?_⟩
  · rw [hadv]
    rfl
  · rw [hadv]
    rfl
  · rw [hadv]
    show z0.lmeta.moves ≤ z0.lmeta.moves + 1
    omega

private theorem nesBump_live
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      (nesBumpTo kind qDest newValue g).live = some z) :
    ∃ z0 : GhostToken n psi,
      g = some z0 ∧
      z.lmeta = ghostStepLineageAdvance z0.lmeta := by
  cases hg : g with
  | none =>
      rw [hg] at hz
      simp [nesBumpTo] at hz
  | some z0 =>
      rw [hg] at hz
      by_cases hv : nesLocalValid kind qDest newValue
      · have hzz :
            ({ value := newValue
               lmeta := ghostStepLineageAdvance z0.lmeta } :
              GhostToken n psi) = z := by
          simpa [nesBumpTo, hv] using hz
        subst z
        exact ⟨z0, rfl, rfl⟩
      · simp [nesBumpTo, hv] at hz

private theorem nesBump_live_of_done
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈ (nesBumpTo kind qDest newValue g).done)
    (z : GhostToken n psi)
    (hz :
      (nesBumpTo kind qDest newValue g).live = some z) :
    z.lmeta = m := by
  rcases nesBump_done_source kind qDest newValue g m hm with
    ⟨z0, hg0, hmadv, _hterm⟩
  rcases nesBump_live kind qDest newValue g z hz with
    ⟨z1, hg1, hzadv⟩
  rw [hg0] at hg1
  have h01 : z0 = z1 := Option.some.inj hg1
  subst z1
  rw [hzadv, hmadv]

/-! ## The three shapes of the finishing move -/

private theorem nesFinish_shape
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) :
    (∃ nx : TokenData psi,
      nesFinishMove hpsi kind l r lv2 rv0 gl2 gr0 =
        ⟨none,
          (nesBumpTo kind r nx gl2).live,
          (nesBumpTo kind r nx gl2).done⟩) ∨
    (∃ nx : TokenData psi,
      nesFinishMove hpsi kind l r lv2 rv0 gl2 gr0 =
        ⟨(nesBumpTo kind l nx gr0).live,
          none,
          (nesBumpTo kind l nx gr0).done⟩) ∨
    nesFinishMove hpsi kind l r lv2 rv0 gl2 gr0 =
      ⟨gl2, gr0, []⟩ := by
  cases hlv : lv2 with
  | none =>
      cases hrv : rv0 with
      | none =>
          right
          right
          simp only [nesFinishMove]
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · right
            left
            simp only [nesFinishMove, dif_pos hm1]
            exact ⟨_, rfl⟩
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · right
              left
              simp only
                [nesFinishMove, dif_neg hm1, dif_pos hm2]
              exact ⟨_, rfl⟩
            · right
              right
              simp only
                [nesFinishMove, dif_neg hm1, dif_neg hm2]
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · left
        simp only [nesFinishMove, dif_pos h1]
        exact ⟨_, rfl⟩
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · left
          simp only
            [nesFinishMove, dif_neg h1, dif_pos h2]
          exact ⟨_, rfl⟩
        · cases hrv : rv0 with
          | none =>
              right
              right
              simp only
                [nesFinishMove, dif_neg h1, dif_neg h2]
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · right
                left
                simp only
                  [nesFinishMove, dif_neg h1, dif_neg h2,
                    dif_pos hm1]
                exact ⟨_, rfl⟩
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · right
                  left
                  simp only
                    [nesFinishMove, dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2]
                  exact ⟨_, rfl⟩
                · right
                  right
                  simp only
                    [nesFinishMove, dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]

/-- Everything the rows need about one finishing move. -/
private def NesFinishGood
    {n psi : Nat}
    (gl2 gr0 : Option (GhostToken n psi))
    (res : GhostMoveResult n psi) : Prop :=
  (∀ z, res.left = some z → NesFrom gl2 z ∨ NesFrom gr0 z) ∧
  (∀ z, res.right = some z → NesFrom gl2 z ∨ NesFrom gr0 z) ∧
  (∀ m, m ∈ res.done →
    m.moves = tokenTrajectoryMoves psi ∧
    (∀ z, res.left = some z → z.lmeta = m) ∧
    (∀ z, res.right = some z → z.lmeta = m) ∧
    ∃ z0 : GhostToken n psi,
      (gl2 = some z0 ∨ gr0 = some z0) ∧
      m = ghostStepLineageAdvance z0.lmeta)

private theorem nesFinish_good
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) :
    NesFinishGood gl2 gr0
      (nesFinishMove hpsi kind l r lv2 rv0 gl2 gr0) := by
  rcases nesFinish_shape hpsi kind l r lv2 rv0 gl2 gr0 with
    ⟨nx, h⟩ | ⟨nx, h⟩ | h
  · rw [h]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact absurd hz (by simp)
    · intro z hz
      rcases nesBump_live kind r nx gl2 z hz with ⟨z0, hg, hadv⟩
      exact .inl (nesFrom_adv gl2 z z0 hg hadv)
    · intro m hm
      rcases nesBump_done_source kind r nx gl2 m hm with
        ⟨z0, hg, hmadv, hterm⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hmadv]
        exact hterm
      · intro z hz
        exact absurd hz (by simp)
      · intro z hz
        exact nesBump_live_of_done kind r nx gl2 m hm z hz
      · exact ⟨z0, .inl hg, hmadv⟩
  · rw [h]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases nesBump_live kind l nx gr0 z hz with ⟨z0, hg, hadv⟩
      exact .inr (nesFrom_adv gr0 z z0 hg hadv)
    · intro z hz
      exact absurd hz (by simp)
    · intro m hm
      rcases nesBump_done_source kind l nx gr0 m hm with
        ⟨z0, hg, hmadv, hterm⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hmadv]
        exact hterm
      · intro z hz
        exact nesBump_live_of_done kind l nx gr0 m hm z hz
      · intro z hz
        exact absurd hz (by simp)
      · exact ⟨z0, .inr hg, hmadv⟩
  · rw [h]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact .inl (nesFrom_self gl2 z hz)
    · intro z hz
      exact .inr (nesFrom_self gr0 z hz)
    · intro m hm
      exact absurd hm (by simp)

/-! ## One selected-colour move -/

private def NesMoveGood
    {n psi : Nat}
    (kind : TokenKind)
    (step : Nat)
    (gl gr : Option (GhostToken n psi))
    (res : GhostMoveResult n psi) : Prop :=
  (∀ z, res.left = some z →
    NesBirth kind step z ∨ NesFrom gl z ∨ NesFrom gr z) ∧
  (∀ z, res.right = some z →
    NesBirth kind step z ∨ NesFrom gl z ∨ NesFrom gr z) ∧
  (∀ m, m ∈ res.done →
    m.moves = tokenTrajectoryMoves psi ∧
    (∀ z, res.left = some z → z.lmeta = m) ∧
    (∀ z, res.right = some z → z.lmeta = m) ∧
    ∃ z0 : GhostToken n psi,
      (gl = some z0 ∨ gr = some z0) ∧
      m = ghostStepLineageAdvance z0.lmeta)

private theorem nesGhostMove_good
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    NesMoveGood kind step gl gr
      (nesGhostMoveToken hpsi kind step site l r gl gr) := by
  let lv0 := nesLiveValue kind l
  let rv0 := nesLiveValue kind r
  let gl0 := nesLiveShadow kind l gl
  let gr0 := nesLiveShadow kind r gr
  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      nesBirthGhost
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
    have hres :
        nesGhostMoveToken hpsi kind step site l r gl gr =
          nesFinishMove
            hpsi kind l r
            lv2 rv0 gl2 gr0 := by
      simp only [nesGhostMoveToken, if_pos hlast]
      rfl
    -- the left source gl2 is either the birth or the shadow of gl
    have hgl2 :
        ∀ z0 : GhostToken n psi,
          gl2 = some z0 →
          z0 = birth ∨ gl = some z0 := by
      intro z0 hz0
      by_cases hcol : collide
      · simp [gl2, hcol] at hz0
      · have hgl1 : gl1 = some z0 := by
          simpa [gl2, hcol] using hz0
        by_cases hbirth : hb
        · have hz : birth = z0 := by
            simpa [gl1, hbirth] using hgl1
          exact .inl hz.symm
        · have hgl0 : gl0 = some z0 := by
            simpa [gl1, hbirth] using hgl1
          exact .inr
            (nesLiveShadow_source kind l gl z0 hgl0)
    have hsrc :
        ∀ z : GhostToken n psi,
          NesFrom gl2 z ∨ NesFrom gr0 z →
          NesBirth kind step z ∨ NesFrom gl z ∨ NesFrom gr z := by
      intro z hz
      rcases hz with ⟨z0, hz0, hid, hsite, hmv⟩ | ⟨z0, hz0, hid, hsite, hmv⟩
      · rcases hgl2 z0 hz0 with hbz | hglz
        · left
          subst z0
          exact hid
        · exact .inr (.inl ⟨z0, hglz, hid, hsite, hmv⟩)
      · exact .inr (.inr
          ⟨z0, nesLiveShadow_source kind r gr z0 hz0,
            hid, hsite, hmv⟩)
    have hfin :=
      nesFinish_good hpsi kind l r lv2 rv0 gl2 gr0
    rw [hres]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact hsrc z (hfin.1 z hz)
    · intro z hz
      exact hsrc z (hfin.2.1 z hz)
    · intro m hm
      rcases hfin.2.2 m hm with ⟨hterm, hL, hR, z0, hz0, hmadv⟩
      refine ⟨hterm, hL, hR, ?_⟩
      rcases hz0 with hz0 | hz0
      · rcases hgl2 z0 hz0 with hbz | hglz
        · exfalso
          subst z0
          have h1 : m.moves = 1 := by
            rw [hmadv]
            rfl
          have hgt := nesTrajectoryMoves_gt_one psi hpsi
          omega
        · exact ⟨z0, .inl hglz, hmadv⟩
      · exact
          ⟨z0,
            .inr (nesLiveShadow_source kind r gr z0 hz0),
            hmadv⟩
  · have hres :
        nesGhostMoveToken hpsi kind step site l r gl gr =
          ⟨gl0, gr0, []⟩ := by
      simp only [nesGhostMoveToken, if_neg hlast]
      rfl
    rw [hres]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact .inr (.inl
        (nesFrom_self gl z
          (nesLiveShadow_source kind l gl z hz)))
    · intro z hz
      exact .inr (.inr
        (nesFrom_self gr z
          (nesLiveShadow_source kind r gr z hz)))
    · intro m hm
      exact absurd hm (by simp)

private theorem nesSelectedPair_good
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    NesMoveGood kind step
      (ghostTokenAt kind G e)
      (ghostTokenAt kind G (ring.rightNeighbor e))
      (nesSelectedPair hpsi ring step G e kind) := by
  unfold nesSelectedPair
  exact nesGhostMove_good hpsi kind step e _ _ _ _

/-! ## Post-step owners and completions -/

private theorem nesGhostStep_owner_eq
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind (nesGhostStep hpsi ring step G e) i =
      nesSetTwo (ghostTokenAt kind G) e (ring.rightNeighbor e)
        (nesSelectedPair hpsi ring step G e kind).left
        (nesSelectedPair hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl

private theorem nesGhostStep_owner
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (hz :
      ghostTokenAt kind (nesGhostStep hpsi ring step G e) i =
        some z) :
    (i ≠ e ∧ i ≠ ring.rightNeighbor e ∧
      ghostTokenAt kind G i = some z) ∨
    (nesSelectedPair hpsi ring step G e kind).left = some z ∨
    (nesSelectedPair hpsi ring step G e kind).right = some z := by
  rw [nesGhostStep_owner_eq] at hz
  unfold nesSetTwo at hz
  by_cases hie : i = e
  · rw [if_pos hie] at hz
    exact .inr (.inl hz)
  · rw [if_neg hie] at hz
    by_cases hir : i = ring.rightNeighbor e
    · rw [if_pos hir] at hz
      exact .inr (.inr hz)
    · rw [if_neg hir] at hz
      exact .inl ⟨hie, hir, hz⟩

private theorem nesGhostStep_mem_completed
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (m : LineageMeta n)
    (hm : m ∈ (nesGhostStep hpsi ring step G e).completed) :
    m ∈ G.completed ∨
    ∃ kind : TokenKind,
      m ∈ (nesSelectedPair hpsi ring step G e kind).done := by
  rw [nesGhostStep_completed] at hm
  simp only [List.mem_append] at hm
  rcases hm with (hold | hb) | hw
  · exact .inl hold
  · exact .inr ⟨.black, hb⟩
  · exact .inr ⟨.white, hw⟩

/-! ## Row A: clock preservation -/

theorem lemma16FreshNoEarlyCompletionIdStepClockRow_proved :
    Lemma16FreshNoEarlyCompletionIdStepClockRow := by
  unfold Lemma16FreshNoEarlyCompletionIdStepClockRow
  intro n psi kappa hpsi ring step G e hbefore hclock
  rw [← nesGhostStep_eq hpsi ring step G e]
  refine ⟨?_, ?_⟩
  · unfold GhostIdsBefore
    intro kind i z bornKind s hz hid
    have hsrc :
        ∀ w : Option (GhostToken n psi),
          (∀ z1 : GhostToken n psi, w = some z1 →
            ∃ i1, ghostTokenAt kind G i1 = some z1) →
          NesFrom w z → s < step + 1 := by
      intro w hw hfrom
      rcases hfrom with ⟨z0, hz0, hid0, _, _⟩
      rcases hw z0 hz0 with ⟨i1, hown⟩
      have := hbefore kind i1 z0 bornKind s hown (hid0 ▸ hid)
      omega
    have hgood := nesSelectedPair_good hpsi ring step G e kind
    have hcase :
        ∀ z : GhostToken n psi,
          z.lmeta.id = .born bornKind s →
          (NesBirth kind step z ∨
            NesFrom (ghostTokenAt kind G e) z ∨
            NesFrom (ghostTokenAt kind G (ring.rightNeighbor e)) z) →
          s < step + 1 := by
      intro z hid hc
      rcases hc with hb | hf | hf
      · unfold NesBirth at hb
        rw [hid] at hb
        injection hb with _ hs
        omega
      · rcases hf with ⟨z0, hz0, hid0, _, _⟩
        have := hbefore kind e z0 bornKind s hz0 (hid0 ▸ hid)
        omega
      · rcases hf with ⟨z0, hz0, hid0, _, _⟩
        have :=
          hbefore kind (ring.rightNeighbor e) z0 bornKind s hz0
            (hid0 ▸ hid)
        omega
    clear hsrc
    rcases nesGhostStep_owner hpsi ring step G e kind i z hz with
      ⟨_, _, hold⟩ | hL | hR
    · have := hbefore kind i z bornKind s hold hid
      omega
    · exact hcase z hid (hgood.1 z hL)
    · exact hcase z hid (hgood.2.1 z hR)
  · intro m hm bornKind s hid
    rcases nesGhostStep_mem_completed hpsi ring step G e m hm with
      hold | ⟨kind, hdone⟩
    · have := hclock m hold bornKind s hid
      omega
    · rcases (nesSelectedPair_good hpsi ring step G e kind).2.2 m hdone with
        ⟨_, _, _, z0, hz0, hmadv⟩
      have hid0 : z0.lmeta.id = .born bornKind s := by
        rw [hmadv] at hid
        exact hid
      rcases hz0 with hz0 | hz0
      · have := hbefore kind e z0 bornKind s hz0 hid0
        omega
      · have :=
          hbefore kind (ring.rightNeighbor e) z0 bornKind s hz0 hid0
        omega

/-! ## Row B: separation from the old completed list -/

theorem lemma16FreshNoEarlyCompletionIdStepOldCompletedRow_proved :
    Lemma16FreshNoEarlyCompletionIdStepOldCompletedRow := by
  unfold Lemma16FreshNoEarlyCompletionIdStepOldCompletedRow
  intro n psi kappa hpsi ring step G e hclock hnoearly
  intro k kind i z hz hfresh hyoung m hm hideq
  rw [← nesGhostStep_eq hpsi ring step G e] at hz
  -- an old owner of the same lineage contradicts the pre no-early clause
  have hold :
      ∀ (j : Fin n) (z0 : GhostToken n psi),
        ghostTokenAt kind G j = some z0 →
        z.lmeta.id = z0.lmeta.id →
        z.lmeta.birthSite = z0.lmeta.birthSite →
        z0.lmeta.moves ≤ z.lmeta.moves →
        False := by
    intro j z0 hz0 hid hsite hmv
    have hfresh0 : FreshAt kind k z0.lmeta := by
      rcases hfresh with ⟨t, ht, hs⟩
      exact ⟨t, hid ▸ ht, hsite ▸ hs⟩
    have hyoung0 :
        z0.lmeta.moves < tokenTrajectoryMoves psi := by
      omega
    have hpre := hnoearly k kind
    unfold Lemma16FreshNoEarlyCompletionId at hpre
    have hno := hpre j z0 hz0 hfresh0 hyoung0
    unfold Lemma16NoPriorCompletionId at hno
    exact hno m hm (hideq.trans hid)
  have hcase :
      (NesBirth kind step z ∨
        NesFrom (ghostTokenAt kind G e) z ∨
        NesFrom (ghostTokenAt kind G (ring.rightNeighbor e)) z) →
      False := by
    intro hc
    rcases hc with hb | hf | hf
    · unfold NesBirth at hb
      have hmid : m.id = .born kind step := hideq.trans hb
      have := hclock m hm kind step hmid
      omega
    · rcases hf with ⟨z0, hz0, hid, hsite, hmv⟩
      exact hold e z0 hz0 hid hsite hmv
    · rcases hf with ⟨z0, hz0, hid, hsite, hmv⟩
      exact hold (ring.rightNeighbor e) z0 hz0 hid hsite hmv
  have hgood := nesSelectedPair_good hpsi ring step G e kind
  rcases nesGhostStep_owner hpsi ring step G e kind i z hz with
    ⟨_, _, hown⟩ | hL | hR
  · exact hold i z hown rfl rfl (Nat.le_refl _)
  · exact hcase (hgood.1 z hL)
  · exact hcase (hgood.2.1 z hR)

/-! ## Row C: separation from newly appended completions -/

theorem lemma16FreshNoEarlyCompletionIdStepNewCompletedRow_proved :
    Lemma16FreshNoEarlyCompletionIdStepNewCompletedRow := by
  unfold Lemma16FreshNoEarlyCompletionIdStepNewCompletedRow
  intro n psi kappa hpsi ring step G e huniq hcoh _hbefore
  intro k kind i z hz hfresh hyoung m hm hnew hideq
  rw [← nesGhostStep_eq hpsi ring step G e] at hz hm
  rcases nesGhostStep_mem_completed hpsi ring step G e m hm with
    hold | ⟨kind', hdone⟩
  · exact hnew hold
  rcases (nesSelectedPair_good hpsi ring step G e kind').2.2 m hdone with
    ⟨hterm, hL', hR', z1, hz1, hmadv⟩
  rcases hfresh with ⟨t, hzid, _hzsite⟩
  have hid1 : z1.lmeta.id = .born kind t := by
    have h : m.id = z1.lmeta.id := by
      rw [hmadv]
      rfl
    rw [← h, hideq, hzid]
  -- the done source sits at an endpoint of the interaction
  have hsrc :
      ∃ i1 : Fin n,
        (i1 = e ∨ i1 = ring.rightNeighbor e) ∧
        ghostTokenAt kind' G i1 = some z1 := by
    rcases hz1 with hz1 | hz1
    · exact ⟨e, .inl rfl, hz1⟩
    · exact ⟨ring.rightNeighbor e, .inr rfl, hz1⟩
  rcases hsrc with ⟨i1, hi1, hown1⟩
  have hkinds := hcoh kind' kind i1 z1 t hown1 hid1
  have hkk : kind' = kind := hkinds.1
  subst hkk
  rcases nesGhostStep_owner hpsi ring step G e kind' i z hz with
    ⟨hie, hir, hown⟩ | hL | hR
  · have hsame : z.lmeta.id = z1.lmeta.id := by
      rw [hzid, hid1]
    have hij := huniq kind' i i1 z z1 hown hown1 hsame
    rcases hi1 with h | h
    · exact hie (hij.trans h)
    · exact hir (hij.trans h)
  · have := hL' z hL
    rw [this] at hyoung
    omega
  · have := hR' z hR
    rw [this] at hyoung
    omega

/-! ## Assembled one-step history row -/

theorem lemma16FreshNoEarlyCompletionIdStepHistoryRow_proved :
    Lemma16FreshNoEarlyCompletionIdStepHistoryRow :=
  lemma16FreshNoEarlyCompletionIdStepHistoryRow_proved_of_localRows
    lemma16FreshNoEarlyCompletionIdStepClockRow_proved
    lemma16FreshNoEarlyCompletionIdStepOldCompletedRow_proved
    lemma16FreshNoEarlyCompletionIdStepNewCompletedRow_proved

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdStepClockRow_proved
#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdStepOldCompletedRow_proved
#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdStepNewCompletedRow_proved
#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdStepHistoryRow_proved
