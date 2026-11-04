import Leader.PPL.ReachCPB.MismatchHistFreshTerminalDetectBirth
import Leader.PPL.ReachCPB.MismatchHistFreshTerminalSourceClass
import Leader.PPL.ReachCPB.StepDetectPersistence
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
Selected-pass birth view (the literal Algorithm-3 line-20 leaf).

The done premise, read through a mirror of the selected-colour ghost pass,
yields: the old owner bumped to done is either the left owner (then, by
Option injectivity, it is z) or a right owner with the same lineage ID as z
(excluded by GhostIdsUnique, since the right neighbour differs from e for
n >= 3).  In the left case the ghost pass also certifies that both last
flags of the selected input are false, the initiator's selected token is the
locally valid value z.value, and the responder has no locally valid selected
token.  A mirror of MoveToken (proved definitionally equal) then takes the
c = 1 branch; DistReadyCapped makes DetermineMode leave the responder in
Detect with its ID unchanged, so the stated bit mismatch fires line 20.
For white, the preceding black pass keeps the responder mode, and either
keeps its ID or already produced the born4 view.

The private helper block below is a renamed copy of the done-source helpers
in ReachCPBMismatchHistFreshTerminalSourceClass.lean.
-/

private def spbProvBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def spbProvMkToken
    {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def spbProvLocalValid
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

private instance instDecidableSpbProvLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (spbProvLocalValid kind q t) := by
  unfold spbProvLocalValid
  infer_instance

private def spbProvTokenPrelude
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

private def spbProvLiveShadow
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
          if z.value = t ∧ spbProvLocalValid kind q t then
            some z
          else
            none

private def spbProvLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if spbProvLocalValid kind q t then
        some t
      else
        none

private def spbProvBirthGhost
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      spbProvMkToken
        (offsetPsiCode psi hpsi)
        (spbProvBitToFin (!idBit))
        (spbProvBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def spbProvBumpTo
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
        if spbProvLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def spbProvNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    spbProvMkToken
      (offsetPsiCode psi hpsi)
      (spbProvBitToFin (!sourceBit))
      (spbProvBitToFin sourceBit)
  else
    spbProvMkToken
      (offsetPsiCode psi hpsi)
      (spbProvBitToFin sourceBit)
      (0 : Fin 2)

private def spbProvFinishMove
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
          spbProvMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b := spbProvBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid psi (by omega) (tokenCode t)
        let next :=
          spbProvMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b := spbProvBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some tr =>
            let cr := decodeOffset psi (tokenCode tr)
            if hm1 : cr = -1 then
              let next :=
                spbProvNegTurnNext hpsi l.id tr
              let b := spbProvBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : cr ≤ -2 then
              have hc : ValidOffset psi cr :=
                decodeOffset_valid psi (by omega) (tokenCode tr)
              let next :=
                spbProvMkToken
                  (encodeOffset psi (cr + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  tr.1.2 tr.2
              let b := spbProvBumpTo kind l next gr0
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
              spbProvNegTurnNext hpsi l.id tr
            let b := spbProvBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : cr ≤ -2 then
            have hc : ValidOffset psi cr :=
              decodeOffset_valid psi (by omega) (tokenCode tr)
            let next :=
              spbProvMkToken
                (encodeOffset psi (cr + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                tr.1.2 tr.2
            let b := spbProvBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def spbProvGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := spbProvLiveValue kind l
  let rv0 := spbProvLiveValue kind r
  let gl0 := spbProvLiveShadow kind l gl
  let gr0 := spbProvLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (spbProvBirthGhost hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (spbProvBirthGhost hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    spbProvFinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def spbProvSelectedInput
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let pre := spbProvTokenPrelude hpsi l r
  match kind with
  | .black =>
      pre
  | .white =>
      moveToken hpsi .black pre.1 pre.2

private def spbProvSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let p :=
    spbProvSelectedInput hpsi kind
      (G.phys e)
      (G.phys (ring.rightNeighbor e))
  spbProvGhostMoveToken
    hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e)
    (ghostTokenAt kind G
      (ring.rightNeighbor e))

private theorem spbProvSelectedPair_eq_export
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    spbProvSelectedPair
        hpsi ring step G e kind =
      ghostStepSelectedPair
        hpsi ring step G e kind := by
  cases kind <;> rfl

private theorem spbProvTrajectoryMoves_gt_one
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

private theorem spbProvLiveShadow_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      spbProvLiveShadow kind q g = some z) :
    g = some z := by
  cases hg : g with
  | none =>
      simp [spbProvLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [spbProvLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                spbProvLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [spbProvLiveShadow, hg, ht, hv]
                using hz
            subst z
            rfl
          · simp
              [spbProvLiveShadow, hg, ht, hv]
              at hz

private theorem spbProvLiveShadow_value
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (z : GhostToken n psi)
    (hz :
      spbProvLiveShadow kind q g = some z) :
    spbProvLiveValue kind q = some z.value := by
  cases hg : g with
  | none =>
      simp [spbProvLiveShadow, hg] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none =>
          simp [spbProvLiveShadow, hg, ht] at hz
      | some t =>
          by_cases hv :
              z0.value = t ∧
                spbProvLocalValid kind q t
          · have hzz : z0 = z := by
              simpa
                [spbProvLiveShadow, hg, ht, hv]
                using hz
            subst z
            rcases hv with ⟨hvalue, hvalid⟩
            simp
              [spbProvLiveValue, ht, hvalid, hvalue]
          · simp
              [spbProvLiveShadow, hg, ht, hv]
              at hz

private theorem spbBump_done_source
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈
        (spbProvBumpTo
          kind qDest newValue g).done) :
    ∃ z : GhostToken n psi,
      g = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      (ghostStepLineageAdvance z.lmeta).moves =
        tokenTrajectoryMoves psi := by
  cases hg : g with
  | none =>
      simp [spbProvBumpTo, hg] at hm
  | some z =>
      by_cases hdone :
          (ghostStepLineageAdvance z.lmeta).moves =
            tokenTrajectoryMoves psi
      · have hmm :
            m = ghostStepLineageAdvance z.lmeta := by
          simpa [spbProvBumpTo, hg, hdone]
            using hm
        exact ⟨z, rfl, hmm, hdone⟩
      · simp [spbProvBumpTo, hg, hdone] at hm

private theorem spbProvFinish_done_source_class
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (m : LineageMeta n)
    (hm :
      m ∈
        (spbProvFinishMove
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
          simp [spbProvFinishMove, hlv, hrv] at hm
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [spbProvFinishMove, hlv, hrv,
                dif_pos hm1] at hm
            let next :=
              spbProvNegTurnNext hpsi l.id tr
            rcases
                spbBump_done_source
                  kind l next gr0 m hm with
              ⟨z, hgr, hmadv, hterm⟩
            exact
              .inr
                ⟨tr, z, rfl, hgr, hmadv,
                  hterm, by omega⟩
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) ≤ -2
            · simp only
                [spbProvFinishMove, hlv, hrv,
                  dif_neg hm1, dif_pos hm2] at hm
              have hc :
                  ValidOffset psi
                    (decodeOffset psi
                      (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                spbProvMkToken
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
                  spbBump_done_source
                    kind l next gr0 m hm with
                ⟨z, hgr, hmadv, hterm⟩
              exact
                .inr
                  ⟨tr, z, rfl, hgr, hmadv,
                    hterm, by omega⟩
            · simp
                [spbProvFinishMove, hlv, hrv,
                  hm1, hm2] at hm
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [spbProvFinishMove, hlv, dif_pos h1] at hm
        let next :=
          spbProvMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        exact
          .inl
            (spbBump_done_source
              kind r next gl2 m hm)
      · by_cases h2 :
          2 ≤ decodeOffset psi (tokenCode t)
        · simp only
            [spbProvFinishMove, hlv,
              dif_neg h1, dif_pos h2] at hm
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            spbProvMkToken
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
              (spbBump_done_source
                kind r next gl2 m hm)
        · cases hrv : rv0 with
          | none =>
              simp
                [spbProvFinishMove, hlv, hrv,
                  h1, h2] at hm
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [spbProvFinishMove, hlv, hrv,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1] at hm
                let next :=
                  spbProvNegTurnNext hpsi l.id tr
                rcases
                    spbBump_done_source
                      kind l next gr0 m hm with
                  ⟨z, hgr, hmadv, hterm⟩
                exact
                  .inr
                    ⟨tr, z, rfl, hgr, hmadv,
                      hterm, by omega⟩
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) ≤ -2
                · simp only
                    [spbProvFinishMove, hlv, hrv,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2] at hm
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    spbProvMkToken
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
                      spbBump_done_source
                        kind l next gr0 m hm with
                    ⟨z, hgr, hmadv, hterm⟩
                  exact
                    .inr
                      ⟨tr, z, rfl, hgr, hmadv,
                        hterm, by omega⟩
                · simp
                    [spbProvFinishMove, hlv, hrv,
                      h1, h2, hm1, hm2] at hm


/-! ## Left-done source with its physical certificate -/

private theorem spbGhostMove_done_left_phys
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
        (spbProvGhostMoveToken
          hpsi kind step site l r gl gr).done) :
    (∃ z : GhostToken n psi,
      gl = some z ∧
      m = ghostStepLineageAdvance z.lmeta ∧
      l.last = false ∧ r.last = false ∧
      spbProvLiveValue kind l = some z.value ∧
      spbProvLiveValue kind r = none) ∨
    (∃ z : GhostToken n psi,
      gr = some z ∧
      m = ghostStepLineageAdvance z.lmeta) := by
  let lv0 := spbProvLiveValue kind l
  let rv0 := spbProvLiveValue kind r
  let gl0 := spbProvLiveShadow kind l gl
  let gr0 := spbProvLiveShadow kind r gr

  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      spbProvBirthGhost
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
          (spbProvFinishMove
            hpsi kind l r
            lv2 rv0 gl2 gr0).done := by
      simpa only
        [spbProvGhostMoveToken,
          if_pos hlast]
        using hm

    rcases
        spbProvFinish_done_source_class
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
              [birth, spbProvBirthGhost,
                ghostStepLineageAdvance]
              using hterm
          have hgt :=
            spbProvTrajectoryMoves_gt_one
              psi hpsi
          omega
        · have hgl0 :
              gl0 = some z := by
            simpa [gl1, hbirth] using hgl1
          have hsource :
              gl = some z :=
            spbProvLiveShadow_source
              kind l gl z hgl0
          have hvalue :
              lv0 = some z.value :=
            spbProvLiveShadow_value
              kind l gl z hgl0
          have hlv1 :
              lv1 = some z.value := by
            simpa [lv1, hbirth] using hvalue
          have hcol' :
              ¬ (lv1 ≠ none ∧ rv0 ≠ none) := hcol
          have hrv0 : rv0 = none := by
            refine Classical.byContradiction ?_
            intro hne
            apply hcol'
            refine ⟨?_, hne⟩
            rw [hlv1]
            intro hh
            cases hh
          exact
            .inl
              ⟨z, hsource, hmadv,
                hlast.1, hlast.2,
                hvalue, hrv0⟩

    · rcases hright with
        ⟨tr, z, _hrv, hgr0, hmadv,
          _hterm, _hneg⟩
      have hsource :
          gr = some z :=
        spbProvLiveShadow_source
          kind r gr z hgr0
      exact .inr ⟨z, hsource, hmadv⟩

  · simp
      [spbProvGhostMoveToken,
        if_neg hlast] at hm

private theorem spbProvLiveValue_some
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (v : TokenData psi)
    (h : spbProvLiveValue kind q = some v) :
    tokenAt kind q = some v ∧
      spbProvLocalValid kind q v := by
  cases ht : tokenAt kind q with
  | none =>
      simp [spbProvLiveValue, ht] at h
  | some t =>
      by_cases hv : spbProvLocalValid kind q t
      · have htv : t = v := by
          simpa [spbProvLiveValue, ht, hv] using h
        subst htv
        exact ⟨rfl, hv⟩
      · simp [spbProvLiveValue, ht, hv] at h

/-! ## A definitional mirror of Algorithm 3 -/

private def spbSet
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }

private def spbClear
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match tokenAt kind q with
  | none => q
  | some t =>
      if spbProvLocalValid kind q t then q else spbSet kind q none

private def spbLeaderBirth
    {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }

private def spbMove
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let l := spbClear kind l
  let r := spbClear kind r
  if hlast : l.last = false ∧ r.last = false then
    let l :=
      if l.dist.val = tokenD' psi kind ∧ tokenAt kind l = none then
        spbSet kind l
          (some (spbProvMkToken (offsetPsiCode psi hpsi)
            (spbProvBitToFin (!l.id)) (spbProvBitToFin l.id)))
      else l
    let l :=
      if tokenAt kind l ≠ none ∧ tokenAt kind r ≠ none then
        spbSet kind l none
      else l
    let moveLeft := fun (l r : State psi kappa) =>
      match tokenAt kind r with
      | none => (l, r)
      | some t =>
          let c := decodeOffset psi t.1.1
          if hm1 : c = -1 then
            let next :=
              if t.2 = (1 : Fin 2) then
                spbProvMkToken (offsetPsiCode psi hpsi)
                  (spbProvBitToFin (!l.id)) (spbProvBitToFin l.id)
              else
                spbProvMkToken (offsetPsiCode psi hpsi)
                  (spbProvBitToFin l.id) (0 : Fin 2)
            let l := spbSet kind l (some next)
            let r := spbSet kind r none
            (l, r)
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid psi (by omega) t.1.1
            let nextOffset :=
              encodeOffset psi (c + 1) (by
                rcases hc with hn | hp
                · left
                  omega
                · exfalso
                  omega)
            let l := spbSet kind l
              (some (spbProvMkToken nextOffset t.1.2 t.2))
            let r := spbSet kind r none
            (l, r)
          else
            (l, r)
    match tokenAt kind l with
    | none => moveLeft l r
    | some t =>
        let c := decodeOffset psi t.1.1
        if hc1 : c = 1 then
          let bit := t.1.2.val == 1
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              spbLeaderBirth r
            else if r.mode = false then
              { r with id := bit }
            else r
          let r := spbSet kind r
            (some (spbProvMkToken (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2))
          let l := spbSet kind l none
          (l, r)
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid psi (by omega) t.1.1
          let nextOffset :=
            encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega)
          let r := spbSet kind r
            (some (spbProvMkToken nextOffset t.1.2 t.2))
          let l := spbSet kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)

private theorem spbMove_eq
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    spbMove hpsi kind l r = moveToken hpsi kind l r := by
  cases kind <;> rfl

private theorem spbClear_fields
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    (spbClear kind q).mode = q.mode ∧
      (spbClear kind q).id = q.id ∧
      (spbClear kind q).last = q.last := by
  unfold spbClear
  cases tokenAt kind q with
  | none =>
      exact ⟨rfl, rfl, rfl⟩
  | some t =>
      dsimp only
      split
      · exact ⟨rfl, rfl, rfl⟩
      · cases kind <;> exact ⟨rfl, rfl, rfl⟩

private theorem spbClear_self
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (ht : tokenAt kind q = some t)
    (hv : spbProvLocalValid kind q t) :
    spbClear kind q = q := by
  unfold spbClear
  rw [ht]
  dsimp only
  rw [if_pos hv]

private theorem spbClear_none
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (h : spbProvLiveValue kind q = none) :
    tokenAt kind (spbClear kind q) = none := by
  unfold spbClear
  cases ht : tokenAt kind q with
  | none =>
      exact ht
  | some t =>
      by_cases hv : spbProvLocalValid kind q t
      · simp [spbProvLiveValue, ht, hv] at h
      · dsimp only
        rw [if_neg hv]
        cases kind <;> rfl

/-- Algorithm 3 line 20 on a Detect responder. -/
private theorem spbMove_line20
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (t : TokenData psi)
    (hll : l.last = false)
    (hrl : r.last = false)
    (ht : spbProvLiveValue kind l = some t)
    (hc1 : decodeOffset psi (tokenCode t) = 1)
    (hrv : spbProvLiveValue kind r = none)
    (hmode : r.mode = true)
    (hbit : tokenBitBool t ≠ r.id) :
    PPL.Elim.view4 (moveToken hpsi kind l r).2 =
      PPL.Safety.PeacefulProps.born4 := by
  rcases spbProvLiveValue_some kind l t ht with ⟨htok, hval⟩
  have hcl : spbClear kind l = l :=
    spbClear_self kind l t htok hval
  have hcrTok : tokenAt kind (spbClear kind r) = none :=
    spbClear_none kind r hrv
  rcases spbClear_fields kind r with ⟨hcrMode, hcrId, hcrLast⟩
  rw [← spbMove_eq]
  unfold spbMove
  simp only [hcl]
  generalize spbClear kind r = r' at hcrTok hcrMode hcrId hcrLast ⊢
  have hr'mode : r'.mode = true := hcrMode.trans hmode
  have hr'last : r'.last = false := hcrLast.trans hrl
  have hbit' : (t.1.2.val == 1) ≠ r'.id := by
    rw [hcrId]
    exact hbit
  have hc1' : decodeOffset psi t.1.1 = 1 := hc1
  have hlast : l.last = false ∧ r'.last = false := ⟨hll, hr'last⟩
  rw [dif_pos hlast]
  have hnb :
      ¬ (l.dist.val = tokenD' psi kind ∧ tokenAt kind l = none) := by
    intro hh
    rw [htok] at hh
    cases hh.2
  rw [if_neg hnb]
  have hnc :
      ¬ (tokenAt kind l ≠ none ∧ tokenAt kind r' ≠ none) := by
    intro hh
    exact hh.2 hcrTok
  rw [if_neg hnc]
  try dsimp only
  rw [htok]
  try dsimp only
  rw [dif_pos hc1']
  have hcond : r'.mode = true ∧ (t.1.2.val == 1) ≠ r'.id :=
    ⟨hr'mode, hbit'⟩
  rw [if_pos hcond]
  cases kind <;> rfl

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 200000 in
/-- The responder keeps its ID through Algorithm 3 in Detect, unless it is
born. -/
private theorem spbMove_detect_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (hmode : r.mode = true) :
    (moveToken hpsi kind l r).2.mode = r.mode ∧
      ((moveToken hpsi kind l r).2.id = r.id ∨
        PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          PPL.Safety.PeacefulProps.born4) := by
  rcases spbClear_fields kind r with ⟨hcrMode, hcrId, _hcrLast⟩
  rw [← spbMove_eq]
  unfold spbMove
  generalize spbClear kind l = l' at *
  generalize spbClear kind r = r' at hcrMode hcrId ⊢
  have hr'mode : r'.mode = true := hcrMode.trans hmode
  rw [← hcrMode, ← hcrId]
  cases kind <;>
    (try dsimp only) <;>
    repeat' split
  all_goals
    first
    | exact ⟨rfl, Or.inl rfl⟩
    | exact ⟨rfl, Or.inr rfl⟩
    | (exfalso; simp_all; done)
    | simp_all [spbSet, spbLeaderBirth, PPL.Elim.view4,
        PPL.Safety.PeacefulProps.born4]

/-! ## DetermineMode / line 6 prefix: responder mode and ID -/

private theorem spbDetermineMode_right_id
    {psi kappa : Nat}
    (l r : State psi kappa) :
    (determineMode l r).2.id = r.id := by
  simp only [determineMode]
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals try (split <;> try dsimp only)
  all_goals rfl

private theorem spbPre_right_mode_id
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2.mode =
        (determineMode l r).2.mode ∧
      (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2.id =
        (determineMode l r).2.id := by
  dsimp only [PPL.Safety.PeacefulProps.preTokenPair,
    createLeaderThroughLine6]
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

private theorem spbRightNeighbor_ne_self
    {n : Nat}
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem spbSelectedInput_black
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    spbProvSelectedInput hpsi .black l r =
      PPL.Safety.PeacefulProps.preTokenPair hpsi l r := by
  rfl

private theorem spbSelectedInput_white
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    spbProvSelectedInput hpsi .white l r =
      moveToken hpsi .black
        (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).1
        (PPL.Safety.PeacefulProps.preTokenPair hpsi l r).2 := by
  rfl

/-! ## The row -/

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 200000 in
theorem lemma16TerminalSelectedPassBirthViewRow_proved :
    Lemma16TerminalSelectedPassBirthViewRow := by
  unfold Lemma16TerminalSelectedPassBirthViewRow
  intro n psi kappa
  intro hpsi hn3 ring kind step G e z m
  intro hU hdist howner hadv hmDone hc1 hmismatch
  dsimp only

  let rsite := ring.rightNeighbor e
  let l : State psi kappa := G.phys e
  let r : State psi kappa := G.phys rsite
  let p :=
    PPL.Safety.PeacefulProps.preTokenPair hpsi l r

  -- DistReadyCapped: leaderless, signal-free, clock-capped
  have hlead : l.leader = false :=
    hdist.1.1.2.1 e
  have hlsig : l.signalR.val = 0 :=
    detectStep_signalFree_at G.phys hdist.1.1.2.2.1 e
  have hrsig : r.signalR.val = 0 :=
    detectStep_signalFree_at G.phys hdist.1.1.2.2.1 rsite
  have hlclock : l.clock.val = kappa := hdist.1.2 e
  have hrclock : r.clock.val = kappa := hdist.1.2 rsite
  have hdm :=
    detectStep_determineMode_capped
      hpsi l r hlead hlsig hrsig hlclock hrclock
  dsimp only at hdm
  have hdmode : (determineMode l r).2.mode = true :=
    hdm.2.2.2.1
  rcases spbPre_right_mode_id hpsi l r with ⟨hpmode0, hpid0⟩
  have hpmode : p.2.mode = true := hpmode0.trans hdmode
  have hpid : p.2.id = r.id :=
    hpid0.trans (spbDetermineMode_right_id l r)

  -- The done premise through the mirror
  have hmMirror :
      m ∈
        (spbProvSelectedPair
          hpsi ring step G e kind).done := by
    rw [spbProvSelectedPair_eq_export]
    exact hmDone
  unfold spbProvSelectedPair at hmMirror
  rcases
      spbGhostMove_done_left_phys
        hpsi kind step e
        (spbProvSelectedInput hpsi kind l r).1
        (spbProvSelectedInput hpsi kind l r).2
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G rsite)
        m hmMirror with hleft | hright
  · rcases hleft with
      ⟨z0, howner0, _hadv0, hll, hrl, hlv, hrv⟩
    have hz0 : z0 = z := by
      have hsome : some z0 = some z :=
        howner0.symm.trans howner
      exact Option.some.inj hsome
    subst hz0
    cases kind with
    | black =>
        rw [spbSelectedInput_black] at hll hrl hlv hrv
        show
          PPL.Elim.view4
              (moveToken hpsi .black p.1 p.2).2 =
            PPL.Safety.PeacefulProps.born4
        have hbit : tokenBitBool z0.value ≠ p.2.id := by
          rw [hpid]
          exact hmismatch
        exact
          spbMove_line20 hpsi .black p.1 p.2 z0.value
            hll hrl hlv hc1 hrv hpmode hbit
    | white =>
        rw [spbSelectedInput_white] at hll hrl hlv hrv
        show
          PPL.Elim.view4
              (moveToken hpsi .white
                (moveToken hpsi .black p.1 p.2).1
                (moveToken hpsi .black p.1 p.2).2).2 =
            PPL.Safety.PeacefulProps.born4
        rcases spbMove_detect_id hpsi .black p.1 p.2 hpmode with
          ⟨hbmode, hbid | hbborn⟩
        · have hbit :
              tokenBitBool z0.value ≠
                (moveToken hpsi .black p.1 p.2).2.id := by
            rw [hbid, hpid]
            exact hmismatch
          exact
            spbMove_line20 hpsi .white
              (moveToken hpsi .black p.1 p.2).1
              (moveToken hpsi .black p.1 p.2).2
              z0.value
              hll hrl hlv hc1 hrv
              (hbmode.trans hpmode) hbit
        · have hwcases :=
            PPL.moveToken_view4_cases
              hpsi PPL.TokenKind.white
              (moveToken hpsi .black p.1 p.2).1
              (moveToken hpsi .black p.1 p.2).2
          rcases hwcases.2 with hsame | hborn
          · exact hsame.trans hbborn
          · simpa [PPL.Safety.PeacefulProps.born4]
              using hborn
  · rcases hright with ⟨z0, howner0, hadv0⟩
    exfalso
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
    have hre : rsite = e :=
      hU kind rsite e z0 z howner0 howner hid
    exact spbRightNeighbor_ne_self hn3 ring e hre

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16TerminalSelectedPassBirthViewRow_proved
