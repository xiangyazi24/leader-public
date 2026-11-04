import Leader.PPL.TokenCompletion.SweepOldOwner
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

def Lemma4SweepFreshLineagePersistenceStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i j : Fin n)
    (z z' : GhostToken n psi),
    GhostIdsUniqueAt step G →
    Lemma4InWindow ring k psi i →
    ghostTokenAt kind G i = some z →
    FreshAt kind k z.lmeta →
    Lemma4InWindow ring k psi j →
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) j =
      some z' →
    z'.lmeta.id = z.lmeta.id →
    FreshAt kind k z'.lmeta

private def freshPersistBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def freshPersistMkToken {psi : Nat}
    (o : Fin (2 * psi - 1)) (b c : Fin 2) : TokenData psi :=
  ((o, b), c)

private def freshPersistLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧ ((psi : Nat) : Int) ≤ target ∧
      target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧ 1 ≤ target ∧
      target ≤ (((psi - 1 : Nat)) : Int))

private instance freshPersistLocalValidDecidable
    {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) :
    Decidable (freshPersistLocalValid kind q t) := by
  unfold freshPersistLocalValid
  infer_instance

private def freshPersistPrelude {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let s := createLeaderThroughLine6 hpsi l r
  let r1 := if s.right.mode = false then {s.right with dist := s.tmp} else s.right
  let l1 :=
    if r1.leader = true then {s.left with last := true}
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then {s.left with last := false}
    else {s.left with last := r1.last}
  (l1, r1)

private def freshPersistLiveShadow {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi)) : Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if z.value = t ∧ freshPersistLocalValid kind q t then some z else none

private def freshPersistLiveValue {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) : Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t => if freshPersistLocalValid kind q t then some t else none

private def freshPersistBirth {n psi : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) : GhostToken n psi :=
  { value := freshPersistMkToken (offsetPsiCode psi hpsi)
      (freshPersistBitToFin (!idBit)) (freshPersistBitToFin idBit),
    lmeta := (⟨LineageId.born kind step, site, step, 0⟩ : LineageMeta n) }

private def freshPersistBump {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) (v : TokenData psi)
    (g : Option (GhostToken n psi)) : Bumped n psi :=
  match g with
  | none => ⟨none, []⟩
  | some z =>
      let m := ghostStepLineageAdvance z.lmeta
      let z' : GhostToken n psi := { value := v, lmeta := m }
      let done := if m.moves = tokenTrajectoryMoves psi then [m] else []
      let live := if freshPersistLocalValid kind q v then some z' else none
      ⟨live, done⟩

private def freshPersistNegTurn {psi : Nat}
    (hpsi : 2 ≤ psi) (idBit : Bool) (t : TokenData psi) : TokenData psi :=
  if t.2 = (1 : Fin 2) then
    freshPersistMkToken (offsetPsiCode psi hpsi)
      (freshPersistBitToFin (!idBit)) (freshPersistBitToFin idBit)
  else
    freshPersistMkToken (offsetPsiCode psi hpsi)
      (freshPersistBitToFin idBit) (0 : Fin 2)

private def freshPersistFinish {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa)
    (lv rv : Option (TokenData psi))
    (gl gr : Option (GhostToken n psi)) : GhostMoveResult n psi :=
  match lv with
  | some t =>
      let c := decodeOffset psi (tokenCode t)
      if h1 : c = 1 then
        let v := freshPersistMkToken (offsetNegPsiPlusOneCode psi hpsi) t.1.2 t.2
        let b := freshPersistBump kind r v gl
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c := decodeOffset_valid psi (by omega) (tokenCode t)
        let v := freshPersistMkToken
          (encodeOffset psi (c - 1) (by
            rcases hc with hn | hp
            · exfalso; omega
            · right; omega)) t.1.2 t.2
        let b := freshPersistBump kind r v gl
        ⟨none, b.live, b.done⟩
      else
        match rv with
        | none => ⟨gl, gr, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let b := freshPersistBump kind l (freshPersistNegTurn hpsi l.id t) gr
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c := decodeOffset_valid psi (by omega) (tokenCode t)
              let v := freshPersistMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left; omega
                  · exfalso; omega)) t.1.2 t.2
              let b := freshPersistBump kind l v gr
              ⟨b.live, none, b.done⟩
            else ⟨gl, gr, []⟩
  | none =>
      match rv with
      | none => ⟨gl, gr, []⟩
      | some t =>
          let c := decodeOffset psi (tokenCode t)
          if hm1 : c = -1 then
            let b := freshPersistBump kind l (freshPersistNegTurn hpsi l.id t) gr
            ⟨b.live, none, b.done⟩
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c := decodeOffset_valid psi (by omega) (tokenCode t)
            let v := freshPersistMkToken
              (encodeOffset psi (c + 1) (by
                rcases hc with hn | hp
                · left; omega
                · exfalso; omega)) t.1.2 t.2
            let b := freshPersistBump kind l v gr
            ⟨b.live, none, b.done⟩
          else ⟨gl, gr, []⟩

private def freshPersistMove {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat) (site : Fin n)
    (l r : State psi kappa) (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := freshPersistLiveValue kind l
  let rv0 := freshPersistLiveValue kind r
  let gl0 := freshPersistLiveShadow kind l gl
  let gr0 := freshPersistLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let guard := l.dist.val = tokenD' psi kind ∧ lv0 = none
    let born := freshPersistBirth hpsi kind step site l.id
    let lv1 := if guard then some born.value else lv0
    let gl1 := if guard then some born else gl0
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    freshPersistFinish hpsi kind l r
      (if collide then none else lv1) rv0
      (if collide then none else gl1) gr0
  else ⟨gl0, gr0, []⟩

private def freshPersistSelectedInput {psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let p := freshPersistPrelude hpsi l r
  match kind with
  | .black => p
  | .white => moveToken hpsi .black p.1 p.2

private def freshPersistSelectedPair {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (kind : TokenKind) :
    GhostMoveResult n psi :=
  let r := ring.rightNeighbor e
  let p := freshPersistSelectedInput hpsi kind (G.phys e) (G.phys r)
  freshPersistMove hpsi kind step e p.1 p.2
    (ghostTokenAt kind G e) (ghostTokenAt kind G r)

private theorem freshPersistSelectedPair_eq
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) :
    freshPersistSelectedPair hpsi ring step G e kind =
      ghostStepSelectedPair hpsi ring step G e kind := by
  cases kind <;> rfl

private def freshPersistGood {n psi : Nat}
    (id : LineageId n) (k : Fin n) (g : Option (GhostToken n psi)) : Prop :=
  ∀ z, g = some z → z.lmeta.id = id → z.lmeta.birthSite = k

private theorem freshPersistGood_none {n psi : Nat}
    (id : LineageId n) (k : Fin n) :
    freshPersistGood (psi := psi) id k none := by
  intro z hz _
  simp at hz

private theorem freshPersistPreGood
    {n psi kappa : Nat} {kind : TokenKind} {step : Nat}
    {G : GhostConfig n psi kappa} {i k : Fin n} {z : GhostToken n psi}
    (hu : GhostIdsUniqueAt step G)
    (ho : ghostTokenAt kind G i = some z)
    (hf : FreshAt kind k z.lmeta)
    (site : Fin n) :
    freshPersistGood z.lmeta.id k (ghostTokenAt kind G site) := by
  rcases hf with ⟨t, hb, hs⟩
  intro u hu0 hid
  have hsi : site = i := hu.1 kind site i u z hu0 ho hid
  subst site
  rw [ho] at hu0
  have hzu : z = u := Option.some.inj hu0
  subst u
  exact hs

private theorem freshPersistBirthGood
    {n psi : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step t : Nat) (site k : Fin n) (idBit : Bool)
    (id : LineageId n) (hid : id = .born kind t) (hlt : t < step) :
    freshPersistGood id k (some (freshPersistBirth hpsi kind step site idBit)) := by
  intro u hu huid
  have hbu : freshPersistBirth hpsi kind step site idBit = u :=
    Option.some.inj hu
  subst u
  have heq : (LineageId.born kind step : LineageId n) = .born kind t := by
    calc
      .born kind step =
          (freshPersistBirth hpsi kind step site idBit).lmeta.id := by rfl
      _ = id := huid
      _ = .born kind t := hid
  have hst : step = t := by
    cases heq
    rfl
  exfalso
  omega

private theorem freshPersistShadowGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hg : freshPersistGood id k g) :
    freshPersistGood id k (freshPersistLiveShadow kind q g) := by
  intro z hz hid
  cases g with
  | none => simp [freshPersistLiveShadow] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none => simp [freshPersistLiveShadow, ht] at hz
      | some t =>
          by_cases hv : z0.value = t ∧ freshPersistLocalValid kind q t
          · have heq : z0 = z := by
              simpa [freshPersistLiveShadow, ht, hv] using hz
            subst z
            exact hg z0 rfl hid
          · simp [freshPersistLiveShadow, ht, hv] at hz

private theorem freshPersistBumpGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (kind : TokenKind) (q : State psi kappa) (v : TokenData psi)
    (g : Option (GhostToken n psi))
    (hg : freshPersistGood id k g) :
    freshPersistGood id k (freshPersistBump kind q v g).live := by
  intro z hz hid
  cases g with
  | none => simp [freshPersistBump] at hz
  | some z0 =>
      by_cases hv : freshPersistLocalValid kind q v
      · simp only [freshPersistBump, if_pos hv, Option.some.injEq] at hz
        subst z
        have hid0 : z0.lmeta.id = id := by
          simpa [ghostStepLineageAdvance] using hid
        have hs := hg z0 rfl hid0
        simpa [ghostStepLineageAdvance] using hs
      · simp [freshPersistBump, hv] at hz

private theorem freshPersistFinishGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa)
    (lv rv : Option (TokenData psi)) (gl gr : Option (GhostToken n psi))
    (hgl : freshPersistGood id k gl) (hgr : freshPersistGood id k gr) :
    let q := freshPersistFinish hpsi kind l r lv rv gl gr
    freshPersistGood id k q.left ∧ freshPersistGood id k q.right := by
  cases lv with
  | none =>
      cases rv with
      | none => exact ⟨hgl, hgr⟩
      | some t =>
          by_cases h1 : decodeOffset psi (tokenCode t) = -1
          · simp only [freshPersistFinish, dif_pos h1]
            exact ⟨freshPersistBumpGood id k kind l
              (freshPersistNegTurn hpsi l.id t) gr hgr,
              freshPersistGood_none id k⟩
          · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
            · simp only [freshPersistFinish, dif_neg h1, dif_pos h2]
              exact ⟨freshPersistBumpGood id k kind l _ gr hgr,
                freshPersistGood_none id k⟩
            · simp only [freshPersistFinish, dif_neg h1, dif_neg h2]
              exact ⟨hgl, hgr⟩
  | some t =>
      by_cases h1 : decodeOffset psi (tokenCode t) = 1
      · simp only [freshPersistFinish, dif_pos h1]
        exact ⟨freshPersistGood_none id k,
          freshPersistBumpGood id k kind r _ gl hgl⟩
      · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode t)
        · simp only [freshPersistFinish, dif_neg h1, dif_pos h2]
          exact ⟨freshPersistGood_none id k,
            freshPersistBumpGood id k kind r _ gl hgl⟩
        · cases rv with
          | none =>
              simp only [freshPersistFinish, dif_neg h1, dif_neg h2]
              exact ⟨hgl, hgr⟩
          | some tr =>
              by_cases hm1 : decodeOffset psi (tokenCode tr) = -1
              · simp only [freshPersistFinish, dif_neg h1, dif_neg h2, dif_pos hm1]
                exact ⟨freshPersistBumpGood id k kind l
                  (freshPersistNegTurn hpsi l.id tr) gr hgr,
                  freshPersistGood_none id k⟩
              · by_cases hm2 : decodeOffset psi (tokenCode tr) ≤ -2
                · simp only [freshPersistFinish, dif_neg h1, dif_neg h2,
                    dif_neg hm1, dif_pos hm2]
                  exact ⟨freshPersistBumpGood id k kind l _ gr hgr,
                    freshPersistGood_none id k⟩
                · simp only [freshPersistFinish, dif_neg h1, dif_neg h2,
                    dif_neg hm1, dif_neg hm2]
                  exact ⟨hgl, hgr⟩

private theorem freshPersistMoveGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step t : Nat) (site : Fin n)
    (l r : State psi kappa) (gl gr : Option (GhostToken n psi))
    (hid : id = .born kind t) (hlt : t < step)
    (hgl : freshPersistGood id k gl) (hgr : freshPersistGood id k gr) :
    let q := freshPersistMove hpsi kind step site l r gl gr
    freshPersistGood id k q.left ∧ freshPersistGood id k q.right := by
  have hgl0 := freshPersistShadowGood id k kind l gl hgl
  have hgr0 := freshPersistShadowGood id k kind r gr hgr
  by_cases hlast : l.last = false ∧ r.last = false
  · let lv0 := freshPersistLiveValue kind l
    let rv0 := freshPersistLiveValue kind r
    let guard := l.dist.val = tokenD' psi kind ∧ lv0 = none
    let born := freshPersistBirth hpsi kind step site l.id
    let lv1 := if guard then some born.value else lv0
    let gl1 := if guard then some born else freshPersistLiveShadow kind l gl
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let gl2 := if collide then none else gl1
    have hgl1 : freshPersistGood id k gl1 := by
      by_cases hb : guard
      · simp [gl1, hb]
        exact freshPersistBirthGood hpsi kind step t site k l.id id hid hlt
      · simpa [gl1, hb] using hgl0
    have hgl2 : freshPersistGood id k gl2 := by
      by_cases hc : collide
      · simp [gl2, hc]
        exact freshPersistGood_none id k
      · simpa [gl2, hc] using hgl1
    have hf := freshPersistFinishGood id k hpsi kind l r
      (if collide then none else lv1) rv0 gl2
      (freshPersistLiveShadow kind r gr) hgl2 hgr0
    simpa [freshPersistMove, hlast, lv0, rv0, guard, born,
      lv1, gl1, collide, gl2] using hf
  · simpa [freshPersistMove, hlast] using And.intro hgl0 hgr0

private theorem freshPersistSelectedPairGood
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (kind : TokenKind) (step : Nat) (G : GhostConfig n psi kappa)
    (e i k : Fin n) (z : GhostToken n psi)
    (hu : GhostIdsUniqueAt step G)
    (ho : ghostTokenAt kind G i = some z)
    (hf : FreshAt kind k z.lmeta) :
    let q := ghostStepSelectedPair hpsi ring step G e kind
    freshPersistGood z.lmeta.id k q.left ∧
      freshPersistGood z.lmeta.id k q.right := by
  rcases hf with ⟨t, hb, hs⟩
  have hlt : t < step := hu.2 kind i z kind t ho hb
  have hgl := freshPersistPreGood hu ho ⟨t, hb, hs⟩ e
  have hgr := freshPersistPreGood hu ho ⟨t, hb, hs⟩ (ring.rightNeighbor e)
  let p := freshPersistSelectedInput hpsi kind
    (G.phys e) (G.phys (ring.rightNeighbor e))
  have hm := freshPersistMoveGood z.lmeta.id k hpsi kind step t e
    p.1 p.2 (ghostTokenAt kind G e)
    (ghostTokenAt kind G (ring.rightNeighbor e))
    hb hlt hgl hgr
  rw [← freshPersistSelectedPair_eq hpsi ring step G e kind]
  exact hm

theorem lemma4SweepFreshLineagePersistenceStep_proved :
    Lemma4SweepFreshLineagePersistenceStep := by
  unfold Lemma4SweepFreshLineagePersistenceStep
  intro n psi kappa hpsi ring k kind step G e i j z z'
  intro hu _ ho hf _ hpost hid
  rcases hf with ⟨t, hb, hs⟩
  have hpair := freshPersistSelectedPairGood hpsi ring kind step G e i k z
    hu ho ⟨t, hb, hs⟩
  refine ⟨t, hid.trans hb, ?_⟩
  by_cases hje : j = e
  · subst j
    exact hpair.1 z'
      ((ghostTokenAt_ghostStep_initiator hpsi ring step G e kind).symm.trans hpost)
      hid
  · by_cases hjr : j = ring.rightNeighbor e
    · subst j
      have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact hje h
      exact hpair.2 z'
        ((ghostTokenAt_ghostStep_responder_of_ne
          hpsi ring step G e kind hne).symm.trans hpost) hid
    · have hpre :=
        (ghostTokenAt_ghostStep_frame hpsi ring step G e j kind hje hjr).symm.trans hpost
      exact (freshPersistPreGood hu ho ⟨t, hb, hs⟩ j) z' hpre hid

end PPL

#print axioms PPL.lemma4SweepFreshLineagePersistenceStep_proved
