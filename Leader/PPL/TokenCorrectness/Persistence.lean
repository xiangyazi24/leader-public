import Leader.PPL.TokenCorrectness.Ghost

namespace PPL

set_option autoImplicit false

/-! ## Live lineage-ID uniqueness with a fresh global birth clock -/

def GhostIdsUnique {n psi kappa : Nat}
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (kind : TokenKind) (i j : Fin n)
    (zi zj : GhostToken n psi),
    ghostTokenAt kind G i = some zi →
    ghostTokenAt kind G j = some zj →
    zi.lmeta.id = zj.lmeta.id →
    i = j

def GhostIdsBefore {n psi kappa : Nat}
    (t : Nat) (G : GhostConfig n psi kappa) : Prop :=
  ∀ (kind : TokenKind) (i : Fin n) (z : GhostToken n psi)
    (bornKind : TokenKind) (s : Nat),
    ghostTokenAt kind G i = some z →
    z.lmeta.id = .born bornKind s →
    s < t

def GhostIdsUniqueAt {n psi kappa : Nat}
    (t : Nat) (G : GhostConfig n psi kappa) : Prop :=
  GhostIdsUnique G ∧ GhostIdsBefore t G

/-! The private TokenCorrectness helpers are mirrored definitionally so this
downstream file can reason about the ghost fields without editing the parent
module. -/

private def r2BitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def r2MkToken {psi : Nat} (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def r2LocalValid {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧ ((psi : Nat) : Int) <= target ∧
      target <= (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧ 1 <= target ∧
      target <= (((psi - 1 : Nat)) : Int))

private instance instDecidableR2LocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa) (t : TokenData psi) :
    Decidable (r2LocalValid kind q t) := by
  unfold r2LocalValid
  infer_instance

private def r2TokenPrelude {psi kappa : Nat} (hpsi : 2 <= psi)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let s := createLeaderThroughLine6 hpsi l r
  let l0 := s.left
  let r0 := s.right
  let tmp := s.tmp
  let r1 :=
    if r0.mode = false then { r0 with dist := tmp } else r0
  let l1 :=
    if r1.leader = true then
      { l0 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def r2LiveShadow {n psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if z.value = t ∧ r2LocalValid kind q t then
            some z
          else none

private def r2LiveValue {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if r2LocalValid kind q t then some t else none

private def r2BirthGhost {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat) (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      r2MkToken (offsetPsiCode psi hpsi)
        (r2BitToFin (!idBit)) (r2BitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def r2BumpTo {n psi kappa : Nat}
    (kind : TokenKind) (qDest : State psi kappa)
    (newValue : TokenData psi) (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none => ⟨none, []⟩
  | some z =>
      let m' : LineageMeta n :=
        { z.lmeta with moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi := { value := newValue, lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then [m'] else []
      let live :=
        if r2LocalValid kind qDest newValue then some z' else none
      ⟨live, done⟩

private def r2FinishMove {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) : GhostMoveResult n psi :=
match lv2 with
| some t =>
    let c := decodeOffset psi (tokenCode t)
    if h1 : c = 1 then
      let next :=
        r2MkToken (offsetNegPsiPlusOneCode psi hpsi)
          t.1.2 t.2
      let b := r2BumpTo kind r next gl2
      ⟨none, b.live, b.done⟩
    else if h2 : 2 <= c then
      have hc : ValidOffset psi c :=
        decodeOffset_valid psi (by omega) (tokenCode t)
      let next :=
        r2MkToken
          (encodeOffset psi (c - 1) (by
            rcases hc with hn | hp
            · exfalso
              omega
            · right
              omega))
          t.1.2 t.2
      let b := r2BumpTo kind r next gl2
      ⟨none, b.live, b.done⟩
    else
      match rv0 with
      | none => ⟨gl2, gr0, []⟩
      | some t =>
          let c := decodeOffset psi (tokenCode t)
          if hm1 : c = -1 then
            let next :=
              if t.2 = (1 : Fin 2) then
                r2MkToken (offsetPsiCode psi hpsi)
                  (r2BitToFin (!l.id)) (r2BitToFin l.id)
              else
                r2MkToken (offsetPsiCode psi hpsi)
                  (r2BitToFin l.id) (0 : Fin 2)
            let b := r2BumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c <= -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid psi (by omega) (tokenCode t)
            let next :=
              r2MkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b := r2BumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩
| none =>
    match rv0 with
    | none => ⟨gl2, gr0, []⟩
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if hm1 : c = -1 then
          let next :=
            if t.2 = (1 : Fin 2) then
              r2MkToken (offsetPsiCode psi hpsi)
                (r2BitToFin (!l.id)) (r2BitToFin l.id)
            else
              r2MkToken (offsetPsiCode psi hpsi)
                (r2BitToFin l.id) (0 : Fin 2)
          let b := r2BumpTo kind l next gr0
          ⟨b.live, none, b.done⟩
        else if hm2 : c <= -2 then
          have hc : ValidOffset psi c :=
            decodeOffset_valid psi (by omega) (tokenCode t)
          let next :=
            r2MkToken
              (encodeOffset psi (c + 1) (by
                rcases hc with hn | hp
                · left
                  omega
                · exfalso
                  omega))
              t.1.2 t.2
          let b := r2BumpTo kind l next gr0
          ⟨b.live, none, b.done⟩
        else
          ⟨gl2, gr0, []⟩

private def r2GhostMoveToken {n psi kappa : Nat}
    (hpsi : 2 <= psi) (kind : TokenKind)
    (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := r2LiveValue kind l
  let rv0 := r2LiveValue kind r
  let gl0 := r2LiveShadow kind l gl
  let gr0 := r2LiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (r2BirthGhost hpsi kind step site l.id)
      else gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (r2BirthGhost hpsi kind step site l.id).value
      else lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    r2FinishMove hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def r2SetTwo {n : Nat} {A : Type} (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) : Fin n -> A :=
  fun k => if k = i then xi else if k = j then xj else f k

private def r2MovedPair {n psi kappa : Nat}
    (hpsi : 2 <= psi) (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa)
    (e : Fin n) (kind : TokenKind) : GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let pre := r2TokenPrelude hpsi (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      r2GhostMoveToken hpsi .black step e pre.1 pre.2
        (G.black e) (G.black rsite)
  | .white =>
      let qb := moveToken hpsi .black pre.1 pre.2
      r2GhostMoveToken hpsi .white step e qb.1 qb.2
        (G.white e) (G.white rsite)

/-- Definitional bridge from the public ghostStep to the mirrored local pair. -/
private theorem ghostTokenAt_ghostStep_eq_r2
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) (i : Fin n) :
    ghostTokenAt kind (ghostStep hpsi ring step G e) i =
      r2SetTwo (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (r2MovedPair hpsi ring step G e kind).left
        (r2MovedPair hpsi ring step G e kind).right i := by
  cases kind <;> rfl

/-! ## Initial ownership -/

private noncomputable def r2InitialOwned {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa) (i : Fin n) :
    Option (GhostToken n psi) := by
  classical
  exact
    match tokenAt kind (C i) with
    | none => none
    | some t =>
        if r2LocalValid kind (C i) t then
          some
            { value := t
              lmeta :=
                { id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0 } }
        else none

private theorem ghostTokenAt_initial_eq_r2
    {n psi kappa : Nat} (C : Config n psi kappa)
    (kind : TokenKind) (i : Fin n) :
    ghostTokenAt kind (initialGhost C) i =
      r2InitialOwned kind C i := by
  cases kind <;> rfl

private theorem initial_owner_id
    {n psi kappa : Nat} (C : Config n psi kappa)
    (kind : TokenKind) (i : Fin n) (z : GhostToken n psi)
    (howner : ghostTokenAt kind (initialGhost C) i = some z) :
    z.lmeta.id = .initial kind i := by
  classical
  rw [ghostTokenAt_initial_eq_r2 C kind i] at howner
  unfold r2InitialOwned at howner
  cases ht : tokenAt kind (C i) with
  | none =>
      simp [ht] at howner
  | some t =>
      by_cases hv : r2LocalValid kind (C i) t
      · simp [ht, hv] at howner
        cases howner
        rfl
      · simp [ht, hv] at howner

theorem ghostIdsUnique_initial
    {n psi kappa : Nat} (C : Config n psi kappa) :
    GhostIdsUniqueAt 0 (initialGhost C) := by
  constructor
  · intro kind i j zi zj hi hj hid
    have hii := initial_owner_id C kind i zi hi
    have hij := initial_owner_id C kind j zj hj
    rw [hii, hij] at hid
    cases hid
    rfl
  · intro kind i z bornKind s howner hid
    have hi := initial_owner_id C kind i z howner
    rw [hi] at hid
    cases hid

/-! ## Option-level linearity of one selected-color shadow move -/

private def R2OptDisjoint {n psi : Nat}
    (a b : Option (GhostToken n psi)) : Prop :=
  ∀ za zb,
    a = some za →
    b = some zb →
    za.lmeta.id ≠ zb.lmeta.id

private def R2OptBefore {n psi : Nat}
    (t : Nat) (a : Option (GhostToken n psi)) : Prop :=
  ∀ z bornKind s,
    a = some z →
    z.lmeta.id = .born bornKind s →
    s < t

private def R2OptFrom {n psi : Nat}
    (a b : Option (GhostToken n psi)) : Prop :=
  ∀ z, b = some z →
    ∃ z0, a = some z0 ∧ z.lmeta.id = z0.lmeta.id

private theorem r2Shadow_from {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    R2OptFrom g (r2LiveShadow kind q g) := by
  intro z hz
  cases g with
  | none => simp [r2LiveShadow] at hz
  | some z0 =>
      unfold r2LiveShadow at hz
      split at hz <;> simp_all
      all_goals split at hz <;> simp_all

private theorem r2Bump_from {n psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) (g : Option (GhostToken n psi)) :
    R2OptFrom g (r2BumpTo kind q t g).live := by
  intro z hz
  cases g with
  | none => simp [r2BumpTo] at hz
  | some z0 =>
      unfold r2BumpTo at hz
      split at hz <;> simp_all
      all_goals cases hz.2 <;> rfl

private theorem r2Before_of_from {n psi : Nat}
    {t : Nat} {a b : Option (GhostToken n psi)}
    (hf : R2OptFrom a b) (ha : R2OptBefore t a) :
    R2OptBefore t b := by
  intro z bornKind s hz hid
  obtain ⟨z0, h0, hsame⟩ := hf z hz
  apply ha z0 bornKind s h0
  exact hsame.symm.trans hid

private theorem r2Disjoint_of_from {n psi : Nat}
    {a b c d : Option (GhostToken n psi)}
    (hac : R2OptFrom a c) (hbd : R2OptFrom b d)
    (hab : R2OptDisjoint a b) : R2OptDisjoint c d := by
  intro zc zd hc hd heq
  obtain ⟨za, ha, hza⟩ := hac zc hc
  obtain ⟨zb, hb, hzb⟩ := hbd zd hd
  exact hab za zb ha hb (hza.symm.trans (heq.trans hzb))

private theorem r2From_refl {n psi : Nat}
    (a : Option (GhostToken n psi)) : R2OptFrom a a := by
  intro z hz
  exact ⟨z, hz, rfl⟩

private theorem r2Before_succ {n psi : Nat}
    {t : Nat} {a : Option (GhostToken n psi)}
    (ha : R2OptBefore t a) : R2OptBefore (t + 1) a := by
  intro z kind s hz hid
  have hs := ha z kind s hz hid
  omega

private theorem r2Birth_before {n psi : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool) :
    R2OptBefore (step + 1)
      (some (r2BirthGhost hpsi kind step site idBit)) := by
  intro z bornKind s hz hid
  cases hz
  simp [r2BirthGhost] at hid
  cases hid
  omega

private theorem r2Birth_disjoint_old {n psi : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step : Nat)
    (site : Fin n) (idBit : Bool)
    (a : Option (GhostToken n psi))
    (ha : R2OptBefore step a) :
    R2OptDisjoint
      (some (r2BirthGhost hpsi kind step site idBit)) a := by
  intro za zb hz hb heq
  cases hz
  have hs := ha zb kind step hb
  apply Nat.lt_irrefl step
  apply hs
  simpa [r2BirthGhost] using heq.symm

/-! Once the prelude chooses its two ghost options, the motion suffix either
retains them, moves one option to the other side, or deletes an option. The
token arithmetic only selects which of these shapes occurs. -/

private theorem r2FinishMove_good {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi)) (step : Nat)
    (hdis : R2OptDisjoint gl2 gr0)
    (hbl : R2OptBefore (step + 1) gl2)
    (hbr : R2OptBefore (step + 1) gr0) :
    let q := r2FinishMove hpsi kind l r lv2 rv0 gl2 gr0
    R2OptDisjoint q.left q.right ∧
      R2OptBefore (step + 1) q.left ∧
      R2OptBefore (step + 1) q.right := by
  have hnone : R2OptBefore (step + 1)
      (none : Option (GhostToken n psi)) := by
    intro z bk s hz _
    simp at hz
  have hright : ∀ (dest : State psi kappa) (v : TokenData psi),
      R2OptDisjoint (none : Option (GhostToken n psi))
          (r2BumpTo kind dest v gl2).live ∧
        R2OptBefore (step + 1) (none : Option (GhostToken n psi)) ∧
        R2OptBefore (step + 1) (r2BumpTo kind dest v gl2).live := by
    intro dest v
    refine ⟨?_, hnone, r2Before_of_from (r2Bump_from kind dest v gl2) hbl⟩
    intro za zb ha _ _
    simp at ha
  have hleft : ∀ (dest : State psi kappa) (v : TokenData psi),
      R2OptDisjoint (r2BumpTo kind dest v gr0).live
          (none : Option (GhostToken n psi)) ∧
        R2OptBefore (step + 1) (r2BumpTo kind dest v gr0).live ∧
        R2OptBefore (step + 1) (none : Option (GhostToken n psi)) := by
    intro dest v
    refine ⟨?_, r2Before_of_from (r2Bump_from kind dest v gr0) hbr, hnone⟩
    intro za zb _ hb _
    simp at hb
  dsimp only
  unfold r2FinishMove
  repeat' (first | split <;> try dsimp only)
  all_goals first
    | exact ⟨hdis, hbl, hbr⟩
    | exact hright _ _
    | exact hleft _ _

private theorem r2FinishMove_external {n psi kappa : Nat}
    (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 ext : Option (GhostToken n psi))
    (hdl : R2OptDisjoint gl2 ext)
    (hdr : R2OptDisjoint gr0 ext) :
    let q := r2FinishMove hpsi kind l r lv2 rv0 gl2 gr0
    R2OptDisjoint q.left ext ∧ R2OptDisjoint q.right ext := by
  have hnone : R2OptDisjoint
      (none : Option (GhostToken n psi)) ext := by
    intro za zb ha _ _
    simp at ha
  have hright : ∀ (dest : State psi kappa) (v : TokenData psi),
      R2OptDisjoint (none : Option (GhostToken n psi)) ext ∧
        R2OptDisjoint (r2BumpTo kind dest v gl2).live ext := by
    intro dest v
    exact ⟨hnone,
      r2Disjoint_of_from (r2Bump_from kind dest v gl2)
        (r2From_refl ext) hdl⟩
  have hleft : ∀ (dest : State psi kappa) (v : TokenData psi),
      R2OptDisjoint (r2BumpTo kind dest v gr0).live ext ∧
        R2OptDisjoint (none : Option (GhostToken n psi)) ext := by
    intro dest v
    exact ⟨r2Disjoint_of_from (r2Bump_from kind dest v gr0)
      (r2From_refl ext) hdr, hnone⟩
  dsimp only
  unfold r2FinishMove
  repeat' (first | split <;> try dsimp only)
  all_goals first
    | exact ⟨hdl, hdr⟩
    | exact hright _ _
    | exact hleft _ _

private theorem r2GhostMoveToken_good
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hdis : R2OptDisjoint gl gr)
    (hbl : R2OptBefore step gl)
    (hbr : R2OptBefore step gr) :
    let q := r2GhostMoveToken hpsi kind step site l r gl gr
    R2OptDisjoint q.left q.right ∧
      R2OptBefore (step + 1) q.left ∧
      R2OptBefore (step + 1) q.right := by
  let gl0 := r2LiveShadow kind l gl
  let gr0 := r2LiveShadow kind r gr
  have hgl0 := r2Shadow_from kind l gl
  have hgr0 := r2Shadow_from kind r gr
  have hdis0 : R2OptDisjoint gl0 gr0 :=
    r2Disjoint_of_from hgl0 hgr0 hdis
  have hbl0 : R2OptBefore step gl0 := r2Before_of_from hgl0 hbl
  have hbr0 : R2OptBefore step gr0 := r2Before_of_from hgr0 hbr
  by_cases hlast : l.last = false ∧ r.last = false
  · let rv0 := r2LiveValue kind r
    let lv0 := r2LiveValue kind l
    let birth := r2BirthGhost hpsi kind step site l.id
    let hb := l.dist.val = tokenD' psi kind ∧ lv0 = none
    let gl1 := if hb then some birth else gl0
    let lv1 := if hb then some birth.value else lv0
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let gl2 := if collide then none else gl1
    let lv2 := if collide then none else lv1
    have hbl1 : R2OptBefore (step + 1) gl1 := by
      by_cases h : hb
      · simpa [gl1, h, birth] using
          r2Birth_before hpsi kind step site l.id
      · simpa [gl1, h] using r2Before_succ hbl0
    have hdis1 : R2OptDisjoint gl1 gr0 := by
      by_cases h : hb
      · simpa [gl1, h, birth] using
          r2Birth_disjoint_old hpsi kind step site l.id gr0 hbr0
      · simpa [gl1, h] using hdis0
    have hbl2 : R2OptBefore (step + 1) gl2 := by
      by_cases h : collide
      · intro z bk s hz _
        simp [gl2, h] at hz
      · simpa [gl2, h] using hbl1
    have hdis2 : R2OptDisjoint gl2 gr0 := by
      by_cases h : collide
      · intro za zb ha _ _
        simp [gl2, h] at ha
      · simpa [gl2, h] using hdis1
    have hq : r2GhostMoveToken hpsi kind step site l r gl gr =
        r2FinishMove hpsi kind l r lv2 rv0 gl2 gr0 := by
      simp only [r2GhostMoveToken, if_pos hlast]
      rfl
    dsimp only
    rw [hq]
    exact r2FinishMove_good hpsi kind l r lv2 rv0 gl2 gr0 step
      hdis2 hbl2 (r2Before_succ hbr0)
  · have hq : r2GhostMoveToken hpsi kind step site l r gl gr =
        (⟨gl0, gr0, []⟩ : GhostMoveResult n psi) := by
      simp [r2GhostMoveToken, hlast, gl0, gr0]
    dsimp only
    rw [hq]
    exact ⟨hdis0, r2Before_succ hbl0, r2Before_succ hbr0⟩

private theorem r2GhostMoveToken_external
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr ext : Option (GhostToken n psi))
    (hdl : R2OptDisjoint gl ext)
    (hdr : R2OptDisjoint gr ext)
    (hbe : R2OptBefore step ext) :
    let q := r2GhostMoveToken hpsi kind step site l r gl gr
    R2OptDisjoint q.left ext ∧ R2OptDisjoint q.right ext := by
  let gl0 := r2LiveShadow kind l gl
  let gr0 := r2LiveShadow kind r gr
  have hgl0 := r2Shadow_from kind l gl
  have hgr0 := r2Shadow_from kind r gr
  have hdl0 : R2OptDisjoint gl0 ext :=
    r2Disjoint_of_from hgl0 (r2From_refl ext) hdl
  have hdr0 : R2OptDisjoint gr0 ext :=
    r2Disjoint_of_from hgr0 (r2From_refl ext) hdr
  by_cases hlast : l.last = false ∧ r.last = false
  · let rv0 := r2LiveValue kind r
    let lv0 := r2LiveValue kind l
    let birth := r2BirthGhost hpsi kind step site l.id
    let hb := l.dist.val = tokenD' psi kind ∧ lv0 = none
    let gl1 := if hb then some birth else gl0
    let lv1 := if hb then some birth.value else lv0
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let gl2 := if collide then none else gl1
    let lv2 := if collide then none else lv1
    have hdl1 : R2OptDisjoint gl1 ext := by
      by_cases h : hb
      · simpa [gl1, h, birth] using
          r2Birth_disjoint_old hpsi kind step site l.id ext hbe
      · simpa [gl1, h] using hdl0
    have hdl2 : R2OptDisjoint gl2 ext := by
      by_cases h : collide
      · intro za zb ha _ _
        simp [gl2, h] at ha
      · simpa [gl2, h] using hdl1
    have hq : r2GhostMoveToken hpsi kind step site l r gl gr =
        r2FinishMove hpsi kind l r lv2 rv0 gl2 gr0 := by
      simp only [r2GhostMoveToken, if_pos hlast]
      rfl
    dsimp only
    rw [hq]
    exact r2FinishMove_external hpsi kind l r lv2 rv0 gl2 gr0 ext
      hdl2 hdr0
  · have hq : r2GhostMoveToken hpsi kind step site l r gl gr =
        (⟨gl0, gr0, []⟩ : GhostMoveResult n psi) := by
      simp [r2GhostMoveToken, hlast, gl0, gr0]
    dsimp only
    rw [hq]
    exact ⟨hdl0, hdr0⟩

private theorem r2MovedPair_good
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind)
    (hdis :
      R2OptDisjoint
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G (ring.rightNeighbor e)))
    (hbl : R2OptBefore step (ghostTokenAt kind G e))
    (hbr :
      R2OptBefore step
        (ghostTokenAt kind G (ring.rightNeighbor e))) :
    let q := r2MovedPair hpsi ring step G e kind
    R2OptDisjoint q.left q.right ∧
      R2OptBefore (step + 1) q.left ∧
      R2OptBefore (step + 1) q.right := by
  unfold r2MovedPair
  cases kind <;> dsimp only
  all_goals
    apply r2GhostMoveToken_good <;> assumption

private theorem r2MovedPair_external
    {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) (ext : Option (GhostToken n psi))
    (hdl : R2OptDisjoint (ghostTokenAt kind G e) ext)
    (hdr :
      R2OptDisjoint
        (ghostTokenAt kind G (ring.rightNeighbor e)) ext)
    (hbe : R2OptBefore step ext) :
    let q := r2MovedPair hpsi ring step G e kind
    R2OptDisjoint q.left ext ∧ R2OptDisjoint q.right ext := by
  unfold r2MovedPair
  cases kind <;> dsimp only
  all_goals
    apply r2GhostMoveToken_external <;> assumption

private theorem rightNeighbor_ne_self_r2
    {n : Nat} (hn2 : 2 <= n)
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.val + 1) % n = i.val at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      have hi := i.isLt
      omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem ghostIdsUnique_step
    {n psi kappa : Nat} (hpsi : 2 <= psi) (hn2 : 2 <= n)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n)
    (hU : GhostIdsUniqueAt step G) :
    GhostIdsUniqueAt (step + 1) (ghostStep hpsi ring step G e) := by
  classical
  rcases hU with ⟨huniq, hbefore⟩
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_r2 hn2 ring e
  constructor
  · intro kind i j zi zj hi hj hid
    rw [ghostTokenAt_ghostStep_eq_r2 hpsi ring step G e kind i] at hi
    rw [ghostTokenAt_ghostStep_eq_r2 hpsi ring step G e kind j] at hj

    have hpair :
        R2OptDisjoint
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G (ring.rightNeighbor e)) := by
      intro a b ha hb hab
      have heq :=
        huniq kind e (ring.rightNeighbor e) a b ha hb hab
      exact hne heq.symm

    have hbe : R2OptBefore step (ghostTokenAt kind G e) := by
      intro z bornKind s hz hs
      exact hbefore kind e z bornKind s hz hs

    have hbr :
        R2OptBefore step
          (ghostTokenAt kind G (ring.rightNeighbor e)) := by
      intro z bornKind s hz hs
      exact hbefore kind (ring.rightNeighbor e) z bornKind s hz hs

    have hgood :=
      r2MovedPair_good hpsi ring step G e kind hpair hbe hbr
    dsimp only at hgood

    have hext :
        ∀ x : Fin n,
          x ≠ e →
          x ≠ ring.rightNeighbor e →
          let q := r2MovedPair hpsi ring step G e kind
          R2OptDisjoint q.left (ghostTokenAt kind G x) ∧
            R2OptDisjoint q.right (ghostTokenAt kind G x) := by
      intro x hxe hxr
      have hdl :
          R2OptDisjoint
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G x) := by
        intro a b ha hb hab
        have heq := huniq kind e x a b ha hb hab
        exact hxe heq.symm
      have hdr :
          R2OptDisjoint
            (ghostTokenAt kind G (ring.rightNeighbor e))
            (ghostTokenAt kind G x) := by
        intro a b ha hb hab
        have heq :=
          huniq kind (ring.rightNeighbor e) x a b ha hb hab
        exact hxr heq.symm
      have hbx : R2OptBefore step (ghostTokenAt kind G x) := by
        intro z bornKind s hz hs
        exact hbefore kind x z bornKind s hz hs
      exact
        r2MovedPair_external hpsi ring step G e kind
          (ghostTokenAt kind G x) hdl hdr hbx

    by_cases hie : i = e
    · subst i
      simp [r2SetTwo] at hi
      by_cases hje : j = e
      · exact hje.symm
      · by_cases hjr : j = ring.rightNeighbor e
        · subst j
          simp [r2SetTwo, hne] at hj
          exfalso
          exact (hgood.1 zi zj hi hj) hid
        · simp [r2SetTwo, hje, hjr] at hj
          have hx := hext j hje hjr
          dsimp only at hx
          exfalso
          exact (hx.1 zi zj hi hj) hid
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        simp [r2SetTwo, hne] at hi
        by_cases hje : j = e
        · subst j
          simp [r2SetTwo] at hj
          exfalso
          exact (hgood.1 zj zi hj hi) hid.symm
        · by_cases hjr : j = ring.rightNeighbor e
          · exact hjr.symm
          · simp [r2SetTwo, hje, hjr] at hj
            have hx := hext j hje hjr
            dsimp only at hx
            exfalso
            exact (hx.2 zi zj hi hj) hid
      · simp [r2SetTwo, hie, hir] at hi
        by_cases hje : j = e
        · subst j
          simp [r2SetTwo] at hj
          have hx := hext i hie hir
          dsimp only at hx
          exfalso
          exact (hx.1 zj zi hj hi) hid.symm
        · by_cases hjr : j = ring.rightNeighbor e
          · subst j
            simp [r2SetTwo, hne] at hj
            have hx := hext i hie hir
            dsimp only at hx
            exfalso
            exact (hx.2 zj zi hj hi) hid.symm
          · simp [r2SetTwo, hje, hjr] at hj
            exact huniq kind i j zi zj hi hj hid

  · intro kind i z bornKind s hi hid
    rw [ghostTokenAt_ghostStep_eq_r2 hpsi ring step G e kind i] at hi

    have hpair :
        R2OptDisjoint
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G (ring.rightNeighbor e)) := by
      intro a b ha hb hab
      have heq :=
        huniq kind e (ring.rightNeighbor e) a b ha hb hab
      exact hne heq.symm

    have hbe : R2OptBefore step (ghostTokenAt kind G e) := by
      intro z0 bornKind0 s0 hz hs
      exact hbefore kind e z0 bornKind0 s0 hz hs

    have hbr :
        R2OptBefore step
          (ghostTokenAt kind G (ring.rightNeighbor e)) := by
      intro z0 bornKind0 s0 hz hs
      exact hbefore kind (ring.rightNeighbor e) z0 bornKind0 s0 hz hs

    have hgood :=
      r2MovedPair_good hpsi ring step G e kind hpair hbe hbr
    dsimp only at hgood

    by_cases hie : i = e
    · subst i
      simp [r2SetTwo] at hi
      exact hgood.2.1 z bornKind s hi hid
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        simp [r2SetTwo, hne] at hi
        exact hgood.2.2 z bornKind s hi hid
      · simp [r2SetTwo, hie, hir] at hi
        have hs := hbefore kind i z bornKind s hi hid
        omega

/-! ## Repaired Remark 2 statement

The global step number is explicit.  Using z.lmeta.moves here is not sound:
moves is a lineage-local trajectory counter, not the birth-ID clock.

This is the sole remaining open semantic branch in this file. -/

def remark2_one_step_unique : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (step : Nat)
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa) (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi)
    (hphys : G.phys = C)
    (hG : GhostSound G)
    (huniq : GhostIdsUniqueAt step G)
    (howner : ghostTokenAt kind G i = some z)
    (hvalid : ValidToken kind C i)
    (hwork : WorkingFor ring root C i kind seg.val)
    (hcorr : CorrectToken ring root C i kind seg.val)
    (hC : CDLAt ring root C)
    (hC' :
      CDLAt ring root
        (PopulationProtocol.step (protocol psi kappa) ring C e)),
    let C' := PopulationProtocol.step (protocol psi kappa) ring C e
    let G' := ghostStep hpsi ring step G e
    sourceIota ring root C seg.val ≠ sourceIota ring root C' seg.val ∨
      LineageDeleted kind z.lmeta.id G' ∨
      CorrectDescendant ring root seg.val kind z.lmeta.id G'

end PPL

#print axioms PPL.ghostIdsUnique_initial
#print axioms PPL.ghostIdsUnique_step
#check PPL.remark2_one_step_unique
