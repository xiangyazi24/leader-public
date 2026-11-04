import Leader.PPL.CompletionRunner.ForcedConstructInstance

/-!
# Step-parametric Lemma 4: fresh-lineage persistence for the prime runner

`FreshLineagePersistenceStep primeRunner`, i.e. the prime analogue of
`lemma4SweepFreshLineagePersistenceStep_proved`.

The ordinary proof (`TokenCorrectnessLemma4SweepFreshPersist.lean`) never
looks at the physical transition: it only uses that the ghost MoveToken keeps
the lineage ID and birth site of every surviving or moved owner, and that a
birth at clock `step` has the new ID `.born kind step`.  The same holds for
the prime ghost MoveToken, applied to whatever local pair the prime prelude
and the prime black MoveToken produce.  Since the prime ghost bookkeeping is
private to `L18PrimeGhost.lean`, it is mirrored verbatim below (the mirror is
definitionally the original: `pfpSelectedPair_eq` is `rfl`), and the ordinary
proof is re-run on the mirror.  The mirror is public so that
`PrimeBridge.lean` can reuse it.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 1. Verbatim mirror of the private prime ghost bookkeeping -/

def pfpGhostBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

def pfpGhostMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

def pfpGhostLocalValid
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

instance instDecidablePfpGhostLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (pfpGhostLocalValid kind q t) := by
  unfold pfpGhostLocalValid
  infer_instance

/-- Mirror of the private `primeGhostSetTwo`. -/
def pfpGhostSetTwo
    {n : Nat} {A : Type}
    (f : Fin n → A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n → A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

/--
The pre-Algorithm-3 pair for P_PL prime.

This is the prefix of pprimeCreateLeader through Algorithm-2 line 9:
DetermineMode is literal, line 6 is suppressed, the line-4 distance is always
written, then last is updated from that written responder.
-/
def pfpGhostPrelude
    {psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    State psi kappa × State psi kappa :=
  let q := determineMode l r
  let tmp : Fin (2 * psi) :=
    if q.2.leader = true then
      ⟨0, by omega⟩
    else
      ⟨(q.1.dist.val + 1) % (2 * psi),
        Nat.mod_lt _ (by omega)⟩
  let r1 : State psi kappa :=
    { q.2 with dist := tmp }
  let l1 : State psi kappa :=
    if r1.leader = true then
      { q.1 with last := true }
    else if r1.dist.val = 0 ∨ r1.dist.val = psi then
      { q.1 with last := false }
    else
      { q.1 with last := r1.last }
  (l1, r1)

def pfpGhostLiveShadow
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
          if z.value = t ∧
              pfpGhostLocalValid kind q t then
            some z
          else
            none

def pfpGhostLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if pfpGhostLocalValid kind q t then
        some t
      else
        none

def pfpGhostBirth
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      pfpGhostMkToken
        (offsetPsiCode psi hpsi)
        (pfpGhostBitToFin (!idBit))
        (pfpGhostBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

def pfpGhostBumpTo
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
        { z.lmeta with moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if pfpGhostLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

def pfpGhostNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    pfpGhostMkToken
      (offsetPsiCode psi hpsi)
      (pfpGhostBitToFin (!sourceBit))
      (pfpGhostBitToFin sourceBit)
  else
    pfpGhostMkToken
      (offsetPsiCode psi hpsi)
      (pfpGhostBitToFin sourceBit)
      (0 : Fin 2)

def pfpGhostFinishMove
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
          pfpGhostMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          pfpGhostBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          pfpGhostMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          pfpGhostBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                pfpGhostNegTurnNext hpsi l.id t
              let b :=
                pfpGhostBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                pfpGhostMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                pfpGhostBumpTo kind l next gr0
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
              pfpGhostNegTurnNext hpsi l.id t
            let b :=
              pfpGhostBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              pfpGhostMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              pfpGhostBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

def pfpGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := pfpGhostLiveValue kind l
  let rv0 := pfpGhostLiveValue kind r
  let gl0 := pfpGhostLiveShadow kind l gl
  let gr0 := pfpGhostLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (pfpGhostBirth
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (pfpGhostBirth
            hpsi kind step site l.id).value
      else
        lv0
    let gl1 := born
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 :=
      if collide then none else lv1
    let gl2 :=
      if collide then none else gl1
    pfpGhostFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩


def pfpSelectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let pre :=
    pfpGhostPrelude hpsi
      (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      pfpGhostMoveToken
        hpsi .black step e
        pre.1 pre.2
        (ghostTokenAt .black G e)
        (ghostTokenAt .black G rsite)
  | .white =>
      let qb :=
        pprimeMoveToken hpsi .black pre.1 pre.2
      pfpGhostMoveToken
        hpsi .white step e
        qb.1 qb.2
        (ghostTokenAt .white G e)
        (ghostTokenAt .white G rsite)

theorem pfpSelectedPair_eq
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (step : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (kind : TokenKind) :
    ghostStepSelectedPair_prime hpsi ring step G e kind =
      pfpSelectedPair hpsi ring step G e kind := by
  cases kind <;> rfl

/-! ## 2. Lineage provenance through one prime ghost MoveToken -/

/-- Every owner of lineage `id` in `g` has birth site `k`. -/
def PfpGood {n psi : Nat}
    (id : LineageId n) (k : Fin n) (g : Option (GhostToken n psi)) : Prop :=
  ∀ z, g = some z → z.lmeta.id = id → z.lmeta.birthSite = k

theorem pfpGood_none {n psi : Nat}
    (id : LineageId n) (k : Fin n) :
    PfpGood (psi := psi) id k none := by
  intro z hz _
  simp at hz

theorem pfpPreGood
    {n psi kappa : Nat} {kind : TokenKind} {step : Nat}
    {G : GhostConfig n psi kappa} {i k : Fin n} {z : GhostToken n psi}
    (hu : GhostIdsUniqueAt step G)
    (ho : ghostTokenAt kind G i = some z)
    (hf : FreshAt kind k z.lmeta)
    (site : Fin n) :
    PfpGood z.lmeta.id k (ghostTokenAt kind G site) := by
  rcases hf with ⟨t, hb, hs⟩
  intro u hu0 hid
  have hsi : site = i := hu.1 kind site i u z hu0 ho hid
  subst site
  rw [ho] at hu0
  have hzu : z = u := Option.some.inj hu0
  subst u
  exact hs

private theorem pfpGood_ite {n psi : Nat}
    {id : LineageId n} {k : Fin n} (c : Prop) [Decidable c]
    {a b : Option (GhostToken n psi)}
    (ha : PfpGood id k a) (hb : PfpGood id k b) :
    PfpGood id k (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact ha
  · rw [if_neg hc]
    exact hb

private theorem pfpBirthGood
    {n psi : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (step t : Nat) (site k : Fin n) (idBit : Bool)
    (id : LineageId n) (hid : id = .born kind t) (hlt : t < step) :
    PfpGood id k (some (pfpGhostBirth hpsi kind step site idBit)) := by
  intro u hu huid
  have hbu : pfpGhostBirth hpsi kind step site idBit = u :=
    Option.some.inj hu
  subst u
  have heq : (LineageId.born kind step : LineageId n) = .born kind t := by
    calc
      .born kind step =
          (pfpGhostBirth hpsi kind step site idBit).lmeta.id := by rfl
      _ = id := huid
      _ = .born kind t := hid
  have hst : step = t := by
    cases heq
    rfl
  exfalso
  omega

private theorem pfpShadowGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (kind : TokenKind) (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hg : PfpGood id k g) :
    PfpGood id k (pfpGhostLiveShadow kind q g) := by
  intro z hz hid
  cases g with
  | none => simp [pfpGhostLiveShadow] at hz
  | some z0 =>
      cases ht : tokenAt kind q with
      | none => simp [pfpGhostLiveShadow, ht] at hz
      | some t =>
          by_cases hv : z0.value = t ∧ pfpGhostLocalValid kind q t
          · have heq : z0 = z := by
              simpa [pfpGhostLiveShadow, ht, hv] using hz
            subst z
            exact hg z0 rfl hid
          · simp [pfpGhostLiveShadow, ht, hv] at hz

private theorem pfpBumpGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (kind : TokenKind) (q : State psi kappa) (v : TokenData psi)
    (g : Option (GhostToken n psi))
    (hg : PfpGood id k g) :
    PfpGood id k (pfpGhostBumpTo kind q v g).live := by
  intro z hz hid
  cases g with
  | none => simp [pfpGhostBumpTo] at hz
  | some z0 =>
      by_cases hv : pfpGhostLocalValid kind q v
      · simp only [pfpGhostBumpTo, if_pos hv, Option.some.injEq] at hz
        subst z
        have hid0 : z0.lmeta.id = id := by
          simpa using hid
        have hs := hg z0 rfl hid0
        simpa using hs
      · simp [pfpGhostBumpTo, hv] at hz

private theorem pfpFinishGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (hpsi : 2 ≤ psi) (kind : TokenKind) (l r : State psi kappa)
    (lv rv : Option (TokenData psi)) (gl gr : Option (GhostToken n psi))
    (hgl : PfpGood id k gl) (hgr : PfpGood id k gr) :
    PfpGood id k (pfpGhostFinishMove hpsi kind l r lv rv gl gr).left ∧
      PfpGood id k (pfpGhostFinishMove hpsi kind l r lv rv gl gr).right := by
  cases lv with
  | none =>
      cases rv with
      | none => exact ⟨hgl, hgr⟩
      | some t =>
          by_cases h1 : decodeOffset psi (tokenCode t) = -1
          · simp only [pfpGhostFinishMove, dif_pos h1]
            exact ⟨pfpBumpGood id k kind l _ gr hgr, pfpGood_none id k⟩
          · by_cases h2 : decodeOffset psi (tokenCode t) ≤ -2
            · simp only [pfpGhostFinishMove, dif_neg h1, dif_pos h2]
              exact ⟨pfpBumpGood id k kind l _ gr hgr, pfpGood_none id k⟩
            · simp only [pfpGhostFinishMove, dif_neg h1, dif_neg h2]
              exact ⟨hgl, hgr⟩
  | some t =>
      by_cases h1 : decodeOffset psi (tokenCode t) = 1
      · simp only [pfpGhostFinishMove, dif_pos h1]
        exact ⟨pfpGood_none id k, pfpBumpGood id k kind r _ gl hgl⟩
      · by_cases h2 : 2 ≤ decodeOffset psi (tokenCode t)
        · simp only [pfpGhostFinishMove, dif_neg h1, dif_pos h2]
          exact ⟨pfpGood_none id k, pfpBumpGood id k kind r _ gl hgl⟩
        · cases rv with
          | none =>
              simp only [pfpGhostFinishMove, dif_neg h1, dif_neg h2]
              exact ⟨hgl, hgr⟩
          | some tr =>
              by_cases hm1 : decodeOffset psi (tokenCode tr) = -1
              · simp only [pfpGhostFinishMove, dif_neg h1, dif_neg h2,
                  dif_pos hm1]
                exact ⟨pfpBumpGood id k kind l _ gr hgr, pfpGood_none id k⟩
              · by_cases hm2 : decodeOffset psi (tokenCode tr) ≤ -2
                · simp only [pfpGhostFinishMove, dif_neg h1, dif_neg h2,
                    dif_neg hm1, dif_pos hm2]
                  exact ⟨pfpBumpGood id k kind l _ gr hgr, pfpGood_none id k⟩
                · simp only [pfpGhostFinishMove, dif_neg h1, dif_neg h2,
                    dif_neg hm1, dif_neg hm2]
                  exact ⟨hgl, hgr⟩

private theorem pfpMoveGood
    {n psi kappa : Nat} (id : LineageId n) (k : Fin n)
    (hpsi : 2 ≤ psi) (kind : TokenKind) (step t : Nat) (site : Fin n)
    (l r : State psi kappa) (gl gr : Option (GhostToken n psi))
    (hid : id = .born kind t) (hlt : t < step)
    (hgl : PfpGood id k gl) (hgr : PfpGood id k gr) :
    PfpGood id k (pfpGhostMoveToken hpsi kind step site l r gl gr).left ∧
      PfpGood id k (pfpGhostMoveToken hpsi kind step site l r gl gr).right := by
  have hgl0 := pfpShadowGood id k kind l gl hgl
  have hgr0 := pfpShadowGood id k kind r gr hgr
  unfold pfpGhostMoveToken
  by_cases hlast : l.last = false ∧ r.last = false
  · rw [dif_pos hlast]
    apply pfpFinishGood
    · exact pfpGood_ite _ (pfpGood_none id k)
        (pfpGood_ite _ (pfpBirthGood hpsi kind step t site k l.id id hid hlt)
          hgl0)
    · exact hgr0
  · rw [dif_neg hlast]
    exact ⟨hgl0, hgr0⟩

/-- Both selected-pair outputs of a prime ghost step keep the birth site of a
fresh lineage (IDs unique before the step). -/
theorem pfpSelectedPairGood
    {n psi kappa : Nat} (hpsi : 2 ≤ psi) (ring : DirectedRing n)
    (kind : TokenKind) (step : Nat) (G : GhostConfig n psi kappa)
    (e i k : Fin n) (z : GhostToken n psi)
    (hu : GhostIdsUniqueAt step G)
    (ho : ghostTokenAt kind G i = some z)
    (hf : FreshAt kind k z.lmeta) :
    PfpGood z.lmeta.id k
        (ghostStepSelectedPair_prime hpsi ring step G e kind).left ∧
      PfpGood z.lmeta.id k
        (ghostStepSelectedPair_prime hpsi ring step G e kind).right := by
  rcases hf with ⟨t, hb, hs⟩
  have hlt : t < step := hu.2 kind i z kind t ho hb
  have hgl := pfpPreGood hu ho ⟨t, hb, hs⟩ e
  have hgr := pfpPreGood hu ho ⟨t, hb, hs⟩ (ring.rightNeighbor e)
  rw [pfpSelectedPair_eq hpsi ring step G e kind]
  cases kind with
  | black =>
      exact pfpMoveGood z.lmeta.id k hpsi .black step t e _ _
        _ _ hb hlt hgl hgr
  | white =>
      exact pfpMoveGood z.lmeta.id k hpsi .white step t e _ _
        _ _ hb hlt hgl hgr

/-! ## 3. Fresh-lineage persistence -/

/--
`FreshLineagePersistenceStep primeRunner`: under lineage-ID uniqueness, an
in-window same-ID successor of a fresh owner after one prime ghost step is
again fresh.  Proof as in the ordinary case: off the pair the owner is a
pre-step owner, identified with the fresh one by ID uniqueness; on the pair
the mirrored MoveToken keeps birth site and ID, and a new birth has a newer ID.
-/
theorem prime_freshLineagePersistenceStep :
    FreshLineagePersistenceStep primeRunner := by
  intro n psi kappa hpsi ring k kind step G e i j z z'
  intro hu _ ho hf _ hpost hid
  change ghostTokenAt kind (ghostStepPrime hpsi ring step G e) j = some z'
    at hpost
  rcases hf with ⟨t, hb, hs⟩
  have hpair := pfpSelectedPairGood hpsi ring kind step G e i k z
    hu ho ⟨t, hb, hs⟩
  refine ⟨t, hid.trans hb, ?_⟩
  by_cases hje : j = e
  · subst j
    exact hpair.1 z'
      ((ghostTokenAt_ghostStep_initiator_prime
        hpsi ring step G e kind).symm.trans hpost)
      hid
  · by_cases hjr : j = ring.rightNeighbor e
    · subst j
      have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact hje h
      exact hpair.2 z'
        ((ghostTokenAt_ghostStep_responder_of_ne_prime
          hpsi ring step G e kind hne).symm.trans hpost) hid
    · have hpre :=
        (ghostTokenAt_ghostStep_frame_prime
          hpsi ring step G e j kind hje hjr).symm.trans hpost
      exact (pfpPreGood hu ho ⟨t, hb, hs⟩ j) z' hpre hid

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.prime_freshLineagePersistenceStep
