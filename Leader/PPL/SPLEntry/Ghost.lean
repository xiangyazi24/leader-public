import Leader.PPL.SPLEntry.ForcingWord
import Leader.PPL.TokenCorrectness.Persistence
import Lean

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false

open PPL
open PPL.Probability

/-! ## Prime-local mirror of the ordinary token ghost bookkeeping -/

private def primeGhostBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def primeGhostMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def primeGhostLocalValid
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

private instance instDecidablePrimeGhostLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (primeGhostLocalValid kind q t) := by
  unfold primeGhostLocalValid
  infer_instance

/--
The pre-Algorithm-3 pair for P_PL prime.

This is the prefix of pprimeCreateLeader through Algorithm-2 line 9:
DetermineMode is literal, line 6 is suppressed, the line-4 distance is always
written, then last is updated from that written responder.
-/
private def primeGhostPrelude
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

private def primeGhostLiveShadow
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
              primeGhostLocalValid kind q t then
            some z
          else
            none

private def primeGhostLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if primeGhostLocalValid kind q t then
        some t
      else
        none

private def primeGhostBirth
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      primeGhostMkToken
        (offsetPsiCode psi hpsi)
        (primeGhostBitToFin (!idBit))
        (primeGhostBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def primeGhostBumpTo
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
        if primeGhostLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def primeGhostNegTurnNext
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    primeGhostMkToken
      (offsetPsiCode psi hpsi)
      (primeGhostBitToFin (!sourceBit))
      (primeGhostBitToFin sourceBit)
  else
    primeGhostMkToken
      (offsetPsiCode psi hpsi)
      (primeGhostBitToFin sourceBit)
      (0 : Fin 2)

private def primeGhostFinishMove
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
          primeGhostMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          primeGhostBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 ≤ c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          primeGhostMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          primeGhostBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                primeGhostNegTurnNext hpsi l.id t
              let b :=
                primeGhostBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c ≤ -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                primeGhostMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                primeGhostBumpTo kind l next gr0
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
              primeGhostNegTurnNext hpsi l.id t
            let b :=
              primeGhostBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              primeGhostMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              primeGhostBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def primeGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := primeGhostLiveValue kind l
  let rv0 := primeGhostLiveValue kind r
  let gl0 := primeGhostLiveShadow kind l gl
  let gr0 := primeGhostLiveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (primeGhostBirth
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (primeGhostBirth
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
    primeGhostFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def primeGhostSetTwo
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
Selected-colour prime ghost update.

For white, the local states are the actual result of the prime black
MoveToken call, so the forced-Construct responder id write is visible to the
second colour exactly when the executable prime transition sees it.
-/
def ghostStepSelectedPair_prime
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
    primeGhostPrelude hpsi
      (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      primeGhostMoveToken
        hpsi .black step e
        pre.1 pre.2
        (ghostTokenAt .black G e)
        (ghostTokenAt .black G rsite)
  | .white =>
      let qb :=
        pprimeMoveToken hpsi .black pre.1 pre.2
      primeGhostMoveToken
        hpsi .white step e
        qb.1 qb.2
        (ghostTokenAt .white G e)
        (ghostTokenAt .white G rsite)

/--
One proof-only P_PL-prime step.  The physical row is exactly pprimeStep;
birth, shadowing, bumpTo, move counting and completion logging are the same
ghost operations as in the ordinary runner.
-/
def ghostStepPrime
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let gb :=
    ghostStepSelectedPair_prime
      hpsi ring step G e .black
  let gw :=
    ghostStepSelectedPair_prime
      hpsi ring step G e .white
  { phys := pprimeStep ring G.phys e
    black :=
      primeGhostSetTwo
        G.black e rsite gb.left gb.right
    white :=
      primeGhostSetTwo
        G.white e rsite gw.left gw.right
    completed :=
      G.completed ++ gb.done ++ gw.done }

def ghostRunPrime
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) :
    Nat →
      GhostConfig n psi kappa →
      DetSchedule n →
      GhostConfig n psi kappa
  | _, G, [] => G
  | t, G, e :: es =>
      ghostRunPrime hpsi ring (t + 1)
        (ghostStepPrime hpsi ring t G e) es

theorem ghostStepPrime_phys
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n) :
    (ghostStepPrime hpsi ring step G e).phys =
      pprimeStep ring G.phys e := by
  rfl

theorem ghostRunPrime_phys
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (t : Nat)
    (G : GhostConfig n psi kappa)
    (sched : DetSchedule n) :
    (ghostRunPrime hpsi ring t G sched).phys =
      runPPrime ring G.phys sched := by
  induction sched generalizing t G with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [ghostRunPrime, runPPrime]
      simpa only [ghostStepPrime_phys] using
        ih (t := t + 1)
          (G := ghostStepPrime hpsi ring t G e)

/-! ## Prime ghost-step export surface -/

private theorem ghostTokenAt_ghostStepPrime_eq_setTwo
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStepPrime hpsi ring step G e) i =
      primeGhostSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (ghostStepSelectedPair_prime
          hpsi ring step G e kind).left
        (ghostStepSelectedPair_prime
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl

theorem ghostTokenAt_ghostStep_frame_prime
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e j : Fin n)
    (kind : TokenKind)
    (hje : j ≠ e)
    (hjr : j ≠ ring.rightNeighbor e) :
    ghostTokenAt kind
        (ghostStepPrime hpsi ring step G e) j =
      ghostTokenAt kind G j := by
  rw [ghostTokenAt_ghostStepPrime_eq_setTwo
    hpsi ring step G e kind j]
  simp [primeGhostSetTwo, hje, hjr]

theorem ghostTokenAt_ghostStep_initiator_prime
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ghostTokenAt kind
        (ghostStepPrime hpsi ring step G e) e =
      (ghostStepSelectedPair_prime
        hpsi ring step G e kind).left := by
  rw [ghostTokenAt_ghostStepPrime_eq_setTwo
    hpsi ring step G e kind e]
  simp [primeGhostSetTwo]

theorem ghostTokenAt_ghostStep_responder_of_ne_prime
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ghostTokenAt kind
        (ghostStepPrime hpsi ring step G e)
        (ring.rightNeighbor e) =
      (ghostStepSelectedPair_prime
        hpsi ring step G e kind).right := by
  rw [ghostTokenAt_ghostStepPrime_eq_setTwo
    hpsi ring step G e kind
      (ring.rightNeighbor e)]
  simp [primeGhostSetTwo, hne]

/-! ## Initial and one-step lineage-ID uniqueness -/

theorem ghostIdsUnique_initial_prime
    {n psi kappa : Nat}
    (C : Config n psi kappa) :
    GhostIdsUniqueAt 0 (initialGhost C) := by
  exact PPL.ghostIdsUnique_initial C

private def PrimeOptDisjoint
    {n psi : Nat}
    (a b : Option (GhostToken n psi)) : Prop :=
  ∀ za zb,
    a = some za →
    b = some zb →
    za.lmeta.id ≠ zb.lmeta.id

private def PrimeOptBefore
    {n psi : Nat}
    (t : Nat)
    (a : Option (GhostToken n psi)) : Prop :=
  ∀ z bornKind s,
    a = some z →
    z.lmeta.id = .born bornKind s →
    s < t

private def PrimeOptFrom
    {n psi : Nat}
    (a b : Option (GhostToken n psi)) : Prop :=
  ∀ z,
    b = some z →
    ∃ z0,
      a = some z0 ∧
      z.lmeta.id = z0.lmeta.id

private theorem primeShadow_from
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi)) :
    PrimeOptFrom g
      (primeGhostLiveShadow kind q g) := by
  intro z hz
  cases g with
  | none =>
      simp [primeGhostLiveShadow] at hz
  | some z0 =>
      unfold primeGhostLiveShadow at hz
      split at hz <;> simp_all
      all_goals
        split at hz <;> simp_all

private theorem primeBump_from
    {n psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi)
    (g : Option (GhostToken n psi)) :
    PrimeOptFrom g
      (primeGhostBumpTo kind q t g).live := by
  intro z hz
  cases g with
  | none =>
      simp [primeGhostBumpTo] at hz
  | some z0 =>
      unfold primeGhostBumpTo at hz
      split at hz <;> simp_all
      all_goals
        cases hz.2 <;> rfl

private theorem primeBefore_of_from
    {n psi : Nat}
    {t : Nat}
    {a b : Option (GhostToken n psi)}
    (hf : PrimeOptFrom a b)
    (ha : PrimeOptBefore t a) :
    PrimeOptBefore t b := by
  intro z bornKind s hz hid
  obtain ⟨z0, h0, hsame⟩ := hf z hz
  apply ha z0 bornKind s h0
  exact hsame.symm.trans hid

private theorem primeDisjoint_of_from
    {n psi : Nat}
    {a b c d : Option (GhostToken n psi)}
    (hac : PrimeOptFrom a c)
    (hbd : PrimeOptFrom b d)
    (hab : PrimeOptDisjoint a b) :
    PrimeOptDisjoint c d := by
  intro zc zd hc hd heq
  obtain ⟨za, ha, hza⟩ := hac zc hc
  obtain ⟨zb, hb, hzb⟩ := hbd zd hd
  exact
    hab za zb ha hb
      (hza.symm.trans (heq.trans hzb))

private theorem primeFrom_refl
    {n psi : Nat}
    (a : Option (GhostToken n psi)) :
    PrimeOptFrom a a := by
  intro z hz
  exact ⟨z, hz, rfl⟩

private theorem primeBefore_succ
    {n psi : Nat}
    {t : Nat}
    {a : Option (GhostToken n psi)}
    (ha : PrimeOptBefore t a) :
    PrimeOptBefore (t + 1) a := by
  intro z kind s hz hid
  have hs := ha z kind s hz hid
  omega

private theorem primeBirth_before
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    PrimeOptBefore (step + 1)
      (some
        (primeGhostBirth
          hpsi kind step site idBit)) := by
  intro z bornKind s hz hid
  cases hz
  simp [primeGhostBirth] at hid
  cases hid
  omega

private theorem primeBirth_disjoint_old
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool)
    (a : Option (GhostToken n psi))
    (ha : PrimeOptBefore step a) :
    PrimeOptDisjoint
      (some
        (primeGhostBirth
          hpsi kind step site idBit))
      a := by
  intro za zb hz hb heq
  cases hz
  have hs := ha zb kind step hb
  apply Nat.lt_irrefl step
  apply hs
  simpa [primeGhostBirth] using heq.symm

private theorem primeFinishMove_good
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (step : Nat)
    (hdis : PrimeOptDisjoint gl2 gr0)
    (hbl : PrimeOptBefore (step + 1) gl2)
    (hbr : PrimeOptBefore (step + 1) gr0) :
    let q :=
      primeGhostFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0
    PrimeOptDisjoint q.left q.right ∧
      PrimeOptBefore (step + 1) q.left ∧
      PrimeOptBefore (step + 1) q.right := by
  have hnone :
      PrimeOptBefore (step + 1)
        (none : Option (GhostToken n psi)) := by
    intro z bk s hz _
    simp at hz
  have hright :
      ∀ (dest : State psi kappa)
        (v : TokenData psi),
      PrimeOptDisjoint
          (none : Option (GhostToken n psi))
          (primeGhostBumpTo
            kind dest v gl2).live ∧
        PrimeOptBefore (step + 1)
          (none : Option (GhostToken n psi)) ∧
        PrimeOptBefore (step + 1)
          (primeGhostBumpTo
            kind dest v gl2).live := by
    intro dest v
    refine ⟨?_, hnone, ?_⟩
    · intro za zb ha _ _
      simp at ha
    · exact
        primeBefore_of_from
          (primeBump_from
            kind dest v gl2)
          hbl
  have hleft :
      ∀ (dest : State psi kappa)
        (v : TokenData psi),
      PrimeOptDisjoint
          (primeGhostBumpTo
            kind dest v gr0).live
          (none : Option (GhostToken n psi)) ∧
        PrimeOptBefore (step + 1)
          (primeGhostBumpTo
            kind dest v gr0).live ∧
        PrimeOptBefore (step + 1)
          (none : Option (GhostToken n psi)) := by
    intro dest v
    refine ⟨?_, ?_, hnone⟩
    · intro za zb _ hb _
      simp at hb
    · exact
        primeBefore_of_from
          (primeBump_from
            kind dest v gr0)
          hbr
  dsimp only
  unfold primeGhostFinishMove
  repeat' (first | split <;> try dsimp only)
  all_goals first
    | exact ⟨hdis, hbl, hbr⟩
    | exact hright _ _
    | exact hleft _ _

private theorem primeFinishMove_external
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 ext :
      Option (GhostToken n psi))
    (hdl : PrimeOptDisjoint gl2 ext)
    (hdr : PrimeOptDisjoint gr0 ext) :
    let q :=
      primeGhostFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0
    PrimeOptDisjoint q.left ext ∧
      PrimeOptDisjoint q.right ext := by
  have hnone :
      PrimeOptDisjoint
        (none : Option (GhostToken n psi))
        ext := by
    intro za zb ha _ _
    simp at ha
  have hright :
      ∀ (dest : State psi kappa)
        (v : TokenData psi),
      PrimeOptDisjoint
          (none : Option (GhostToken n psi))
          ext ∧
        PrimeOptDisjoint
          (primeGhostBumpTo
            kind dest v gl2).live
          ext := by
    intro dest v
    exact
      ⟨hnone,
        primeDisjoint_of_from
          (primeBump_from
            kind dest v gl2)
          (primeFrom_refl ext)
          hdl⟩
  have hleft :
      ∀ (dest : State psi kappa)
        (v : TokenData psi),
      PrimeOptDisjoint
          (primeGhostBumpTo
            kind dest v gr0).live
          ext ∧
        PrimeOptDisjoint
          (none : Option (GhostToken n psi))
          ext := by
    intro dest v
    exact
      ⟨primeDisjoint_of_from
          (primeBump_from
            kind dest v gr0)
          (primeFrom_refl ext)
          hdr,
        hnone⟩
  dsimp only
  unfold primeGhostFinishMove
  repeat' (first | split <;> try dsimp only)
  all_goals first
    | exact ⟨hdl, hdr⟩
    | exact hright _ _
    | exact hleft _ _

private theorem primeGhostMove_good
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hdis : PrimeOptDisjoint gl gr)
    (hbl : PrimeOptBefore step gl)
    (hbr : PrimeOptBefore step gr) :
    let q :=
      primeGhostMoveToken
        hpsi kind step site l r gl gr
    PrimeOptDisjoint q.left q.right ∧
      PrimeOptBefore (step + 1) q.left ∧
      PrimeOptBefore (step + 1) q.right := by
  let gl0 :=
    primeGhostLiveShadow kind l gl
  let gr0 :=
    primeGhostLiveShadow kind r gr
  have hgl0 :=
    primeShadow_from kind l gl
  have hgr0 :=
    primeShadow_from kind r gr
  have hdis0 :
      PrimeOptDisjoint gl0 gr0 :=
    primeDisjoint_of_from
      hgl0 hgr0 hdis
  have hbl0 :
      PrimeOptBefore step gl0 :=
    primeBefore_of_from hgl0 hbl
  have hbr0 :
      PrimeOptBefore step gr0 :=
    primeBefore_of_from hgr0 hbr
  by_cases hlast :
      l.last = false ∧ r.last = false
  · let rv0 :=
      primeGhostLiveValue kind r
    let lv0 :=
      primeGhostLiveValue kind l
    let birth :=
      primeGhostBirth
        hpsi kind step site l.id
    let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let gl1 :=
      if hb then some birth else gl0
    let lv1 :=
      if hb then some birth.value else lv0
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let gl2 :=
      if collide then none else gl1
    let lv2 :=
      if collide then none else lv1
    have hbl1 :
        PrimeOptBefore (step + 1) gl1 := by
      by_cases h : hb
      · simpa [gl1, h, birth] using
          primeBirth_before
            hpsi kind step site l.id
      · simpa [gl1, h] using
          primeBefore_succ hbl0
    have hdis1 :
        PrimeOptDisjoint gl1 gr0 := by
      by_cases h : hb
      · simpa [gl1, h, birth] using
          primeBirth_disjoint_old
            hpsi kind step site l.id
            gr0 hbr0
      · simpa [gl1, h] using hdis0
    have hbl2 :
        PrimeOptBefore (step + 1) gl2 := by
      by_cases h : collide
      · intro z bk s hz _
        simp [gl2, h] at hz
      · simpa [gl2, h] using hbl1
    have hdis2 :
        PrimeOptDisjoint gl2 gr0 := by
      by_cases h : collide
      · intro za zb ha _ _
        simp [gl2, h] at ha
      · simpa [gl2, h] using hdis1
    have hq :
        primeGhostMoveToken
            hpsi kind step site l r gl gr =
          primeGhostFinishMove
            hpsi kind l r
            lv2 rv0 gl2 gr0 := by
      simp only
        [primeGhostMoveToken, if_pos hlast, dif_pos hlast]
      rfl
    dsimp only
    rw [hq]
    exact
      primeFinishMove_good
        hpsi kind l r
        lv2 rv0 gl2 gr0 step
        hdis2 hbl2
        (primeBefore_succ hbr0)
  · have hq :
        primeGhostMoveToken
            hpsi kind step site l r gl gr =
          (⟨gl0, gr0, []⟩ :
            GhostMoveResult n psi) := by
      simp
        [primeGhostMoveToken,
          hlast, gl0, gr0]
    dsimp only
    rw [hq]
    exact
      ⟨hdis0,
        primeBefore_succ hbl0,
        primeBefore_succ hbr0⟩

private theorem primeGhostMove_external
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr ext :
      Option (GhostToken n psi))
    (hdl : PrimeOptDisjoint gl ext)
    (hdr : PrimeOptDisjoint gr ext)
    (hbe : PrimeOptBefore step ext) :
    let q :=
      primeGhostMoveToken
        hpsi kind step site l r gl gr
    PrimeOptDisjoint q.left ext ∧
      PrimeOptDisjoint q.right ext := by
  let gl0 :=
    primeGhostLiveShadow kind l gl
  let gr0 :=
    primeGhostLiveShadow kind r gr
  have hgl0 :=
    primeShadow_from kind l gl
  have hgr0 :=
    primeShadow_from kind r gr
  have hdl0 :
      PrimeOptDisjoint gl0 ext :=
    primeDisjoint_of_from
      hgl0 (primeFrom_refl ext) hdl
  have hdr0 :
      PrimeOptDisjoint gr0 ext :=
    primeDisjoint_of_from
      hgr0 (primeFrom_refl ext) hdr
  by_cases hlast :
      l.last = false ∧ r.last = false
  · let rv0 :=
      primeGhostLiveValue kind r
    let lv0 :=
      primeGhostLiveValue kind l
    let birth :=
      primeGhostBirth
        hpsi kind step site l.id
    let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let gl1 :=
      if hb then some birth else gl0
    let lv1 :=
      if hb then some birth.value else lv0
    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let gl2 :=
      if collide then none else gl1
    let lv2 :=
      if collide then none else lv1
    have hdl1 :
        PrimeOptDisjoint gl1 ext := by
      by_cases h : hb
      · simpa [gl1, h, birth] using
          primeBirth_disjoint_old
            hpsi kind step site l.id
            ext hbe
      · simpa [gl1, h] using hdl0
    have hdl2 :
        PrimeOptDisjoint gl2 ext := by
      by_cases h : collide
      · intro za zb ha _ _
        simp [gl2, h] at ha
      · simpa [gl2, h] using hdl1
    have hq :
        primeGhostMoveToken
            hpsi kind step site l r gl gr =
          primeGhostFinishMove
            hpsi kind l r
            lv2 rv0 gl2 gr0 := by
      simp only
        [primeGhostMoveToken, if_pos hlast, dif_pos hlast]
      rfl
    dsimp only
    rw [hq]
    exact
      primeFinishMove_external
        hpsi kind l r
        lv2 rv0 gl2 gr0 ext
        hdl2 hdr0
  · have hq :
        primeGhostMoveToken
            hpsi kind step site l r gl gr =
          (⟨gl0, gr0, []⟩ :
            GhostMoveResult n psi) := by
      simp
        [primeGhostMoveToken,
          hlast, gl0, gr0]
    dsimp only
    rw [hq]
    exact ⟨hdl0, hdr0⟩

private theorem primeSelectedPair_good
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hdis :
      PrimeOptDisjoint
        (ghostTokenAt kind G e)
        (ghostTokenAt kind G
          (ring.rightNeighbor e)))
    (hbl :
      PrimeOptBefore step
        (ghostTokenAt kind G e))
    (hbr :
      PrimeOptBefore step
        (ghostTokenAt kind G
          (ring.rightNeighbor e))) :
    let q :=
      ghostStepSelectedPair_prime
        hpsi ring step G e kind
    PrimeOptDisjoint q.left q.right ∧
      PrimeOptBefore (step + 1) q.left ∧
      PrimeOptBefore (step + 1) q.right := by
  unfold ghostStepSelectedPair_prime
  cases kind <;> dsimp only
  all_goals
    apply primeGhostMove_good <;> assumption

private theorem primeSelectedPair_external
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (ext : Option (GhostToken n psi))
    (hdl :
      PrimeOptDisjoint
        (ghostTokenAt kind G e) ext)
    (hdr :
      PrimeOptDisjoint
        (ghostTokenAt kind G
          (ring.rightNeighbor e))
        ext)
    (hbe : PrimeOptBefore step ext) :
    let q :=
      ghostStepSelectedPair_prime
        hpsi ring step G e kind
    PrimeOptDisjoint q.left ext ∧
      PrimeOptDisjoint q.right ext := by
  unfold ghostStepSelectedPair_prime
  cases kind <;> dsimp only
  all_goals
    apply primeGhostMove_external <;> assumption

private theorem rightNeighbor_ne_self_primeGhost
    {n : Nat}
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (i : Fin n) :
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

theorem ghostIdsUnique_step_prime
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hU : GhostIdsUniqueAt step G) :
    GhostIdsUniqueAt (step + 1)
      (ghostStepPrime hpsi ring step G e) := by
  classical
  rcases hU with ⟨huniq, hbefore⟩
  have hne :
      ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_primeGhost
      hn2 ring e
  constructor
  · intro kind i j zi zj hi hj hid
    rw [ghostTokenAt_ghostStepPrime_eq_setTwo
      hpsi ring step G e kind i] at hi
    rw [ghostTokenAt_ghostStepPrime_eq_setTwo
      hpsi ring step G e kind j] at hj

    have hpair :
        PrimeOptDisjoint
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e)) := by
      intro a b ha hb hab
      have heq :=
        huniq kind e
          (ring.rightNeighbor e)
          a b ha hb hab
      exact hne heq.symm

    have hbe :
        PrimeOptBefore step
          (ghostTokenAt kind G e) := by
      intro z bornKind s hz hs
      exact
        hbefore kind e z
          bornKind s hz hs

    have hbr :
        PrimeOptBefore step
          (ghostTokenAt kind G
            (ring.rightNeighbor e)) := by
      intro z bornKind s hz hs
      exact
        hbefore kind
          (ring.rightNeighbor e)
          z bornKind s hz hs

    have hgood :=
      primeSelectedPair_good
        hpsi ring step G e kind
        hpair hbe hbr
    dsimp only at hgood

    have hext :
        ∀ x : Fin n,
          x ≠ e →
          x ≠ ring.rightNeighbor e →
          let q :=
            ghostStepSelectedPair_prime
              hpsi ring step G e kind
          PrimeOptDisjoint q.left
              (ghostTokenAt kind G x) ∧
            PrimeOptDisjoint q.right
              (ghostTokenAt kind G x) := by
      intro x hxe hxr
      have hdl :
          PrimeOptDisjoint
            (ghostTokenAt kind G e)
            (ghostTokenAt kind G x) := by
        intro a b ha hb hab
        have heq :=
          huniq kind e x
            a b ha hb hab
        exact hxe heq.symm
      have hdr :
          PrimeOptDisjoint
            (ghostTokenAt kind G
              (ring.rightNeighbor e))
            (ghostTokenAt kind G x) := by
        intro a b ha hb hab
        have heq :=
          huniq kind
            (ring.rightNeighbor e)
            x a b ha hb hab
        exact hxr heq.symm
      have hbx :
          PrimeOptBefore step
            (ghostTokenAt kind G x) := by
        intro z bornKind s hz hs
        exact
          hbefore kind x z
            bornKind s hz hs
      exact
        primeSelectedPair_external
          hpsi ring step G e kind
          (ghostTokenAt kind G x)
          hdl hdr hbx

    by_cases hie : i = e
    · subst i
      simp [primeGhostSetTwo] at hi
      by_cases hje : j = e
      · exact hje.symm
      · by_cases hjr :
          j = ring.rightNeighbor e
        · subst j
          simp
            [primeGhostSetTwo, hne] at hj
          exfalso
          exact
            (hgood.1 zi zj hi hj) hid
        · simp
            [primeGhostSetTwo,
              hje, hjr] at hj
          have hx := hext j hje hjr
          dsimp only at hx
          exfalso
          exact
            (hx.1 zi zj hi hj) hid
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        simp
          [primeGhostSetTwo, hne] at hi
        by_cases hje : j = e
        · subst j
          simp [primeGhostSetTwo] at hj
          exfalso
          exact
            (hgood.1 zj zi hj hi)
              hid.symm
        · by_cases hjr :
            j = ring.rightNeighbor e
          · exact hjr.symm
          · simp
              [primeGhostSetTwo,
                hje, hjr] at hj
            have hx := hext j hje hjr
            dsimp only at hx
            exfalso
            exact
              (hx.2 zi zj hi hj) hid
      · simp
          [primeGhostSetTwo,
            hie, hir] at hi
        by_cases hje : j = e
        · subst j
          simp [primeGhostSetTwo] at hj
          have hx := hext i hie hir
          dsimp only at hx
          exfalso
          exact
            (hx.1 zj zi hj hi)
              hid.symm
        · by_cases hjr :
            j = ring.rightNeighbor e
          · subst j
            simp
              [primeGhostSetTwo, hne] at hj
            have hx := hext i hie hir
            dsimp only at hx
            exfalso
            exact
              (hx.2 zj zi hj hi)
                hid.symm
          · simp
              [primeGhostSetTwo,
                hje, hjr] at hj
            exact
              huniq kind i j
                zi zj hi hj hid

  · intro kind i z bornKind s hi hid
    rw [ghostTokenAt_ghostStepPrime_eq_setTwo
      hpsi ring step G e kind i] at hi

    have hpair :
        PrimeOptDisjoint
          (ghostTokenAt kind G e)
          (ghostTokenAt kind G
            (ring.rightNeighbor e)) := by
      intro a b ha hb hab
      have heq :=
        huniq kind e
          (ring.rightNeighbor e)
          a b ha hb hab
      exact hne heq.symm

    have hbe :
        PrimeOptBefore step
          (ghostTokenAt kind G e) := by
      intro z0 bornKind0 s0 hz hs
      exact
        hbefore kind e z0
          bornKind0 s0 hz hs

    have hbr :
        PrimeOptBefore step
          (ghostTokenAt kind G
            (ring.rightNeighbor e)) := by
      intro z0 bornKind0 s0 hz hs
      exact
        hbefore kind
          (ring.rightNeighbor e)
          z0 bornKind0 s0 hz hs

    have hgood :=
      primeSelectedPair_good
        hpsi ring step G e kind
        hpair hbe hbr
    dsimp only at hgood

    by_cases hie : i = e
    · subst i
      simp [primeGhostSetTwo] at hi
      exact
        hgood.2.1 z bornKind s hi hid
    · by_cases hir :
        i = ring.rightNeighbor e
      · subst i
        simp
          [primeGhostSetTwo, hne] at hi
        exact
          hgood.2.2 z bornKind s hi hid
      · simp
          [primeGhostSetTwo,
            hie, hir] at hi
        have hs :=
          hbefore kind i z
            bornKind s hi hid
        omega

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.ghostStepPrime_phys
#print axioms PPL.Convergence.L18.ghostRunPrime_phys
#print axioms PPL.Convergence.L18.ghostStepSelectedPair_prime
#print axioms PPL.Convergence.L18.ghostTokenAt_ghostStep_frame_prime
#print axioms PPL.Convergence.L18.ghostTokenAt_ghostStep_initiator_prime
#print axioms PPL.Convergence.L18.ghostTokenAt_ghostStep_responder_of_ne_prime
#print axioms PPL.Convergence.L18.ghostIdsUnique_initial_prime
#print axioms PPL.Convergence.L18.ghostIdsUnique_step_prime
