import Leader.PPL.TokenCorrectness.Persistence
import Leader.PPL.TokenCompletion.HalfPowerDynamics
import Leader.PPL.TokenCompletion.RightmostRows

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
# Lemma 4 run facts

There are two independent run-history facts in this file.

1. Live lineage identifiers remain unique along an actual `ghostRun`.  The
   global birth clock carried by `ghostRun` is exactly the list-prefix
   length, so the closed run theorem ends at `pre.length`.

2. The literal all-run kinematics statement cannot use
   `lemma4TokenProgress` directly: that public rank reads the current
   physical `dist`, and Algorithm 2 may rewrite `dist` while a positive
   responder token is left in place by Algorithm 3.  The invariant that is
   actually intrinsic to the ghost lineage is the paper's token trajectory:

     * at a positive signed counter c, after q completed macro-turns,
         x = q + (psi - c)
         moves = q * (2*psi-1) + (psi-c);
     * at a negative signed counter c,
         x = q + |c| + 1
         moves = q * (2*psi-1) + (2*psi-1-|c|).

   Here x is an *unwrapped* clockwise displacement from the fresh lineage's
   birth site k.  The physical site is `shiftRight ring k x`.

This is the exact proof-level form of the paper fact "the token offset records
the number of moves since its birth".  It is stable under arbitrary physical
interactions because it mentions only the birth site, current ghost value and
ghost move counter.  In a C_d window, the canonical dist field identifies the
same q with `lemma4TokenStage`, so this is the run-history seam needed by the
rightmost rows.

At the last positive service, x = 2*psi-2 and c = 1.  The equations force
q = psi-1 and hence
  moves + 1 = 2*psi*psi - 2*psi + 1 = tokenTrajectoryMoves psi.
-/

/-! -------------------------------------------------------------------------
    1. Lineage-ID uniqueness on runs
------------------------------------------------------------------------- -/

private theorem ghostIdsUnique_run_from
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn2 : 2 <= n)
    (ring : DirectedRing n) :
    forall (t : Nat)
      (G : GhostConfig n psi kappa)
      (pre : DetSchedule n),
      GhostIdsUniqueAt t G ->
      GhostIdsUniqueAt (t + pre.length)
        (ghostRun hpsi ring t G pre) := by
  intro t G pre hU
  induction pre generalizing t G with
  | nil =>
      change GhostIdsUniqueAt t G
      exact hU
  | cons e es ih =>
      simp only [ghostRun, List.length_cons]
      have hstep :
          GhostIdsUniqueAt (t + 1)
            (ghostStep hpsi ring t G e) :=
        ghostIdsUnique_step hpsi hn2 ring t G e hU
      have htail :=
        ih (t := t + 1)
          (G := ghostStep hpsi ring t G e)
          hstep
      have harith :
          (t + 1) + es.length =
            t + (es.length + 1) := by
        omega
      rw [harith] at htail
      exact htail

theorem ghostIdsUnique_run
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn2 : 2 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n) :
    GhostIdsUniqueAt pre.length
      (ghostRun hpsi ring 0 (initialGhost C0) pre) := by
  have h :=
    ghostIdsUnique_run_from
      hpsi hn2 ring
      0 (initialGhost C0) pre
      (ghostIdsUnique_initial C0)
  simpa using h

/-! -------------------------------------------------------------------------
    2. Intrinsic fresh-lineage trajectory
------------------------------------------------------------------------- -/

/--
Intrinsic trajectory coordinate for one fresh lineage.

The witness `q` counts completed negative-to-positive turns.  The natural
number `x` is not reduced modulo the ring size; that is deliberate.  It is
the number of clockwise edges from the birth site in the universal-cover
picture of the token trajectory.
-/
def Lemma4FreshTrajectoryPoint
    (psi moves x : Nat) (c : Int) : Prop :=
  (∃ q : Nat,
    0 < c ∧
      c.toNat <= psi ∧
        x = q + (psi - c.toNat) ∧
          moves =
            q * (2 * psi - 1) +
              (psi - c.toNat)) ∨
  (∃ q : Nat,
    c < 0 ∧
      c.natAbs < psi ∧
        x = q + c.natAbs + 1 ∧
          moves =
            q * (2 * psi - 1) +
              (2 * psi - 1 - c.natAbs))

/--
All live fresh owners have the intrinsic trajectory coordinate determined by
their ghost metadata and token value.
-/
def Lemma4FreshKinematics
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  forall (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi),
    ghostTokenAt kind G i = some z ->
    FreshAt kind k z.lmeta ->
    ∃ x : Nat,
      i = shiftRight ring k x ∧
        Lemma4FreshTrajectoryPoint
          psi z.lmeta.moves x
          (decodeOffset psi (tokenCode z.value))

private theorem runFacts_shiftRight_zero
    {n : Nat}
    (ring : DirectedRing n) (k : Fin n) :
    shiftRight ring k 0 = k := by
  apply Fin.ext
  simp [shiftRight, Nat.mod_eq_of_lt k.isLt]

private theorem runFacts_shiftRight_add
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) (a b : Nat) :
    shiftRight ring (shiftRight ring k a) b =
      shiftRight ring k (a + b) := by
  apply Fin.ext
  change
    (((k.val + a) % n + b) % n) =
      (k.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem runFacts_rightNeighbor_shiftRight
    {n : Nat}
    (ring : DirectedRing n)
    (k : Fin n) (x : Nat) :
    ring.rightNeighbor (shiftRight ring k x) =
      shiftRight ring k (x + 1) := by
  change
    shiftRight ring (shiftRight ring k x) 1 =
      shiftRight ring k (x + 1)
  rw [runFacts_shiftRight_add]

private theorem runFacts_rightNeighbor_injective
    {n : Nat}
    (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by
        omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by
      omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by
        omega
      omega

private theorem runFacts_left_of_right_site
    {n : Nat}
    (ring : DirectedRing n)
    (k e : Fin n)
    (x : Nat)
    (hx : 0 < x)
    (hsite :
      ring.rightNeighbor e =
        shiftRight ring k x) :
    e = shiftRight ring k (x - 1) := by
  apply runFacts_rightNeighbor_injective ring
  rw [hsite, runFacts_rightNeighbor_shiftRight]
  congr 1
  omega

private theorem runFactsFreshPoint_birth
    {psi : Nat}
    (hpsi : 2 <= psi) :
    Lemma4FreshTrajectoryPoint
      psi 0 0 (((psi : Nat) : Int)) := by
  left
  refine Exists.intro 0 ?_
  refine And.intro (by omega) ?_
  refine And.intro (by simp) ?_
  refine And.intro ?_ ?_
  · simp
  · simp

private theorem runFactsFreshPoint_positive_step
    {psi moves x : Nat} {c : Int}
    (hpoint :
      Lemma4FreshTrajectoryPoint
        psi moves x c)
    (hc : 2 <= c) :
    Lemma4FreshTrajectoryPoint
      psi (moves + 1) (x + 1) (c - 1) := by
  rcases hpoint with hp | hn
  · rcases hp with
      ⟨q, hpos, hbound, hx, hmoves⟩
    cases c with
    | ofNat v =>
        have hv : 2 <= v := by
          simp only [Int.ofNat_eq_coe] at *; omega
        change v <= psi at hbound
        change x = q + (psi - v) at hx
        change
          moves =
            q * (2 * psi - 1) + (psi - v)
          at hmoves
        have hcast :
            (Int.ofNat v - 1) =
              Int.ofNat (v - 1) := by
          simp only [Int.ofNat_eq_coe] at *; omega
        unfold Lemma4FreshTrajectoryPoint
        rw [hcast]
        left
        refine ⟨q, ?_, ?_, ?_, ?_⟩
        · omega
        · change v - 1 <= psi
          omega
        · change x + 1 =
            q + (psi - (v - 1))
          omega
        · change moves + 1 =
            q * (2 * psi - 1) +
              (psi - (v - 1))
          omega
    | negSucc v =>
        omega
  · rcases hn with
      ⟨q, hneg, _hbound, _hx, _hmoves⟩
    omega

private theorem runFactsFreshPoint_positive_turn
    {psi moves x : Nat} {c : Int}
    (hpsi : 2 <= psi)
    (hpoint :
      Lemma4FreshTrajectoryPoint
        psi moves x c)
    (hc : c = 1) :
    Lemma4FreshTrajectoryPoint
      psi (moves + 1) (x + 1)
        (1 - ((psi : Nat) : Int)) := by
  subst c
  rcases hpoint with hp | hn
  · rcases hp with
      ⟨q, _hpos, _hbound, hx, hmoves⟩
    change x = q + (psi - 1) at hx
    change
      moves =
        q * (2 * psi - 1) + (psi - 1)
      at hmoves
    have hneg :
        1 - ((psi : Nat) : Int) < 0 := by
      omega
    have habs :
        (1 - ((psi : Nat) : Int)).natAbs =
          psi - 1 := by
      have heq :
          1 - ((psi : Nat) : Int) =
            -(((psi - 1 : Nat) : Int)) := by
        omega
      rw [heq]
      simp
    right
    refine ⟨q, hneg, ?_, ?_, ?_⟩
    · rw [habs]
      omega
    · rw [habs]
      omega
    · rw [habs]
      omega
  · rcases hn with
      ⟨q, hneg, _hbound, _hx, _hmoves⟩
    omega

private theorem runFactsFreshPoint_negative_step
    {psi moves x : Nat} {c : Int}
    (hpoint :
      Lemma4FreshTrajectoryPoint
        psi moves x c)
    (hc : c <= -2) :
    0 < x ∧
      Lemma4FreshTrajectoryPoint
        psi (moves + 1) (x - 1) (c + 1) := by
  rcases hpoint with hp | hn
  · rcases hp with
      ⟨q, hpos, _hbound, _hx, _hmoves⟩
    omega
  · rcases hn with
      ⟨q, hneg, hbound, hx, hmoves⟩
    have hxpos : 0 < x := by
      omega
    refine And.intro hxpos ?_
    cases c with
    | ofNat v =>
        simp only [Int.ofNat_eq_coe] at *; omega
    | negSucc v =>
        cases v with
        | zero =>
            omega
        | succ u =>
            have heq :
                (Int.negSucc (Nat.succ u) + 1) =
                  Int.negSucc u := by
              omega
            rw [heq]
            right
            refine ⟨q, ?_, ?_, ?_, ?_⟩
            · simp
            · simp at hbound ⊢
              omega
            · simp at hx ⊢
              omega
            · simp at hmoves ⊢
              omega

private theorem runFactsFreshPoint_negative_turn
    {psi moves x : Nat} {c : Int}
    (hpsi : 2 <= psi)
    (hpoint :
      Lemma4FreshTrajectoryPoint
        psi moves x c)
    (hc : c = -1) :
    0 < x ∧
      Lemma4FreshTrajectoryPoint
        psi (moves + 1) (x - 1)
          (((psi : Nat) : Int)) := by
  subst c
  rcases hpoint with hp | hn
  · rcases hp with
      ⟨q, hpos, _hbound, _hx, _hmoves⟩
    omega
  · rcases hn with
      ⟨q, _hneg, _hbound, hx, hmoves⟩
    have hxpos : 0 < x := by
      simp at hx
      omega
    refine And.intro hxpos ?_
    left
    refine ⟨q + 1, ?_, ?_, ?_, ?_⟩
    · omega
    · simp
    · simp at hx
      omega
    · simp at hmoves
      have hmul :
          (q + 1) * (2 * psi - 1) =
            q * (2 * psi - 1) +
              (2 * psi - 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [hmul]
      omega

/--
The final positive service has one move left.  This is the exact arithmetic
fact needed by the rightmost fresh-owner branch.
-/
theorem lemma4FreshTrajectoryPoint_finalPositive
    {psi moves : Nat}
    (hpsi : 2 <= psi)
    (hpoint :
      Lemma4FreshTrajectoryPoint
        psi moves (2 * psi - 2) (1 : Int)) :
    moves + 1 = tokenTrajectoryMoves psi := by
  rcases hpoint with hp | hn
  · rcases hp with
      ⟨q, _hpos, _hbound, hx, hmoves⟩
    change
      2 * psi - 2 = q + (psi - 1)
      at hx
    change
      moves =
        q * (2 * psi - 1) + (psi - 1)
      at hmoves
    have hq : q = psi - 1 := by
      omega
    rw [hq] at hmoves
    have hsubmul :
        (psi - 1) * (2 * psi - 1) =
          psi * (2 * psi - 1) -
            (2 * psi - 1) := by
      rw [Nat.sub_mul, Nat.one_mul]
    have hmuld :
        psi * (2 * psi - 1) =
          2 * psi * psi - psi := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      congr 1 <;> ac_rfl
    rw [hsubmul, hmuld] at hmoves
    unfold tokenTrajectoryMoves
    have hge : 2 * psi * 2 <= 2 * psi * psi :=
      Nat.mul_le_mul_left (2 * psi) hpsi
    generalize 2 * psi * psi = P at hmoves hge ⊢
    omega
  · rcases hn with
      ⟨q, hneg, _hbound, _hx, _hmoves⟩
    omega

/-! -------------------------------------------------------------------------
    3. A definitionally-equal public-name mirror of the private ghost row
------------------------------------------------------------------------- -/

private def runFactsBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def runFactsMkToken {psi : Nat}
    (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def runFactsLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) <= target ∧
        target <= (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 <= target ∧
        target <= (((psi - 1 : Nat)) : Int))

private instance instDecidableRunFactsLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (runFactsLocalValid kind q t) := by
  unfold runFactsLocalValid
  infer_instance

private def runFactsTokenPrelude
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
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
    else if r1.dist.val = 0 ∨
        r1.dist.val = psi then
      { l0 with last := false }
    else
      { l0 with last := r1.last }
  (l1, r1)

private def runFactsLiveShadow
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
              runFactsLocalValid kind q t then
            some z
          else
            none

private def runFactsLiveValue
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa) :
    Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if runFactsLocalValid kind q t then
        some t
      else
        none

private def runFactsBirthGhost
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      runFactsMkToken
        (offsetPsiCode psi hpsi)
        (runFactsBitToFin (!idBit))
        (runFactsBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

private def runFactsBumpTo
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
        { z.lmeta with
          moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi :=
        { value := newValue
          lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then
          [m']
        else
          []
      let live :=
        if runFactsLocalValid kind qDest newValue then
          some z'
        else
          none
      ⟨live, done⟩

private def runFactsNegTurnNext
    {psi : Nat}
    (hpsi : 2 <= psi)
    (sourceBit : Bool)
    (t : TokenData psi) :
    TokenData psi :=
  if t.2 = (1 : Fin 2) then
    runFactsMkToken
      (offsetPsiCode psi hpsi)
      (runFactsBitToFin (!sourceBit))
      (runFactsBitToFin sourceBit)
  else
    runFactsMkToken
      (offsetPsiCode psi hpsi)
      (runFactsBitToFin sourceBit)
      (0 : Fin 2)

private def runFactsFinishMove
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
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
          runFactsMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        let b :=
          runFactsBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else if h2 : 2 <= c then
        have hc : ValidOffset psi c :=
          decodeOffset_valid
            psi (by omega) (tokenCode t)
        let next :=
          runFactsMkToken
            (encodeOffset psi (c - 1) (by
              rcases hc with hn | hp
              · exfalso
                omega
              · right
                omega))
            t.1.2 t.2
        let b :=
          runFactsBumpTo kind r next gl2
        ⟨none, b.live, b.done⟩
      else
        match rv0 with
        | none =>
            ⟨gl2, gr0, []⟩
        | some t =>
            let c := decodeOffset psi (tokenCode t)
            if hm1 : c = -1 then
              let next :=
                runFactsNegTurnNext hpsi l.id t
              let b :=
                runFactsBumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid
                  psi (by omega) (tokenCode t)
              let next :=
                runFactsMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left
                      omega
                    · exfalso
                      omega))
                  t.1.2 t.2
              let b :=
                runFactsBumpTo kind l next gr0
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
              runFactsNegTurnNext hpsi l.id t
            let b :=
              runFactsBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else if hm2 : c <= -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid
                psi (by omega) (tokenCode t)
            let next :=
              runFactsMkToken
                (encodeOffset psi (c + 1) (by
                  rcases hc with hn | hp
                  · left
                    omega
                  · exfalso
                    omega))
                t.1.2 t.2
            let b :=
              runFactsBumpTo kind l next gr0
            ⟨b.live, none, b.done⟩
          else
            ⟨gl2, gr0, []⟩

private def runFactsGhostMoveToken
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (step : Nat)
    (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := runFactsLiveValue kind l
  let rv0 := runFactsLiveValue kind r
  let gl0 := runFactsLiveShadow kind l gl
  let gr0 := runFactsLiveShadow kind r gr
  if l.last = false ∧ r.last = false then
    let born :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (runFactsBirthGhost
            hpsi kind step site l.id)
      else
        gl0
    let lv1 :=
      if l.dist.val = tokenD' psi kind ∧
          lv0 = none then
        some
          (runFactsBirthGhost
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
    runFactsFinishMove
      hpsi kind l r lv2 rv0 gl2 gr0
  else
    ⟨gl0, gr0, []⟩

private def runFactsSetTwo
    {n : Nat} {A : Type}
    (f : Fin n -> A)
    (i j : Fin n)
    (xi xj : A) :
    Fin n -> A :=
  fun k =>
    if k = i then xi
    else if k = j then xj
    else f k

private def runFactsMovedPair
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    GhostMoveResult n psi :=
  let rsite := ring.rightNeighbor e
  let pre :=
    runFactsTokenPrelude hpsi
      (G.phys e) (G.phys rsite)
  match kind with
  | .black =>
      runFactsGhostMoveToken
        hpsi .black step e
        pre.1 pre.2
        (G.black e) (G.black rsite)
  | .white =>
      let qb :=
        moveToken hpsi .black pre.1 pre.2
      runFactsGhostMoveToken
        hpsi .white step e
        qb.1 qb.2
        (G.white e) (G.white rsite)

private theorem runFactsGhostTokenAtStep
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (i : Fin n) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      runFactsSetTwo
        (ghostTokenAt kind G)
        e (ring.rightNeighbor e)
        (runFactsMovedPair
          hpsi ring step G e kind).left
        (runFactsMovedPair
          hpsi ring step G e kind).right
        i := by
  cases kind <;> rfl

/-! -------------------------------------------------------------------------
    4. Option-level kinematics
------------------------------------------------------------------------- -/

private def RunFactsOptionKinematics
    {n psi : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (g : Option (GhostToken n psi)) : Prop :=
  forall z : GhostToken n psi,
    g = some z ->
    FreshAt kind k z.lmeta ->
    Exists fun x : Nat =>
      And
        (site = shiftRight ring k x)
        (Lemma4FreshTrajectoryPoint
          psi z.lmeta.moves x
          (decodeOffset psi
            (tokenCode z.value)))

private def RunFactsAlignedKinematics
    {n psi : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (v : Option (TokenData psi))
    (g : Option (GhostToken n psi)) : Prop :=
  (forall z : GhostToken n psi,
      g = some z ->
      v = some z.value) ∧
    RunFactsOptionKinematics
      ring k site kind g

private theorem runFactsOption_none
    {n psi : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind) :
    RunFactsOptionKinematics
      (psi := psi)
      ring k site kind none := by
  intro z hz _hfresh
  simp at hz

private theorem runFactsAligned_none
    {n psi : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind) :
    RunFactsAlignedKinematics
      (psi := psi)
      ring k site kind none none := by
  constructor
  · intro z hz
    simp at hz
  · exact runFactsOption_none ring k site kind

private theorem runFactsLiveShadow_aligned
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (q : State psi kappa)
    (g : Option (GhostToken n psi))
    (hkin :
      RunFactsOptionKinematics
        ring k site kind g) :
    RunFactsAlignedKinematics
      ring k site kind
      (runFactsLiveValue kind q)
      (runFactsLiveShadow kind q g) := by
  constructor
  · intro z hz
    cases hg : g with
    | none =>
        simp [runFactsLiveShadow, hg] at hz
    | some z0 =>
        cases ht : tokenAt kind q with
        | none =>
            simp [runFactsLiveShadow, hg, ht] at hz
        | some t =>
            by_cases hv :
                z0.value = t ∧
                  runFactsLocalValid kind q t
            · have hzz : z0 = z := by
                simpa [runFactsLiveShadow, hg, ht, hv]
                  using hz
              subst z
              simp [runFactsLiveValue, ht, hv.1, hv.2]
            · simp [runFactsLiveShadow, hg, ht, hv] at hz
  · intro z hz hfresh
    cases hg : g with
    | none =>
        simp [runFactsLiveShadow, hg] at hz
    | some z0 =>
        cases ht : tokenAt kind q with
        | none =>
            simp [runFactsLiveShadow, hg, ht] at hz
        | some t =>
            by_cases hv :
                z0.value = t ∧
                  runFactsLocalValid kind q t
            · have hzz : z0 = z := by
                simpa [runFactsLiveShadow, hg, ht, hv]
                  using hz
              subst z
              exact hkin z0 hg hfresh
            · simp [runFactsLiveShadow, hg, ht, hv] at hz

private theorem runFactsBirth_aligned
    {n psi : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (idBit : Bool) :
    RunFactsAlignedKinematics
      ring k k kind
      (some
        (runFactsBirthGhost
          hpsi kind step k idBit).value)
      (some
        (runFactsBirthGhost
          hpsi kind step k idBit)) := by
  constructor
  · intro z hz
    cases hz
    rfl
  · intro z hz hfresh
    cases hz
    refine ⟨0, ?_, ?_⟩
    · exact (runFacts_shiftRight_zero ring k).symm
    · simpa [runFactsBirthGhost,
        runFactsMkToken, tokenCode,
        decodeOffset_psi]
        using runFactsFreshPoint_birth hpsi

private theorem runFactsBump_origin
    {n psi kappa : Nat}
    (kind : TokenKind)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hz :
      (runFactsBumpTo
        kind qDest newValue g).live =
          some z') :
    ∃ z : GhostToken n psi,
      g = some z ∧
        z'.value = newValue ∧
          z'.lmeta.id = z.lmeta.id ∧
            z'.lmeta.birthSite = z.lmeta.birthSite ∧
              z'.lmeta.birthStep = z.lmeta.birthStep ∧
                z'.lmeta.moves = z.lmeta.moves + 1 := by
  cases g with
  | none =>
      simp [runFactsBumpTo] at hz
  | some z =>
      by_cases hv :
          runFactsLocalValid
            kind qDest newValue
      · simp [runFactsBumpTo, hv] at hz
        cases hz
        exact
          ⟨z, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp [runFactsBumpTo, hv] at hz

private theorem runFactsFreshAt_of_bump
    {n psi kappa : Nat}
    (kind : TokenKind)
    (k : Fin n)
    (qDest : State psi kappa)
    (newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (z' : GhostToken n psi)
    (hz :
      (runFactsBumpTo
        kind qDest newValue g).live =
          some z')
    (hfresh :
      FreshAt kind k z'.lmeta) :
    ∃ z : GhostToken n psi,
      g = some z ∧
        FreshAt kind k z.lmeta ∧
          z'.value = newValue ∧
            z'.lmeta.moves = z.lmeta.moves + 1 ∧
              z'.lmeta.id = z.lmeta.id ∧
                z'.lmeta.birthSite = z.lmeta.birthSite := by
  obtain
      ⟨z, hg, hval, hid, hsite,
        _hstep, hmoves⟩ :=
    runFactsBump_origin
      kind qDest newValue g z' hz
  rcases hfresh with ⟨t, hborn, hk⟩
  have hborn0 :
      z.lmeta.id = .born kind t := by
    exact hid.symm.trans hborn
  have hk0 :
      z.lmeta.birthSite = k := by
    exact hsite.symm.trans hk
  exact
    ⟨z, hg, ⟨t, hborn0, hk0⟩,
      hval, hmoves, hid, hsite⟩

private theorem runFactsBump_right
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (qDest : State psi kappa)
    (oldValue newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (halign :
      forall z,
        g = some z ->
        some oldValue = some z.value)
    (hkin :
      RunFactsOptionKinematics
        ring k site kind g)
    (htrans :
      forall (m x : Nat),
        Lemma4FreshTrajectoryPoint
            psi m x
            (decodeOffset psi
              (tokenCode oldValue)) ->
        Lemma4FreshTrajectoryPoint
          psi (m + 1) (x + 1)
          (decodeOffset psi
            (tokenCode newValue))) :
    RunFactsOptionKinematics
      ring k (ring.rightNeighbor site)
      kind
      (runFactsBumpTo
        kind qDest newValue g).live := by
  intro z' hz' hfresh'
  obtain
      ⟨z, hg, hfresh, hval, hmoves,
        _hid, _hsite⟩ :=
    runFactsFreshAt_of_bump
      kind k qDest newValue g z' hz'
      hfresh'
  obtain ⟨x, hxsite, hpoint⟩ :=
    hkin z hg hfresh
  have hal := halign z hg
  have hOld : oldValue = z.value :=
    Option.some.inj hal
  have hpoint' :
      Lemma4FreshTrajectoryPoint
        psi z.lmeta.moves x
        (decodeOffset psi
          (tokenCode oldValue)) := by
    rw [hOld]
    exact hpoint
  refine ⟨x + 1, ?_, ?_⟩
  · calc
      ring.rightNeighbor site =
          ring.rightNeighbor
            (shiftRight ring k x) := by
        rw [hxsite]
      _ = shiftRight ring k (x + 1) :=
        runFacts_rightNeighbor_shiftRight
          ring k x
  · rw [hmoves, hval]
    exact htrans z.lmeta.moves x hpoint'

private theorem runFactsBump_left
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (qDest : State psi kappa)
    (oldValue newValue : TokenData psi)
    (g : Option (GhostToken n psi))
    (halign :
      forall z,
        g = some z ->
        some oldValue = some z.value)
    (hkin :
      RunFactsOptionKinematics
        ring k (ring.rightNeighbor site)
          kind g)
    (htrans :
      forall (m x : Nat),
        Lemma4FreshTrajectoryPoint
            psi m x
            (decodeOffset psi
              (tokenCode oldValue)) ->
        0 < x ∧
          Lemma4FreshTrajectoryPoint
            psi (m + 1) (x - 1)
            (decodeOffset psi
              (tokenCode newValue))) :
    RunFactsOptionKinematics
      ring k site kind
      (runFactsBumpTo
        kind qDest newValue g).live := by
  intro z' hz' hfresh'
  obtain
      ⟨z, hg, hfresh, hval, hmoves,
        _hid, _hsite⟩ :=
    runFactsFreshAt_of_bump
      kind k qDest newValue g z' hz'
      hfresh'
  obtain ⟨x, hxsite, hpoint⟩ :=
    hkin z hg hfresh
  have hal := halign z hg
  have hOld : oldValue = z.value :=
    Option.some.inj hal
  have hpoint' :
      Lemma4FreshTrajectoryPoint
        psi z.lmeta.moves x
        (decodeOffset psi
          (tokenCode oldValue)) := by
    rw [hOld]
    exact hpoint
  have ht :=
    htrans z.lmeta.moves x hpoint'
  refine ⟨x - 1, ?_, ?_⟩
  · exact
      runFacts_left_of_right_site
        ring k site x ht.1 hxsite
  · rw [hmoves, hval]
    exact ht.2

/-! -------------------------------------------------------------------------
    5. The six movement branches
------------------------------------------------------------------------- -/

private theorem runFactsFinishMove_kinematics
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (l r : State psi kappa)
    (lv2 rv0 : Option (TokenData psi))
    (gl2 gr0 : Option (GhostToken n psi))
    (hleft :
      RunFactsAlignedKinematics
        ring k site kind lv2 gl2)
    (hright :
      RunFactsAlignedKinematics
        ring k (ring.rightNeighbor site)
          kind rv0 gr0) :
    let out :=
      runFactsFinishMove
        hpsi kind l r lv2 rv0 gl2 gr0
    RunFactsOptionKinematics
        ring k site kind out.left ∧
      RunFactsOptionKinematics
        ring k (ring.rightNeighbor site)
          kind out.right := by
  cases lv2 with
  | some t =>
      by_cases h1 :
          decodeOffset psi (tokenCode t) = 1
      · simp only
          [runFactsFinishMove, dif_pos h1]
        let next :=
          runFactsMkToken
            (offsetNegPsiPlusOneCode psi hpsi)
            t.1.2 t.2
        have hnext :
            decodeOffset psi
                (tokenCode next) =
              1 - ((psi : Nat) : Int) := by
          dsimp [next, runFactsMkToken, tokenCode]
          exact decodeOffset_negPsiPlusOne psi hpsi
        constructor
        · exact
            runFactsOption_none ring k site kind
        · apply
            runFactsBump_right
              ring k site kind r t next
              gl2 hleft.1 hleft.2
          intro m x hp
          rw [hnext]
          exact
            runFactsFreshPoint_positive_turn
              hpsi hp h1
      · by_cases h2 :
          2 <= decodeOffset psi (tokenCode t)
        · simp only
            [runFactsFinishMove,
              dif_neg h1, dif_pos h2]
          have hc :
              ValidOffset psi
                (decodeOffset psi (tokenCode t)) :=
            decodeOffset_valid
              psi (by omega) (tokenCode t)
          let next :=
            runFactsMkToken
              (encodeOffset psi
                (decodeOffset psi (tokenCode t) - 1)
                (by
                  rcases hc with hn | hp
                  · exfalso
                    omega
                  · right
                    omega))
              t.1.2 t.2
          have hnext :
              decodeOffset psi
                  (tokenCode next) =
                decodeOffset psi (tokenCode t) - 1 := by
            dsimp [next, runFactsMkToken, tokenCode]
            exact decode_encode _ _ _
          constructor
          · exact
              runFactsOption_none ring k site kind
          · apply
              runFactsBump_right
                ring k site kind r t next
                gl2 hleft.1 hleft.2
            intro m x hp
            rw [hnext]
            exact
              runFactsFreshPoint_positive_step hp h2
        · cases rv0 with
          | none =>
              simp only
                [runFactsFinishMove,
                  dif_neg h1, dif_neg h2]
              exact ⟨hleft.2, hright.2⟩
          | some tr =>
              by_cases hm1 :
                  decodeOffset psi (tokenCode tr) = -1
              · simp only
                  [runFactsFinishMove,
                    dif_neg h1, dif_neg h2,
                    dif_pos hm1]
                let next :=
                  runFactsNegTurnNext hpsi l.id tr
                have hnext :
                    decodeOffset psi
                        (tokenCode next) =
                      ((psi : Nat) : Int) := by
                  unfold next runFactsNegTurnNext
                  by_cases hcarry :
                      tr.2 = (1 : Fin 2)
                  · rw [if_pos hcarry]
                    dsimp [runFactsMkToken, tokenCode]
                    exact decodeOffset_psi psi hpsi
                  · rw [if_neg hcarry]
                    dsimp [runFactsMkToken, tokenCode]
                    exact decodeOffset_psi psi hpsi
                constructor
                · apply
                    runFactsBump_left
                      ring k site kind l tr next
                      gr0 hright.1 hright.2
                  intro m x hp
                  rw [hnext]
                  exact
                    runFactsFreshPoint_negative_turn
                      hpsi hp hm1
                · exact
                    runFactsOption_none
                      ring k (ring.rightNeighbor site) kind
              · by_cases hm2 :
                  decodeOffset psi (tokenCode tr) <= -2
                · simp only
                    [runFactsFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_pos hm2]
                  have hc :
                      ValidOffset psi
                        (decodeOffset psi
                          (tokenCode tr)) :=
                    decodeOffset_valid
                      psi (by omega) (tokenCode tr)
                  let next :=
                    runFactsMkToken
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
                  have hnext :
                      decodeOffset psi
                          (tokenCode next) =
                        decodeOffset psi
                            (tokenCode tr) + 1 := by
                    dsimp [next, runFactsMkToken, tokenCode]
                    exact decode_encode _ _ _
                  constructor
                  · apply
                      runFactsBump_left
                        ring k site kind l tr next
                        gr0 hright.1 hright.2
                    intro m x hp
                    rw [hnext]
                    exact
                      runFactsFreshPoint_negative_step hp hm2
                  · exact
                      runFactsOption_none
                        ring k (ring.rightNeighbor site) kind
                · simp only
                    [runFactsFinishMove,
                      dif_neg h1, dif_neg h2,
                      dif_neg hm1, dif_neg hm2]
                  exact ⟨hleft.2, hright.2⟩
  | none =>
      cases rv0 with
      | none =>
          simp only [runFactsFinishMove]
          exact ⟨hleft.2, hright.2⟩
      | some tr =>
          by_cases hm1 :
              decodeOffset psi (tokenCode tr) = -1
          · simp only
              [runFactsFinishMove, dif_pos hm1]
            let next :=
              runFactsNegTurnNext hpsi l.id tr
            have hnext :
                decodeOffset psi
                    (tokenCode next) =
                  ((psi : Nat) : Int) := by
              unfold next runFactsNegTurnNext
              by_cases hcarry :
                  tr.2 = (1 : Fin 2)
              · rw [if_pos hcarry]
                dsimp [runFactsMkToken, tokenCode]
                exact decodeOffset_psi psi hpsi
              · rw [if_neg hcarry]
                dsimp [runFactsMkToken, tokenCode]
                exact decodeOffset_psi psi hpsi
            constructor
            · apply
                runFactsBump_left
                  ring k site kind l tr next
                  gr0 hright.1 hright.2
              intro m x hp
              rw [hnext]
              exact
                runFactsFreshPoint_negative_turn
                  hpsi hp hm1
            · exact
                runFactsOption_none
                  ring k (ring.rightNeighbor site) kind
          · by_cases hm2 :
              decodeOffset psi (tokenCode tr) <= -2
            · simp only
                [runFactsFinishMove,
                  dif_neg hm1, dif_pos hm2]
              have hc :
                  ValidOffset psi
                    (decodeOffset psi (tokenCode tr)) :=
                decodeOffset_valid
                  psi (by omega) (tokenCode tr)
              let next :=
                runFactsMkToken
                  (encodeOffset psi
                    (decodeOffset psi (tokenCode tr) + 1)
                    (by
                      rcases hc with hn | hp
                      · left
                        omega
                      · exfalso
                        omega))
                  tr.1.2 tr.2
              have hnext :
                  decodeOffset psi
                      (tokenCode next) =
                    decodeOffset psi (tokenCode tr) + 1 := by
                dsimp [next, runFactsMkToken, tokenCode]
                exact decode_encode _ _ _
              constructor
              · apply
                  runFactsBump_left
                    ring k site kind l tr next
                    gr0 hright.1 hright.2
                intro m x hp
                rw [hnext]
                exact
                  runFactsFreshPoint_negative_step hp hm2
              · exact
                  runFactsOption_none
                    ring k (ring.rightNeighbor site) kind
            · simp only
                [runFactsFinishMove,
                  dif_neg hm1, dif_neg hm2]
              exact ⟨hleft.2, hright.2⟩

/-! -------------------------------------------------------------------------
    6. Birth/collision prefix and one ghost step
------------------------------------------------------------------------- -/

private theorem runFactsGhostMoveToken_kinematics
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k site : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi))
    (hgl :
      RunFactsOptionKinematics
        ring k site kind gl)
    (hgr :
      RunFactsOptionKinematics
        ring k (ring.rightNeighbor site)
          kind gr) :
    let out :=
      runFactsGhostMoveToken
        hpsi kind step site l r gl gr
    RunFactsOptionKinematics
        ring k site kind out.left ∧
      RunFactsOptionKinematics
        ring k (ring.rightNeighbor site)
          kind out.right := by
  let lv0 := runFactsLiveValue kind l
  let rv0 := runFactsLiveValue kind r
  let gl0 := runFactsLiveShadow kind l gl
  let gr0 := runFactsLiveShadow kind r gr
  have hgl0 :
      RunFactsAlignedKinematics
        ring k site kind lv0 gl0 := by
    exact
      runFactsLiveShadow_aligned
        ring k site kind l gl hgl
  have hgr0 :
      RunFactsAlignedKinematics
        ring k (ring.rightNeighbor site)
          kind rv0 gr0 := by
    exact
      runFactsLiveShadow_aligned
        ring k (ring.rightNeighbor site)
          kind r gr hgr

  by_cases hlast :
      l.last = false ∧ r.last = false
  · let hb :=
      l.dist.val = tokenD' psi kind ∧
        lv0 = none
    let birth :=
      runFactsBirthGhost
        hpsi kind step site l.id
    let lv1 : Option (TokenData psi) :=
      if hb then some birth.value else lv0
    let gl1 : Option (GhostToken n psi) :=
      if hb then some birth else gl0

    have hgl1 :
        RunFactsAlignedKinematics
          ring k site kind lv1 gl1 := by
      by_cases hbirth : hb
      · have hk :
            FreshAt kind k birth.lmeta ->
              site = k := by
          intro hf
          rcases hf with ⟨t, _hid, hsite⟩
          simpa [birth, runFactsBirthGhost]
            using hsite
        constructor
        · intro z hz
          simp [lv1, gl1, hbirth] at hz
          cases hz
          show (if hb then some birth.value else lv0) = some birth.value
          rw [if_pos hbirth]
        · intro z hz hfresh
          simp [gl1, hbirth] at hz
          cases hz
          have hsite : site = k := hk hfresh
          subst site
          exact
            (runFactsBirth_aligned
                            hpsi ring k kind step l.id).2
              birth rfl hfresh
      · simpa [lv1, gl1, hbirth]
          using hgl0

    let collide :=
      lv1 ≠ none ∧ rv0 ≠ none
    let lv2 : Option (TokenData psi) :=
      if collide then none else lv1
    let gl2 : Option (GhostToken n psi) :=
      if collide then none else gl1

    have hgl2 :
        RunFactsAlignedKinematics
          ring k site kind lv2 gl2 := by
      by_cases hcol : collide
      · simp [lv2, gl2, hcol]
        exact
          runFactsAligned_none
            (psi := psi)             ring k site kind
      · simpa [lv2, gl2, hcol]
          using hgl1

    have hfinish :=
      runFactsFinishMove_kinematics
        hpsi ring k site kind l r
        lv2 rv0 gl2 gr0 hgl2 hgr0

    simp only
      [runFactsGhostMoveToken,
        if_pos hlast]
    exact hfinish
  · simp only
      [runFactsGhostMoveToken,
        if_neg hlast]
    exact ⟨hgl0.2, hgr0.2⟩

private theorem runFactsMovedPair_kinematics
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hkin :
      Lemma4FreshKinematics ring k G) :
    let out :=
      runFactsMovedPair
        hpsi ring step G e kind
    RunFactsOptionKinematics
        ring k e kind out.left ∧
      RunFactsOptionKinematics
        ring k (ring.rightNeighbor e)
          kind out.right := by
  have hleft :
      RunFactsOptionKinematics
        ring k e kind
        (ghostTokenAt kind G e) := by
    intro z hz hf
    exact hkin kind e z hz hf
  have hright :
      RunFactsOptionKinematics
        ring k (ring.rightNeighbor e)
          kind
          (ghostTokenAt kind G
            (ring.rightNeighbor e)) := by
    intro z hz hf
    exact
      hkin kind (ring.rightNeighbor e)
        z hz hf
  unfold runFactsMovedPair
  cases kind with
  | black =>
      dsimp only
      exact
        runFactsGhostMoveToken_kinematics
          hpsi ring k e .black step
          (runFactsTokenPrelude hpsi
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).1
          (runFactsTokenPrelude hpsi
            (G.phys e)
            (G.phys (ring.rightNeighbor e))).2
          (G.black e)
          (G.black (ring.rightNeighbor e))
          hleft hright
  | white =>
      dsimp only
      let pre :=
        runFactsTokenPrelude hpsi
          (G.phys e)
          (G.phys (ring.rightNeighbor e))
      let qb :=
        moveToken hpsi .black pre.1 pre.2
      exact
        runFactsGhostMoveToken_kinematics
          hpsi ring k e .white step
          qb.1 qb.2
          (G.white e)
          (G.white (ring.rightNeighbor e))
          hleft hright

private theorem lemma4FreshKinematics_step
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (hkin :
      Lemma4FreshKinematics ring k G) :
    Lemma4FreshKinematics ring k
      (ghostStep hpsi ring step G e) := by
  intro kind i z howner hfresh
  have hpair :=
    runFactsMovedPair_kinematics
      hpsi ring k step G e kind hkin

  by_cases hie : i = e
  · subst i
    rw [
      runFactsGhostTokenAtStep
        hpsi ring step G e kind e]
      at howner
    simp only
      [runFactsSetTwo, if_pos rfl]
      at howner
    exact hpair.1 z howner hfresh

  · by_cases hir :
      i = ring.rightNeighbor e
    · subst i
      have hne :
          ring.rightNeighbor e ≠ e := by
        exact hie
      rw [
        runFactsGhostTokenAtStep
          hpsi ring step G e kind
            (ring.rightNeighbor e)]
        at howner
      simp only
        [runFactsSetTwo,
          if_neg hne, if_pos rfl]
        at howner
      exact hpair.2 z howner hfresh

    · have howner0 :
          ghostTokenAt kind G i = some z := by
        rw [
          runFactsGhostTokenAtStep
            hpsi ring step G e kind i]
          at howner
        simpa
          [runFactsSetTwo, hie, hir]
          using howner
      exact hkin kind i z howner0 hfresh

/-! -------------------------------------------------------------------------
    7. Initial and run closure
------------------------------------------------------------------------- -/

private theorem lemma4FreshKinematics_initial
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (C0 : Config n psi kappa) :
    Lemma4FreshKinematics
      ring k (initialGhost C0) := by
  intro kind i z howner hfresh
  rcases hfresh with ⟨t, hborn, _hsite⟩
  have hU :=
    (ghostIdsUnique_initial C0).2
      kind i z kind t howner hborn
  omega

private theorem lemma4FreshKinematics_run_from
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n) :
    forall (t : Nat)
      (G : GhostConfig n psi kappa)
      (pre : DetSchedule n),
      Lemma4FreshKinematics ring k G ->
      Lemma4FreshKinematics ring k
        (ghostRun hpsi ring t G pre) := by
  intro t G pre hkin
  induction pre generalizing t G with
  | nil =>
      exact hkin
  | cons e es ih =>
      simp only [ghostRun]
      exact
        ih (t := t + 1)
          (G := ghostStep hpsi ring t G e)
          (lemma4FreshKinematics_step
            hpsi ring k t G e hkin)

theorem lemma4FreshKinematics_run
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n) :
    Lemma4FreshKinematics ring k
      (ghostRun hpsi ring 0
        (initialGhost C0) pre) := by
  exact
    lemma4FreshKinematics_run_from
      hpsi ring k 0 (initialGhost C0) pre
      (lemma4FreshKinematics_initial
        ring k C0)

/--
Convenience extraction for rightmost-row consumers.
-/
theorem lemma4FreshKinematics_run_owner
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (kind : TokenKind)
    (i : Fin n)
    (z : GhostToken n psi)
    (howner :
      ghostTokenAt kind
          (ghostRun hpsi ring 0
            (initialGhost C0) pre) i =
        some z)
    (hfresh :
      FreshAt kind k z.lmeta) :
    ∃ x : Nat,
      i = shiftRight ring k x ∧
        Lemma4FreshTrajectoryPoint
          psi z.lmeta.moves x
          (decodeOffset psi
            (tokenCode z.value)) :=
  lemma4FreshKinematics_run
    hpsi ring k C0 pre
    kind i z howner hfresh

end PPL

#print axioms PPL.ghostIdsUnique_run
#print axioms PPL.lemma4FreshTrajectoryPoint_finalPositive
#print axioms PPL.lemma4FreshKinematics_run
#print axioms PPL.lemma4FreshKinematics_run_owner
