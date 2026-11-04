import Leader.PPL.Predicates
import Leader.PPL.Probability.FixedWord

namespace PPL

set_option autoImplicit false

/-!
Token correctness and the historical token-completion argument.

There are two deliberately separate layers.

* The physical component is exactly Config n psi kappa and is advanced by
  PopulationProtocol.step (protocol psi kappa).  No field is added to State.
* The ghost component owns only valid token occurrences.  An invalid raw
  residue is unowned.  This is important at the final target: Definition 4
  says that the trajectory completes on that move, while Algorithm 3 leaves an
  invalid raw token to be removed by line 12 on the next incident interaction.

The ghost identity is proof-only and erases definitionally.
-/

/-! ## Source segment view used by Remark 2 -/

/-- Start of rooted full segment S_seg. -/
def sourceStart {n : Nat} (psi : Nat) (ring : DirectedRing n)
    (root : Fin n) (seg : Nat) : Fin n :=
  shiftRight ring root (seg * psi)

/-- Extensional little-endian representation of paper iota(S_seg).
Equality here is exactly equality of all psi source bits. -/
def sourceIota {n psi kappa : Nat} (ring : DirectedRing n)
    (root : Fin n) (C : Config n psi kappa) (seg : Nat) :
    Fin psi -> Bool :=
  fun x => (C (shiftRight ring (sourceStart psi ring root seg) x.val)).id

private def sourceIota_bit {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa) (seg : Nat)
    (h : sourceIota ring root C seg = sourceIota ring root C' seg)
    (x : Fin psi) :
    (C (shiftRight ring (sourceStart psi ring root seg) x.val)).id =
      (C' (shiftRight ring (sourceStart psi ring root seg) x.val)).id := by
  exact congrFun h x

private def firstZeroAux_source_congr {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa) (seg fuel j : Nat)
    (hbound : j + fuel <= psi)
    (hsrc : sourceIota ring root C seg = sourceIota ring root C' seg) :
    firstZeroAux ring C (sourceStart psi ring root seg) fuel j =
      firstZeroAux ring C' (sourceStart psi ring root seg) fuel j := by
  induction fuel generalizing j with
  | zero => rfl
  | succ fuel ih =>
      unfold firstZeroAux
      have hj : j < psi := by omega
      let x : Fin psi := ⟨j, hj⟩
      have hb := sourceIota_bit ring root C C' seg hsrc x
      change
        (C (shiftRight ring (sourceStart psi ring root seg) j)).id =
          (C' (shiftRight ring (sourceStart psi ring root seg) j)).id at hb
      rw [hb]
      split
      · rfl
      · exact ih (j := j + 1) (by omega)

private def firstZero_source_congr {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa) (seg : Nat)
    (hsrc : sourceIota ring root C seg = sourceIota ring root C' seg) :
    firstZeroBit ring C (sourceStart psi ring root seg) =
      firstZeroBit ring C' (sourceStart psi ring root seg) := by
  unfold firstZeroBit
  exact firstZeroAux_source_congr ring root C C' seg psi 0
    (by omega) hsrc

private def payloadCorrect_source_congr {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C C' : Config n psi kappa) (seg x : Nat)
    (hx : x < psi) (t : TokenData psi)
    (hsrc : sourceIota ring root C seg = sourceIota ring root C' seg) :
    payloadCorrect ring C (sourceStart psi ring root seg) x t <->
      payloadCorrect ring C' (sourceStart psi ring root seg) x t := by
  unfold payloadCorrect
  have hj := firstZero_source_congr ring root C C' seg hsrc
  let ix : Fin psi := ⟨x, hx⟩
  have hb := sourceIota_bit ring root C C' seg hsrc ix
  change
    (C (shiftRight ring (sourceStart psi ring root seg) x)).id =
      (C' (shiftRight ring (sourceStart psi ring root seg) x)).id at hb
  rw [hj, hb]

/-! ## Proof-only token lineage refinement -/

inductive LineageId (n : Nat) where
  | initial (kind : TokenKind) (site : Fin n)
  | born (kind : TokenKind) (step : Nat)
  deriving DecidableEq

structure LineageMeta (n : Nat) where
  id : LineageId n
  birthSite : Fin n
  birthStep : Nat
  moves : Nat
  deriving DecidableEq

structure GhostToken (n psi : Nat) where
  value : TokenData psi
  lmeta : LineageMeta n
  deriving DecidableEq

/-- Exact Definition-4 move count. -/
def tokenTrajectoryMoves (psi : Nat) : Nat :=
  2 * psi * psi - 2 * psi + 1

structure GhostConfig (n psi kappa : Nat) where
  phys : Config n psi kappa
  black : Fin n -> Option (GhostToken n psi)
  white : Fin n -> Option (GhostToken n psi)
  completed : List (LineageMeta n)

def ghostTokenAt {n psi kappa : Nat} (kind : TokenKind)
    (G : GhostConfig n psi kappa) (i : Fin n) :
    Option (GhostToken n psi) :=
  match kind with
  | .black => G.black i
  | .white => G.white i

def eraseGhost {n psi kappa : Nat} (G : GhostConfig n psi kappa) :
    Config n psi kappa :=
  G.phys

private def tcBitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)

private def tcMkToken {psi : Nat} (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)

private def tcLocalValid {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧ ((psi : Nat) : Int) <= target ∧
      target <= (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧ 1 <= target ∧
      target <= (((psi - 1 : Nat)) : Int))

private instance {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) :
    Decidable (tcLocalValid kind q t) := by
  unfold tcLocalValid
  infer_instance

private def tokenPrelude {psi kappa : Nat} (hpsi : 2 <= psi)
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

private def liveShadow {n psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (g : Option (GhostToken n psi)) :
    Option (GhostToken n psi) :=
  match g with
  | none => none
  | some z =>
      match tokenAt kind q with
      | none => none
      | some t =>
          if ht : z.value = t ∧ tcLocalValid kind q t then
            some z
          else none

private def liveValue {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : Option (TokenData psi) :=
  match tokenAt kind q with
  | none => none
  | some t =>
      if tcLocalValid kind q t then some t else none

private def birthGhost {n psi : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat) (site : Fin n) (idBit : Bool) :
    GhostToken n psi :=
  { value :=
      tcMkToken (offsetPsiCode psi hpsi)
        (tcBitToFin (!idBit)) (tcBitToFin idBit)
    lmeta :=
      { id := .born kind step
        birthSite := site
        birthStep := step
        moves := 0 } }

structure Bumped (n psi : Nat) where
  live : Option (GhostToken n psi)
  done : List (LineageMeta n)

private def bumpTo {n psi kappa : Nat}
    (kind : TokenKind) (qDest : State psi kappa)
    (newValue : TokenData psi) (g : Option (GhostToken n psi)) :
    Bumped n psi :=
  match g with
  | none => ⟨none, []⟩
  | some z =>
      let m' : LineageMeta n := { z.lmeta with moves := z.lmeta.moves + 1 }
      let z' : GhostToken n psi := { value := newValue, lmeta := m' }
      let done :=
        if m'.moves = tokenTrajectoryMoves psi then [m'] else []
      let live :=
        if tcLocalValid kind qDest newValue then some z' else none
      ⟨live, done⟩

structure GhostMoveResult (n psi : Nat) where
  left : Option (GhostToken n psi)
  right : Option (GhostToken n psi)
  done : List (LineageMeta n)

private def ghostMoveToken {n psi kappa : Nat} (hpsi : 2 <= psi)
    (kind : TokenKind) (step : Nat) (site : Fin n)
    (l r : State psi kappa)
    (gl gr : Option (GhostToken n psi)) :
    GhostMoveResult n psi :=
  let lv0 := liveValue kind l
  let rv0 := liveValue kind r
  let gl0 := liveShadow kind l gl
  let gr0 := liveShadow kind r gr
  if hlast : l.last = false ∧ r.last = false then
    let born :=
      if hb : l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (birthGhost hpsi kind step site l.id)
      else gl0
    let lv1 :=
      if hb : l.dist.val = tokenD' psi kind ∧ lv0 = none then
        some (birthGhost hpsi kind step site l.id).value
      else lv0
    let gl1 := born
    let collide := lv1 ≠ none ∧ rv0 ≠ none
    let lv2 := if collide then none else lv1
    let gl2 := if collide then none else gl1
    match lv2 with
    | some t =>
        let c := decodeOffset psi (tokenCode t)
        if h1 : c = 1 then
          let next :=
            tcMkToken (offsetNegPsiPlusOneCode psi hpsi)
              t.1.2 t.2
          let b := bumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else if h2 : 2 <= c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid psi (by omega) (tokenCode t)
          let next :=
            tcMkToken
              (encodeOffset psi (c - 1) (by
                rcases hc with hn | hp
                · exfalso; omega
                · right; omega))
              t.1.2 t.2
          let b := bumpTo kind r next gl2
          ⟨none, b.live, b.done⟩
        else
          match rv0 with
          | none => ⟨gl2, gr0, []⟩
          | some t =>
              let c := decodeOffset psi (tokenCode t)
              if hm1 : c = -1 then
                let next :=
                  if t.2 = (1 : Fin 2) then
                    tcMkToken (offsetPsiCode psi hpsi)
                      (tcBitToFin (!l.id)) (tcBitToFin l.id)
                  else
                    tcMkToken (offsetPsiCode psi hpsi)
                      (tcBitToFin l.id) (0 : Fin 2)
                let b := bumpTo kind l next gr0
                ⟨b.live, none, b.done⟩
              else if hm2 : c <= -2 then
                have hc : ValidOffset psi c :=
                  decodeOffset_valid psi (by omega) (tokenCode t)
                let next :=
                  tcMkToken
                    (encodeOffset psi (c + 1) (by
                      rcases hc with hn | hp
                      · left; omega
                      · exfalso; omega))
                    t.1.2 t.2
                let b := bumpTo kind l next gr0
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
                  tcMkToken (offsetPsiCode psi hpsi)
                    (tcBitToFin (!l.id)) (tcBitToFin l.id)
                else
                  tcMkToken (offsetPsiCode psi hpsi)
                    (tcBitToFin l.id) (0 : Fin 2)
              let b := bumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else if hm2 : c <= -2 then
              have hc : ValidOffset psi c :=
                decodeOffset_valid psi (by omega) (tokenCode t)
              let next :=
                tcMkToken
                  (encodeOffset psi (c + 1) (by
                    rcases hc with hn | hp
                    · left; omega
                    · exfalso; omega))
                  t.1.2 t.2
              let b := bumpTo kind l next gr0
              ⟨b.live, none, b.done⟩
            else
              ⟨gl2, gr0, []⟩
  else
    ⟨gl0, gr0, []⟩

private def setTwo {n : Nat} {A : Type} (f : Fin n -> A)
    (i j : Fin n) (xi xj : A) : Fin n -> A :=
  fun k => if k = i then xi else if k = j then xj else f k

/-- One proof-only step.  Physical row selection is never ghost-dependent. -/
def ghostStep {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) :
    GhostConfig n psi kappa :=
  let rsite := ring.rightNeighbor e
  let pre := tokenPrelude hpsi (G.phys e) (G.phys rsite)
  let gb :=
    ghostMoveToken hpsi .black step e pre.1 pre.2
      (G.black e) (G.black rsite)
  let qb := moveToken hpsi .black pre.1 pre.2
  let gw :=
    ghostMoveToken hpsi .white step e qb.1 qb.2
      (G.white e) (G.white rsite)
  { phys := PopulationProtocol.step (protocol psi kappa) ring G.phys e
    black := setTwo G.black e rsite gb.left gb.right
    white := setTwo G.white e rsite gw.left gw.right
    completed := G.completed ++ gb.done ++ gw.done }

/-- The extension erases to the literal P_PL step. -/
theorem ghostStep_erases {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) :
    eraseGhost (ghostStep hpsi ring step G e) =
      PopulationProtocol.step (protocol psi kappa) ring (eraseGhost G) e := by
  rfl

private noncomputable def initialOwned {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa) (i : Fin n) :
    Option (GhostToken n psi) := by
  classical
  exact
    match tokenAt kind (C i) with
    | none => none
    | some t =>
        if tcLocalValid kind (C i) t then
          some
            { value := t
              lmeta :=
                { id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0 } }
        else none

noncomputable def initialGhost {n psi kappa : Nat} (C : Config n psi kappa) :
    GhostConfig n psi kappa :=
  { phys := C
    black := initialOwned .black C
    white := initialOwned .white C
    completed := [] }

def ghostRun {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) :
    Nat -> GhostConfig n psi kappa -> DetSchedule n -> GhostConfig n psi kappa
  | _, G, [] => G
  | t, G, e :: es =>
      ghostRun hpsi ring (t + 1) (ghostStep hpsi ring t G e) es

private def ghostRun_append {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (t : Nat)
    (G : GhostConfig n psi kappa) (a b : DetSchedule n) :
    ghostRun hpsi ring t G (a ++ b) =
      ghostRun hpsi ring (t + a.length)
        (ghostRun hpsi ring t G a) b := by
  induction a generalizing t G with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, ghostRun, List.length_cons]
      rw [ih]
      congr 1
      omega

theorem ghostRun_erases {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (t : Nat)
    (G : GhostConfig n psi kappa) (es : DetSchedule n) :
    eraseGhost (ghostRun hpsi ring t G es) =
      PPL.Probability.runPopulationSchedule
        (protocol psi kappa) ring (eraseGhost G) es := by
  induction es generalizing t G with
  | nil => rfl
  | cons e es ih =>
      simp only [ghostRun, PPL.Probability.runPopulationSchedule]
      rw [ih]
      rfl

/-! A live lineage owns only a valid physical token. -/

def LiveLineage {n psi kappa : Nat} (kind : TokenKind)
    (id : LineageId n) (G : GhostConfig n psi kappa) : Prop :=
  ∃ i z, ghostTokenAt kind G i = some z ∧ z.lmeta.id = id

def LineageDeleted {n psi kappa : Nat} (kind : TokenKind)
    (id : LineageId n) (G : GhostConfig n psi kappa) : Prop :=
  ¬ LiveLineage kind id G

def CorrectDescendant {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n) (seg : Nat)
    (kind : TokenKind) (id : LineageId n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∃ i z,
    ghostTokenAt kind G i = some z ∧
      z.lmeta.id = id ∧
      CorrectToken ring root G.phys i kind seg

private def ghost_live_value_sound {n psi kappa : Nat}
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  ∀ i z, ghostTokenAt kind G i = some z ->
    tokenAt kind (G.phys i) = some z.value ∧
      tcLocalValid kind (G.phys i) z.value

def GhostSound {n psi kappa : Nat} (G : GhostConfig n psi kappa) : Prop :=
  ghost_live_value_sound .black G ∧ ghost_live_value_sound .white G


/-! ## Remark 2: open exact statement -/

def remark2_one_step : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi) (hn3 : 3 <= n)
    (ring : DirectedRing n) (root : Fin n)
    (seg : Fin (segmentCount n psi - 2))
    (C : Config n psi kappa) (e : Fin n)
    (G : GhostConfig n psi kappa) (kind : TokenKind)
    (i : Fin n) (z : GhostToken n psi)
    (hphys : G.phys = C)
    (hG : GhostSound G)
    (howner : ghostTokenAt kind G i = some z)
    (hvalid : ValidToken kind C i)
    (hwork : WorkingFor ring root C i kind seg.val)
    (hcorr : CorrectToken ring root C i kind seg.val)
    (hC : CDLAt ring root C)
    (hC' :
      CDLAt ring root
        (PopulationProtocol.step (protocol psi kappa) ring C e)),
    let C' := PopulationProtocol.step (protocol psi kappa) ring C e
    let G' := ghostStep hpsi ring z.lmeta.moves G e
    sourceIota ring root C seg.val ≠ sourceIota ring root C' seg.val ∨
      LineageDeleted kind z.lmeta.id G' ∨
      CorrectDescendant ring root seg.val kind z.lmeta.id G'

/-! ## Lemma 4 word and C_d trace -/

def seqR {n : Nat} (ring : DirectedRing n)
    (k : Fin n) (m : Nat) : DetSchedule n :=
  List.ofFn (fun x : Fin m => shiftRight ring k x.val)

def seqL {n : Nat} (ring : DirectedRing n)
    (k : Fin n) (m : Nat) : DetSchedule n :=
  List.ofFn (fun x : Fin m => shiftLeft ring k (x.val + 1))

def wordPower {n : Nat} : Nat -> DetSchedule n -> DetSchedule n
  | 0, _ => []
  | r + 1, w => w ++ wordPower r w

private def wordPower_length {n : Nat} (r : Nat) (w : DetSchedule n) :
    (wordPower r w).length = r * w.length := by
  induction r with
  | zero => simp [wordPower]
  | succ r ih =>
      simp [wordPower, ih, Nat.succ_mul, Nat.add_comm]

def lemma4Block {n : Nat} (ring : DirectedRing n)
    (k : Fin n) (psi : Nat) : DetSchedule n :=
  seqR ring k (2 * psi - 1) ++
    seqL ring (shiftRight ring k (2 * psi - 1)) (2 * psi - 1)

def lemma4Word {n : Nat} (ring : DirectedRing n)
    (k : Fin n) (psi : Nat) : DetSchedule n :=
  wordPower (2 * psi) (lemma4Block ring k psi)

/-- Exact source word length: 2 psi copies of two sweeps of length 2 psi - 1. -/
theorem lemma4Word_length {n psi : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) :
    (lemma4Word ring k psi).length = 8 * psi * psi - 4 * psi := by
  rw [lemma4Word, wordPower_length]
  have hR : (seqR ring k (2 * psi - 1)).length = 2 * psi - 1 := by
    simp [seqR]
  have hL :
      (seqL ring (shiftRight ring k (2 * psi - 1))
        (2 * psi - 1)).length = 2 * psi - 1 := by
    simp [seqL]
  rw [lemma4Block, List.length_append, hR, hL]
  have hs : (2 * psi - 1) + (2 * psi - 1) = 4 * psi - 2 := by
    omega
  rw [hs, Nat.mul_sub_left_distrib]
  congr 1 <;> ac_rfl

/-- Source C_d for the selected color (black d=0, white d=psi). -/
def Cd {n psi kappa : Nat} (ring : DirectedRing n)
    (k : Fin n) (kind : TokenKind) (C : Config n psi kappa) : Prop :=
  ∀ x : Fin (2 * psi),
    let v := shiftRight ring k x.val
    (C v).dist.val =
        (x.val + tokenD' psi kind) % (2 * psi) ∧
      (C v).last = false

/-- Every intermediate physical configuration, including both endpoints,
satisfies C_d.  This is the hypothesis printed in Lemma 4. -/
def CdTrace {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) :
    Config n psi kappa -> DetSchedule n -> Prop
  | C, [] => Cd ring k kind C
  | C, e :: es =>
      Cd ring k kind C ∧
        CdTrace hpsi ring k kind
          (PopulationProtocol.step (protocol psi kappa) ring C e) es


def FreshAt {n : Nat} (kind : TokenKind) (k : Fin n)
    (m : LineageMeta n) : Prop :=
  ∃ t, m.id = .born kind t ∧ m.birthSite = k

def FreshCompletion {n psi : Nat} (kind : TokenKind)
    (k : Fin n) (m : LineageMeta n) : Prop :=
  FreshAt kind k m ∧ m.moves = tokenTrajectoryMoves psi

def HasFreshCompletion {n psi kappa : Nat} (kind : TokenKind)
    (k : Fin n) (G : GhostConfig n psi kappa) : Prop :=
  ∃ m, m ∈ G.completed ∧ FreshCompletion (psi := psi) kind k m


/-! ## Lemma 4: open deterministic statement -/

def lemma4_deterministic_core : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (schedule : DetSchedule n)
    (hCd : CdTrace hpsi ring k kind C schedule)
    (hsub : (lemma4Word ring k psi).Sublist schedule),
    HasFreshCompletion kind k
      (ghostRun hpsi ring 0 (initialGhost C) schedule)

/-- Fixed-word probability wrapper with the exact Lemma-4 length. -/
theorem lemma4_fixedWordMissCount_mul_twoPow_le_of_length
    {n psi : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (K : Nat) :
    let L := 8 * psi * psi - 4 * psi
    let horizon := 2 * n * (L + K)
    PPL.Probability.fixedWordMissCount
        (lemma4Word ring k psi) horizon * 2 ^ K <= n ^ horizon := by
  dsimp only
  exact
    PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
      (lemma4Word ring k psi)
      (8 * psi * psi - 4 * psi) K
      (lemma4Word_length hpsi ring k)

/-
The initial-only C_d premise is refuted at psi = 3, n = 7 by firing
(u6,u0) before the selected word. The deterministic statement above retains
the trace-wide premise. Remark 2 and the deterministic core remain open
propositions; no theorem is claimed for them here.
-/

end PPL

#print axioms PPL.ghostStep_erases
#print axioms PPL.ghostRun_erases
#print axioms PPL.lemma4Word_length
#print axioms PPL.lemma4_fixedWordMissCount_mul_twoPow_le_of_length
#check PPL.remark2_one_step
#check PPL.lemma4_deterministic_core
