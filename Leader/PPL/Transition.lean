import Leader.PPL.State
import Leader.Core.Basic


/-!
# Literal P_PL v2 transition, Algorithms 1--5


This is a direct transcription of arXiv:2305.08375v2. Each algorithm is a
separate function and assignments are threaded in printed imperative order.
The paper domain is psi >= 2. The proof-free public `transition psi kappa`
is total on the reused carrier by returning the input pair when psi < 2;
that branch is outside the paper domain and outside `ppl_reference.py`,
which rejects psi < 2.
-/


namespace PPL


set_option autoImplicit false


abbrev TokenData (psi : Nat) :=
  (Fin (2 * psi - 1) × Fin 2) × Fin 2


inductive TokenKind where
  | black
  | white
  deriving DecidableEq


private def tokenD (psi : Nat) : TokenKind → Nat
  | .black => 0
  | .white => psi


private def getToken {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : Option (TokenData psi) :=
  match kind with
  | .black => q.tokenB
  | .white => q.tokenW


private def setToken {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : Option (TokenData psi)) : State psi kappa :=
  match kind with
  | .black => { q with tokenB := t }
  | .white => { q with tokenW := t }


private def tokenOffset {psi : Nat} (t : TokenData psi) :
    Fin (2 * psi - 1) :=
  t.1.1


private def tokenBit {psi : Nat} (t : TokenData psi) : Fin 2 :=
  t.1.2


private def tokenCarry {psi : Nat} (t : TokenData psi) : Fin 2 :=
  t.2


private def mkToken {psi : Nat} (offset : Fin (2 * psi - 1))
    (bit carry : Fin 2) : TokenData psi :=
  ((offset, bit), carry)


private def bitToFin (b : Bool) : Fin 2 :=
  if b then (1 : Fin 2) else (0 : Fin 2)


private def finToBit (b : Fin 2) : Bool :=
  b.val == 1


private def zeroFin (m : Nat) : Fin (m + 1) :=
  ⟨0, by omega⟩


private def topFin (m : Nat) : Fin (m + 1) :=
  ⟨m, by omega⟩


/-- Literal `min(x+1,m)` from Algorithm 4. -/
private def cappedSucc {m : Nat} (x : Fin (m + 1)) : Fin (m + 1) :=
  ⟨Nat.min (x.val + 1) m, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩


/-- Literal predecessor, used only after proving the current signal is
strictly positive. No saturating/clamping case is available to the caller. -/
private def predFinOfPos {m : Nat} (x : Fin (m + 1))
    (hx : 0 < x.val) : Fin (m + 1) :=
  ⟨x.val - 1, by omega⟩


private def zeroDist {psi : Nat} (hpsi : 0 < psi) : Fin (2 * psi) :=
  ⟨0, by omega⟩


/-- Algorithm 2 line 4's `(dist+1) mod 2*psi`. -/
private def distSucc {psi : Nat} (hpsi : 0 < psi)
    (d : Fin (2 * psi)) : Fin (2 * psi) :=
  ⟨(d.val + 1) % (2 * psi), Nat.mod_lt _ (by omega)⟩


/-- Paper Target(v,d), computed in signed integer arithmetic before the
positive modulus. -/
private def tokenTarget {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) : Int :=
  (((q.dist.val : Nat) : Int) + decodeOffset psi (tokenOffset t) +
      (((tokenD psi kind : Nat)) : Int)) %
    (((2 * psi : Nat)) : Int)


/-- Paper Valid(v,d), Algorithm 3 macro / Definition 3. -/
private def tokenValid {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenOffset t)
  let target := tokenTarget kind q t
  (0 < c ∧ ((psi : Nat) : Int) ≤ target ∧
      target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧ 1 ≤ target ∧ target ≤ (((psi - 1 : Nat)) : Int))


private instance {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) (t : TokenData psi) :
    Decidable (tokenValid kind q t) := by
  unfold tokenValid; infer_instance


private def clearInvalid {psi kappa : Nat} (kind : TokenKind)
    (q : State psi kappa) : State psi kappa :=
  match getToken kind q with
  | none => q
  | some t =>
      if tokenValid kind q t then q else setToken kind q none


private theorem offset_sub_one_valid {psi : Nat} {c : Int}
    (hc : ValidOffset psi c) (h2 : 2 ≤ c) :
    ValidOffset psi (c - 1) := by
  rcases hc with hneg | hpos
  · exfalso
    omega
  · right
    omega


private theorem offset_add_one_valid {psi : Nat} {c : Int}
    (hc : ValidOffset psi c) (h2 : c ≤ -2) :
    ValidOffset psi (c + 1) := by
  rcases hc with hneg | hpos
  · left
    omega
  · exfalso
    omega


/-- The assignment used at Algorithms 2 line 6 and 3 line 20. -/
private def leaderBirth {psi kappa : Nat}
    (q : State psi kappa) : State psi kappa :=
  { q with
    leader := true
    bullet := (2 : Fin 3)
    shield := true
    signalB := false }


/-- Algorithm 4 lines 49--50. By the State-module convention,
`true = Detect`. -/
private def finishModes {psi kappa : Nat}
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  ({ l with mode := l.clock.val == kappa },
   { r with mode := r.clock.val == kappa })


/-- Algorithm 4: DetermineMode(), lines 34--50. -/
def determineMode {psi kappa : Nat}
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  -- line 34
  let l :=
    if l.leader = true then
      -- line 35
      { l with signalR := topFin kappa }
    else l
  -- line 36
  let l : State psi kappa := { l with hits := zeroFin psi }
  -- line 37
  let r : State psi kappa := { r with hits := cappedSucc r.hits }
  -- line 38
  if hsignal : 0 < l.signalR.val ∨ 0 < r.signalR.val then
    -- line 39
    let l0 : State psi kappa := { l with clock := zeroFin kappa }
    let r0 : State psi kappa := { r with clock := zeroFin kappa }
    -- line 40
    if hge : r0.signalR.val ≤ l0.signalR.val then
      have hlpos : 0 < l0.signalR.val := by
        dsimp only [l0, r0] at hge ⊢
        rcases hsignal with hl | hr
        · exact hl
        · omega
      -- line 41
      let r1 : State psi kappa := { r0 with signalR := l0.signalR, hits := zeroFin psi }
      -- line 42
      let l1 : State psi kappa := { l0 with signalR := zeroFin kappa }
      -- line 43
      let r2 :=
        if hhit : r1.hits.val = psi then
          -- lines 44--45
          { r1 with
              signalR := predFinOfPos l0.signalR hlpos
              hits := zeroFin psi }
        else r1
      -- lines 49--50
      finishModes l1 r2
    else
      have hrpos : 0 < r0.signalR.val := by
        dsimp only [l0, r0] at hge ⊢
        rcases hsignal with hl | hr
        · omega
        · exact hr
      -- line 42
      let l1 : State psi kappa := { l0 with signalR := zeroFin kappa }
      -- line 43
      let r1 :=
        if hhit : r0.hits.val = psi then
          -- lines 44--45
          { r0 with
              signalR := predFinOfPos r0.signalR hrpos
              hits := zeroFin psi }
        else r0
      -- lines 49--50
      finishModes l1 r1
  else
    -- line 46
    let r :=
      if hhit : r.hits.val = psi then
        -- line 47
        let r : State psi kappa := { r with clock := cappedSucc r.clock }
        -- line 48
        { r with hits := zeroFin psi }
      else r
    -- lines 49--50
    finishModes l r


/-- Algorithm 3: MoveToken(token,d), lines 12--33.
The `TokenKind` fixes d to 0 (black) or psi (white). -/
def moveToken {psi kappa : Nat} (hpsi : 2 ≤ psi) (kind : TokenKind)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  -- line 12
  let l := clearInvalid kind l
  let r := clearInvalid kind r
  -- line 13
  if hlast : l.last = false ∧ r.last = false then
    -- lines 14--15
    let l :=
      if l.dist.val = tokenD psi kind ∧ getToken kind l = none then
        setToken kind l
          (some (mkToken (offsetPsiCode psi hpsi)
            (bitToFin (!l.id)) (bitToFin l.id)))
      else l
    -- lines 16--17
    let l :=
      if getToken kind l ≠ none ∧ getToken kind r ≠ none then
        setToken kind l none
      else l
    let moveLeft := fun (l r : State psi kappa) =>
      match getToken kind r with
      | none => (l, r)
      | some t =>
          let c := decodeOffset psi (tokenOffset t)
          -- line 28
          if hm1 : c = -1 then
            -- line 29
            let next :=
              if tokenCarry t = (1 : Fin 2) then
                mkToken (offsetPsiCode psi hpsi)
                  (bitToFin (!l.id)) (bitToFin l.id)
              else
                mkToken (offsetPsiCode psi hpsi)
                  (bitToFin l.id) (0 : Fin 2)
            let l := setToken kind l (some next)
            -- line 30
            let r := setToken kind r none
            (l, r)
          -- line 31
          else if hm2 : c ≤ -2 then
            have hc : ValidOffset psi c :=
              decodeOffset_valid psi (by omega) (tokenOffset t)
            let nextOffset :=
              encodeOffset psi (c + 1) (offset_add_one_valid hc hm2)
            -- line 32
            let l := setToken kind l
              (some (mkToken nextOffset (tokenBit t) (tokenCarry t)))
            -- line 33
            let r := setToken kind r none
            (l, r)
          else
            (l, r)
    match getToken kind l with
    | none => moveLeft l r
    | some t =>
        let c := decodeOffset psi (tokenOffset t)
        -- line 18
        if hc1 : c = 1 then
          let bit := finToBit (tokenBit t)
          -- lines 19--20
          let r :=
            if r.mode = true ∧ bit ≠ r.id then
              leaderBirth r
            -- lines 21--22
            else if r.mode = false then
              { r with id := bit }
            else r
          -- line 23: exact signed bounce 1-psi = -psi+1
          let r := setToken kind r
            (some (mkToken (offsetNegPsiPlusOneCode psi hpsi)
              (tokenBit t) (tokenCarry t)))
          -- line 24
          let l := setToken kind l none
          (l, r)
        -- line 25
        else if hc2 : 2 ≤ c then
          have hc : ValidOffset psi c :=
            decodeOffset_valid psi (by omega) (tokenOffset t)
          let nextOffset :=
            encodeOffset psi (c - 1) (offset_sub_one_valid hc hc2)
          -- line 26
          let r := setToken kind r
            (some (mkToken nextOffset (tokenBit t) (tokenCarry t)))
          -- line 27
          let l := setToken kind l none
          (l, r)
        else
          moveLeft l r
  else
    (l, r)


/-- Algorithm 2 line 4, evaluated after DetermineMode and captured once. -/
private def createLeaderTmp {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) : Fin (2 * psi) :=
  if r.leader = true then
    zeroDist (by omega)
  else
    distSucc (by omega) l.dist


/-- Exact guard whose true branch performs Algorithm 2 line 6. -/
def createLeaderLine6Guard {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) : Prop :=
  let q := determineMode l r
  let tmp := createLeaderTmp hpsi q.1 q.2
  q.2.mode = true ∧ tmp ≠ q.2.dist


instance {psi kappa : Nat} (hpsi : 2 ≤ psi) (l r : State psi kappa) :
    Decidable (createLeaderLine6Guard hpsi l r) := by
  unfold createLeaderLine6Guard; infer_instance


/-- State immediately after Algorithm 2 line 6, retaining the line-4 temporary
so later code cannot accidentally recompute it. -/
structure CreateLeaderAfterLine6 (psi kappa : Nat) where
  left : State psi kappa
  right : State psi kappa
  tmp : Fin (2 * psi)


def createLeaderThroughLine6 {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) : CreateLeaderAfterLine6 psi kappa :=
  -- line 3
  let q := determineMode l r
  -- line 4
  let tmp := createLeaderTmp hpsi q.1 q.2
  -- line 5
  let r :=
    if createLeaderLine6Guard hpsi l r then
      -- line 6
      leaderBirth q.2
    else q.2
  ⟨q.1, r, tmp⟩


/-- Sanity theorem for Algorithm 2 line 6: before Algorithm 5 is called, a
line-6 birth has exactly the four fields printed in the paper. -/
theorem createLeader_line6_birth {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) (h : createLeaderLine6Guard hpsi l r) :
    let s := createLeaderThroughLine6 hpsi l r
    s.right.leader = true ∧
      s.right.bullet = (2 : Fin 3) ∧
      s.right.shield = true ∧
      s.right.signalB = false := by
  simp [createLeaderThroughLine6, h, leaderBirth]


/-- Algorithm 2: CreateLeader(), lines 3--11. -/
def createLeader {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  let s := createLeaderThroughLine6 hpsi l r
  let l := s.left
  let r := s.right
  let tmp := s.tmp
  -- line 7
  let r :=
    if r.mode = false then
      -- line 8
      { r with dist := tmp }
    else r
  -- line 9
  let l :=
    if r.leader = true then
      { l with last := true }
    else if r.dist.val = 0 ∨ r.dist.val = psi then
      { l with last := false }
    else
      { l with last := r.last }
  -- line 10
  let q := moveToken hpsi .black l r
  -- line 11
  moveToken hpsi .white q.1 q.2


/-- Algorithm 5: EliminateLeaders(), lines 51--62. -/
def eliminateLeaders {psi kappa : Nat}
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  -- line 51
  let l :=
    if l.leader = true ∧ l.signalB = true then
      -- line 52
      { l with
          bullet := (2 : Fin 3)
          shield := true
          signalB := false }
    else l
  -- line 53
  let r :=
    if r.leader = true ∧ r.signalB = true then
      -- line 54
      { r with
          bullet := (1 : Fin 3)
          shield := false
          signalB := false }
    else r
  -- line 55
  let q :=
    if l.bullet.val > 0 then
      let r :=
        -- line 56
        if r.leader = true then
          -- line 57
          if l.bullet = (2 : Fin 3) ∧ r.shield = false then
            { r with leader := false }
          else
            { r with leader := true }
        else
          -- line 58
          let r :=
            if r.bullet = (0 : Fin 3) then
              -- line 59
              { r with bullet := l.bullet }
            else r
          -- line 60
          { r with signalB := false }
      -- line 61
      ({ l with bullet := (0 : Fin 3) }, r)
    else
      (l, r)
  -- line 62 -- intentionally outside the line-55 conditional
  ({ q.1 with signalB := q.1.signalB || q.2.signalB || q.2.leader }, q.2)


/-- Sanity theorem pinning the indentation of line 62. If neither FIRE
branch runs and the left bullet is zero, line 55 is skipped but line 62 still
writes the max/OR of the three printed fields. -/
theorem eliminateLeaders_line62_of_left_bullet_zero {psi kappa : Nat}
    (l r : State psi kappa)
    (hlbullet : l.bullet = (0 : Fin 3))
    (hlfire : ¬ (l.leader = true ∧ l.signalB = true))
    (hrfire : ¬ (r.leader = true ∧ r.signalB = true)) :
    (eliminateLeaders l r).1.signalB =
      (l.signalB || r.signalB || r.leader) := by
  simp [eliminateLeaders, hlfire, hrfire, hlbullet]


/-- Algorithm 1: P_PL. CreateLeader runs first, and Algorithm 5 therefore
reads every write made by Algorithms 2--4 in the same interaction. -/
def ppl {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) : State psi kappa × State psi kappa :=
  -- line 1
  let q := createLeader hpsi l r
  -- line 2
  eliminateLeaders q.1 q.2


/-- Public proof-free local transition. The identity branch is solely a
totalization outside the paper/Python domain psi >= 2. -/
def transition (psi kappa : Nat) :
    State psi kappa → State psi kappa → State psi kappa × State psi kappa :=
  fun l r =>
    if hpsi : 2 ≤ psi then
      ppl hpsi l r
    else
      (l, r)


theorem transition_eq_ppl {psi kappa : Nat} (hpsi : 2 ≤ psi)
    (l r : State psi kappa) :
    transition psi kappa l r = ppl hpsi l r := by
  simp [transition, hpsi]


def protocol (psi kappa : Nat) : PopulationProtocol where
  Q := State psi kappa
  Y := Bool
  transition := transition psi kappa
  output := fun q => q.leader


end PPL

#print axioms PPL.createLeader_line6_birth
#print axioms PPL.eliminateLeaders_line62_of_left_bullet_zero
#print axioms PPL.transition_eq_ppl
