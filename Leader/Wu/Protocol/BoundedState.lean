import Leader.Wu.Protocol.State

/-!
# Finite-by-construction state representation

`AgentState` intentionally remains the executable audit model and contains raw
`Nat`/`Int` payloads. This module defines the bounded representation suggested
by Algorithm 1 (plus documented sentinels/operational values) without silently
changing the current transition. Erasure and certified reification form a
machine-checked bijection with the audit states satisfying
`AgentState.inProtocolDomain`. `Leader.Wu.Protocol.BoundedProtocol` uses this representation
only after proving the explicit repaired audit transition's output-domain theorem.
-/

inductive BoundedPathInfo (ψ : Nat) where
  | bot
  | some (label : Fin ψ) (bit : Fin 2)
  deriving DecidableEq, Repr

structure BoundedPath2Info (ψ : Nat) where
  label : Fin ψ
  bit : Fin 2
  position : Fin (ψ + 1)
  /-- Encodes printed action values 1 through 6 as values 0 through 5. -/
  action : Fin 6
  deriving DecidableEq, Repr

structure BoundedPath3Info (ψ : Nat) where
  label : Fin ψ
  bit : Fin 2
  flag : Fin 2
  deriving DecidableEq, Repr

/-- Algorithm 5's `-1` clean-command sentinel, missing from Algorithm 1. -/
inductive CleaningLabel (ψ : Nat) where
  | normal (label : Fin ψ)
  | clean
  deriving DecidableEq, Repr

/-- Every numeric payload is finite by construction. `count` is indexed by κ,
which is why a faithful state type must depend on both ψ and κ. -/
structure BoundedAgentState (ψ κ : Nat) where
  leader : Bool
  probe : Bool
  phase : Bool
  bit : Bool
  wait : Bool
  state : MainState
  path : BoundedPathInfo ψ
  reset : Bool
  carry : Bool
  count : Fin (κ + 1)
  label : Fin ψ
  h_field : Bool
  path2 : Option (BoundedPath2Info ψ)
  path3 : Option (BoundedPath3Info ψ)
  path4 : Option (CleaningLabel ψ × Fin 2)
  path5 : Option (CleaningLabel ψ × Fin 2)
  p : Bool
  p_carry : Bool
  reset_cmd : Bool
  echo : Bool
  signal_B : Fin 2
  bullet : Fin 3
  shield : Bool
  write_state : WriteState
  write : WriteAction
  last : Bool
  last_set : Bool
  last_unset : Bool
  b_carry : Bool
  gen_ws : Bool
  ws_echo : Bool
  signal_ws : Bool
  deriving DecidableEq, Repr

namespace BoundedAgentState

private def erasePath {ψ : Nat} : BoundedPathInfo ψ → PathInfo
  | .bot => .bot
  | .some label bit => .some label.val bit.val

private def erasePath2 {ψ : Nat} (p : BoundedPath2Info ψ) : Path2Info :=
  { label := p.label.val
    bit := p.bit.val
    position := p.position.val
    action := p.action.val + 1 }

private def erasePath3 {ψ : Nat} (p : BoundedPath3Info ψ) : Path3Info :=
  { label := p.label.val, bit := p.bit.val, flag := p.flag.val }

private def eraseCleaningLabel {ψ : Nat} : CleaningLabel ψ → Int
  | .normal label => Int.ofNat label.val
  | .clean => -1

private def eraseCleanPath {ψ : Nat}
    (p : CleaningLabel ψ × Fin 2) : Int × Nat :=
  (eraseCleaningLabel p.1, p.2.val)

private def reifyPath {ψ : Nat} (p : PathInfo)
    (hp : match p with
      | .bot => True
      | .some label bit => label < ψ ∧ bit ≤ 1) : BoundedPathInfo ψ :=
  match p with
  | .bot => .bot
  | .some label bit => .some ⟨label, hp.1⟩ ⟨bit, by omega⟩

private theorem erase_reifyPath {ψ : Nat} (p : PathInfo)
    (hp : match p with
      | .bot => True
      | .some label bit => label < ψ ∧ bit ≤ 1) :
    erasePath (reifyPath p hp) = p := by
  cases p <;> rfl

private def reifyPath2 {ψ : Nat} (p : Path2Info)
    (hp : p.label < ψ ∧ p.bit ≤ 1 ∧ p.position ≤ ψ ∧
      1 ≤ p.action ∧ p.action ≤ 6) : BoundedPath2Info ψ :=
  { label := ⟨p.label, hp.1⟩
    bit := ⟨p.bit, by omega⟩
    position := ⟨p.position, by omega⟩
    action := ⟨p.action - 1, by omega⟩ }

private theorem erase_reifyPath2 {ψ : Nat} (p : Path2Info)
    (hp : p.label < ψ ∧ p.bit ≤ 1 ∧ p.position ≤ ψ ∧
      1 ≤ p.action ∧ p.action ≤ 6) :
    erasePath2 (reifyPath2 p hp) = p := by
  cases p with
  | mk label bit position action =>
    simp only [erasePath2, reifyPath2]
    congr
    dsimp only at hp
    omega

private def reifyPath2Option {ψ : Nat} (p : Option Path2Info)
    (hp : match p with
      | none => True
      | some q => q.label < ψ ∧ q.bit ≤ 1 ∧ q.position ≤ ψ ∧
          1 ≤ q.action ∧ q.action ≤ 6) : Option (BoundedPath2Info ψ) :=
  match p with
  | none => none
  | some q => some (reifyPath2 q hp)

private theorem erase_reifyPath2Option {ψ : Nat} (p : Option Path2Info)
    (hp : match p with
      | none => True
      | some q => q.label < ψ ∧ q.bit ≤ 1 ∧ q.position ≤ ψ ∧
          1 ≤ q.action ∧ q.action ≤ 6) :
    (reifyPath2Option p hp).map erasePath2 = p := by
  cases p with
  | none => rfl
  | some q => simp [reifyPath2Option, erase_reifyPath2]

private def reifyPath3 {ψ : Nat} (p : Path3Info)
    (hp : p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1) :
    BoundedPath3Info ψ :=
  { label := ⟨p.label, hp.1⟩
    bit := ⟨p.bit, by omega⟩
    flag := ⟨p.flag, by omega⟩ }

private theorem erase_reifyPath3 {ψ : Nat} (p : Path3Info)
    (hp : p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1) :
    erasePath3 (reifyPath3 p hp) = p := by
  cases p
  rfl

private def reifyPath3Option {ψ : Nat} (p : Option Path3Info)
    (hp : match p with
      | none => True
      | some q => q.label < ψ ∧ q.bit ≤ 1 ∧ q.flag ≤ 1) :
    Option (BoundedPath3Info ψ) :=
  match p with
  | none => none
  | some q => some (reifyPath3 q hp)

private theorem erase_reifyPath3Option {ψ : Nat} (p : Option Path3Info)
    (hp : match p with
      | none => True
      | some q => q.label < ψ ∧ q.bit ≤ 1 ∧ q.flag ≤ 1) :
    (reifyPath3Option p hp).map erasePath3 = p := by
  cases p with
  | none => rfl
  | some q => simp [reifyPath3Option, erase_reifyPath3]

private def reifyCleaningLabel {ψ : Nat} (x : Int)
    (hlo : (-1 : Int) ≤ x) (hhi : x < Int.ofNat ψ) : CleaningLabel ψ :=
  if hx : x = -1 then .clean
  else .normal ⟨x.toNat, by
    have hx0 : (0 : Int) ≤ x := by omega
    rw [← Int.ofNat_lt]
    rw [Int.toNat_of_nonneg hx0]
    exact hhi⟩

private theorem erase_reifyCleaningLabel {ψ : Nat} (x : Int)
    (hlo : (-1 : Int) ≤ x) (hhi : x < Int.ofNat ψ) :
    eraseCleaningLabel (reifyCleaningLabel x hlo hhi) = x := by
  by_cases hx : x = -1
  · simp [reifyCleaningLabel, hx, eraseCleaningLabel]
  · have hx0 : (0 : Int) ≤ x := by omega
    simp [reifyCleaningLabel, hx, eraseCleaningLabel,
      Int.toNat_of_nonneg hx0]

private def reifyCleanPath {ψ : Nat} (p : Int × Nat)
    (hp : (-1 : Int) ≤ p.1 ∧ p.1 < Int.ofNat ψ ∧ p.2 ≤ 1) :
    CleaningLabel ψ × Fin 2 :=
  (reifyCleaningLabel p.1 hp.1 hp.2.1, ⟨p.2, by omega⟩)

private theorem erase_reifyCleanPath {ψ : Nat} (p : Int × Nat)
    (hp : (-1 : Int) ≤ p.1 ∧ p.1 < Int.ofNat ψ ∧ p.2 ≤ 1) :
    eraseCleanPath (reifyCleanPath p hp) = p := by
  apply Prod.ext
  · exact erase_reifyCleaningLabel p.1 hp.1 hp.2.1
  · rfl

private def reifyCleanPathOption {ψ : Nat} (p : Option (Int × Nat))
    (hp : match p with
      | none => True
      | some (label, bit) =>
          (-1 : Int) ≤ label ∧ label < Int.ofNat ψ ∧ bit ≤ 1) :
    Option (CleaningLabel ψ × Fin 2) :=
  match p with
  | none => none
  | some q => some (reifyCleanPath q hp)

private theorem erase_reifyCleanPathOption {ψ : Nat}
    (p : Option (Int × Nat))
    (hp : match p with
      | none => True
      | some (label, bit) =>
          (-1 : Int) ≤ label ∧ label < Int.ofNat ψ ∧ bit ≤ 1) :
    (reifyCleanPathOption p hp).map eraseCleanPath = p := by
  cases p with
  | none => rfl
  | some q => simp [reifyCleanPathOption, erase_reifyCleanPath]

private theorem reify_erasePath {ψ : Nat} (p : BoundedPathInfo ψ)
    (hp : match erasePath p with
      | .bot => True
      | .some label bit => label < ψ ∧ bit ≤ 1) :
    reifyPath (erasePath p) hp = p := by
  cases p <;> rfl

private theorem reify_erasePath2 {ψ : Nat} (p : BoundedPath2Info ψ)
    (hp : let q := erasePath2 p
      q.label < ψ ∧ q.bit ≤ 1 ∧ q.position ≤ ψ ∧
        1 ≤ q.action ∧ q.action ≤ 6) :
    reifyPath2 (erasePath2 p) hp = p := by
  cases p with
  | mk label bit position action =>
    cases label
    cases bit
    cases position
    cases action
    simp [reifyPath2, erasePath2]

private theorem reify_erasePath2Option {ψ : Nat}
    (p : Option (BoundedPath2Info ψ))
    (hp : match p.map erasePath2 with
      | none => True
      | some q => q.label < ψ ∧ q.bit ≤ 1 ∧ q.position ≤ ψ ∧
          1 ≤ q.action ∧ q.action ≤ 6) :
    reifyPath2Option (p.map erasePath2) hp = p := by
  cases p with
  | none => rfl
  | some q => simp [reifyPath2Option, reify_erasePath2]

private theorem reify_erasePath3 {ψ : Nat} (p : BoundedPath3Info ψ)
    (hp : let q := erasePath3 p
      q.label < ψ ∧ q.bit ≤ 1 ∧ q.flag ≤ 1) :
    reifyPath3 (erasePath3 p) hp = p := by
  cases p with
  | mk label bit flag =>
    cases label
    cases bit
    cases flag
    rfl

private theorem reify_erasePath3Option {ψ : Nat}
    (p : Option (BoundedPath3Info ψ))
    (hp : match p.map erasePath3 with
      | none => True
      | some q => q.label < ψ ∧ q.bit ≤ 1 ∧ q.flag ≤ 1) :
    reifyPath3Option (p.map erasePath3) hp = p := by
  cases p with
  | none => rfl
  | some q => simp [reifyPath3Option, reify_erasePath3]

private theorem reify_eraseCleaningLabel {ψ : Nat} (x : CleaningLabel ψ)
    (hlo : (-1 : Int) ≤ eraseCleaningLabel x)
    (hhi : eraseCleaningLabel x < Int.ofNat ψ) :
    reifyCleaningLabel (eraseCleaningLabel x) hlo hhi = x := by
  cases x with
  | normal label =>
    cases label
    simp [reifyCleaningLabel, eraseCleaningLabel]
  | clean => simp [reifyCleaningLabel, eraseCleaningLabel]

private theorem reify_eraseCleanPath {ψ : Nat}
    (p : CleaningLabel ψ × Fin 2)
    (hp : let q := eraseCleanPath p
      (-1 : Int) ≤ q.1 ∧ q.1 < Int.ofNat ψ ∧ q.2 ≤ 1) :
    reifyCleanPath (eraseCleanPath p) hp = p := by
  apply Prod.ext
  · exact reify_eraseCleaningLabel p.1 hp.1 hp.2.1
  · apply Fin.ext
    rfl

private theorem reify_eraseCleanPathOption {ψ : Nat}
    (p : Option (CleaningLabel ψ × Fin 2))
    (hp : match p.map eraseCleanPath with
      | none => True
      | some (label, bit) =>
          (-1 : Int) ≤ label ∧ label < Int.ofNat ψ ∧ bit ≤ 1) :
    reifyCleanPathOption (p.map eraseCleanPath) hp = p := by
  cases p with
  | none => rfl
  | some q => simp [reifyCleanPathOption, reify_eraseCleanPath]

/-- Forget bounds while preserving every concrete field value. -/
def erase {ψ κ : Nat} (s : BoundedAgentState ψ κ) : AgentState ψ :=
  { leader := s.leader
    probe := s.probe
    phase := s.phase
    bit := s.bit
    wait := s.wait
    state := s.state
    path := erasePath s.path
    reset := s.reset
    carry := s.carry
    count := s.count.val
    label := s.label
    h_field := s.h_field
    path2 := s.path2.map erasePath2
    path3 := s.path3.map erasePath3
    path4 := s.path4.map eraseCleanPath
    path5 := s.path5.map eraseCleanPath
    p := s.p
    p_carry := s.p_carry
    reset_cmd := s.reset_cmd
    echo := s.echo
    signal_B := s.signal_B
    bullet := s.bullet
    shield := s.shield
    write_state := s.write_state
    write := s.write
    last := s.last
    last_set := s.last_set
    last_unset := s.last_unset
    b_carry := s.b_carry
    gen_ws := s.gen_ws
    ws_echo := s.ws_echo
    signal_ws := s.signal_ws }

/-- Reify every audit-state field satisfying the declared numeric domain into
its finite-by-construction representation. -/
def ofDomain {ψ κ : Nat} (s : AgentState ψ)
    (hs : s.inProtocolDomain κ) : BoundedAgentState ψ κ :=
  { leader := s.leader
    probe := s.probe
    phase := s.phase
    bit := s.bit
    wait := s.wait
    state := s.state
    path := reifyPath s.path hs.2.1
    reset := s.reset
    carry := s.carry
    count := ⟨s.count, by have := hs.1; omega⟩
    label := s.label
    h_field := s.h_field
    path2 := reifyPath2Option s.path2 hs.2.2.1
    path3 := reifyPath3Option s.path3 hs.2.2.2.1
    path4 := reifyCleanPathOption s.path4 hs.2.2.2.2.1
    path5 := reifyCleanPathOption s.path5 hs.2.2.2.2.2
    p := s.p
    p_carry := s.p_carry
    reset_cmd := s.reset_cmd
    echo := s.echo
    signal_B := s.signal_B
    bullet := s.bullet
    shield := s.shield
    write_state := s.write_state
    write := s.write
    last := s.last
    last_set := s.last_set
    last_unset := s.last_unset
    b_carry := s.b_carry
    gen_ws := s.gen_ws
    ws_echo := s.ws_echo
    signal_ws := s.signal_ws }

/-- Reification is a right inverse to erasure on the declared protocol domain. -/
theorem erase_ofDomain {ψ κ : Nat} (s : AgentState ψ)
    (hs : s.inProtocolDomain κ) : erase (ofDomain s hs) = s := by
  cases s
  simp only [erase, ofDomain, AgentState.mk.injEq, true_and, and_true,
    eq_self]
  constructor
  · exact erase_reifyPath _ _
  constructor
  · exact erase_reifyPath2Option _ _
  constructor
  · exact erase_reifyPath3Option _ _
  constructor
  · exact erase_reifyCleanPathOption _ _
  · exact erase_reifyCleanPathOption _ _

private theorem eraseCleaningLabel_bounds {ψ : Nat} (hψ : 0 < ψ)
    (x : CleaningLabel ψ) :
    (-1 : Int) ≤ eraseCleaningLabel x ∧
      eraseCleaningLabel x < Int.ofNat ψ := by
  cases x with
  | normal label => simp [eraseCleaningLabel]
  | clean =>
    simp only [eraseCleaningLabel]
    have hz : (0 : Int) < Int.ofNat ψ := Int.natCast_pos.mpr hψ
    omega

/-- Erasure always satisfies the audited Algorithm-1 numeric domain. -/
theorem erase_inProtocolDomain {ψ κ : Nat} (s : BoundedAgentState ψ κ) :
    (erase s).inProtocolDomain κ := by
  unfold AgentState.inProtocolDomain erase
  constructor
  · change s.count.val ≤ κ
    have hc := s.count.isLt
    omega
  constructor
  · cases s.path with
    | bot => trivial
    | some label bit =>
      exact ⟨label.isLt, by have := bit.isLt; omega⟩
  constructor
  · cases h : s.path2 with
    | none => trivial
    | some p =>
      change p.label.val < ψ ∧ p.bit.val ≤ 1 ∧
        p.position.val ≤ ψ ∧ 1 ≤ p.action.val + 1 ∧
        p.action.val + 1 ≤ 6
      exact ⟨p.label.isLt,
        by have := p.bit.isLt; omega,
        by have := p.position.isLt; omega,
        by omega,
        by have := p.action.isLt; omega⟩
  constructor
  · cases h : s.path3 with
    | none => trivial
    | some p =>
      change p.label.val < ψ ∧ p.bit.val ≤ 1 ∧ p.flag.val ≤ 1
      exact ⟨p.label.isLt,
        by have := p.bit.isLt; omega,
        by have := p.flag.isLt; omega⟩
  constructor
  · cases h : s.path4 with
    | none => trivial
    | some p =>
      change (-1 : Int) ≤ eraseCleaningLabel p.1 ∧
        eraseCleaningLabel p.1 < Int.ofNat ψ ∧ p.2.val ≤ 1
      have hψ : 0 < ψ := Nat.zero_lt_of_lt s.label.isLt
      exact ⟨(eraseCleaningLabel_bounds hψ p.1).1,
        (eraseCleaningLabel_bounds hψ p.1).2,
        by have := p.2.isLt; omega⟩
  · cases h : s.path5 with
    | none => trivial
    | some p =>
      change (-1 : Int) ≤ eraseCleaningLabel p.1 ∧
        eraseCleaningLabel p.1 < Int.ofNat ψ ∧ p.2.val ≤ 1
      have hψ : 0 < ψ := Nat.zero_lt_of_lt s.label.isLt
      exact ⟨(eraseCleaningLabel_bounds hψ p.1).1,
        (eraseCleaningLabel_bounds hψ p.1).2,
        by have := p.2.isLt; omega⟩

/-- Erasing and then reifying a bounded state returns the same state. -/
theorem ofDomain_erase {ψ κ : Nat} (s : BoundedAgentState ψ κ) :
    ofDomain (erase s) (erase_inProtocolDomain s) = s := by
  cases s
  simp only [ofDomain, erase, BoundedAgentState.mk.injEq, true_and,
    and_true, eq_self]
  constructor
  · exact reify_erasePath _ _
  constructor
  · exact reify_erasePath2Option _ _
  constructor
  · exact reify_erasePath3Option _ _
  constructor
  · exact reify_eraseCleanPathOption _ _
  · exact reify_eraseCleanPathOption _ _

/-- Erasure packaged with its value-range certificate. -/
def eraseToDomain {ψ κ : Nat} (s : BoundedAgentState ψ κ) :
    {u : AgentState ψ // u.inProtocolDomain κ} :=
  ⟨erase s, erase_inProtocolDomain s⟩

/-- Reification of a certified audit state. -/
def ofDomainSubtype {ψ κ : Nat}
    (s : {u : AgentState ψ // u.inProtocolDomain κ}) :
    BoundedAgentState ψ κ :=
  ofDomain s.1 s.2

theorem ofDomainSubtype_eraseToDomain {ψ κ : Nat}
    (s : BoundedAgentState ψ κ) :
    ofDomainSubtype (eraseToDomain s) = s :=
  ofDomain_erase s

theorem eraseToDomain_ofDomainSubtype {ψ κ : Nat}
    (s : {u : AgentState ψ // u.inProtocolDomain κ}) :
    eraseToDomain (ofDomainSubtype s) = s := by
  apply Subtype.ext
  exact erase_ofDomain s.1 s.2

/-- A no-Mathlib bijection witness between the finite representation and the
value-bounded part of the audit representation. -/
theorem eraseToDomain_bijective {ψ κ : Nat} :
    Function.Injective (@eraseToDomain ψ κ) ∧
      Function.Surjective (@eraseToDomain ψ κ) := by
  constructor
  · exact Function.LeftInverse.injective ofDomainSubtype_eraseToDomain
  · exact Function.RightInverse.surjective eraseToDomain_ofDomainSubtype

end BoundedAgentState
