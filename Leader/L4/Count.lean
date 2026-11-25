import Leader.L4.Statement
import Lean.Elab.Tactic.Omega

namespace L4

/-- A two-sided finite coding, with no dependency on Mathlib's cardinal API. -/
structure ExactCoding (α β : Type) where
  encode : α → β
  decode : β → α
  left_inv : ∀ a, decode (encode a) = a
  right_inv : ∀ b, encode (decode b) = b

namespace ExactCoding

def id (α : Type) : ExactCoding α α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

def trans (a : ExactCoding α β) (b : ExactCoding β γ) : ExactCoding α γ where
  encode x := b.encode (a.encode x)
  decode z := a.decode (b.decode z)
  left_inv x := by rw [b.left_inv, a.left_inv]
  right_inv z := by rw [a.right_inv, b.right_inv]

def prod (a : ExactCoding α β) (b : ExactCoding γ δ) :
    ExactCoding (α × γ) (β × δ) where
  encode x := (a.encode x.1, b.encode x.2)
  decode y := (a.decode y.1, b.decode y.2)
  left_inv x := by
    rcases x with ⟨x, y⟩
    change (a.decode (a.encode x), b.decode (b.encode y)) = (x, y)
    rw [a.left_inv, b.left_inv]
  right_inv z := by
    rcases z with ⟨x, y⟩
    change (a.encode (a.decode x), b.encode (b.decode y)) = (x, y)
    rw [a.right_inv, b.right_inv]

private theorem productRightPos (z : Fin (a * b)) : 0 < b := by
  cases b with
  | zero => exact Fin.elim0 (by simpa using z)
  | succ b => exact Nat.zero_lt_succ b

/-- Mixed-radix pairing, also covering the empty alphabet case. -/
def finProd (a b : Nat) : ExactCoding (Fin a × Fin b) (Fin (a * b)) where
  encode z := ⟨z.2.val + z.1.val * b, by
    have hstep : (z.1.val + 1) * b ≤ a * b :=
      Nat.mul_le_mul_right b z.1.isLt
    rw [Nat.add_mul, Nat.one_mul] at hstep
    have hlt := z.2.isLt
    omega⟩
  decode z := (⟨z.val / b, (Nat.div_lt_iff_lt_mul (productRightPos z)).2 z.isLt⟩,
    ⟨z.val % b, Nat.mod_lt _ (productRightPos z)⟩)
  left_inv z := by
    rcases z with ⟨i, j⟩
    apply Prod.ext
    · apply Fin.ext
      change (j.val + i.val * b) / b = i.val
      rw [Nat.add_mul_div_right j.val i.val (Nat.zero_lt_of_lt j.isLt),
        Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    · apply Fin.ext
      change (j.val + i.val * b) % b = j.val
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  right_inv z := by
    apply Fin.ext
    change z.val % b + (z.val / b) * b = z.val
    rw [Nat.mul_comm (z.val / b) b, Nat.mod_add_div]

/-- Finite alphabets multiply under products. -/
def pair (a : ExactCoding α (Fin m)) (b : ExactCoding β (Fin n)) :
    ExactCoding (α × β) (Fin (m * n)) :=
  (a.prod b).trans (finProd m n)

end ExactCoding

private def boolCoding : ExactCoding Bool (Fin 2) where
  encode x := if x then 1 else 0
  decode x := x.val == 1
  left_inv x := by cases x <;> rfl
  right_inv x := by
    apply Fin.ext
    have hlt := x.isLt
    by_cases h : x.val = 0
    · simp [h]
    · have h' : x.val = 1 := by omega
      simp [h']

private def bulletCoding : ExactCoding Bullet (Fin 3) where
  encode
    | .none => 0
    | .dummy => 1
    | .live => 2
  decode x :=
    match x.val with
    | 0 => .none
    | 1 => .dummy
    | _ => .live
  left_inv x := by cases x <;> rfl
  right_inv x := by
    apply Fin.ext
    have hlt := x.isLt
    have h : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases h with h | h | h <;> simp [h]

private def signalCoding : ExactCoding Signal (Fin 3) where
  encode
    | .zero => 0
    | .one => 1
    | .two => 2
  decode x :=
    match x.val with
    | 0 => .zero
    | 1 => .one
    | _ => .two
  left_inv x := by cases x <;> rfl
  right_inv x := by
    apply Fin.ext
    have hlt := x.isLt
    have h : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases h with h | h | h <;> simp [h]

private def railCoding : ExactCoding Rail (Fin 7) where
  encode
    | .e => 0
    | .t => 1
    | .ui => 2
    | .uc => 3
    | .di => 4
    | .dc => 5
    | .x => 6
  decode k :=
    match k.val with
    | 0 => .e
    | 1 => .t
    | 2 => .ui
    | 3 => .uc
    | 4 => .di
    | 5 => .dc
    | _ => .x
  left_inv k := by cases k <;> rfl
  right_inv k := by
    apply Fin.ext
    have hlt := k.isLt
    have h : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨
        k.val = 4 ∨ k.val = 5 ∨ k.val = 6 := by omega
    rcases h with h | h | h | h | h | h | h <;> simp [h] <;> decide

private def sourceEncode (Q : Nat) : Source Q → Fin (2 * Q + 3)
  | .off => ⟨0, by omega⟩
  | .i0 => ⟨1, by omega⟩
  | .i1 => ⟨2, by omega⟩
  | .count k => ⟨k.val + 3, by have h := k.isLt; omega⟩
  | .await k => ⟨Q + k.val + 3, by have h := k.isLt; omega⟩

private def sourceDecode (Q : Nat) (x : Fin (2 * Q + 3)) : Source Q :=
  if _h0 : x.val = 0 then .off else
  if _h1 : x.val = 1 then .i0 else
  if _h2 : x.val = 2 then .i1 else
  if h : x.val < Q + 3 then .count ⟨x.val - 3, by omega⟩
  else .await ⟨x.val - (Q + 3), by have h' := x.isLt; omega⟩

private def sourceCoding (Q : Nat) : ExactCoding (Source Q) (Fin (2 * Q + 3)) where
  encode := sourceEncode Q
  decode := sourceDecode Q
  left_inv x := by
    cases x with
    | off => simp [sourceEncode, sourceDecode]
    | i0 => simp [sourceEncode, sourceDecode]
    | i1 => simp [sourceEncode, sourceDecode]
    | count k =>
      have h := k.isLt
      have h1 : k.val + 3 ≠ 1 := by omega
      have h2 : k.val + 3 ≠ 2 := by omega
      have h3 : k.val + 3 < Q + 3 := by omega
      simp [sourceEncode, sourceDecode, h1, h2, h3]
    | await k =>
      have h1 : Q + k.val + 3 ≠ 1 := by omega
      have h2 : Q + k.val + 3 ≠ 2 := by omega
      have h3 : ¬ Q + k.val + 3 < Q + 3 := by omega
      have heq : Q + k.val + 3 - (Q + 3) = k.val := by omega
      simp [sourceEncode, sourceDecode, h1, h2, h3, heq]
  right_inv x := by
    apply Fin.ext
    unfold sourceDecode
    split
    · simp_all [sourceEncode]
    split
    · simp_all [sourceEncode]
    split
    · simp_all [sourceEncode]
    split <;> simp only [sourceEncode] <;> omega

private abbrev Fields (p c1 : Nat) :=
  Fin p × Bool × Bool × Bullet × Bool × Signal × Bool × Source (2 * c1) × Rail

private def fieldsCoding (p c1 : Nat) : ExactCoding (Site p c1) (Fields p c1) where
  encode z := (z.residue, z.mark, z.leader, z.bullet, z.shield,
    z.signal, z.stock, z.source, z.rail)
  decode z := ⟨z.1, z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1,
    z.2.2.2.2.2.1, z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨_, _, _, _, _, _, _, _, _⟩
    rfl

/-- The exact Cartesian alphabet size printed in the paper. -/
def stateCount (p c1 : Nat) : Nat := p * 1008 * (4 * c1 + 3)

private def stateCodingRaw (p c1 : Nat) :
    ExactCoding (Site p c1)
      (Fin (p * (2 * (2 * (3 * (2 * (3 * (2 * ((2 * (2 * c1) + 3) * 7))))))))) :=
  (fieldsCoding p c1).trans
    ((ExactCoding.id (Fin p)).pair <|
      boolCoding.pair <| boolCoding.pair <| bulletCoding.pair <| boolCoding.pair <|
      signalCoding.pair <| boolCoding.pair <| (sourceCoding (2 * c1)).pair railCoding)

/-- A bijection with the finite ordinal of size `stateCount p c1`.
No positivity assumptions are needed for the counting identity. -/
def stateCoding (p c1 : Nat) : ExactCoding (Site p c1) (Fin (stateCount p c1)) := by
  have hc : 2 * (2 * c1) + 3 = 4 * c1 + 3 := by omega
  have hs : p * (2 * (2 * (3 * (2 * (3 * (2 * ((2 * (2 * c1) + 3) * 7))))))) =
      stateCount p c1 := by
    rw [hc]
    calc
      _ = p * (2 * 2 * 3 * 2 * 3 * 2 * (4 * c1 + 3) * 7) := by
        simp only [Nat.mul_assoc]
      _ = p * (2 * 2 * 3 * 2 * 3 * 2 * 7 * (4 * c1 + 3)) := by
        rw [Nat.mul_right_comm (2 * 2 * 3 * 2 * 3 * 2) (4 * c1 + 3) 7]
      _ = stateCount p c1 := by
        unfold stateCount
        rw [Nat.mul_assoc p 1008]
  exact hs ▸ stateCodingRaw p c1

theorem stateCountExact (p c1 : Nat) :
    ∃ encode : Site p c1 → Fin (p * 1008 * (4 * c1 + 3)),
      ∃ decode : Fin (p * 1008 * (4 * c1 + 3)) → Site p c1,
        (∀ z, decode (encode z) = z) ∧ (∀ k, encode (decode k) = k) :=
  ⟨(stateCoding p c1).encode, (stateCoding p c1).decode,
    (stateCoding p c1).left_inv, (stateCoding p c1).right_inv⟩

/-- The alphabet-size conjunct of the L4 headline holds unconditionally. -/
theorem stateCount_headline (p c1 : Nat) : StateCount p c1 := by
  unfold StateCount
  let c := stateCoding p c1
  refine ⟨c.decode, ?_, ?_⟩
  · intro i j h
    have h' := congrArg c.encode h
    rw [c.right_inv i, c.right_inv j] at h'
    exact h'
  · intro x
    exact ⟨c.encode x, c.left_inv x⟩

end L4
