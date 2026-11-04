import Leader.L3.Headline.Statement
import Leader.L3.ParamsFacts

/-!
# State count (`prop:states`, clause 0 of `L3Headline`)

`Agent (compileAdvice q)` is in bijection with `Fin (agentCard c)`, and
`agentCard c ≤ stateBudget c.s` for `q ≥ 3`.  The bijection is built structurally from combinators
(`Bij.prod`, `Bij.sum`, `Bij.option`, `Bij.map`) on the field types; `Agent c` is identified with
a flat product type `T` of its fields by `toT` / `ofT`, whose round trips hold definitionally.

Exact count, factor by factor, against `stateBudget` (`renewal.tex:1356`):

| field(s) of `Agent c` | exact count | factor of the paper |
|---|---|---|
| `l b sh sg mode bit tok req grant C alpha m EU ED u beta` | `2·3·2·2·6·2·9·2^9` | inside `M_0` |
| `ser` (5 enums) | `3·3·4·3·4 = 432` | inside `M_0` |
| `si.kind busy cur z p a`, `wBase`, `wCarry`, `qCarry`, `topDirty` | `3·2·3·2·2·2·3·3·5·2` | inside `M_0` |
| `small` | `kStar + 2 = 201` | `201` |
| `d` | `a = topA` | `a` |
| `wOut`, `qOut` | `2 + 2a = A` each | `A^2` |
| `wIn`, `qIn` | `2 + 4a = B` each | `B^2` |
| `rawKick`, `rawTok` | `2·(1 + 32 t)` | `64 s + 2` |
| `h` | `34 t + 3` | `34 s + 3` |
| `kH`, `si.j` | `(t+1)^2` | `(s+1)^2` |
| `siLease` | `8 t + 5` | `8 s + 5` |
| `pack` | `b + 2 = s + 13` | `s + 13` |
| `lease` | `13 (b+2) + 1 = 13 (s+13) + 1` | `13 (s+13) + 1` |

The constant part is `7430083706880 ≤ M_0 = 97086427103232`; each `t`-dependent factor is monotone in
`t ≤ s`.  No factor of the exact count is outside the paper's product.
-/

namespace L3

set_option autoImplicit false

/-! ## Bijection combinators -/

/-- `α` is in bijection with `Fin n` (explicit decoder, injective and surjective). -/
def Bij (α : Type) (n : Nat) : Prop :=
  ∃ dec : Fin n → α, (∀ i j, dec i = dec j → i = j) ∧ (∀ a, ∃ i, dec i = a)

theorem Bij.fin (n : Nat) : Bij (Fin n) n :=
  ⟨fun i => i, fun _ _ h => h, fun a => ⟨a, rfl⟩⟩

theorem Bij.unit : Bij Unit 1 :=
  ⟨fun _ => (), fun i j _ => Fin.ext (by have := i.isLt; have := j.isLt; omega),
    fun _ => ⟨⟨0, by omega⟩, rfl⟩⟩

theorem Bij.bool : Bij Bool 2 :=
  ⟨fun i => decide (i.val = 1), by decide, by
    intro b
    cases b
    · exact ⟨⟨0, by omega⟩, by decide⟩
    · exact ⟨⟨1, by omega⟩, by decide⟩⟩

theorem Bij.map {α β : Type} {n : Nat} (h : Bij α n) (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) : Bij β n := by
  obtain ⟨d, hinj, hsurj⟩ := h
  refine ⟨fun i => f (d i), ?_, ?_⟩
  · intro i j hij
    apply hinj
    have := congrArg g hij
    rw [hgf, hgf] at this
    exact this
  · intro b
    obtain ⟨i, hi⟩ := hsurj (g b)
    refine ⟨i, ?_⟩
    show f (d i) = b
    rw [hi]
    exact hfg b

theorem Bij.cast {α : Type} {n m : Nat} (h : Bij α n) (e : n = m) : Bij α m := by
  subst e; exact h

theorem pos_of_fin_mul {n m : Nat} (k : Fin (n * m)) : 0 < m :=
  Nat.pos_of_ne_zero (by
    intro h; subst h; have := k.isLt; omega)

/-- Mixed-radix decoder for products. -/
def prodDec {α β : Type} {n m : Nat} (d1 : Fin n → α) (d2 : Fin m → β) (k : Fin (n * m)) :
    α × β :=
  (d1 ⟨k.val / m, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm n m))⟩,
   d2 ⟨k.val % m, Nat.mod_lt _ (pos_of_fin_mul k)⟩)

theorem Bij.prod {α β : Type} {n m : Nat} (ha : Bij α n) (hb : Bij β m) : Bij (α × β) (n * m) := by
  obtain ⟨d1, i1, s1⟩ := ha
  obtain ⟨d2, i2, s2⟩ := hb
  refine ⟨prodDec d1 d2, ?_, ?_⟩
  · intro k k' h
    unfold prodDec at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : k.val / m = k'.val / m := congrArg Fin.val (i1 _ _ h1)
    have e2 : k.val % m = k'.val % m := congrArg Fin.val (i2 _ _ h2)
    apply Fin.ext
    have a1 := Nat.div_add_mod k.val m
    have a2 := Nat.div_add_mod k'.val m
    calc k.val = m * (k.val / m) + k.val % m := a1.symm
      _ = m * (k'.val / m) + k'.val % m := by rw [e1, e2]
      _ = k'.val := a2
  · rintro ⟨a, b⟩
    obtain ⟨i, hi⟩ := s1 a
    obtain ⟨j, hj⟩ := s2 b
    have hjm := j.isLt
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hjm
    have h1 : m * (i.val + 1) ≤ m * n := Nat.mul_le_mul_left m i.isLt
    have h2 : m * (i.val + 1) = m * i.val + m := Nat.mul_succ m i.val
    have hlt : m * i.val + j.val < n * m := by
      rw [Nat.mul_comm n m]; omega
    refine ⟨⟨m * i.val + j.val, hlt⟩, ?_⟩
    have hq : (m * i.val + j.val) / m = i.val := by
      rw [Nat.mul_add_div hm]; simp [Nat.div_eq_of_lt hjm]
    have hr : (m * i.val + j.val) % m = j.val := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hjm]
    refine Prod.ext ?_ ?_
    · show d1 ⟨(m * i.val + j.val) / m, _⟩ = a
      rw [← hi]; exact congrArg d1 (Fin.ext hq)
    · show d2 ⟨(m * i.val + j.val) % m, _⟩ = b
      rw [← hj]; exact congrArg d2 (Fin.ext hr)

def sumDec {α β : Type} {n m : Nat} (d1 : Fin n → α) (d2 : Fin m → β) (k : Fin (n + m)) :
    α ⊕ β :=
  if h : k.val < n then Sum.inl (d1 ⟨k.val, h⟩)
  else Sum.inr (d2 ⟨k.val - n, by have := k.isLt; omega⟩)

theorem sumDec_lt {α β : Type} {n m : Nat} (d1 : Fin n → α) (d2 : Fin m → β) (k : Fin (n + m))
    (h : k.val < n) : sumDec d1 d2 k = Sum.inl (d1 ⟨k.val, h⟩) := by
  unfold sumDec; rw [dif_pos h]

theorem sumDec_ge {α β : Type} {n m : Nat} (d1 : Fin n → α) (d2 : Fin m → β) (k : Fin (n + m))
    (h : ¬ k.val < n) :
    sumDec d1 d2 k = Sum.inr (d2 ⟨k.val - n, by have := k.isLt; omega⟩) := by
  unfold sumDec; rw [dif_neg h]

theorem Bij.sum {α β : Type} {n m : Nat} (ha : Bij α n) (hb : Bij β m) : Bij (α ⊕ β) (n + m) := by
  obtain ⟨d1, i1, s1⟩ := ha
  obtain ⟨d2, i2, s2⟩ := hb
  refine ⟨sumDec d1 d2, ?_, ?_⟩
  · intro k k' h
    by_cases c1 : k.val < n <;> by_cases c2 : k'.val < n
    · rw [sumDec_lt d1 d2 k c1, sumDec_lt d1 d2 k' c2] at h
      exact Fin.ext (Fin.mk.inj (i1 _ _ (Sum.inl.inj h)))
    · rw [sumDec_lt d1 d2 k c1, sumDec_ge d1 d2 k' c2] at h
      cases h
    · rw [sumDec_ge d1 d2 k c1, sumDec_lt d1 d2 k' c2] at h
      cases h
    · rw [sumDec_ge d1 d2 k c1, sumDec_ge d1 d2 k' c2] at h
      have e : k.val - n = k'.val - n := congrArg Fin.val (i2 _ _ (Sum.inr.inj h))
      exact Fin.ext (by omega)
  · intro o
    cases o with
    | inl a =>
      obtain ⟨i, hi⟩ := s1 a
      refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      exact (sumDec_lt d1 d2 _ i.isLt).trans (congrArg Sum.inl hi)
    | inr b =>
      obtain ⟨j, hj⟩ := s2 b
      have hjm := j.isLt
      refine ⟨⟨n + j.val, by omega⟩, ?_⟩
      exact (sumDec_ge d1 d2 _ (by show ¬ (n + j.val < n); omega)).trans
        (congrArg Sum.inr ((congrArg d2 (Fin.ext (by simp))).trans hj))

def optDec {α : Type} {n : Nat} (d : Fin n → α) (k : Fin (n + 1)) : Option α :=
  if h : k.val = 0 then none else some (d ⟨k.val - 1, by have := k.isLt; omega⟩)

theorem optDec_zero {α : Type} {n : Nat} (d : Fin n → α) (k : Fin (n + 1)) (h : k.val = 0) :
    optDec d k = none := by
  unfold optDec; rw [dif_pos h]

theorem optDec_succ {α : Type} {n : Nat} (d : Fin n → α) (k : Fin (n + 1)) (h : ¬ k.val = 0) :
    optDec d k = some (d ⟨k.val - 1, by have := k.isLt; omega⟩) := by
  unfold optDec; rw [dif_neg h]

theorem Bij.option {α : Type} {n : Nat} (h : Bij α n) : Bij (Option α) (n + 1) := by
  obtain ⟨d, hi, hs⟩ := h
  refine ⟨optDec d, ?_, ?_⟩
  · intro k k' hk
    by_cases h0 : k.val = 0 <;> by_cases h0' : k'.val = 0
    · exact Fin.ext (by omega)
    · rw [optDec_zero d k h0, optDec_succ d k' h0'] at hk
      cases hk
    · rw [optDec_succ d k h0, optDec_zero d k' h0'] at hk
      cases hk
    · rw [optDec_succ d k h0, optDec_succ d k' h0'] at hk
      have e : k.val - 1 = k'.val - 1 := congrArg Fin.val (hi _ _ (Option.some.inj hk))
      exact Fin.ext (by omega)
  · intro o
    cases o with
    | none => exact ⟨⟨0, by omega⟩, optDec_zero d _ rfl⟩
    | some a =>
      obtain ⟨i, hi'⟩ := hs a
      have hil := i.isLt
      refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
      exact (optDec_succ d _ (by show ¬ (i.val + 1 = 0); omega)).trans
        (congrArg some ((congrArg d (Fin.ext (by simp))).trans hi'))

@[inherit_doc] local infixr:70 " ⊗ " => Bij.prod

/-- Bijection with `Fin k` from an explicit index pair. -/
theorem bij_of_idx {E : Type} (k : Nat) (ofIdx : Fin k → E) (toIdx : E → Fin k)
    (h1 : ∀ i, toIdx (ofIdx i) = i) (h2 : ∀ e, ofIdx (toIdx e) = e) : Bij E k :=
  Bij.map (Bij.fin k) ofIdx toIdx h1 h2

/-! ## Enumerations -/

def modeOf (i : Fin 6) : Mode :=
  [Mode.RESET, .RWAIT, .ARMED, .IWAIT, .CSTART, .CWAIT].getD i.val .RESET
def modeTo : Mode → Fin 6
  | .RESET => 0 | .RWAIT => 1 | .ARMED => 2 | .IWAIT => 3 | .CSTART => 4 | .CWAIT => 5
theorem bij_mode : Bij Mode 6 :=
  bij_of_idx 6 modeOf modeTo (by decide) (by intro e; cases e <;> rfl)

def btokOf (i : Fin 9) : BTok :=
  [BTok.E, .RR, .RL, .IR, .AL, .CR0, .CR1, .CL0, .CL1].getD i.val .E
def btokTo : BTok → Fin 9
  | .E => 0 | .RR => 1 | .RL => 2 | .IR => 3 | .AL => 4 | .CR0 => 5 | .CR1 => 6
  | .CL0 => 7 | .CL1 => 8
theorem bij_btok : Bij BTok 9 :=
  bij_of_idx 9 btokOf btokTo (by decide) (by intro e; cases e <;> rfl)

def sphaseOf (i : Fin 3) : SerPhase := [SerPhase.C, .B, .F].getD i.val .C
def sphaseTo : SerPhase → Fin 3 | .C => 0 | .B => 1 | .F => 2
theorem bij_sphase : Bij SerPhase 3 :=
  bij_of_idx 3 sphaseOf sphaseTo (by decide) (by intro e; cases e <;> rfl)

def soutOf (i : Fin 3) : SerOut := [SerOut.NEW, .WAIT, .DONE].getD i.val .NEW
def soutTo : SerOut → Fin 3 | .NEW => 0 | .WAIT => 1 | .DONE => 2
theorem bij_sout : Bij SerOut 3 :=
  bij_of_idx 3 soutOf soutTo (by decide) (by intro e; cases e <;> rfl)

def sprobeOf (i : Fin 4) : SerProbe :=
  [SerProbe.NONE, .PENDING, .INTERNAL_OK, .LEAF_OK].getD i.val .NONE
def sprobeTo : SerProbe → Fin 4 | .NONE => 0 | .PENDING => 1 | .INTERNAL_OK => 2 | .LEAF_OK => 3
theorem bij_sprobe : Bij SerProbe 4 :=
  bij_of_idx 4 sprobeOf sprobeTo (by decide) (by intro e; cases e <;> rfl)

def scertOf (i : Fin 3) : SerCert := [SerCert.IDLE, .REQUESTED, .RUNNING].getD i.val .IDLE
def scertTo : SerCert → Fin 3 | .IDLE => 0 | .REQUESTED => 1 | .RUNNING => 2
theorem bij_scert : Bij SerCert 3 :=
  bij_of_idx 3 scertOf scertTo (by decide) (by intro e; cases e <;> rfl)

def swphaseOf (i : Fin 4) : SerWPhase :=
  [SerWPhase.OFF, .QUARANTINE, .VALIDATING, .CURRENT].getD i.val .OFF
def swphaseTo : SerWPhase → Fin 4 | .OFF => 0 | .QUARANTINE => 1 | .VALIDATING => 2 | .CURRENT => 3
theorem bij_swphase : Bij SerWPhase 4 :=
  bij_of_idx 4 swphaseOf swphaseTo (by decide) (by intro e; cases e <;> rfl)

def sikindOf (i : Fin 3) : SIKind := [SIKind.OFF, .PREFIX, .ROOT].getD i.val .OFF
def sikindTo : SIKind → Fin 3 | .OFF => 0 | .PREFIX => 1 | .ROOT => 2
theorem bij_sikind : Bij SIKind 3 :=
  bij_of_idx 3 sikindOf sikindTo (by decide) (by intro e; cases e <;> rfl)

def sicurOf (i : Fin 3) : SICur := [SICur.NONE, .BACK, .SUM].getD i.val .NONE
def sicurTo : SICur → Fin 3 | .NONE => 0 | .BACK => 1 | .SUM => 2
theorem bij_sicur : Bij SICur 3 :=
  bij_of_idx 3 sicurOf sicurTo (by decide) (by intro e; cases e <;> rfl)

def wbaseOf (i : Fin 3) : WBase := [WBase.NONE, .SEEK, .ZERO].getD i.val .NONE
def wbaseTo : WBase → Fin 3 | .NONE => 0 | .SEEK => 1 | .ZERO => 2
theorem bij_wbase : Bij WBase 3 :=
  bij_of_idx 3 wbaseOf wbaseTo (by decide) (by intro e; cases e <;> rfl)

/-! ## Records and tagged tokens -/

theorem bij_ser : Bij Ser (3 * (3 * (4 * (3 * 4)))) :=
  (bij_sphase ⊗ bij_sout ⊗ bij_sprobe ⊗ bij_scert ⊗ bij_swphase).map
    (fun p => { phase := p.1, out := p.2.1, probe := p.2.2.1, cert := p.2.2.2.1,
                wphase := p.2.2.2.2 })
    (fun s => (s.phase, s.out, s.probe, s.cert, s.wphase))
    (fun _ => rfl) (fun _ => rfl)

/-- `Small` has `kStar + 2 = 201` values: `OFF`, `SPENT`, `RUN j` with `j < kStar`. -/
theorem bij_small : Bij Small 201 :=
  ((Bij.unit.sum (Bij.unit.sum (Bij.fin kStar))).map
    (fun x => match x with
      | .inl _ => Small.OFF
      | .inr (.inl _) => Small.SPENT
      | .inr (.inr j) => Small.RUN j)
    (fun s => match s with
      | .OFF => .inl ()
      | .SPENT => .inr (.inl ())
      | .RUN j => .inr (.inr j))
    (by intro x; rcases x with u | u | j <;> rfl)
    (by intro s; cases s <;> rfl)).cast (by decide)

theorem bij_out (A : Nat) : Bij (OutTok A) (2 + 2 * A) :=
  ((Bij.unit.sum (Bij.unit.sum ((Bij.fin A) ⊗ Bij.bool))).map
    (fun x => match x with
      | .inl _ => OutTok.E
      | .inr (.inl _) => OutTok.U
      | .inr (.inr p) => OutTok.D p.1 p.2)
    (fun s => match s with
      | .E => .inl ()
      | .U => .inr (.inl ())
      | .D v T => .inr (.inr (v, T)))
    (by intro x; rcases x with u | u | p <;> rfl)
    (by intro s; cases s <;> rfl)).cast (by omega)

theorem bij_in (A : Nat) : Bij (InTok A) (2 + 4 * A) :=
  ((Bij.unit.sum (Bij.unit.sum (((Bij.fin A) ⊗ Bij.bool).sum ((Bij.fin A) ⊗ Bij.bool)))).map
    (fun x => match x with
      | .inl _ => InTok.E
      | .inr (.inl _) => InTok.X
      | .inr (.inr (.inl p)) => InTok.P p.1 p.2
      | .inr (.inr (.inr p)) => InTok.S p.1 p.2)
    (fun s => match s with
      | .E => .inl ()
      | .X => .inr (.inl ())
      | .P v T => .inr (.inr (.inl (v, T)))
      | .S v T => .inr (.inr (.inr (v, T))))
    (by intro x; rcases x with u | u | p | p <;> rfl)
    (by intro s; cases s <;> rfl)).cast (by omega)

theorem bij_wcarry : Bij WCarry 3 :=
  ((Bij.unit.sum Bij.bool).map
    (fun x => match x with
      | .inl _ => WCarry.OFF
      | .inr c => WCarry.W c)
    (fun s => match s with
      | .OFF => .inl ()
      | .W c => .inr c)
    (by intro x; rcases x with u | c <;> rfl)
    (by intro s; cases s <;> rfl))

theorem bij_qcarry : Bij QCarry 5 :=
  ((Bij.unit.sum (Bij.bool ⊗ Bij.bool)).map
    (fun x => match x with
      | .inl _ => QCarry.OFF
      | .inr p => QCarry.L p.1 p.2)
    (fun s => match s with
      | .OFF => .inl ()
      | .L c e => .inr (c, e))
    (by intro x; rcases x with u | p <;> rfl)
    (by intro s; cases s <;> rfl))

theorem bij_raw (t : Nat) : Bij (RawTok t) (t * (2 * (2 * (2 * (2 * 2))))) :=
  ((Bij.fin t) ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool).map
    (fun p => { jm1 := p.1, z := p.2.1, p := p.2.2.1, a := p.2.2.2.1, h := p.2.2.2.2.1,
                m := p.2.2.2.2.2 })
    (fun r => (r.jm1, r.z, r.p, r.a, r.h, r.m))
    (fun _ => rfl) (fun _ => rfl)

/-! ## The agent -/

/-- The fixed part of the agent (everything whose range does not depend on `c`). -/
abbrev BaseFields : Type := Bool × (Fin 3 × (Bool × (Bool × (Mode × (Bool × (BTok × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Bool × (Ser × (SIKind × (Bool × (SICur × (Bool × (Bool × (Bool × (WBase × (WCarry × (QCarry × (Bool))))))))))))))))))))))))))

/-- Exact count of `BaseFields`. -/
def cntBaseFields : Nat := 2 * (3 * (2 * (2 * (6 * (2 * (9 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * ((3 * (3 * (4 * (3 * 4)))) * (3 * (2 * (3 * (2 * (2 * (2 * (3 * (3 * (5 * (2))))))))))))))))))))))))))

theorem bij_baseFields : Bij BaseFields cntBaseFields := Bij.bool ⊗ (Bij.fin 3) ⊗ Bij.bool ⊗ Bij.bool ⊗ bij_mode ⊗ Bij.bool ⊗ bij_btok ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ bij_ser ⊗ bij_sikind ⊗ Bij.bool ⊗ bij_sicur ⊗ Bij.bool ⊗ Bij.bool ⊗ Bij.bool ⊗ bij_wbase ⊗ bij_wcarry ⊗ bij_qcarry ⊗ Bij.bool

/-- Exact number of local states of `Agent c` (product of the field-range sizes). -/
def agentCard (c : Compiled) : Nat := cntBaseFields * (201 * (c.topA * ((2 + 2 * c.topA) * ((2 + 2 * c.topA) * ((2 + 4 * c.topA) * ((2 + 4 * c.topA) * ((2 * (c.t * 32 + 1)) * ((34 * c.t + 3) * ((c.t + 1) * ((c.t + 1) * ((c.siLeaseMax + 1) * ((c.b + 2) * ((c.bankLeaseCap + 1))))))))))))))

/-- Flat product type of all fields. -/
abbrev AgentT (c : Compiled) : Type := BaseFields × Small × (Fin c.topA × (OutTok c.topA × (OutTok c.topA × (InTok c.topA × (InTok c.topA × ((Bool × Option (RawTok c.t)) × (Fin (34 * c.t + 3) × (Fin (c.t + 1) × (Fin (c.t + 1) × (Fin (c.siLeaseMax + 1) × (Fin (c.b + 2) × (Fin (c.bankLeaseCap + 1)))))))))))))

def Agent.toT {c : Compiled} (a : Agent c) : AgentT c := ((a.l, a.b, a.sh, a.sg, a.mode, a.bit, a.tok, a.req, a.grant, a.C, a.alpha, a.m, a.EU, a.ED, a.u, a.beta, a.ser, a.si.kind, a.si.busy, a.si.cur, a.si.z, a.si.p, a.si.a, a.wBase, a.wCarry, a.qCarry, a.topDirty), a.small, a.d, a.wOut, a.qOut, a.wIn, a.qIn, (a.rawKick, a.rawTok), a.h, a.kH, a.si.j, a.siLease, a.pack, a.lease)

def Agent.ofT {c : Compiled} (t : AgentT c) : Agent c :=
  { l := t.1.1, b := t.1.2.1, sh := t.1.2.2.1, sg := t.1.2.2.2.1,
    pack := t.2.2.2.2.2.2.2.2.2.2.2.2.1, mode := t.1.2.2.2.2.1, bit := t.1.2.2.2.2.2.1, tok := t.1.2.2.2.2.2.2.1,
    lease := t.2.2.2.2.2.2.2.2.2.2.2.2.2, small := t.2.1, req := t.1.2.2.2.2.2.2.2.1, grant := t.1.2.2.2.2.2.2.2.2.1,
    C := t.1.2.2.2.2.2.2.2.2.2.1, alpha := t.1.2.2.2.2.2.2.2.2.2.2.1, m := t.1.2.2.2.2.2.2.2.2.2.2.2.1, EU := t.1.2.2.2.2.2.2.2.2.2.2.2.2.1, ED := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    u := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, beta := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, d := t.2.2.1, ser := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    siLease := t.2.2.2.2.2.2.2.2.2.2.2.1,
    si := { kind := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, busy := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, cur := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, j := t.2.2.2.2.2.2.2.2.2.2.1, z := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, a := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 },
    rawKick := t.2.2.2.2.2.2.2.1.1, rawTok := t.2.2.2.2.2.2.2.1.2, h := t.2.2.2.2.2.2.2.2.1, kH := t.2.2.2.2.2.2.2.2.2.1,
    wBase := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, wOut := t.2.2.2.1, wIn := t.2.2.2.2.2.1, wCarry := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    qOut := t.2.2.2.2.1, qIn := t.2.2.2.2.2.2.1, qCarry := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, topDirty := t.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }

theorem bij_agent (c : Compiled) : Bij (Agent c) (agentCard c) :=
  (bij_baseFields ⊗ bij_small ⊗ (Bij.fin c.topA) ⊗ (bij_out c.topA) ⊗ (bij_out c.topA) ⊗ (bij_in c.topA) ⊗ (bij_in c.topA) ⊗ (Bij.bool ⊗ (bij_raw c.t).option) ⊗ (Bij.fin (34 * c.t + 3)) ⊗ (Bij.fin (c.t + 1)) ⊗ (Bij.fin (c.t + 1)) ⊗ (Bij.fin (c.siLeaseMax + 1)) ⊗ (Bij.fin (c.b + 2)) ⊗ (Bij.fin (c.bankLeaseCap + 1))).map Agent.ofT Agent.toT
    (fun _ => rfl) (fun a => by cases a; rfl)

/-! ## The budget -/

theorem compileAdvice_t_le_s (q : Nat) (h3 : 3 ≤ q) : (compileAdvice q).t ≤ (compileAdvice q).s := by
  by_cases h : q < 33
  · exact (by decide +kernel : ∀ q, q < 33 → 3 ≤ q → (compileAdvice q).t ≤ (compileAdvice q).s) q h h3
  · rw [compileAdvice_t_large q (by omega), compileAdvice_s]
    omega

theorem cntBaseFields_le : cntBaseFields ≤ 97086427103232 := by decide

theorem agentCard_le (c : Compiled) (hts : c.t ≤ c.s) : agentCard c ≤ stateBudget c.s := by
  have ha : c.topA = 2 ^ floorLogTwo c.s := rfl
  have hb : c.b = c.s + 11 := rfl
  have hl : c.bankLeaseCap = 13 * (c.b + 2) := rfl
  have hs : c.siLeaseMax = 8 * c.t + 4 := rfl
  unfold agentCard stateBudget
  have h64 : 2 * (c.t * 32 + 1) = 64 * c.t + 2 := by omega
  rw [h64]
  simp only [Nat.pow_two, Nat.mul_assoc]
  rw [ha]
  generalize 2 ^ floorLogTwo c.s = a
  refine Nat.mul_le_mul cntBaseFields_le (Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _)
    (Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _)
    (Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul ?_ (Nat.mul_le_mul ?_ (Nat.mul_le_mul ?_
    (Nat.mul_le_mul ?_ (Nat.mul_le_mul ?_ (Nat.mul_le_mul ?_ ?_))))))))))))
  all_goals omega

theorem ceilLogTwo_ge_three (n : Nat) (hn : 5 ≤ n) : 3 ≤ ceilLogTwo n := by
  have h := (ceilLogTwo_spec n (by omega)).2
  rcases Nat.lt_or_ge (ceilLogTwo n) 3 with hc | hc
  · have hk : ceilLogTwo n ≤ 2 := by omega
    have : 2 ^ ceilLogTwo n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hk
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    omega
  · exact hc

/-- Clause 0 of `L3Headline` (`prop:states`). -/
theorem stateCount (n : Nat) (hn : 5 ≤ n) :
    ∃ N, N ≤ stateBudget (compileAdvice (ceilLogTwo n)).s ∧
      ∃ decode : Fin N → Agent (compileAdvice (ceilLogTwo n)),
        (∀ i j, decode i = decode j → i = j) ∧ (∀ a, ∃ i, decode i = a) := by
  have h3 : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  refine ⟨agentCard (compileAdvice (ceilLogTwo n)), ?_, bij_agent _⟩
  exact agentCard_le _ (compileAdvice_t_le_s _ h3)

end L3
