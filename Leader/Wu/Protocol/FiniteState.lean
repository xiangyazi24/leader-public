import Leader.Wu.Protocol.BoundedState
import Init.Data.List.OfFn
import Init.Data.List.Lemmas
import Init.Data.List.Pairwise

/-!
# Explicit finite-state certificate

Lean core does not provide Mathlib's `Fintype` hierarchy.  An
`ExhaustiveList α` is a constructive finiteness witness: one concrete list
contains every value of `α`.  The final certificate is assembled through
balanced products and never evaluates the enormous state list.
-/

universe u v

structure ExhaustiveList (α : Type u) where
  values : List α
  complete : ∀ x : α, x ∈ values

namespace ExhaustiveList

private theorem nodup_map_of_injective {xs : List α}
    (hxs : xs.Nodup) (f : α → β) (hf : Function.Injective f) :
    (xs.map f).Nodup := by
  exact List.Pairwise.map f (fun _ _ hne => hf.ne hne) hxs

private theorem nodup_ofFn_of_injective {n : Nat}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        rw [List.mem_ofFn] at hm
        obtain ⟨i, hi⟩ := hm
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- Canonical exhaustive list for a finite index type. -/
def fin (n : Nat) : ExhaustiveList (Fin n) where
  values := List.ofFn (fun i : Fin n => i)
  complete := by
    intro i
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Exhaustive Boolean list. -/
def bool : ExhaustiveList Bool where
  values := [false, true]
  complete := by
    intro b
    cases b <;> simp

/-- Exhaustiveness is preserved by `Option`. -/
def option (A : ExhaustiveList α) : ExhaustiveList (Option α) where
  values := none :: A.values.map some
  complete := by
    intro x
    cases x with
    | none => simp
    | some a => exact List.Mem.tail none (List.mem_map_of_mem (A.complete a))

/-- Cartesian product of exhaustive lists. -/
def prod (A : ExhaustiveList α) (B : ExhaustiveList β) :
    ExhaustiveList (α × β) where
  values := A.values.flatMap (fun a => B.values.map (fun b => (a, b)))
  complete := by
    intro x
    rcases x with ⟨a, b⟩
    exact List.mem_flatMap_of_mem (A.complete a)
      (List.mem_map_of_mem (B.complete b))

private theorem sum_map_const (xs : List α) (n : Nat) :
    (xs.map fun _ => n).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons _ xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- Cartesian-product certificates multiply list lengths exactly. This counts
certificate entries; without `Nodup` it is only a state-cardinality upper bound. -/
theorem values_length_prod (A : ExhaustiveList α) (B : ExhaustiveList β) :
    (prod A B).values.length = A.values.length * B.values.length := by
  simp only [prod, List.length_flatMap, List.length_map]
  exact sum_map_const A.values B.values.length

/-- Canonical finite-index values contain no duplicates. -/
theorem values_nodup_fin (n : Nat) : (fin n).values.Nodup := by
  apply nodup_ofFn_of_injective
  intro i j h
  exact h

/-- The Boolean certificate contains no duplicates. -/
theorem values_nodup_bool : bool.values.Nodup := by
  decide

/-- Option preserves duplicate-freedom. -/
theorem values_nodup_option (A : ExhaustiveList α)
    (hA : A.values.Nodup) : (option A).values.Nodup := by
  change (none :: A.values.map some).Nodup
  rw [List.nodup_cons]
  constructor
  · simp
  · exact nodup_map_of_injective hA some (by
      intro a b h
      simpa using h)

/-- Cartesian product preserves duplicate-freedom. -/
theorem values_nodup_prod (A : ExhaustiveList α) (B : ExhaustiveList β)
    (hA : A.values.Nodup) (hB : B.values.Nodup) :
    (prod A B).values.Nodup := by
  change (A.values.flatMap
    (fun a => B.values.map (fun b => (a, b)))).Nodup
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  constructor
  · intro a ha
    exact nodup_map_of_injective hB (fun b => (a, b)) (by
      intro x y h
      exact congrArg Prod.snd h)
  · exact hA.imp (by
      intro a₁ a₂ ha x hx y hy hxy
      rcases List.mem_map.mp hx with ⟨b₁, _, rfl⟩
      rcases List.mem_map.mp hy with ⟨b₂, _, rfl⟩
      exact ha (congrArg Prod.fst hxy))

/-- The canonical finite-index certificate has exactly `n` entries. -/
theorem values_length_fin (n : Nat) : (fin n).values.length = n := by
  simp [fin]

/-- The Boolean certificate has two entries. -/
theorem values_length_bool : bool.values.length = 2 := by
  rfl

/-- Push an exhaustive list through a surjective decoder. -/
def mapSurjective (A : ExhaustiveList α) (f : α → β)
    (hf : Function.Surjective f) : ExhaustiveList β where
  values := A.values.map f
  complete := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact List.mem_map_of_mem (A.complete x)

/-- An injective decoder maps a duplicate-free certificate to another
duplicate-free certificate. -/
theorem values_nodup_mapSurjective (A : ExhaustiveList α)
    (f : α → β) (hf : Function.Surjective f)
    (hA : A.values.Nodup) (hinj : Function.Injective f) :
    (mapSurjective A f hf).values.Nodup := by
  change (A.values.map f).Nodup
  exact nodup_map_of_injective hA f hinj

/-- Mapping a certificate does not change its list length, even when the map is
not injective. -/
theorem values_length_mapSurjective (A : ExhaustiveList α) (f : α → β)
    (hf : Function.Surjective f) :
    (mapSurjective A f hf).values.length = A.values.length := by
  simp [mapSurjective]

/-- Finite-index decoder carried by any exhaustive list. -/
def decode (A : ExhaustiveList α) : Fin A.values.length → α :=
  A.values.get

/-- Duplicate-free certificate values make the finite-index decoder injective. -/
theorem decode_injective_of_values_nodup (A : ExhaustiveList α)
    (hA : A.values.Nodup) : Function.Injective A.decode := by
  intro i j hij
  apply Fin.ext
  apply (List.getElem_inj (i := i.val) (j := j.val) hA).mp
  simpa [decode, List.get_eq_getElem] using hij

/-- Every value is represented by a finite index into the exhaustive list. -/
theorem decode_surjective (A : ExhaustiveList α) :
    Function.Surjective A.decode := by
  intro x
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (A.complete x)
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [decode, List.get_eq_getElem]
  exact hget

end ExhaustiveList

namespace PPLLFinite

/-- Exact `MainState` constructor enumeration. -/
def mainState : ExhaustiveList MainState where
  values := [.produce, .done, .depart, .none, .congest, .lock,
    .compare1, .compare2, .eliminate_signal, .CHECK_ready,
    .equal, .larger, .less, .toss, .toss_done]
  complete := by intro s; cases s <;> simp

/-- Exact `WriteState` constructor enumeration. -/
def writeState : ExhaustiveList WriteState where
  values := [.depart, .ready, .increment_WS, .increment_WS_done,
    .done, .equal, .larger, .less, .produce, .overwrite,
    .move_flip, .move, .increment_group, .none]
  complete := by intro s; cases s <;> simp

/-- Exact `WriteAction` constructor enumeration. -/
def writeAction : ExhaustiveList WriteAction where
  values := [.overwrite, .move_flip, .move, .increment_group, .none]
  complete := by intro a; cases a <;> simp

private def boundedPathInfoSource (ψ : Nat) :
    ExhaustiveList (Option (Fin ψ × Fin 2)) :=
  (ExhaustiveList.prod (ExhaustiveList.fin ψ)
    (ExhaustiveList.fin 2)).option

def boundedPathInfo (ψ : Nat) : ExhaustiveList (BoundedPathInfo ψ) :=
  ExhaustiveList.mapSurjective (boundedPathInfoSource ψ)
    (fun x => match x with
      | none => .bot
      | some (label, bit) => .some label bit)
    (by
      intro p
      cases p with
      | bot => exact ⟨none, rfl⟩
      | some label bit => exact ⟨some (label, bit), rfl⟩)

private def boundedPath2InfoSource (ψ : Nat) :
    ExhaustiveList ((Fin ψ × Fin 2) × (Fin (ψ + 1) × Fin 6)) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod (ExhaustiveList.fin ψ) (ExhaustiveList.fin 2))
    (ExhaustiveList.prod (ExhaustiveList.fin (ψ + 1))
      (ExhaustiveList.fin 6))

def boundedPath2Info (ψ : Nat) : ExhaustiveList (BoundedPath2Info ψ) :=
  ExhaustiveList.mapSurjective (boundedPath2InfoSource ψ)
    (fun x =>
      { label := x.1.1, bit := x.1.2,
        position := x.2.1, action := x.2.2 })
    (by
      intro p
      exact ⟨((p.label, p.bit), (p.position, p.action)), by cases p; rfl⟩)

private def boundedPath3InfoSource (ψ : Nat) :
    ExhaustiveList (Fin ψ × (Fin 2 × Fin 2)) :=
  ExhaustiveList.prod (ExhaustiveList.fin ψ)
    (ExhaustiveList.prod (ExhaustiveList.fin 2) (ExhaustiveList.fin 2))

def boundedPath3Info (ψ : Nat) : ExhaustiveList (BoundedPath3Info ψ) :=
  ExhaustiveList.mapSurjective (boundedPath3InfoSource ψ)
    (fun x => { label := x.1, bit := x.2.1, flag := x.2.2 })
    (by
      intro p
      exact ⟨(p.label, (p.bit, p.flag)), by cases p; rfl⟩)

def cleaningLabel (ψ : Nat) : ExhaustiveList (CleaningLabel ψ) :=
  ExhaustiveList.mapSurjective (ExhaustiveList.option (ExhaustiveList.fin ψ))
    (fun x => match x with
      | none => .clean
      | some label => .normal label)
    (by
      intro c
      cases c with
      | normal label => exact ⟨some label, rfl⟩
      | clean => exact ⟨none, rfl⟩)

def boundedPath2Option (ψ : Nat) :
    ExhaustiveList (Option (BoundedPath2Info ψ)) :=
  (boundedPath2Info ψ).option

def boundedPath3Option (ψ : Nat) :
    ExhaustiveList (Option (BoundedPath3Info ψ)) :=
  (boundedPath3Info ψ).option

def boundedCleanPathOption (ψ : Nat) :
    ExhaustiveList (Option (CleaningLabel ψ × Fin 2)) :=
  (ExhaustiveList.prod (cleaningLabel ψ) (ExhaustiveList.fin 2)).option

/-! ## Duplicate-free path certificates -/

private theorem mainState_values_nodup : mainState.values.Nodup := by decide
private theorem writeState_values_nodup : writeState.values.Nodup := by decide
private theorem writeAction_values_nodup : writeAction.values.Nodup := by decide

private theorem boundedPathInfoSource_values_nodup (ψ : Nat) :
    (boundedPathInfoSource ψ).values.Nodup := by
  apply ExhaustiveList.values_nodup_option
  apply ExhaustiveList.values_nodup_prod
  · exact ExhaustiveList.values_nodup_fin ψ
  · exact ExhaustiveList.values_nodup_fin 2

private theorem boundedPathInfo_values_nodup (ψ : Nat) :
    (boundedPathInfo ψ).values.Nodup := by
  unfold boundedPathInfo
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact boundedPathInfoSource_values_nodup ψ
  · intro x y h
    cases x <;> cases y <;> simp_all [Prod.ext_iff]

private theorem boundedPath2InfoSource_values_nodup (ψ : Nat) :
    (boundedPath2InfoSource ψ).values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_fin ψ
    · exact ExhaustiveList.values_nodup_fin 2
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_fin (ψ + 1)
    · exact ExhaustiveList.values_nodup_fin 6

private theorem boundedPath2Info_values_nodup (ψ : Nat) :
    (boundedPath2Info ψ).values.Nodup := by
  unfold boundedPath2Info
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact boundedPath2InfoSource_values_nodup ψ
  · intro x y h
    rcases x with ⟨⟨xl, xb⟩, ⟨xp, xa⟩⟩
    rcases y with ⟨⟨yl, yb⟩, ⟨yp, ya⟩⟩
    cases h
    rfl

private theorem boundedPath3InfoSource_values_nodup (ψ : Nat) :
    (boundedPath3InfoSource ψ).values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · exact ExhaustiveList.values_nodup_fin ψ
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_fin 2
    · exact ExhaustiveList.values_nodup_fin 2

private theorem boundedPath3Info_values_nodup (ψ : Nat) :
    (boundedPath3Info ψ).values.Nodup := by
  unfold boundedPath3Info
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact boundedPath3InfoSource_values_nodup ψ
  · intro x y h
    rcases x with ⟨xl, xb, xf⟩
    rcases y with ⟨yl, yb, yf⟩
    cases h
    rfl

private theorem cleaningLabel_values_nodup (ψ : Nat) :
    (cleaningLabel ψ).values.Nodup := by
  unfold cleaningLabel
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact ExhaustiveList.values_nodup_option
      (ExhaustiveList.fin ψ) (ExhaustiveList.values_nodup_fin ψ)
  · intro x y h
    cases x <;> cases y <;> simp_all

private theorem boundedPath2Option_values_nodup (ψ : Nat) :
    (boundedPath2Option ψ).values.Nodup :=
  ExhaustiveList.values_nodup_option _ (boundedPath2Info_values_nodup ψ)

private theorem boundedPath3Option_values_nodup (ψ : Nat) :
    (boundedPath3Option ψ).values.Nodup :=
  ExhaustiveList.values_nodup_option _ (boundedPath3Info_values_nodup ψ)

private theorem boundedCleanPathOption_values_nodup (ψ : Nat) :
    (boundedCleanPathOption ψ).values.Nodup := by
  apply ExhaustiveList.values_nodup_option
  apply ExhaustiveList.values_nodup_prod
  · exact cleaningLabel_values_nodup ψ
  · exact ExhaustiveList.values_nodup_fin 2

/-! ## Balanced state-product certificate -/

private structure BlockA (ψ : Nat) where
  leader : Bool
  probe : Bool
  phase : Bool
  bit : Bool
  wait : Bool
  state : MainState
  path : BoundedPathInfo ψ
  reset : Bool

private structure BlockB (ψ κ : Nat) where
  carry : Bool
  count : Fin (κ + 1)
  label : Fin ψ
  h_field : Bool
  path2 : Option (BoundedPath2Info ψ)
  path3 : Option (BoundedPath3Info ψ)
  path4 : Option (CleaningLabel ψ × Fin 2)
  path5 : Option (CleaningLabel ψ × Fin 2)

private structure BlockC where
  p : Bool
  p_carry : Bool
  reset_cmd : Bool
  echo : Bool
  signal_B : Fin 2
  bullet : Fin 3
  shield : Bool
  write_state : WriteState

private structure BlockD where
  write : WriteAction
  last : Bool
  last_set : Bool
  last_unset : Bool
  b_carry : Bool
  gen_ws : Bool
  ws_echo : Bool
  signal_ws : Bool

private def blockASource (ψ : Nat) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool)
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool mainState)
      (ExhaustiveList.prod (boundedPathInfo ψ) ExhaustiveList.bool))

private def blockA (ψ : Nat) : ExhaustiveList (BlockA ψ) :=
  ExhaustiveList.mapSurjective (blockASource ψ)
    (fun x =>
      { leader := x.1.1.1, probe := x.1.1.2,
        phase := x.1.2.1, bit := x.1.2.2,
        wait := x.2.1.1, state := x.2.1.2,
        path := x.2.2.1, reset := x.2.2.2 })
    (by
      intro a
      exact ⟨(((a.leader, a.probe), (a.phase, a.bit)),
        ((a.wait, a.state), (a.path, a.reset))), by cases a; rfl⟩)

private theorem blockASource_values_nodup (ψ : Nat) :
    (blockASource ψ).values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_bool
      · exact mainState_values_nodup
    · apply ExhaustiveList.values_nodup_prod
      · exact boundedPathInfo_values_nodup ψ
      · exact ExhaustiveList.values_nodup_bool

private theorem blockA_values_nodup (ψ : Nat) :
    (blockA ψ).values.Nodup := by
  unfold blockA
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact blockASource_values_nodup ψ
  · intro x y h
    rcases x with ⟨⟨⟨xl, xp⟩, ⟨xph, xb⟩⟩,
      ⟨⟨xw, xs⟩, ⟨xpath, xr⟩⟩⟩
    rcases y with ⟨⟨⟨yl, yp⟩, ⟨yph, yb⟩⟩,
      ⟨⟨yw, ys⟩, ⟨ypath, yr⟩⟩⟩
    cases h
    rfl

private def blockBSource (ψ κ : Nat) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool (ExhaustiveList.fin (κ + 1)))
      (ExhaustiveList.prod (ExhaustiveList.fin ψ) ExhaustiveList.bool))
    (ExhaustiveList.prod
      (ExhaustiveList.prod (boundedPath2Option ψ) (boundedPath3Option ψ))
      (ExhaustiveList.prod (boundedCleanPathOption ψ)
        (boundedCleanPathOption ψ)))

private def blockB (ψ κ : Nat) : ExhaustiveList (BlockB ψ κ) :=
  ExhaustiveList.mapSurjective (blockBSource ψ κ)
    (fun x =>
      { carry := x.1.1.1, count := x.1.1.2,
        label := x.1.2.1, h_field := x.1.2.2,
        path2 := x.2.1.1, path3 := x.2.1.2,
        path4 := x.2.2.1, path5 := x.2.2.2 })
    (by
      intro b
      exact ⟨(((b.carry, b.count), (b.label, b.h_field)),
        ((b.path2, b.path3), (b.path4, b.path5))), by cases b; rfl⟩)

private theorem blockBSource_values_nodup (ψ κ : Nat) :
    (blockBSource ψ κ).values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_bool
      · exact ExhaustiveList.values_nodup_fin (κ + 1)
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_fin ψ
      · exact ExhaustiveList.values_nodup_bool
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · exact boundedPath2Option_values_nodup ψ
      · exact boundedPath3Option_values_nodup ψ
    · apply ExhaustiveList.values_nodup_prod <;>
        exact boundedCleanPathOption_values_nodup ψ

private theorem blockB_values_nodup (ψ κ : Nat) :
    (blockB ψ κ).values.Nodup := by
  unfold blockB
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact blockBSource_values_nodup ψ κ
  · intro x y h
    rcases x with ⟨⟨⟨xc, xn⟩, ⟨xl, xh⟩⟩,
      ⟨⟨xp2, xp3⟩, ⟨xp4, xp5⟩⟩⟩
    rcases y with ⟨⟨⟨yc, yn⟩, ⟨yl, yh⟩⟩,
      ⟨⟨yp2, yp3⟩, ⟨yp4, yp5⟩⟩⟩
    cases h
    rfl

private def blockCSource :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool)
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))
    (ExhaustiveList.prod
      (ExhaustiveList.prod (ExhaustiveList.fin 2) (ExhaustiveList.fin 3))
      (ExhaustiveList.prod ExhaustiveList.bool writeState))

private def blockC : ExhaustiveList BlockC :=
  ExhaustiveList.mapSurjective blockCSource
    (fun x =>
      { p := x.1.1.1, p_carry := x.1.1.2,
        reset_cmd := x.1.2.1, echo := x.1.2.2,
        signal_B := x.2.1.1, bullet := x.2.1.2,
        shield := x.2.2.1, write_state := x.2.2.2 })
    (by
      intro c
      exact ⟨(((c.p, c.p_carry), (c.reset_cmd, c.echo)),
        ((c.signal_B, c.bullet), (c.shield, c.write_state))), by cases c; rfl⟩)

private theorem blockCSource_values_nodup : blockCSource.values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_fin 2
      · exact ExhaustiveList.values_nodup_fin 3
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_bool
      · exact writeState_values_nodup

private theorem blockC_values_nodup : blockC.values.Nodup := by
  unfold blockC
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact blockCSource_values_nodup
  · intro x y h
    rcases x with ⟨⟨⟨xp, xpc⟩, ⟨xr, xe⟩⟩,
      ⟨⟨xsb, xb⟩, ⟨xsh, xws⟩⟩⟩
    rcases y with ⟨⟨⟨yp, ypc⟩, ⟨yr, ye⟩⟩,
      ⟨⟨ysb, yb⟩, ⟨ysh, yws⟩⟩⟩
    cases h
    rfl

private def blockDSource :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod writeAction ExhaustiveList.bool)
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool)
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))

private def blockD : ExhaustiveList BlockD :=
  ExhaustiveList.mapSurjective blockDSource
    (fun x =>
      { write := x.1.1.1, last := x.1.1.2,
        last_set := x.1.2.1, last_unset := x.1.2.2,
        b_carry := x.2.1.1, gen_ws := x.2.1.2,
        ws_echo := x.2.2.1, signal_ws := x.2.2.2 })
    (by
      intro d
      exact ⟨(((d.write, d.last), (d.last_set, d.last_unset)),
        ((d.b_carry, d.gen_ws), (d.ws_echo, d.signal_ws))), by cases d; rfl⟩)

private theorem blockDSource_values_nodup : blockDSource.values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · exact writeAction_values_nodup
      · exact ExhaustiveList.values_nodup_bool
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool
  · apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool
    · apply ExhaustiveList.values_nodup_prod <;>
        exact ExhaustiveList.values_nodup_bool

private theorem blockD_values_nodup : blockD.values.Nodup := by
  unfold blockD
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact blockDSource_values_nodup
  · intro x y h
    rcases x with ⟨⟨⟨xw, xl⟩, ⟨xls, xlu⟩⟩,
      ⟨⟨xbc, xg⟩, ⟨xwe, xsw⟩⟩⟩
    rcases y with ⟨⟨⟨yw, yl⟩, ⟨yls, ylu⟩⟩,
      ⟨⟨ybc, yg⟩, ⟨ywe, ysw⟩⟩⟩
    cases h
    rfl

private def stateSource (ψ κ : Nat) :=
  ExhaustiveList.prod (ExhaustiveList.prod (blockA ψ) (blockB ψ κ))
    (ExhaustiveList.prod blockC blockD)

private theorem stateSource_values_nodup (ψ κ : Nat) :
    (stateSource ψ κ).values.Nodup := by
  unfold stateSource
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · exact blockA_values_nodup ψ
    · exact blockB_values_nodup ψ κ
  · apply ExhaustiveList.values_nodup_prod
    · exact blockC_values_nodup
    · exact blockD_values_nodup

private def assembleState {ψ κ : Nat}
    (x : (BlockA ψ × BlockB ψ κ) × (BlockC × BlockD)) :
    BoundedAgentState ψ κ :=
  { leader := x.1.1.leader
    probe := x.1.1.probe
    phase := x.1.1.phase
    bit := x.1.1.bit
    wait := x.1.1.wait
    state := x.1.1.state
    path := x.1.1.path
    reset := x.1.1.reset
    carry := x.1.2.carry
    count := x.1.2.count
    label := x.1.2.label
    h_field := x.1.2.h_field
    path2 := x.1.2.path2
    path3 := x.1.2.path3
    path4 := x.1.2.path4
    path5 := x.1.2.path5
    p := x.2.1.p
    p_carry := x.2.1.p_carry
    reset_cmd := x.2.1.reset_cmd
    echo := x.2.1.echo
    signal_B := x.2.1.signal_B
    bullet := x.2.1.bullet
    shield := x.2.1.shield
    write_state := x.2.1.write_state
    write := x.2.2.write
    last := x.2.2.last
    last_set := x.2.2.last_set
    last_unset := x.2.2.last_unset
    b_carry := x.2.2.b_carry
    gen_ws := x.2.2.gen_ws
    ws_echo := x.2.2.ws_echo
    signal_ws := x.2.2.signal_ws }

private def disassembleState {ψ κ : Nat}
    (s : BoundedAgentState ψ κ) :
    (BlockA ψ × BlockB ψ κ) × (BlockC × BlockD) :=
  (({
    leader := s.leader, probe := s.probe, phase := s.phase,
    bit := s.bit, wait := s.wait, state := s.state,
    path := s.path, reset := s.reset }, {
    carry := s.carry, count := s.count, label := s.label,
    h_field := s.h_field, path2 := s.path2, path3 := s.path3,
    path4 := s.path4, path5 := s.path5 }), ({
    p := s.p, p_carry := s.p_carry, reset_cmd := s.reset_cmd,
    echo := s.echo, signal_B := s.signal_B, bullet := s.bullet,
    shield := s.shield, write_state := s.write_state }, {
    write := s.write, last := s.last, last_set := s.last_set,
    last_unset := s.last_unset, b_carry := s.b_carry,
    gen_ws := s.gen_ws, ws_echo := s.ws_echo,
    signal_ws := s.signal_ws }))

private theorem disassemble_assembleState {ψ κ : Nat} :
    Function.LeftInverse (@disassembleState ψ κ) (@assembleState ψ κ) := by
  intro x
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  cases a
  cases b
  cases c
  cases d
  rfl

private theorem assembleState_injective {ψ κ : Nat} :
    Function.Injective (@assembleState ψ κ) :=
  disassemble_assembleState.injective

/-- Exhaustive finite-state witness for the actual bounded local carrier. -/
def boundedAgentState (ψ κ : Nat) :
    ExhaustiveList (BoundedAgentState ψ κ) :=
  ExhaustiveList.mapSurjective (stateSource ψ κ) assembleState
    (by
      intro s
      refine ⟨(({
        leader := s.leader, probe := s.probe, phase := s.phase,
        bit := s.bit, wait := s.wait, state := s.state,
        path := s.path, reset := s.reset }, {
        carry := s.carry, count := s.count, label := s.label,
        h_field := s.h_field, path2 := s.path2, path3 := s.path3,
        path4 := s.path4, path5 := s.path5 }), ({
        p := s.p, p_carry := s.p_carry, reset_cmd := s.reset_cmd,
        echo := s.echo, signal_B := s.signal_B, bullet := s.bullet,
        shield := s.shield, write_state := s.write_state }, {
        write := s.write, last := s.last, last_set := s.last_set,
        last_unset := s.last_unset, b_carry := s.b_carry,
        gen_ws := s.gen_ws, ws_echo := s.ws_echo,
        signal_ws := s.signal_ws })), ?_⟩
      cases s
      rfl)

/-- The bounded-state certificate has no duplicate semantic state. -/
theorem boundedAgentState_values_nodup (ψ κ : Nat) :
    (boundedAgentState ψ κ).values.Nodup := by
  unfold boundedAgentState
  apply ExhaustiveList.values_nodup_mapSurjective
  · exact stateSource_values_nodup ψ κ
  · exact assembleState_injective

/-- Every bounded local state occurs in the explicit finite list. -/
theorem mem_boundedAgentState {ψ κ : Nat} (s : BoundedAgentState ψ κ) :
    s ∈ (boundedAgentState ψ κ).values :=
  (boundedAgentState ψ κ).complete s

/-- Strong finite-state certificate: a finite index type surjects onto every
bounded local state. -/
theorem boundedAgentState_decode_surjective (ψ κ : Nat) :
    Function.Surjective (boundedAgentState ψ κ).decode :=
  (boundedAgentState ψ κ).decode_surjective

/-- Duplicate-freedom makes the bounded-state decoder injective. -/
theorem boundedAgentState_decode_injective (ψ κ : Nat) :
    Function.Injective (boundedAgentState ψ κ).decode :=
  ExhaustiveList.decode_injective_of_values_nodup _
    (boundedAgentState_values_nodup ψ κ)

/-- Exact finite-index representation of every bounded local state. -/
theorem boundedAgentState_decode_bijective (ψ κ : Nat) :
    Function.Injective (boundedAgentState ψ κ).decode ∧
      Function.Surjective (boundedAgentState ψ κ).decode :=
  ⟨boundedAgentState_decode_injective ψ κ,
    boundedAgentState_decode_surjective ψ κ⟩

end PPLLFinite
