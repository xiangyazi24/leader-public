import Leader.Wu.Entrance.LocalReverseFill

set_option autoImplicit false
set_option Elab.async false

/-!
# Closed reverse-fill witness at the n=104 seed-44 checkpoint

The 15 cells below are the exact physical `SNAP_CELL` records for ring
positions 48--62 at t=21535.  The observer/provenance records are deliberately
not represented: every transition below is the actual physical R1 row.

The checkpoint file prints bounded `path2.action := 3` at cell 59.  The bounded
encoding stores source action `a` as `a-1`, so the corresponding raw
`AgentState` used with `BoundedAgentState.ofDomain` has action 4.
-/

namespace B6ReverseFillWitness

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
  BirthCheckChainR1PerBlock

abbrev Cell := ExpiringAgentState 4 4 64
abbrev LocalCfg := Fin 15 → Cell
abbrev RingCfg := BirthCheckPermitRepairLeaf.FC 104 4 4 64

/-- Common-field constructor for the 15 closed checkpoint cells. -/
private def rawCell
    (lab : Fin 4) (residentBit wait : Bool) (state : MainState)
    (path : PathInfo) (reset : Bool) (count : Nat) (hField : Bool)
    (path2 : Option Path2Info)
    (path4 path5 : Option (Int × Nat))
    (p : Bool) (writeState : WriteState) : AgentState 4 where
  leader := false
  probe := false
  phase := false
  bit := residentBit
  wait := wait
  state := state
  path := path
  reset := reset
  carry := false
  count := count
  label := lab
  h_field := hField
  path2 := path2
  path3 := none
  path4 := path4
  path5 := path5
  p := p
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := writeState
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

private def pack (u : AgentState 4) (hu : u.inProtocolDomain 4)
    (stall : Fin 65) : Cell :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, stall⟩

/-- Ring cell 48. -/
def c48 : Cell :=
  pack
    (rawCell 0 false false .none .bot true 0 false
      none none none false .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 57

/-- Ring cell 49. -/
def c49 : Cell :=
  pack
    (rawCell 1 true true .none .bot false 4 true
      none none none false .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 64

/-- Ring cell 50. -/
def c50 : Cell :=
  pack
    (rawCell 2 true true .none .bot false 0 false
      none none none false .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 64

/-- Ring cell 51. -/
def c51 : Cell :=
  pack
    (rawCell 3 false true .none (.some 0 0) false 0 false
      none none (some (0, 0)) false .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 64

/-- Ring cell 52. -/
def c52 : Cell :=
  pack
    (rawCell 0 false false .none .bot false 0 true
      none (some (1, 0)) none false .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 62

/-- Ring cell 53. -/
def c53 : Cell :=
  pack
    (rawCell 1 false true .CHECK_ready (.some 1 1) false 4 false
      none (some (1, 1)) none false .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 61

/-- Ring cell 54. -/
def c54 : Cell :=
  pack
    (rawCell 2 false true .none .bot false 0 false
      none none (some (1, 1)) true .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 62

/-- Ring cell 55. -/
def c55 : Cell :=
  pack
    (rawCell 3 true true .none .bot false 0 false
      none (some (2, 1)) none false .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 61

/-- Ring cell 56. -/
def c56 : Cell :=
  pack
    (rawCell 0 false false .none (.some 2 1) true 0 false
      none none (some (2, 1)) false .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 61

/-- Ring cell 57. -/
def c57 : Cell :=
  pack
    (rawCell 1 true true .none .bot false 4 false
      none (some (3, 1)) none true .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 64

/-- Ring cell 58. -/
def c58 : Cell :=
  pack
    (rawCell 2 true true .none (.some 3 1) false 0 false
      none none none false .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 64

/-- Ring cell 59.  Raw action 4 reifies to printed bounded action 3. -/
def c59 : Cell :=
  pack
    (rawCell 3 true true .eliminate_signal .bot false 0 false
      (some { label := 0, bit := 0, position := 0, action := 4 })
      none (some (0, 0)) false .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 44

/-- Ring cell 60. -/
def c60 : Cell :=
  pack
    (rawCell 0 false false .none .bot false 0 true
      none none none false .none)
    (by simp [rawCell, AgentState.inProtocolDomain]) 63

/-- Ring cell 61. -/
def c61 : Cell :=
  pack
    (rawCell 1 false true .none (.some 0 0) false 4 false
      none none (some (0, 1)) false .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 62

/-- Ring cell 62. -/
def c62 : Cell :=
  pack
    (rawCell 2 true true .eliminate_signal (.some 1 0) false 0 false
      none none (some (1, 1)) true .depart)
    (by simp [rawCell, AgentState.inProtocolDomain]) 64

/-- Local index `i` denotes physical ring cell `48+i`. -/
def checkpoint (i : Fin 15) : Cell :=
  match i.val with
  | 0 => c48
  | 1 => c49
  | 2 => c50
  | 3 => c51
  | 4 => c52
  | 5 => c53
  | 6 => c54
  | 7 => c55
  | 8 => c56
  | 9 => c57
  | 10 => c58
  | 11 => c59
  | 12 => c60
  | 13 => c61
  | _ => c62
/-! ## Local 15-cell execution and closed parking certificates -/

/-- Exact width-two R1 physical row used by both the probe and `step1`. -/
def r1Row (l r : Cell) : Cell × Cell :=
  BirthCheckPermitRepair.row
    (ψ := 4) (width := 2) (κ := 4) (τ := 64)
    (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 2 ≤ 4) l r

private def localRight (e : Fin 15) (h : e.val + 1 < 15) : Fin 15 :=
  ⟨e.val + 1, h⟩

/-- One internal local request.  Edge 14 is deliberately a stutter; it is not
used by the certified word. -/
def localStep (C : LocalCfg) (e : Fin 15) : LocalCfg :=
  if h : e.val + 1 < 15 then
    let r := localRight e h
    let q := r1Row (C e) (C r)
    fun i =>
      if i = e then q.1
      else if i = r then q.2
      else C i
  else C

/-- The requested local interpreter. -/
def localRun (w : List (Fin 15)) (C : LocalCfg) : LocalCfg :=
  w.foldl localStep C

private theorem localRight_ne (e : Fin 15) (h : e.val + 1 < 15) :
    localRight e h ≠ e := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [localRight] at hv
  omega

theorem localStep_left (C : LocalCfg) (e : Fin 15)
    (h : e.val + 1 < 15) :
    localStep C e e = (r1Row (C e) (C (localRight e h))).1 := by
  simp [localStep, h, localRight]

theorem localStep_right (C : LocalCfg) (e : Fin 15)
    (h : e.val + 1 < 15) :
    localStep C e (localRight e h) =
      (r1Row (C e) (C (localRight e h))).2 := by
  have hne := localRight_ne e h
  simp only [localStep, dif_pos h]
  rw [if_neg hne]
  simp

theorem localStep_other (C : LocalCfg) (e i : Fin 15)
    (hie : i ≠ e) (hir : i.val ≠ e.val + 1) :
    localStep C e i = C i := by
  by_cases h : e.val + 1 < 15
  · have hne : i ≠ localRight e h := by
      intro hi
      apply hir
      have hv := congrArg Fin.val hi
      simpa [localRight] using hv
    simp [localStep, h, hie, hne]
  · simp [localStep, h]

/-- No request in `w` serves `i` as either endpoint. -/
abbrev MissesLocal (i : Fin 15) (w : List (Fin 15)) : Prop :=
  ∀ e ∈ w, i ≠ e ∧ i.val ≠ e.val + 1

theorem localRun_cell_eq_of_misses (w : List (Fin 15))
    (C : LocalCfg) (i : Fin 15) (h : MissesLocal i w) :
    localRun w C i = C i := by
  induction w generalizing C with
  | nil => rfl
  | cons e w ih =>
      have he := h e List.mem_cons_self
      have hw : MissesLocal i w := by
        intro f hf
        exact h f (List.mem_cons_of_mem e hf)
      change localRun w (localStep C e) i = C i
      rw [ih (C := localStep C e) hw]
      exact localStep_other C e i he.1 he.2

/-- A tiny prefix relation used only for the parking-persistence statements. -/
def PrefixOf {α : Type} (p w : List α) : Prop :=
  ∃ t, w = p ++ t

private theorem misses_of_prefix (i : Fin 15) {p w : List (Fin 15)}
    (h : MissesLocal i w) (hp : PrefixOf p w) : MissesLocal i p := by
  rcases hp with ⟨t, rfl⟩
  intro e he
  exact h e (by simp [he])

/-- A decidable, forall-free package of exactly the fields needed to build the
actual `BirthCheckChainR1Ring.ReadyCell` proposition. -/
def CleanOK : Option (Int × Nat) → Prop
  | none => True
  | some p => p.1 ≠ (-1 : Int)

instance cleanOKDecidable (x : Option (Int × Nat)) : Decidable (CleanOK x) := by
  cases x <;> unfold CleanOK <;> infer_instance

abbrev ReadyClosed (k : Nat) (c : Cell) : Prop :=
  let u := c.core.erase.core
  u.label.val = k ∧
  u.leader = false ∧
  u.path = .some k (if u.bit then 1 else 0) ∧
  u.path2 = none ∧
  u.state ≠ .depart ∧
  u.state ≠ .equal ∧
  u.state ≠ .larger ∧
  u.state ≠ .less ∧
  u.state ≠ .produce ∧
  u.state ≠ .done ∧
  u.state ≠ .toss ∧
  u.state ≠ .congest ∧
  u.state ≠ .eliminate_signal ∧
  u.reset_cmd = false ∧
  (k = 0 → CleanOK u.path4) ∧
  CleanOK u.path5 ∧
  c.stall.val ≠ 0

private theorem cleanOK_spec (x : Option (Int × Nat)) (h : CleanOK x) :
    ∀ p, x = some p → p.1 ≠ (-1 : Int) := by
  cases x with
  | none =>
      intro p hp
      cases hp
  | some q =>
      change q.1 ≠ (-1 : Int) at h
      intro p hp
      cases hp
      exact h

private theorem readyCell_of_closed {k : Nat} {c : Cell}
    (h : ReadyClosed k c) : ReadyCell k c := by
  unfold ReadyClosed at h
  dsimp only at h
  rcases h with
    ⟨hlab, hleader, hpath, hp2, hdepart, hequal, hlarger, hless,
      hproduce, hdone, htoss, hcongest, helim, hreset,
      hp4, hp5, hstall⟩
  have hopen : BirthCheckChainR1.CheckOpenMatch c.core.erase.core := by
    refine
      { path := ?_
        path2 := hp2
        notDepart := hdepart
        notEqual := hequal
        notLarger := hlarger
        notLess := hless }
    rw [hlab]
    exact hpath
  have h4 : k = 0 →
      ∀ p, c.core.erase.core.path4 = some p → p.1 ≠ (-1 : Int) := by
    intro hk p hp
    exact cleanOK_spec _ (hp4 hk) p hp
  have h5 : ∀ p, c.core.erase.core.path5 = some p → p.1 ≠ (-1 : Int) := by
    intro p hp
    exact cleanOK_spec _ hp5 p hp
  exact
    { label := hlab
      leader := hleader
      openMatch := hopen
      notProduce := hproduce
      notDone := hdone
      notToss := htoss
      notCongest := hcongest
      notEliminate := helim
      reset := hreset
      path4 := h4
      path5 := h5
      stall := hstall }

/-- The exact local request word from the replay, translated by subtracting 48. -/
def localWord : List (Fin 15) :=
  [3, 8, 10, 4, 5, 9, 6, 7, 4, 8, 5, 6, 7]

/-- Named executable states make the four parking cuts independently reducible. -/
def S0 : LocalCfg := checkpoint
def S1 : LocalCfg := localStep S0 3
def S2 : LocalCfg := localStep S1 8
def S3 : LocalCfg := localStep S2 10
def S4 : LocalCfg := localStep S3 4
def S5 : LocalCfg := localStep S4 5
def S6 : LocalCfg := localStep S5 9
def S7 : LocalCfg := localStep S6 6
def S8 : LocalCfg := localStep S7 7
def S9 : LocalCfg := localStep S8 4
def S10 : LocalCfg := localStep S9 8
def S11 : LocalCfg := localStep S10 5
def S12 : LocalCfg := localStep S11 6
def S13 : LocalCfg := localStep S12 7

theorem localRun_word : localRun localWord S0 = S13 := by
  rfl

/-- Exact net arrivals at the four parking interactions. -/
def pathOf (c : Cell) : PathInfo := c.core.erase.core.path

theorem park3_transfer :
    pathOf (S2 11) = .bot ∧
    pathOf (S2 10) = .some 3 1 ∧
    pathOf (S3 10) = .bot ∧
    pathOf (S3 11) = .some 3 1 := by
  decide +kernel

theorem park2_transfer :
    pathOf (S5 10) = .bot ∧
    pathOf (S5 9) = .some 2 1 ∧
    pathOf (S6 9) = .bot ∧
    pathOf (S6 10) = .some 2 1 := by
  decide +kernel

theorem park1_transfer :
    pathOf (S9 9) = .bot ∧
    pathOf (S9 8) = .some 1 1 ∧
    pathOf (S10 8) = .bot ∧
    pathOf (S10 9) = .some 1 1 := by
  decide +kernel

theorem park0_transfer :
    pathOf (S12 8) = .bot ∧
    pathOf (S12 7) = .some 0 0 ∧
    pathOf (S13 7) = .bot ∧
    pathOf (S13 8) = .some 0 0 := by
  decide +kernel

/-- These four computations prove the actual Prop, not the probe Boolean. -/
private theorem ready3_facts : ReadyClosed 3 (S3 11) := by
  decide +kernel

private theorem ready2_facts : ReadyClosed 2 (S6 10) := by
  decide +kernel

private theorem ready1_facts : ReadyClosed 1 (S10 9) := by
  decide +kernel

private theorem ready0_facts : ReadyClosed 0 (S13 8) := by
  decide +kernel

theorem ready3_at_step3 : ReadyCell 3 (S3 11) :=
  readyCell_of_closed ready3_facts

theorem ready2_at_step6 : ReadyCell 2 (S6 10) :=
  readyCell_of_closed ready2_facts

theorem ready1_at_step10 : ReadyCell 1 (S10 9) :=
  readyCell_of_closed ready1_facts

theorem ready0_at_step13 : ReadyCell 0 (S13 8) :=
  readyCell_of_closed ready0_facts

/-- The exact remaining words after each reverse-order parking event. -/
def tail3 : List (Fin 15) := [4, 5, 9, 6, 7, 4, 8, 5, 6, 7]
def tail6 : List (Fin 15) := [6, 7, 4, 8, 5, 6, 7]
def tail10 : List (Fin 15) := [5, 6, 7]
def tail13 : List (Fin 15) := []

theorem localRun_tail3 : localRun tail3 S3 = S13 := by rfl
theorem localRun_tail6 : localRun tail6 S6 = S13 := by rfl
theorem localRun_tail10 : localRun tail10 S10 = S13 := by rfl
theorem localRun_tail13 : localRun tail13 S13 = S13 := by rfl

private theorem tail3_misses : MissesLocal 11 tail3 := by
  decide +kernel

private theorem tail6_misses : MissesLocal 10 tail6 := by
  decide +kernel

private theorem tail10_misses : MissesLocal 9 tail10 := by
  decide +kernel

private theorem tail13_misses : MissesLocal 8 tail13 := by
  decide +kernel

theorem parking_no_post_touch :
    MissesLocal 11 tail3 ∧
    MissesLocal 10 tail6 ∧
    MissesLocal 9 tail10 ∧
    MissesLocal 8 tail13 :=
  ⟨tail3_misses, tail6_misses, tail10_misses, tail13_misses⟩

theorem ready_persists_of_misses {k : Nat}
    (C : LocalCfg) (i : Fin 15) (w : List (Fin 15))
    (hReady : ReadyCell k (C i)) (hMiss : MissesLocal i w) :
    ∀ p, PrefixOf p w → ReadyCell k (localRun p C i) := by
  intro p hp
  have hm := misses_of_prefix i hMiss hp
  have heq := localRun_cell_eq_of_misses p C i hm
  rw [heq]
  exact hReady

theorem ready3_from_step3 :
    ∀ p, PrefixOf p tail3 → ReadyCell 3 (localRun p S3 11) :=
  ready_persists_of_misses S3 11 tail3 ready3_at_step3 tail3_misses

theorem ready2_from_step6 :
    ∀ p, PrefixOf p tail6 → ReadyCell 2 (localRun p S6 10) :=
  ready_persists_of_misses S6 10 tail6 ready2_at_step6 tail6_misses

theorem ready1_from_step10 :
    ∀ p, PrefixOf p tail10 → ReadyCell 1 (localRun p S10 9) :=
  ready_persists_of_misses S10 9 tail10 ready1_at_step10 tail10_misses

theorem ready0_from_step13 :
    ∀ p, PrefixOf p tail13 → ReadyCell 0 (localRun p S13 8) :=
  ready_persists_of_misses S13 8 tail13 ready0_at_step13 tail13_misses

theorem ready3_final : ReadyCell 3 (S13 11) := by
  rw [← localRun_tail3]
  exact ready3_from_step3 tail3 ⟨[], by simp⟩

theorem ready2_final : ReadyCell 2 (S13 10) := by
  rw [← localRun_tail6]
  exact ready2_from_step6 tail6 ⟨[], by simp⟩

theorem ready1_final : ReadyCell 1 (S13 9) := by
  rw [← localRun_tail10]
  exact ready1_from_step10 tail10 ⟨[], by simp⟩

theorem final_ready_cells :
    ReadyCell 0 (S13 8) ∧
    ReadyCell 1 (S13 9) ∧
    ReadyCell 2 (S13 10) ∧
    ReadyCell 3 (S13 11) :=
  ⟨ready0_at_step13, ready1_final, ready2_final, ready3_final⟩

/-- Closed local reverse-fill/parking statement, including the no-touch suffixes. -/
theorem local_reverse_fill_parking :
    ReadyCell 3 (S3 11) ∧
    ReadyCell 2 (S6 10) ∧
    ReadyCell 1 (S10 9) ∧
    ReadyCell 0 (S13 8) ∧
    MissesLocal 11 tail3 ∧
    MissesLocal 10 tail6 ∧
    MissesLocal 9 tail10 ∧
    MissesLocal 8 tail13 :=
  ⟨ready3_at_step3, ready2_at_step6, ready1_at_step10,
    ready0_at_step13, tail3_misses, tail6_misses,
    tail10_misses, tail13_misses⟩
/-! ## Ring/local agreement and the actual `LocalReverseFill` certificate -/

def ring104 : DirectedRing 104 := ⟨by decide⟩

def embed (i : Fin 15) : Fin 104 :=
  ⟨48 + i.val, by omega⟩

private theorem embed_injective : Function.Injective embed := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [embed] at hv
  omega

theorem embed_right (e : Fin 15) (h : e.val + 1 < 15) :
    ring104.rightNeighbor (embed e) = embed (localRight e h) := by
  apply Fin.ext
  change (48 + e.val + 1) % 104 = 48 + (e.val + 1)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The literal initiator list from the kept finite replay. -/
def ringWord : List (Fin 104) :=
  [51, 56, 58, 52, 53, 57, 54, 55, 52, 56, 53, 54, 55]

def ringStep (C : RingCfg) (e : Fin 104) : RingCfg :=
  BirthCheckPermitRepairLeaf.step1
    (by decide : 0 < 4) (by decide : 2 ≤ 4) ring104 C e

/-- Agreement between a full ring and the 15-cell checkpoint window. -/
def Agrees (G : RingCfg) (L : LocalCfg) : Prop :=
  ∀ i : Fin 15, G (embed i) = L i

def AgreesCheckpoint (G : RingCfg) : Prop := Agrees G S0

/-- One internal local request is exactly the restriction of one ring `step1`
request.  This proof uses the exported `step1_left`, `step1_right`, and
`step1_other`; it does not unfold the R1 protocol. -/
theorem ring_local_step_agree
    (G : RingCfg) (L : LocalCfg) (e : Fin 15)
    (he : e.val + 1 < 15) (hA : Agrees G L) :
    Agrees (ringStep G (embed e)) (localStep L e) := by
  intro i
  let r : Fin 15 := localRight e he
  have her : ring104.rightNeighbor (embed e) = embed r := by
    simpa [r] using embed_right e he
  have hne : ring104.rightNeighbor (embed e) ≠ embed e := by
    rw [her]
    intro h
    exact localRight_ne e he (embed_injective h)
  by_cases hie : i = e
  · subst i
    have hleft := BirthCheckChainR1Ring.step1_left
      (by decide : 0 < 4) (by decide : 2 ≤ 4) ring104 G (embed e)
    rw [her] at hleft
    change
      BirthCheckPermitRepairLeaf.step1
          (by decide : 0 < 4) (by decide : 2 ≤ 4)
          ring104 G (embed e) (embed e) = localStep L e e
    calc
      _ = (r1Row (G (embed e)) (G (embed r))).1 := by
        simpa [r1Row] using hleft
      _ = (r1Row (L e) (L r)).1 := by rw [hA e, hA r]
      _ = localStep L e e := (localStep_left L e he).symm
  · by_cases hir : i = r
    · subst i
      have hright := BirthCheckChainR1Ring.step1_right
        (by decide : 0 < 4) (by decide : 2 ≤ 4)
        ring104 G (embed e) hne
      rw [her] at hright
      change
        BirthCheckPermitRepairLeaf.step1
            (by decide : 0 < 4) (by decide : 2 ≤ 4)
            ring104 G (embed e) (embed r) = localStep L e r
      calc
        _ = (r1Row (G (embed e)) (G (embed r))).2 := by
          simpa [r1Row] using hright
        _ = (r1Row (L e) (L r)).2 := by rw [hA e, hA r]
        _ = localStep L e r := (localStep_right L e he).symm
    · have hge : embed i ≠ embed e := by
        intro h
        exact hie (embed_injective h)
      have hgr : embed i ≠ ring104.rightNeighbor (embed e) := by
        rw [her]
        intro h
        exact hir (embed_injective h)
      have hlocalR : i.val ≠ e.val + 1 := by
        intro h
        apply hir
        apply Fin.ext
        simpa [r, localRight] using h
      change
        BirthCheckPermitRepairLeaf.step1
            (by decide : 0 < 4) (by decide : 2 ≤ 4)
            ring104 G (embed e) (embed i) = localStep L e i
      calc
        _ = G (embed i) :=
          BirthCheckPermitRepairLeaf.step1_other
            (by decide : 0 < 4) (by decide : 2 ≤ 4)
            ring104 G (embed e) (embed i) hge hgr
        _ = L i := hA i
        _ = localStep L e i :=
          (localStep_other L e i hie hlocalR).symm

/-- All local letters are genuinely internal, so the one-step agreement
iterates over a word. -/
abbrev InternalLocal (w : List (Fin 15)) : Prop :=
  ∀ e ∈ w, e.val + 1 < 15

theorem ring_local_run_agree (w : List (Fin 15))
    (G : RingCfg) (L : LocalCfg)
    (hw : InternalLocal w) (hA : Agrees G L) :
    Agrees ((w.map embed).foldl ringStep G) (localRun w L) := by
  induction w generalizing G L with
  | nil => exact hA
  | cons e w ih =>
      have he := hw e List.mem_cons_self
      have hrest : InternalLocal w := by
        intro f hf
        exact hw f (List.mem_cons_of_mem e hf)
      change
        Agrees ((w.map embed).foldl ringStep (ringStep G (embed e)))
          (localRun w (localStep L e))
      exact ih _ _ hrest (ring_local_step_agree G L e he hA)

private theorem localWord_internal : InternalLocal localWord := by
  decide +kernel

theorem map_localWord_eq_ringWord : localWord.map embed = ringWord := by
  decide +kernel

theorem final_agrees (G : RingCfg) (hG : AgreesCheckpoint G) :
    Agrees (ringWord.foldl ringStep G) S13 := by
  have h0 : Agrees G S0 := by simpa [AgreesCheckpoint] using hG
  have h := ring_local_run_agree localWord G S0 localWord_internal h0
  rw [map_localWord_eq_ringWord, localRun_word] at h
  exact h

def start56 : Fin 104 := ⟨56, by decide⟩

theorem target0 : cell ring104 start56 0 = embed 8 := by decide +kernel
theorem target1 : cell ring104 start56 1 = embed 9 := by decide +kernel
theorem target2 : cell ring104 start56 2 = embed 10 := by decide +kernel
theorem target3 : cell ring104 start56 3 = embed 11 := by decide +kernel

/-- Stronger than the existential ReadyWindow conclusion: the witness start is
literally ring cell 56. -/
theorem ring_ready_at_56 (G : RingCfg) (hG : AgreesCheckpoint G) :
    ∀ k, k < 4 →
      ReadyCell k ((ringWord.foldl ringStep G) (cell ring104 start56 k)) := by
  intro k hk
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hA := final_agrees G hG
  rcases hcases with h0 | h1 | h2 | h3
  · subst k
    rw [target0, hA 8]
    exact ready0_at_step13
  · subst k
    rw [target1, hA 9]
    exact ready1_final
  · subst k
    rw [target2, hA 10]
    exact ready2_final
  · subst k
    rw [target3, hA 11]
    exact ready3_final

/-- The requested ring-level conclusion for any outside completion agreeing
with the checkpoint on cells 48--62. -/
theorem ring_reverse_fill_readyWindow
    (G : RingCfg) (hG : AgreesCheckpoint G) :
    ReadyWindow ring104 (ringWord.foldl ringStep G) :=
  ⟨start56, ring_ready_at_56 G hG⟩

/-! The accepted p185lr abstraction from `B6LocalReverseFill.lean` can now be
instantiated by the same finite witness. -/

def interval15 : B6LocalReverseFill.Interval ring104 where
  first := ⟨48, by decide⟩
  size := 15
  nonempty := by decide
  fits := by decide

private theorem ringWord_internal_interval :
    B6LocalReverseFill.InternalWord interval15 ringWord := by
  unfold B6LocalReverseFill.InternalWord B6LocalReverseFill.internal
  decide +kernel

private theorem contains56 :
    B6LocalReverseFill.ContainsTarget ring104 interval15 start56 4 := by
  unfold B6LocalReverseFill.ContainsTarget
  decide +kernel

theorem final_hit_inside (G : RingCfg) (hG : AgreesCheckpoint G) :
    B6LocalReverseFill.HitInside ring104 interval15
      (ringWord.foldl ringStep G) := by
  right
  refine ⟨start56, contains56, ?_⟩
  intro k
  exact ring_ready_at_56 G hG k.val k.isLt

/-- Closed instantiation of the campaign's actual local reverse-fill contract:
all requests are internal to the 15-cell interval and the full requested word
itself is a successful prefix. -/
theorem local_reverse_fill_certificate
    (G : RingCfg) (hG : AgreesCheckpoint G) :
    B6LocalReverseFill.LocalReverseFill
      (by decide : 0 < 4) (by decide : 2 ≤ 4)
      ring104 interval15 ringWord G := by
  refine ⟨ringWord_internal_interval, ?_⟩
  refine ⟨ringWord, ?_, ?_⟩
  · exact ⟨[], by simp⟩
  · unfold B6LocalReverseFill.runR
    exact final_hit_inside G hG

end B6ReverseFillWitness
