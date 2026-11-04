import Leader.Wu.Protocol.FiniteState

set_option autoImplicit false

namespace PPLLStateBoundCarrier

/-!
# Plain-list state-count certificate

This file deliberately avoids `ExhaustiveList.mapSurjective` in every length
calculation.  The counting lists are assembled directly from finite per-field
lists and a recursive Cartesian product.  Consequently there are no proof-term
arguments in the expressions seen by the length lemmas.
-/

private def enumProd {α β : Type} (xs : List α) (ys : List β) :
    List (α × β) :=
  match xs with
  | [] => []
  | x :: xs => ys.map (fun y => (x, y)) ++ enumProd xs ys

@[simp] private theorem enumProd_length {α β : Type}
    (xs : List α) (ys : List β) :
    (enumProd xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [enumProd]
  | cons x xs ih =>
      simp [enumProd, ih, Nat.succ_mul, Nat.add_comm]

private theorem mem_enumProd_of_mem {α β : Type}
    {xs : List α} {ys : List β} {x : α} {y : β}
    (hx : x ∈ xs) (hy : y ∈ ys) : (x, y) ∈ enumProd xs ys := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_append_left _ (List.mem_map_of_mem hy)
      · exact List.mem_append_right _ (ih hx)

private def finList (n : Nat) : List (Fin n) :=
  List.ofFn (fun i : Fin n => i)

@[simp] private theorem finList_length (n : Nat) :
    (finList n).length = n := by
  simp [finList]

private theorem finList_complete {n : Nat} (x : Fin n) : x ∈ finList n := by
  simp [finList]

private def boolList : List Bool := [false, true]

@[simp] private theorem boolList_length : boolList.length = 2 := rfl

private theorem boolList_complete (x : Bool) : x ∈ boolList := by
  cases x <;> simp [boolList]

private def optionList {α : Type} (xs : List α) : List (Option α) :=
  none :: xs.map some

@[simp] private theorem optionList_length {α : Type} (xs : List α) :
    (optionList xs).length = xs.length + 1 := by
  simp [optionList, Nat.add_comm]

private theorem optionList_complete {α : Type} {xs : List α}
    (hxs : ∀ x : α, x ∈ xs) (x : Option α) : x ∈ optionList xs := by
  cases x with
  | none => exact List.mem_cons_self
  | some x => exact List.mem_cons_of_mem _ (List.mem_map_of_mem (hxs x))

private def mainStateList : List MainState :=
  [.produce, .done, .depart, .none, .congest, .lock,
   .compare1, .compare2, .eliminate_signal, .CHECK_ready,
   .equal, .larger, .less, .toss, .toss_done]

@[simp] private theorem mainStateList_length : mainStateList.length = 15 := rfl

private theorem mainStateList_complete (x : MainState) : x ∈ mainStateList := by
  cases x <;> simp [mainStateList]

private def writeStateList : List WriteState :=
  [.depart, .ready, .increment_WS, .increment_WS_done,
   .done, .equal, .larger, .less, .produce, .overwrite,
   .move_flip, .move, .increment_group, .none]

@[simp] private theorem writeStateList_length : writeStateList.length = 14 := rfl

private theorem writeStateList_complete (x : WriteState) : x ∈ writeStateList := by
  cases x <;> simp [writeStateList]

private def writeActionList : List WriteAction :=
  [.overwrite, .move_flip, .move, .increment_group, .none]

@[simp] private theorem writeActionList_length : writeActionList.length = 5 := rfl

private theorem writeActionList_complete (x : WriteAction) : x ∈ writeActionList := by
  cases x <;> simp [writeActionList]

/-! ## Parameterized field lists -/

private def pathList (psi : Nat) : List (BoundedPathInfo psi) :=
  .bot ::
    (enumProd (finList psi) (finList 2)).map
      (fun x => BoundedPathInfo.some x.1 x.2)

@[simp] private theorem pathList_length (psi : Nat) :
    (pathList psi).length = 2 * psi + 1 := by
  simp [pathList]
  omega

private def path2List (psi : Nat) : List (BoundedPath2Info psi) :=
  (enumProd
      (enumProd (finList psi) (finList 2))
      (enumProd (finList (psi + 1)) (finList 6))).map
    (fun x =>
      { label := x.1.1
        bit := x.1.2
        position := x.2.1
        action := x.2.2 })

@[simp] private theorem path2List_length (psi : Nat) :
    (path2List psi).length = 12 * psi * (psi + 1) := by
  simp only [path2List, List.length_map, enumProd_length, finList_length]
  calc
    _ = (2 * 6) * psi * (psi + 1) := by ac_rfl
    _ = 12 * psi * (psi + 1) := by rfl

private def path2OptionList (psi : Nat) :
    List (Option (BoundedPath2Info psi)) :=
  optionList (path2List psi)

@[simp] private theorem path2OptionList_length (psi : Nat) :
    (path2OptionList psi).length = 12 * psi * (psi + 1) + 1 := by
  simp [path2OptionList]

private def path3List (psi : Nat) : List (BoundedPath3Info psi) :=
  (enumProd (finList psi)
      (enumProd (finList 2) (finList 2))).map
    (fun x =>
      { label := x.1
        bit := x.2.1
        flag := x.2.2 })

@[simp] private theorem path3List_length (psi : Nat) :
    (path3List psi).length = 4 * psi := by
  simp only [path3List, List.length_map, enumProd_length, finList_length]
  calc
    _ = (2 * 2) * psi := by ac_rfl
    _ = 4 * psi := by rfl

private def path3OptionList (psi : Nat) :
    List (Option (BoundedPath3Info psi)) :=
  optionList (path3List psi)

@[simp] private theorem path3OptionList_length (psi : Nat) :
    (path3OptionList psi).length = 4 * psi + 1 := by
  simp [path3OptionList]

private def cleaningLabelList (psi : Nat) : List (CleaningLabel psi) :=
  .clean :: (finList psi).map (fun i => CleaningLabel.normal i)

@[simp] private theorem cleaningLabelList_length (psi : Nat) :
    (cleaningLabelList psi).length = psi + 1 := by
  simp [cleaningLabelList]

private def cleanPathOptionList (psi : Nat) :
    List (Option (CleaningLabel psi × Fin 2)) :=
  optionList (enumProd (cleaningLabelList psi) (finList 2))

@[simp] private theorem cleanPathOptionList_length (psi : Nat) :
    (cleanPathOptionList psi).length = 2 * psi + 3 := by
  simp [cleanPathOptionList]
  omega

/-! Completeness follows the same field lists used in the length proof. -/

private theorem pathList_complete {psi : Nat} (x : BoundedPathInfo psi) :
    x ∈ pathList psi := by
  cases x with
  | bot => exact List.mem_cons_self
  | some label bit =>
      apply List.mem_cons_of_mem
      exact List.mem_map_of_mem
        (mem_enumProd_of_mem (finList_complete label) (finList_complete bit))

private theorem path2List_complete {psi : Nat} (x : BoundedPath2Info psi) :
    x ∈ path2List psi := by
  rcases x with ⟨label, bit, position, action⟩
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem
      (mem_enumProd_of_mem (finList_complete label) (finList_complete bit))
      (mem_enumProd_of_mem (finList_complete position) (finList_complete action)))

private theorem path2OptionList_complete {psi : Nat}
    (x : Option (BoundedPath2Info psi)) : x ∈ path2OptionList psi :=
  optionList_complete path2List_complete x

private theorem path3List_complete {psi : Nat} (x : BoundedPath3Info psi) :
    x ∈ path3List psi := by
  rcases x with ⟨label, bit, flag⟩
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem (finList_complete label)
      (mem_enumProd_of_mem (finList_complete bit) (finList_complete flag)))

private theorem path3OptionList_complete {psi : Nat}
    (x : Option (BoundedPath3Info psi)) : x ∈ path3OptionList psi :=
  optionList_complete path3List_complete x

private theorem cleaningLabelList_complete {psi : Nat} (x : CleaningLabel psi) :
    x ∈ cleaningLabelList psi := by
  cases x with
  | clean => exact List.mem_cons_self
  | normal label =>
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem (finList_complete label))

private theorem cleanPathOptionList_complete {psi : Nat}
    (x : Option (CleaningLabel psi × Fin 2)) : x ∈ cleanPathOptionList psi := by
  apply optionList_complete _ x
  intro p
  exact mem_enumProd_of_mem (cleaningLabelList_complete p.1) (finList_complete p.2)

/-! ## Balanced field blocks -/

private structure BlockA (psi : Nat) where
  leader : Bool
  probe : Bool
  phase : Bool
  bit : Bool
  wait : Bool
  state : MainState
  path : BoundedPathInfo psi
  reset : Bool

private structure BlockB (psi kappa : Nat) where
  carry : Bool
  count : Fin (kappa + 1)
  label : Fin psi
  h_field : Bool
  path2 : Option (BoundedPath2Info psi)
  path3 : Option (BoundedPath3Info psi)
  path4 : Option (CleaningLabel psi × Fin 2)
  path5 : Option (CleaningLabel psi × Fin 2)

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

private def blockAList (psi : Nat) : List (BlockA psi) :=
  (enumProd
      (enumProd
        (enumProd boolList boolList)
        (enumProd boolList boolList))
      (enumProd
        (enumProd boolList mainStateList)
        (enumProd (pathList psi) boolList))).map
    (fun x =>
      { leader := x.1.1.1
        probe := x.1.1.2
        phase := x.1.2.1
        bit := x.1.2.2
        wait := x.2.1.1
        state := x.2.1.2
        path := x.2.2.1
        reset := x.2.2.2 })

@[simp] private theorem blockAList_length (psi : Nat) :
    (blockAList psi).length = 960 * (2 * psi + 1) := by
  simp only [blockAList, List.length_map, enumProd_length,
    boolList_length, mainStateList_length, pathList_length]
  calc
    _ = (2 * 2 * 2 * 2 * 2 * 2 * 15) * (2 * psi + 1) := by
      ac_rfl
    _ = 960 * (2 * psi + 1) := by
      rw [show 2 * 2 * 2 * 2 * 2 * 2 * 15 = 960 by decide]

private def blockBList (psi kappa : Nat) : List (BlockB psi kappa) :=
  (enumProd
      (enumProd
        (enumProd boolList (finList (kappa + 1)))
        (enumProd (finList psi) boolList))
      (enumProd
        (enumProd (path2OptionList psi) (path3OptionList psi))
        (enumProd (cleanPathOptionList psi) (cleanPathOptionList psi)))).map
    (fun x =>
      { carry := x.1.1.1
        count := x.1.1.2
        label := x.1.2.1
        h_field := x.1.2.2
        path2 := x.2.1.1
        path3 := x.2.1.2
        path4 := x.2.2.1
        path5 := x.2.2.2 })

@[simp] private theorem blockBList_length (psi kappa : Nat) :
    (blockBList psi kappa).length =
      4 * (kappa + 1) * psi *
        (12 * psi * (psi + 1) + 1) *
        (4 * psi + 1) * (2 * psi + 3) ^ 2 := by
  simp only [blockBList, List.length_map, enumProd_length,
    boolList_length, finList_length,
    path2OptionList_length, path3OptionList_length,
    cleanPathOptionList_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  calc
    _ = (2 * 2) * (kappa + 1) * psi *
        (12 * psi * (psi + 1) + 1) *
        (4 * psi + 1) *
        ((2 * psi + 3) * (2 * psi + 3)) := by
      ac_rfl
    _ = 4 * (kappa + 1) * psi *
        (12 * psi * (psi + 1) + 1) *
        (4 * psi + 1) *
        ((2 * psi + 3) * (2 * psi + 3)) := by
      rw [show 2 * 2 = 4 by decide]

private def blockCList : List BlockC :=
  (enumProd
      (enumProd
        (enumProd boolList boolList)
        (enumProd boolList boolList))
      (enumProd
        (enumProd (finList 2) (finList 3))
        (enumProd boolList writeStateList))).map
    (fun x =>
      { p := x.1.1.1
        p_carry := x.1.1.2
        reset_cmd := x.1.2.1
        echo := x.1.2.2
        signal_B := x.2.1.1
        bullet := x.2.1.2
        shield := x.2.2.1
        write_state := x.2.2.2 })

@[simp] private theorem blockCList_length : blockCList.length = 2688 := by
  simp only [blockCList, List.length_map, enumProd_length,
    boolList_length, finList_length, writeStateList_length]

private def blockDList : List BlockD :=
  (enumProd
      (enumProd
        (enumProd writeActionList boolList)
        (enumProd boolList boolList))
      (enumProd
        (enumProd boolList boolList)
        (enumProd boolList boolList))).map
    (fun x =>
      { write := x.1.1.1
        last := x.1.1.2
        last_set := x.1.2.1
        last_unset := x.1.2.2
        b_carry := x.2.1.1
        gen_ws := x.2.1.2
        ws_echo := x.2.2.1
        signal_ws := x.2.2.2 })

@[simp] private theorem blockDList_length : blockDList.length = 640 := by
  simp only [blockDList, List.length_map, enumProd_length,
    writeActionList_length, boolList_length]

private theorem blockAList_complete {psi : Nat} (x : BlockA psi) :
    x ∈ blockAList psi := by
  rcases x with ⟨leader, probe, phase, bit, wait, state, path, reset⟩
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (boolList_complete leader) (boolList_complete probe))
        (mem_enumProd_of_mem (boolList_complete phase) (boolList_complete bit)))
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (boolList_complete wait) (mainStateList_complete state))
        (mem_enumProd_of_mem (pathList_complete path) (boolList_complete reset))))

private theorem blockBList_complete {psi kappa : Nat} (x : BlockB psi kappa) :
    x ∈ blockBList psi kappa := by
  rcases x with ⟨carry, count, label, h_field, path2, path3, path4, path5⟩
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (boolList_complete carry) (finList_complete count))
        (mem_enumProd_of_mem (finList_complete label) (boolList_complete h_field)))
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (path2OptionList_complete path2) (path3OptionList_complete path3))
        (mem_enumProd_of_mem (cleanPathOptionList_complete path4)
          (cleanPathOptionList_complete path5))))

private theorem blockCList_complete (x : BlockC) : x ∈ blockCList := by
  rcases x with ⟨p, p_carry, reset_cmd, echo, signal_B, bullet, shield, write_state⟩
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (boolList_complete p) (boolList_complete p_carry))
        (mem_enumProd_of_mem (boolList_complete reset_cmd) (boolList_complete echo)))
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (finList_complete signal_B) (finList_complete bullet))
        (mem_enumProd_of_mem (boolList_complete shield) (writeStateList_complete write_state))))

private theorem blockDList_complete (x : BlockD) : x ∈ blockDList := by
  rcases x with ⟨write, last, last_set, last_unset, b_carry, gen_ws, ws_echo, signal_ws⟩
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (writeActionList_complete write) (boolList_complete last))
        (mem_enumProd_of_mem (boolList_complete last_set) (boolList_complete last_unset)))
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem (boolList_complete b_carry) (boolList_complete gen_ws))
        (mem_enumProd_of_mem (boolList_complete ws_echo) (boolList_complete signal_ws))))

private def stateSource (psi kappa : Nat) :=
  enumProd
    (enumProd (blockAList psi) (blockBList psi kappa))
    (enumProd blockCList blockDList)

private def assembleState {psi kappa : Nat}
    (x : (BlockA psi × BlockB psi kappa) × (BlockC × BlockD)) :
    BoundedAgentState psi kappa :=
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

/-- Direct Cartesian counting list for `BoundedAgentState`, with its exact
length and surjective coverage proved below. -/
def boundedAgentStateList (psi kappa : Nat) :
    List (BoundedAgentState psi kappa) :=
  (stateSource psi kappa).map (fun x => assembleState x)

/-- Every actual bounded state occurs in the same list used for the polynomial
count.  The proof reconstructs its four field blocks without changing the
enumeration or assuming coverage of a different finite carrier. -/
theorem boundedAgentStateList_complete (psi kappa : Nat)
    (x : BoundedAgentState psi kappa) : x ∈ boundedAgentStateList psi kappa := by
  let a : BlockA psi :=
    ⟨x.leader, x.probe, x.phase, x.bit, x.wait, x.state, x.path, x.reset⟩
  let b : BlockB psi kappa :=
    ⟨x.carry, x.count, x.label, x.h_field, x.path2, x.path3, x.path4, x.path5⟩
  let c : BlockC :=
    ⟨x.p, x.p_carry, x.reset_cmd, x.echo, x.signal_B, x.bullet, x.shield, x.write_state⟩
  let d : BlockD :=
    ⟨x.write, x.last, x.last_set, x.last_unset, x.b_carry,
      x.gen_ws, x.ws_echo, x.signal_ws⟩
  have hmem : ((a, b), (c, d)) ∈ stateSource psi kappa :=
    mem_enumProd_of_mem
      (mem_enumProd_of_mem (blockAList_complete a) (blockBList_complete b))
      (mem_enumProd_of_mem (blockCList_complete c) (blockDList_complete d))
  exact List.mem_map_of_mem hmem

/-- Exact entry count of the bounded Cartesian carrier. -/
theorem boundedAgentState_length (psi kappa : Nat) :
    (boundedAgentStateList psi kappa).length =
      6606028800 * (kappa + 1) * psi * (2 * psi + 1) *
        (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
        (2 * psi + 3) ^ 2 := by
  simp only [boundedAgentStateList, List.length_map, stateSource,
    enumProd_length, blockAList_length, blockBList_length,
    blockCList_length, blockDList_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  calc
    _ = (960 * 4 * 2688 * 640) * (kappa + 1) * psi *
        (2 * psi + 1) * (12 * psi * (psi + 1) + 1) *
        (4 * psi + 1) * ((2 * psi + 3) * (2 * psi + 3)) := by
      ac_rfl
    _ = 6606028800 * (kappa + 1) * psi *
        (2 * psi + 1) * (12 * psi * (psi + 1) + 1) *
        (4 * psi + 1) * ((2 * psi + 3) * (2 * psi + 3)) := by
      rw [show 960 * 4 * 2688 * 640 = 6606028800 by decide]

/-! ## Polynomial cap -/

private theorem cap_rearrange (H : Nat) :
    6606028800 * H * H * (3 * H) * (25 * (H * H)) *
        (5 * H) * (25 * (H * H)) =
      61931520000000 * H ^ 8 := by
  rw [← show 6606028800 * 3 * 25 * 5 * 25 =
    61931520000000 by decide]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  ac_rfl

/-- With `kappa := h` and `psi <= h+1`, the exact legacy bounded carrier has
polynomial degree eight in `h+1`. -/
theorem carrier_le_poly :
    ∀ h psi : Nat, 1 ≤ psi → psi ≤ h + 1 →
      6606028800 * (h + 1) * psi * (2 * psi + 1) *
          (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
          (2 * psi + 3) ^ 2 ≤
        61931520000000 * (h + 1) ^ 8 := by
  intro h psi hpsiPos hpsiBound
  let H := h + 1
  have hpsiH : psi ≤ H := by
    simpa [H] using hpsiBound
  have hH : 1 ≤ H := Nat.le_trans hpsiPos hpsiH
  have hpsi1 : psi + 1 ≤ 2 * H := by omega
  have h2psi : 2 * psi + 1 ≤ 3 * H := by omega
  have h4psi : 4 * psi + 1 ≤ 5 * H := by omega
  have hclean : 2 * psi + 3 ≤ 5 * H := by omega
  have hpair : psi * (psi + 1) ≤ H * (2 * H) :=
    Nat.mul_le_mul hpsiH hpsi1
  have hscaled :
      12 * (psi * (psi + 1)) ≤ 12 * (H * (2 * H)) :=
    Nat.mul_le_mul_left 12 hpair
  have hHH : 1 ≤ H * H := by
    have hmul := Nat.mul_le_mul hH hH
    simpa using hmul
  have hpath2 :
      12 * psi * (psi + 1) + 1 ≤ 25 * (H * H) := by
    calc
      12 * psi * (psi + 1) + 1 =
          12 * (psi * (psi + 1)) + 1 := by
        rw [Nat.mul_assoc]
      _ ≤ 12 * (H * (2 * H)) + 1 :=
        Nat.add_le_add_right hscaled 1
      _ = (12 * 2) * (H * H) + 1 := by
        apply congrArg (fun x : Nat => x + 1)
        ac_rfl
      _ = 24 * (H * H) + 1 := by
        rw [show 12 * 2 = 24 by decide]
      _ ≤ 25 * (H * H) := by
        omega
  have hcleanPow : (2 * psi + 3) ^ 2 ≤ 25 * (H * H) := by
    calc
      (2 * psi + 3) ^ 2 =
          (2 * psi + 3) * (2 * psi + 3) := by
        simp [Nat.pow_succ]
      _ ≤ (5 * H) * (5 * H) :=
        Nat.mul_le_mul hclean hclean
      _ = (5 * 5) * (H * H) := by
        ac_rfl
      _ = 25 * (H * H) := by
        rw [show 5 * 5 = 25 by decide]
  change
    6606028800 * H * psi * (2 * psi + 1) *
        (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
        (2 * psi + 3) ^ 2 ≤
      61931520000000 * H ^ 8
  have h0 : 6606028800 * H ≤ 6606028800 * H := Nat.le_refl _
  have h1 :
      6606028800 * H * psi ≤ 6606028800 * H * H :=
    Nat.mul_le_mul h0 hpsiH
  have h2 :
      6606028800 * H * psi * (2 * psi + 1) ≤
        6606028800 * H * H * (3 * H) :=
    Nat.mul_le_mul h1 h2psi
  have h3 :
      6606028800 * H * psi * (2 * psi + 1) *
          (12 * psi * (psi + 1) + 1) ≤
        6606028800 * H * H * (3 * H) * (25 * (H * H)) :=
    Nat.mul_le_mul h2 hpath2
  have h4 :
      6606028800 * H * psi * (2 * psi + 1) *
          (12 * psi * (psi + 1) + 1) * (4 * psi + 1) ≤
        6606028800 * H * H * (3 * H) * (25 * (H * H)) *
          (5 * H) :=
    Nat.mul_le_mul h3 h4psi
  have h5 :
      6606028800 * H * psi * (2 * psi + 1) *
          (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
          (2 * psi + 3) ^ 2 ≤
        6606028800 * H * H * (3 * H) * (25 * (H * H)) *
          (5 * H) * (25 * (H * H)) :=
    Nat.mul_le_mul h4 hcleanPow
  calc
    6606028800 * H * psi * (2 * psi + 1) *
        (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
        (2 * psi + 3) ^ 2 ≤
      6606028800 * H * H * (3 * H) * (25 * (H * H)) *
        (5 * H) * (25 * (H * H)) := h5
    _ = 61931520000000 * H ^ 8 := cap_rearrange H

/-- Useful replacement for the meta-claim that the carrier has no `Fin n`
coordinate: changing an ignored ring-size parameter cannot change its length. -/
theorem boundedAgentState_length_independent_of_n
    (n psi kappa : Nat) :
    (fun _n : Nat => (boundedAgentStateList psi kappa).length) n =
      6606028800 * (kappa + 1) * psi * (2 * psi + 1) *
        (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
        (2 * psi + 3) ^ 2 := by
  simpa using boundedAgentState_length psi kappa

#print axioms boundedAgentStateList_complete
#print axioms boundedAgentState_length
#print axioms carrier_le_poly
#print axioms boundedAgentState_length_independent_of_n

end PPLLStateBoundCarrier
