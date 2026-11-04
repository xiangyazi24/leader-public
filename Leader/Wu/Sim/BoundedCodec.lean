import Std.Data.TreeMap.Raw.Lemmas
import Leader.Wu.Protocol.BoundedProtocol
import Lean.Data.Json
import Init.Data.Array.BasicAux
import Init.Data.Array.OfFn
import Init.Data.Vector.OfFn

set_option autoImplicit false

open Lean

namespace PPLLSimCodec

abbrev Config (n psi kappa : Nat) := Vector (BoundedAgentState psi kappa) n

private def objN (n : Nat) (j : Json) : Except String Unit := do
  let o <- j.getObj?
  if o.size = n then pure () else
    throw s!"expected object with {n} fields, got {o.size}"

private def fld (j : Json) (k : String) : Except String Json := j.getObjVal? k

private def dFin (n : Nat) (j : Json) : Except String (Fin n) := do
  let x <- j.getNat?
  if h : x < n then pure <| ⟨x, h⟩ else
    throw s!"Fin value {x} out of range 0..{n-1}"

private def dMain (j : Json) : Except String MainState := do
  match <- j.getStr? with
  | "produce" => pure .produce | "done" => pure .done
  | "depart" => pure .depart | "none" => pure .none
  | "congest" => pure .congest | "lock" => pure .lock
  | "compare1" => pure .compare1 | "compare2" => pure .compare2
  | "eliminate_signal" => pure .eliminate_signal
  | "CHECK_ready" => pure .CHECK_ready | "equal" => pure .equal
  | "larger" => pure .larger | "less" => pure .less
  | "toss" => pure .toss | "toss_done" => pure .toss_done
  | s => throw s!"unknown MainState tag: {s}"

private def eMain : MainState -> String
  | .produce => "produce" | .done => "done" | .depart => "depart"
  | .none => "none" | .congest => "congest" | .lock => "lock"
  | .compare1 => "compare1" | .compare2 => "compare2"
  | .eliminate_signal => "eliminate_signal" | .CHECK_ready => "CHECK_ready"
  | .equal => "equal" | .larger => "larger" | .less => "less"
  | .toss => "toss" | .toss_done => "toss_done"

private def dWS (j : Json) : Except String WriteState := do
  match <- j.getStr? with
  | "depart" => pure .depart | "ready" => pure .ready
  | "increment_WS" => pure .increment_WS
  | "increment_WS_done" => pure .increment_WS_done
  | "done" => pure .done | "equal" => pure .equal
  | "larger" => pure .larger | "less" => pure .less
  | "produce" => pure .produce | "overwrite" => pure .overwrite
  | "move_flip" => pure .move_flip | "move" => pure .move
  | "increment_group" => pure .increment_group | "none" => pure .none
  | s => throw s!"unknown WriteState tag: {s}"

private def eWS : WriteState -> String
  | .depart => "depart" | .ready => "ready" | .increment_WS => "increment_WS"
  | .increment_WS_done => "increment_WS_done" | .done => "done"
  | .equal => "equal" | .larger => "larger" | .less => "less"
  | .produce => "produce" | .overwrite => "overwrite"
  | .move_flip => "move_flip" | .move => "move"
  | .increment_group => "increment_group" | .none => "none"

private def dWA (j : Json) : Except String WriteAction := do
  match <- j.getStr? with
  | "overwrite" => pure .overwrite | "move_flip" => pure .move_flip
  | "move" => pure .move | "increment_group" => pure .increment_group
  | "none" => pure .none
  | s => throw s!"unknown WriteAction tag: {s}"

private def eWA : WriteAction -> String
  | .overwrite => "overwrite" | .move_flip => "move_flip" | .move => "move"
  | .increment_group => "increment_group" | .none => "none"

private def dPath {psi : Nat} : Json -> Except String (BoundedPathInfo psi)
  | .null => pure .bot
  | j => do
      objN 2 j
      let l <- dFin psi (← fld j "label")
      let b <- dFin 2 (← fld j "bit")
      return .some l b

def ePath {psi : Nat} : BoundedPathInfo psi -> Json
  | .bot => .null
  | .some l b => Json.mkObj [("label", l.val), ("bit", b.val)]

private def dP2 {psi : Nat} : Json -> Except String (Option (BoundedPath2Info psi))
  | .null => pure none
  | j => do
      objN 4 j
      let label <- dFin psi (← fld j "label")
      let bit <- dFin 2 (← fld j "bit")
      let position <- dFin (psi+1) (← fld j "position")
      let a <- (← fld j "action").getNat?
      if h : 1 <= a ∧ a <= 6 then
        return some { label, bit, position, action := ⟨a-1, by omega⟩ }
      else throw s!"path2 action {a} outside 1..6"

def eP2 {psi : Nat} : Option (BoundedPath2Info psi) -> Json
  | none => .null
  | some p => Json.mkObj [("label", p.label.val), ("bit", p.bit.val),
      ("position", p.position.val), ("action", (p.action.val + 1 : Nat))]

private def dP3 {psi : Nat} : Json -> Except String (Option (BoundedPath3Info psi))
  | .null => pure none
  | j => do
      objN 3 j
      let label <- dFin psi (← fld j "label")
      let bit <- dFin 2 (← fld j "bit")
      let flag <- dFin 2 (← fld j "flag")
      return some { label, bit, flag }

def eP3 {psi : Nat} : Option (BoundedPath3Info psi) -> Json
  | none => .null
  | some p => Json.mkObj
      [("label", p.label.val), ("bit", p.bit.val), ("flag", p.flag.val)]

private def dCleanLabel {psi : Nat} (j : Json) : Except String (CleaningLabel psi) := do
  let x <- j.getInt?
  if hx : x = -1 then pure .clean
  else if h0 : 0 <= x then
    let n := x.toNat
    if hn : n < psi then pure (.normal ⟨n, hn⟩)
    else throw s!"cleaning label {x} >= psi={psi}"
  else throw s!"cleaning label {x} is below -1"

private def eCleanLabel {psi : Nat} : CleaningLabel psi -> Json
  | .clean => (-1 : Int)
  | .normal l => l.val

private def dClean {psi : Nat} :
    Json -> Except String (Option (CleaningLabel psi × Fin 2))
  | .null => pure none
  | j => do
      objN 2 j
      let l <- dCleanLabel (psi:=psi) (← fld j "label")
      let b <- dFin 2 (← fld j "bit")
      return some (l, b)

def eClean {psi : Nat} : Option (CleaningLabel psi × Fin 2) -> Json
  | none => .null
  | some (l,b) => Json.mkObj [("label", eCleanLabel l), ("bit", b.val)]

def decodeState {psi kappa : Nat} (j : Json) :
    Except String (BoundedAgentState psi kappa) := do
  objN 32 j
  let leader <- (← fld j "leader").getBool?
  let probe <- (← fld j "probe").getBool?
  let phase <- (← fld j "phase").getBool?
  let bit <- (← fld j "bit").getBool?
  let wait <- (← fld j "wait").getBool?
  let state <- dMain (← fld j "state")
  let path <- dPath (psi:=psi) (← fld j "path")
  let reset <- (← fld j "reset").getBool?
  let carry <- (← fld j "carry").getBool?
  let count <- dFin (kappa+1) (← fld j "count")
  let label <- dFin psi (← fld j "label")
  let h_field <- (← fld j "h_field").getBool?
  let path2 <- dP2 (psi:=psi) (← fld j "path2")
  let path3 <- dP3 (psi:=psi) (← fld j "path3")
  let path4 <- dClean (psi:=psi) (← fld j "path4")
  let path5 <- dClean (psi:=psi) (← fld j "path5")
  let p <- (← fld j "p").getBool?
  let p_carry <- (← fld j "p_carry").getBool?
  let reset_cmd <- (← fld j "reset_cmd").getBool?
  let echo <- (← fld j "echo").getBool?
  let signal_B <- dFin 2 (← fld j "signal_B")
  let bullet <- dFin 3 (← fld j "bullet")
  let shield <- (← fld j "shield").getBool?
  let write_state <- dWS (← fld j "write_state")
  let write <- dWA (← fld j "write")
  let last <- (← fld j "last").getBool?
  let last_set <- (← fld j "last_set").getBool?
  let last_unset <- (← fld j "last_unset").getBool?
  let b_carry <- (← fld j "b_carry").getBool?
  let gen_ws <- (← fld j "gen_ws").getBool?
  let ws_echo <- (← fld j "ws_echo").getBool?
  let signal_ws <- (← fld j "signal_ws").getBool?
  return {
    leader := leader, probe := probe, phase := phase, bit := bit, wait := wait,
    state := state, path := path, reset := reset, carry := carry, count := count,
    label := label, h_field := h_field, path2 := path2, path3 := path3,
    path4 := path4, path5 := path5, p := p, p_carry := p_carry,
    reset_cmd := reset_cmd, echo := echo, signal_B := signal_B, bullet := bullet,
    shield := shield, write_state := write_state, write := write, last := last,
    last_set := last_set, last_unset := last_unset, b_carry := b_carry,
    gen_ws := gen_ws, ws_echo := ws_echo, signal_ws := signal_ws }

def encodeState {psi kappa : Nat} (s : BoundedAgentState psi kappa) : Json :=
  Json.mkObj [
    ("leader", s.leader), ("probe", s.probe), ("phase", s.phase), ("bit", s.bit),
    ("wait", s.wait), ("state", eMain s.state), ("path", ePath s.path),
    ("reset", s.reset), ("carry", s.carry), ("count", s.count.val),
    ("label", s.label.val), ("h_field", s.h_field), ("path2", eP2 s.path2),
    ("path3", eP3 s.path3), ("path4", eClean s.path4), ("path5", eClean s.path5),
    ("p", s.p), ("p_carry", s.p_carry), ("reset_cmd", s.reset_cmd),
    ("echo", s.echo), ("signal_B", s.signal_B.val), ("bullet", s.bullet.val),
    ("shield", s.shield), ("write_state", eWS s.write_state), ("write", eWA s.write),
    ("last", s.last), ("last_set", s.last_set), ("last_unset", s.last_unset),
    ("b_carry", s.b_carry), ("gen_ws", s.gen_ws), ("ws_echo", s.ws_echo),
    ("signal_ws", s.signal_ws) ]

private abbrev KV := String × Json


private theorem objN_mkObj_length {xs : List KV}
    (hd : xs.Pairwise (fun a b => compare a.1 b.1 ≠ .eq)) :
    objN xs.length (Json.mkObj xs) = .ok () := by
  simp [objN, Json.mkObj, Json.getObj?,
    Std.TreeMap.Raw.size_ofList (cmp := compare) hd] <;> rfl


private theorem fld_mkObj_of_mem {xs : List KV} {k : String} {v : Json}
    (hd : xs.Pairwise (fun a b => compare a.1 b.1 ≠ .eq))
    (hm : (k, v) ∈ xs) :
    fld (Json.mkObj xs) k = .ok v := by
  have hget :
      (Std.TreeMap.Raw.ofList xs compare).get? k = some v := by
    rw [Std.TreeMap.Raw.get?_eq_getElem?]
    exact Std.TreeMap.Raw.getElem?_ofList_of_mem
      (cmp := compare) (by simp) hd hm
  rw [Std.TreeMap.Raw.get?_eq_getElem?] at hget
  simp [fld, Json.mkObj, Json.getObjVal?, hget] <;> rfl


@[simp] private theorem dFin_val {n : Nat} (x : Fin n) :
    dFin n (x.val : Json) = .ok x := by
  have hnat : ((x.val : Nat) : Json).getNat? = .ok x.val := by rfl
  change (if h : x.val < n then Except.ok (⟨x.val, h⟩ : Fin n)
    else Except.error s!"Fin value {x.val} out of range 0..{n-1}") = .ok x
  simp [x.isLt]


@[simp] private theorem dMain_eMain (x : MainState) :
    dMain (eMain x) = .ok x := by
  cases x <;> rfl


@[simp] private theorem dWS_eWS (x : WriteState) :
    dWS (eWS x) = .ok x := by
  cases x <;> rfl


@[simp] private theorem dWA_eWA (x : WriteAction) :
    dWA (eWA x) = .ok x := by
  cases x <;> rfl


private def pathFields {psi : Nat} (l : Fin psi) (b : Fin 2) : List KV :=
  [("label", l.val), ("bit", b.val)]


private theorem pathFields_distinct {psi : Nat} (l : Fin psi) (b : Fin 2) :
    (pathFields l b).Pairwise (fun a c => compare a.1 c.1 ≠ .eq) := by
  unfold pathFields
  simp [List.pairwise_cons]


private theorem ePath_some_eq {psi : Nat} (l : Fin psi) (b : Fin 2) :
    ePath (BoundedPathInfo.some l b) = Json.mkObj (pathFields l b) := rfl


@[simp] private theorem dPath_ePath {psi : Nat} (p : BoundedPathInfo psi) :
    dPath (ePath p) = .ok p := by
  cases p with
  | bot => rfl
  | some l b =>
      rw [ePath_some_eq]
      have hd := pathFields_distinct l b
      have ho : objN 2 (Json.mkObj (pathFields l b)) = .ok () := by
        simpa [pathFields] using (objN_mkObj_length hd)
      have hl : fld (Json.mkObj (pathFields l b)) "label" =
          .ok (l.val : Json) :=
        fld_mkObj_of_mem hd (by simp [pathFields])
      have hb : fld (Json.mkObj (pathFields l b)) "bit" =
          .ok (b.val : Json) :=
        fld_mkObj_of_mem hd (by simp [pathFields])
      simp only [Json.mkObj] at ho hl hb ⊢
      simp [dPath, ho, hl, hb, Bind.bind, Except.bind, Except.map] <;> rfl


private def p2Fields {psi : Nat} (p : BoundedPath2Info psi) : List KV :=
  [("label", p.label.val), ("bit", p.bit.val),
   ("position", p.position.val), ("action", ((p.action.val + 1 : Nat) : Json))]


private theorem p2Fields_distinct {psi : Nat} (p : BoundedPath2Info psi) :
    (p2Fields p).Pairwise (fun a c => compare a.1 c.1 ≠ .eq) := by
  unfold p2Fields
  simp [List.pairwise_cons]


private theorem eP2_some_eq {psi : Nat} (p : BoundedPath2Info psi) :
    eP2 (some p) = Json.mkObj (p2Fields p) := rfl


@[simp] private theorem dP2_eP2 {psi : Nat}
    (q : Option (BoundedPath2Info psi)) :
    dP2 (eP2 q) = .ok q := by
  cases q with
  | none => rfl
  | some p =>
      rw [eP2_some_eq]
      have hd := p2Fields_distinct p
      have ho : objN 4 (Json.mkObj (p2Fields p)) = .ok () := by
        simpa [p2Fields] using (objN_mkObj_length hd)
      have hl : fld (Json.mkObj (p2Fields p)) "label" =
          .ok (p.label.val : Json) :=
        fld_mkObj_of_mem hd (by simp [p2Fields])
      have hb : fld (Json.mkObj (p2Fields p)) "bit" =
          .ok (p.bit.val : Json) :=
        fld_mkObj_of_mem hd (by simp [p2Fields])
      have hp : fld (Json.mkObj (p2Fields p)) "position" =
          .ok (p.position.val : Json) :=
        fld_mkObj_of_mem hd (by simp [p2Fields])
      have ha : fld (Json.mkObj (p2Fields p)) "action" =
          .ok ((p.action.val + 1 : Nat) : Json) :=
        fld_mkObj_of_mem hd (by simp [p2Fields])
      have hbounds : 1 ≤ p.action.val + 1 ∧ p.action.val + 1 ≤ 6 := by
        have hlt := p.action.isLt
        omega
      simp only [Json.mkObj] at ho hl hb hp ha ⊢
      have hnat : (((p.action.val + 1 : Nat) : Json)).getNat? = .ok (p.action.val + 1) := by rfl
      simp [dP2, ho, hl, hb, hp, ha, hnat, hbounds, Bind.bind, Except.bind, Except.map] <;> rfl


private def p3Fields {psi : Nat} (p : BoundedPath3Info psi) : List KV :=
  [("label", p.label.val), ("bit", p.bit.val), ("flag", p.flag.val)]


private theorem p3Fields_distinct {psi : Nat} (p : BoundedPath3Info psi) :
    (p3Fields p).Pairwise (fun a c => compare a.1 c.1 ≠ .eq) := by
  unfold p3Fields
  simp [List.pairwise_cons]


private theorem eP3_some_eq {psi : Nat} (p : BoundedPath3Info psi) :
    eP3 (some p) = Json.mkObj (p3Fields p) := rfl


@[simp] private theorem dP3_eP3 {psi : Nat}
    (q : Option (BoundedPath3Info psi)) :
    dP3 (eP3 q) = .ok q := by
  cases q with
  | none => rfl
  | some p =>
      rw [eP3_some_eq]
      have hd := p3Fields_distinct p
      have ho : objN 3 (Json.mkObj (p3Fields p)) = .ok () := by
        simpa [p3Fields] using (objN_mkObj_length hd)
      have hl : fld (Json.mkObj (p3Fields p)) "label" =
          .ok (p.label.val : Json) :=
        fld_mkObj_of_mem hd (by simp [p3Fields])
      have hb : fld (Json.mkObj (p3Fields p)) "bit" =
          .ok (p.bit.val : Json) :=
        fld_mkObj_of_mem hd (by simp [p3Fields])
      have hf : fld (Json.mkObj (p3Fields p)) "flag" =
          .ok (p.flag.val : Json) :=
        fld_mkObj_of_mem hd (by simp [p3Fields])
      simp only [Json.mkObj] at ho hl hb hf ⊢
      simp [dP3, ho, hl, hb, hf, Bind.bind, Except.bind, Except.map] <;> rfl


@[simp] private theorem dCleanLabel_eCleanLabel {psi : Nat}
    (l : CleaningLabel psi) :
    dCleanLabel (eCleanLabel l) = .ok l := by
  cases l with
  | normal x =>
      have hint : (((x.val : Nat) : Json)).getInt? = .ok (Int.ofNat x.val) := by rfl
      simp [dCleanLabel, eCleanLabel, hint, x.isLt, Bind.bind, Except.bind] <;> rfl
  | clean => rfl


private def cleanFields {psi : Nat}
    (l : CleaningLabel psi) (b : Fin 2) : List KV :=
  [("label", eCleanLabel l), ("bit", b.val)]


private theorem cleanFields_distinct {psi : Nat}
    (l : CleaningLabel psi) (b : Fin 2) :
    (cleanFields l b).Pairwise (fun a c => compare a.1 c.1 ≠ .eq) := by
  unfold cleanFields
  simp [List.pairwise_cons]


private theorem eClean_some_eq {psi : Nat}
    (l : CleaningLabel psi) (b : Fin 2) :
    eClean (some (l, b)) = Json.mkObj (cleanFields l b) := rfl


@[simp] private theorem dClean_eClean {psi : Nat}
    (q : Option (CleaningLabel psi × Fin 2)) :
    dClean (eClean q) = .ok q := by
  cases q with
  | none => rfl
  | some q =>
      rcases q with ⟨l, b⟩
      rw [eClean_some_eq]
      have hd := cleanFields_distinct l b
      have ho : objN 2 (Json.mkObj (cleanFields l b)) = .ok () := by
        simpa [cleanFields] using (objN_mkObj_length hd)
      have hl : fld (Json.mkObj (cleanFields l b)) "label" =
          .ok (eCleanLabel l) :=
        fld_mkObj_of_mem hd (by simp [cleanFields])
      have hb : fld (Json.mkObj (cleanFields l b)) "bit" =
          .ok (b.val : Json) :=
        fld_mkObj_of_mem hd (by simp [cleanFields])
      simp only [Json.mkObj] at ho hl hb ⊢
      simp [dClean, ho, hl, hb, Bind.bind, Except.bind, Except.map] <;> rfl


private def stateFields {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) : List KV := [
  ("leader", s.leader), ("probe", s.probe), ("phase", s.phase), ("bit", s.bit),
  ("wait", s.wait), ("state", eMain s.state), ("path", ePath s.path),
  ("reset", s.reset), ("carry", s.carry), ("count", s.count.val),
  ("label", s.label.val), ("h_field", s.h_field), ("path2", eP2 s.path2),
  ("path3", eP3 s.path3), ("path4", eClean s.path4), ("path5", eClean s.path5),
  ("p", s.p), ("p_carry", s.p_carry), ("reset_cmd", s.reset_cmd),
  ("echo", s.echo), ("signal_B", s.signal_B.val), ("bullet", s.bullet.val),
  ("shield", s.shield), ("write_state", eWS s.write_state), ("write", eWA s.write),
  ("last", s.last), ("last_set", s.last_set), ("last_unset", s.last_unset),
  ("b_carry", s.b_carry), ("gen_ws", s.gen_ws), ("ws_echo", s.ws_echo),
  ("signal_ws", s.signal_ws) ]


private theorem stateFields_distinct {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) :
    (stateFields s).Pairwise (fun a c => compare a.1 c.1 ≠ .eq) := by
  unfold stateFields
  simp [List.pairwise_cons]


private theorem stateFields_length {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) : (stateFields s).length = 32 := rfl


private theorem encodeState_eq_fields {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) :
    encodeState s = Json.mkObj (stateFields s) := rfl


@[simp] private theorem objN_encodeState {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) :
    objN 32 (encodeState s) = .ok () := by
  rw [encodeState_eq_fields]
  simpa only [stateFields_length] using
    (objN_mkObj_length (stateFields_distinct s))


private theorem fld_encodeState_of_mem {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) {k : String} {v : Json}
    (h : (k, v) ∈ stateFields s) :
    fld (encodeState s) k = .ok v := by
  rw [encodeState_eq_fields]
  exact fld_mkObj_of_mem (stateFields_distinct s) h


syntax "ppll_codec_field " ident str term : command
macro_rules
  | `(ppll_codec_field $nm:ident $key:str $f:term) =>
      `(@[simp] private theorem $nm {psi kappa : Nat}
          (s : BoundedAgentState psi kappa) :
          fld (encodeState s) $key = .ok (($f) s : Json) := by
        exact fld_encodeState_of_mem s (by simp [stateFields]))


ppll_codec_field rt_leader "leader" (fun s => s.leader)
ppll_codec_field rt_probe "probe" (fun s => s.probe)
ppll_codec_field rt_phase "phase" (fun s => s.phase)
ppll_codec_field rt_bit "bit" (fun s => s.bit)
ppll_codec_field rt_wait "wait" (fun s => s.wait)
ppll_codec_field rt_state "state" (fun s => eMain s.state)
ppll_codec_field rt_path "path" (fun s => ePath s.path)
ppll_codec_field rt_reset "reset" (fun s => s.reset)
ppll_codec_field rt_carry "carry" (fun s => s.carry)
ppll_codec_field rt_count "count" (fun s => s.count.val)
ppll_codec_field rt_label "label" (fun s => s.label.val)
ppll_codec_field rt_h_field "h_field" (fun s => s.h_field)
ppll_codec_field rt_path2 "path2" (fun s => eP2 s.path2)
ppll_codec_field rt_path3 "path3" (fun s => eP3 s.path3)
ppll_codec_field rt_path4 "path4" (fun s => eClean s.path4)
ppll_codec_field rt_path5 "path5" (fun s => eClean s.path5)
ppll_codec_field rt_p "p" (fun s => s.p)
ppll_codec_field rt_p_carry "p_carry" (fun s => s.p_carry)
ppll_codec_field rt_reset_cmd "reset_cmd" (fun s => s.reset_cmd)
ppll_codec_field rt_echo "echo" (fun s => s.echo)
ppll_codec_field rt_signal_B "signal_B" (fun s => s.signal_B.val)
ppll_codec_field rt_bullet "bullet" (fun s => s.bullet.val)
ppll_codec_field rt_shield "shield" (fun s => s.shield)
ppll_codec_field rt_write_state "write_state" (fun s => eWS s.write_state)
ppll_codec_field rt_write "write" (fun s => eWA s.write)
ppll_codec_field rt_last "last" (fun s => s.last)
ppll_codec_field rt_last_set "last_set" (fun s => s.last_set)
ppll_codec_field rt_last_unset "last_unset" (fun s => s.last_unset)
ppll_codec_field rt_b_carry "b_carry" (fun s => s.b_carry)
ppll_codec_field rt_gen_ws "gen_ws" (fun s => s.gen_ws)
ppll_codec_field rt_ws_echo "ws_echo" (fun s => s.ws_echo)
ppll_codec_field rt_signal_ws "signal_ws" (fun s => s.signal_ws)


theorem decodeState_encodeState {psi kappa : Nat}
    (s : BoundedAgentState psi kappa) :
    decodeState (encodeState s) = .ok s := by
  cases s
  simp [decodeState, Json.getBool?, Bind.bind, Except.bind, Except.map] <;> rfl

def decodeConfig {n psi kappa : Nat} (j : Json) :
    Except String (Config n psi kappa) := do
  let a <- j.getArr?
  if h : a.size = n then
    let v : Vector Json n := ⟨a, h⟩
    Vector.ofFnM fun i =>
      match decodeState (psi:=psi) (kappa:=kappa) (v.get i) with
      | .ok state => .ok state
      | .error message => .error s!"states[{i.val}]: {message}"
  else throw s!"configuration length {a.size}, expected {n}"

def encodeConfig {n psi kappa : Nat} (C : Config n psi kappa) : Json :=
  Json.arr <| C.toArray.map encodeState

def decodeConfigText {n psi kappa : Nat} (s : String) :
    Except String (Config n psi kappa) :=
  Json.parse s >>= decodeConfig (n:=n) (psi:=psi) (kappa:=kappa)

def encodeConfigText {n psi kappa : Nat} (C : Config n psi kappa) : String :=
  (encodeConfig C).compress

end PPLLSimCodec
