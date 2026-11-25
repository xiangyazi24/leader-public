import Leader.L4.Height.GateResidence
import Leader.L4.BStarParkedPhysical
import Leader.L4.BStarGeneratedPCAncestry
import Leader.L4.BStarSeparatingProgress
import Leader.L4.BStarOwnerLaunchOrigin
import Leader.L4.BStarReleaseOrigin
import Leader.L4.BStarResetHealthyService
import Leader.L4.BStarResetConsumedClean

namespace L4.Height

open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarLongToken BStarLongDoor BStarLongFixedRouting BStarH6WordChart BStarH6Ordinal
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner
open BStarAdmitIncidentGeometry BStarClearanceRaceMark BStarBitParity
open BStarSteeredLikelihood BStarParkedSteering BStarSteeringSupport
open BStarClearanceSource BStarSeparatingRail BStarSeparatingProgress
open BStarResetMarkAdapter BStarResetSchedule BStarSeparatorControl

/-- One tour's physical work. Outbound motion uses the literal
forward-coordinate sum and reserves the later reverse and receipt marks. -/
def physicalTourWork (len forwardScore : Nat) : Mode → Nat
  | .idle => 6 * (len + 1) + 4
  | .busy _ (.out _) => forwardScore + 2 * (len + 1)
  | .busy _ (.back k) => 2 * (k + 1)

private theorem aggregate_one {A : Type} (a : A) (xs : List A) (f : A → Nat)
    (N : xs.Nodup) (M : a ∈ xs) (Z : ∀ b ∈ xs, b ≠ a → f b = 0) :
    BStarClearanceAggregate.total f xs = f a := by
  have allZero (ys : List A) (H : ∀ b ∈ ys, f b = 0) :
      BStarClearanceAggregate.total f ys = 0 := by
    induction ys with
    | nil => rfl
    | cons b ys ih =>
      unfold BStarClearanceAggregate.total at *
      rw [List.map_cons, List.sum_cons, H b (List.mem_cons_self), ih
        (fun j J => H j (List.mem_cons_of_mem _ J))]
  induction xs with
  | nil => exact (List.not_mem_nil M).elim
  | cons b ys ih =>
    obtain ⟨notMem, tailN⟩ := List.nodup_cons.mp N
    rcases List.mem_cons.mp M with equal | tailM
    · subst b
      have eq := allZero ys (fun j J => Z j (List.mem_cons_of_mem _ J)
        (fun E => notMem (E ▸ J)))
      simp [BStarClearanceAggregate.total] at eq ⊢
      omega
    · have eq := Z b List.mem_cons_self (fun E => notMem (E.symm ▸ tailM))
      have tail := ih tailN tailM (fun j J => Z j (List.mem_cons_of_mem _ J))
      simpa [BStarClearanceAggregate.total, eq] using tail

section Physical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "run" => BStarResetSchedule.run step

/-- An emitted prefix still carries a diversion of this exact nominee.
Continuations are measured in candidate marks. -/
def divertedNomination
    (start : X) (redirect : Word n → Fin n → Option (Fin n))
    (Q : X → Prop) (now : Word n) (nominee : Fin n) : Prop :=
  ∃ a skipped f, Q (run start a) ∧ redirect a nominee = some f ∧
    (∀ j ∈ skipped, j ≠ nominee) ∧
    now = (a ++ [f]) ++ emit (chooseBy redirect) (a ++ [f]) skipped

theorem diverted_nomination_passes {base : X} {hh : ∃ i, oldH6 B base i = true}
    (start : X) {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (physical : ∀ a i, fresh a i → firstAdmission hp (base := base) (hh := hh) (run start a) i)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (now : Word n) (e : Fin n)
    (H : divertedNomination hp start redirect Q now e) :
    chooseBy redirect now e = e := by
  obtain ⟨a, skipped, f, q, first, avoid, rfl⟩ := H
  exact submask_redirect_two_hits hp start mask physical Q fiber closed ready distinct
    a skipped e f q first avoid

private theorem emit_append_one {m : Nat} (choose : Word m → Fin m → Fin m)
    (a w : Word m) (e : Fin m) :
    emit choose a (w ++ [e]) = emit choose a w ++ [choose (a ++ emit choose a w) e] := by
  induction w generalizing a with
  | nil => simp [emit]
  | cons k w ih => simp [emit, ih, List.append_assoc]

theorem diverted_nomination_extends
    (start : X) (redirect : Word n → Fin n → Option (Fin n))
    (Q : X → Prop) (now : Word n) (nominee candidate : Fin n)
    (H : divertedNomination hp start redirect Q now nominee)
    (skip : candidate ≠ nominee) :
    divertedNomination hp start redirect Q
      (now ++ [chooseBy redirect now candidate]) nominee := by
  obtain ⟨a, skipped, f, q, first, avoid, rfl⟩ := H
  refine ⟨a, skipped ++ [candidate], f, q, first, ?_, ?_⟩
  · intro j hit
    rcases List.mem_append.mp hit with A | B'
    · exact avoid j A
    · have J : j = candidate := by simpa using B'
      exact J.symm ▸ skip
  · rw [emit_append_one]
    simp only [List.append_assoc]

theorem diversion_starts
    (start : X) (redirect : Word n → Fin n → Option (Fin n))
    (Q : X → Prop) (now : Word n) (nominee : Fin n) (q : Q (run start now))
    (redirected : chooseBy redirect now nominee ≠ nominee) :
    divertedNomination hp start redirect Q
      (now ++ [chooseBy redirect now nominee]) nominee := by
  cases h : redirect now nominee with
  | none => exact (redirected (by simp [chooseBy, h])).elim
  | some f =>
    refine ⟨now, [], f, q, h, (fun j J => (List.not_mem_nil J).elim), ?_⟩
    simp [chooseBy, h, emit]

/-- The source takes a real receipt to the next strictly higher opcode,
or restarts at zero. A denial or a fault is included in this statement. -/
theorem receipt_program_order (old : BitVec LW) (f : Payload)
    (legal : (ctrlOp.read old).toNat < 413) :
    BStarLiteralPC.pcNext old f = 0 ∨
      (ctrlOp.read old).toNat < BStarLiteralPC.pcNext old f := by
  unfold BStarLiteralPC.pcNext
  dsimp only
  split
  · exact .inl rfl
  · split
    · rename_i ar
      have range := BStarArithmeticControllerReturn.arithmetic_range _ ar
      rcases BStarArithmeticControllerReturn.successor_order old _ range.2 with H | H
      · exact .inl H
      · exact .inr (by omega)
    · exact (BStarResetControllerProgress.ordinary_progress old _ f legal).imp id And.left

/-- One physical generated busy-to-busy mark never moves the cursor
backwards in its outward-then-return travel order. -/
theorem actual_cursor_advance {x : X} {addr : Nat → Pos n} {len op : Nat}
    {e : Fin n} {z d : Cursor}
    (event : Event hp addr len x e (.busy op z) (.busy op d)) : Advance len z d := by
  cases event with
  | transit _ _ _ _ seen =>
    cases seen with
    | cons _ _ advance _ tail =>
      cases tail
      exact advance
  | arrived_hold => exact .stay _

theorem physical_receipt_program_order {base x : X} {addr : Nat → Pos n}
    {len op : Nat} {e : Fin n}
    (root : (addr 0).2 = 0) (header : (oldHeaders B (x (addr 0).1)).h6 = true)
    (sep : e ≠ rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (event : Event hp addr len x e (.busy op (.back 0)) .idle) :
    let old := (ctrlOp.read (x (addr 0).1).long).toNat
    let new := (ctrlOp.read (step x e (addr 0).1).long).toNat
    new = 0 ∨ old < new := by
  dsimp only
  obtain ⟨f, _, pc⟩ := BStarGeneratedPCAncestry.consume_pc hp root header sep cur event
  rw [pc]
  have valid := cur.1.2.1
  unfold LongDoorGuard.valid at valid
  have legal : (ctrlOp.read (x (addr 0).1).long).toNat < 413 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2
  exact receipt_program_order _ f legal

/-- The matching opcode-2 acceptance is the positive physical stop,
after the release has traversed all three grant ports. -/
theorem release_receipt_stops {base x : X} {addr : Nat → Pos n}
    {len : Nat} {e : Fin n} (f : Payload)
    (root : (addr 0).2 = 0) (header : (oldHeaders B (x (addr 0).1)).h6 = true)
    (sep : e ≠ rightNeighbor e)
    (cur : Current hp base addr len x (.busy 2 (.back 0)))
    (event : Event hp addr len x e (.busy 2 (.back 0)) .idle)
    (read : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0) = .reply f)
    (healthy : f.fault = 0) (op : f.opcode.toNat = 2) :
    (ctrlOp.read (step x e (addr 0).1).long).toNat = 3 := by
  obtain ⟨q, token, pc⟩ := BStarGeneratedPCAncestry.consume_pc hp root header sep cur event
  have E : q = f := Token.reply.inj (token.symm.trans read)
  subst q
  have old : (ctrlOp.read (x (addr 0).1).long).toNat = 2 := cur.1.2.2.2
  rw [pc]
  simp [BStarLiteralPC.pcNext, old, healthy, op, arithKind,
    BStarResetControllerProgress.nextOrdinary]

/-- Each chart position has a fixed physical link label, or a terminal
label at its last position. -/
noncomputable def chartMark {base : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (j : Nat) : Fin n :=
  if h : j ≤ len then Classical.choose (BStarResetChartNomination.nominate hp C head cont j h)
  else fall.1

theorem chart_mark_selected {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (j : Nat) (hj : j ≤ len) (same : ∀ i, Layout B base i = Layout B x i) :
    (if j < len then Label.link j else Label.terminal) ∈
      labels hp x (chartMark hp C head cont j) (fun k => S.getD k fall) len := by
  rw [chartMark, dif_pos hj]
  exact Classical.choose_spec (BStarResetChartNomination.nominate hp C head cont j hj) x same

/-- The fixed nominee really has the pointed slot as its selected
old command source, including at the terminal. -/
theorem chart_mark_outbound {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (k : Nat) (hk : k ≤ len) (same : ∀ i, Layout B base i = Layout B x i) :
    let e := chartMark hp C head cont k
    ∃ K, K ∈ orderedCommands (oldPair B x e) ∧ K.kind ≠ .door ∧ S.getD k fall = address e K.source := by
  let e := chartMark hp C head cont k
  let addr := fun j => S.getD j fall
  have H := chart_mark_selected hp C head cont k hk same
  by_cases inner : k < len
  · rw [if_pos inner] at H
    obtain ⟨_, K, a, M, dest, source, _⟩ := (mem_link hp x e addr len k).mp H
    have shape := BStarAcquireReturn.link_shape _ K a M dest
    refine ⟨K, M, ?_, source⟩
    rw [shape.2.1]
    decide
  · have eq : k = len := by omega
    rw [if_neg inner] at H
    subst k
    obtain ⟨K, M, kind, _, _, source⟩ := (mem_terminal hp x e addr len).mp H
    refine ⟨K, M, ?_, source⟩
    rw [kind]
    decide

/-- The old bound packet determines whether this slot still needs a
side observation. Race 2 has recorded the incoming side, race 3 the
outgoing side. -/
def pendingSide (g : LongGeometry) (j : Fin 11) (v : Token) : Option Side :=
  match bind g j v with
  | .forward p =>
    if p.fault == 0 && gate p.opcode.toNat j g then
      if p.race = 1 ∨ p.race = 2 then some .left
      else if p.race = 3 then some .right else none
    else none
  | _ => none

def oldWaiting (b : LargeRows (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (addr : Nat → Pos n) (x : X) : Mode → Bool
  | .busy _ (.out k) =>
    let z := addr k
    (pendingSide (longGeometry b (x z.1)) z.2 (atSite (x z.1).long z.2)).isSome
  | _ => false

private theorem pending_gate_fields (g : LongGeometry) (j : Fin 11) (u : Token)
    (s : Side) (H : pendingSide g j u = some s) :
    ∃ bit v, bind g j u = .forward v ∧ v.opcode.toNat = gateOpcode bit ∧
      v.fault = 0 ∧ gate (gateOpcode bit) j g = true ∧
      ((v.race = 1 ∧ s = .left) ∨ ∃ t, t ≠ s ∧ v.race = firstCode t) := by
  unfold pendingSide at H
  cases eq : bind g j u with
  | empty => simp [eq] at H
  | trail => simp [eq] at H
  | reply _ => simp [eq] at H
  | forward v =>
    simp only [eq] at H
    split at H
    · rename_i live
      have fault := beq_iff_eq.mp (Bool.and_eq_true_iff.mp live).1
      have gateLive := (Bool.and_eq_true_iff.mp live).2
      have kind : ∃ bit, v.opcode.toNat = gateOpcode bit := by
        have test := (Bool.and_eq_true_iff.mp gateLive).2
        simp only [Bool.or_eq_true] at test
        rcases test with admitLive | bitLive
        · exact ⟨false, beq_iff_eq.mp (Bool.and_eq_true_iff.mp admitLive).1⟩
        · exact ⟨true, beq_iff_eq.mp (Bool.and_eq_true_iff.mp bitLive).1⟩
      obtain ⟨bit, op⟩ := kind
      refine ⟨bit, v, rfl, op, fault, op ▸ gateLive, ?_⟩
      split at H
      · rename_i R
        have side := (Option.some.inj H).symm
        rcases R with one | two
        · exact .inl ⟨one, side⟩
        · exact .inr ⟨.right, by rw [side]; decide, two⟩
      · split at H
        · rename_i R
          have side := (Option.some.inj H).symm
          exact .inr ⟨.left, by rw [side]; decide, R⟩
        · contradiction
    · contradiction

/-- The empty pending side is exactly zero race debt. Positive debt
two is FIRST and therefore has the same outgoing nominee everywhere. -/
private theorem pending_weight (g : LongGeometry) (j : Fin 11) (u : Token) :
    let q := BStarClearanceGate.weight g j (bind g j u)
    (pendingSide g j u = none ↔ q = 0) ∧
      (q = 2 → pendingSide g j u = some .left) := by
  dsimp only
  unfold pendingSide
  cases H : bind g j u <;> simp only [BStarClearanceGate.weight]
  · simp
  · simp
  · rename_i v
    by_cases G : (v.fault == 0 && gate v.opcode.toNat j g) = true
    · rw [if_pos G, if_pos G]
      unfold BStarClearanceGate.raceWeight
      by_cases one : v.race = 1
      · simp [one]
      · by_cases two : v.race = 2
        · simp [two]
        · by_cases three : v.race = 3
          · simp [three]
          · have h1 : v.race.toNat ≠ 1 := fun H => one (BitVec.eq_of_toNat_eq H)
            have h2 : v.race.toNat ≠ 2 := fun H => two (BitVec.eq_of_toNat_eq H)
            have h3 : v.race.toNat ≠ 3 := fun H => three (BitVec.eq_of_toNat_eq H)
            have no12 : ¬ (v.race = 1 ∨ v.race = 2) := fun H => H.elim one two
            have no23 : ¬ (v.race.toNat = 2 ∨ v.race.toNat = 3) := fun H => H.elim h2 h3
            rw [if_neg no12, if_neg three, if_neg h1, if_neg no23]
            simp
    · rw [if_neg G, if_neg G]
      simp
  · simp

/-- A waiting side obtained by binding the actual old bytes is an
ADMIT or BIT of this owner, at its literal certified gate. -/
theorem generated_pending_gate {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (w : Word n) (atWord : x = run start w) (k op : Nat)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op (.out k)))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (s : Side) :
    let a := S.getD k fall
    pendingSide (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) = some s →
    ∃ i bit v, a = (i, 1) ∧ oldOrdinal B base hh i = gateOrdinal bit ∧ op = gateOpcode bit ∧
      bind (longGeometry B (x i)) 1 (atSite (x i).long 1) = .forward v ∧
      v.opcode.toNat = gateOpcode bit ∧ v.fault = 0 ∧
      ((v.race = 1 ∧ s = .left) ∨ ∃ t, t ≠ s ∧ v.race = firstCode t) := by
  dsimp only
  let a := S.getD k fall
  intro pending
  obtain ⟨bit, v, read, opcode, fault, gateLive, race⟩ := pending_gate_fields _ _ _ s pending
  have fixed : ∀ i, oldH6 B x i = oldH6 B base i :=
    fun i => (congrArg Prod.fst (cur.1.1 i)).symm
  obtain ⟨slotVal, ord⟩ := (selected_gate_iff hp hh fixed ready a.1 a.2 bit).mp gateLive
  have slot : a.2 = 1 := Fin.ext slotVal
  obtain ⟨raw, atRaw, rawHealthy⟩ := BStarReleaseOrigin.crop_origin_op
    (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) v (gateOpcode bit)
    ⟨fault, opcode⟩ read
  have origin := (BStarOwnerLaunchOrigin.healthy_forward_origin hp C distinct hist
    (atWord ▸ cur) k cur.2.1.1 raw (atWord ▸ atRaw) (gateOpcode bit) rawHealthy.1 rawHealthy.2).1
  have pc : op = gateOpcode bit := by injection origin
  have atGate : a = (a.1, 1) := Prod.ext rfl slot
  have packed : bind (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) = .forward v := read
  rw [slot] at packed
  exact ⟨a.1, bit, v, atGate, ord, pc, packed, opcode, fault, race⟩

/-- Nominate the physical old door/link, or the side still required
by a live ADMIT or BIT. Every phase uses the same fixed owner chart. -/
noncomputable def serialNominee {base : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (x : X) : Mode → Fin n
  | .idle | .busy _ (.back 0) => RearTrace.predecessor (S.getD 0 fall).1
  | .busy _ (.back (k+1)) => chartMark hp C head cont k
  | .busy _ (.out k) =>
    let a := S.getD k fall
    let old := x a.1
    ((pendingSide (longGeometry B old) a.2 (atSite old.long a.2)).map (incident a.1)).getD
      (chartMark hp C head cont k)

/-- A mark missing a parked gate's required opposite side preserves
the actual nomination, including through the next geometry binding. -/
theorem recorded_side_keeps_nomination {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (i e : Fin n) (sep : e ≠ rightNeighbor e)
    (bit : Bool) (k : Nat) (atGate : S.getD k fall = (i, 1))
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (nextReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 (step x e))
    (same : ∀ j, oldH6 B (step x e) j = oldH6 B base j)
    (G : gate (gateOpcode bit) 1 (longGeometry B (x i)) = true)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (v : Payload) (op : v.opcode.toNat = gateOpcode bit) (fault : v.fault = 0)
    (read : bind (longGeometry B (x i)) 1 (atSite (x i).long 1) = .forward v)
    (s : Side) (race : v.race = firstCode s)
    (avoid : ∀ t, BStarAcquireDoorHistory.siteOf e t = i → t = s) :
    pendingSide (longGeometry B (step x e i)) 1 (atSite (step x e i).long 1) =
      pendingSide (longGeometry B (x i)) 1 (atSite (x i).long 1) := by
  have bytes := BStarGateStutter.first_wait_raw hp C i e sep bit k ready atGate G cur
    v read op fault s race avoid
  have token := congrArg decode bytes
  have fixed : ∀ j, oldH6 B x j = oldH6 B base j :=
    fun j => (congrArg Prod.fst (cur.1.1 j)).symm
  have gates (command : Nat) : gate command 1 (longGeometry B (step x e i)) =
      gate command 1 (longGeometry B (x i)) := by
    rw [BStarClearanceOffset.gate_at_ordinal hp _ hh (step x e) same nextReady,
      BStarClearanceOffset.gate_at_ordinal hp _ hh x fixed ready]
  have binding (t : Token) : bind (longGeometry B (step x e i)) 1 t =
      bind (longGeometry B (x i)) 1 t := by
    cases t <;> simp [BStarLongCommand.bind, gates]
  change atSite (step x e i).long 1 = atSite (x i).long 1 at token
  unfold pendingSide
  simp only [token, binding, read, gates]

/-- The fixed reverse label clears the pointed reply's old slot on
the actual mark. No gate or FENCE premise concerns return. -/
theorem physical_reverse_nominee {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (distinct : ∀ e : Fin n, e ≠ rightNeighbor e) (op k : Nat)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.back (k+1)))) :
    project (fun j => S.getD j fall) (step x (chartMark hp C head cont k)) (k+1) = .empty := by
  let addr := fun j => S.getD j fall
  let e := chartMark hp C head cont k
  have bound : k+1 ≤ len := cur.2.1.1
  have lt : k < len := by omega
  let M := BStarSeparatorRing.mark_at hp C e (distinct e) op cur.1 (.back (k+1)) (by simp) cur.2.1
  have label : Label.link k ∈ labels hp x e addr len := by
    simpa only [if_pos lt] using chart_mark_selected hp C head cont k (by omega) cur.1.1
  have link := (mem_link hp x e addr len k).mp label
  exact (M.td k link (cur.2.1.2.2.1 _ (Nat.lt_succ_self k)) cur.2.1.2.1).2

/-- The return cursor's debt never increases on a busy mark. Each
physical reverse move pays two units. -/
theorem physical_return_work {x : X} {addr : Nat → Pos n} {len op k : Nat}
    {e : Fin n} {d : Cursor}
    (ev : Event hp addr len x e (.busy op (.back k)) (.busy op d)) :
    physicalTourWork len 0 (.busy op d) ≤ physicalTourWork len 0 (.busy op (.back k)) ∧
      (d ≠ .back k → physicalTourWork len 0 (.busy op d) + 2 ≤
        physicalTourWork len 0 (.busy op (.back k))) := by
  cases actual_cursor_advance hp ev with
  | stay => exact ⟨Nat.le_refl _, fun H => (H rfl).elim⟩
  | reverse => simp only [physicalTourWork] <;> omega

/-- A generated reply at zero is consumed on the literal incoming
door mark. The next generated mode is idle. -/
theorem incoming_receipt_selected {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (q : Q x) (op : Nat)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.back 0))) :
    let addr := fun j => S.getD j fall
    let e := RearTrace.predecessor (addr 0).1
    Event hp addr len x e (.busy op (.back 0)) .idle ∧
      Current hp base addr len (step x e) .idle := by
  dsimp only
  obtain ⟨d, E, N⟩ := current_step hp C Q fiber closed distinct q
    (RearTrace.predecessor (S.getD 0 fall).1) _ cur
  cases E with
  | transit _ _ _ live _ => exact (live rfl).elim
  | arrived_hold _ ne => exact (ne rfl).elim
  | consume _ eq empty => exact ⟨.consume _ eq empty, N⟩

/-- During actual generated outward service, all labels decrease or
hold the owner's existing forward-coordinate sum. The proved source
hold and chart footprint discharge the premises of indexed service. -/
theorem generated_forward_rank {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (e : Fin n) (sep : e ≠ rightNeighbor e) (op k : Nat)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k))) :
    let cost := fun y => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base y (BStarClearanceIndexedSum.distance S)) S
    cost (step x e) ≤ cost x := by
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  have rootSlot : (addr 0).2 = 0 := (BStarResetChartService.root_header hp C cur.1.1).2
  have R : atSite (x root).long 0 = project addr x 0 := by
    change atSite (x root).long 0 = atSite (x root).long (addr 0).2
    rw [rootSlot]
  have held : Held (x root).long := by
    refine ⟨cur.1.2.1, cur.1.2.2.1, ?_⟩
    rw [R]
    by_cases atDoor : k = 0
    · subst k
      exact .inr cur.2.1.2.1
    · exact .inl (cur.2.1.2.2 0 (Nat.pos_of_ne_zero atDoor))
  have wait := BStarClearanceSource.held_before hp x root e held
  have doorAddress : root = (BStarAcquireLiteralChain.endpoint (oldH6 B base) hh o 0).1 :=
    congrArg Prod.fst C.root
  rw [doorAddress] at wait
  exact (BStarClearanceIndexedWait.pre_service_sum hp C cur.1.1 baseReady ready e sep wait).1

/-- A generated outward state has exactly one forward contribution to
the rank. The addend is the actual bound race at the pointed slot. -/
theorem generated_forward_rank_eq {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (op k : Nat)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k))) :
    let a := S.getD k fall
    let g := longGeometry B (base a.1)
    let t := BStarLongCommand.bind g a.2 (atSite (x a.1).long a.2)
    BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base x (BStarClearanceIndexedSum.distance S)) S =
      4 * (len + 1 - k) + BStarClearanceGate.weight g a.2 t := by
  dsimp only
  let addr := fun j => S.getD j fall
  let a := addr k
  let score := BStarClearanceCommandSum.physicalRank B base x (BStarClearanceIndexedSum.distance S)
  have klen : k < S.length := by have K := cur.2.1.1; have L := C.length; omega
  have ak : a = S[k] := (List.getElem_eq_getD (h := klen) fall).symm
  have am : a ∈ S := ak.symm ▸ List.getElem_mem _
  have reads (b : Pos n) :
      score b = BStarClearanceGate.forwardRank (longGeometry B (base b.1)) b.2
        (BStarClearanceIndexedSum.distance S b)
        (BStarLongCommand.bind (longGeometry B (base b.1)) b.2 (atSite (x b.1).long b.2)) := rfl
  have zeros (b : Pos n) (bm : b ∈ S) (ne : b ≠ a) : score b = 0 := by
    obtain ⟨j, jl, jb⟩ := List.getElem_of_mem bm
    have bj : addr j = b := (List.getElem_eq_getD (h := jl) fall).symm.trans jb
    have jle : j ≤ len := by have L := C.length; omega
    have jk : j ≠ k := fun E => ne (bj.symm.trans (congrArg addr E))
    rcases Nat.lt_or_gt_of_ne jk with L | L
    · have V := cur.2.1.2.2 j L
      change atSite (x (addr j).1).long (addr j).2 = .trail at V
      rw [bj] at V
      rw [reads, V]
      rfl
    · have V := cur.2.2 j L jle
      change atSite (x (addr j).1).long (addr j).2 = .empty at V
      rw [bj] at V
      rw [reads, V]
      rfl
  rw [show BStarClearanceAggregate.total score S = score a from aggregate_one a S score C.nodup am zeros]
  rw [reads, show BStarClearanceIndexedSum.distance S a = len + 1 - k from by
    rw [ak, BStarClearanceIndexedSum.distance_idx C.nodup, C.length]]
  obtain ⟨p, F⟩ := cur.2.1.2.1
  change atSite (x a.1).long a.2 = .forward p at F
  change BStarClearanceGate.forwardRank (longGeometry B (base a.1)) a.2 (len+1-k)
      (bind (longGeometry B (base a.1)) a.2 (atSite (x a.1).long a.2)) = _
  rw [F]
  unfold BStarLongCommand.bind
  dsimp only
  split <;> split <;> first | rfl | (split <;> rfl)

/-- All actual outbound marks weakly lower the weighted tour work.
A cursor move pays two, including the arrival that arms a gate. -/
theorem physical_outbound_work {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (e : Fin n) (sep : e ≠ rightNeighbor e) (op k : Nat) (d : Cursor)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (ev : Event hp (fun j => S.getD j fall) len x e (.busy op (.out k)) (.busy op d))
    (cur' : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op d)) :
    let score := fun y => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base y (BStarClearanceIndexedSum.distance S)) S
    let before := physicalTourWork len (score x) (.busy op (.out k))
    let after := physicalTourWork len (score (step x e)) (.busy op d)
    after ≤ before ∧ (d ≠ .out k → after + 2 ≤ before) := by
  dsimp only
  have motion := actual_cursor_advance hp ev
  cases motion with
  | stay =>
    have weak := generated_forward_rank hp C baseReady ready e sep op k cur
    simp only [physicalTourWork]
    exact ⟨Nat.add_le_add_right weak _, fun H => (H rfl).elim⟩
  | forward =>
    rw [generated_forward_rank_eq hp C op k cur, generated_forward_rank_eq hp C op (k+1) cur']
    have h := cur'.2.1.1
    have w := BStarClearanceGate.bounded
      (longGeometry B (base (S.getD (k+1) fall).1)) (S.getD (k+1) fall).2
      (bind (longGeometry B (base (S.getD (k+1) fall).1)) (S.getD (k+1) fall).2
        (atSite (step x e (S.getD (k+1) fall).1).long (S.getD (k+1) fall).2))
    simp only [physicalTourWork]
    omega
  | turn =>
    rw [generated_forward_rank_eq hp C op len cur]
    simp only [physicalTourWork]
    omega

/-- A literal required-side observation spends one unit of outbound
work even though the pointed command cursor does not move. -/
theorem physical_gate_work {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (qx : Q x) (i : Fin n) (side : Side) (bit : Bool) (k : Nat)
    (atGate : S.getD k fall = (i, 1)) (ord : oldOrdinal B base hh i = gateOrdinal bit)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy (gateOpcode bit) (.out k)))
    (v : Payload) (bits : BitVec 3)
    (read : bind (longGeometry B (x i)) 1 (atSite (x i).long 1) = .forward v)
    (op : v.opcode.toNat = gateOpcode bit) (fault : v.fault = 0)
    (race : (v.race = 1 ∧ bits = firstCode side) ∨
      ∃ old, old ≠ side ∧ v.race = firstCode old ∧ bits = finalCode old) :
    let e := incident i side
    let y := step x e
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    Current hp base (fun j => S.getD j fall) len y (.busy (gateOpcode bit) (.out k)) ∧
      physicalTourWork len (score y) (.busy (gateOpcode bit) (.out k)) + 1 =
        physicalTourWork len (score x) (.busy (gateOpcode bit) (.out k)) := by
  let e := incident i side
  let y := step x e
  have qy : Q y := closed x qx e
  have fixed (z : X) (qz : Q z) : ∀ j, oldH6 B z j = oldH6 B base j :=
    fun j => (congrArg Prod.fst (fiber z qz j)).symm
  have geom (z : X) (qz : Q z) (cmd : Nat) : gate cmd 1 (longGeometry B (base i)) =
      gate cmd 1 (longGeometry B (z i)) := by
    rw [BStarClearanceOffset.gate_at_ordinal hp _ hh base (fun _ => rfl) baseReady,
      BStarClearanceOffset.gate_at_ordinal hp _ hh z (fixed z qz) (ready z qz)]
  have binding (z : X) (qz : Q z) (t : Token) : bind (longGeometry B (base i)) 1 t =
      bind (longGeometry B (z i)) 1 t := by
    cases t <;> simp [BStarLongCommand.bind, geom z qz]
  have onGate : gate (gateOpcode bit) 1 (longGeometry B (x i)) = true :=
    (selected_gate_iff hp hh (fixed x qx) (ready x qx) i 1 bit).mpr ⟨rfl, ord⟩
  have hit : BStarAcquireDoorHistory.siteOf e side = i := by
    cases side with
    | left => rfl
    | right => exact RearTrace.right_predecessor i
  obtain ⟨_, _, cur', bound⟩ := BStarGateStutter.observed_race_step hp C Q fiber closed
    distinct i e bit k qx atGate cur v read op fault (ready _ qx) (ready _ qy) onGate side hit bits race
  have gateRef : gate v.opcode.toNat 1 (longGeometry B (base i)) = true := by
    rw [geom x qx, op]
    exact onGate
  have obs : observe ⟨side, 1⟩ (longGeometry B (base i)) v = some {v with race := bits} := by
    rcases race with ⟨R, rfl⟩ | ⟨old, other, R, rfl⟩
    · exact BStarGateUnmask.observe_first_any _ _ _ gateRef fault R
    · rw [BStarGateUnmask.observe_other_any _ _ _ _ gateRef fault R, if_neg other.symm]
  have paid := BStarClearanceGate.observe_unit _ _ _ _ obs
  dsimp only
  refine ⟨cur', ?_⟩
  rw [generated_forward_rank_eq hp C _ k cur, generated_forward_rank_eq hp C _ k cur', atGate]
  simp only [physicalTourWork]
  have oldBound : bind (longGeometry B (base i)) 1 (atSite (x i).long 1) = .forward v :=
    (binding x qx (atSite (x i).long 1)).trans read
  have newBound : bind (longGeometry B (base i)) 1 (atSite (step x e i).long 1) =
      .forward {v with race := bits} :=
    (binding y qy (atSite (y i).long 1)).trans bound
  let weight := BStarClearanceGate.weight (longGeometry B (base i)) 1
  let oldDebt := weight (bind (longGeometry B (base i)) 1 (atSite (x i).long 1))
  let newDebt := weight (bind (longGeometry B (base i)) 1 (atSite (step x e i).long 1))
  have observation : newDebt + 1 = oldDebt :=
    (congrArg (fun t => weight t + 1) newBound).trans (paid.trans (congrArg weight oldBound).symm)
  change 4*(len+1-k) + newDebt + 2*(len+1) + 1 =
    4*(len+1-k) + oldDebt + 2*(len+1)
  omega

/-- The computed waiting nomination pays on its genuine incident mark.
At FIRST either incidence pays, which includes every same-gate
steering of the nominated candidate. -/
theorem generated_pending_pays {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (qx : Q x) (w : Word n) (atWord : x = run start w) (k op : Nat)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op (.out k)))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (s : Side) :
    let a := S.getD k fall
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    pendingSide (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) = some s →
    ∀ t, (t = s ∨ ∃ v, bind (longGeometry B (x a.1)) a.2
          (atSite (x a.1).long a.2) = .forward v ∧ v.race = 1) →
      let y := step x (incident a.1 t)
      Current hp base (fun j => S.getD j fall) len y (.busy op (.out k)) ∧
        physicalTourWork len (score y) (.busy op (.out k)) + 1 =
          physicalTourWork len (score x) (.busy op (.out k)) := by
  dsimp only
  intro pending t hit
  obtain ⟨i, bit, v, addr, ord, opc, read, opv, fault, race⟩ :=
    generated_pending_gate hp C distinct w atWord k op hist cur (ready x qx) s pending
  subst op
  rw [addr] at hit ⊢
  rcases race with ⟨first, _⟩ | ⟨old, opposite, seen⟩
  · exact physical_gate_work hp C Q fiber closed distinct baseReady ready qx i t bit k
      addr ord cur v _ read opv fault (.inl ⟨first, rfl⟩)
  · have same : t = s := by
      rcases hit with eq | ⟨u, U, first⟩
      · exact eq
      · have eq := Token.forward.inj (read.symm.trans U)
        subst u
        rw [first] at seen
        cases old <;> simp [firstCode] at seen
    subst t
    exact physical_gate_work hp C Q fiber closed distinct baseReady ready qx i s bit k
      addr ord cur v _ read opv fault (.inr ⟨old, opposite, seen, rfl⟩)

/-- A stationary outward step of equal work preserves the exact
computed side. In OTHER, preservation uses the actual old packed
bytes and the fact that every opposite-side incidence spends work. -/
theorem generated_pending_stable {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (qx : Q x) (w : Word n) (atWord : x = run start w) (k op : Nat) (e : Fin n)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op (.out k)))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (cur' : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op (.out k))) :
    let a := S.getD k fall
    let y := step x e
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    physicalTourWork len (score y) (.busy op (.out k)) =
        physicalTourWork len (score x) (.busy op (.out k)) →
      pendingSide (longGeometry B (y a.1)) a.2 (atSite (y a.1).long a.2) =
        pendingSide (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) := by
  dsimp only
  let a := S.getD k fall
  let y := step x e
  have qy : Q y := closed x qx e
  have fixed (z : X) (qz : Q z) : ∀ j, oldH6 B z j = oldH6 B base j :=
    fun j => (congrArg Prod.fst (fiber z qz j)).symm
  have gates (z : X) (qz : Q z) (cmd : Nat) : gate cmd a.2 (longGeometry B (base a.1)) =
      gate cmd a.2 (longGeometry B (z a.1)) := by
    rw [BStarClearanceOffset.gate_at_ordinal hp _ hh base (fun _ => rfl) baseReady,
      BStarClearanceOffset.gate_at_ordinal hp _ hh z (fixed z qz) (ready z qz)]
  have bind_same (z : X) (qz : Q z) (t : Token) : bind (longGeometry B (base a.1)) a.2 t =
      bind (longGeometry B (z a.1)) a.2 t := by
    cases t <;> simp [BStarLongCommand.bind, gates z qz]
  let raceDebt := fun z : X =>
    BStarClearanceGate.weight (longGeometry B (z a.1)) a.2
      (bind (longGeometry B (z a.1)) a.2 (atSite (z a.1).long a.2))
  have weight_same (z : X) (qz : Q z) (t : Token) :
      BStarClearanceGate.weight (longGeometry B (base a.1)) a.2 t =
        BStarClearanceGate.weight (longGeometry B (z a.1)) a.2 t := by
    cases t <;> simp [BStarClearanceGate.weight, gates z qz]
  have referenceDebt (z : X) (qz : Q z) :
      BStarClearanceGate.weight (longGeometry B (base a.1)) a.2
        (bind (longGeometry B (base a.1)) a.2 (atSite (z a.1).long a.2)) = raceDebt z :=
    (congrArg (BStarClearanceGate.weight (longGeometry B (base a.1)) a.2)
      (bind_same z qz (atSite (z a.1).long a.2))).trans (weight_same z qz _)
  have px := pending_weight (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2)
  have py := pending_weight (longGeometry B (y a.1)) a.2 (atSite (y a.1).long a.2)
  intro equal
  have debt : raceDebt y = raceDebt x := by
    rw [generated_forward_rank_eq hp C _ k cur, generated_forward_rank_eq hp C _ k cur'] at equal
    change _ + 2*(len+1) = _ + 2*(len+1) at equal
    have oldDebt := referenceDebt x qx
    have newDebt := referenceDebt (step x e) qy
    simp only [a] at oldDebt newDebt
    simp only [oldDebt, newDebt] at equal
    change 4*(len+1-k) + raceDebt y + 2*(len+1) =
      4*(len+1-k) + raceDebt x + 2*(len+1) at equal
    omega
  cases H : pendingSide (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) with
  | none => exact py.1.mpr (debt.trans (px.1.mp H))
  | some s =>
    obtain ⟨i, bit, v, addr, ord, opc, read, opv, fault, race⟩ :=
      generated_pending_gate hp C distinct w atWord k op hist cur (ready x qx) s H
    have G := (selected_gate_iff hp hh (fixed x qx) (ready x qx) i 1 bit).mpr ⟨rfl, ord⟩
    rcases race with ⟨first, rfl⟩ | ⟨old, diff, seen⟩
    · have oldDebt : raceDebt x = 2 := by
        unfold raceDebt
        have physicalAddr : a = (i, 1) := addr
        rw [physicalAddr, read]
        simp [BStarClearanceGate.weight, opv, fault, G, first, BStarClearanceGate.raceWeight]
      exact py.2 (debt.trans oldDebt)
    · have skip : ∀ t, BStarAcquireDoorHistory.siteOf e t = i → t = old := by
        intro t loc
        apply Classical.byContradiction
        intro other
        have eq : t = s := by
          cases t <;> cases s <;> cases old <;>
            first | rfl | exact (diff rfl).elim | exact (other rfl).elim
        have E : e = incident i t := by
          cases t
          · exact loc
          · exact (RearTrace.predecessor_right e).symm.trans
              (congrArg RearTrace.predecessor loc)
        have pay := (generated_pending_pays hp C Q fiber closed distinct baseReady ready
          qx w atWord k op hist cur s H t (.inl eq)).2
        erw [addr, ← E] at pay
        let work := fun z : X => physicalTourWork len
          (BStarClearanceAggregate.total
            (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S)
          (.busy op (.out k))
        change work (step x e) + 1 = work x at pay
        have tie : work (step x e) = work x := equal
        rw [tie] at pay
        omega
      subst op
      have stays := recorded_side_keeps_nomination hp C i e (distinct e) bit k addr
        (ready x qx) (ready y qy) (fixed y qy) G cur v opv fault read old seen skip
      have physicalAddr : a = (i, 1) := addr
      rw [physicalAddr] at H
      rw [addr]
      exact stays.trans H

/-- Even a redirected occurrence of an owner's own pending side
spends the gate unit. A redirect can only hit this very ADMIT gate,
and its old FIRST state permits either side. -/
theorem pending_candidate_pays {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect) (a w : Word n)
    (physical : ∀ i, fresh a i → firstAdmission hp (base := base) (hh := hh) x i)
    (qx : Q x) (atWord : x = run start w) (k op : Nat)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op (.out k)))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k))) (s : Side) :
    let b := S.getD k fall
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    pendingSide (longGeometry B (x b.1)) b.2 (atSite (x b.1).long b.2) = some s →
    let y := step x (chooseBy redirect a (incident b.1 s))
    Current hp base (fun j => S.getD j fall) len y (.busy op (.out k)) ∧
      physicalTourWork len (score y) (.busy op (.out k)) + 1 =
        physicalTourWork len (score x) (.busy op (.out k)) := by
  dsimp only
  intro pending
  cases H : redirect a (incident (S.getD k fall).1 s) with
  | none =>
    simpa only [chooseBy, H, Option.getD] using
      generated_pending_pays hp C Q fiber closed distinct baseReady ready qx w
        atWord k op hist cur s pending s (.inl rfl)
  | some f =>
    obtain ⟨i, bit, v, addr, ord, opc, read, opv, fault, race⟩ :=
      generated_pending_gate hp C distinct w atWord k op hist cur (ready x qx) s pending
    obtain ⟨j, t, J, freshAt, E, redirected⟩ := mask a (incident (S.getD k fall).1 s) f H
    have pair : incident i s = incident j t := (congrArg (fun d : Pos n =>
      incident d.1 s) addr).symm.trans E
    obtain ⟨same, _, _⟩ :=
      incident_gate_injective (oldH6 B base) hh i j bit false ord J s t pair
    subst j
    obtain ⟨_, _, _, _, _, q, _, _, _, U, _, _, R⟩ := physical i freshAt
    have first : ∃ u, bind (longGeometry B (x (S.getD k fall).1)) (S.getD k fall).2
        (atSite (x (S.getD k fall).1).long (S.getD k fall).2) = .forward u ∧ u.race = 1 := by
      rw [addr]
      exact ⟨q, U, R⟩
    have paid := generated_pending_pays hp C Q fiber closed distinct baseReady ready qx w
      atWord k op hist cur s pending (opposite t) (.inr first)
    rw [addr] at paid
    have emitted : chooseBy redirect a (incident (S.getD k fall).1 s) = f := by
      change (redirect a (incident (S.getD k fall).1 s)).getD _ = f
      rw [H]
      rfl
    rw [emitted, redirected]
    exact paid

end Physical

section Forward

open BStarLongCommandData BStarLongLiteral BStarLongTransport BStarLongEvents BStarLongRouting

/-- A nominated forward claim whose literal gate and FENCE tests pass
does advance in the full old-pair row. A prep conflict may fault the
carried payload, but cannot turn that advance into a wait. -/
theorem enabled_forward_offer (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (v w : Payload) (selectedClaim : C ∈ orderedCommands g)
    (nonDoor : C.kind ≠ .door) (old : bound g (readK x) C.source = .forward v)
    (leaves : depart (geometry g C.source.side) C.source.occurrence v = some w)
    (clear : checkFence g (BStarLongPrep.view x) C.source w ≠ .hold) :
    ∃ p, (C, .advance p) ∈ actualOffers g x := by
  have ready : ∃ p, gatedAt g x C = .advance p := by
    unfold gatedAt classifyOld
    change ∃ p, checkOffer g (BStarLongPrep.view x)
      (C, classify C (geometry g C.source.side) (bound g (readK x) C.source)
        ((C.destination.map (bound g (readK x))).getD .empty)) = .advance p
    rw [old]
    simp only [classify, beq_iff_eq, nonDoor, if_false, leaves, checkOffer]
    cases e : checkFence g (BStarLongPrep.view x) C.source w with
    | advance => exact ⟨w, rfl⟩
    | hold => exact (clear e).elim
    | fault => exact ⟨failedPayload, rfl⟩
  obtain ⟨p, outcome⟩ := ready
  have offered := (gated_mem g x C (.advance p)).mpr ⟨selectedClaim, outcome.symm⟩
  let data := round g x
  have carried : ∃ q, cancel data.faults (C, .advance p) = (C, .advance q) := by
    unfold cancel
    dsimp only
    split <;> exact ⟨_, rfl⟩
  obtain ⟨q, cast⟩ := carried
  have member : (C, .advance q) ∈ data.offered :=
    List.mem_map.mpr ⟨(C, .advance p), offered, cast⟩
  have final : ∃ t, BStarLongGrant.update g x data.offered (C, .advance q) = (C, .advance t) := by
    unfold BStarLongGrant.update
    dsimp only
    split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨t, landed⟩ := final
  exact ⟨t, List.mem_map.mpr ⟨(C, .advance q), member, landed⟩⟩

private theorem terminal_finishes_reply (p : Payload) : anyTag.D (finish p) := by
  unfold finish
  simp only []
  split
  · exact ⟨_, rfl⟩
  · split
    · split <;> exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

/-- A selected actual advance or terminal turn removes the old pointed
forward from its slot on the fully joined mark. In particular a
literal delivery of a ready ordinary nomination changes its cursor. -/
theorem selected_forward_leaves_old {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (sep : e ≠ rightNeighbor e) (C : CommandClaim) (v : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
    C ∈ orderedCommands g → C.kind ≠ .door →
    (C, .advance v) ∈ actualOffers g raw →
    ¬ anyTag.F (BStarAcquireForwardTrace.atCursor (AllSizeS1Geometry.step b x e) (address e C.source)) := by
  dsimp only
  intro claim nonDoor advance
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := oldPair b x e
  let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
  have safe (side : C.source.side = .right) (zero : C.source.occurrence.val = 0) :
      g.2.axes.h6 = false ∨ LongDoorGuard.valid manifest raw.2 = true := by
    cases d : C.destination with
    | none => have H := (BStarAcquireChainEndpoints.terminal g C claim d nonDoor).2.2.2; omega
    | some a => exact ((BStarAcquireReturn.link_shape g C a claim d).2.2 side zero).elim
  rw [← BStarResetRailRing.new_read b x e sep C.source,
    BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e, x (rightNeighbor e)) C.source safe]
  change ¬ anyTag.F (decode (readRaw (patchPair (longWork g raw) raw) C.source))
  cases d : C.destination with
  | none =>
    rw [BStarResetQuiet.terminal_finish g raw C v d advance, decode_encode]
    exact BStarSeparatorParked.disjoint_class _ (terminal_finishes_reply _)
  | some a =>
    have ne := (BStarAcquireReturn.link_shape g C a claim d).1.symm
    rw [(BStarClearanceForward.move_lands g raw C v a d advance ne).1, decode_encode]
    exact BStarSeparatorParked.forward_not_trail

end Forward

section Ordinary

open BStarLongCommandData BStarLongTransport BStarLongEvents

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B

private theorem departure_of_no_pending (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (a : AtK) (v : Payload) (old : bound g (readK raw) a = .forward v)
    (settled : pendingSide (geometry g a.side) a.occurrence (readK raw a) = none) :
    ∃ w, depart (geometry g a.side) a.occurrence v = some w := by
  cases H : depart (geometry g a.side) a.occurrence v with
  | some w => exact ⟨w, rfl⟩
  | none =>
    obtain ⟨live, sound⟩ := BStarClearanceBlockade.race_wait g raw a v old H
    change bind (geometry g a.side) a.occurrence (readK raw a) = .forward v at old
    unfold pendingSide at settled
    rw [old] at settled
    dsimp only at settled
    rw [if_pos live] at settled
    rcases sound with one | two | three
    · have E : v.race = 1 := BitVec.eq_of_toNat_eq one
      simp [E] at settled
    · have E : v.race = 2 := BitVec.eq_of_toNat_eq two
      simp [E] at settled
    · have E : v.race = 3 := BitVec.eq_of_toNat_eq three
      simp [E] at settled

/-- A selected ordinary outbound nominee spends at least two units in
the actual row. The local exclusions concern only a pending race at the
pointed slot or a literal occupied-mobile FENCE on the selected old pair. -/
theorem ordinary_outbound_pays {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (op k : Nat) (d : Cursor)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k))) :
    let a := S.getD k fall
    let e := chartMark hp C head cont k
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    pendingSide (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2) = none →
    (∀ K ∈ orderedCommands g, K.kind ≠ .door → a = address e K.source →
      ∀ v w, bound g (readK raw) K.source = .forward v →
        depart (geometry g K.source.side) K.source.occurrence v = some w →
        checkFence g (BStarLongPrep.view raw) K.source w ≠ .hold) →
    Event hp (fun j => S.getD j fall) len x e (.busy op (.out k)) (.busy op d) →
    Current hp base (fun j => S.getD j fall) len (step x e) (.busy op d) →
    physicalTourWork len (score (step x e)) (.busy op d) + 2 ≤
      physicalTourWork len (score x) (.busy op (.out k)) := by
  dsimp only
  intro settled clear ev cur'
  let a := S.getD k fall
  let e := chartMark hp C head cont k
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
  obtain ⟨K, member, notDoor, atSource⟩ :=
    chart_mark_outbound hp C head cont k cur.2.1.1 cur.1.1
  have read : readK raw K.source = atSite (x a.1).long a.2 :=
    (BStarResetRailRing.old_read x e K.source).trans
      (congrArg (BStarAcquireForwardTrace.atCursor x) atSource.symm)
  have geom : geometry g K.source.side = longGeometry B (x a.1) := calc
    _ = longGeometry B (x (address e K.source).1) := by
      cases H : K.source.side <;> simp [g, oldPair, geometry, site, H]
    _ = _ := congrArg (fun z : Pos n => longGeometry B (x z.1)) atSource.symm
  have slot : K.source.occurrence = a.2 := congrArg Prod.snd atSource.symm
  obtain ⟨v, front⟩ := cur.2.1.2.1
  change atSite (x a.1).long a.2 = .forward v at front
  have typed : anyTag.F (bound g (readK raw) K.source) := by
    unfold bound
    rw [read, front]
    exact bound_F _ _ v
  obtain ⟨boundPayload, old⟩ := typed
  have noRace : pendingSide (geometry g K.source.side) K.source.occurrence
      (readK raw K.source) = none := by
    simpa only [read, geom, slot] using settled
  obtain ⟨w, leaves⟩ := departure_of_no_pending g raw K.source boundPayload old noRace
  obtain ⟨u, offer⟩ := enabled_forward_offer g raw K boundPayload w member notDoor old leaves
    (clear K member notDoor atSource _ _ old leaves)
  have motion : d ≠ .out k := by
    intro eq
    subst d
    apply selected_forward_leaves_old hp x e (distinct e) K u member notDoor offer
    rw [← atSource]
    exact cur'.2.1.2.1
  exact (physical_outbound_work hp C baseReady ready e (distinct e) op k d cur ev cur').2 motion

set_option maxRecDepth 2048 in
/-- Outbound serial service on the actual word. The selected raw
letter pays one at a pending gate or two at a regular offer. On every
letter the debt is weak and a tie preserves the computed nominee. -/
theorem outbound_serial_mark {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (qx : Q x) (w : Word n) (atWord : x = BStarResetSchedule.run step start w)
    (k op : Nat) (e : Fin n) (d : Cursor)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op (.out k)))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (ev : Event hp (fun j => S.getD j fall) len x e (.busy op (.out k)) (.busy op d))
    (cur' : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op d)) :
    let a := S.getD k fall
    let nominal := chartMark hp C head cont k
    let g := oldPair B x nominal
    let raw : Pair (BitVec LW) := ((x nominal).long, (x (rightNeighbor nominal)).long)
    let side := pendingSide (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2)
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    let before := physicalTourWork len (score x) (.busy op (.out k))
    let after := physicalTourWork len (score (step x e)) (.busy op d)
    after ≤ before ∧
      (after = before →
        serialNominee hp C head cont (step x e) (.busy op d) =
          serialNominee hp C head cont x (.busy op (.out k)) ∧
        oldWaiting B (fun j => S.getD j fall) (step x e) (.busy op d) = side.isSome) ∧
      ((∀ K ∈ orderedCommands g, K.kind ≠ .door → a = address nominal K.source →
        ∀ v w, bound g (readK raw) K.source = .forward v →
          depart (geometry g K.source.side) K.source.occurrence v = some w →
          checkFence g (BStarLongPrep.view raw) K.source w ≠ .hold) →
        e = serialNominee hp C head cont x (.busy op (.out k)) →
        after + (if side.isSome then 1 else 2) ≤ before) := by
  dsimp only
  let y := step x e
  let score := fun z => BStarClearanceAggregate.total
    (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
  let before := physicalTourWork len (score x) (.busy op (.out k))
  let after := physicalTourWork len (score y) (.busy op d)
  have flow := physical_outbound_work hp C baseReady (ready x qx) e (distinct e) op k d cur ev cur'
  refine ⟨flow.1, ?_, ?_⟩
  · intro equal
    have still : d = .out k := by
      apply Classical.byContradiction
      intro away
      have paid : after + 2 ≤ before := flow.2 away
      change after = before at equal
      omega
    subst d
    have side := generated_pending_stable hp C Q fiber closed distinct baseReady ready
      qx w atWord k op e hist cur cur' equal
    simp only [serialNominee, oldWaiting, side] <;> trivial
  · intro clear selected
    unfold serialNominee at selected
    dsimp only at selected
    cases H : pendingSide (longGeometry B (x (S.getD k fall).1)) (S.getD k fall).2
        (atSite (x (S.getD k fall).1).long (S.getD k fall).2) with
    | none =>
      have E : e = chartMark hp C head cont k := by simpa only [H, Option.map_none, Option.getD] using selected
      clear selected
      subst e
      simp only [Option.isSome_none, Bool.false_eq_true, if_false]
      exact ordinary_outbound_pays hp C head cont distinct baseReady (ready x qx)
        op k d cur H clear ev cur'
    | some s =>
      have E : e = incident (S.getD k fall).1 s := by simpa only [H, Option.map_some, Option.getD] using selected
      clear selected
      subst e
      have paid := generated_pending_pays hp C Q fiber closed distinct baseReady ready
        qx w atWord k op hist cur s H s (.inl rfl)
      have mode := current_mode_unique hp _ _ cur' paid.1
      have eq : d = .out k := by injection mode
      subst d
      simp only [Option.isSome_some, if_true]
      exact Nat.le_of_eq paid.2

end Ordinary

section HealthyReset

open BStarLongCommandData BStarLongTransport BStarLongEvents BStarLongRouting
open BStarResetQuiet BStarResetQuietTable BStarResetIdleRing BStarAcquireAnchors
open BStarResetTaggedRows BStarResetHealthyService BStarOwnerLaunchOrigin
open BStarResetChartService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "run" => BStarResetSchedule.run step

/-- A returned reset reply keeps its exact decoded value on all
letters other than the source receipt. The outgoing contact at the
source selects a DE hold, including its normalization and K0 write. -/
theorem returned_reset_holds {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (e : Fin n) (sep : e ≠ rightNeighbor e)
    (op : Nat) (small : op < 3)
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.back 0)))
    (away : e ≠ RearTrace.predecessor (S.getD 0 fall).1)
    (healthy : (healthyTag op).D (project (fun j => S.getD j fall) x 0)) :
    (healthyTag op).D (project (fun j => S.getD j fall) (step x e) 0) := by
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
  have H := cur.1.1
  have right : root ≠ rightNeighbor e := fun r => away
    ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor r.symm))
  by_cases left : root = e
  · have hit : addr 0 = address e (L 0) := Prod.ext left (root_header hp C H).2
    have read (j : Nat) (a : AtK) (atJ : addr j = address e a) :
        readK raw a = project addr x j :=
      (BStarResetRailRing.old_read x e a).trans
        (congrArg (BStarAcquireForwardTrace.atCursor x) atJ).symm
    have mid : avoids (L 0) (middle g raw) := by
      apply middle_avoids_of_chart
      intro v hv ha
      have selected : v.1 ∈ orderedCommands g := by
        rw [← actualOffers_claims g raw]
        exact List.mem_map.mpr ⟨v, hv, rfl⟩
      rcases touches hp C H e 0 (Nat.zero_le _) v.1 (L 0) selected ha hit with D|T|F|⟨j, U, _⟩
      · cases D.2.2
      · obtain ⟨eq, K, _, _, _, terminal, atTerm⟩ := T
        have value := congrArg (fun z : Pos n => z.2.val) (hit.symm.trans (eq ▸ atTerm))
        exact (by change 0 = K.source.occurrence.val at value; omega : False).elim
      · obtain ⟨lim, K, dst, member, link, source, dest⟩ := F
        have same := address_inj e sep (hit.symm.trans source)
        obtain ⟨p, oldReply⟩ := cur.2.1.2.1
        have D : readK raw K.source = .reply p := (read 0 K.source source).trans oldReply
        have E : readK raw dst = .empty :=
          (read 1 dst dest).trans (cur.2.1.2.2.2 1 (by decide) (by omega))
        have idle : LinkHold (bound g (readK raw) K.source) (bound g (readK raw) dst) := by
          unfold bound
          rw [D, E]
          obtain ⟨q, Q⟩ := bound_D (geometry g K.source.side) K.source.occurrence p
          rw [Q]
          exact .de q
        have rule := link_avoids g raw K dst member
          (BStarAcquireReturn.link_shape g K dst member link).2.1 link idle
        exact fun u hu E => rule.1 u (List.mem_flatMap.mpr ⟨v, hv, hu⟩) (E.trans same)
      · omega
    have tagged : ResetLive (readK raw (L 0)) := by
      rw [read 0 (L 0) hit]
      change project addr x 0 = finish (resetPayload op) at healthy
      rw [healthy]
      exact .d _ (BStarResetNoFault.healthy op (by omega))
    have frame := idle_at hp x e sep (L 0) (.inr tagged)
      (not_discarded hp C H e 0 (Nat.zero_le _) _ hit) mid (safe_nonright _ _ _ (by decide))
    change project addr (step x e) 0 = finish (resetPayload op)
    unfold project
    rw [hit]
    exact frame.trans ((read 0 (L 0) hit).trans healthy)
  · change project addr (step x e) 0 = finish (resetPayload op)
    exact (idle_off_pair hp x e (addr 0) left right).trans healthy

private theorem tagged_cursor_unique {len : Nat} {u : BStarSeparatingRail.Rail}
    (a b : Cursor) (A : Good anyTag len u a) (D : Good anyTag len u b) : a = b := by
  cases a with
  | out j =>
    cases b with
    | out k =>
      rcases Nat.lt_trichotomy j k with L | rfl | L
      · obtain ⟨v, F⟩ := A.2.1
        rw [D.2.2 j L] at F
        contradiction
      · rfl
      · obtain ⟨v, F⟩ := D.2.1
        rw [A.2.2 k L] at F
        contradiction
    | back k => exact (BStarOwnerControlHistory.pointed_backward_no_forward u len k D j A.1 A.2.1).elim
  | back j =>
    cases b with
    | out k => exact (BStarOwnerControlHistory.pointed_backward_no_forward u len j A k D.1 D.2.1).elim
    | back k =>
      rcases Nat.lt_trichotomy j k with L | rfl | L
      · obtain ⟨v, R⟩ := A.2.1
        rw [D.2.2.1 j L] at R
        contradiction
      · rfl
      · obtain ⟨v, R⟩ := D.2.1
        rw [A.2.2.1 k L] at R
        contradiction

private theorem weaken_healthy {op len : Nat} {u : BStarSeparatingRail.Rail}
    (d : Cursor) (D : Good (healthyTag op) len u d) : Good anyTag len u d := by
  cases d with
  | out k => exact ⟨D.1, ⟨_, D.2.1⟩, D.2.2⟩
  | back k =>
    have reset : anyTag.D (u k) := by
      have tag := D.2.1
      change u k = finish (resetPayload op) at tag
      rw [tag]
      exact terminal_finishes_reply _
    exact ⟨D.1, reset, D.2.2⟩

private theorem busy_reset_healthy {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    {w : Word n} {z z' : Cursor} {op : Nat} (small : op < 3)
    (hist : BusyOnly hp base (fun j => S.getD j fall) len op x z w z')
    (old : Good (healthyTag op) len (project (fun j => S.getD j fall) x) z) :
    Good (healthyTag op) len (project (fun j => S.getD j fall) (run x w)) z' := by
  induction hist with
  | nil _ => exact old
  | @cons x z d last e w cur event tail ih =>
    have cur' := busy_start hp tail
    by_cases arrived : z = .back 0
    · subst z
      cases event with
      | transit _ _ _ live _ => exact (live rfl).elim
      | arrived_hold _ away =>
        exact ih ⟨Nat.zero_le _, returned_reset_holds hp C e (distinct e) op small
          cur away old.2.1, cur'.2.1.2.2⟩
    · let service := healthyService hp C cur.1.1 e (distinct e) op small z arrived
        old cur.1.2.1 cur.1.2.2.1
      obtain ⟨d', _, H⟩ := BStarSeparatingRail.lift_mark service.mark z arrived old
      have E := tagged_cursor_unique d' d (weaken_healthy d' H) cur'.2.1
      exact ih (E ▸ H)

/-- Any recovered generated reset in flight has the true reset tag.
This includes a reply that reached K0 before the query and then
waited across outgoing-root contacts. -/
theorem generated_reset_healthy {base start : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    {w : Word n} {z : Cursor} {op : Nat} (small : op < 3)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op z)) :
    Good (healthyTag op) len (project (fun j => S.getD j fall) (run start w)) z := by
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  obtain ⟨pre, post, e, split, own, launch, pc, busy⟩ := from_idle hp hist
  let x := run start pre
  let y := step x e
  have word : run start w = run y post := by
    rw [split, BStarResetSchedule.run_append]
    rfl
  obtain ⟨_, arg, named, snap⟩ := launch
  have expected := BStarResetDoor.reset_initial (x root).long op small
  change initial (ctrlOp.read (x root).long).toNat (x root).long = some arg at named
  change (ctrlOp.read (x root).long).toNat = op at pc
  rw [pc, expected] at named
  have arg0 := (Option.some.inj named).symm
  subst arg
  have addr0 := (root_header hp C (busy_start hp busy).1.1).2
  have token : (healthyTag op).F (project addr y 0) := by
    change atSite (y root).long (addr 0).2 = .forward (resetPayload op)
    rw [addr0]
    have raw := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) snap
    change atSite (y root).long 0 = forward (ctrlOp.read (x root).long).toNat 0 at raw
    rw [raw, pc]
    rfl
  rw [word]
  exact busy_reset_healthy hp C distinct small busy
    ⟨Nat.zero_le _, token, fun _ H => (Nat.not_lt_zero _ H).elim⟩

/-- The actual source accept of a reached reset is the healthy
literal 0→1, 1→2, or 2→3 transition. -/
theorem generated_reset_receipt {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    {w : Word n} (atWord : x = run start w) (op : Nat) (small : op < 3) (e : Fin n)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w (.busy op (.back 0)))
    (cur : Current hp base (fun j => S.getD j fall) len x (.busy op (.back 0)))
    (event : Event hp (fun j => S.getD j fall) len x e (.busy op (.back 0)) .idle) :
    (ctrlOp.read (step x e (S.getD 0 fall).1).long).toNat = op + 1 := by
  have own : e = RearTrace.predecessor (S.getD 0 fall).1 := by
    cases event with | consume _ E _ => exact E
  subst e
  have rail : Good (healthyTag op) len (project (fun j => S.getD j fall) x) (.back 0) :=
    atWord.symm ▸ generated_reset_healthy hp C distinct small hist
  have clean : Clean (project (fun j => S.getD j fall)) (BStarResetRailRing.resetTag op) len x :=
    ⟨weakD op _ rail.2.1, rail.2.2.2⟩
  have next := (BStarResetConsumedClean.consumed_clean hp C op small cur.1 clean distinct).2.2 rail.2.1
  have value : (BitVec.ofNat 9 (op+1)).toNat = op+1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  exact (congrArg BitVec.toNat next).trans value

end HealthyReset

section Debt

/-- An owner stops on the next acceptance of release. Opcodes from
PACE through DUMMY carry a reserve for all three release commands. -/
def toursThroughRelease (pc : Nat) : Nat :=
  if pc < 3 then 3 - pc else 416 - pc

theorem tours_through_release_bound (pc : Nat) (legal : pc < 413) :
    0 < toursThroughRelease pc ∧ toursThroughRelease pc ≤ 413 := by
  unfold toursThroughRelease
  split <;> omega

theorem tours_through_release_advance {pc next : Nat} (legal : pc < 413)
    (advance : (pc < 2 ∧ next = pc + 1) ∨
      (3 ≤ pc ∧ (next = 0 ∨ pc < next))) :
    toursThroughRelease next < toursThroughRelease pc := by
  unfold toursThroughRelease
  split <;> split <;> omega

/-- Remaining physical work through the first strict RREL receipt.
The event latch is sticky and sets the debt to zero at that receipt. -/
def releasedCycleWork (len pc forwardScore : Nat) (mode : Mode) (released : Bool) : Nat :=
  if released then 0 else
    (toursThroughRelease pc - 1) * (6 * (len + 1) + 10) +
      physicalTourWork len forwardScore mode

private theorem released_work_positive (len pc score : Nat) (m : Mode) :
    0 < releasedCycleWork len pc score m false := by
  simp only [releasedCycleWork, Bool.false_eq_true, if_false]
  cases m with
  | idle => simp only [physicalTourWork]; omega
  | busy op z => cases z <;> simp only [physicalTourWork] <;> omega

theorem released_cycle_budget (len pc score : Nat) (mode : Mode) (legal : pc < 413)
    (front : score ≤ 4 * (len + 1) + 2)
    (inside : ∀ k op, mode = .busy op (.back k) → k ≤ len) :
    releasedCycleWork len pc score mode false ≤ 420 * (6 * (len + 1) + 10) := by
  have work : physicalTourWork len score mode ≤ 6 * (len + 1) + 10 := by
    cases mode with
    | idle => simp only [physicalTourWork]; omega
    | busy op d =>
      cases d with
      | out k => simp only [physicalTourWork]; omega
      | back k =>
        have bound := inside k op rfl
        simp only [physicalTourWork]
        omega
  have tours := (tours_through_release_bound pc legal).2
  have reserve : toursThroughRelease pc - 1 ≤ 419 := by omega
  simp only [releasedCycleWork, Bool.false_eq_true, if_false]
  calc
    _ ≤ 419 * (6 * (len + 1) + 10) + (6 * (len + 1) + 10) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ reserve) work
    _ = 420 * (6 * (len + 1) + 10) := by omega

/-- A successful receipt which changes program grade pays even when
it enters a new clean ISSUE with the full per-tour reserve. -/
theorem released_cycle_receipt_pays (len pc next score score' : Nat)
    (within : pc < 413) (after : next < 413)
    (advance : (pc < 2 ∧ next = pc + 1) ∨ (3 ≤ pc ∧ (next = 0 ∨ pc < next))) :
    releasedCycleWork len next score' .idle false + 2 ≤
      releasedCycleWork len pc score (.busy pc (.back 0)) false := by
  have decrease := tours_through_release_advance within advance
  have positive := (tours_through_release_bound next after).1
  have grade : (toursThroughRelease next - 1) + 1 ≤ toursThroughRelease pc - 1 := by omega
  have paid := Nat.mul_le_mul_right (6 * (len + 1) + 10) grade
  rw [Nat.add_mul, Nat.one_mul] at paid
  simp only [releasedCycleWork, physicalTourWork, Bool.false_eq_true, if_false]
  omega

/-- The actual acceptance stopping the cycle pays both units of the
prepaid back-zero receipt even when it is the next mark after query. -/
theorem released_cycle_rrel_pays (len score score' : Nat) :
    releasedCycleWork len 3 score' .idle true + 2 ≤
      releasedCycleWork len 2 score (.busy 2 (.back 0)) false := by
  simp [releasedCycleWork, physicalTourWork, toursThroughRelease]

/-- A bad nonreset ISSUE consumes its old program grade and takes the
literal restart at zero in the same source row. -/
theorem released_cycle_bad_issue_pays (len pc score score' : Nat) (reset : 3 ≤ pc)
    (legal : pc < 413) :
    releasedCycleWork len 0 score' .idle false + 2 ≤
      releasedCycleWork len pc score .idle false := by
  have grade : (toursThroughRelease 0 - 1) + 1 ≤ toursThroughRelease pc - 1 := by
    rw [show toursThroughRelease 0 = 3 by decide, toursThroughRelease,
      if_neg (show ¬ pc < 3 by omega)]
    omega
  have paid := Nat.mul_le_mul_right (6 * (len + 1) + 10) grade
  rw [Nat.add_mul, Nat.one_mul] at paid
  simp only [releasedCycleWork, physicalTourWork, Bool.false_eq_true, if_false]
  omega

/-- Rewrite the retry bit only when a raw service pays the current debt
or a candidate first tries the same pending nomination. -/
def retryAfter {n : Nat} (work work' : Nat) (pending : Bool)
    (nominee candidate : Fin n) : Bool :=
  if work' < work then false else pending || candidate == nominee

/-- The literal old-pair forward rank already pays two on a hop. Its
one-unit races require no retry credit. This version preserves the
larger payment on a replay while allowing single-unit ordinary work. -/
theorem weighted_candidate_serial_drift {n : Nat} (nominee : Fin n) (work : Nat)
    (pending : Bool) (newWork : Fin n → Nat) (emitted : Fin n → Fin n)
    (live : 0 < work) (weak : ∀ e, newWork e ≤ work)
    (delivery : emitted nominee = nominee → newWork nominee + 1 + pending.toNat ≤ work)
    (unparked : pending = true → emitted nominee = nominee) :
    let now := work - pending.toNat
    let next := fun e => newWork e - (retryAfter work (newWork e) pending nominee e).toNat
    (∀ e, next e ≤ now) ∧ (∃ e, next e + 1 ≤ now) := by
  dsimp only
  constructor
  · intro e
    by_cases h : newWork e < work
    · cases pending <;> simp [retryAfter, h, Bool.toNat] <;> omega
    · have eq : newWork e = work := Nat.le_antisymm (weak e) (Nat.le_of_not_gt h)
      cases pending <;> cases test : (e == nominee) <;>
        simp [retryAfter, eq, test, Bool.toNat] <;> omega
  · refine ⟨nominee, ?_⟩
    cases pending with
    | false =>
      by_cases h : newWork nominee < work
      · simp [retryAfter, h, Bool.toNat] <;> omega
      · have eq : newWork nominee = work := Nat.le_antisymm (weak nominee) (Nat.le_of_not_gt h)
        simp [retryAfter, eq, Bool.toNat] <;> omega
    | true =>
      have paid : newWork nominee + 2 ≤ work := delivery (unparked rfl)
      have h : newWork nominee < work := by omega
      rw [show retryAfter work (newWork nominee) true nominee nominee = false from if_pos h]
      change newWork nominee + 1 ≤ work - 1
      omega

theorem serial_and_fence_budget {n W L H : Nat} (positive : 0 < W)
    (link : L ≤ 11 * W) (chain : H ≤ 2 * W) :
    n * (420 * (6 * L + 10) + 128 * H) ≤ 2^15 * n * W := by
  rw [Nat.mul_comm (2^15) n, Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  omega

end Debt

section Cycle

open BStarLongCommandData BStarLongTransport BStarLongEvents BStarResetChartService
open BStarAcquireWaitControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "run" => BStarResetSchedule.run step

/-- Only a physical back-zero to idle event for opcode 2 closes the
released-cycle latch. The generated event type makes this a receipt. -/
def releaseEvent (m d : Mode) : Bool :=
  match d with
  | .busy _ _ => false
  | .idle =>
    match m with
    | .busy op (.back 0) => op == 2
    | _ => false

/-- No occupied owned FENCE lane at the selected next ordinary offer.
This proposition exposes the old-pair test used on exit from the
comparison phase. The all-letter weak inequality also holds while this
test fails. -/
def nominatedFenceClear {base : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (x : X) : Mode → Prop
  | .busy _ (.out k) =>
    let a := S.getD k fall
    let e := chartMark hp C head cont k
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
    ∀ K ∈ orderedCommands g, K.kind ≠ .door → a = address e K.source →
      ∀ v w, bound g (readK raw) K.source = .forward v →
        depart (geometry g K.source.side) K.source.occurrence v = some w →
        checkFence g (BStarLongPrep.view raw) K.source w ≠ .hold
  | _ => True

private theorem legal_current {base x : X} {addr : Nat → Pos n} {len : Nat}
    (m : Mode) (cur : Current hp base addr len x m) :
    (ctrlOp.read (x (addr 0).1).long).toNat < 413 := by
  cases m with
  | idle => exact BStarClearanceResidual.issue_range cur.1
  | busy op z =>
    have valid := cur.1.2.1
    unfold LongDoorGuard.valid at valid
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2

private def RawStepDrift {n : Nat} (len oldPC newPC oldScore newScore : Nat)
    (m d : Mode) (e nominee nextNominee : Fin n)
    (waiting nextWaiting : Bool) (clear : Prop) : Prop :=
  let before := releasedCycleWork len oldPC oldScore m false
  let after := releasedCycleWork len newPC newScore d (releaseEvent m d)
  after ≤ before ∧
    (after = before → nextNominee = nominee ∧ nextWaiting = waiting) ∧
    (clear → e = nominee → after + (if waiting then 1 else 2) ≤ before)

private theorem raw_step_pays_two {n : Nat} {len oldPC newPC oldScore newScore : Nat}
    {m d : Mode} {e nominee nextNominee : Fin n}
    {waiting nextWaiting : Bool} {clear : Prop}
    (paid : releasedCycleWork len newPC newScore d (releaseEvent m d) + 2 ≤
      releasedCycleWork len oldPC oldScore m false) :
    RawStepDrift len oldPC newPC oldScore newScore m d e nominee nextNominee waiting nextWaiting clear := by
  let before := releasedCycleWork len oldPC oldScore m false
  let after := releasedCycleWork len newPC newScore d (releaseEvent m d)
  change after + 2 ≤ before at paid
  have strict : after < before := by omega
  change after ≤ before ∧ (after = before → _) ∧ (clear → e = nominee → _)
  refine ⟨Nat.le_of_lt strict, fun tie => (Nat.ne_of_lt strict tie).elim, fun _ _ => ?_⟩
  cases waiting <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

private theorem issue_work_pays (len pc oldScore newScore op : Nat)
    (cap : newScore ≤ 4 * (len+1) + 2) :
    releasedCycleWork len pc newScore (.busy op (.out 0)) false + 2 ≤
      releasedCycleWork len pc oldScore .idle false := by
  simp only [releasedCycleWork, physicalTourWork, Bool.false_eq_true, if_false]
  omega

private theorem receipt_latch_false (op : Nat) (notRelease : op ≠ 2) :
    releaseEvent (.busy op (.back 0)) .idle = false := by
  simp [releaseEvent, notRelease]

set_option maxHeartbeats 4800000 in
/-- Raw next-letter serial drift through the next real release.
The chosen nominee is physical in every mode and every raw tie keeps
it. Transit, foreign marks, launch, rejection and receipt are the
actual indexed full-row events. -/
theorem released_cycle_raw_mark {base start x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (qx : Q x) (w : Word n) (atWord : x = run start w)
    (m d : Mode) (e : Fin n)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len start .idle w m)
    (cur : Current hp base (fun j => S.getD j fall) len x m)
    (event : Event hp (fun j => S.getD j fall) len x e m d)
    (cur' : Current hp base (fun j => S.getD j fall) len (step x e) d) :
    let addr := fun j => S.getD j fall
    let root := (addr 0).1
    let pc := fun z : X => (ctrlOp.read (z root).long).toNat
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    let before := releasedCycleWork len (pc x) (score x) m false
    let after := releasedCycleWork len (pc (step x e)) (score (step x e)) d (releaseEvent m d)
    let nominee := serialNominee hp C head cont x m
    after ≤ before ∧
      (after = before → serialNominee hp C head cont (step x e) d = nominee ∧
        oldWaiting B addr (step x e) d = oldWaiting B addr x m) ∧
      (nominatedFenceClear hp C head cont x m → e = nominee →
        after + (if oldWaiting B addr x m then 1 else 2) ≤ before) := by
  dsimp only
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let y := step x e
  let pc := fun z : X => (ctrlOp.read (z root).long).toNat
  let score := fun z => BStarClearanceAggregate.total
    (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
  change RawStepDrift len (pc x) (pc y) (score x) (score y) m d e
    (serialNominee hp C head cont x m) (serialNominee hp C head cont y d)
    (oldWaiting B addr x m) (oldWaiting B addr y d) (nominatedFenceClear hp C head cont x m)
  have marked := fiber x qx
  have header := root_header hp C marked
  have legal := legal_current hp m cur
  have legal' := legal_current hp d cur'
  cases event with
  | idle_hold away =>
    have same := congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat)
      (BStarOwnerControlHistory.idle_nonown hp C marked cur.2 e (distinct e) away).2
    change pc y = pc x at same
    rw [same]
    unfold RawStepDrift
    exact ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩, fun _ hit => (away hit).elim⟩
  | bad_issue own bad =>
    have writes := BStarOwnerControlHistory.idle_launch_or_hold hp C marked cur.2 distinct e cur.1
    rcases writes with A | R | G
    · exact (A.1 own).elim
    · have reset := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) R.2.2.1
      change pc y = 0 at reset
      have high : 3 ≤ pc x := by
        apply Nat.le_of_not_gt
        intro H
        have good := BStarResetDoor.reset_initial (x root).long (pc x) (by omega)
        have impossible : some 0 = (none : Option Nat) := good.symm.trans bad
        cases impossible
      rw [reset]
      exact raw_step_pays_two (released_cycle_bad_issue_pays len (pc x) (score x) (score y) high legal)
    · obtain ⟨_, _, good, _⟩ := G.2.1
      have impossible := good.symm.trans bad
      cases impossible
  | launch own launch =>
    have same : pc y = pc x := cur'.1.2.2.2
    let weight := BStarClearanceGate.weight (longGeometry B (base root)) (addr 0).2
      (bind (longGeometry B (base root)) (addr 0).2 (atSite (y root).long (addr 0).2))
    have bounded : weight ≤ 2 := BStarClearanceGate.bounded _ _ _
    have boundary : score y = 4*(len+1)+weight :=
      generated_forward_rank_eq hp C _ 0 cur'
    have cap : score y ≤ 4*(len+1)+2 := by rw [boundary]; exact Nat.add_le_add_left bounded _
    rw [same]
    exact raw_step_pays_two (issue_work_pays len (pc x) (score x) (score y) _ cap)
  | arrived_hold op away =>
    have same : pc y = pc x := cur'.1.2.2.2.trans cur.1.2.2.2.symm
    rw [same]
    unfold RawStepDrift
    exact ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩, fun _ hit => (away hit).elim⟩
  | @transit op z d live seen =>
    have same : pc y = pc x := cur'.1.2.2.2.trans cur.1.2.2.2.symm
    rw [same]
    unfold RawStepDrift
    have ev : Event hp addr len x e (.busy op z) (.busy op d) :=
      .transit op z d live seen
    cases z with
    | out k =>
      have work := outbound_serial_mark hp C head cont Q fiber closed distinct baseReady ready
        qx w atWord k op e d hist cur ev cur'
      simp only [releaseEvent, releasedCycleWork, Bool.false_eq_true, if_false]
      refine ⟨Nat.add_le_add_left work.1 _, ?_, ?_⟩
      · intro E
        exact work.2.1 (Nat.add_left_cancel E)
      · intro clear selected
        have pay := work.2.2 clear selected
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left pay _
    | back k =>
      cases k with
      | zero => exact (live rfl).elim
      | succ k =>
        have move := actual_cursor_advance hp ev
        cases move with
        | stay =>
          refine ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩, ?_⟩
          intro _ hit
          change e = chartMark hp C head cont k at hit
          subst e
          have clear := physical_reverse_nominee hp C head cont distinct op k cur
          obtain ⟨p, P⟩ := cur'.2.1.2.1
          rw [clear] at P
          contradiction
        | reverse =>
          simp only [releaseEvent, releasedCycleWork, physicalTourWork, oldWaiting,
            Bool.false_eq_true, if_false]
          exact ⟨by omega, fun E => by omega, fun _ _ => by omega⟩
  | consume op own cleared =>
    have evt : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op own cleared
    have old : pc x = op := cur.1.2.2.2
    rw [old]
    by_cases reset : op < 3
    · have next := generated_reset_receipt hp C distinct atWord op reset e hist cur evt
      change pc y = op + 1 at next
      rw [next]
      by_cases stopped : op = 2
      · rw [stopped]
        exact raw_step_pays_two (released_cycle_rrel_pays len (score x) (score y))
      · have opSmall : op < 2 := by omega
        apply raw_step_pays_two
        rw [receipt_latch_false op stopped]
        have pay := released_cycle_receipt_pays len op (op+1) (score x) (score y)
          (by omega) (by omega) (.inl ⟨opSmall, rfl⟩)
        exact pay
    · have next := physical_receipt_program_order hp (base:=base) (x:=x) (addr:=addr)
        (len:=len) (op:=op) (e:=e) header.2 header.1 (distinct e) cur evt
      change pc y = 0 ∨ pc x < pc y at next
      have high : 3 ≤ op := Nat.le_of_not_gt reset
      have ne : op ≠ 2 := fun eq => (by decide : ¬ 3≤2) (eq ▸ high)
      have within : op < 413 := old ▸ legal
      have after : pc y < 413 := legal'
      have advance : pc y = 0 ∨ op < pc y := old ▸ next
      apply raw_step_pays_two
      rw [receipt_latch_false op ne]
      exact released_cycle_receipt_pays len op (pc y) (score x) (score y)
        within after (.inr ⟨high, advance⟩)

end Cycle

section Candidate

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "run" => BStarResetSchedule.run step

/-- Lift an actual physical nomination to the predictable steered
candidate step. The returned invariant stores a proof of the exact
diversion word whenever a retry is pending. -/
theorem compensated_physical_step
    {base : X} {hh : ∃ i, oldH6 B base i = true}
    (start : X) {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (physical : ∀ a i, fresh a i → firstAdmission hp (base := base) (hh := hh) (run start a) i)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e))
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (work : Word n → Nat) (nominate : Word n → Fin n) (a : Word n) (pending : Bool)
    (q : Q (run start a)) (live : 0 < work a)
    (waited : pending = true → divertedNomination hp start redirect Q a (nominate a))
    (weak : ∀ e, work (a ++ [e]) ≤ work a)
    (served : work (a ++ [nominate a]) + 1 + pending.toNat ≤ work a)
    (stable : ∀ e, work (a ++ [e]) = work a → nominate (a ++ [e]) = nominate a) :
    let emitted := chooseBy redirect a
    let next := fun e => a ++ [emitted e]
    let waiting := fun e => retryAfter (work a) (work (next e)) pending (nominate a) e
    let oldRank := work a - pending.toNat
    let rank := fun e => work (next e) - (waiting e).toNat
    (∀ e, Q (run start (next e)) ∧
      (waiting e = true → divertedNomination hp start redirect Q (next e) (nominate (next e)))) ∧
    (∀ e, rank e ≤ oldRank) ∧ (∃ e, rank e + 1 ≤ oldRank) := by
  dsimp only
  let emitted := chooseBy redirect a
  let next := fun e => a ++ [emitted e]
  let nominee := nominate a
  have paid : work (a ++ [nominee]) + 1 < work a + 1 := by
    change work (a ++ [nominee]) + 1 + pending.toNat ≤ work a at served
    omega
  have unmask (H : pending = true) : emitted nominee = nominee :=
    diverted_nomination_passes hp start mask physical Q fiber closed ready distinct a nominee (waited H)
  refine ⟨?_, weighted_candidate_serial_drift nominee (work a) pending
    (fun e => work (next e)) emitted live (fun e => weak (emitted e)) (fun H => ?_) unmask⟩
  · intro e
    change Q (run start (next e)) ∧ _
    refine ⟨?_, ?_⟩
    · unfold next
      rw [BStarResetSchedule.run_append]
      exact closed _ q _
    · intro kept
      change retryAfter (work a) (work (next e)) pending nominee e = true at kept
      have equal : work (next e) = work a := by
        by_cases H : work (next e) < work a
        · simp [retryAfter, H] at kept
        · exact Nat.le_antisymm (weak (emitted e)) (Nat.le_of_not_gt H)
      change divertedNomination hp start redirect Q (next e) (nominate (next e))
      have sameNom : nominate (next e) = nominee := stable (emitted e) equal
      rw [sameNom]
      cases H : pending with
      | false =>
        have nominated : e = nominee := by simpa [retryAfter, equal, H] using kept
        subst e
        have changed : emitted nominee ≠ nominee := by
          intro same
          have eq : work (a ++ [nominee]) = work a := by simpa only [next, same] using equal
          rw [eq] at paid
          exact (Nat.lt_irrefl _ paid)
        exact diversion_starts hp start redirect Q a nominee q changed
      | true =>
        have skipped : e ≠ nominee := by
          intro eq
          subst e
          have E : work (a ++ [nominee]) = work a := by simpa only [next, unmask H] using equal
          rw [E] at paid
          exact (Nat.lt_irrefl _ paid)
        exact diverted_nomination_extends hp start redirect Q a nominee e (waited H) skipped
  · simpa only [next, H] using served

set_option maxHeartbeats 1200000 in
/-- The released-owner serial Bellman field on the old emitted
prefix. The only service guard is the literal selected FENCE test.
An all-letter successor preserves the exact diversion certificate
and forbids a retry at the owner's own still-waiting gate. -/
theorem released_cycle_hserial {base origin query : X}
    {hh : ∃ i, oldH6 B base i = true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i = Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (baseReady : BStarClearanceOffset.correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (physical : ∀ a i, fresh a i → firstAdmission hp (base := base) (hh := hh) (run query a) i)
    (a w : Word n) (m : Mode) (pending : Bool) (d : Fin n → Mode) :
    let x := run query a
    let addr := fun j => S.getD j fall
    let nominee := serialNominee hp C head cont x m
    let emitted := chooseBy redirect a
    let y := fun e => step x (emitted e)
    let pc := fun z : X => (ctrlOp.read (z (addr 0).1).long).toNat
    let score := fun z => BStarClearanceAggregate.total
      (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
    let before := releasedCycleWork len (pc x) (score x) m false
    let after := fun e => releasedCycleWork len (pc (y e)) (score (y e)) (d (emitted e))
      (releaseEvent m (d (emitted e)))
    let nextRetry := fun e => retryAfter before (after e) pending nominee e
    Q x → x = run origin w →
    GeneratedOwner hp base addr len origin .idle w m →
    Current hp base addr len x m →
    (∀ e, Event hp addr len x e m (d e) ∧ Current hp base addr len (step x e) (d e)) →
    nominatedFenceClear hp C head cont x m →
    (pending = true → divertedNomination hp query redirect Q a nominee ∧ oldWaiting B addr x m = false) →
    ((∀ e, Q (y e) ∧ (nextRetry e = true →
      divertedNomination hp query redirect Q (a ++ [emitted e])
        (serialNominee hp C head cont (y e) (d (emitted e))) ∧
      oldWaiting B addr (y e) (d (emitted e)) = false)) ∧
     (∀ e, after e - (nextRetry e).toNat ≤ before - pending.toNat) ∧
     (∃ e, after e - (nextRetry e).toNat + 1 ≤ before - pending.toNat)) := by
  dsimp only
  intro qx atWord hist cur actual clear retryEvidence
  let x := run query a
  let addr := fun j => S.getD j fall
  let nominee := serialNominee hp C head cont x m
  let emitted := chooseBy redirect a
  let pc := fun z : X => (ctrlOp.read (z (addr 0).1).long).toNat
  let score := fun z => BStarClearanceAggregate.total
    (BStarClearanceCommandSum.physicalRank B base z (BStarClearanceIndexedSum.distance S)) S
  let before := releasedCycleWork len (pc x) (score x) m false
  let rawAfter := fun e => releasedCycleWork len (pc (step x e)) (score (step x e)) (d e)
    (releaseEvent m (d e))
  have raw (e : Fin n) := released_cycle_raw_mark hp C head cont Q fiber closed distinct
    baseReady ready qx w atWord m (d e) e hist cur (actual e).1 (actual e).2
  have live : 0 < before := released_work_positive len (pc x) (score x) m
  have delivered (h : emitted nominee = nominee) :
      rawAfter (emitted nominee) + 1 + pending.toNat ≤ before := by
    rw [h]
    have paid : rawAfter nominee + (if oldWaiting B addr x m then 1 else 2) ≤ before :=
      (raw nominee).2.2 clear rfl
    cases H : pending with
    | false =>
      change rawAfter nominee + 1 ≤ before
      by_cases W : oldWaiting B addr x m = true
      · rw [if_pos W] at paid
        exact paid
      · rw [if_neg W] at paid
        omega
    | true =>
      have W : oldWaiting B addr x m = false := (retryEvidence H).2
      have noGate : ¬ oldWaiting B addr x m = true := by
        intro yes
        have impossible := W.symm.trans yes
        cases impossible
      rw [if_neg noGate] at paid
      change rawAfter nominee + 2 ≤ before
      exact paid
  have unmask (H : pending = true) : emitted nominee = nominee :=
    diverted_nomination_passes hp query mask physical Q fiber closed ready distinct a nominee
      (retryEvidence H).1
  refine ⟨?_, weighted_candidate_serial_drift nominee before pending
    (fun e => rawAfter (emitted e)) emitted live (fun e => (raw (emitted e)).1)
    delivered unmask⟩
  intro e
  refine ⟨closed _ qx _, ?_⟩
  intro kept
  change retryAfter before (rawAfter (emitted e)) pending nominee e = true at kept
  have equal : rawAfter (emitted e) = before := by
    by_cases H : rawAfter (emitted e) < before
    · simp [retryAfter, H] at kept
    · exact Nat.le_antisymm (raw (emitted e)).1 (Nat.le_of_not_gt H)
  obtain ⟨same, sameGate⟩ := (raw (emitted e)).2.1 equal
  rw [same, sameGate]
  cases H : pending with
  | true =>
    have skipped : e ≠ nominee := by
      intro E
      subst e
      have paid := delivered (unmask H)
      omega
    exact ⟨diverted_nomination_extends hp query redirect Q a nominee e (retryEvidence H).1 skipped,
      (retryEvidence H).2⟩
  | false =>
    have nominated : e = nominee := by simpa [retryAfter, equal, H] using kept
    subst e
    have diverted : emitted nominee ≠ nominee := by
      intro U
      have pay := delivered U
      omega
    refine ⟨diversion_starts hp query redirect Q a nominee qx diverted, ?_⟩
    suffices ¬ oldWaiting B addr x m = true by
      exact Bool.eq_false_iff.mpr this
    intro ownGate
    cases m with
    | idle => contradiction
    | busy op z =>
      cases z with
      | back k => contradiction
      | out k =>
        let spot := addr k
        cases test : pendingSide (longGeometry B (x spot.1)) spot.2 (atSite (x spot.1).long spot.2) with
        | none => simp [oldWaiting, spot, test] at ownGate
        | some s =>
          have mark : nominee = incident spot.1 s := by
            simp only [nominee, serialNominee, spot, addr, test, Option.map_some, Option.getD]
          have paid := pending_candidate_pays hp C Q fiber closed distinct baseReady ready
            mask a w (physical a) qx atWord k op hist cur s test
          rw [← mark] at paid
          have mode := current_mode_unique hp _ _ (actual (emitted nominee)).2 paid.1
          change d (emitted nominee) = .busy op (.out k) at mode
          have pcStable : pc (step x (emitted nominee)) = pc x :=
            paid.1.1.2.2.2.trans cur.1.2.2.2.symm
          unfold rawAfter before at equal
          rw [mode, pcStable] at equal
          simp only [releaseEvent, releasedCycleWork, Bool.false_eq_true, if_false] at equal
          have one : physicalTourWork len (score (step x (emitted nominee))) (.busy op (.out k)) + 1 =
              physicalTourWork len (score x) (.busy op (.out k)) := paid.2
          have tie : physicalTourWork len (score (step x (emitted nominee))) (.busy op (.out k)) =
              physicalTourWork len (score x) (.busy op (.out k)) := Nat.add_left_cancel equal
          rw [tie] at one
          omega

end Candidate

end L4.Height
