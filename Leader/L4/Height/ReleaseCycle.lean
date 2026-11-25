import Leader.L4.Height.ProductionFence
import Leader.L4.Height.SerialProduction
import Leader.L4.Height.FenceEscrow
import Leader.L4.Height.ReleaseBarrier

set_option maxRecDepth 8192
namespace L4.Height.ReleaseCycle

open Classical
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport
open BStarLongCommand BStarLongCommandData BStarLongToken BStarLongDoor BStarLongEvents
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongFixedRouting BStarResetMarkAdapter BStarLongPackets
open BStarClearanceDataChart BStarLongFiberOwner BStarSeparatorControl BStarSeparatingRail
open BStarAcquireAnchors

noncomputable section

private theorem depart_fields (g : LongGeometry) (j : Fin 11) (v w : Payload)
    (departed : depart g j v = some w) :
    v.fault = w.fault ∧ v.opcode = w.opcode := by
  unfold depart at departed
  split at departed
  · dsimp only at departed
    split at departed
    · contradiction
    · cases departed
      exact ⟨rfl, rfl⟩
  · cases departed
    exact ⟨rfl, rfl⟩

section Physical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "run" => BStarResetSchedule.run (AllSizeS1Geometry.step (n := n) B)

/-- The only literal FENCE hold on the nominated old pair comes from
opcode 11 of this very owner and an occupied active sheet it owns. -/
theorem physical_clear_of_exit {base origin x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside) = true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2 = true)
    (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (a : List (Fin n)) (m : Mode) (atWord : x = run origin a)
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len origin .idle a m)
    (cur : Current hp base (fun j => S.getD j fall) len x m)
    (free : (∀ k, m ≠ .busy 11 (.out k)) ∨
      ∀ i sh, dataOwner (oldH6 B base) i sh = o.val →
        activeSheet (longGeometry B (base i)) sh = true →
        (readLane (Sheet.index sh) (x i).long).mobile = .empty) :
    nominatedFenceClear hp C head cont x m := by
  cases m with
  | idle => trivial
  | busy op z =>
    cases z with
    | back k => trivial
    | out k =>
      dsimp only [nominatedFenceClear]
      intro K selected notDoor atSource v w old departed held
      let e := chartMark hp C head cont k
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long, (x (rightNeighbor e)).long)
      let i := site e K.source.side
      obtain ⟨sh, fault, opcode, _, active, sameOwner, _, _, occupied⟩ :=
        BStarClearanceBlockade.literal_blockade g (BStarLongPrep.view raw) K.source w held
      have fields := depart_fields (geometry g K.source.side) K.source.occurrence v w departed
      rcases free with noFence | empty
      · have nonfault : v.fault = 0 := fields.1.trans fault
        have correct : v.opcode.toNat = 11 := (congrArg BitVec.toNat fields.2).trans opcode
        obtain ⟨witness, query, valid⟩ := BStarReleaseOrigin.crop_origin_op
          (geometry g K.source.side) K.source.occurrence (readK raw K.source) v 11
          ⟨nonfault, correct⟩ old
        have F : project (fun j => S.getD j fall) x k = .forward witness := by
          change BStarAcquireForwardTrace.atCursor x (S.getD k fall)=_
          rw [atSource]
          exact (BStarResetRailRing.old_read x e K.source).symm.trans query
        have mode := (BStarOwnerLaunchOrigin.healthy_forward_origin hp C distinct hist
          (atWord ▸ cur) k cur.2.1.1 witness (atWord ▸ F) 11 valid.1 valid.2).1
        exact noFence k mode
      · have inChart : S.getD k fall ∈ S := by
          have bound := cur.2.1.1
          have L := C.length
          rw [← List.getElem_eq_getD (h := show k < S.length by omega)]
          exact List.getElem_mem _
        have ownerAt : commandOwner (oldH6 B base) i K.source.occurrence = o.val := by
          have H := (C.entries _ inChart).2
          rw [atSource] at H
          exact H
        have belongs : dataOwner (oldH6 B base) i sh = o.val :=
          (sameOwner (total (oldH6 B base)) (word (oldH6 B base) i)).symm.trans ownerAt
        have geo : geometry g K.source.side = longGeometry B (x i) := by
          cases H : K.source.side <;> simp [g, oldPair, geometry, i, site, H]
        have inside : (longGeometry B (base i)).inside = (longGeometry B (x i)).inside :=
          congrArg (fun t : Bool × Bool × Bool => t.2.1) (cur.1.1 i)
        have activeRef : activeSheet (longGeometry B (base i)) sh = true := by
          rw [geo] at active
          cases sh <;> simp [activeSheet, inside] at active ⊢ <;> assumption
        have atLane : BStarLongPrep.view raw ⟨K.source.side, sh⟩ =
            readLane (Sheet.index sh) (x i).long := by
          cases H : K.source.side <;> simp [BStarLongPrep.view, raw, i, site, H, lane]
        apply occupied
        rw [atLane]
        exact empty i sh belongs activeRef

end Physical

section Escrow

open FenceEscrow

/-- The retry update needs the current comparison mode. The outer
escrow keeps its existing candidate-word clock, and the inner copy
feeds that same mode to the physical next-letter calculation. -/
def updateWithMode {S : Type} {n : Nat} (paths : List (List (Fin n)))
    (s : FenceEscrow.State S n → Fin n → S) (busy : S → Prop) (x : FenceEscrow.State S n) (e : Fin n) :
    FenceEscrow.State S n :=
  update paths (fun y f => s (y,x.2) f) busy x e

private theorem synchronized_step {S : Type} {n : Nat} (p : List (List (Fin n)))
    (s : FenceEscrow.State S n → Fin n → S) (busy : S → Prop) (x : FenceEscrow.State (FenceEscrow.State S n) n) (e : Fin n)
    (same : x.1.2 = x.2) :
    update p (updateWithMode p s busy) (fun y => busy y.1) x e =
      let z := updateWithMode p s busy x.1 e
      (z,z.2) := by
  obtain ⟨⟨y,m⟩,m'⟩ := x
  change m = m' at same
  subst m'
  rfl

/-- Existing escrow algebra with a mode-aware physical transition.
The old comparison state may suppress retries, including a mark
that empties the comparison on that very candidate. -/
def withComparisonMode {S : Type} {n H : Nat} (positive : 0 < H) (paths : List (List (Fin n)))
    (size : paths.length ≤ 2*H^2*2^(2*H+1))
    (length : ∀ v ∈ paths, v.length ≤ 4*H+2)
    (s : FenceEscrow.State S n → Fin n → S) (busy : S → Prop)
    (Q P : FenceEscrow.State S n → Prop) (R : FenceEscrow.State S n → Nat)
    (closed : ∀ y e, Q y → Q (updateWithMode paths s busy y e))
    (weak : ∀ y, Q y → ¬ P y → ∀ e, R (updateWithMode paths s busy y e) ≤ R y)
    (strict : ∀ y, Q y → ¬ P y → ¬ active y.2 →
      ∃ e, R (updateWithMode paths s busy y e) + 1 ≤ R y) :
    ResidualPotentialData (S := FenceEscrow.State (FenceEscrow.State S n) n) (n := n) :=
  cycleData positive paths size length (updateWithMode paths s busy) (fun y => busy y.1)
    (fun x => x.1.2 = x.2 ∧ Q x.1) (fun x => P x.1) (fun x => R x.1)
    (by
      intro y e q
      rw [synchronized_step paths s busy y e q.1]
      exact ⟨rfl, closed y.1 e q.2⟩)
    (by
      intro y q off e
      rw [synchronized_step paths s busy y e q.1]
      exact weak y.1 q.2 off e)
    (by
      intro y q off outside
      obtain ⟨e, paid⟩ := strict y.1 q.2 off (fun h => outside (q.1 ▸ h))
      exact ⟨e, by simpa only [synchronized_step paths s busy y e q.1] using paid⟩)

end Escrow

section Tracking

open FenceEscrow FenceComparison

/-- The suffix starts at the actual first busy cut and includes
only busy cuts, including the final prefix. -/
def stayedBusy {n : Nat} (busy : List (Fin n) → Prop) (entry suffix : List (Fin n)) : Prop :=
  ∀ k ≤ suffix.length, busy (entry ++ suffix.take k)

/-- After comparison exit, retain either the source's program barrier
or a completed comparison of this same still-live FENCE. -/
def tracked {n : Nat} (p : List (List (Fin n))) (busy past : List (Fin n) → Prop)
    (a : List (Fin n)) : FenceEscrow.Mode n → Prop
  | .before => ¬ busy a
  | .during b => ∃ entry, a = entry++b ∧ stayedBusy busy entry b
  | .afterExit => past a ∨ ∃ entry b, a = entry++b ∧ stayedBusy busy entry b ∧ load p b = 0

private theorem busy_end {n : Nat} {busy : List (Fin n) → Prop}
    {a b : List (Fin n)} (h : stayedBusy busy a b) : busy (a++b) := by
  simpa only [List.take_length] using h b.length (Nat.le_refl _)

private theorem busy_extend {n : Nat} {busy : List (Fin n) → Prop}
    {a b : List (Fin n)} {e : Fin n} (h : stayedBusy busy a b)
    (next : busy (a++(b++[e]))) : stayedBusy busy a (b++[e]) := by
  intro k small
  by_cases old : k≤b.length
  · rw [List.take_append_of_le_length old]
    exact h k old
  · have endAt : k=(b++[e]).length := by simp only [List.length_append, List.length_singleton] at small ⊢; omega
    rw [endAt, List.take_length]
    exact next

theorem tracked_start {n : Nat} (p : List (List (Fin n)))
    (busy past : List (Fin n) → Prop) (a : List (Fin n)) :
    tracked p busy past a (if busy a then enter p [] else .before) := by
  by_cases started : busy a
  · rw [if_pos started]
    have residence : stayedBusy busy a [] := by intro _ _; simpa using started
    by_cases empty : load p [] = 0
    · rw [enter, if_pos empty]
      exact .inr ⟨a, [], by simp, residence, empty⟩
    · rw [enter, if_neg empty]
      exact ⟨a, by simp, residence⟩
  · rw [if_neg started]
    exact started

/-- Advance the actual comparison ledger by one candidate. The two
program facts are exactly crossing out of busy opcode 11, and
remaining past it until the later physical RREL receipt. -/
theorem tracked_next {n : Nat} (p : List (List (Fin n))) (busy past : List (Fin n) → Prop)
    (a : List (Fin n)) (e : Fin n) (m : FenceEscrow.Mode n) (old : tracked p busy past a m)
    (exits : busy a → ¬ busy (a++[e]) → past (a++[e]))
    (keeps : past a → past (a++[e])) :
    tracked p busy past (a++[e]) (update p (fun a e => a++[e]) busy (a,m) e).2 := by
  cases m with
  | before => exact tracked_start p busy past (a++[e])
  | during b =>
    obtain ⟨entry, eq, stays⟩ := old
    have present : busy a := eq.symm ▸ busy_end stays
    by_cases next : busy (a++[e])
    · have w : a++[e]=entry++(b++[e]) := by rw [eq, List.append_assoc]
      have history := busy_extend stays (w ▸ next)
      change tracked p busy past (a++[e]) (if busy (a++[e]) then enter p (b++[e]) else .afterExit)
      rw [if_pos next]
      unfold enter
      split
      · rename_i empty
        exact .inr ⟨entry, b++[e], w, history, empty⟩
      · exact ⟨entry, w, history⟩
    · change tracked p busy past (a++[e]) (if busy (a++[e]) then enter p (b++[e]) else .afterExit)
      rw [if_neg next]
      exact .inl (exits present next)
  | afterExit =>
    change past (a++[e]) ∨ _
    rcases old with behind | ⟨entry, b, eq, stays, empty⟩
    · exact .inl (keeps behind)
    · by_cases next : busy (a++[e])
      · have w : a++[e]=entry++(b++[e]) := by rw [eq, List.append_assoc]
        have weak := (comparison_step p b).1 e
        exact .inr ⟨entry, b++[e], w, busy_extend stays (w ▸ next), by omega⟩
      · exact .inl (exits (eq.symm ▸ busy_end stays) next)

end Tracking

section Barrier

open ReleaseBarrier BStarResetChartService BStarAcquireWaitControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B

def busyFence (m : BStarGeneratedOwner.Mode) : Prop := ∃ z, m = .busy 11 z

/-- A source change from 2 to 3 is exactly the kind of event that
closes the release ledger. Every other event preserves the barrier. -/
theorem source_step_latches {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (same : ∀ i, Layout B base i = Layout B x i) (e : Fin n) {m d : BStarGeneratedOwner.Mode}
    (cur : Current hp base (fun j=>S.getD j fall) len x m)
    (ev : Event hp (fun j=>S.getD j fall) len x e m d)
    (after : Current hp base (fun j=>S.getD j fall) len (step x e) d)
    (old : source x (S.getD 0 fall).1 = 2)
    (next : source (step x e) (S.getD 0 fall).1 = 3) :
    releaseEvent m d = true := by
  cases ev with
  | idle_hold away =>
    have samePC := congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat)
      (BStarOwnerControlHistory.idle_nonown hp C same cur.2 e (distinct e) away).2
    change source (step x e) (S.getD 0 fall).1 = source x (S.getD 0 fall).1 at samePC
    omega
  | bad_issue own bad =>
    change (ctrlOp.read (x (S.getD 0 fall).1).long).toNat = 2 at old
    dsimp only at bad
    have impossible := BStarResetDoor.reset_initial (x (S.getD 0 fall).1).long 2 (by decide)
    have no := (congrArg (fun op => initial op (x (S.getD 0 fall).1).long) old).symm.trans bad
    exact False.elim (by have eq := impossible.symm.trans no; cases eq)
  | launch own good =>
    have samePC : source (step x e) (S.getD 0 fall).1 = source x (S.getD 0 fall).1 :=
      after.1.2.2.2
    omega
  | transit op z target live seen =>
    have samePC : source (step x e) (S.getD 0 fall).1 = source x (S.getD 0 fall).1 :=
      after.1.2.2.2.trans cur.1.2.2.2.symm
    omega
  | arrived_hold op away =>
    have samePC : source (step x e) (S.getD 0 fall).1 = source x (S.getD 0 fall).1 :=
      after.1.2.2.2.trans cur.1.2.2.2.symm
    omega
  | consume op own clear =>
    have pc : source x (S.getD 0 fall).1 = op := cur.1.2.2.2
    have eq : op = 2 := pc.symm.trans old
    rw [eq]
    rfl

theorem fence_barrier_step {base x : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (distinct : ∀ e : Fin n, e ≠ rightNeighbor e)
    (same : ∀ i, Layout B base i = Layout B x i) (e : Fin n) {m d : BStarGeneratedOwner.Mode}
    (cur : Current hp base (fun j=>S.getD j fall) len x m)
    (ev : Event hp (fun j=>S.getD j fall) len x e m d)
    (after : Current hp base (fun j=>S.getD j fall) len (step x e) d)
    (openCycle : releaseEvent m d = false) :
    let past := fun y => Past (source y (S.getD 0 fall).1)
    (busyFence m → ¬busyFence d → past (step x e)) ∧
      (past x → past (step x e)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩ out
    cases ev with
    | transit _ _ d live seen => exact (out ⟨d, rfl⟩).elim
    | arrived_hold => exact (out ⟨.back 0, rfl⟩).elim
    | consume _ sameMark clear => exact fence_receipt hp C distinct same e cur (.consume 11 sameMark clear)
  · intro behind
    exact preserve hp C distinct same e cur ev after behind (fun ⟨old, next⟩ => by
      have close := source_step_latches hp C distinct same e cur ev after old next
      rw [openCycle] at close
      contradiction)

theorem fence_barrier_excludes {base x : X} {addr : Nat → Pos n} {len : Nat}
    (m : BStarGeneratedOwner.Mode) (cur : Current hp base addr len x m)
    (past : Past (source x (addr 0).1)) : ¬busyFence m := by
  rintro ⟨z, rfl⟩
  have pc : source x (addr 0).1 = 11 := cur.1.2.2.2
  rw [pc] at past
  unfold Past at past
  omega

end Barrier

section ComparisonBridge

open BStarSteeredLikelihood OpenFenceLine FenceLineTransfer FenceEmbedding FenceComparison
open ProductionFence ReleaseBarrier

private theorem emit_cat {n : Nat} (c : Word n → Fin n → Fin n) (a u v : Word n) :
    emit c a (u++v) = emit c a u ++ emit c (a++emit c a u) v := by
  induction u generalizing a with
  | nil => simp [emit]
  | cons e u ih =>
    simp only [List.cons_append, emit, ih, List.append_assoc, List.nil_append]

def candidatePlay {n : Nat} (c : Word n → Fin n → Fin n) : Word n → Fin n → Fin n :=
  fun a e => c (emit c [] a) e

private theorem labels_emit {n : Nat} (c : Word n → Fin n → Fin n) (a w : Word n) :
    ProductionFence.labels (candidatePlay c) a w = emit c (emit c [] a) w := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih =>
    simp only [ProductionFence.labels, candidatePlay, emit, ih, emit_cat, List.nil_append]

private theorem labels_take {n : Nat} (play : Word n → Fin n → Fin n) (a w : Word n) (k : Nat) :
    (ProductionFence.labels play a w).take k = ProductionFence.labels play a (w.take k) := by
  induction w generalizing a k with
  | nil => simp [ProductionFence.labels]
  | cons e w ih =>
    cases k with
    | zero => rfl
    | succ k => simp [ProductionFence.labels, ih]

private theorem labels_size {n : Nat} (play : Word n → Fin n → Fin n) (a w : Word n) :
    (ProductionFence.labels play a w).length = w.length := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih => simp [ProductionFence.labels, ih]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "run" => BStarResetSchedule.run step

/-- After path exhaustion while still in the same opcode-11 excursion,
the global candidate history determines the exact comparison word and
every active owned lane is physically empty. -/
theorem drained_on_tracked_tape {base origin : X} {hh : ∃ i, oldH6 B base i = true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop)
    (fiber : ∀ x, Q x → ∀ j, Layout B base j = Layout B x j)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (sep : ∀ e : Fin n, e ≠ rightNeighbor e)
    (initial : Q origin) (clean : Current hp base (fun j => S.getD j fall) len origin .idle)
    (prior : Word n) {u v width H : Nat}
    (L : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 u width)
    (R : BStarCopyLeftStrip.Strip B base (S.getD len fall).1 v width)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 u = (S.getD len fall).1)
    (inside : ∀ j, (longGeometry B (base j)).inside =
      decide (BStarH6Ordinal.oldOrdinal B base hh j < width))
    (lH : u+width ≤ H) (rH : v+width ≤ H)
    (emitMark : Word n → Fin n → Fin n) (two : Twice (candidatePlay emitMark))
    (mode : Word n → BStarGeneratedOwner.Mode)
    (current : ∀ a, Current hp base (fun j => S.getD j fall) len
      (run origin (prior++emit emitMark [] a)) (mode a))
    (entry suffix : Word n) (residence : stayedBusy (fun a => busyFence (mode a)) entry suffix) :
    let l := u+width
    let rlen := v+width
    let hi := (S.getD 0 fall).1
    let mid := (S.getD len fall).1
    load (pairedPaths l rlen (leftBond hi) (rightBond mid rlen)) suffix = 0 →
    ∀ i sh, dataOwner (oldH6 B base) i sh = o.val →
      activeSheet (longGeometry B (base i)) sh = true →
      (readLane (Sheet.index sh) (run origin (prior++emit emitMark [] (entry++suffix)) i).long).mobile =
        .empty := by
  dsimp only
  intro exhausted
  let play := fun a => candidatePlay emitMark (entry++a)
  let past := prior++emit emitMark [] entry
  have twice : Twice play := by
    intro a e mid
    obtain ⟨u,f,v,eq,send⟩ := two (entry++a) e mid
    exact ⟨u,f,v,eq,by simpa only [play,List.append_assoc] using send⟩
  have played (w : Word n) :
      prior++emit emitMark [] (entry++w) = past++ProductionFence.labels play [] w := by
    have same (a w : Word n) :
        ProductionFence.labels play a w = ProductionFence.labels (candidatePlay emitMark) (entry++a) w := by
      induction w generalizing a with
      | nil => rfl
      | cons e w ih =>
        simp only [ProductionFence.labels, play, ih, List.append_assoc]
    rw [same, labels_emit, List.append_nil, emit_cat]
    simp only [past, List.nil_append, List.append_assoc]
  have clear := (ProductionFence.drain_or_exit hp C Q fiber closed sep initial clean
    past L R lH rH play twice).done suffix exhausted
  dsimp only at clear
  rcases clear with ⟨pre, rest, eq, off⟩ | empty
  · let k := pre.length
    have bound : k ≤ suffix.length := by
      have V := congrArg List.length eq
      rw [labels_size, List.length_append] at V
      omega
    have cut : pre = ProductionFence.labels play [] (suffix.take k) := by
      rw [← labels_take, eq, List.take_append_of_le_length (Nat.le_refl pre.length)]
      exact List.take_length.symm
    obtain ⟨z, hz⟩ := residence k bound
    have atCut := current (entry++suffix.take k)
    rw [played, ←cut, hz] at atCut
    exact (off ⟨z,atCut⟩).elim
  · intro i sh owned active
    have covered := FenceCoverage.cover hp C L R seam inside i sh active owned
    rw [played]
    exact empty i sh owned covered

end ComparisonBridge

section Tape

open BStarSteeredLikelihood

/-- Actual released-owner candidate history together with the local
retry bit and the sticky RREL receipt latch. -/
structure Tape (n : Nat) where
  candidates : Word n
  released : Bool
  retry : Bool

def tapeNext {n : Nat} (mode : Word n → BStarGeneratedOwner.Mode)
    (work : Word n → Bool → Nat) (nominate : Word n → Fin n)
    (x : FenceEscrow.State (Tape n) n) (e : Fin n) : Tape n :=
  let a := x.1.candidates
  let b := a++[e]
  let released := x.1.released || releaseEvent (mode a) (mode b)
  let retry := if FenceEscrow.active x.2 then false
    else retryAfter (work a x.1.released) (work b released) x.1.retry (nominate a) e
  ⟨b, released, retry⟩

private theorem tape_comparison_next {n : Nat} (paths : List (Word n))
    (mode : Word n → BStarGeneratedOwner.Mode) (work : Word n → Bool → Nat) (nominate : Word n → Fin n)
    (x : FenceEscrow.State (Tape n) n) (e : Fin n) :
    (updateWithMode paths (tapeNext mode work nominate) (fun y => busyFence (mode y.candidates)) x e).2 =
      (FenceEscrow.update paths (fun a f => a++[f]) (fun a => busyFence (mode a)) (x.1.candidates,x.2) e).2 := rfl

end Tape

section ReleasedData

open BStarSteeredLikelihood BStarParkedSteering BStarResetSchedule BStarClearanceOffset
open FenceEscrow FenceComparison FenceLineTransfer FenceEmbedding OpenFenceLine ReleaseBarrier

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n := n) B
local notation "raw" => BStarResetSchedule.run step

/-- Physical inputs for one released owner. Origin is its recovered
clean cut and prior is the exact already emitted prefix up to query.
The ledger starts fresh at query even if opcode 11 is already busy. -/
theorem released_owner_data {base origin query : X} {hh : ∃ i,oldH6 B base i=true}
    {owner : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh owner S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (Q : X → Prop) (fiber : ∀ x, Q x → ∀ i, Layout B base i=Layout B x i)
    (closed : ∀ x, Q x → ∀ e, Q (step x e)) (sep : ∀ e : Fin n, e≠rightNeighbor e)
    (baseReady : correct (oldH6 B base) hh 5 base)
    (ready : ∀ x, Q x → correct (oldH6 B base) hh 5 x)
    (originReady : Q origin) (clean : Current hp base (fun j => S.getD j fall) len origin .idle)
    (prior : Word n) (replay : raw origin prior = query)
    {u v radius H W : Nat}
    (L : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 u radius)
    (R : BStarCopyLeftStrip.Strip B base (S.getD len fall).1 v radius)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 u=(S.getD len fall).1)
    (inside : ∀ j,(longGeometry B (base j)).inside=decide (oldOrdinal B base hh j<radius))
    (lH : u+radius≤H) (rH : v+radius≤H) (hw : 0<W) (capH : H≤2*W) (capLen : len+1≤11*W)
    {fresh : Word n → Fin n → Prop} {redirect : Word n → Fin n → Option (Fin n)}
    (mask : FreshOnly (oldH6 B base) hh fresh redirect)
    (physical : ∀ a i, fresh a i → firstAdmission hp (base:=base) (hh:=hh) (raw query a) i)
    (two : Twice (candidatePlay (chooseBy redirect))) :
    ∃ (D : ResidualPotentialData (S:=FenceEscrow.State (FenceEscrow.State (Tape n) n) n) (n:=n))
      (initial : FenceEscrow.State (FenceEscrow.State (Tape n) n) n) (mode : Word n → BStarGeneratedOwner.Mode),
      initial.1.1 = ⟨[],false,false⟩ ∧ D.Q initial ∧ D.Phi initial≤2^15*n*W ∧
      (∀ a, Current hp base (fun j => S.getD j fall) len
        (raw query (emit (chooseBy redirect) [] a)) (mode a)) ∧
      (∀ y e, (D.next y e).1.1.candidates=y.1.1.candidates++[e]) ∧
      (∀ y e, (D.next y e).1.1.released=
        (y.1.1.released || releaseEvent (mode y.1.1.candidates) (mode (y.1.1.candidates++[e])))) ∧
      (∀ y, D.P y ↔ y.1.1.released=true) := by
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let pick := chooseBy redirect
  let sent := emit pick []
  let word := fun a => prior++sent a
  let state := fun a => raw query (sent a)
  have actual (a : Word n) : raw origin (word a) = state a := by
    unfold word state
    rw [BStarResetSchedule.run_append, replay]
  have language (a : Word n) :
      ∃ m, GeneratedOwner hp base addr len origin .idle (word a) m ∧
        Q (state a) ∧ Current hp base addr len (state a) m := by
    obtain ⟨m, gen, q, cur⟩ :=
      generated_word hp C Q fiber closed sep (word a) .idle originReady clean
    rw [actual a] at q cur
    exact ⟨m,gen,q,cur⟩
  let mode := fun a => Classical.choose (language a)
  have trace (a : Word n) := Classical.choose_spec (language a)
  have qstate (a : Word n) : Q (state a) := (trace a).2.1
  have cur (a : Word n) : Current hp base addr len (state a) (mode a) := (trace a).2.2
  have gen (a : Word n) : GeneratedOwner hp base addr len origin .idle (word a) (mode a) := (trace a).1
  have stateStep (a : Word n) (e : Fin n) : state (a++[e])=step (state a) (pick (sent a) e) := by
    unfold state sent
    rw [emit_cat, BStarResetSchedule.run_append]
    rfl
  let pc := fun a => (ctrlOp.read (state a root).long).toNat
  let score := fun a => BStarClearanceAggregate.total
    (BStarClearanceCommandSum.physicalRank B base (state a) (BStarClearanceIndexedSum.distance S)) S
  let work := fun a released => releasedCycleWork len (pc a) (score a) (mode a) released
  let nominate := fun a => serialNominee hp C head cont (state a) (mode a)
  let busy := fun a => busyFence (mode a)
  let past := fun a => Past (pc a)
  let paths := pairedPaths (u+radius) (v+radius) (leftBond root) (rightBond (addr len).1 (v+radius))
  let advance := tapeNext mode work nominate
  let escrowBusy (y : Tape n) := busy y.candidates
  let update := updateWithMode paths advance escrowBusy
  let invariant (y : FenceEscrow.State (Tape n) n) :=
    y.1.released=false →
    tracked paths busy past y.1.candidates y.2 ∧
      (y.1.retry=true → ¬ active y.2 ∧
        divertedNomination hp query redirect Q (sent y.1.candidates) (nominate y.1.candidates) ∧
        oldWaiting B addr (state y.1.candidates) (mode y.1.candidates)=false)
  let stop (y : FenceEscrow.State (Tape n) n) := y.1.released=true
  let rank (y : FenceEscrow.State (Tape n) n) := work y.1.candidates y.1.released-y.1.retry.toNat
  have pathsClear := paired_clearance (Nat.add_pos_left L.seam_pos _) (Nat.add_pos_left R.seam_pos _)
    lH rH (leftBond root) (rightBond (addr len).1 (v+radius)) (candidatePlay pick) two
  have hH : 0<H := Nat.lt_of_lt_of_le (Nat.add_pos_left L.seam_pos _) lH
  have clear (a : Word n) (m : FenceEscrow.Mode n) (t : tracked paths busy past a m)
      (off : ¬active m) : nominatedFenceClear hp C head cont (state a) (mode a) := by
    apply physical_clear_of_exit hp C head cont sep (word a) (mode a) (actual a).symm (gen a) (cur a)
    have excludes (bn : ¬busy a) : ∀ k,mode a ≠ .busy 11 (.out k) :=
      fun k eq => bn ⟨.out k,eq⟩
    cases m with
    | before => exact .inl (excludes t)
    | during _ => exact (off True.intro).elim
    | afterExit =>
      rcases t with barrier | ⟨entry, suffix, eq, residence, zero⟩
      · exact .inl (excludes (fence_barrier_excludes hp (mode a) (cur a) barrier))
      · right
        have empty := drained_on_tracked_tape hp C Q fiber closed sep originReady clean prior
          L R seam inside lH rH pick two mode (fun b => (actual b).symm ▸ cur b)
          entry suffix residence zero
        rw [eq, ←actual]
        exact empty
  have possible (a : Word n) (e : Fin n) :
      ∃ m, Event hp addr len (state a) e (mode a) m ∧
        Current hp base addr len (step (state a) e) m :=
    current_step hp C Q fiber closed sep (qstate a) e (mode a) (cur a)
  let nextMode := fun a e => Classical.choose (possible a e)
  have choices (a : Word n) (e : Fin n) := Classical.choose_spec (possible a e)
  have next_eq (a : Word n) (e : Fin n) :
      nextMode a (pick (sent a) e)=mode (a++[e]) :=
    current_mode_unique hp _ _ (choices a (pick (sent a) e)).2 (stateStep a e ▸ cur (a++[e]))
  have mark (a : Word n) (e : Fin n) :
      Event hp addr len (state a) (pick (sent a) e) (mode a) (mode (a++[e])) :=
    next_eq a e ▸ (choices a (pick (sent a) e)).1
  have oldWork (a : Word n) (e : Fin n) :=
    released_cycle_raw_mark hp C head cont Q fiber closed sep baseReady ready (qstate a)
      (word a) (actual a).symm (mode a) (mode (a++[e])) (pick (sent a) e)
      (gen a) (cur a) (mark a e) (stateStep a e ▸ cur (a++[e]))
  have doSerial (y : FenceEscrow.State (Tape n) n) (isOpen : y.1.released=false)
      (trackedNow : tracked paths busy past y.1.candidates y.2)
      (trackingRetry : y.1.retry=true →
        divertedNomination hp query redirect Q (sent y.1.candidates) (nominate y.1.candidates) ∧
          oldWaiting B addr (state y.1.candidates) (mode y.1.candidates)=false)
      (off : ¬active y.2) :
      (∀ e, (update y e).1.retry=true →
        divertedNomination hp query redirect Q (sent (update y e).1.candidates)
          (nominate (update y e).1.candidates) ∧
          oldWaiting B addr (state (update y e).1.candidates) (mode (update y e).1.candidates)=false) ∧
      (∀ e, rank (update y e)≤rank y) ∧ (∃ e,rank (update y e)+1≤rank y) := by
    let a := y.1.candidates
    have serial := released_cycle_hserial hp C head cont Q fiber closed sep baseReady ready
      mask physical (sent a) (word a) (mode a) y.1.retry (nextMode a)
      (qstate a) (actual a).symm (gen a) (cur a) (choices a) (clear a y.2 trackedNow off) trackingRetry
    have liftRank (e : Fin n) : rank (update y e) =
        work (a++[e]) (releaseEvent (mode a) (mode (a++[e]))) -
          (retryAfter (work a false) (work (a++[e]) (releaseEvent (mode a) (mode (a++[e]))))
            y.1.retry (nominate a) e).toNat := by
      simp only [rank, update, updateWithMode, FenceEscrow.update, advance, tapeNext,
        if_neg off, isOpen, Bool.false_or, a]
    have sentStep (e : Fin n) : sent (a++[e])=sent a++[pick (sent a) e] := by
      unfold sent
      rw [emit_cat]
      rfl
    refine ⟨?_,?_,?_⟩
    · intro e pending
      have H := (serial.1 e).2
      dsimp only at H
      rw [next_eq a e, ←stateStep a e, ←sentStep e] at H
      simp only [update, updateWithMode, FenceEscrow.update, advance, tapeNext,
        if_neg off, isOpen, Bool.false_or] at pending
      exact H pending
    · intro e
      rw [liftRank]
      have H := serial.2.1 e
      dsimp only at H
      rw [next_eq a e, ←stateStep a e] at H
      simpa only [rank, isOpen] using H
    · obtain ⟨e,H⟩ := serial.2.2
      refine ⟨e,?_⟩
      rw [liftRank]
      dsimp only at H
      rw [next_eq a e, ←stateStep a e] at H
      simpa only [rank, isOpen] using H
  have noRetryEntry (y : FenceEscrow.State (Tape n) n) (e : Fin n) (old : y.1.released=false)
      (track : tracked paths busy past y.1.candidates y.2)
      (out : ¬active y.2) (new : active (update y e).2) :
      (update y e).1.retry=false := by
    let a := y.1.candidates
    have before : y.2=.before := by
      cases H : y.2 with
      | before => rfl
      | during z => exact (out (by simp [H,active])).elim
      | afterExit =>
        have E : (update y e).2=.afterExit := by
          rw [show (update y e).2 = _ from tape_comparison_next paths mode work nominate y e, H]
          rfl
        rw [E] at new
        exact new.elim
    have nextBusy : busy (a++[e]) := by
      apply Classical.byContradiction
      intro notBusy
      have E : (update y e).2=.before := by
        rw [show (update y e).2 = _ from tape_comparison_next paths mode work nominate y e, before]
        exact if_neg notBusy
      rw [E] at new
      exact new.elim
    have priorOff : ¬busy a := by rw [before] at track; exact track
    have selected : pick (sent a) e = nominate a := by
      have event := mark a e
      change ¬ busyFence (mode a) at priorOff
      change busyFence (mode (a++[e])) at nextBusy
      change pick (sent a) e = serialNominee hp C head cont (state a) (mode a)
      generalize mEq : mode a = m at event priorOff ⊢
      generalize dEq : mode (a++[e]) = d at event nextBusy
      cases event with
      | idle_hold => obtain ⟨_, eq⟩ := nextBusy; contradiction
      | bad_issue => obtain ⟨_, eq⟩ := nextBusy; contradiction
      | launch own _ => exact own
      | transit op z dest _ _ =>
        obtain ⟨j, eq⟩ := nextBusy
        have pc : op=11 := by injection eq
        subst op
        exact (priorOff ⟨z,rfl⟩).elim
      | arrived_hold => exact (priorOff nextBusy).elim
      | consume => obtain ⟨_, eq⟩ := nextBusy; contradiction
    have paid := (oldWork a e).2.2 (clear a y.2 track out) selected
    have drop : work (a++[e]) (releaseEvent (mode a) (mode (a++[e]))) < work a false := by
      rw [←stateStep a e] at paid
      change work (a++[e]) (releaseEvent (mode a) (mode (a++[e]))) +
        (if oldWaiting B addr (state a) (mode a) then 1 else 2) ≤ work a false at paid
      split at paid <;> omega
    simp only [update, updateWithMode, FenceEscrow.update, advance, tapeNext,
      if_neg out, old, Bool.false_or, a, retryAfter, if_pos drop]
  have closedInv (y : FenceEscrow.State (Tape n) n) (e : Fin n) (hy : invariant y) : invariant (update y e) := by
    intro openNext
    let a := y.1.candidates
    have stopBits : (y.1.released || releaseEvent (mode a) (mode (a++[e]))) = false := openNext
    obtain ⟨openNow, noReceipt⟩ := Bool.or_eq_false_iff.mp stopBits
    obtain ⟨track, retry⟩ := hy openNow
    have barrier := fence_barrier_step hp C sep (fiber _ (qstate a)) (pick (sent a) e)
      (cur a) (mark a e) (stateStep a e ▸ cur (a++[e])) noReceipt
    simp only [←stateStep a e] at barrier
    refine ⟨?_,?_⟩
    · change tracked paths busy past (a++[e]) (update y e).2
      rw [show (update y e).2 = _ from tape_comparison_next paths mode work nominate y e]
      exact tracked_next paths busy past a e y.2 track barrier.1 barrier.2
    · intro kept
      by_cases inFence : active y.2
      · simp only [update, updateWithMode, FenceEscrow.update, advance, tapeNext, if_pos inFence] at kept
        contradiction
      · have result := doSerial y openNow track (fun h => (retry h).2) inFence
        exact ⟨fun activeNow => Bool.noConfusion ((noRetryEntry y e openNow track inFence activeNow).symm.trans kept),
          result.1 e kept⟩
  have everywhere (y : FenceEscrow.State (Tape n) n) (hy : invariant y) (notReleased : ¬ stop y) :
      ∀ e, rank (update y e)≤rank y := by
    have openNow : y.1.released=false := Bool.eq_false_iff.mpr notReleased
    obtain ⟨track, retry⟩ := hy openNow
    by_cases inFence : active y.2
    · intro e
      have unarmed : y.1.retry=false := Bool.eq_false_iff.mpr (fun t => (retry t).1 inFence)
      have flow := (oldWork y.1.candidates e).1
      simpa only [←stateStep y.1.candidates e, rank, update, updateWithMode, FenceEscrow.update,
        advance, tapeNext, if_pos inFence, openNow, Bool.false_or, unarmed, Bool.toNat, Bool.cond_false, Nat.sub_zero,
        work, pc, score] using flow
    · exact (doSerial y openNow track (fun h => (retry h).2) inFence).2.1
  have strict (y : FenceEscrow.State (Tape n) n) (hy : invariant y) (notReleased : ¬ stop y) (off : ¬active y.2) :
      ∃ e,rank (update y e)+1≤rank y := by
    have openNow : y.1.released=false := Bool.eq_false_iff.mpr notReleased
    obtain ⟨track, retry⟩ := hy openNow
    exact (doSerial y openNow track (fun h => (retry h).2) off).2.2
  let D := withComparisonMode hH paths pathsClear.size pathsClear.length advance escrowBusy
    invariant stop rank closedInv everywhere strict
  let initialization := if busy [] then enter paths [] else FenceEscrow.Mode.before
  let begin : FenceEscrow.State (Tape n) n := (⟨[],false,false⟩,initialization)
  have starting : invariant begin := by
    intro _
    exact ⟨tracked_start paths busy past [],fun h => Bool.noConfusion h⟩
  have valid : FenceEscrow.valid paths initialization := by
    unfold initialization
    by_cases bb : busy []
    · rw [if_pos bb]
      unfold enter
      split
      · trivial
      · exact Nat.pos_of_ne_zero (by assumption)
    · rw [if_neg bb]
      trivial
  have rankCap : rank begin≤420*(6*(len+1)+10) := by
    let w := 6*(len+1)+10
    have budget : physicalTourWork len (score []) (mode []) ≤ w := by
      have cur0 := cur []
      cases eq : mode [] with
      | idle => simp only [physicalTourWork, w]; omega
      | busy op z =>
        rw [eq] at cur0
        cases z with
        | out k =>
          have eqScore := generated_forward_rank_eq hp C op k cur0
          have p := BStarClearanceGate.bounded (longGeometry B (base (addr k).1)) (addr k).2
            (bind (longGeometry B (base (addr k).1)) (addr k).2
              (atSite (state [] (addr k).1).long (addr k).2))
          change score [] = 4*(len+1-k) +
            BStarClearanceGate.weight (longGeometry B (base (addr k).1)) (addr k).2
              (bind (longGeometry B (base (addr k).1)) (addr k).2
                (atSite (state [] (addr k).1).long (addr k).2)) at eqScore
          rw [eqScore]
          simp only [physicalTourWork,w]
          omega
        | back k =>
          have bound := cur0.2.1.1
          simp only [physicalTourWork,w]
          omega
    have legal : pc [] < 413 := by
      have H := cur []
      cases m : mode [] with
      | idle => rw [m] at H; exact BStarClearanceResidual.issue_range H.1
      | busy op z =>
        rw [m] at H
        have V := H.1.2.1
        unfold LongDoorGuard.valid at V
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp V).2
    have tours := (tours_through_release_bound _ legal).2
    have reserve : toursThroughRelease (pc []) - 1 ≤ 419 := by omega
    change (toursThroughRelease (pc []) - 1)*w + physicalTourWork len (score []) (mode []) ≤ _
    calc
      _ ≤ 419*w+w := Nat.add_le_add (Nat.mul_le_mul_right _ reserve) budget
      _ = 420*w := by omega
  have escrowCap : charge H paths initialization ≤ 128*n*H := by
    cases mode : initialization with
    | before => exact Nat.le_refl _
    | afterExit => exact Nat.zero_le _
    | during a =>
      calc
        _ ≤ (16*H)*(8*n) := FencePathPotential.reserve_cap _ _ _
        _ = 128*n*H := by ac_rfl
  refine ⟨D,(begin,initialization),mode,rfl,⟨⟨rfl,starting⟩,valid⟩,?_,cur,
    fun _ _ => rfl,fun _ _ => rfl,fun _ => Iff.rfl⟩
  exact combined_cap hw capLen capH rankCap _ escrowCap

end ReleasedData

end
end L4.Height.ReleaseCycle

