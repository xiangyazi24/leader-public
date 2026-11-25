import Leader.L4.BStarTrace
import Init.Data.List.Sort.Lemmas

/-! Literal old-pair claims. This is the command/data geometry
and reservation schedule; no token or packet transition is assumed. -/
namespace L4.BStarLongClaims
open AllSizeProtocol

inductive Side where
  | left | right
  deriving DecidableEq, Repr

def Side.key : Side → Nat
  | .left => 0
  | .right => 1

structure At (α : Type) where
  side : Side
  occurrence : α
  deriving DecidableEq, Repr

def L {α : Type} (j : α) : At α := ⟨.left,j⟩
def R {α : Type} (j : α) : At α := ⟨.right,j⟩

structure Claim (α κ : Type) where
  kind : κ
  source : At α
  destination : Option (At α)
  deriving DecidableEq, Repr

def Claim.slots {α κ : Type} (q : Claim α κ) : List (At α) :=
  q.source :: q.destination.toList

inductive Cmd where
  | door | terminal | link
  deriving DecidableEq, Repr

def Cmd.key : Cmd → Nat
  | .door => 0
  | .terminal => 1
  | .link => 2

inductive Sheet where
  | ls | ld | rs | rd
  deriving DecidableEq, Repr

def Sheet.key : Sheet → Nat
  | .ls => 0
  | .ld => 1
  | .rs => 2
  | .rd => 3

inductive Data where
  | ending | hop
  deriving DecidableEq, Repr

def Data.key : Data → Nat
  | .ending => 0
  | .hop => 1

abbrev CommandClaim := Claim (Fin 11) Cmd
abbrev DataClaim := Claim Sheet Data

/-- Numeric lexicographic key: second endpoint absent precedes every
present endpoint. Capacity 24 covers every 11-occurrence address. -/
def claimKey {α κ : Type} (ord : α → Nat) (kind : κ → Nat) (q : Claim α κ) : Nat :=
  let rank := fun s : At α => 2*ord s.occurrence+s.side.key
  let dst := match q.destination with | none => 0 | some s => 1+rank s
  (24*kind q.kind+rank q.source)*24+dst

def commandKey : CommandClaim → Nat := claimKey Fin.val Cmd.key
def dataKey : DataClaim → Nat := claimKey Sheet.key Data.key

def ends (x : LongGeometry) : Bool := x.inside && x.last

def link (a b : At (Fin 11)) : CommandClaim := ⟨.link,a,some b⟩

def commandClaims (g : Pair LongGeometry) : List CommandClaim :=
  let x := g.1
  let y := g.2
  (if y.axes.h6 then
    [⟨.door,R 0,none⟩,⟨.terminal,R 10,none⟩,
      link (L 0) (R 1), link (L 1) (R 2), link (L 2) (L 3),
      link (R 3) (L 4), link (R 4) (L 5), link (R 5) (R 6), link (L 6) (R 7)] ++
      (if y.inside then [link (L 7) (R 8), link (R 9) (L 10)] else [])
  else
    ([0,1,2,6,7] : List (Fin 11)).map (fun j => link (L j) (R j)) ++
    ([3,4,5,10] : List (Fin 11)).map (fun j => link (R j) (L j)) ++
      (if x.inside && y.inside && !ends x then
        [link (L 8) (R 8),link (R 9) (L 9)] else [])) ++
  (if ends x then [link (L 8) (L 9)] else [])

def hop (a b : At Sheet) : DataClaim := ⟨.hop,a,some b⟩
def ending (a : At Sheet) : DataClaim := ⟨.ending,a,none⟩

def dataClaims (g : Pair LongGeometry) : List DataClaim :=
  let x := g.1
  let y := g.2
  (if y.axes.h6 then
    (if y.inside then [hop (L .ls) (R .ld),hop (R .rs) (L .rd)] else []) ++ [ending (R .rd)]
  else
    [hop (L .ls) (R .ls),hop (R .rd) (L .rd)] ++
    (if x.inside && y.inside && !ends x then
      [hop (L .ld) (R .ld),hop (R .rs) (L .rs)] else [])) ++
  (if ends x then [ending (L .ld)] else [])

def discarded (g : Pair LongGeometry) : List (At (Fin 11)) :=
  (if g.1.inside then [] else [L 8,L 9]) ++
  (if g.2.inside then [] else [R 8,R 9])

def free {α : Type} [DecidableEq α] (used slots : List α) : Bool :=
  slots.all fun s => !(used.contains s)

theorem free_iff {α : Type} [DecidableEq α] (used slots : List α) :
    free used slots=true ↔ ∀ s∈slots, s∉used := by
  simp [free,List.all_eq_true]

/-- Accept whole slot sets in order. Reservations survive the failure
of a later row action and are supplied before any offer is chosen. -/
def select {α C : Type} [DecidableEq α] (slots : C → List α) :
    List α → List C → List C
  | _, [] => []
  | used, c::cs =>
    if free used (slots c) then c::select slots (slots c++used) cs
    else select slots used cs

theorem select_sublist {α C : Type} [DecidableEq α] (slots : C → List α)
    (used : List α) (L : List C) : (select slots used L).Sublist L := by
  induction L generalizing used with
  | nil => exact .slnil
  | cons c cs ih =>
    unfold select
    split
    · exact .cons_cons _ (ih _)
    · exact .cons _ (ih _)

theorem select_away {α C : Type} [DecidableEq α] (slots : C → List α)
    (used : List α) (L : List C) :
    ∀ c∈select slots used L, ∀ s∈slots c, s∉used := by
  induction L generalizing used with
  | nil => simp [select]
  | cons c cs ih =>
    unfold select
    split
    · rename_i h
      intro d hd s hs hu
      rcases List.mem_cons.mp hd with rfl|hd
      · exact ((free_iff ..).mp h s hs) hu
      · exact ih _ d hd s hs (List.mem_append_right _ hu)
    · exact ih used

theorem select_pairwise {α C : Type} [DecidableEq α] (slots : C → List α)
    (used : List α) (L : List C) :
    (select slots used L).Pairwise (fun c d => ∀ s∈slots d, s∉slots c) := by
  induction L generalizing used with
  | nil => exact .nil
  | cons c cs ih =>
    unfold select
    split
    · apply List.Pairwise.cons
      · intro d hd s hs hc
        exact select_away slots _ _ d hd s hs (List.mem_append_left _ hc)
      · exact ih _
    · exact ih _

theorem select_flatten_nodup {α C : Type} [DecidableEq α] (slots : C → List α)
    (used : List α) (L : List C) (h : ∀ c∈L, (slots c).Nodup) :
    ((select slots used L).flatMap slots).Nodup := by
  induction L generalizing used with
  | nil => exact .nil
  | cons c cs ih =>
    have htail : ∀ a∈cs, (slots a).Nodup := fun a ha => h a (List.mem_cons_of_mem c ha)
    unfold select
    split
    · rw [List.flatMap_cons,List.nodup_append]
      refine ⟨h c (List.mem_cons_self ..),ih _ htail,?_⟩
      intro s h₁ t h₂ E
      subst t
      obtain ⟨d,hd,hs⟩ := List.mem_flatMap.mp h₂
      exact select_away slots _ _ d hd s hs (List.mem_append_left _ h₁)
    · exact ih _ htail

def insert {C : Type} (key : C → Nat) (a : C) : List C → List C
  | [] => [a]
  | b::t => if key a≤key b then a::b::t else b::insert key a t

def offers {C : Type} (key : C → Nat) (L : List C) : List C :=
  L.foldr (insert key) []

def orderedCommands (g : Pair LongGeometry) : List CommandClaim :=
  select Claim.slots [] (offers commandKey (commandClaims g))

/-- Preparation reservations are lane-wide, not just byte masks.
Drop colliding offers first; order remaining END before HOP. -/
def orderedData (g : Pair LongGeometry) (reserved : List (At Sheet)) : List DataClaim :=
  select Claim.slots reserved (offers dataKey (dataClaims g))

private def geo (h ins last : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,ins,last,0,false⟩

/-- Both visits of the same seam are present, with their terminal and
door incidences on R only. Left.END still bids on a separate local turn. -/
theorem seam_fixture :
    orderedCommands (geo false true true,geo true true false) =
      [⟨.door,R 0,none⟩,⟨.terminal,R 10,none⟩,
       link (L 0) (R 1),link (L 1) (R 2),link (L 2) (L 3),
       link (R 3) (L 4),link (R 4) (L 5),link (R 5) (R 6),
       link (L 6) (R 7),link (L 7) (R 8),link (L 8) (L 9),link (R 9) (L 10)] ∧
    orderedData (geo false true true,geo true true false) [] =
      [ending (L .ld),ending (R .rd),hop (L .ls) (R .ld),hop (R .rs) (L .rd)] := by
  decide +kernel

/-- LAST is a stale byte when !IN; an off-IN right seam still gets the
door/terminal and END(R.RD), but neither of the two prefix hops. -/
theorem stale_seam_fixture :
    orderedCommands (geo true false true,geo true false true) =
      [⟨.door,R 0,none⟩,⟨.terminal,R 10,none⟩,
       link (L 0) (R 1),link (L 1) (R 2),link (L 2) (L 3),
       link (R 3) (L 4),link (R 4) (L 5),link (R 5) (R 6),link (L 6) (R 7)] ∧
    orderedData (geo true false true,geo true false true) [] = [ending (R .rd)] ∧
    discarded (geo true false true,geo true false true)=[L 8,L 9,R 8,R 9] := by
  decide +kernel

theorem body_fixture :
    orderedCommands (geo true true false,geo false true true) =
      [link (L 0) (R 0),link (L 1) (R 1),link (L 2) (R 2),
       link (R 3) (L 3),link (R 4) (L 4),link (R 5) (L 5),
       link (L 6) (R 6),link (L 7) (R 7),link (L 8) (R 8),
       link (R 9) (L 9),link (R 10) (L 10)] ∧
    orderedData (geo true true false,geo false true true) [R .ld] =
      [hop (L .ls) (R .ls),hop (R .rs) (L .rs),hop (R .rd) (L .rd)] := by
  decide +kernel

private theorem reduceGeometry (x y : LongGeometry) :
    commandClaims (x,y) =
      commandClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) ∧
    dataClaims (x,y) =
      dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) ∧
    discarded (x,y) =
      discarded (geo false x.inside x.last,geo y.axes.h6 y.inside false) := by
  exact ⟨rfl,rfl,rfl⟩

/-- Across every meaningful Boolean geometry mask, no command slot is
used twice, including the stale off-IN cleanup geometry. This theorem
is universal in all unexamined raw cache/prefix fields. -/
theorem geometry_exhaustive (x y : LongGeometry) :
    (((orderedCommands (x,y)).flatMap Claim.slots)++discarded (x,y)).Nodup ∧
      ((orderedData (x,y) []).flatMap Claim.slots).Nodup := by
  obtain ⟨a,b,c⟩ := reduceGeometry x y
  unfold orderedCommands orderedData
  rw [a,b,c]
  generalize x.inside=ix
  generalize x.last=lx
  generalize y.axes.h6=hy
  generalize y.inside=iy
  cases ix <;> cases lx <;> cases hy <;> cases iy <;> decide +kernel

theorem data_reservations (g : Pair LongGeometry) (reserved : List (At Sheet)) :
    (orderedData g reserved).Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots) ∧
    ∀ c∈orderedData g reserved, ∀ s∈c.slots, s∉reserved :=
  ⟨select_pairwise ..,select_away Claim.slots reserved (offers dataKey (dataClaims g))⟩

theorem mem_insert {C : Type} (key : C → Nat) (a b : C) (L : List C) :
    b∈insert key a L ↔ b=a ∨ b∈L := by
  induction L with
  | nil => simp [insert]
  | cons c cs ih =>
    unfold insert
    split
    · exact List.mem_cons
    · simp only [List.mem_cons,ih,or_left_comm]

theorem insert_sorted {C : Type} (key : C → Nat) (a : C) (L : List C)
    (h : L.Pairwise (fun x y => key x≤key y)) :
    (insert key a L).Pairwise (fun x y => key x≤key y) := by
  induction L with
  | nil => simp [insert]
  | cons b bs ih =>
    obtain ⟨hb,hs⟩ := List.pairwise_cons.mp h
    unfold insert
    split
    · rename_i ha
      refine List.pairwise_cons.mpr ⟨?_,h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl|hz
      · exact ha
      · exact Nat.le_trans ha (hb _ hz)
    · rename_i ha
      refine List.pairwise_cons.mpr ⟨?_,ih hs⟩
      intro z hz
      rcases (mem_insert key a z bs).mp hz with rfl|hz
      · omega
      · exact hb _ hz

theorem offers_sorted {C : Type} (key : C → Nat) (L : List C) :
    (offers key L).Pairwise (fun a b => key a≤key b) := by
  induction L with
  | nil => exact .nil
  | cons a L ih => exact insert_sorted key a (offers key L) ih

theorem orderedCommands_sorted (g : Pair LongGeometry) :
    (orderedCommands g).Pairwise (fun a b => commandKey a≤commandKey b) :=
  (offers_sorted commandKey (commandClaims g)).sublist (select_sublist ..)

theorem orderedData_sorted (g : Pair LongGeometry) (reserved : List (At Sheet)) :
    (orderedData g reserved).Pairwise (fun a b => dataKey a≤dataKey b) :=
  (offers_sorted dataKey (dataClaims g)).sublist (select_sublist ..)

inductive Prep where
  | clear | rclear | stop | rstop | load | inject | enable
  deriving DecidableEq, Repr

def Prep.priority : Prep → Nat
  | .clear | .rclear => 0
  | .stop | .rstop => 1
  | .load => 2
  | .inject => 3
  | .enable => 4

def prepSites (x : LongGeometry) (j : Fin 11) (op : Prep) : List Sheet :=
  match op with
  | .load => if x.inside then
      if j=0 then [.ls] else if j=2 then [.rs] else []
    else []
  | .inject => if x.inside then
      if j=5 then [.ls] else if j=2 then [.rs] else []
    else []
  | _ => if j=0 then [.ls]
      else if j=1 then (if x.inside then [.ld,.rd] else [.rd])
      else if j=2 && x.inside then [.rs] else []

structure PrepClaim where
  op : Prep
  origin : At (Fin 11)
  lane : At Sheet
  deriving DecidableEq, Repr

def prepClaims (x : LongGeometry) (s : At (Fin 11)) (op : Prep) : List PrepClaim :=
  (prepSites x s.occurrence op).map (fun l => ⟨op,s,⟨s.side,l⟩⟩)

def prepKey (p : PrepClaim) : Nat :=
  (2*p.lane.occurrence.key+p.lane.side.key)*120+
    24*p.op.priority+2*p.origin.occurrence.val+p.origin.side.key

def reserve (p : PrepClaim) : List (At Sheet) := [p.lane]

def orderedPrep (L : List PrepClaim) : List PrepClaim :=
  select reserve [] (offers prepKey L)

theorem prep_lane_unique (L : List PrepClaim) : ((orderedPrep L).map PrepClaim.lane).Nodup := by
  have H := select_flatten_nodup reserve [] (offers prepKey L) (by intro c hc; simp [reserve])
  have W (xs : List PrepClaim) : xs.flatMap reserve=xs.map PrepClaim.lane := by
    induction xs with
    | nil => rfl
    | cons c t ih => simp [reserve,ih]
  rw [W] at H
  exact H

/-- The winner is charged its lane without consulting its execution
result. In particular a failed winning CLEAR/LOAD is not released to
the dependent data-claim fold. -/
def reservedLanes (L : List PrepClaim) : List (At Sheet) :=
  (orderedPrep L).map PrepClaim.lane

theorem orderedData_after_prep (g : Pair LongGeometry) (P : List PrepClaim) :
    ∀ d∈orderedData g (reservedLanes P), ∀ s∈d.slots,
      s∉reservedLanes P :=
  (data_reservations g (reservedLanes P)).2

end L4.BStarLongClaims
