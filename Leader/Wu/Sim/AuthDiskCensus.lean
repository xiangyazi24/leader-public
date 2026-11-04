import Lean.Data.Json
import Std.Data.HashMap
import Leader.Wu.Sim.AuthCarrier

/-!
# Disk-backed per-seed closure census for AuthF (copy of `PPLLDiskCensus`)

Copy of `Leader/Wu/Sim/DiskClosureCensus.lean` (that file is an executable root with its own `main`,
so it cannot be imported) with three changes: the agent carrier is
`PPLLAuthSim.AuthB` (bounded core + AuthF provenance sidecars) with its codec and
local transition; layer records store agent indices as `u32` (records `4n + 5`
bytes), since the marks multiply the number of distinct agents; `--keybits` may be up
to 32 (exact keys while `n` fields of `W` bits fit in 128 bits, else fingerprint128).
Everything below the carrier (BFS, visited table, witnesses, fixpoint, bottom SCC) is
unchanged.  The original documentation follows.


Design-exploration tool (board G6.2), not a proof certificate.  Same successor
relation as `PPLLClosureCensus` (the ring census on rotation classes): for a
configuration `c` on the directed ring of `n` agents, the successor at edge `e`
replaces cells `e, e+1 mod n` by the local transition of the chosen variant on
`(c e, c (e+1 mod n))`, and configurations are identified with their least
rotation (`canon`, same order and tie-breaking as `PPLLClosureCensus.canon`).
`localTransition` and `reify` are copied verbatim from the census build used
for the G6.2 Z-div runs (variant families in the same lookup order).

What changes is only where the states live.

* **Visited set.**  An open-addressing table of 16-byte keys in one flat
  `ByteArray` (linear probing, load factor at most 3/4, so about 21 bytes of
  RAM per class).  If the least rotation fits in 128 bits (`n` fields of
  `W` bits each, `W = --keybits`, holding agent index + 1, at most `64 / W`
  fields per 64-bit word) the key *is* the state, so the table is exact.
  Otherwise the key is a 128-bit fingerprint (two independent 64-bit chained
  mixes), i.e. hash compaction: a collision silently merges two classes, with
  probability at most `N² / 2¹²⁹` for `N` classes under the random-hash model;
  `summary.json` reports the mode and that bound.
* **Frontier and states on disk.**  BFS layer `d` of a seed is the file
  `L{d}.bin` of fixed-size records `(least rotation as n × u16, parent slot
  u32, edge u8)` in discovery order; the parent slot and the edge (in the
  parent's canonical coordinates) give a shortest witness path.  Edges out of
  leaderless classes go to `E{d}.bin` as `(slot, n successor slots)` with
  successors that carry a leader replaced by `0xFFFFFFFF`.
* `--noedges` skips the `E` files (layer files only, `2n + 5` bytes per class);
  the leaderless fixpoint and the bottom-SCC search are then not run.
* **Per-seed budgets.**  By default every seed gets a fresh table and its own
  class budget `CAP`, so one seed cannot starve the others; `--shared` keeps
  one table across seeds (the union census of `PPLLClosureCensus`, used for
  the cross-check), and `--graph` (shared only, small runs) also writes the
  legacy `nodes.txt` / `edges.txt` / `unexpanded.txt` / `seeds.txt` files.
* **Streaming analysis.**  Per seed the tool itself reports the reachable
  class count, completeness, depth, max / min leader count, the number of
  multi-leader and leaderless classes, and a shortest witness edge word (on the
  seed's own site numbering, replayed and re-checked physically) to the first
  multi-leader class and the first leaderless class.  For a leaderless class
  the question "is a leaderless bottom SCC reached" is decided without the
  graph in RAM: a class reaches a leaderless bottom SCC iff its forward closure
  contains no leader, so it suffices to compute, by a fixpoint over the
  streamed `E` files, the leaderless classes that reach a leader; any other
  leaderless class of a *complete* closure lies above a leaderless bottom SCC.
* **Stop predicate.**  `--stop leader` ends a seed at the first class with a
  leader, `--stop leader_or_hole` at the first class with a leader or a cell
  with `path = none`; the witness word to that class is recorded and the
  outcome is `target_found`.  A seed whose closure completes without a target
  (`complete_without_target`) is leaderless throughout; the tool then also
  locates one bottom SCC below the seed (see `bottomScc`) and records its size
  and a witness word to one of its members.  Otherwise `budget_exhausted`.
  A transition output outside the bounded domain ends that seed with outcome
  `error` (the run continues).
* **Resumable.**  After every completed layer `ckpt.json` records the seed,
  the per-seed statistics and the layer sizes; the table is rebuilt on restart
  by re-inserting the layer files in order (same capacity and insertion order,
  hence the same slots, so stored parent slots stay valid).
* **Disk guard.**  Before each layer and every 64 MiB written, the free space
  of the work directory (`df`) must stay above `--minfree` GiB; otherwise the
  seed stops with status `disk_cap` (and the run stops if even a fresh seed
  has no room).  Each seed's layer files are removed when the next seed starts
  (per-seed mode); they are regenerable intermediates inside the work dir.

Usage:
`ppll-disk-census VARIANT N PSI KAPPA CAP SEEDS.jsonl OUTDIR WORKDIR
   [--shared] [--graph] [--from A] [--to B] [--only i,j,…] [--keybits W] [--minfree GiB]
   [--stop none|leader|leader_or_hole] [--noedges] [--scclimit N]`

Outputs in OUTDIR: `results.jsonl` (one line per finished seed: outcome,
reachable classes, depth, leader counts, witnesses with physical edge words
and final configurations, bottom SCC), `seedlog.json` (the same as one array)
and `summary.json` at the end, `agents.jsonl`, `ckpt.json`; with `--graph`
also the legacy `nodes.txt`, `edges.txt`, `unexpanded.txt`, `seeds.txt`
read by `analyze.py` / `analyze_census.py`.
-/

set_option autoImplicit false

open Lean

namespace PPLLAuthCensus

abbrev Agent (ψ κ : Nat) := PPLLAuthSim.AuthB ψ κ

def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) :=
  PPLLAuthSim.localTransition variant hψ κ

/-! ## Byte helpers (little endian) -/

@[inline] def rd16 (b : ByteArray) (o : Nat) : Nat :=
  (b.get! o).toNat + (b.get! (o + 1)).toNat * 256

@[inline] def rd32 (b : ByteArray) (o : Nat) : UInt32 :=
  (b.get! o).toUInt32 ||| ((b.get! (o + 1)).toUInt32 <<< 8) |||
    ((b.get! (o + 2)).toUInt32 <<< 16) ||| ((b.get! (o + 3)).toUInt32 <<< 24)

@[inline] def rd64 (b : ByteArray) (o : Nat) : UInt64 :=
  (rd32 b o).toUInt64 ||| ((rd32 b (o + 4)).toUInt64 <<< 32)

@[inline] def wr32 (b : ByteArray) (o : Nat) (v : UInt32) : ByteArray :=
  let b := b.set! o v.toUInt8
  let b := b.set! (o + 1) (v >>> 8).toUInt8
  let b := b.set! (o + 2) (v >>> 16).toUInt8
  b.set! (o + 3) (v >>> 24).toUInt8

@[inline] def wr64 (b : ByteArray) (o : Nat) (v : UInt64) : ByteArray :=
  wr32 (wr32 b o v.toUInt32) (o + 4) (v >>> 32).toUInt32

@[inline] def push16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v % 256).toUInt8).push (v / 256 % 256).toUInt8

@[inline] def push32 (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8

/-- A zero-filled byte array of `n` bytes (read from `/dev/zero`, so that a
multi-gigabyte table is allocated by one system call). -/
def zeros (n : Nat) : IO ByteArray := do
  if n == 0 then return ByteArray.empty
  let h ← IO.FS.Handle.mk "/dev/zero" .read
  let b ← h.read n.toUSize
  if b.size != n then throw (IO.userError s!"zeros: short read {b.size} < {n}")
  return b

/-- Zero a byte array in place (1 MiB `copySlice` blocks), so that the
per-seed table is reused rather than reallocated. -/
def zeroFill (b : ByteArray) : IO ByteArray := do
  let z ← zeros (1 <<< 20)
  let mut b := b
  let mut off := 0
  while off < b.size do
    let len := min (1 <<< 20) (b.size - off)
    b := z.copySlice 0 b off len
    off := off + len
  return b

/-- Read until `n` bytes or end of file. -/
partial def readFull (h : IO.FS.Handle) (n : Nat) : IO ByteArray := do
  let b ← h.read n.toUSize
  if b.size == n || b.size == 0 then return b
  let rec go (acc : ByteArray) : IO ByteArray := do
    if acc.size ≥ n then return acc
    let c ← h.read (n - acc.size).toUSize
    if c.size == 0 then return acc
    go (acc ++ c)
  go b

/-- Next chunk of whole records of size `rs` (empty at end of file). -/
def readChunk (h : IO.FS.Handle) (rs : Nat) : IO ByteArray := do
  let b ← readFull h (rs * 65536)
  if b.size % rs != 0 then throw (IO.userError s!"truncated record file ({b.size} bytes, record {rs})")
  return b

/-- A long-lived `df` helper, spawned before the table is allocated: spawning
a process from a process with a large resident set costs time proportional to
its page tables, so the free-space guard must not fork from the big process. -/
structure DfHelper where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

def DfHelper.start : IO DfHelper := do
  let c ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "while read d; do df -B1 --output=avail \"$d\" | tail -n 1; done"]
      stdin := .piped, stdout := .piped, stderr := .inherit }
  return ⟨c⟩

/-- Free bytes of the file system holding `dir` (one query). -/
def DfHelper.free1 (h : DfHelper) (dir : System.FilePath) : IO Nat := do
  h.child.stdin.putStrLn dir.toString
  h.child.stdin.flush
  let l ← h.child.stdout.getLine
  match l.trimAscii.toString.toNat? with
  | some v => return v
  | none => throw (IO.userError s!"df helper output not understood: {l}")

/-- Free bytes, retried: a transient failure (the helper's `df` could not fork
under memory pressure) is retried up to 30 times, 2 s apart, before the error
is raised; the run can then be resumed from its checkpoint. -/
partial def DfHelper.free (h : DfHelper) (dir : System.FilePath) (tries : Nat := 30) : IO Nat := do
  try h.free1 dir
  catch e =>
    if tries == 0 then throw e
    IO.eprintln s!"free-space query failed ({e}); retrying"
    IO.sleep 2000
    h.free dir (tries - 1)

/-! ## The visited table -/

@[inline] def mix64 (x : UInt64) : UInt64 :=
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

@[inline] def slotStart (cap : Nat) (lo hi : UInt64) : Nat :=
  (mix64 (lo ^^^ mix64 (hi ^^^ 0x9E3779B97F4A7C15))).toNat % cap

/-- Linear probing from slot `s`: the slot holding `(lo, hi)` (`true`) or the
first empty slot (`false`).  Keys are never `(0, 0)`, which marks an empty
slot.  Terminates because the table is kept at most 3/4 full. -/
partial def probe (data : ByteArray) (cap : Nat) (lo hi : UInt64) (s : Nat) : Nat × Bool :=
  let o := s * 16
  let a := rd64 data o
  let b := rd64 data (o + 8)
  if a == lo && b == hi then (s, true)
  else if a == 0 && b == 0 then (s, false)
  else probe data cap lo hi (if s + 1 == cap then 0 else s + 1)

/-- The table lives in an `IO.Ref` and is only touched through `modifyGet`,
which takes the array out of the reference, so every write is in place (a
`ByteArray` threaded through nested `do` loops was copied once per layer). -/
@[inline] def tInsert (t : IO.Ref ByteArray) (cap : Nat) (lo hi : UInt64) : IO (Nat × Bool) :=
  t.modifyGet fun d =>
    let (s, found) := probe d cap lo hi (slotStart cap lo hi)
    if found then ((s, true), d) else ((s, false), wr64 (wr64 d (s * 16) lo) (s * 16 + 8) hi)

@[inline] def tFind (t : IO.Ref ByteArray) (cap : Nat) (lo hi : UInt64) : IO (Nat × Bool) :=
  t.modifyGet fun d => (probe d cap lo hi (slotStart cap lo hi), d)

/-- Key mode: `exact` packs the `n` agent fields (index + 1, `w` bits each,
`per` fields per word) into 128 bits; otherwise a 128-bit fingerprint. -/
structure KeyMode where
  exact : Bool
  w : Nat
  per : Nat

def keyOf (km : KeyMode) (c : Array Nat) : UInt64 × UInt64 := Id.run do
  if km.exact then
    let mut lo : UInt64 := 0
    let mut hi : UInt64 := 0
    for j in [0:c.size] do
      let v := (c[j]! + 1).toUInt64
      if j < km.per then lo := (lo <<< km.w.toUInt64) ||| v
      else hi := (hi <<< km.w.toUInt64) ||| v
    return (lo, hi)
  else
    let mut h1 : UInt64 := 0x243F6A8885A308D3
    let mut h2 : UInt64 := 0x13198A2E03707344
    for j in [0:c.size] do
      let v := (c[j]! + 1).toUInt64
      h1 := mix64 (h1 ^^^ (v * 0x9E3779B97F4A7C15))
      h2 := mix64 (h2 + v * 0xC2B2AE3D27D4EB4F + 0x165667B19E3779F9)
    if h1 == 0 && h2 == 0 then return (1, 0) else return (h1, h2)

/-! ## Agents, memoised local transition, rotation classes -/

structure Ag (ψ κ : Nat) where
  arr : Array (Agent ψ κ) := #[]
  ix : Std.HashMap String Nat := {}
  lead : Array Bool := #[]
  hole : Array Bool := #[]
  memo : Std.HashMap UInt64 UInt64 := {}

def Ag.intern {ψ κ : Nat} (g : Ag ψ κ) (a : Agent ψ κ) : Ag ψ κ × Nat :=
  let key := PPLLAuthSim.key a
  match g.ix[key]? with
  | some i => (g, i)
  | none =>
    let i := g.arr.size
    let isHole : Bool := a.hole
    let g' : Ag ψ κ :=
      { arr := g.arr.push a, ix := g.ix.insert key i, lead := g.lead.push a.leader
        hole := g.hole.push isHole, memo := g.memo }
    (g', i)

/-- Interned local transition on the pair of agent indices `(x, y)`, memoised. -/
def Ag.step {ψ κ : Nat} (g : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ)) (x y : Nat) :
    Except String (Ag ψ κ × Nat × Nat) :=
  let key := (x.toUInt64 <<< 32) ||| y.toUInt64
  match g.memo[key]? with
  | some r => .ok (g, (r >>> 32).toNat, (r &&& 0xFFFFFFFF).toNat)
  | none =>
    match g.arr[x]?, g.arr[y]? with
    | some u, some v => do
      let q ← tr u v
      let (g1, ia) := g.intern q.1
      let (g2, ib) := g1.intern q.2
      pure ({ g2 with memo := g2.memo.insert key ((ia.toUInt64 <<< 32) ||| ib.toUInt64) }, ia, ib)
    | _, _ => .error "agent index out of range"

def leaders {ψ κ : Nat} (g : Ag ψ κ) (c : Array Nat) : Nat :=
  c.foldl (fun acc i => if g.lead[i]! then acc + 1 else acc) 0

/-- Stop predicate of a class: `0` none, `1` some cell is a leader, `2` some
cell is a leader or has `path = none` (a main-path hole). -/
def isTarget {ψ κ : Nat} (g : Ag ψ κ) (mode : Nat) (c : Array Nat) : Bool :=
  mode != 0 && c.any fun i => g.lead[i]! || (mode == 2 && g.hole[i]!)

/-- Is rotation `k` of `c` lexicographically smaller than rotation `b`? -/
def rotLess (c : Array Nat) (k b : Nat) : Bool := Id.run do
  let n := c.size
  for j in [0:n] do
    let x := c[(k + j) % n]!
    let y := c[(b + j) % n]!
    if x < y then return true
    if y < x then return false
  return false

/-- Least rotation, rotation `k` being `c[k], …, c[n-1], c[0], …, c[k-1]`;
the same array as `PPLLClosureCensus.canon` (strict comparison, first minimum). -/
def canon (c : Array Nat) : Array Nat := Id.run do
  let n := c.size
  let mut best := 0
  for k in [1:n] do
    if rotLess c k best then best := k
  if best == 0 then return c
  return Array.ofFn (n := n) fun j => c[(best + j.val) % n]!

/-! ## Layer records -/

def encRec (b : ByteArray) (c : Array Nat) (parent : UInt32) (e : Nat) : ByteArray := Id.run do
  let mut b := b
  for x in c do b := push32 b x.toUInt32
  b := push32 b parent
  return b.push e.toUInt8

def decState (b : ByteArray) (o n : Nat) : Array Nat :=
  Array.ofFn (n := n) fun j => (rd32 b (o + 4 * j.val)).toNat

def rootParent : UInt32 := 0xFFFFFFFF

/-- Per-seed statistics over the classes discovered so far. -/
structure Stats where
  count : Nat := 0
  expanded : Nat := 0
  maxL : Nat := 0
  minL : Nat := 0
  leaderless : Nat := 0
  multi : Nat := 0
  firstMulti : Option (Nat × Nat) := none
  firstLeaderless : Option (Nat × Nat) := none
  firstTarget : Option (Nat × Nat) := none
  layers : Array Nat := #[]
  deriving ToJson, FromJson, Inhabited

def Stats.note (s : Stats) (l : Nat) (pos : Nat × Nat) : Stats :=
  { s with
    count := s.count + 1
    maxL := max s.maxL l
    minL := if s.count == 0 then l else min s.minL l
    leaderless := if l == 0 then s.leaderless + 1 else s.leaderless
    multi := if l ≥ 2 then s.multi + 1 else s.multi
    firstMulti := if l ≥ 2 && s.firstMulti.isNone then some pos else s.firstMulti
    firstLeaderless := if l == 0 && s.firstLeaderless.isNone then some pos else s.firstLeaderless }

def layerPath (dir : System.FilePath) (d : Nat) : System.FilePath := dir / s!"L{d}.bin"
def edgePath (dir : System.FilePath) (d : Nat) : System.FilePath := dir / s!"E{d}.bin"

/-- Re-insert the records of a layer file into the table (resume). Every record
must be new, since each class is stored in exactly one layer. -/
def reinsert (path : System.FilePath) (n cap : Nat) (km : KeyMode)
    (tref : IO.Ref ByteArray) (tcount : Nat) : IO Nat := do
  let rs := 4 * n + 5
  let h ← IO.FS.Handle.mk path .read
  let mut tcount := tcount
  let mut buf ← readChunk h rs
  while buf.size > 0 do
    let mut off := 0
    while off < buf.size do
      let c := decState buf off n
      let (lo, hi) := keyOf km c
      let (_, found) ← tInsert tref cap lo hi
      if found then throw (IO.userError s!"resume: duplicate class in {path}")
      tcount := tcount + 1
      off := off + rs
    buf ← readChunk h rs
  return tcount

/-- The record with index `idx` of a layer file. -/
def recordAt (path : System.FilePath) (rs idx : Nat) : IO ByteArray := do
  let h ← IO.FS.Handle.mk path .read
  let mut base := 0
  let mut buf ← readChunk h rs
  while buf.size > 0 do
    let k := buf.size / rs
    if idx < base + k then
      let o := (idx - base) * rs
      return buf.extract o (o + rs)
    base := base + k
    buf ← readChunk h rs
  throw (IO.userError s!"record {idx} not in {path}")

/-- The record of a layer file whose class occupies table slot `slot`. -/
def recordBySlot? (path : System.FilePath) (n cap : Nat) (km : KeyMode) (tdata : ByteArray)
    (slot : Nat) : IO (Option (Nat × ByteArray)) := do
  let rs := 4 * n + 5
  let h ← IO.FS.Handle.mk path .read
  let mut base := 0
  let mut buf ← readChunk h rs
  while buf.size > 0 do
    let mut off := 0
    while off < buf.size do
      let c := decState buf off n
      let (lo, hi) := keyOf km c
      if (probe tdata cap lo hi (slotStart cap lo hi)).1 == slot then
        return some (base + off / rs, buf.extract off (off + rs))
      off := off + rs
    base := base + buf.size / rs
    buf ← readChunk h rs
  return none

def recordBySlot (path : System.FilePath) (n cap : Nat) (km : KeyMode) (tdata : ByteArray)
    (slot : Nat) : IO (Nat × ByteArray) := do
  match ← recordBySlot? path n cap km tdata slot with
  | some r => return r
  | none => throw (IO.userError s!"slot {slot} not in {path}")

/-- Layer and index of the class in slot `slot` (scanning the layer files). -/
def locateSlot (dir : System.FilePath) (nl n cap : Nat) (km : KeyMode) (tdata : ByteArray)
    (slot : Nat) : IO (Nat × Nat) := do
  for d in [0:nl] do
    if let some (i, _) ← recordBySlot? (layerPath dir d) n cap km tdata slot then return (d, i)
  throw (IO.userError s!"slot {slot} in no layer")

/-! ## A bottom SCC below a class, from the streamed `E` files

The `E` files hold every expanded leaderless class with its successors.  Starting
from a class `x` whose forward closure lies inside them (a class of a complete
leaderless closure, or a leaderless class reaching no leader), repeat: compute
the forward closure `F` of `x`; if every class of `F` reaches `x` back, `F` is a
bottom SCC; otherwise move `x` to a class of `F` that does not reach `x`, whose
forward closure is a proper subset of `F`.  The graph is loaded as flat `u32`
arrays (about `8n + 20` bytes per class), only up to `limit` classes. -/

def bitGet (b : ByteArray) (x : Nat) : Bool := (b.get! (x / 8)) &&& ((1 : UInt8) <<< (x % 8).toUInt8) != 0

def bottomScc (dir : System.FilePath) (nl n cap limit startSlot : Nat) :
    IO (Except String (Nat × Nat × Nat)) := do
  let es := 4 * (n + 1)
  let exit : UInt32 := 0xFFFFFFFF
  let mut map ← zeros (cap * 4)
  let mut idSlot := ByteArray.empty
  let mut N := 0
  for d in [0:nl] do
    if !(← (edgePath dir d).pathExists) then continue
    let h ← IO.FS.Handle.mk (edgePath dir d) .read
    let mut b ← readChunk h es
    while b.size > 0 do
      let mut o := 0
      while o < b.size do
        let x := (rd32 b o).toNat
        map := wr32 map (x * 4) (N + 1).toUInt32
        idSlot := push32 idSlot x.toUInt32
        N := N + 1
        o := o + es
      if N > limit then return .error s!"more than {limit} leaderless classes"
      b ← readChunk h es
  let m0 := (rd32 map (startSlot * 4)).toNat
  if m0 == 0 then return .error "start class has no edge record"
  let mut succ := ByteArray.emptyWithCapacity (N * n * 4)
  for d in [0:nl] do
    if !(← (edgePath dir d).pathExists) then continue
    let h ← IO.FS.Handle.mk (edgePath dir d) .read
    let mut b ← readChunk h es
    while b.size > 0 do
      let mut o := 0
      while o < b.size do
        for k in [0:n] do
          let y := rd32 b (o + 4 + 4 * k)
          let v := if y == exit then exit else
            let m := rd32 map (y.toNat * 4)
            if m == 0 then exit else m - 1
          succ := push32 succ v
        o := o + es
      b ← readChunk h es
  map := ByteArray.empty
  -- reverse adjacency (counting sort)
  let mut cnt ← zeros ((N + 1) * 4)
  for q in [0:N * n] do
    let v := rd32 succ (q * 4)
    if v != exit then
      let i := (v.toNat + 1) * 4
      cnt := wr32 cnt i (rd32 cnt i + 1)
  for i in [1:N + 1] do
    cnt := wr32 cnt (i * 4) (rd32 cnt (i * 4) + rd32 cnt ((i - 1) * 4))
  let mut fill := cnt.extract 0 cnt.size
  let mut rev ← zeros (N * n * 4)
  for q in [0:N * n] do
    let v := rd32 succ (q * 4)
    if v != exit then
      let p := (rd32 fill (v.toNat * 4)).toNat
      rev := wr32 rev (p * 4) (q / n).toUInt32
      fill := wr32 fill (v.toNat * 4) (p + 1).toUInt32
  fill := ByteArray.empty
  let mut mark ← zeros (N * 4)
  let mut q1 ← zeros (N * 4)
  let mut q2 ← zeros (N * 4)
  let mut epoch : UInt32 := 0
  let mut x := m0 - 1
  let mut iters := 0
  while true do
    iters := iters + 1
    epoch := epoch + 2
    -- forward closure F of x
    mark := wr32 mark (x * 4) epoch
    q1 := wr32 q1 0 x.toUInt32
    let mut head := 0
    let mut tail := 1
    while head < tail do
      let u := (rd32 q1 (head * 4)).toNat
      head := head + 1
      for k in [0:n] do
        let v := rd32 succ ((u * n + k) * 4)
        if v == exit then return .error "closure leaves the recorded leaderless classes"
        if rd32 mark (v.toNat * 4) != epoch then
          mark := wr32 mark (v.toNat * 4) epoch
          q1 := wr32 q1 (tail * 4) v
          tail := tail + 1
    let f := tail
    -- backward closure of x inside F
    mark := wr32 mark (x * 4) (epoch + 1)
    q2 := wr32 q2 0 x.toUInt32
    let mut h2 := 0
    let mut t2 := 1
    while h2 < t2 do
      let u := (rd32 q2 (h2 * 4)).toNat
      h2 := h2 + 1
      for p in [(rd32 cnt (u * 4)).toNat:(rd32 cnt ((u + 1) * 4)).toNat] do
        let v := (rd32 rev (p * 4)).toNat
        if rd32 mark (v * 4) == epoch then
          mark := wr32 mark (v * 4) (epoch + 1)
          q2 := wr32 q2 (t2 * 4) v.toUInt32
          t2 := t2 + 1
    if t2 == f then return .ok (f, (rd32 idSlot (x * 4)).toNat, iters)
    let mut y := x
    for i in [0:f] do
      let v := (rd32 q1 (i * 4)).toNat
      if rd32 mark (v * 4) == epoch then
        y := v
        break
    x := y
  return .error "unreachable"

/-- Shortest BFS path from the seed to record `idx` of layer `t`: the canonical
classes `s₀ … s_t` and the edges `e₁ … e_t` (edge `e_k` in the canonical
coordinates of `s_{k-1}`). -/
def pathTo (dir : System.FilePath) (n cap : Nat) (km : KeyMode) (tdata : ByteArray)
    (t idx : Nat) : IO (Array (Array Nat) × Array Nat) := do
  let rs := 4 * n + 5
  let r ← recordAt (layerPath dir t) rs idx
  let mut states : Array (Array Nat) := #[decState r 0 n]
  let mut edges : Array Nat := if t == 0 then #[] else #[(r.get! (4 * n + 4)).toNat]
  let mut parent := rd32 r (4 * n)
  let mut l := t
  while l > 0 do
    l := l - 1
    let (_, p) ← recordBySlot (layerPath dir l) n cap km tdata parent.toNat
    states := states.push (decState p 0 n)
    if l > 0 then edges := edges.push (p.get! (4 * n + 4)).toNat
    parent := rd32 p (4 * n)
  if parent != rootParent then throw (IO.userError "witness path does not end at the seed")
  return (states.reverse, edges.reverse)

/-- Replay a canonical path on the seed's physical configuration: at each step
find a rotation `k` with `rot_k phys = s_{j-1}`, fire the physical edge
`e + k mod n`, and check that the result is in class `s_j`.  Returns the
physical edge word and the final physical configuration. -/
def replay {ψ κ : Nat} (g : Ag ψ κ)
    (tr : Agent ψ κ → Agent ψ κ → Except String (Agent ψ κ × Agent ψ κ))
    (phys0 : Array Nat) (states : Array (Array Nat)) (edges : Array Nat) :
    IO (Ag ψ κ × Array Nat × Array Nat) := do
  let n := phys0.size
  let mut g := g
  let mut phys := phys0
  let mut word : Array Nat := #[]
  if canon phys != states[0]! then throw (IO.userError "replay: seed is not s₀")
  for j in [0:edges.size] do
    let cp := states[j]!
    let some k := (List.range n).find? (fun k => (List.range n).all fun m => phys[(m + k) % n]! == cp[m]!)
      | throw (IO.userError "replay: no rotation matches")
    let i := (edges[j]! + k) % n
    let (g', a, b) ← IO.ofExcept (g.step tr phys[i]! phys[(i + 1) % n]!)
    g := g'
    phys := (phys.set! i a).set! ((i + 1) % n) b
    word := word.push i
    if canon phys != states[j + 1]! then throw (IO.userError s!"replay: step {j} leaves the class")
  return (g, word, phys)

def witnessJson {ψ κ : Nat} (g : Ag ψ κ) (kind : String) (layer : Nat) (word phys : Array Nat) :
    Json :=
  Json.mkObj
    [ ("kind", kind), ("length", layer), ("word", toJson word)
    , ("final_leaders", leaders g phys)
    , ("final", Json.arr ((phys.filterMap fun i => g.arr[i]?).map PPLLAuthSim.encode)) ]

/-! ## The census -/

def run (variant : String) (n ψ κ budget : Nat) (seedPath outDir work : System.FilePath)
    (shared graph : Bool) (seedFrom seedTo w minFreeGiB : Nat) (stopMode : Nat) (only : Array Nat)
    (sccLimit : Nat) (noEdges : Bool) : IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← match localTransition variant hψ κ with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    if n < 2 then throw (IO.userError "n must be at least 2")
    if graph && !shared then throw (IO.userError "--graph requires --shared")
    if w == 0 || w > 32 then throw (IO.userError "--keybits must be in 1..32")
    let per := 64 / w
    let km : KeyMode := ⟨n ≤ 2 * per, w, per⟩
    let maxAgents := if km.exact then 2 ^ w - 1 else 2 ^ 31
    let cap := budget * 4 / 3 + 16
    if cap ≥ 2 ^ 32 - 1 then throw (IO.userError "CAP too large for 32-bit slots")
    let rs := 4 * n + 5
    let es := 4 * (n + 1)
    let minFree := minFreeGiB * 1024 * 1024 * 1024
    IO.FS.createDirAll outDir
    IO.FS.createDirAll work
    let ckptPath := outDir / "ckpt.json"
    let params := Json.mkObj
      [ ("variant", variant), ("n", n), ("psi", ψ), ("kappa", κ), ("cap", budget)
      , ("seeds", seedPath.toString), ("shared", shared), ("keybits", w)
      , ("from", seedFrom), ("to", seedTo), ("work", work.toString)
      , ("stop", stopMode), ("only", toJson only), ("noedges", noEdges) ]
    let mut ag : Ag ψ κ := {}
    let mut results : Array Json := #[]
    let mut startSeed := seedFrom
    let mut resume : Option Stats := none
    if !graph && (← ckptPath.pathExists) then
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile ckptPath))
      if (j.getObjValD "params").compress != params.compress then
        throw (IO.userError s!"{ckptPath} belongs to a run with other parameters")
      let na ← IO.ofExcept (j.getObjValAs? Nat "agents")
      let lines ← IO.FS.lines (outDir / "agents.jsonl")
      if lines.size < na then throw (IO.userError "agents.jsonl shorter than the checkpoint")
      for k in [0:na] do
        let a ← IO.ofExcept (PPLLAuthSim.decode (ψ := ψ) (κ := κ)
          (← IO.ofExcept (Json.parse lines[k]!)))
        if (PPLLAuthSim.encode a).compress != lines[k]! then
          throw (IO.userError s!"agent {k} does not round-trip")
        let (g, i) := ag.intern a
        ag := g
        if i != k then throw (IO.userError s!"agent {k} duplicated")
      let nr ← IO.ofExcept (j.getObjValAs? Nat "results_count")
      let rl ← IO.FS.lines (outDir / "results.jsonl")
      if rl.size < nr then throw (IO.userError "results.jsonl shorter than the checkpoint")
      for k in [0:nr] do results := results.push (← IO.ofExcept (Json.parse rl[k]!))
      startSeed ← IO.ofExcept (j.getObjValAs? Nat "seed")
      match j.getObjValD "current" with
      | .null => pure ()
      | cur => resume := some (← IO.ofExcept (fromJson? cur))
      IO.eprintln s!"resuming at seed {startSeed}, {results.size} seeds done, {na} agents"
    -- seeds, in file order, as interned physical configurations
    let mut seedsPhys : Array (Array Nat) := #[]
    for line in (← IO.FS.lines seedPath) do
      if line.trimAscii.toString.isEmpty then continue
      let j ← IO.ofExcept (Json.parse line)
      let cfg ← IO.ofExcept (PPLLAuthSim.decodeConfig (ψ := ψ) (κ := κ) n j)
      let mut c : Array Nat := #[]
      for a in cfg do
        let (g, i) := ag.intern a
        ag := g
        c := c.push i
      seedsPhys := seedsPhys.push c
    let seedEnd := min seedTo seedsPhys.size
    -- results.jsonl holds one line per finished seed (the checkpoint records how many count)
    if !graph then
      IO.FS.writeFile (outDir / "results.jsonl") (String.join (results.toList.map (·.compress ++ "\n")))
    -- agents.jsonl holds exactly the first `agentsWritten` agents; later ones are appended
    let mut agentsWritten := 0
    if !graph then
      let h ← IO.FS.Handle.mk (outDir / "agents.jsonl") .write
      for a in ag.arr do h.putStrLn (PPLLAuthSim.encode a).compress
      h.flush
      agentsWritten := ag.arr.size
    let writeCkpt : Nat → Option Stats → Array Json → Ag ψ κ → Nat → IO Nat :=
      fun seed cur res g aw => do
        let mut aw := aw
        if g.arr.size != aw then
          let h ← IO.FS.Handle.mk (outDir / "agents.jsonl") .append
          for a in g.arr.extract aw g.arr.size do h.putStrLn (PPLLAuthSim.encode a).compress
          h.flush
          aw := g.arr.size
        let j := Json.mkObj
          [ ("params", params), ("agents", g.arr.size), ("seed", seed), ("results_count", res.size)
          , ("current", match cur with | some s => toJson s | none => Json.null) ]
        IO.FS.writeFile (outDir / "ckpt.json.tmp") (j.compress ++ "\n")
        IO.FS.rename (outDir / "ckpt.json.tmp") ckptPath
        return aw
    -- table and (graph mode) id maps
    let dfh ← DfHelper.start
    let freeBytes := fun d => dfh.free d
    let tref ← IO.mkRef (← zeros (cap * 16))
    let mut tcount := 0
    let mut idOf : ByteArray ← if graph then zeros (cap * 4) else pure ByteArray.empty
    let mut expd : ByteArray ← if graph then zeros cap else pure ByteArray.empty
    let mut gcount := 0
    let nodesH? ← if graph then some <$> IO.FS.Handle.mk (outDir / "nodes.txt") .write else pure none
    let edgesH? ← if graph then some <$> IO.FS.Handle.mk (outDir / "edges.txt") .write else pure none
    let mut seedIds : Array Nat := #[]
    if shared then
      -- resume: re-insert the finished seeds' layers in order
      for r in results do
        let si ← IO.ofExcept (r.getObjValAs? Nat "seed")
        let ls ← IO.ofExcept (r.getObjValAs? (Array Nat) "layers")
        for d in [0:ls.size] do
          tcount ← reinsert (layerPath (work / s!"s{si}") d) n cap km tref tcount
    let mut runStatus := "done"
    let mut sinceCheck := 0
    let tRun ← IO.monoMsNow
    for si in [startSeed:seedEnd] do
      if !only.isEmpty && !only.contains si then continue
      let t0 ← IO.monoMsNow
      let dir := if shared then work / s!"s{si}" else work / "cur"
      let resuming := resume.isSome && si == startSeed
      if !shared && !resuming && si != startSeed then
        let d ← tref.modifyGet fun d => (d, ByteArray.empty)
        tref.set (← zeroFill d)
        tcount := 0
      if !resuming then
        if (← dir.pathExists) then IO.FS.removeDirAll dir
      IO.FS.createDirAll dir
      if !resuming then
        if (← freeBytes work) < minFree + (1 <<< 30) then
          runStatus := "disk_cap"
          agentsWritten ← writeCkpt si none results ag agentsWritten
          IO.eprintln s!"stop: free space below {minFreeGiB} GiB + 1 GiB before seed {si}"
          break
      let mut stats : Stats := {}
      let before := tcount
      let mut covered := false
      if let some st := resume then
        if resuming then
          stats := st
          for d in [0:st.layers.size] do
            tcount ← reinsert (layerPath dir d) n cap km tref tcount
          resume := none
      if !resuming then
        let c0 := canon seedsPhys[si]!
        let (lo, hi) := keyOf km c0
        let (s, found) ← tInsert tref cap lo hi
        if found then
          covered := true
          if graph then seedIds := seedIds.push (rd32 idOf (s * 4)).toNat
        else
          tcount := tcount + 1
          let h ← IO.FS.Handle.mk (layerPath dir 0) .write
          h.write (encRec ByteArray.empty c0 rootParent 0)
          h.flush
          stats := (stats.note (leaders ag c0) (0, 0))
          stats := { stats with layers := #[1] }
          if isTarget ag stopMode c0 then stats := { stats with firstTarget := some (0, 0) }
          if graph then
            idOf := wr32 idOf (s * 4) gcount.toUInt32
            seedIds := seedIds.push gcount
            if let some nh := nodesH? then
              nh.putStrLn (" ".intercalate (toString (leaders ag c0) :: c0.toList.map toString))
            gcount := gcount + 1
      let mut errMsg : Option String := none
      let mut status := if stats.firstTarget.isSome then "target_found" else "complete"
      if !covered && stats.firstTarget.isNone then
        -- breadth-first search, one layer file at a time
        while stats.layers[stats.layers.size - 1]! > 0 do
          let d := stats.layers.size - 1
          if (← freeBytes work) < minFree then
            status := "disk_cap"
            break
          let rh ← IO.FS.Handle.mk (layerPath dir d) .read
          let lh ← IO.FS.Handle.mk (layerPath dir (d + 1)) .write
          let eh ← IO.FS.Handle.mk (edgePath dir d) .write
          let mut lbuf := ByteArray.emptyWithCapacity (1 <<< 22)
          let mut ebuf := ByteArray.emptyWithCapacity (1 <<< 22)
          let mut lrecs := 0
          let mut stop := false
          let mut buf ← readChunk rh rs
          while buf.size > 0 && !stop do
            let mut off := 0
            while off < buf.size do
              if tcount + n > budget then
                status := "seed_cap"; stop := true; break
              if sinceCheck ≥ (1 <<< 26) then
                sinceCheck := 0
                if (← freeBytes work) < minFree then
                  status := "disk_cap"; stop := true; break
              let c := decState buf off n
              off := off + rs
              let (lo, hi) := keyOf km c
              let sx := (← tFind tref cap lo hi).1
              let lc := leaders ag c
              let mut succ : Array Nat := #[]
              let mut ssl : Array Nat := #[]
              for e in [0:n] do
                let jx := (e + 1) % n
                let (g', a', b') ← match ag.step tr c[e]! c[jx]! with
                  | .ok r => pure r
                  | .error err =>
                    -- an out-of-domain transition output ends this seed, not the run
                    errMsg := some err; status := "error"; stop := true; break
                ag := g'
                if ag.arr.size > maxAgents then
                  throw (IO.userError s!"more than {maxAgents} agents; raise --keybits")
                let c' := canon ((c.set! e a').set! jx b')
                let (lo', hi') := keyOf km c'
                let (s, found) ← tInsert tref cap lo' hi'
                let l' := leaders ag c'
                if !found then
                  tcount := tcount + 1
                  lbuf := encRec lbuf c' sx.toUInt32 e
                  stats := stats.note l' (d + 1, lrecs)
                  lrecs := lrecs + 1
                  if isTarget ag stopMode c' then
                    stats := { stats with firstTarget := some (d + 1, lrecs - 1) }
                    status := "target_found"; stop := true
                  if graph then
                    idOf := wr32 idOf (s * 4) gcount.toUInt32
                    if let some nh := nodesH? then
                      nh.putStrLn (" ".intercalate (toString l' :: c'.toList.map toString))
                    gcount := gcount + 1
                if graph then succ := succ.push (rd32 idOf (s * 4)).toNat
                if lc == 0 then ssl := ssl.push (if l' > 0 then rootParent.toNat else s)
                if stop then break
              if stop then break
              if lc == 0 && !noEdges then
                ebuf := push32 ebuf sx.toUInt32
                for v in ssl do ebuf := push32 ebuf v.toUInt32
              if graph then
                let x := (rd32 idOf (sx * 4)).toNat
                expd := expd.set! x 1
                if let some eh' := edgesH? then
                  eh'.putStrLn (" ".intercalate (toString x :: succ.toList.map toString))
              stats := { stats with expanded := stats.expanded + 1 }
              if lbuf.size ≥ (1 <<< 22) then
                lh.write lbuf; sinceCheck := sinceCheck + lbuf.size
                lbuf := ByteArray.emptyWithCapacity (1 <<< 22)
              if ebuf.size ≥ (1 <<< 22) then
                eh.write ebuf; sinceCheck := sinceCheck + ebuf.size
                ebuf := ByteArray.emptyWithCapacity (1 <<< 22)
            if !stop then buf ← readChunk rh rs
          lh.write lbuf; lh.flush
          eh.write ebuf; eh.flush
          stats := { stats with layers := stats.layers.push lrecs }
          let el := (← IO.monoMsNow) - t0
          IO.eprintln s!"seed {si} layer {d + 1}: {lrecs} new, classes {stats.count}, expanded {stats.expanded}, {stats.expanded * 1000 / (max el 1)} exp/s, max leaders {stats.maxL}"
          if stop then break
          if !graph then agentsWritten ← writeCkpt si (some stats) results ag agentsWritten
      -- witnesses and the leaderless-bottom fixpoint
      let complete := status == "complete"
      let mut wits : Array Json := #[]
      if let some (t, idx) := stats.firstMulti then
        let (sts, es') ← pathTo dir n cap km (← tref.get) t idx
        let (g', word, phys) ← replay ag tr seedsPhys[si]! sts es'
        ag := g'
        wits := wits.push (witnessJson ag "multi_leader" t word phys)
      if let some (t, idx) := stats.firstLeaderless then
        let (sts, es') ← pathTo dir n cap km (← tref.get) t idx
        let (g', word, phys) ← replay ag tr seedsPhys[si]! sts es'
        ag := g'
        wits := wits.push (witnessJson ag "leaderless_first" t word phys)
      if let some (t, idx) := stats.firstTarget then
        let (sts, es') ← pathTo dir n cap km (← tref.get) t idx
        let (g', word, phys) ← replay ag tr seedsPhys[si]! sts es'
        ag := g'
        wits := wits.push (witnessJson ag (if stopMode == 1 then "leader" else "leader_or_hole") t word phys)
      let mut bottom : Json := Json.null
      let bottomWitness : Nat → Ag ψ κ → IO (Json × Ag ψ κ) := fun startSlot g => do
        match ← bottomScc dir stats.layers.size n cap sccLimit startSlot with
        | .error e => return (Json.mkObj [("error", e)], g)
        | .ok (size, rep, iters) =>
          let (d, idx) ← locateSlot dir stats.layers.size n cap km (← tref.get) rep
          let (sts, es') ← pathTo dir n cap km (← tref.get) d idx
          let (g', word, phys) ← replay g tr seedsPhys[si]! sts es'
          return (Json.mkObj [("size", size), ("iterations", iters),
            ("witness", witnessJson g' "bottom_scc_member" d word phys)], g')
      if stopMode != 0 && complete && stats.leaderless > 0 && !noEdges then
        -- complete closure without a target: every class is leaderless
        let (lo, hi) := keyOf km (canon seedsPhys[si]!)
        let sx := (← tFind tref cap lo hi).1
        let (j, g') ← bottomWitness sx ag
        ag := g'
        bottom := j
      let mut stuck : Option Nat := none
      if stats.leaderless > 0 && stats.firstTarget.isNone && !noEdges then
        let mut good ← zeros (cap / 8 + 1)
        let nl := stats.layers.size
        let mut changed := true
        let mut passes := 0
        while changed do
          changed := false
          passes := passes + 1
          for dd in [0:nl] do
            let d := nl - 1 - dd
            if !(← (edgePath dir d).pathExists) then continue
            let h ← IO.FS.Handle.mk (edgePath dir d) .read
            let mut b ← readChunk h es
            while b.size > 0 do
              let mut o := 0
              while o < b.size do
                let x := (rd32 b o).toNat
                if (good.get! (x / 8)) &&& ((1 : UInt8) <<< (x % 8).toUInt8) == 0 then
                  let mut hit := false
                  for k in [0:n] do
                    let y := rd32 b (o + 4 + 4 * k)
                    if y == rootParent then hit := true
                    else
                      let yn := y.toNat
                      if (good.get! (yn / 8)) &&& ((1 : UInt8) <<< (yn % 8).toUInt8) != 0 then hit := true
                  if hit then
                    good := good.set! (x / 8) ((good.get! (x / 8)) ||| ((1 : UInt8) <<< (x % 8).toUInt8))
                    changed := true
                o := o + es
              b ← readChunk h es
        -- expanded leaderless classes from which no leader is reachable (in the explored part)
        let mut bad := 0
        let mut firstBad : Option (Nat × Nat) := none
        for d in [0:nl] do
          if !(← (edgePath dir d).pathExists) then continue
          let h ← IO.FS.Handle.mk (edgePath dir d) .read
          let mut b ← readChunk h es
          while b.size > 0 do
            let mut o := 0
            while o < b.size do
              let x := (rd32 b o).toNat
              if (good.get! (x / 8)) &&& ((1 : UInt8) <<< (x % 8).toUInt8) == 0 then
                bad := bad + 1
                if firstBad.isNone then firstBad := some (d, x)
              o := o + es
            b ← readChunk h es
        stuck := some bad
        IO.eprintln s!"seed {si}: leaderless fixpoint {passes} passes, {bad} expanded leaderless classes reach no leader"
        if let some (d, x) := firstBad then
          let (idx, _) ← recordBySlot (layerPath dir d) n cap km (← tref.get) x
          let (sts, es') ← pathTo dir n cap km (← tref.get) d idx
          let (g', word, phys) ← replay ag tr seedsPhys[si]! sts es'
          ag := g'
          wits := wits.push (witnessJson ag (if complete then "leaderless_bottom" else "leaderless_no_leader_in_explored") d word phys)
          if complete && bottom.isNull then
            let (j, g') ← bottomWitness x ag
            ag := g'
            bottom := j
      let depth := (List.range stats.layers.size).foldl (fun a d => if stats.layers[d]! > 0 then d else a) 0
      let secs := ((← IO.monoMsNow) - t0).toFloat / 1000.0
      let res := Json.mkObj
        [ ("seed", si), ("node", if graph then toJson seedIds[seedIds.size - 1]! else Json.null)
        , ("status", status), ("complete", complete), ("covered", covered)
        , ("reachable", stats.count), ("new_classes", tcount - before)
        , ("expanded", stats.expanded), ("unexpanded", stats.count - stats.expanded)
        , ("depth", depth), ("max_leaders", stats.maxL), ("min_leaders", stats.minL)
        , ("multi_leader_classes", stats.multi), ("leaderless_classes", stats.leaderless)
        , ("leaderless_expanded_reaching_no_leader", match stuck with | some b => toJson b | none => Json.null)
        , ("leaderless_bottom", if stats.leaderless == 0 then toJson false
            -- a complete closure without a target has no leader at all
            else if stopMode != 0 && complete then toJson true
            else match stuck with
              | some b => if complete then toJson (decide (b > 0)) else Json.null
              | none => Json.null)
        , ("outcome", if stopMode == 0 then toJson status
            else toJson (if status == "error" then "error" else if status == "target_found" then "target_found"
              else if complete then "complete_without_target" else "budget_exhausted"))
        , ("error", match errMsg with | some e => toJson e | none => Json.null)
        , ("witnesses", Json.arr wits), ("bottom_scc", bottom)
        , ("layers", toJson stats.layers), ("seconds", toJson secs) ]
      IO.println res.compress
      results := results.push res
      if !graph then
        let h ← IO.FS.Handle.mk (outDir / "results.jsonl") .append
        h.putStrLn res.compress
        h.flush
      if !graph then agentsWritten ← writeCkpt (si + 1) none results ag agentsWritten
    -- outputs
    let hA ← IO.FS.Handle.mk (outDir / "agents.jsonl") .write
    for a in ag.arr do hA.putStrLn (PPLLAuthSim.encode a).compress
    hA.flush
    IO.FS.writeFile (outDir / "seedlog.json") ((Json.arr results).compress ++ "\n")
    let getN := fun (r : Json) (k : String) => (r.getObjValAs? Nat k).toOption.getD 0
    let getB := fun (r : Json) (k : String) => (r.getObjValAs? Bool k).toOption.getD false
    let totalClasses := results.foldl (fun a r => a + getN r "reachable") 0
    let bound : Float := if km.exact then 0.0 else
      results.foldl (fun a r => let x := (getN r "reachable").toFloat; a + x * x) 0.0 / (2.0 ^ 129.0)
    let mut extra : List (String × Json) := []
    if graph then
      if let some nh := nodesH? then nh.flush
      if let some eh := edgesH? then eh.flush
      let mut un : Array Nat := #[]
      for x in [0:gcount] do
        if expd.get! x == 0 then un := un.push x
      IO.FS.writeFile (outDir / "unexpanded.txt") ("\n".intercalate (un.toList.map toString) ++ "\n")
      IO.FS.writeFile (outDir / "seeds.txt") ("\n".intercalate (seedIds.toList.map toString) ++ "\n")
      extra := [("unexpanded", toJson un.size)]
    let fields : List (String × Json) :=
      [ ("variant", toJson variant), ("n", toJson n), ("psi", toJson ψ), ("kappa", toJson κ)
      , ("cap", toJson budget), ("seed_cap", toJson budget)
      , ("quotient", toJson "rotation classes"), ("topology", toJson "ring")
      , ("mode", toJson (if shared then "shared" else "per_seed"))
      , ("key", toJson (if km.exact then s!"exact ({w} bits per agent)" else "fingerprint128"))
      , ("collision_bound", toJson bound)
      , ("classes", toJson (if shared then tcount else totalClasses))
      , ("agents", toJson ag.arr.size), ("pair_memo", toJson ag.memo.size)
      , ("seeds", toJson (seedEnd - seedFrom)), ("seeds_done", toJson results.size)
      , ("seeds_complete", toJson (results.filter fun r => getB r "complete").size)
      , ("max_leaders", toJson (results.foldl (fun a r => max a (getN r "max_leaders")) 0))
      , ("seeds_with_multi_leader", toJson (results.filter fun r => getN r "multi_leader_classes" > 0).size)
      , ("seeds_with_leaderless_bottom", toJson (results.filter fun r => getB r "leaderless_bottom").size)
      , ("run_status", toJson runStatus)
      , ("stop", toJson (["none", "leader", "leader_or_hole"].getD stopMode "?"))
      , ("outcomes", Json.mkObj ((["target_found", "complete_without_target", "budget_exhausted", "complete", "seed_cap", "disk_cap", "error"].map fun k =>
          (k, toJson (results.filter fun r => (r.getObjValAs? String "outcome").toOption == some k).size)).filter fun p => p.2 != toJson 0))
      , ("seconds", toJson (((← IO.monoMsNow) - tRun).toFloat / 1000.0)) ]
    let summary := Json.mkObj (fields ++ extra)
    IO.FS.writeFile (outDir / "summary.json") (summary.compress ++ "\n")
    IO.println summary.compress
    return 0
  else throw (IO.userError "psi must be positive")

end PPLLAuthCensus

def main (args : List String) : IO UInt32 := do
  match args with
  | variant :: n :: ψ :: κ :: cap :: seeds :: out :: work :: flags =>
    match n.toNat?, ψ.toNat?, κ.toNat?, cap.toNat? with
    | some n, some ψ, some κ, some cap =>
      let rec opt (fs : List String) (k : String) : Option Nat :=
        match fs with
        | a :: b :: rest => if a == k then b.toNat? else opt (b :: rest) k
        | _ => none
      let known := ["--shared", "--graph", "--from", "--to", "--keybits", "--minfree", "--stop", "--only", "--scclimit", "--noedges"]
      let rec sopt (fs : List String) (k : String) : Option String :=
        match fs with
        | a :: b :: rest => if a == k then some b else sopt (b :: rest) k
        | _ => none
      let stopMode := match sopt flags "--stop" with
        | some "leader" => 1 | some "leader_or_hole" => 2 | _ => 0
      if (sopt flags "--stop").isSome && stopMode == 0 && sopt flags "--stop" != some "none" then
        IO.eprintln "--stop must be none, leader or leader_or_hole"; return 2
      let only : Array Nat := match sopt flags "--only" with
        | some l => ((l.splitOn ",").filterMap String.toNat?).toArray
        | none => #[]
      if flags.any (fun f => f.startsWith "--" && !known.contains f) then
        IO.eprintln s!"unknown flag in {flags}"; return 2
      PPLLAuthCensus.run variant n ψ κ cap seeds out work
        (flags.contains "--shared") (flags.contains "--graph")
        ((opt flags "--from").getD 0) ((opt flags "--to").getD 1000000000)
        ((opt flags "--keybits").getD 16) ((opt flags "--minfree").getD 20) stopMode only
        ((opt flags "--scclimit").getD 200000000) (flags.contains "--noedges")
    | _, _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ =>
    IO.eprintln "usage: ppll-authf-census VARIANT N PSI KAPPA CAP SEEDS OUTDIR WORKDIR [--shared] [--graph] [--from A] [--to B] [--keybits W] [--minfree GiB] [--stop none|leader|leader_or_hole] [--only i,j,..] [--scclimit N] [--noedges]"
    return 2
