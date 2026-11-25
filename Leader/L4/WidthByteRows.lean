import Leader.L4.AllSizeProtocol

/-! The SANITIZE2 width client packed by the scaled offset grammar.
This adapter uses the high-first numerical lane convention;
it is not an assertion of byte identity to another record serialization. -/
namespace L4.WidthByteRows
open AllSizeProtocol

abbrev W (c : Nat) := 30+ell (c+1)

def offField (c : Nat) : Field (W c) (ell (c+1)) := ⟨30,by unfold W; omega⟩
def suffixField (c j d : Nat) (h : j+d≤30) : Field (W c) d :=
  ⟨30-j-d,by unfold W; omega⟩

def get {c : Nat} (x : BitVec (W c)) (j d : Nat) (h : j+d≤30) : Nat :=
  ((suffixField c j d h).read x).toNat

def put (c j d : Nat) (h : j+d≤30) (v : Nat) : Patch (W c) :=
  (suffixField c j d h).assign (BitVec.ofNat d v)

def inside {c : Nat} (x : BitVec (W c)) : Bool := get (c:=c) x 3 1 (by decide)==1
def last {c : Nat} (x : BitVec (W c)) : Bool := get (c:=c) x 4 1 (by decide)==1

def offset {c : Nat} (header : Bool) (x : BitVec (W c)) : Nat :=
  if header then 0 else min c ((offField c).read x).toNat

theorem offset_cap {c : Nat} (h : Bool) (x : BitVec (W c)) : offset h x≤c := by
  cases h <;> simp [offset,Nat.min_le_left]

/-- Unit tags ignore padding. Recognizable malformed F/D return a
canonical fault *and* issue a materialization intent. F needs OK and D
needs PASS: these checks extend the sparse typed regression domain. -/
structure Token where
  tag : Nat
  op : Nat := 0
  arg : Nat := 0
  fault : Bool := false
  deriving DecidableEq, Repr

def encode (t : Token) : BitVec 16 :=
  BitVec.ofNat 16 (16384*t.tag + 8192*t.fault.toNat + 1024*t.op +
    (if t.tag==3 && t.fault then 64 else 0) + t.arg)

def faultCode (tag : Nat) : Token := ⟨tag,0,0,true⟩

def decode (x : BitVec 16) : Token :=
  let tag := (x.extractLsb' 14 2).toNat
  let fault := x.getLsbD 13
  let op := (x.extractLsb' 10 3).toNat
  let race := (x.extractLsb' 7 3).toNat
  let outcome := (x.extractLsb' 5 2).toNat
  let arg := (x.extractLsb' 0 4).toNat
  if tag≤1 then ⟨tag,0,0,false⟩
  else
    if fault || op>5 || race != 0 || outcome != 0 ||
        (tag==2 && op==2 && (arg%4==3 || arg/4==3))
      then faultCode tag
      else
        let bits := if tag==2 && op==2 then 4 else
          if op==3 && tag==2 || op==2 && tag==3 then 2 else
          if op==1 || op==4 && tag==2 then 1 else 0
        ⟨tag,op,arg%(2^bits),false⟩

/-- Selected masked mark action. Every field written by an opcode is
patched even if the resulting bit is already equal. -/
def departing {c : Nat} (r i : Nat) (x : BitVec (W c)) (t : Token) :
    Patch (W c) × Token :=
  let Wp := put c
  let count := get (c:=c) x 5 1 (by decide)
  let done := get (c:=c) x 1 1 (by decide)
  let pick := get (c:=c) x 2 1 (by decide)
  let change := fun j (h : j+1≤30) b => Wp j 1 h b
  if t.fault then (.empty _,t)
  else
    match t.op with
    | 0 => (((change 1 (by decide) 0).compose (change 2 (by decide) 0)).compose
           (change 5 (by decide) 0),t)
    | 1 =>
      let d : Nat := if done==0 && t.arg==0 then 1 else 0
      ((change 2 (by decide) d).compose (change 1 (by decide) (d ||| done)),
       {t with arg := t.arg ||| d})
    | 2 =>
      if i<c then
        let cmp := fun d prev => if count < d then 1 else if d < count then 2 else prev
        let a := cmp ((r >>> i)%2) (t.arg/4)
        let b := cmp (((r-1) >>> i)%2) (t.arg%4)
        (.empty _, {t with arg := 4*a+b})
      else (.empty _,t)
    | 3 =>
      if pick==1 then ((change 3 (by decide) (t.arg/2)).compose
        (change 4 (by decide) (t.arg%2)),t) else (.empty _,t)
    | 4 =>
      if i<c then ((change 5 (by decide) ((t.arg+count)%2)),{t with arg := (t.arg+count)/2})
      else (.empty _,t)
    | 5 => (change 6 (by decide) (if i<c then count else 0),t)
    | _ => (.empty _,t)

def finish (t : Token) : Token :=
  if t.fault then faultCode 3
  else ⟨3,t.op,
    if t.op==1 then t.arg else if t.op==2 then
      2*(t.arg/4==1).toNat+(t.arg%4==0).toNat else 0,false⟩

def tokenPatch (c : Nat) (t : Token) : Patch (W c) :=
  (suffixField c 14 16 (by decide)).assign (encode t)

def control (c phase op arg : Nat) : Patch (W c) :=
  put c 7 7 (by decide) (32*phase+4*op+arg)

def emptyToken : Token := ⟨0,0,0,false⟩
def trailToken : Token := ⟨1,0,0,false⟩

/-- Door consumes only its old decoded K token. ISSUE updates phase only;
WAIT relaunch/reset writes the control record and E token, not extra
padding elsewhere. -/
def doorPatch {c : Nat} (x : BitVec (W c)) (t : Token) : Patch (W c) :=
  let p := get (c:=c) x 7 2 (by decide)
  let op := get (c:=c) x 9 3 (by decide)
  let a := get (c:=c) x 12 2 (by decide)
  let go := fun op a => (control c 1 op a).compose (tokenPatch c emptyToken)
  if op>5 || p==0 || p==3 then go 0 0
  else if p==1 then
    let arg := if op==3 then a else if op==4 then 1 else 0
    (put c 7 2 (by decide) 2).compose (tokenPatch c ⟨2,op,arg,false⟩)
  else if t.tag==1 || t.tag==2 then .empty _
  else if t.tag != 3 || t.op != op || t.fault then go 0 0
  else match op with
    | 0 => go 1 0
    | 1 => go (if t.arg==1 then 2 else 5) 0
    | 2 => go 3 t.arg
    | 3 => go 4 0
    | 4 => go 1 0
    | _ => go 0 0

/-- Total padded width work on one immutable old pair. It reads
old offset but leaves offset/cache writes to the separate geometry
join. No unrelated IN/LAST/counter/source/token is re-encoded. -/
def row {c : Nat} (r : Nat) (headers : Pair Bool) (x : Pair (BitVec (W c))) :
    Pair (Patch (W c)) :=
  let h := headers.1
  let j := headers.2
  let i := offset h x.1
  let f := decode ((suffixField c 14 16 (by decide)).read x.1)
  let d := decode ((suffixField c 14 16 (by decide)).read x.2)
  let reset := control c 1 0 0
  let canon := fun t : Token => if t.fault then tokenPatch c t else .empty (W c)
  let a := (if h then .empty _ else reset).compose (canon f)
  let b := (if j then .empty _ else reset).compose (canon d)
  let y :=
    if f.tag==2 then
      let (eff,t) := departing (c:=c) r i x.1 f
      let a := a.compose eff
      if j then (a.compose (tokenPatch c (finish t)),b)
      else (a.compose (tokenPatch c trailToken),b.compose (tokenPatch c t))
    else if j && f.tag==1 then (a.compose (tokenPatch c emptyToken),b)
    else if !j && d.tag==3 then (a.compose (tokenPatch c d),b.compose (tokenPatch c emptyToken))
    else if !j && f.tag==1 && d.tag==0 then (a.compose (tokenPatch c emptyToken),b)
    else (a,b)
  (y.1,if j then y.2.compose (doorPatch (c:=c) x.2 d) else y.2)

/-- The width work row owns no bit of the high geometry prefix. -/
def WorkOnly {c : Nat} (p : Patch (W c)) : Prop :=
  ∀ i, 29≤i → p.mask.getLsbD i=false

private theorem empty_work (c : Nat) : WorkOnly (c:=c) (.empty (W c)) := by
  intro i h
  simp [Patch.empty]

private theorem join_work {c : Nat} (p q : Patch (W c)) (hp : WorkOnly (c:=c) p)
    (hq : WorkOnly (c:=c) q) : WorkOnly (c:=c) (p.compose q) := by
  intro i hi
  simp [Patch.compose,hp i hi,hq i hi]

private theorem field_work {c j d : Nat} (h : j+d≤30) (hj : 1≤j) (v : Nat) :
    WorkOnly (c:=c) (put c j d h v) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have H := ((suffixField c j d h).inMask (BitVec.ofNat d v) i).mp hm
  simp only [suffixField] at H
  omega

private theorem token_work (c : Nat) (t : Token) : WorkOnly (c:=c) (tokenPatch c t) :=
  field_work (by decide) (by decide) (encode t).toNat

private theorem control_work (c phase op arg : Nat) : WorkOnly (c:=c) (control c phase op arg) :=
  field_work (by decide) (by decide) _

private theorem depart_work {c : Nat} (r i : Nat) (x : BitVec (W c)) (t : Token) :
    WorkOnly (c:=c) (departing (c:=c) r i x t).1 := by
  unfold departing
  dsimp only
  split
  · apply empty_work
  · split
    · exact join_work _ _ (join_work _ _ (field_work (by decide) (by decide) _)
        (field_work (by decide) (by decide) _)) (field_work (by decide) (by decide) _)
    · exact join_work _ _ (field_work (by decide) (by decide) _)
        (field_work (by decide) (by decide) _)
    · split <;> apply empty_work
    · split
      · exact join_work _ _ (field_work (by decide) (by decide) _)
          (field_work (by decide) (by decide) _)
      · apply empty_work
    · split
      · apply field_work <;> decide
      · apply empty_work
    · apply field_work <;> decide
    · apply empty_work

private theorem door_work {c : Nat} (x : BitVec (W c)) (t : Token) :
    WorkOnly (c:=c) (doorPatch (c:=c) x t) := by
  unfold doorPatch
  dsimp only
  split
  · exact join_work _ _ (control_work c _ _ _) (token_work c _)
  · split
    · exact join_work _ _ (field_work (by decide) (by decide) _) (token_work c _)
    · split
      · apply empty_work
      · split
        · exact join_work _ _ (control_work c _ _ _) (token_work c _)
        · split <;> exact join_work _ _ (control_work c _ _ _) (token_work c _)

/-- The adapter never competes with the two geometry writers,
including on invalid tokens, ignored payloads and idempotent writes. -/
theorem row_work_only {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (W c))) :
    WorkOnly (c:=c) (row (c:=c) r h x).1 ∧ WorkOnly (c:=c) (row (c:=c) r h x).2 := by
  let ok := fun (y : Pair (Patch (W c))) => WorkOnly (c:=c) y.1 ∧ WorkOnly (c:=c) y.2
  have canon (p : Token) : WorkOnly (c:=c)
      (if p.fault then tokenPatch c p else .empty _) := by
    split
    · exact token_work c _
    · exact empty_work _
  have start (h : Bool) : WorkOnly (c:=c) (if h then .empty _ else control c 1 0 0) := by
    split
    · exact empty_work _
    · exact control_work c _ _ _
  unfold row
  dsimp only
  generalize ha : (if h.1 = true then Patch.empty (W c) else control c 1 0 0).compose _ = a
  generalize hb : (if h.2 = true then Patch.empty (W c) else control c 1 0 0).compose _ = b
  have ha' : WorkOnly (c:=c) a := ha ▸ join_work _ _ (start _) (canon _)
  have hb' : WorkOnly (c:=c) b := hb ▸ join_work _ _ (start _) (canon _)
  let Y := if (decode ((suffixField c 14 16 (by decide)).read x.1)).tag==2 then
      let (eff,t) := departing (c:=c) r (offset h.1 x.1) x.1
        (decode ((suffixField c 14 16 (by decide)).read x.1))
      let aa := a.compose eff
      if h.2 then (aa.compose (tokenPatch c (finish t)),b)
      else (aa.compose (tokenPatch c trailToken),b.compose (tokenPatch c t))
    else if h.2 && (decode ((suffixField c 14 16 (by decide)).read x.1)).tag==1 then
      (a.compose (tokenPatch c emptyToken),b)
    else if !h.2 && (decode ((suffixField c 14 16 (by decide)).read x.2)).tag==3 then
      (a.compose (tokenPatch c (decode ((suffixField c 14 16 (by decide)).read x.2))),
        b.compose (tokenPatch c emptyToken))
    else if !h.2 && (decode ((suffixField c 14 16 (by decide)).read x.1)).tag==1 &&
      (decode ((suffixField c 14 16 (by decide)).read x.2)).tag==0 then
      (a.compose (tokenPatch c emptyToken),b)
    else (a,b)
  have hy : ok Y := by
    unfold Y
    split
    · generalize E : departing (c:=c) r (offset h.1 x.1) x.1 _ = dt
      have hh := depart_work (c:=c) r (offset h.1 x.1) x.1 (decode ((suffixField c 14 16 (by decide)).read x.1))
      rw [E] at hh
      rcases dt with ⟨d,t⟩
      dsimp only
      split
      · exact ⟨join_work _ _ (join_work _ _ ha' hh) (token_work c _),hb'⟩
      · exact ⟨join_work _ _ (join_work _ _ ha' hh) (token_work c _),join_work _ _ hb' (token_work c _)⟩
    · split
      · exact ⟨join_work _ _ ha' (token_work c _),hb'⟩
      · split
        · exact ⟨join_work _ _ ha' (token_work c _),join_work _ _ hb' (token_work c _)⟩
        · split
          · exact ⟨join_work _ _ ha' (token_work c _),hb'⟩
          · exact ⟨ha',hb'⟩
  change WorkOnly (c:=c) Y.1 ∧ WorkOnly (c:=c)
    (if h.2 then Y.2.compose (doorPatch (c:=c) x.2 _) else Y.2)
  refine ⟨hy.1,?_⟩
  split
  · exact join_work _ _ hy.2 (door_work _ _)
  · exact hy.2

/-- Idempotent BEGIN owns both flags and counter; a held right WAIT
with T has no write even while the left F terminalizes on the seam. -/
theorem begin_mask_fixture :
    let a : BitVec (W 5) := 32768
    let b : BitVec (W 5) := 4210688
    let p := row (c:=5) 3 (true,true) (a,b)
    p.1.mask.toNat=2^28+2^27+2^24+65535 ∧
      p.1.value.toNat=49152 ∧ p.2.mask.toNat=0 := by decide

/-- The width parser refuses off-domain F outcome D race bytes even
though the software typed fixture usually generates only OK/PASS. -/
theorem malformed_examples :
    decode (BitVec.ofNat 16 (32768+32))=faultCode 2 ∧
    decode (BitVec.ofNat 16 (49152+128))=faultCode 3 := by decide

/-- The dormant padding of a holding E token is not globally encoded. -/
theorem dormant_hold_fixture :
    let a : BitVec (W 5) := 1023
    let b : BitVec (W 5) := 4210688
    let p := row (c:=5) 3 (true,true) (a,b)
    p.1.mask.toNat=0 ∧ p.2.mask.toNat=0 ∧ p.1.apply a=a := by decide

end L4.WidthByteRows
