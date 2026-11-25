import Leader.L4.MISByteCodec

/-! The 96-bit MIS provider, selected old-pair work only. -/
namespace L4.MISByteRows
open AllSizeProtocol MISByteCodec

private def selector (x : BitVec 96) : Nat := get x 92 1 (by decide)
private def grant (x : BitVec 96) (j : Fin 3) : Bool := x.getLsbD (91-j.val)
private def bitAt (x j : Nat) : Bool := (x >>> j)%2==1
private def bank (x : BitVec 96) (j : Nat) : Bool := x.getLsbD (88-j)

private def putBank (j : Nat) (b : Bool) : Patch 96 :=
  put (88-j) 1 (by omega) b.toNat

private def putSeal (d : Option Nat) : Patch 96 :=
  put 83 4 (by decide) (match d with | none=>0 | some q=>8+q)

private def grantsPatch (g : Fin 3 → Bool) : Patch 96 :=
  put 89 3 (by decide) (4*(g 0).toNat+2*(g 1).toNat+(g 2).toNat)

private def canonical (x : BitVec 96) (j : Fin 3) : Bool :=
  if grant x 1 then j==1 else grant x j

structure Link where
  src : Fin 3
  dst : Option (Fin 3)

private def links (header : Bool) : List Link :=
  if header then [⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] else
    [⟨0,some 0⟩,⟨1,some 1⟩,⟨2,some 2⟩]

private def parked (t : Token) (h : Bool) (x : BitVec 96) (j : Fin 3) : Bool :=
    t.tag==2 && !t.fault && t.opcode==2 && atGate h x j

private def ready (h : Bool) (x : BitVec 96) (j : Fin 3) (t : Token) : Bool :=
  t.tag==2 && !(parked t h x j && t.race<4)

private def raceNext (t : Token) (side : Nat) : Token :=
  if t.race==1 then {t with race:=side} else
    if (t.race==2 || t.race==3) && t.race != side then
      {t with race:=t.race+2} else t

private def terminal (t : Token) : Token :=
  if t.fault || (t.opcode==6 && !t.applied) then faultToken 3
  else if t.opcode==3 then
    if bitAt t.payload 6 then { tag:=3, opcode:=3, payload:=t.payload%64 }
    else { tag:=3, opcode:=3, outcome:=1 }
  else { tag:=3, opcode:=t.opcode, payload:=if t.opcode==2 then t.payload else 0 }

private def arrival (h : Bool) (x : BitVec 96) (j : Fin 3) (t : Token) : Token :=
  if !t.fault && t.opcode==2 && atGate h x j then {t with race:=1} else t

private def setPLane (p k : Nat) (b : Bool) : Nat :=
  if bitAt p k then if b then p else p-2^k
  else if b then p+2^k else p

private def effect (u v : BitVec 96) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Token) :
    Patch 96 × Patch 96 × Token :=
  let none := Patch.empty 96
  if t.fault then (none,none,t)
  else if t.opcode==6 && hv && j==0 && k==some 1 then
    let ix := (t.payload/2)%2
    if !t.applied && grant v 1 && selector v==t.payload/4 &&
        readSeal v==some t.payload && bank v ix==bitAt t.payload 0 then
      (none,(put 92 1 (by decide) ix).compose (putSeal Option.none),{t with applied:=true})
    else (none,none,faultToken 2)
  else if parked t hu u j then (none,none,{t with race:=0,payload:=t.race-4})
  else if hu && j==1 && t.opcode==0 then (putSeal Option.none,none,t)
  else if hu && t.opcode==3 then
    let p := if win then (setPLane (setPLane t.payload (5-j.val) (selector u==1))
        (2-j.val) (bank u (selector u))) else setPLane t.payload 6 false
    (none,none,{t with payload:=p})
  else if hu && j==1 && (t.opcode==4 || t.opcode==5) then
    let ix := (t.payload/2)%2
    if !(grant u 1 && selector u==t.payload/4) ||
        (t.opcode==5 && bank u ix != bitAt t.payload 0) then (none,none,faultToken 2)
    else if t.opcode==4 then (putBank ix (bitAt t.payload 0),none,t)
    else (putSeal (some t.payload),none,t)
  else (none,none,t)

/-- The complete old-pair width-independent MIS client work. Both the
outbound and return routes read immutable old K and authority. Do not
apply endpoint patches before calling this producer. -/
def row (headers : Pair Bool) (old : Pair (BitVec 96)) : Pair (Patch 96) :=
  let hu:=headers.1
  let hv:=headers.2
  let u:=old.1
  let v:=old.2
  let fu := oldK hu u
  let fv := oldK hv v
  let action := fun (j : Fin 3) (op : Nat) =>
    let t := fu j
    hu && ready hu u j t && !t.fault && t.opcode==op
  let rel := fun j => action j 0
  let ask := fun j => action j 3
  let w := !canonical u 0 && !canonical u 1 && !canonical u 2 && ask 1 && !rel 1
  let win := fun j : Fin 3 =>
    if j==1 then w
    else !w && !canonical u 1 && ask j && !canonical u j && !rel j
  let gg := fun j => (canonical u j && !rel j) || win j
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let a := if hu then grantsPatch gg else clear
  let b := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  let ru := fun (j : Fin 3) =>
    let t := fu j
    if t.fault then putK j t
    else if parked t hu u j && (t.race==1 || t.race==2) then putK j (raceNext t 3)
    else .empty _
  let rv := fun (j : Fin 3) =>
    let t := fv j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  let a := ((a.compose (ru 0)).compose (ru 1)).compose (ru 2)
  let b := ((b.compose (rv 0)).compose (rv 1)).compose (rv 2)
  let routed := (links hv).foldl (fun (a,b) l =>
    let j := l.src
    let t := fu j
    if ready hu u j t then
      let (d,e,t') := effect u v hu hv j l.dst (win j) t
      match l.dst with
      | none => ((a.compose d).compose (putK j (terminal t')),b.compose e)
      | some k => ((a.compose d).compose (putK j T),
        (b.compose e).compose (putK k (arrival hv v k t')))
    else
      if t.tag==2 then (a,b)
      else match l.dst with
      | none => (if t.tag==1 then a.compose (putK j E) else a,b)
      | some k =>
        let reply := fv k
        if reply.tag==3 then (a.compose (putK j reply),b.compose (putK k E))
        else if t.tag==1 && reply.tag==0 then (a.compose (putK j E),b)
        else (a,b)
  ) (a,b)
  if hv then
    let (p,t) := source v (fv 0)
    (routed.1,(routed.2.compose p).compose (match t with | none=>.empty _ | some t=>putK 0 t))
  else routed

/-- The responder's old guarded authority determines the incoming
COMMIT. Exactly that field group receives writes, separately from K1.
The right WAIT/T door does not write its held source or K0. -/
theorem incoming_commit_mask_fixture :
    let u : BitVec 96 := BitVec.ofNat 96 ((encode {tag:=2,opcode:=6,payload:=3}).toNat*2^38)
    let v : BitVec 96 := BitVec.ofNat 96 (2^90+2^87+11*2^83+2^82+2^55)
    let p := row (true,true) (u,v)
    p.2.mask.toNat=2^92+15*2^83+(2^19-1)*2^19 ∧
      selector (p.2.apply v)=1 ∧ readSeal (p.2.apply v)=none ∧
      (oldK true (p.2.apply v) 1).applied=true := by
  decide

/-- Removing the old grant leaves the target bank, selector and seal
raw; the only right-side effect is the departing fault in K1. -/
theorem ungranted_commit_mask_fixture :
    let u : BitVec 96 := BitVec.ofNat 96 ((encode {tag:=2,opcode:=6,payload:=3}).toNat*2^38)
    let v : BitVec 96 := BitVec.ofNat 96 (2^87+11*2^83+2^82+2^55)
    let p := row (true,true) (u,v)
    p.2.mask.toNat=(2^19-1)*2^19 ∧
      selector (p.2.apply v)=0 ∧ readSeal (p.2.apply v)=some 3 ∧
      (oldK true (p.2.apply v) 1).fault=true := by
  decide

/-- ADMIT arriving at the right gate begins FIRST, while an existing
parked ADMIT can independently observe its old incident side. -/
theorem parked_old_pair_fixture :
    let u : BitVec 96 := BitVec.ofNat 96 ((encode {tag:=2,opcode:=2}).toNat*2^38)
    let v : BitVec 96 := BitVec.ofNat 96 (2^82+2^55)
    let p := row (true,true) (u,v)
    (oldK true (p.2.apply v) 1).race=1 ∧ (oldK true (p.1.apply u) 0).tag=1 := by
  decide

end L4.MISByteRows
